module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24InLocal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

section Candidates

variable {G : Type} [Group G]

theorem fi24in_mem_vCandidates_iff {K : Subgroup G} {u : G} (hu : u ∈ K) {v : G} :
    v ∈ vCandidates K u ↔ v ∈ K ∧ ¬ (∀ k ∈ K, v * k = k * v) ∧ orderOf v = 2 := by
  have hsup : K ⊔ zpowers u = K := sup_eq_left.2 (zpowers_le.2 hu)
  unfold vCandidates
  simp only [Set.mem_ofPred_eq, hsup, mem_center_map_iff]
  constructor
  · rintro ⟨hvK, hvZ, h2⟩
    exact ⟨hvK, fun h => hvZ ⟨hvK, h⟩, h2⟩
  · rintro ⟨hvK, hvZ, h2⟩
    exact ⟨hvK, fun h => hvZ h.2, h2⟩

theorem fi24in_orderOf_eq_two_iff {x : G} (h : x * x = 1) : orderOf x = 2 ↔ x ≠ 1 :=
  ⟨fun h2 h1 => by
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num),
   fun h1 => orderOf_eq_prime (by rw [pow_two]; exact h) h1⟩

end Candidates

section Cover

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

omit [Finite H] in
theorem fi24in_img_eq_one_iff (hodd : Odd (Nat.card (center ↥L))) {x : ↥L} (hxx : x * x = 1) :
    (x : ↥L ⧸ center ↥L) = 1 ↔ x = 1 := by
  constructor
  · intro h
    exact Closing.eq_one_of_sq_eq_one_of_odd_center hodd ((QuotientGroup.eq_one_iff _).1 h) hxx
  · rintro rfl
    exact QuotientGroup.mk_one _

omit [Finite H] in
theorem fi24in_comm_iff (hK' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L)
    (hKL : K ≤ L) {x : ↥L} :
    (∀ k ∈ K, (x : H) * k = k * x) ↔
      ∀ y ∈ bar (K.subgroupOf L), (x : ↥L ⧸ center ↥L) * y = y * (x : ↥L ⧸ center ↥L) := by
  constructor
  · intro h y hy
    obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy
    show (x : ↥L ⧸ center ↥L) * (k : ↥L ⧸ center ↥L) = (k : ↥L ⧸ center ↥L) * (x : ↥L ⧸ center ↥L)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg (QuotientGroup.mk (s := center ↥L))
      (Subtype.ext (h k (Subgroup.mem_subgroupOf.1 hk)))
  · intro h k hk
    have hx' : (x : ↥L ⧸ center ↥L) ∈ centralizer (bar (K.subgroupOf L) : Set (↥L ⧸ center ↥L)) :=
      Subgroup.mem_centralizer_iff.2 fun y hy => (h y hy).symm
    have h2 := Subgroup.mem_centralizer_iff.1 (mem_centralizer_of_mk_mem hK' hx')
      (⟨k, hKL hk⟩ : ↥L) (Subgroup.mem_subgroupOf.2 hk)
    exact (congrArg Subtype.val h2).symm

theorem fi24in_twoAdic_cent_eq (hodd : Odd (Nat.card (center ↥L))) (hKL : K ≤ L) {x : ↥L}
    (hxx : x * x = 1) :
    twoAdic (K ⊓ centralizer ({(x : H)} : Set H)) =
      twoAdic (bar (K.subgroupOf L) ⊓
        centralizer ({(x : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L))) := by
  set P : Subgroup ↥L := K.subgroupOf L ⊓ centralizer ({x} : Set ↥L) with hP
  have hA : twoAdic (K ⊓ centralizer ({(x : H)} : Set H)) = twoAdic P := by
    have hmap : P.map L.subtype = K ⊓ centralizer ({(x : H)} : Set H) := by
      ext y
      constructor
      · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.1 hz1, mem_centralizer_singleton_iff.2
          (congrArg Subtype.val (mem_centralizer_singleton_iff.1 hz2))⟩
      · rintro ⟨hy1, hy2⟩
        exact ⟨⟨y, hKL hy1⟩, ⟨Subgroup.mem_subgroupOf.2 hy1, mem_centralizer_singleton_iff.2
          (Subtype.ext (mem_centralizer_singleton_iff.1 hy2))⟩, rfl⟩
    unfold twoAdic
    rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]
  have hB : bar P = bar (K.subgroupOf L) ⊓
      centralizer ({(x : ↥L ⧸ center ↥L)} : Set (↥L ⧸ center ↥L)) := by
    ext y
    constructor
    · rintro ⟨z, ⟨hz1, hz2⟩, rfl⟩
      refine ⟨mk_mem_bar_of_mem hz1, mem_centralizer_singleton_iff.2 ?_⟩
      show (z : ↥L ⧸ center ↥L) * (x : ↥L ⧸ center ↥L) = (x : ↥L ⧸ center ↥L) * (z : ↥L ⧸ center ↥L)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_centralizer_singleton_iff.1 hz2]
    · rintro ⟨hy1, hy2⟩
      obtain ⟨k, hk, rfl⟩ := mem_bar.1 hy1
      refine ⟨k, ⟨hk, mem_centralizer_singleton_iff.2 ?_⟩, rfl⟩
      have hkk : (k * x * k⁻¹) * (k * x * k⁻¹) = 1 := by
        calc (k * x * k⁻¹) * (k * x * k⁻¹) = k * (x * x) * k⁻¹ := by group
          _ = 1 := by rw [hxx]; group
      have himg : ((k * x * k⁻¹ : ↥L) : ↥L ⧸ center ↥L) = (x : ↥L ⧸ center ↥L) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        have h3 : (k : ↥L ⧸ center ↥L) * (x : ↥L ⧸ center ↥L) =
            (x : ↥L ⧸ center ↥L) * (k : ↥L ⧸ center ↥L) := mem_centralizer_singleton_iff.1 hy2
        rw [h3]
        group
      have h4 := Closing.eq_of_mk_eq_of_sq hodd hkk hxx himg
      calc k * x = (k * x * k⁻¹) * k := by group
        _ = x * k := by rw [h4]
  unfold twoAdic at hA ⊢
  rw [hA]
  have := twoAdic_bar hodd P
  unfold twoAdic at this
  rw [← this, hB]

omit [Finite H] in
theorem fi24in_mem_vCandidates_iff_img (hodd : Odd (Nat.card (center ↥L)))
    (hK' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L) (hKL : K ≤ L) (huL : u ∈ L)
    (hbase : Fi24InCoverBase L K u huL) (huK : u ∈ K) (x : ↥L) (hx : (x : H) ∈ K)
    (hxx : x * x = 1) :
    (x : H) ∈ vCandidates K u ↔ (x : ↥L ⧸ center ↥L) ∈ vCandidates (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  rw [fi24in_mem_vCandidates_iff huK, fi24in_mem_vCandidates_iff hbase.u_mem]
  have hxx' : (x : ↥L ⧸ center ↥L) * (x : ↥L ⧸ center ↥L) = 1 := by
    rw [← QuotientGroup.mk_mul, hxx]
    rfl
  have hxxH : (x : H) * (x : H) = 1 := congrArg Subtype.val hxx
  rw [fi24in_orderOf_eq_two_iff hxxH, fi24in_orderOf_eq_two_iff hxx',
    fi24in_comm_iff hK' hKL (x := x)]
  have h1 : (x : ↥L ⧸ center ↥L) ≠ 1 ↔ (x : H) ≠ 1 := by
    rw [Ne, Ne, fi24in_img_eq_one_iff hodd hxx, Subtype.ext_iff]
    rfl
  have hmem : (x : ↥L ⧸ center ↥L) ∈ bar (K.subgroupOf L) :=
    mk_mem_bar_of_mem (Subgroup.mem_subgroupOf.2 hx)
  constructor
  · rintro ⟨-, hA, hB⟩
    exact ⟨hmem, hA, h1.2 hB⟩
  · rintro ⟨-, hA, hB⟩
    exact ⟨hx, hA, h1.1 hB⟩

theorem fi24in_mem_vMaximal_iff (hodd : Odd (Nat.card (center ↥L)))
    (hK' : ⁅K.subgroupOf L, K.subgroupOf L⁆ = K.subgroupOf L) (hKL : K ≤ L) (huL : u ∈ L)
    (hbase : Fi24InCoverBase L K u huL) (huK : u ∈ K) {x : ↥L} (hx : (x : H) ∈ K)
    (hxx : x * x = 1) :
    (x : H) ∈ vMaximal K u ↔ (x : ↥L ⧸ center ↥L) ∈ vMaximal (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
  have hcand := fi24in_mem_vCandidates_iff_img hodd hK' hKL huL hbase huK
  unfold vMaximal
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hc, hmax⟩
    refine ⟨(hcand x hx hxx).1 hc, fun w hw => ?_⟩
    have hw' := (fi24in_mem_vCandidates_iff hbase.u_mem).1 hw
    have hw2 : w * w = 1 := mul_self_eq_one_of_orderOf_eq_two hw'.2.2
    obtain ⟨v₂, hv₂K, hv₂sq, hv₂img⟩ := fi24in_exists_involution_lift hodd hw'.1 hw2
    have hv₂H : (v₂ : H) ∈ K := Subgroup.mem_subgroupOf.1 hv₂K
    have hcv₂ : (v₂ : H) ∈ vCandidates K u :=
      (hcand v₂ hv₂H hv₂sq).2 (by rw [hv₂img]; exact hw)
    have h1 := hmax _ hcv₂
    rw [fi24in_twoAdic_cent_eq hodd hKL hv₂sq, fi24in_twoAdic_cent_eq hodd hKL hxx,
      hv₂img] at h1
    exact h1
  · rintro ⟨hc, hmax⟩
    refine ⟨(hcand x hx hxx).2 hc, fun v' hv' => ?_⟩
    have hv'1 := (fi24in_mem_vCandidates_iff huK).1 hv'
    have hv'2 : v' * v' = 1 := mul_self_eq_one_of_orderOf_eq_two hv'1.2.2
    have hyy : (⟨v', hKL hv'1.1⟩ : ↥L) * ⟨v', hKL hv'1.1⟩ = 1 := Subtype.ext hv'2
    have hcv' := (hcand ⟨v', hKL hv'1.1⟩ hv'1.1 hyy).1 hv'
    have h1 := hmax _ hcv'
    rw [← fi24in_twoAdic_cent_eq hodd hKL (x := ⟨v', hKL hv'1.1⟩) hyy,
      ← fi24in_twoAdic_cent_eq hodd hKL hxx] at h1
    exact h1

theorem fi24in_vPairs_nonempty (hodd : Odd (Nat.card (center ↥L))) (hKq : CFSG.IsQuasisimple ↥K)
    (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hbase : Fi24InCoverBase L K u huL)
    (hpairs : (vPairs (⊤ : Subgroup (↥L ⧸ center ↥L)) (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)).Nonempty) : (vPairs L K u).Nonempty := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have hKu' := central_subgroupOf huL hKu
  have huK := fi24in_mem_of_base hodd huL hu2 hbase
  obtain ⟨w, vY, hvY, hw, y, -, hy⟩ := hpairs
  have hcand := (fi24in_mem_vCandidates_iff hbase.u_mem).1 hvY.1
  have hvv : vY * vY = 1 := mul_self_eq_one_of_orderOf_eq_two hcand.2.2
  obtain ⟨v', hv'K, hv'sq, hv'img⟩ := fi24in_exists_involution_lift hodd hcand.1 hvv
  have hv'H : (v' : H) ∈ K := Subgroup.mem_subgroupOf.1 hv'K
  have hvmax : (v' : H) ∈ vMaximal K u :=
    (fi24in_mem_vMaximal_iff hodd hK' hKL huL hbase huK hv'H hv'sq).2 (by rw [hv'img]; exact hvY)
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm : (⟨u, huL⟩ : ↥L) * v' = v' * ⟨u, huL⟩ := (hKu' v' hv'K).symm
  have hsq1 : (l * ⟨u, huL⟩ * l⁻¹) * (l * ⟨u, huL⟩ * l⁻¹) = 1 := by
    calc (l * ⟨u, huL⟩ * l⁻¹) * (l * ⟨u, huL⟩ * l⁻¹) = l * (⟨u, huL⟩ * ⟨u, huL⟩) * l⁻¹ := by group
      _ = 1 := by rw [hu1]; group
  have hsq2 : (⟨u, huL⟩ * v') * (⟨u, huL⟩ * v') = 1 := by
    calc (⟨u, huL⟩ * v') * (⟨u, huL⟩ * v')
        = ⟨u, huL⟩ * (v' * ⟨u, huL⟩) * v' := by group
      _ = ⟨u, huL⟩ * (⟨u, huL⟩ * v') * v' := by rw [← hcomm]
      _ = (⟨u, huL⟩ * ⟨u, huL⟩) * (v' * v') := by group
      _ = 1 := by rw [hu1, hv'sq, one_mul]
  have himg : ((l * ⟨u, huL⟩ * l⁻¹ : ↥L) : ↥L ⧸ center ↥L) =
      ((⟨u, huL⟩ * v' : ↥L) : ↥L ⧸ center ↥L) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul]
    have h1 : (l : ↥L ⧸ center ↥L) * ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) *
        (l : ↥L ⧸ center ↥L)⁻¹ = w := hy
    rw [h1, hw, hv'img]
  have h2 := Closing.eq_of_mk_eq_of_sq hodd hsq1 hsq2 himg
  exact ⟨u * (v' : H), (v' : H), hvmax, rfl, (l : H), l.2, congrArg Subtype.val h2⟩

theorem fi24in_sol78Generate (hL : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card (center ↥L)))
    (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hbase : Fi24InCoverBase L K u huL)
    (hgen : Sol78Generate (⊤ : Subgroup (↥L ⧸ center ↥L)) (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)) : Sol78Generate L K u := by
  have hu1 := sq_of_orderOf_two huL hu2
  have hK' := commutator_subgroupOf_eq_self hKL hKq
  have huK := fi24in_mem_of_base hodd huL hu2 hbase
  have hX : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = (⊤ : Subgroup ↥L) := by
    have := Group.isPerfect_def.1 hL.1
    rwa [_root_.commutator_def] at this
  intro l hl hmem
  obtain ⟨v, hv, hlv, -⟩ := hmem
  have hcand := (fi24in_mem_vCandidates_iff huK).1 hv.1
  have hvv : v * v = 1 := mul_self_eq_one_of_orderOf_eq_two hcand.2.2
  set x : ↥L := ⟨v, hKL hcand.1⟩ with hxdef
  have hxx : x * x = 1 := Subtype.ext hvv
  have hvY : (x : ↥L ⧸ center ↥L) ∈ vMaximal (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) :=
    (fi24in_mem_vMaximal_iff hodd hK' hKL huL hbase huK (x := x) hcand.1 hxx).1 hv
  set l' : ↥L := ⟨l, hl⟩ with hl'
  have hlx : l' * ⟨u, huL⟩ * l'⁻¹ = ⟨u, huL⟩ * x := Subtype.ext hlv
  have hmemY : (l' : ↥L ⧸ center ↥L) * ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) *
      (l' : ↥L ⧸ center ↥L)⁻¹ ∈ vPairs (⊤ : Subgroup (↥L ⧸ center ↥L)) (bar (K.subgroupOf L))
        ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L) := by
    refine ⟨(x : ↥L ⧸ center ↥L), hvY, ?_, (l' : ↥L ⧸ center ↥L), Subgroup.mem_top _, rfl⟩
    have h1 := congrArg (QuotientGroup.mk (s := center ↥L)) hlx
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul] at h1
    exact h1
  have hgY := hgen (l' : ↥L ⧸ center ↥L) (Subgroup.mem_top _) hmemY
  have hlift := fi24in_sup_conj_eq_top (K := K.subgroupOf L) hX (g := l') hgY
  have := congrArg (Subgroup.map L.subtype) hlift
  rw [Subgroup.map_sup, map_subtype_map_conj, Subgroup.map_subgroupOf_eq_of_le hKL,
    Subgroup.map_top, Subgroup.range_subtype] at this
  exact this

theorem fi24in_local39 (hL : CFSG.IsQuasisimple ↥L) (hodd : Odd (Nat.card (center ↥L)))
    (hKq : CFSG.IsQuasisimple ↥K) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (h35 : K = componentProduct K u)
    (hbase : Fi24InCoverBase L K u huL)
    (hpairs : (vPairs (⊤ : Subgroup (↥L ⧸ center ↥L)) (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)).Nonempty)
    (hgen : Sol78Generate (⊤ : Subgroup (↥L ⧸ center ↥L)) (bar (K.subgroupOf L))
      ((⟨u, huL⟩ : ↥L) : ↥L ⧸ center ↥L)) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u :=
  ⟨fi24in_vPairs_nonempty hodd hKq huL hu2 hKL hKu hbase hpairs,
    fi24in_sol78Fusion39_of_base hodd hKq huL hu2 hKL hKu h35 hbase,
    fi24in_sol78Generate hL hodd hKq huL hu2 hKL hbase hgen⟩

end Cover

end CFSG.EvenSporadicStandard.Induction

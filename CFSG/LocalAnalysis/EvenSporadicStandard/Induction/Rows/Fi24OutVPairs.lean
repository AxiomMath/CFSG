module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Fi24OutDihedral
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSVPairs

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78

section

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem fi24out_twoAdic_subgroupOf_eq {L S : Subgroup H} (hSL : S ≤ L) :
    twoAdic (S.subgroupOf L) = twoAdic S := by
  unfold twoAdic
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSL).toEquiv]

end

namespace Fi24OutLocalData

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
  {huN : u ∈ normalizer (L : Set H)} (D : Fi24OutLocalData H L K u huN)
include D

theorem vPairs_nonempty : (vPairs L K u).Nonempty := by
  classical
  have hodd := D.odd
  have huu := D.u_sq
  set ν := normalizerAction L ⟨u, huN⟩ with hν
  have hνν : ∀ x, ν (ν x) = x := fun x => by
    have := congrArg (fun f : MulAut (↥L ⧸ center ↥L) => f x) D.facts.sq
    simpa using this
  obtain ⟨yb, hm1, hm2, hm3⟩ := D.facts.pair
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective yb
  have hmem : ∀ x : ↥L, u * (x : H) * u⁻¹ ∈ L := fun x => (mem_normalizer_iff.1 huN x).1 x.2
  set uh : ↥L := ⟨u * (h : H) * u⁻¹, hmem h⟩ with huh
  set v : ↥L := uh * h⁻¹ with hv
  set mb : ↥L ⧸ center ↥L := ν (h : ↥L ⧸ center ↥L) * (h : ↥L ⧸ center ↥L)⁻¹ with hmb
  have hνh : ν (h : ↥L ⧸ center ↥L) = (uh : ↥L ⧸ center ↥L) := Closing.act_mk huN h
  have hmbv : mb = (v : ↥L ⧸ center ↥L) := by
    rw [hmb, hνh, hv, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hmbsq : mb * mb = 1 := by
    have h1 : ν mb = mb⁻¹ := by
      rw [hmb, map_mul, map_inv, hνν, mul_inv_rev, inv_inv]
    have h2 : mb = mb⁻¹ := by rw [← h1]; exact hm2.symm
    calc mb * mb = mb * mb⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel mb
  set n := Nat.card ↥(center ↥L) with hn
  have hnodd : Odd n := hodd
  set v₂ : ↥L := v ^ n with hv₂
  have hv₂Y : (v₂ : ↥L ⧸ center ↥L) = mb := by
    rw [hv₂, QuotientGroup.mk_pow, ← hmbv]
    obtain ⟨j, hj⟩ := hnodd
    rw [hj, pow_succ, pow_mul, sq, hmbsq, one_pow, one_mul]
  have hvv : v * v ∈ center ↥L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← hmbv]
    exact hmbsq
  have hv₂sq : v₂ * v₂ = 1 := by
    have h1 : (v * v) ^ n = 1 := by
      have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨v * v, hvv⟩)
      exact congrArg Subtype.val this
    rw [hv₂, ← (Commute.refl v).mul_pow n]
    exact h1
  have hmbfix : mb ∈ fixSubgroup ν := hm2
  have hv₂K : v₂ ∈ K.subgroupOf L := by
    refine mem_of_mk_mem hodd hv₂sq ?_
    rw [hv₂Y, D.bar_eq]
    exact hmbfix
  set w : H := (v₂ : H) with hw
  have hwK : w ∈ K := Subgroup.mem_subgroupOf.1 hv₂K
  have hwsq : w * w = 1 := congrArg (fun z : ↥L => (z : H)) hv₂sq
  have hwu : w * u = u * w := D.K_comm_u w hwK
  have hw1 : w ≠ 1 := by
    intro h1
    have : v₂ = 1 := Subtype.ext h1
    rw [this, QuotientGroup.mk_one] at hv₂Y
    exact hm1 hv₂Y.symm
  set z : ↥L := v₂⁻¹ * v with hz
  have hzc : z ∈ center ↥L := by
    refine QuotientGroup.eq.1 ?_
    rw [hv₂Y, ← hmbv]
  have hzn : z ^ n = 1 := by
    have := pow_card_eq_one' (G := ↥(center ↥L)) (x := ⟨z, hzc⟩)
    exact congrArg Subtype.val this
  set a : H := u * w with ha
  set u' : H := (h : H) * u * (h : H)⁻¹ with hu'
  have haa : a * a = 1 := by
    calc a * a = u * (w * u) * w := by rw [ha]; group
      _ = u * (u * w) * w := by rw [hwu]
      _ = (u * u) * (w * w) := by group
      _ = 1 := by rw [huu, hwsq, one_mul]
  have hu'u' : u' * u' = 1 := by
    calc u' * u' = (h : H) * (u * u) * (h : H)⁻¹ := by rw [hu']; group
      _ = 1 := by rw [huu]; group
  have hvH : (v : H) = u * (h : H) * u⁻¹ * (h : H)⁻¹ := rfl
  have hzH : (z : H) = w⁻¹ * (v : H) := by
    rw [hz, Subgroup.coe_mul, Subgroup.coe_inv]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hu'az : u' = a * (z : H) := by
    rw [hzH, ha, hvH, hu', hui]
    calc (h : H) * u * (h : H)⁻¹ = u * (u * (h : H) * u * (h : H)⁻¹) := by
          calc (h : H) * u * (h : H)⁻¹ = (u * u) * (h : H) * u * (h : H)⁻¹ := by rw [huu, one_mul]
            _ = _ := by group
      _ = u * w * (w⁻¹ * (u * (h : H) * u * (h : H)⁻¹)) := by group
  have haz : a * u' = (z : H) := by
    rw [hu'az, ← mul_assoc, haa, one_mul]
  have hzn' : ((z : H)) ^ n = 1 := by
    have := congrArg (fun y : ↥L => (y : H)) hzn
    simpa using this
  obtain ⟨c, hc, hca⟩ := fi24out_odd_dihedral haa hu'u' hnodd (by rw [haz]; exact hzn')
  rw [haz] at hc
  have hcL : c ∈ L := (Subgroup.zpowers_le.2 z.2) hc
  have hlu : ((c⁻¹ * (h : H)) * u * (c⁻¹ * (h : H))⁻¹) = u * w := by
    calc (c⁻¹ * (h : H)) * u * (c⁻¹ * (h : H))⁻¹ = c⁻¹ * ((h : H) * u * (h : H)⁻¹) * c := by group
      _ = c⁻¹ * (c * a * c⁻¹) * c := by rw [hca, hu']
      _ = u * w := by rw [ha]; group
  have hbarC : bar ((K.subgroupOf L) ⊓ centralizer ({v₂} : Set ↥L)) =
      fixSubgroup ν ⊓ centralizer ({mb} : Set (↥L ⧸ center ↥L)) := by
    ext y
    constructor
    · rintro ⟨c', ⟨hcK, hcv⟩, rfl⟩
      refine ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩
      · show (c' : ↥L ⧸ center ↥L) ∈ fixSubgroup ν
        rw [← D.bar_eq]
        exact mk_mem_bar_of_mem hcK
      · have := mem_centralizer_singleton_iff.1 hcv
        show (c' : ↥L ⧸ center ↥L) * mb = mb * c'
        rw [← hv₂Y, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, this]
    · rintro ⟨hyf, hyc⟩
      rw [← D.bar_eq] at hyf
      obtain ⟨c', hcK, rfl⟩ := mem_bar.1 hyf
      refine ⟨c', ⟨hcK, ?_⟩, rfl⟩
      show c' ∈ centralizer ({v₂} : Set ↥L)
      rw [mem_centralizer_singleton_iff_coe hodd hv₂sq, hv₂Y]
      exact hyc
  have h2adic : twoAdic (K ⊓ centralizer ({w} : Set H)) = twoAdic K := by
    have hS : K ⊓ centralizer ({w} : Set H) ≤ L := inf_le_left.trans D.K_le
    have e1 : (K ⊓ centralizer ({w} : Set H)).subgroupOf L =
        (K.subgroupOf L) ⊓ centralizer ({v₂} : Set ↥L) := by
      ext x
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx1, Subtype.ext hx2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx1, congrArg (fun y : ↥L => (y : H)) hx2⟩
    rw [← fi24out_twoAdic_subgroupOf_eq hS, e1, ← twoAdic_bar hodd, hbarC, hm3, ← D.bar_eq,
      twoAdic_bar hodd, fi24out_twoAdic_subgroupOf_eq D.K_le]
  have hvmax : w ∈ vMaximal K u := by
    refine ⟨⟨Subgroup.mem_sup_left hwK, fun hc => ?_, orderOf_eq_prime (by rwa [pow_two]) hw1⟩,
      fun v' _ => ?_⟩
    · obtain ⟨-, hcomm⟩ := mem_center_map_iff.1 hc
      have hcen : (⟨mb, hmbfix⟩ : ↥(fixSubgroup ν)) ∈ center ↥(fixSubgroup ν) := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨y, hy⟩
        rw [← D.bar_eq] at hy
        obtain ⟨c', hcK, rfl⟩ := mem_bar.1 hy
        refine Subtype.ext ?_
        show (c' : ↥L ⧸ center ↥L) * mb = mb * c'
        rw [← hv₂Y, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext (hcomm (c' : H) (Subgroup.mem_subgroupOf.1 hcK)).symm
      rw [D.facts.center_bot, Subgroup.mem_bot] at hcen
      exact hm1 (congrArg Subtype.val hcen)
    · exact (twoAdic_mono inf_le_left).trans h2adic.ge
  exact vPairs_nonempty_of_mem hvmax ⟨c⁻¹ * (h : H), mul_mem (inv_mem hcL) h.2, hlu⟩

end Fi24OutLocalData

theorem fi24out_hyp38 {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}
    (h35 : K = componentProduct K u) (hne : (vPairs L K u).Nonempty)
    (hfus : Sol78Fusion39 L K u) (hgen : Sol78Generate L K u) :
    centralizer ({u} : Set H) ≤ normalizer (L : Set H) := by
  have hK : ∀ g ∈ centralizer ({u} : Set H), g * u * g⁻¹ = u ∧ K.map (conjHom g) = K := fun g hg =>
    map_conj_eq_of_hyp35 h35 hg
  have h1 : ∀ g ∈ centralizer ({u} : Set H), ∀ w ∈ vPairs L K u, g * w * g⁻¹ ∈ vPairs L K u := by
    intro g hg w hw
    obtain ⟨v, hv, rfl, l, hl, hlw⟩ := hw
    obtain ⟨hug, hKg⟩ := hK g hg
    obtain ⟨c, hc, hcv⟩ := hfus v hv g hg
    have hcu : c * u * c⁻¹ = u := by
      have := mem_centralizer_singleton_iff.1 hc.2
      rw [this]
      group
    have hgv : g * (u * v) * g⁻¹ = u * (g * v * g⁻¹) := by
      calc g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) := by group
        _ = u * (g * v * g⁻¹) := by rw [hug]
    refine ⟨g * v * g⁻¹, vMaximal_conj hKg hug hv, hgv, c * l, mul_mem hc.1 hl, ?_⟩
    calc c * l * u * (c * l)⁻¹ = c * (l * u * l⁻¹) * c⁻¹ := by group
      _ = c * (u * v) * c⁻¹ := by rw [hlw]
      _ = (c * u * c⁻¹) * (c * v * c⁻¹) := by group
      _ = u * (c * v * c⁻¹) := by rw [hcu]
      _ = u * (g * v * g⁻¹) := by rw [hcv]
      _ = g * (u * v) * g⁻¹ := hgv.symm
  intro g hg
  obtain ⟨w, hw⟩ := hne
  obtain ⟨hug, hKg⟩ := hK g hg
  have hw' := h1 g hg w hw
  have hw0 := hw
  obtain ⟨-, -, -, l, hl, hlw⟩ := hw
  obtain ⟨-, -, -, l', hl', hlw'⟩ := hw'
  have hL1 := hgen l hl (by rw [hlw]; exact hw0)
  have hL2 := hgen l' hl' (by rw [hlw']; exact h1 g hg w hw0)
  have hcp1 : componentProduct K w = K.map (conjHom l) := by
    rw [← hlw, componentProduct_conj K u l, ← h35]
  have hcp2 : componentProduct K (g * w * g⁻¹) = K.map (conjHom l') := by
    rw [← hlw', componentProduct_conj K u l', ← h35]
  have e : (K.map (conjHom l)).map (conjHom g) = K.map (conjHom l') := by
    rw [← hcp1, ← componentProduct_conj, hcp2]
  have hL : L.map (conjHom g) = L := by
    calc L.map (conjHom g) = (K ⊔ K.map (conjHom l)).map (conjHom g) := by rw [hL1]
      _ = K.map (conjHom g) ⊔ (K.map (conjHom l)).map (conjHom g) := Subgroup.map_sup _ _ _
      _ = K ⊔ K.map (conjHom l') := by rw [hKg, e]
      _ = L := hL2
  exact Fi24OutLocalData.mem_normalizer_of_map_conj_eq hL

end CFSG.EvenSporadicStandard.Induction

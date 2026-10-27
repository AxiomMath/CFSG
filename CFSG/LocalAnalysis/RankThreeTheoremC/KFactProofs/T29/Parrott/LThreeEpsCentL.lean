module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsNilp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsPairs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
open CFSG.HardMathSupport.Solomon.Coordinator

section Group

variable {G : Type*} [Group G]

theorem exists_pow_mul_zpow {A : Subgroup G} {w : G} (hw : w ∈ normalizer (A : Set G)) {a : G}
    (ha : a ∈ A) (k : ℤ) (n : ℕ) : ∃ a' ∈ A, (a * w ^ k) ^ n = a' * w ^ (k * n) := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨a', ha', h⟩ := ih
    have hwn : w ^ (k * n) ∈ normalizer (A : Set G) := zpow_mem hw _
    have hc : w ^ (k * n) * a * (w ^ (k * n))⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.1 hwn a).1 ha
    refine ⟨a' * (w ^ (k * n) * a * (w ^ (k * n))⁻¹), mul_mem ha' hc, ?_⟩
    rw [pow_succ, h, show k * ((n + 1 : ℕ) : ℤ) = k * n + k by push_cast; ring, zpow_add]
    group

end Group

section Image

variable {X : Type} [Group X] {L : Subgroup X} {π : Bool} {p f : ℕ} {K : Type} [Field K]
  {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

@[expose] def centImage (ν : ↥(slPi π 3 (p ^ f) K) →* ↥L) (y : GL (Fin 3) K) : Subgroup X :=
  ((slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))).subgroupOf
    (slPi π 3 (p ^ f) K)).map (L.subtype.comp ν)

theorem mem_centImage {y : GL (Fin 3) K} {b : X} :
    b ∈ centImage ν y ↔ ∃ s : ↥(slPi π 3 (p ^ f) K), (s : GL (Fin 3) K) * y = y * s ∧
      ((ν s : ↥L) : X) = b := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1
      (Subgroup.mem_subgroupOf.1 hs)).2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨s.2,
      mem_centralizer_singleton_iff.2 hs⟩), rfl⟩

theorem isCyclic_centImage {y : GL (Fin 3) K} (hT : IsTypeThree π (p ^ f) K y) :
    IsCyclic ↥(centImage ν y : Subgroup X) := by
  haveI := hT.cyclic
  set C := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))
  have hle : C ≤ slPi π 3 (p ^ f) K := inf_le_left
  haveI : IsCyclic ↥(C.subgroupOf (slPi π 3 (p ^ f) K)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

theorem IsLiftAt.centImage_le {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) :
    centImage ν y ≤ L ⊓ centralizer ({x} : Set X) := by
  intro b hb
  obtain ⟨s, hs, rfl⟩ := mem_centImage.1 hb
  exact Subgroup.mem_inf.2 ⟨(ν s).2, mem_centralizer_singleton_iff.2
    (hx.commute_of_commute hs.symm)⟩

theorem conj_mem_centImage {y : GL (Fin 3) K} {w : ↥(slPi π 3 (p ^ f) K)}
    (hw : (w : GL (Fin 3) K) ∈ centMod (slPi π 3 (p ^ f) K) y) {b : X}
    (hb : b ∈ centImage ν y) :
    ((ν w : ↥L) : X) * b * ((ν w : ↥L) : X)⁻¹ ∈ centImage ν y := by
  obtain ⟨s, hs, rfl⟩ := mem_centImage.1 hb
  refine mem_centImage.2 ⟨w * s * w⁻¹, ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_commute_of_mem_centMod hw hs
  · rw [map_mul, map_mul, map_inv]
    rfl

theorem LModel.not_mem_centImage (M : LModel L π p f K ν) {y : GL (Fin 3) K}
    {w : ↥(slPi π 3 (p ^ f) K)}
    (hw : (w : GL (Fin 3) K) ∉ slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K))) :
    ((ν w : ↥L) : X) ∉ centImage ν y := by
  intro hmem
  obtain ⟨s, hs, hsw⟩ := mem_centImage.1 hmem
  have h1 : ν (w * s⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [hsw, mul_inv_cancel]
  have h2 := M.ker_scalar _ h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  apply hw
  refine Subgroup.mem_inf.2 ⟨w.2, mem_centralizer_singleton_iff.2 ?_⟩
  have hc := commute_of_mem_statedScalars h2 y
  calc (w : GL (Fin 3) K) * y = ((w : GL (Fin 3) K) * (s : GL (Fin 3) K)⁻¹) * (s * y) := by group
    _ = ((w : GL (Fin 3) K) * (s : GL (Fin 3) K)⁻¹) * (y * s) := by rw [hs]
    _ = y * ((w : GL (Fin 3) K) * (s : GL (Fin 3) K)⁻¹) * s := by rw [← mul_assoc, ← hc]
    _ = y * w := by group

theorem LModel.exists_conj_ne (M : LModel L π p f K ν) {y : GL (Fin 3) K}
    (hT : IsTypeThree π (p ^ f) K y) {w : ↥(slPi π 3 (p ^ f) K)}
    (hC3 : Nat.card ↥(slPi π 3 (p ^ f) K ⊓
      centralizer ({y, (w : GL (Fin 3) K)} : Set (GL (Fin 3) K))) = 3) :
    ∃ b ∈ (centImage ν y : Subgroup X),
      ((ν w : ↥L) : X) * b * ((ν w : ↥L) : X)⁻¹ ≠ b := by
  by_contra hcon
  push Not at hcon
  refine hT.not_forall_conj_mem M.piField M.modThree M.two_lt w.2 hC3 fun t ht => ?_
  have ht' := ht
  have hb : ((ν ⟨t, (Subgroup.mem_inf.1 ht).1⟩ : ↥L) : X) ∈ centImage ν y :=
    mem_centImage.2 ⟨⟨t, (Subgroup.mem_inf.1 ht).1⟩,
      mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).2, rfl⟩
  have h1 := hcon _ hb
  have h2 : ν (w * ⟨t, (Subgroup.mem_inf.1 ht).1⟩ * w⁻¹ *
      ⟨t, (Subgroup.mem_inf.1 ht).1⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, OneMemClass.coe_one]
    rw [h1, mul_inv_cancel]
  have h3 := M.ker_scalar _ h2
  simpa using h3

end Image

section Cover

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} [hLn : L.Normal] {π : Bool} {p f : ℕ}
  {K : Type} [Field K] {ν : ↥(slPi π 3 (p ^ f) K) →* ↥L}

theorem LModel.centralizer_le_centImage (M : LModel L π p f K ν) (hinj : Function.Injective ν)
    {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y) :
    L ⊓ centralizer ({x} : Set X) ≤ centImage ν y := by
  intro b hb
  obtain ⟨hbL, hbx⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨s, hs⟩ := M.surj ⟨b, hbL⟩
  have hsb : ((ν s : ↥L) : X) = b := by rw [hs]
  have h1 := hx.act s (M.conjBy hx.mem s) (M.coe_conjBy hx.mem s)
  rw [hsb] at h1
  have h2 : x * b * x⁻¹ = b := by
    rw [← mem_centralizer_singleton_iff.1 hbx, mul_inv_cancel_right]
  rw [h2, ← hsb] at h1
  have h3 : M.conjBy hx.mem s = s := hinj (Subtype.ext h1.symm)
  refine mem_centImage.2 ⟨s, ?_, hsb⟩
  have h4 : y * (s : GL (Fin 3) K) * y⁻¹ = s := by
    rw [← M.coe_conjBy hx.mem s, h3]
  calc (s : GL (Fin 3) K) * y = y * (s : GL (Fin 3) K) * y⁻¹ * y := by rw [h4]
    _ = y * s := by group

theorem LModel.commute_of_cover (M : LModel L π p f K ν) (hinj : Function.Injective ν)
    (hZ3 : Nat.card (center ↥L) ∣ 3) {x : X} {y : GL (Fin 3) K} (hx : IsLiftAt ν x y)
    (hT : IsTypeThree π (p ^ f) K y) :
    ∃ v : X, v ∈ (center ↥L).map L.subtype ∧ v ^ 3 = 1 ∧ v ≠ 1 ∧ v * x = x * v ∧
      ∀ g ∈ centralizer ({x} : Set X), g * v * g⁻¹ = v := by
  obtain ⟨w₀, hw₀L, hw₀o, hw₀C, hcent, hC3⟩ := hT.exists_w
  have hw₀cm : w₀ ∈ centMod (slPi π 3 (p ^ f) K) y := by
    rw [hcent]
    exact le_sup_right (a := slPi π 3 (p ^ f) K ⊓ centralizer ({y} : Set (GL (Fin 3) K)))
      (Subgroup.mem_zpowers w₀)
  obtain ⟨c, hc, hyw⟩ := exists_conj_eq_scalar_mul hw₀cm
  have hcL : c ∈ slPi π 3 (p ^ f) K := by
    have h1 : c = y * w₀ * y⁻¹ * w₀⁻¹ := by rw [hyw, mul_inv_cancel_right]
    rw [h1]
    exact mul_mem (conj_mem_slPi M.hπ hx.mem hw₀L) (inv_mem hw₀L)
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hw₀C
    refine Subgroup.mem_inf.2 ⟨hw₀L, mem_centralizer_singleton_iff.2 ?_⟩
    rw [one_mul] at hyw
    calc w₀ * y = y * w₀ * y⁻¹ * y := by rw [hyw]
      _ = y * w₀ := by group
  set sw : ↥(slPi π 3 (p ^ f) K) := ⟨w₀, hw₀L⟩
  set sc : ↥(slPi π 3 (p ^ f) K) := ⟨c, hcL⟩
  set w : X := ((ν sw : ↥L) : X)
  set v : X := ((ν sc : ↥L) : X)
  have hxw : x * w * x⁻¹ = v * w := by
    have h := hx.act sw (sc * sw) (by simp only [Subgroup.coe_mul]; exact hyw.symm)
    rw [h, map_mul]
    rfl
  have hscZ : sc ∈ center ↥(slPi π 3 (p ^ f) K) := M.mem_center_of_mem_statedScalars hc
  have hvZ : v ∈ (center ↥L).map L.subtype := ⟨ν sc, M.map_mem_center hscZ, rfl⟩
  have hvc : ∀ l ∈ L, l * v = v * l := fun l hl =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 (M.map_mem_center hscZ) ⟨l, hl⟩)
  have hv3 : v ^ 3 = 1 := by
    obtain ⟨γ, rfl⟩ := hc
    have h1 := ((mem_slPi_iff M.hπ).1 hcL).2
    rw [det_scalar] at h1
    have hγ : γ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
    have : sc ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow]
      show (Matrix.GeneralLinearGroup.scalar (Fin 3) γ) ^ 3 = 1
      rw [← map_pow, hγ, map_one])
    rw [← Subgroup.coe_pow, ← map_pow, this, map_one, Subgroup.coe_one]
  have hv1 : v ≠ 1 := by
    intro h1
    apply hc1
    have : sc = 1 := hinj (by rw [map_one]; exact Subtype.ext h1)
    exact congrArg Subtype.val this
  have hvx : v * x = x * v := by
    have := hx.commute_of_commute (s := sc) (commute_of_mem_statedScalars hc y)
    exact this
  refine ⟨v, hvZ, hv3, hv1, hvx, fun g hg => ?_⟩
  have hZv : (center ↥L).map L.subtype = zpowers v := by
    refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hvZ) ?_).symm
    rw [Subgroup.card_map_of_injective L.subtype_injective, Nat.card_zpowers,
      orderOf_eq_prime hv3 hv1]
    exact Nat.le_of_dvd (by norm_num) hZ3
  have hgv : g * v * g⁻¹ ∈ zpowers v := by
    rw [← hZv]
    exact (normal_map_center_subtype L).conj_mem v hvZ g
  by_contra hne
  have hgv' : g * v * g⁻¹ = v⁻¹ := by
    rcases eq_of_mem_zpowers_of_pow_three hv3 hgv with h1 | h1 | h1
    · exfalso
      apply hv1
      calc v = g⁻¹ * (g * v * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hne
    · rw [h1]
      calc v ^ 2 = v ^ 3 * v⁻¹ := by group
        _ = v⁻¹ := by rw [hv3, one_mul]
  set A := L ⊓ centralizer ({x} : Set X) with hAdef
  have hAeq : A = centImage ν y := le_antisymm (M.centralizer_le_centImage hinj hx)
    hx.centImage_le
  haveI hAcyc : IsCyclic ↥A := by rw [hAeq]; exact isCyclic_centImage hT
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have := (IsCyclic.commGroup (α := ↥A)).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  have hwA : w ∈ normalizer (A : Set X) := by
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    rw [hAeq] at ha ⊢
    exact conj_mem_centImage hw₀cm ha
  have hgA : g ∈ normalizer (A : Set X) := by
    refine mem_normalizer_of_conj_mem fun a ha => ?_
    obtain ⟨haL, hax⟩ := Subgroup.mem_inf.1 ha
    refine Subgroup.mem_inf.2 ⟨hLn.conj_mem a haL g, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := mem_centralizer_singleton_iff.1 hax
    have h2 := mem_centralizer_singleton_iff.1 hg
    calc g * a * g⁻¹ * x = g * a * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = g * a * x * g⁻¹ := by
          rw [show g⁻¹ * x * g = x by rw [mul_assoc, ← h2, inv_mul_cancel_left]]
      _ = g * (a * x) * g⁻¹ := by group
      _ = g * (x * a) * g⁻¹ := by rw [h1]
      _ = g * x * a * g⁻¹ := by group
      _ = x * g * a * g⁻¹ := by rw [h2]
      _ = x * (g * a * g⁻¹) := by group
  have hw3 : ∀ a ∈ A, w ^ 3 * a * (w ^ 3)⁻¹ = a := by
    intro a _
    have hw₀3 : w₀ ^ 3 = 1 := by
      have := pow_orderOf_eq_one w₀
      rwa [hw₀o] at this
    have hsw3 : sw ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact hw₀3)
    have : w ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow, hsw3, map_one, Subgroup.coe_one]
    rw [this, one_mul, inv_one, mul_one]
  have hne' : ∃ a ∈ A, w * a * w⁻¹ ≠ a := by
    obtain ⟨b, hb, hb'⟩ := M.exists_conj_ne (X := X) hT (w := sw) hC3
    exact ⟨b, hAeq ▸ hb, hb'⟩
  refine false_of_conj_inv hAcyc hwA hgA hw3 hne' fun a ha => ?_
  set u := g * w * g⁻¹ with hu
  have hwL : w ∈ L := (ν sw).2
  have huL : u ∈ L := hLn.conj_mem w hwL g
  have hxu : x * u * x⁻¹ = v⁻¹ * u := by
    have h2 := mem_centralizer_singleton_iff.1 hg
    calc x * u * x⁻¹ = g * (x * w * x⁻¹) * g⁻¹ := by
          rw [hu]
          calc x * (g * w * g⁻¹) * x⁻¹ = (x * g) * w * (x * g)⁻¹ := by group
            _ = (g * x) * w * (g * x)⁻¹ := by rw [h2]
            _ = g * (x * w * x⁻¹) * g⁻¹ := by group
      _ = g * (v * w) * g⁻¹ := by rw [hxw]
      _ = (g * v * g⁻¹) * u := by rw [hu]; group
      _ = v⁻¹ * u := by rw [hgv']
  have hvu : u * v = v * u := hvc u huL
  have key : x * (u * w) * x⁻¹ = u * w := by
    calc x * (u * w) * x⁻¹ = (x * u * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (v⁻¹ * u) * (v * w) := by rw [hxu, hxw]
      _ = v⁻¹ * (u * v) * w := by group
      _ = v⁻¹ * (v * u) * w := by rw [hvu]
      _ = u * w := by group
  have hc' : u * w ∈ A := by
    refine Subgroup.mem_inf.2 ⟨mul_mem huL hwL, mem_centralizer_singleton_iff.2 ?_⟩
    calc u * w * x = x * (u * w) * x⁻¹ * x := by rw [key]
      _ = x * (u * w) := by group
  have hw'a : w⁻¹ * a * w ∈ A := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hwA) a).1 ha
    rwa [inv_inv] at this
  calc u * a * u⁻¹ = (u * w) * (w⁻¹ * a * w) * (u * w)⁻¹ := by group
    _ = (w⁻¹ * a * w) * (u * w) * (u * w)⁻¹ := by rw [hAcomm _ hc' _ hw'a]
    _ = w⁻¹ * a * w := by group

end Cover

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott

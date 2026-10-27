module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CentralOdd
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterKlein

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

abbrev conjActNe {P S : Subgroup G} (hPS : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    MulAction ↥P {x : ↥S // x ≠ 1} where
  smul g x := ⟨⟨g * x.1 * (g : G)⁻¹, hPS g g.2 x.1 x.1.2⟩, fun h => x.2 (by
    have h1 : (g : G) * x.1 * (g : G)⁻¹ = 1 := congrArg Subtype.val h
    have h2 : ((x.1 : ↥S) : G) = 1 := by
      calc ((x.1 : ↥S) : G) = (g : G)⁻¹ * ((g : G) * x.1 * (g : G)⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact Subtype.ext h2)⟩
  one_smul x := Subtype.ext (Subtype.ext (by
    change (1 : G) * x.1 * (1 : G)⁻¹ = x.1
    simp))
  mul_smul g h x := Subtype.ext (Subtype.ext (by
    change ((g : G) * h) * x.1 * ((g : G) * h)⁻¹ = g * ((h : G) * x.1 * (h : G)⁻¹) * (g : G)⁻¹
    group))

theorem card_orbit_conjActNe_mul [Finite G] {P S : Subgroup G}
    (hPS : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) (x : {x : ↥S // x ≠ 1}) :
    letI := conjActNe hPS
    Nat.card (MulAction.orbit ↥P x) *
      Nat.card ↥(P ⊓ Subgroup.centralizer ({((x.1 : ↥S) : G)} : Set G)) = Nat.card P := by
  let := conjActNe hPS
  have hstab : MulAction.stabilizer ↥P x =
      (Subgroup.centralizer ({((x.1 : ↥S) : G)} : Set G)).subgroupOf P := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : (g : G) * x.1 * (g : G)⁻¹ = x.1 := congrArg (fun z : {x : ↥S // x ≠ 1} =>
        ((z : ↥S) : G)) h
      calc (g : G) * x.1 = (g : G) * x.1 * (g : G)⁻¹ * g := by group
        _ = x.1 * g := by rw [h1]
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      show (g : G) * x.1 * (g : G)⁻¹ = x.1
      calc (g : G) * x.1 * (g : G)⁻¹ = x.1 * g * (g : G)⁻¹ := by rw [h]
        _ = x.1 := by group
  have hRcard : Nat.card (MulAction.stabilizer ↥P x) =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({((x.1 : ↥S) : G)} : Set G)) := by
    rw [hstab, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← hRcard, ← Nat.card_prod, Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥P x)]

theorem pow_dvd_card_sub_one_of_orbit [Finite G] {p : ℕ} (hp : p.Prime) {P S : Subgroup G}
    (hPp : IsPGroup p P) (hPS : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) {k : ℕ}
    (hb : ∀ x ∈ S, x ≠ 1 →
      Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) * p ^ k ≤ Nat.card P) :
    p ^ k ∣ Nat.card S - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hPp
  let := conjActNe hPS
  have horb : ∀ x : {x : ↥S // x ≠ 1}, p ^ k ∣ Nat.card (MulAction.orbit ↥P x) := by
    intro x
    have horbit := card_orbit_conjActNe_mul hPS x
    rw [ha] at horbit
    have hdvd : Nat.card (MulAction.orbit ↥P x) ∣ p ^ a := Dvd.intro _ horbit
    have hRpos : 0 < Nat.card ↥(P ⊓ Subgroup.centralizer ({((x.1 : ↥S) : G)} : Set G)) :=
      Nat.card_pos
    have hx1 : ((x.1 : ↥S) : G) ≠ 1 := fun h => x.2 (Subtype.ext h)
    have hRb := hb _ x.1.2 hx1
    have hle : p ^ k ≤ Nat.card (MulAction.orbit ↥P x) := by
      by_contra hlt
      push Not at hlt
      rw [ha] at hRb
      nlinarith
    exact pow_dvd_of_le_of_dvd_pow hp hdvd hle
  have hX := dvd_card_of_forall_dvd_card_orbit (G := ↥P) (X := {x : ↥S // x ≠ 1}) horb
  have hXcard : Nat.card {x : ↥S // x ≠ 1} + 1 = Nat.card S := by
    classical
    rw [← Finite.card_option]
    exact Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥S))
  rw [← hXcard, Nat.add_sub_cancel]
  exact hX

theorem card_le_card_sub_one_mul [Finite G] {P S : Subgroup G}
    (hPS : ∀ g ∈ P, ∀ x ∈ S, g * x * g⁻¹ ∈ S) {x : G} (hxS : x ∈ S) (hx1 : x ≠ 1) :
    Nat.card P ≤ (Nat.card S - 1) * Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) := by
  let := conjActNe hPS
  set x' : {x : ↥S // x ≠ 1} := ⟨⟨x, hxS⟩, fun h => hx1 (congrArg Subtype.val h)⟩
  have h := card_orbit_conjActNe_mul hPS x'
  have hXcard : Nat.card {x : ↥S // x ≠ 1} + 1 = Nat.card S := by
    classical
    rw [← Finite.card_option]
    exact Nat.card_congr (Equiv.optionSubtypeNe (1 : ↥S))
  have hle : Nat.card (MulAction.orbit ↥P x') ≤ Nat.card S - 1 := by
    rw [← hXcard, Nat.add_sub_cancel]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [← h]
  exact Nat.mul_le_mul_right _ hle

@[expose] def omegaCenter (T : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ T ∧ (∀ g ∈ T, g * x = x * g) ∧ x * x = 1}
  one_mem' := ⟨T.one_mem, fun g _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haT, hac, ha2⟩ ⟨hbT, hbc, hb2⟩
    refine ⟨T.mul_mem haT hbT, fun g hg => ?_, ?_⟩
    · calc g * (a * b) = (g * a) * b := by group
        _ = (a * g) * b := by rw [hac g hg]
        _ = a * (g * b) := by group
        _ = a * (b * g) := by rw [hbc g hg]
        _ = a * b * g := by group
    · have hab : a * b = b * a := (hac b hbT).symm
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haT, hac, ha2⟩
    have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    refine ⟨T.inv_mem haT, fun g hg => ?_, ?_⟩
    · rw [hai]
      exact hac g hg
    · rw [hai]
      exact ha2

theorem omegaCenter_le (T : Subgroup G) : omegaCenter T ≤ T := fun _ hx => hx.1

theorem conj_mem_omegaCenter {T : Subgroup G} {c : G}
    (hc : ∀ x ∈ T, c * x * c⁻¹ ∈ T) (hc' : ∀ x ∈ T, c⁻¹ * x * c ∈ T) {x : G}
    (hx : x ∈ omegaCenter T) : c * x * c⁻¹ ∈ omegaCenter T := by
  obtain ⟨hxT, hxc, hx2⟩ := hx
  refine ⟨hc x hxT, fun g hg => ?_, ?_⟩
  · have h1 := hxc (c⁻¹ * g * c) (hc' g hg)
    calc g * (c * x * c⁻¹) = c * ((c⁻¹ * g * c) * x) * c⁻¹ := by group
      _ = c * (x * (c⁻¹ * g * c)) * c⁻¹ := by rw [h1]
      _ = c * x * c⁻¹ * g := by group
  · calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group

theorem exists_mem_omegaCenter [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T)
    (hne : T ≠ ⊥) : ∃ x ∈ omegaCenter T, x ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥T := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact hne
  have hcen := hT.center_nontrivial
  obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥T))
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨m, hm⟩ := hT z
  obtain ⟨j, hj2, hj1⟩ := exists_involution_pow (x := z) hm hz1'
  refine ⟨((z ^ j : ↥T) : G), ⟨(z ^ j).2, fun g hg => ?_, ?_⟩, ?_⟩
  · have hc := Subgroup.mem_center_iff.1 hz ⟨g, hg⟩
    have hc' : (⟨g, hg⟩ : ↥T) * z ^ j = z ^ j * ⟨g, hg⟩ := (Commute.pow_right hc j).eq
    exact congrArg Subtype.val hc'
  · exact congrArg Subtype.val hj2
  · intro h
    exact hj1 (Subtype.ext h)

@[expose] def conjInvol {O : Subgroup G} {t : G} (ht : t * t = 1)
    (hO : ∀ x ∈ O, t * x * t⁻¹ ∈ O) : MulAut ↥O where
  toFun x := ⟨t * x * t⁻¹, hO x x.2⟩
  invFun x := ⟨t * x * t⁻¹, hO x x.2⟩
  left_inv x := by
    apply Subtype.ext
    show t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  right_inv x := by
    apply Subtype.ext
    show t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  map_mul' a b := by
    apply Subtype.ext
    show t * ((a : G) * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹)
    group

theorem exists_sylow_normalized_of_involution [Finite G] {O : Subgroup G} {t : G}
    (ht : t * t = 1) (hO : ∀ x ∈ O, t * x * t⁻¹ ∈ O) :
    ∃ T : Sylow 2 ↥O, ∀ x ∈ (T : Subgroup ↥O),
      (⟨t * x * t⁻¹, hO x x.2⟩ : ↥O) ∈ (T : Subgroup ↥O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := conjInvol ht hO with hφ
  have hφφ : φ * φ = 1 := by
    ext x
    show t * (t * (x : G) * t⁻¹) * t⁻¹ = x
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [hti]
    calc t * (t * (x : G) * t) * t = (t * t) * x * (t * t) := by group
      _ = x := by rw [ht]; group
  let f : Sylow 2 ↥O → Sylow 2 ↥O := fun T => φ • T
  have hf : ∀ T, f (f T) = T := by
    intro T
    show φ • (φ • T) = T
    rw [← mul_smul, hφφ, one_smul]
  have h := card_fix_modEq_two f hf
  have h1 := card_sylow_modEq_one 2 ↥O
  have hfix : Nat.card {T : Sylow 2 ↥O // f T = T} ≠ 0 := by
    intro h0
    rw [h0] at h
    have := h1.symm.trans h
    exact absurd this (by decide)
  obtain ⟨⟨T, hT⟩⟩ := Nat.card_ne_zero.1 hfix |>.1
  refine ⟨T, fun x hx => ?_⟩
  have h2 : φ x ∈ ((φ • T : Sylow 2 ↥O) : Subgroup ↥O) := by
    rw [Sylow.pointwise_smul_def]
    exact Subgroup.smul_mem_pointwise_smul x φ _ hx
  have h3 : (φ • T : Sylow 2 ↥O) = T := hT
  rw [h3] at h2
  exact h2

theorem card_le_sq_of_involution [Finite G] {Z : Subgroup G}
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZ2 : ∀ a ∈ Z, a * a = 1) {t : G}
    (ht : t * t = 1) (htZ : ∀ x ∈ Z, t * x * t⁻¹ ∈ Z) :
    Nat.card Z ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({t} : Set G)) ^ 2 := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let φ : ↥Z →* ↥Z :=
    { toFun := fun z => ⟨z * (t * z * t⁻¹), Z.mul_mem z.2 (htZ z z.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show (a : G) * b * (t * (a * b) * t⁻¹) =
          (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹))
        have hc := hZab b b.2 (t * a * t⁻¹) (htZ a a.2)
        calc (a : G) * b * (t * (a * b) * t⁻¹) = a * (b * (t * a * t⁻¹)) * (t * b * t⁻¹) := by
              group
          _ = a * ((t * a * t⁻¹) * b) * (t * b * t⁻¹) := by rw [hc]
          _ = (a * (t * a * t⁻¹)) * (b * (t * b * t⁻¹)) := by group }
  have hmem : ∀ z : ↥Z, (z : G) ∈ Subgroup.centralizer ({t} : Set G) ↔ t * z * t⁻¹ = z := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc t * (z : G) * t⁻¹ = (z * t) * t⁻¹ := by rw [h]
        _ = z := by group
    · intro h
      calc (z : G) * t = (t * z * t⁻¹) * t := by rw [h]
        _ = t * z := by group
  have hker : Nat.card φ.ker ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({t} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun z => ⟨((z : ↥Z) : G),
      Subgroup.mem_inf.2 ⟨(z : ↥Z).2, ?_⟩⟩) ?_
    · rw [hmem]
      have h1 : (z : ↥Z) * (⟨t * (z : ↥Z) * t⁻¹, htZ _ (z : ↥Z).2⟩ : ↥Z) = 1 := z.2
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul, Subgroup.coe_one] at h2
      have h3 := hZ2 _ (z : ↥Z).2
      calc t * ((z : ↥Z) : G) * t⁻¹ = ((z : ↥Z) * (z : ↥Z)) * (t * (z : ↥Z) * t⁻¹) := by
            rw [h3, one_mul]
        _ = (z : ↥Z) * ((z : ↥Z) * (t * (z : ↥Z) * t⁻¹)) := by group
        _ = (z : ↥Z) := by rw [h2, mul_one]
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
  have hrange : Nat.card φ.range ≤ Nat.card ↥(Z ⊓ Subgroup.centralizer ({t} : Set G)) := by
    refine Nat.card_le_card_of_injective (fun m => ⟨((m : ↥Z) : G),
      Subgroup.mem_inf.2 ⟨(m : ↥Z).2, ?_⟩⟩) ?_
    · obtain ⟨z, hz⟩ := m.2
      rw [hmem, ← hz]
      show t * ((z : G) * (t * z * t⁻¹)) * t⁻¹ = (z : G) * (t * z * t⁻¹)
      have hc := hZab z z.2 (t * z * t⁻¹) (htZ z z.2)
      have htt : t * (t * (z : G) * t⁻¹) * t⁻¹ = z := by
        calc t * (t * (z : G) * t⁻¹) * t⁻¹ = (t * t) * z * (t⁻¹ * t⁻¹) := by group
          _ = z := by
            rw [ht, show t⁻¹ * t⁻¹ = (t * t)⁻¹ by group, ht]
            group
      calc t * ((z : G) * (t * z * t⁻¹)) * t⁻¹
          = (t * z * t⁻¹) * (t * (t * z * t⁻¹) * t⁻¹) := by group
        _ = (t * z * t⁻¹) * z := by rw [htt]
        _ = (z : G) * (t * z * t⁻¹) := hc.symm
    · intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
  have htot := Subgroup.card_ker_mul_card_range φ
  rw [← htot, sq]
  exact Nat.mul_le_mul hker hrange

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance

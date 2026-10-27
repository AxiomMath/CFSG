module

public import CFSG.ClassicalInvolution.Q3.Q3PlanOrthChain

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open
open scoped MatrixGroups commutatorElement

section Finite

theorem exists_commutator_mul_of_pow_three : ∀ x : SL(2, ZMod 3), x ^ 3 = 1 → x ≠ 1 →
    ∀ y : SL(2, ZMod 3), y ^ 4 = 1 →
      ∃ q₁ q₂ : SL(2, ZMod 3), q₁ ^ 4 = 1 ∧ q₂ ^ 4 = 1 ∧ y = ⁅x, q₁⁆ * ⁅x, q₂⁆ := by
  decide +kernel

theorem sl2ThreeQ8_le_commutator_zpowers {x : SL(2, ZMod 3)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    sl2ThreeQ8 ≤ ⁅Subgroup.zpowers x, sl2ThreeQ8⁆ := by
  intro y hy
  obtain ⟨q₁, q₂, h₁, h₂, rfl⟩ := exists_commutator_mul_of_pow_three x hx3 hx1 y hy
  exact Subgroup.mul_mem _
    (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) h₁)
    (Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) h₂)

theorem eq_or_eq_inv_of_commute_order_four : ∀ x y : SL(2, ZMod 3), x ^ 4 = 1 → x ^ 2 ≠ 1 →
    y ^ 4 = 1 → y ^ 2 ≠ 1 → x * y = y * x → y = x ∨ y = x⁻¹ := by
  decide +kernel

theorem exists_order_four_sl2Three : ∃ x : SL(2, ZMod 3), x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by
  decide +kernel

end Finite

section Twin

variable {G : Type*} [Group G]

theorem exists_cubes_of_mulEquiv {A : Subgroup G} (eA : SL(2, ZMod 3) ≃* A) {a : G} (ha : a ∈ A) :
    ∃ u₁ ∈ A, ∃ u₂ ∈ A, ∃ u₃ ∈ A, u₁ ^ 3 = 1 ∧ u₂ ^ 3 = 1 ∧ u₃ ^ 3 = 1 ∧ a = u₁ * u₂ * u₃ := by
  obtain ⟨g, hg⟩ := eA.surjective ⟨a, ha⟩
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := sl2Three_exists_cubes g
  have hcube : ∀ w : SL(2, ZMod 3), w ^ 3 = 1 → ((eA w : A) : G) ^ 3 = 1 := fun w hw => by
    rw [← Subgroup.coe_pow, ← map_pow, hw, map_one]
    rfl
  refine ⟨(eA x : A), (eA x).2, (eA y : A), (eA y).2, (eA z : A), (eA z).2, hcube x hx,
    hcube y hy, hcube z hz, ?_⟩
  have := congrArg Subtype.val hg
  rw [map_mul, map_mul] at this
  exact this.symm

theorem mem_of_isSubnormal_twin {A R₁ R₂ T : Subgroup G} (e₁ : SL(2, ZMod 3) ≃* R₁)
    (hcomm : ∀ x ∈ R₁, ∀ y ∈ R₂, x * y = y * x) (hsub : IsSubnormal A T) (hR₁ : R₁ ≤ T)
    {u r s : G} (huA : u ∈ A) (hr : r ∈ R₁) (hs : s ∈ R₂) (hr3 : r ^ 3 = 1) (hr1 : r ≠ 1)
    (hurs : u = r * s) (x : SL(2, ZMod 3)) (hx : x ^ 4 = 1) : ((e₁ x : R₁) : G) ∈ A := by
  let ι : SL(2, ZMod 3) →* G := R₁.subtype.comp e₁.toMonoidHom
  obtain ⟨x₀, hx₀⟩ := e₁.surjective ⟨r, hr⟩
  have hιx₀ : ι x₀ = r := congrArg Subtype.val hx₀
  have hx₀3 : x₀ ^ 3 = 1 := by
    have : ι (x₀ ^ 3) = ι 1 := by rw [map_pow, hιx₀, hr3, map_one]
    have hinj : Function.Injective ι := Subtype.val_injective.comp e₁.injective
    exact hinj this
  have hx₀1 : x₀ ≠ 1 := fun h => hr1 (by rw [← hιx₀, h, map_one])
  have hYT : sl2ThreeQ8.map ι ≤ T := by
    rintro _ ⟨q, -, rfl⟩
    exact hR₁ (e₁ q).2
  have hX : ∀ y ∈ (Subgroup.zpowers x₀).map ι,
      ∃ b, (∀ w ∈ sl2ThreeQ8.map ι, w * b = b * w) ∧ y * b ∈ A := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨s ^ k, fun w hw => ?_, ?_⟩
    · obtain ⟨q, -, rfl⟩ := hw
      exact hcomm _ (e₁ q).2 _ (R₂.zpow_mem hs k)
    · rw [map_zpow, hιx₀]
      have hc : Commute r s := hcomm r hr s hs
      rw [← hc.mul_zpow, ← hurs]
      exact A.zpow_mem huA k
  have hY : sl2ThreeQ8.map ι ≤ ⁅(Subgroup.zpowers x₀).map ι, sl2ThreeQ8.map ι⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono (sl2ThreeQ8_le_commutator_zpowers hx₀3 hx₀1)
  have := le_of_isSubnormal_commutator hsub hYT hX hY
  exact this ⟨x, hx, rfl⟩

theorem eq_or_eq_of_isSubnormal_twin {A R₁ R₂ T : Subgroup G} (eA : SL(2, ZMod 3) ≃* A)
    (e₁ : SL(2, ZMod 3) ≃* R₁) (e₂ : SL(2, ZMod 3) ≃* R₂)
    (hcomm : ∀ x ∈ R₁, ∀ y ∈ R₂, x * y = y * x) (hinf : ∀ g ∈ R₁, g ∈ R₂ → g * g = 1)
    (hcube : ∀ u ∈ A, u ^ 3 = 1 → ∃ r ∈ R₁, ∃ s ∈ R₂, r ^ 3 = 1 ∧ s ^ 3 = 1 ∧ u = r * s)
    (hsub : IsSubnormal A T) (hR₁ : R₁ ≤ T) (hR₂ : R₂ ≤ T) : A = R₁ ∨ A = R₂ := by
  have hcomm' : ∀ x ∈ R₂, ∀ y ∈ R₁, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  have hcard : ∀ {R : Subgroup G} (e : SL(2, ZMod 3) ≃* R), Nat.card R ≤ 24 := fun {R} e => by
    rw [← Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hfin : ∀ {R : Subgroup G} (e : SL(2, ZMod 3) ≃* R), Finite R := fun {R} e =>
    Finite.of_equiv _ e.toEquiv
  by_cases hP₁ : ∃ u ∈ A, ∃ r ∈ R₁, ∃ s ∈ R₂, r ^ 3 = 1 ∧ s ^ 3 = 1 ∧ u = r * s ∧ r ≠ 1
  · by_cases hP₂ : ∃ u ∈ A, ∃ r ∈ R₁, ∃ s ∈ R₂, r ^ 3 = 1 ∧ s ^ 3 = 1 ∧ u = r * s ∧ s ≠ 1
    · exfalso
      obtain ⟨u, huA, r, hr, s, hs, hr3, hs3, hurs, hr1⟩ := hP₁
      obtain ⟨u', hu'A, r', hr', s', hs', hr3', hs3', hurs', hs1'⟩ := hP₂
      obtain ⟨x₁, hx₁4, hx₁2⟩ := exists_order_four_sl2Three
      have h1 := mem_of_isSubnormal_twin e₁ hcomm hsub hR₁ huA hr hs hr3 hr1 hurs x₁ hx₁4
      have h2 := mem_of_isSubnormal_twin e₂ hcomm' hsub hR₂ hu'A hs' hr' hs3' hs1'
        (by rw [hurs', (hcomm r' hr' s' hs')]) x₁ hx₁4
      obtain ⟨y₁, hy₁⟩ := eA.surjective ⟨_, h1⟩
      obtain ⟨y₂, hy₂⟩ := eA.surjective ⟨_, h2⟩
      have hy₁' : ((eA y₁ : A) : G) = ((e₁ x₁ : R₁) : G) := congrArg Subtype.val hy₁
      have hy₂' : ((eA y₂ : A) : G) = ((e₂ x₁ : R₂) : G) := congrArg Subtype.val hy₂
      have hcm : y₁ * y₂ = y₂ * y₁ := by
        apply eA.injective
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hy₁', hy₂']
        exact hcomm _ (e₁ x₁).2 _ (e₂ x₁).2
      have hpow : ∀ (R : Subgroup G) (e : SL(2, ZMod 3) ≃* R) (y : SL(2, ZMod 3)),
          ((eA y : A) : G) = ((e x₁ : R) : G) → y ^ 4 = 1 ∧ y ^ 2 ≠ 1 := fun R e y h => by
        refine ⟨eA.injective (Subtype.ext ?_), fun h2' => hx₁2 (e.injective (Subtype.ext ?_))⟩
        · rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one, h, ← Subgroup.coe_pow,
            ← map_pow, hx₁4, map_one]
          rfl
        · have : ((eA (y ^ 2) : A) : G) = 1 := by rw [h2', map_one]; rfl
          rw [map_pow, Subgroup.coe_pow, h, ← Subgroup.coe_pow, ← map_pow] at this
          rw [map_one]
          exact this
      obtain ⟨h41, h21⟩ := hpow R₁ e₁ y₁ hy₁'
      obtain ⟨h42, h22⟩ := hpow R₂ e₂ y₂ hy₂'
      have hR₂mem : ((e₁ x₁ : R₁) : G) ∈ R₂ := by
        rcases eq_or_eq_inv_of_commute_order_four y₁ y₂ h41 h21 h42 h22 hcm with h | h
        · rw [← hy₁', ← h, hy₂']
          exact (e₂ x₁).2
        · have : ((e₁ x₁ : R₁) : G) = (((e₂ x₁ : R₂) : G))⁻¹ := by
            rw [← hy₁', ← hy₂', h, map_inv, Subgroup.coe_inv, inv_inv]
          rw [this]
          exact R₂.inv_mem (e₂ x₁).2
      have hsq := hinf _ (e₁ x₁).2 hR₂mem
      apply hx₁2
      apply e₁.injective
      apply Subtype.ext
      rw [pow_two, map_mul, Subgroup.coe_mul, hsq, map_one]
      rfl
    · push Not at hP₂
      left
      have hAR : A ≤ R₁ := fun a ha => by
        obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, h1, h2, h3, rfl⟩ := exists_cubes_of_mulEquiv eA ha
        have key : ∀ u ∈ A, u ^ 3 = 1 → u ∈ R₁ := fun u hu hu3 => by
          obtain ⟨r, hr, s, hs, hr3, hs3, hurs⟩ := hcube u hu hu3
          have hs1 := hP₂ u hu r hr s hs hr3 hs3 hurs
          rw [hurs, hs1, mul_one]
          exact hr
        exact R₁.mul_mem (R₁.mul_mem (key u₁ hu₁ h1) (key u₂ hu₂ h2)) (key u₃ hu₃ h3)
      have : Finite R₁ := hfin e₁
      exact eq_of_le_of_natCard_le eA hAR (hcard e₁)
  · push Not at hP₁
    right
    have hAR : A ≤ R₂ := fun a ha => by
      obtain ⟨u₁, hu₁, u₂, hu₂, u₃, hu₃, h1, h2, h3, rfl⟩ := exists_cubes_of_mulEquiv eA ha
      have key : ∀ u ∈ A, u ^ 3 = 1 → u ∈ R₂ := fun u hu hu3 => by
        obtain ⟨r, hr, s, hs, hr3, hs3, hurs⟩ := hcube u hu hu3
        have hr1 := hP₁ u hu r hr s hs hr3 hs3 hurs
        rw [hurs, hr1, one_mul]
        exact hs
      exact R₂.mul_mem (R₂.mul_mem (key u₁ hu₁ h1) (key u₂ hu₂ h2)) (key u₃ hu₃ h3)
    have : Finite R₂ := hfin e₂
    exact eq_of_le_of_natCard_le eA hAR (hcard e₂)

end Twin

end CFSG.ClassicalInvolution.Q3

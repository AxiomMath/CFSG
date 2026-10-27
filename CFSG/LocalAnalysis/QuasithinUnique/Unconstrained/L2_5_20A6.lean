module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_4Aux
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Cube

variable {G : Type*} [Group G]

theorem exists_elemAbelian_card_cube_of_independent [Finite G] {p : ℕ} (hp : p.Prime)
    {a₁ a₂ a₃ : G} (ho₁ : orderOf a₁ = p) (ho₂ : orderOf a₂ = p) (ho₃ : orderOf a₃ = p)
    (c₁₂ : a₁ * a₂ = a₂ * a₁) (c₁₃ : a₁ * a₃ = a₃ * a₁) (c₂₃ : a₂ * a₃ = a₃ * a₂)
    (hind : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, ∀ z ∈ Subgroup.zpowers a₃,
      x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1) :
    ∃ E : Subgroup G, E ≤ Subgroup.zpowers a₁ ⊔ Subgroup.zpowers a₂ ⊔ Subgroup.zpowers a₃ ∧
      CFSG.Assembly.IsElemAbelian p E ∧ Nat.card E = p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have cc₁₂ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a₁ a₂ from c₁₂) i j).eq
  have cc₁₃ : ∀ x ∈ Subgroup.zpowers a₁, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a₁ a₃ from c₁₃) i j).eq
  have cc₂₃ : ∀ x ∈ Subgroup.zpowers a₂, ∀ y ∈ Subgroup.zpowers a₃, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow (show Commute a₂ a₃ from c₂₃) i j).eq
  let φ₁₂ : Subgroup.zpowers a₁ × Subgroup.zpowers a₂ →* G :=
    (Subgroup.zpowers a₁).subtype.noncommCoprod (Subgroup.zpowers a₂).subtype
      (fun x y => cc₁₂ x x.2 y y.2)
  have hφ₁₂ : ∀ q : Subgroup.zpowers a₁ × Subgroup.zpowers a₂, φ₁₂ q = (q.1 : G) * (q.2 : G) :=
    fun q => rfl
  let φ : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃ →* G :=
    φ₁₂.noncommCoprod (Subgroup.zpowers a₃).subtype (fun x z => by
      show φ₁₂ x * (z : G) = (z : G) * φ₁₂ x
      rw [hφ₁₂]
      calc (x.1 : G) * x.2 * z = x.1 * (x.2 * z) := by rw [mul_assoc]
        _ = x.1 * (z * x.2) := by rw [cc₂₃ _ x.2.2 _ z.2]
        _ = (x.1 * z) * x.2 := by rw [mul_assoc]
        _ = (z * x.1) * x.2 := by rw [cc₁₃ _ x.1.2 _ z.2]
        _ = z * (x.1 * x.2) := by rw [mul_assoc])
  have hφ : ∀ q : (Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃,
      φ q = (q.1.1 : G) * (q.1.2 : G) * (q.2 : G) := fun q => rfl
  have hc1 : Nat.card (Subgroup.zpowers a₁) = p := by rw [Nat.card_zpowers, ho₁]
  have hc2 : Nat.card (Subgroup.zpowers a₂) = p := by rw [Nat.card_zpowers, ho₂]
  have hc3 : Nat.card (Subgroup.zpowers a₃) = p := by rw [Nat.card_zpowers, ho₃]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, b⟩, c⟩ hq
    rw [hφ] at hq
    simp only at hq
    obtain ⟨h1, h2, h3⟩ := hind a a.2 b b.2 c c.2 hq
    exact Prod.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2)) (Subtype.ext h3)
  refine ⟨φ.range, ?_, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨q, rfl⟩
    rw [hφ]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left q.1.1.2))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_right q.2.2)
  · rintro _ ⟨q, rfl⟩
    rw [← map_pow]
    have : q ^ p = 1 := by
      refine Prod.ext (Prod.ext ?_ ?_) ?_
      · have := (pow_card_eq_one' : q.1.1 ^ Nat.card (Subgroup.zpowers a₁) = 1)
        rwa [hc1] at this
      · have := (pow_card_eq_one' : q.1.2 ^ Nat.card (Subgroup.zpowers a₂) = 1)
        rwa [hc2] at this
      · have := (pow_card_eq_one' : q.2 ^ Nat.card (Subgroup.zpowers a₃) = 1)
        rwa [hc3] at this
    rw [this, map_one]
  · have h1 : Nat.card ((Subgroup.zpowers a₁ × Subgroup.zpowers a₂) × Subgroup.zpowers a₃) =
        Nat.card φ.range := Nat.card_congr (Equiv.ofInjective φ hinj)
    rw [← h1, Nat.card_prod, Nat.card_prod, hc1, hc2, hc3]
    ring

end Cube

@[expose] def A6RankFacts : Prop :=
  ∀ (X : Type) [Group X], Nonempty (X ≃* alternatingGroup (Fin 6)) →
    (∃ a b : X, orderOf a = 3 ∧ orderOf b = 3 ∧ a * b = b * a ∧
      Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥) ∧
    (∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∃ c ∈ Subgroup.normalizer (V : Set X), orderOf c = 3) ∧
    (∀ x : X, (∀ y : X, y * x = x * y) → x = 1)

section Pair

variable {G : Type} [Group G]

theorem false_of_A6_pair [Finite G] (he : CFSG.Assembly.evenRank G ≤ 2) (hA6 : A6RankFacts)
    {A B : Subgroup G} (hA : Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 6)))
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : False := by
  obtain ⟨⟨a, b, ha, hb, hab, hint⟩, -, hcen⟩ := hA6 ↥A hA
  obtain ⟨-, ⟨V, hV1, hV2, c, hcV, hco⟩, -⟩ := hA6 ↥B hB
  have ha' : orderOf (a : G) = 3 := by rw [Subgroup.orderOf_coe]; exact ha
  have hb' : orderOf (b : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hb
  have hc' : orderOf (c : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hco
  have hab' : (a : G) * b = b * a := congrArg Subtype.val hab
  have hac' : (a : G) * c = c * a := hAB a a.2 c c.2
  have hbc' : (b : G) * c = c * b := hAB b b.2 c c.2
  set V' : Subgroup G := V.map B.subtype with hV'
  have hV'B : V' ≤ B := Subgroup.map_subtype_le V
  have hsub : V'.subgroupOf B = V := Subgroup.comap_map_eq_self_of_injective B.subtype_injective V
  have hnorm := map_subtype_normalizer hV'B
  rw [hsub] at hnorm
  have hcN : (c : G) ∈ Subgroup.normalizer (V' : Set G) := by
    have : (c : G) ∈ (Subgroup.normalizer (V : Set ↥B)).map B.subtype := ⟨c, hcV, rfl⟩
    rw [hnorm] at this
    exact this.2
  have hV'1 : V' ≠ ⊥ := fun e =>
    hV1 ((Subgroup.map_eq_bot_iff_of_injective V B.subtype_injective).mp e)
  have hV'2 : IsPGroup 2 V' :=
    hV2.of_equiv (Subgroup.equivMapOfInjective V B.subtype B.subtype_injective)
  have hind : ∀ x ∈ Subgroup.zpowers (a : G), ∀ y ∈ Subgroup.zpowers (b : G),
      ∀ z ∈ Subgroup.zpowers (c : G), x * y * z = 1 → x = 1 ∧ y = 1 ∧ z = 1 := by
    intro x hx y hy z hz hxyz
    have hxA : x ∈ A := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact A.zpow_mem a.2 i
    have hyA : y ∈ A := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact A.zpow_mem b.2 i
    have hzB : z ∈ B := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact B.zpow_mem c.2 i
    have hzeq : z = (x * y)⁻¹ := eq_inv_of_mul_eq_one_right hxyz
    have hzA : z ∈ A := by rw [hzeq]; exact A.inv_mem (A.mul_mem hxA hyA)
    have hz1 : z = 1 := by
      have := hcen ⟨z, hzA⟩ (fun w => Subtype.ext (hAB w w.2 z hzB))
      exact congrArg Subtype.val this
    rw [hz1, mul_one] at hxyz
    have hx1 : x = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h1 : a ^ i * b ^ j = 1 := Subtype.ext (by simpa using hxyz)
      have h2 : a ^ i = (b ^ j)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : a ^ i ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
        ⟨Subgroup.zpow_mem_zpowers a i, by
          rw [h2]; exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers b j)⟩
      rw [hint, Subgroup.mem_bot] at h3
      simpa using congrArg Subtype.val h3
    rw [hx1, one_mul] at hxyz
    exact ⟨hx1, hxyz, hz1⟩
  obtain ⟨E, hEle, hE, hEcard⟩ := exists_elemAbelian_card_cube_of_independent Nat.prime_three
    ha' hb' hc' hab' hac' hbc' hind
  have hAN : ∀ w : ↥A, (w : G) ∈ Subgroup.normalizer (V' : Set G) := fun w =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hAB w w.2 v (hV'B hv)).symm)
  have hEN : E ≤ Subgroup.normalizer (V' : Set G) :=
    hEle.trans (sup_le (sup_le (Subgroup.zpowers_le.mpr (hAN a))
      (Subgroup.zpowers_le.mpr (hAN b))) (Subgroup.zpowers_le.mpr hcN))
  have hX : pCoreOf 2 (Subgroup.normalizer (V' : Set G)) ≠ ⊥ := by
    have := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 V' _
      Subgroup.le_normalizer
      ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hV'2
    intro e
    rw [e] at this
    exact hV'1 (le_bot_iff.mp this)
  exact Unc25G2.false_of_isElemAbelian_card_cube he hX hEN Nat.prime_three (by norm_num) hE
    hEcard

end Pair

end CFSG.QuasithinUnique

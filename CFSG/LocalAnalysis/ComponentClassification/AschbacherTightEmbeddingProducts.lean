module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

theorem product_mul_injective {G : Type*} [Group G] (A B : Subgroup G)
    (hdisjoint : Disjoint A B) :
    Function.Injective (fun x : A × B => x.1.val * x.2.val) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  change a.val * b.val = c.val * d.val at heq
  have hcross : c.val⁻¹ * a.val = d.val * b.val⁻¹ := by
    calc
      c.val⁻¹ * a.val = c.val⁻¹ * (a.val * b.val) * b.val⁻¹ := by group
      _ = d.val * b.val⁻¹ := by rw [heq]; group
  have hone : c.val⁻¹ * a.val = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hdisjoint.eq_bot]
    exact ⟨A.mul_mem (A.inv_mem c.property) a.property,
      by rw [hcross]; exact B.mul_mem d.property (B.inv_mem b.property)⟩
  have hac : a = c := Subtype.ext (inv_mul_eq_one.mp hone).symm
  have hbd : b = d := by
    apply Subtype.ext
    rw [hac] at heq
    exact mul_left_cancel heq
  exact Prod.ext hac hbd

theorem disjoint_card_mul_le {G : Type*} [Group G] [Finite G]
    (A B X : Subgroup G) (hA : A ≤ X) (hB : B ≤ X) (hdisjoint : Disjoint A B) :
    Nat.card A * Nat.card B ≤ Nat.card X := by
  let mulMap : A × B → X := fun pair =>
    ⟨pair.1.val * pair.2.val, X.mul_mem (hA pair.1.property) (hB pair.2.property)⟩
  have hinjective : Function.Injective mulMap := by
    intro first second heq
    exact product_mul_injective A B hdisjoint (congrArg Subtype.val heq)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective mulMap hinjective

@[expose] noncomputable def commutingProductEquiv {G : Type*} [Group G]
    (A B : Subgroup G) (hcommutes : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisjoint : Disjoint A B) : A × B ≃* ↥(A ⊔ B) := by
  let multiplication := A.subtype.noncommCoprod B.subtype
    (fun a b => by
      change a.val * b.val = b.val * a.val
      exact hcommutes a.val a.property b.val b.property)
  let homomorphism : A × B →* ↥(A ⊔ B) :=
    multiplication.codRestrict (A ⊔ B) (fun pair =>
      Subgroup.mul_mem_sup pair.1.property pair.2.property)
  apply MulEquiv.ofBijective homomorphism
  constructor
  · intro first second heq
    exact product_mul_injective A B hdisjoint (congrArg Subtype.val heq)
  · intro x
    have hmem : x.val ∈ multiplication.range := by
      dsimp only [multiplication]
      rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
      exact x.property
    obtain ⟨pair, hpair⟩ := hmem
    exact ⟨pair, Subtype.ext hpair⟩

theorem commutingProductEquiv_apply {G : Type*} [Group G]
    (A B : Subgroup G) (hcommutes : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisjoint : Disjoint A B) (pair : A × B) :
    (commutingProductEquiv A B hcommutes hdisjoint pair).val = pair.1.val * pair.2.val := rfl

theorem commutingProduct_card {G : Type*} [Group G]
    (A B : Subgroup G) (hcommutes : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hdisjoint : Disjoint A B) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_congr (commutingProductEquiv A B hcommutes hdisjoint).toEquiv, Nat.card_prod]

@[expose] def relativeNormalizer {G : Type*} [Group G] (T S : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (T : Set G) ⊓ S

theorem relativeNormalizer_product_eq {G : Type*} [Group G]
    (Q T S : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hT : T ≤ S) (hS : S ≤ Q ⊔ T) :
    relativeNormalizer T S = T ⊔ (relativeNormalizer T S ⊓ Q) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨q, hq, t, ht, heq⟩ := NormalizedProduct.coordinates Q T hnormalizes x (hS hx.2)
    have htNormalizer : t ∈ relativeNormalizer T S := ⟨Subgroup.le_normalizer ht, hT ht⟩
    have hqNormalizer : q ∈ relativeNormalizer T S := by
      have hmem := (relativeNormalizer T S).mul_mem hx
        ((relativeNormalizer T S).inv_mem htNormalizer)
      rw [← heq, mul_inv_cancel_right] at hmem
      exact hmem
    rw [← heq, sup_comm]
    exact Subgroup.mul_mem_sup ⟨hqNormalizer, hq⟩ ht
  · exact sup_le (le_inf Subgroup.le_normalizer hT) inf_le_left

theorem normalizer_base_commutes {G : Type*} [Group G]
    (Q T : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint T Q) :
    ∀ t ∈ T, ∀ q ∈ Subgroup.normalizer (T : Set G) ⊓ Q, t * q = q * t := by
  intro t ht q hq
  have hconjugateT : q * t * q⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hq.1 t).mp ht
  have hconjugateQ : t * q⁻¹ * t⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hnormalizes ht) q⁻¹).mp (Q.inv_mem hq.2)
  have hone : q * t * q⁻¹ * t⁻¹ = 1 := by
    have hmem : q * t * q⁻¹ * t⁻¹ ∈ T ⊓ Q := by
      refine ⟨T.mul_mem hconjugateT (T.inv_mem ht), ?_⟩
      change q * t * q⁻¹ * t⁻¹ ∈ Q
      simpa only [mul_assoc] using Q.mul_mem hq.2 hconjugateQ
    exact Subgroup.mem_bot.mp (hdisjoint.eq_bot ▸ hmem)
  have heq : q * t * q⁻¹ = t := mul_inv_eq_one.mp hone
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

theorem relativeNormalizer_factors_commute {G : Type*} [Group G]
    (Q T S : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint T Q) :
    ∀ t ∈ T, ∀ q ∈ relativeNormalizer T S ⊓ Q, t * q = q * t := by
  intro t ht q hq
  exact normalizer_base_commutes Q T hnormalizes hdisjoint t ht q ⟨hq.1.1, hq.2⟩

@[expose] noncomputable def relativeNormalizerProductEquiv {G : Type*} [Group G]
    (Q T S : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint T Q) (hT : T ≤ S) (hS : S ≤ Q ⊔ T) :
    T × ↥(relativeNormalizer T S ⊓ Q) ≃* relativeNormalizer T S :=
  (commutingProductEquiv T (relativeNormalizer T S ⊓ Q)
    (relativeNormalizer_factors_commute Q T S hnormalizes hdisjoint)
    (hdisjoint.mono_right inf_le_right)).trans
      (MulEquiv.subgroupCongr (relativeNormalizer_product_eq Q T S hnormalizes hT hS).symm)

theorem relativeNormalizerProductEquiv_apply {G : Type*} [Group G]
    (Q T S : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint T Q) (hT : T ≤ S) (hS : S ≤ Q ⊔ T)
    (pair : T × ↥(relativeNormalizer T S ⊓ Q)) :
    (relativeNormalizerProductEquiv Q T S hnormalizes hdisjoint hT hS pair).val =
      pair.1.val * pair.2.val := by
  exact commutingProductEquiv_apply T (relativeNormalizer T S ⊓ Q)
    (relativeNormalizer_factors_commute Q T S hnormalizes hdisjoint)
    (hdisjoint.mono_right inf_le_right) pair

theorem relativeNormalizer_card {G : Type*} [Group G]
    (Q T S : Subgroup G) (hnormalizes : T ≤ Subgroup.normalizer (Q : Set G))
    (hdisjoint : Disjoint T Q) (hT : T ≤ S) (hS : S ≤ Q ⊔ T) :
    Nat.card (relativeNormalizer T S) = Nat.card T * Nat.card ↥(relativeNormalizer T S ⊓ Q) := by
  rw [← Nat.card_congr (relativeNormalizerProductEquiv Q T S hnormalizes hdisjoint hT hS).toEquiv,
    Nat.card_prod]

theorem overlap_relativeNormalizer_product {G : Type*} [Group G]
    (Q : Subgroup G) (g : G)
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) :
    relativeNormalizer (sylowImage _ T) (sylowImage _ S) =
      sylowImage _ T ⊔ (relativeNormalizer (sylowImage _ T) (sylowImage _ S) ⊓ Q) :=
  relativeNormalizer_product_eq Q _ _ (overlap_sylow_le_normalizer Q g T) hTS (sylowImage_le _ S)

theorem overlap_relativeNormalizer_directProduct {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (htight : TightlyEmbedded Q) (g : G)
    (hg : g ∉ Subgroup.normalizer (Q : Set G))
    (T : Sylow 2 ↥(rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)))
    (S : Sylow 2 ↥(Q ⊔ sylowImage _ T))
    (hTS : sylowImage _ T ≤ sylowImage _ S) :
    ∃ e : sylowImage _ T ×
        ↥(relativeNormalizer (sylowImage _ T) (sylowImage _ S) ⊓ Q) ≃*
          relativeNormalizer (sylowImage _ T) (sylowImage _ S),
      ∀ pair, (e pair).val = pair.1.val * pair.2.val := by
  have hdisjoint : Disjoint (sylowImage _ T) Q :=
    disjoint_iff.mpr (overlap_sylow_inf_eq_bot Q htight g hg T)
  refine ⟨relativeNormalizerProductEquiv Q _ _ (overlap_sylow_le_normalizer Q g T)
    hdisjoint hTS (sylowImage_le _ S), ?_⟩
  exact relativeNormalizerProductEquiv_apply Q _ _ (overlap_sylow_le_normalizer Q g T)
    hdisjoint hTS (sylowImage_le _ S)

end CFSG.ComponentClassification.AschbacherTightEmbedding

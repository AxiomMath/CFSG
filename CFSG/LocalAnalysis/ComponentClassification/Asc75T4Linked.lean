module

public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Conj

public section

namespace CFSG.ComponentClassification.Asc75T4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G]

@[expose] def Linked (A B : Subgroup G) : Prop :=
  twoPrimeLayerIn A ≤ normalizer (B : Set G) ∧ twoPrimeLayerIn B ≤ normalizer (A : Set G)

omit [Finite G] in
theorem Linked.refl (A : Subgroup G) : Linked A A :=
  ⟨(twoPrimeLayerIn_le A).trans le_normalizer, (twoPrimeLayerIn_le A).trans le_normalizer⟩

omit [Finite G] in
theorem Linked.symm {A B : Subgroup G} (h : Linked A B) : Linked B A := ⟨h.2, h.1⟩

theorem linked_rightConjugate_iff {A B : Subgroup G} {g : G} :
    Linked (rightConjugate A g) (rightConjugate B g) ↔ Linked A B := by
  unfold Linked
  rw [twoPrimeLayerIn_rightConjugate, twoPrimeLayerIn_rightConjugate,
    ← AschbacherTheorem3.rightConjugate_normalizer,
    ← AschbacherTheorem3.rightConjugate_normalizer]
  exact and_congr (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective)
    (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective)

theorem commutator_mem_oddCoreIn_of_linked {Q : Subgroup G} (htight : TightlyEmbedded Q)
    {a b : G} (hne : rightConjugate Q a ≠ rightConjugate Q b)
    (hL : Linked (rightConjugate Q a) (rightConjugate Q b)) :
    ∀ t ∈ twoPrimeLayerIn (rightConjugate Q b), ∀ k ∈ twoPrimeLayerIn (rightConjugate Q a),
      t * k * t⁻¹ * k⁻¹ ∈ oddCoreIn (rightConjugate Q a) := by
  set A := rightConjugate Q a
  set B := rightConjugate Q b
  intro t ht k hk
  have hodd : Odd (Nat.card (A ⊓ B : Subgroup G)) :=
    Nat.not_even_iff_odd.mp fun h => hne (eq_of_even_inf_rightConjugate htight h)
  have htA : t ∈ normalizer (twoPrimeLayerIn A : Set G) :=
    normalizer_le_normalizer_twoPrimeLayerIn A (hL.2 ht)
  have hkB : k ∈ normalizer (twoPrimeLayerIn B : Set G) :=
    normalizer_le_normalizer_twoPrimeLayerIn B (hL.1 hk)
  have h1 : t * k * t⁻¹ * k⁻¹ ∈ twoPrimeLayerIn A :=
    mul_mem ((mem_normalizer_iff.mp htA k).mp hk) (inv_mem hk)
  have h2 : t * k * t⁻¹ * k⁻¹ ∈ twoPrimeLayerIn B := by
    have : t * k * t⁻¹ * k⁻¹ = t * (k * t⁻¹ * k⁻¹) := by group
    rw [this]
    exact mul_mem ht ((mem_normalizer_iff.mp hkB _).mp (inv_mem ht))
  have hle : twoPrimeLayerIn A ⊓ twoPrimeLayerIn B ≤ oddCoreIn A := by
    rw [← oddCoreIn_twoPrimeLayerIn A]
    refine le_oddCoreIn (normalIn_of_le_normalizer inf_le_left ?_)
      (hodd.of_dvd_nat (card_dvd_of_le (inf_le_inf (twoPrimeLayerIn_le A)
        (twoPrimeLayerIn_le B))))
    intro x hx
    have hxA := le_normalizer hx
    have hxB := normalizer_le_normalizer_twoPrimeLayerIn B (hL.1 hx)
    rw [mem_normalizer_iff] at hxA hxB ⊢
    intro y
    rw [mem_inf, mem_inf, hxA y, hxB y]
  exact hle ⟨h1, h2⟩

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_eq_one {t : G} {k : ℕ} (htk : t ^ (2 ^ k) = 1) :
    IsPGroup 2 (zpowers t) := by
  rintro ⟨x, hx⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  refine ⟨k, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, htk, one_zpow]

theorem coversLayer_zpowers_of_linked {Q : Subgroup G} (htight : TightlyEmbedded Q) {a b : G}
    (hne : rightConjugate Q a ≠ rightConjugate Q b)
    (hL : Linked (rightConjugate Q a) (rightConjugate Q b)) {t : G}
    (ht : t ∈ twoPrimeLayerIn (rightConjugate Q b)) {k : ℕ} (htk : t ^ (2 ^ k) = 1) :
    CoversLayer (zpowers t) (rightConjugate Q a) := by
  have hz : zpowers t ≤ twoPrimeLayerIn (rightConjugate Q b) := (zpowers_le).mpr ht
  exact coversLayer_of_commutator (isPGroup_zpowers_of_pow_eq_one htk) (hz.trans hL.2)
    fun x hx k hk => commutator_mem_oddCoreIn_of_linked htight hne hL x (hz hx) k hk

omit [Finite G] in
theorem rightConjugate_eq_top_iff {X : Subgroup G} {b : G} :
    rightConjugate X b = ⊤ ↔ X = ⊤ := by
  constructor
  · intro h
    have h1 := congrArg (fun Y => rightConjugate Y b⁻¹) h
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    rw [h1]
    exact map_top_of_surjective _ (MulAut.conj b⁻¹⁻¹).surjective
  · rintro rfl
    exact map_top_of_surjective _ (MulAut.conj b⁻¹).surjective

theorem centralizer_zpowers_ne_top {Q : Subgroup G} (htight : TightlyEmbedded Q)
    (hNQ : normalizer (Q : Set G) ≠ ⊤) {b t : G} (htQ : t ∈ rightConjugate Q b)
    (ht : orderOf t = 2) : centralizer (zpowers t : Set G) ≠ ⊤ := by
  intro htop
  apply hNQ
  have hle : centralizer ({t} : Set G) ≤ normalizer (rightConjugate Q b : Set G) :=
    centralizer_le_of_involution (rightConjugate_tightlyEmbedded Q htight b) htQ ht
  have hCt : centralizer ({t} : Set G) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ centralizer (zpowers t : Set G) := htop ▸ mem_top x
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (mem_centralizer_iff.mp hx) t (mem_zpowers t)
  rw [hCt, top_le_iff, ← AschbacherTheorem3.rightConjugate_normalizer,
    rightConjugate_eq_top_iff] at hle
  exact hle

@[expose] def NormalInCentralizers (Q : Subgroup G) : Prop :=
  ∀ (a : G) (X : Subgroup G), IsPGroup 2 X → centralizer (X : Set G) ≠ ⊤ →
    CoversLayer X (rightConjugate Q a) →
    NormalIn (twoPrimeLayerIn (rightConjugate Q a) ⊓ centralizer (X : Set G))
      (twoPrimeLayerIn (centralizer (X : Set G)))

theorem eq_or_linked_of_normalInCentralizers (h3 : AschbacherTheorem3.Theorem3Statement)
    {Q : Subgroup G} (htight : TightlyEmbedded Q) (hno : NoThm3Alt3 Q)
    (hN : NormalInCentralizers Q) (h4 : HasFourGroup (twoPrimeLayerIn Q))
    {a b : G} {X : Subgroup G} (hX : IsPGroup 2 X) (hXc : centralizer (X : Set G) ≠ ⊤)
    (hXa : CoversLayer X (rightConjugate Q a)) (hXb : CoversLayer X (rightConjugate Q b)) :
    rightConjugate Q a = rightConjugate Q b ∨
      Linked (rightConjugate Q a) (rightConjugate Q b) := by
  have h4a : HasFourGroup (twoPrimeLayerIn (rightConjugate Q a)) := by
    rw [twoPrimeLayerIn_rightConjugate]
    exact h4.map (MulAut.conj a⁻¹).injective
  have h4b : HasFourGroup (twoPrimeLayerIn (rightConjugate Q b)) := by
    rw [twoPrimeLayerIn_rightConjugate]
    exact h4.map (MulAut.conj b⁻¹).injective
  rcases eq_or_normalizes_of_coversLayer_of_normalIn (rightConjugate_tightlyEmbedded Q htight a)
      (rightConjugate_tightlyEmbedded Q htight b) (eq_of_even_inf_rightConjugate htight)
      (caseIPair_rightConjugate h3 htight hno b a) (caseIPair_rightConjugate h3 htight hno a b)
      h4a h4b hXa hXb (hN a X hX hXc hXa) (hN b X hX hXc hXb) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.2, h.1⟩

end CFSG.ComponentClassification.Asc75T4

module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LocalEmbeddingDatum

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type*} [Group G] {H : Subgroup G} {z : G}

theorem smul_mk_eq_mk_iff (x g : G) :
    x • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g ↔ g⁻¹ * x * g ∈ H := by
  rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem conj_smul_eq_iff {Ω : Type*} [MulAction G Ω] (x g : G) (ω : Ω) :
    (g⁻¹ * x * g) • ω = ω ↔ x • (g • ω) = g • ω := by
  rw [mul_smul, mul_smul]
  constructor
  · intro h
    have h' := congrArg (fun w : Ω => g • w) h
    simpa only [smul_inv_smul] using h'
  · intro h
    rw [h, inv_smul_smul]

theorem mk_eq_base_iff (g : G) :
    (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk 1 ↔ g ∈ H := by
  rw [QuotientGroup.eq, mul_one, H.inv_mem_iff]

theorem conj_mem_iff (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (g : G) :
    g⁻¹ * z * g ∈ H ↔ g ∈ H := by
  have h := huniq g⁻¹
  rw [mem_rightConjugate_iff, inv_inv, H.inv_mem_iff] at h
  exact h

theorem mem_of_unique (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) : z ∈ H := by
  have h := (huniq 1).mpr H.one_mem
  rwa [rightConjugate_one] at h

theorem centralizer_le_of_unique (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    Subgroup.centralizer ({z} : Set G) ≤ H := by
  intro g hg
  have hfix : g⁻¹ * z * g = z := by
    rw [mul_assoc, ← Subgroup.mem_centralizer_singleton_iff.mp hg, inv_mul_cancel_left]
  exact (conj_mem_iff huniq g).mp (by rw [hfix]; exact mem_of_unique huniq)

theorem normalizer_eq_of_unique (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) :
    Subgroup.normalizer (H : Set G) = H := by
  apply le_antisymm _ H.le_normalizer
  intro g hg
  apply (conj_mem_iff huniq g).mp
  have hg' := (Subgroup.normalizer (H : Set G)).inv_mem hg
  simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hg' z).mp (mem_of_unique huniq)

theorem smul_eq_iff_eq_base (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (ω : G ⧸ H) : z • ω = ω ↔ ω = QuotientGroup.mk 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [smul_mk_eq_mk_iff, conj_mem_iff huniq, mk_eq_base_iff]

theorem conj_smul_eq_iff_eq (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    (g : G) (ω : G ⧸ H) :
    (g⁻¹ * z * g) • ω = ω ↔ ω = g⁻¹ • (QuotientGroup.mk 1 : G ⧸ H) := by
  rw [conj_smul_eq_iff, smul_eq_iff_eq_base huniq]
  constructor
  · intro h
    rw [← h, inv_smul_smul]
  · intro h
    rw [h, smul_inv_smul]

theorem class_fixes_unique (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H)
    {s : G} (hs : s ∈ involutionPointClass z) :
    ∃ ω₀ : G ⧸ H, ∀ ω : G ⧸ H, s • ω = ω ↔ ω = ω₀ := by
  obtain ⟨g, rfl⟩ := hs
  exact ⟨g⁻¹ • QuotientGroup.mk 1, conj_smul_eq_iff_eq huniq g⟩

theorem class_mem_iff_fixes_base {s : G} :
    s ∈ H ↔ s • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
  rw [smul_mk_eq_mk_iff, inv_one, one_mul, mul_one]

theorem class_mem_iff (huniq : ∀ g : G, z ∈ rightConjugate H g ↔ g ∈ H) (g : G) :
    rightConjugateElem z g ∈ H ↔ g ∈ H :=
  conj_mem_iff huniq g

theorem class_orderOf (hz : orderOf z = 2) {s : G} (hs : s ∈ involutionPointClass z) :
    orderOf s = 2 :=
  order_two_of_mem_pointClass hz hs

theorem class_inv (hz : orderOf z = 2) {s : G} (hs : s ∈ involutionPointClass z) :
    s⁻¹ = s :=
  inv_eq_self_of_orderOf_eq_two (class_orderOf hz hs)

theorem class_mul_self (hz : orderOf z = 2) {s : G} (hs : s ∈ involutionPointClass z) :
    s * s = 1 := by
  simpa only [pow_two] using (orderOf_eq_prime_iff.mp (class_orderOf hz hs)).1

theorem class_conj_mem {s : G} (hs : s ∈ involutionPointClass z) (g : G) :
    g⁻¹ * s * g ∈ involutionPointClass z := by
  obtain ⟨k, rfl⟩ := hs
  refine ⟨k * g, ?_⟩
  simp only [rightConjugateElem, mul_inv_rev, mul_assoc]

end CFSG.ComponentClassification.AschbacherStrongEmbedding

module

public import CFSG.ClassicalInvolution.Asc77.HypOmegaDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem conjSub_le_conjSub_iff (g : G) {A B : Subgroup G} :
    conjSub g A ≤ conjSub g B ↔ A ≤ B := by
  refine ⟨fun h => ?_, conjSub_mono⟩
  have := conjSub_mono (n := g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem conjSub_inj (g : G) {A B : Subgroup G} : conjSub g A = conjSub g B ↔ A = B :=
  ⟨fun h => le_antisymm ((conjSub_le_conjSub_iff g).mp h.le) ((conjSub_le_conjSub_iff g).mp h.ge),
    fun h => h ▸ rfl⟩

theorem isPGroup_conjSub {p : ℕ} [Fact p.Prime] (g : G) {A : Subgroup G} (h : IsPGroup p A) :
    IsPGroup p (conjSub g A) :=
  h.map _

theorem conjSub_le_iff (g : G) {A B : Subgroup G} : conjSub g A ≤ B ↔ A ≤ conjSub g⁻¹ B := by
  rw [← conjSub_le_conjSub_iff g⁻¹, conjSub_inv_conjSub]

theorem mem_normalizer_conjSub_iff (g x : G) (K : Subgroup G) :
    x ∈ Subgroup.normalizer ((conjSub g K : Subgroup G) : Set G) ↔
      g⁻¹ * x * g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h h'
    have := h (g * h' * g⁻¹)
    rw [mem_conjSub_iff, mem_conjSub_iff] at this
    have e1 : g⁻¹ * (g * h' * g⁻¹) * g = h' := by group
    have e2 : g⁻¹ * (x * (g * h' * g⁻¹) * x⁻¹) * g = g⁻¹ * x * g * h' * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1, e2] at this
    exact this
  · intro h h'
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have e2 : g⁻¹ * (x * h' * x⁻¹) * g = g⁻¹ * x * g * (g⁻¹ * h' * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e2]
    exact h _

theorem mem_RSet_iff {R : Subgroup G} : R ∈ RSet Ω ↔ ∃ J ∈ Ω, R ≤ J ∧ IsPGroup 2 R ∧
    ∀ R' : Subgroup G, R' ≤ J → IsPGroup 2 R' → R ≤ R' → R' = R := by
  constructor
  · rintro ⟨J, hJ, P, rfl⟩
    refine ⟨J, hJ, Subgroup.map_subtype_le _, P.isPGroup'.map _, fun R' hR'J hR'2 hle => ?_⟩
    have hP : (P : Subgroup J) ≤ R'.subgroupOf J := Subgroup.map_le_iff_le_comap.mp hle
    have hQ : IsPGroup 2 (R'.subgroupOf J) := hR'2.comap_subtype
    have := P.is_maximal' hQ hP
    rw [← Subgroup.map_subgroupOf_eq_of_le hR'J, this]
  · rintro ⟨J, hJ, hRJ, hR2, hmax⟩
    refine ⟨J, hJ, ⟨R.subgroupOf J, hR2.comap_subtype, fun {Q} hQ hle => ?_⟩, ?_⟩
    · have h1 : R ≤ Q.map J.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hRJ]
        exact Subgroup.map_mono hle
      have h2 := hmax (Q.map J.subtype) (Subgroup.map_subtype_le _) (hQ.map _) h1
      rw [← Subgroup.comap_map_eq_self_of_injective J.subtype_injective Q, h2]
      rfl
    · exact (Subgroup.map_subgroupOf_eq_of_le hRJ).symm

theorem RSet.conj (hΩ : ConjInvariant Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) (g : G) :
    conjSub g R ∈ RSet Ω := by
  obtain ⟨J, hJ, hRJ, hR2, hmax⟩ := mem_RSet_iff.mp hR
  refine mem_RSet_iff.mpr ⟨conjSub g J, hΩ g J hJ, conjSub_mono hRJ, isPGroup_conjSub g hR2,
    fun R' hR'J hR'2 hle => ?_⟩
  have h1 : conjSub g⁻¹ R' ≤ J := by
    have := conjSub_mono (n := g⁻¹) hR'J
    rwa [conjSub_inv_conjSub] at this
  have h2 : R ≤ conjSub g⁻¹ R' := (conjSub_le_iff g).mp hle
  have h3 := hmax _ h1 (isPGroup_conjSub g⁻¹ hR'2) h2
  calc R' = conjSub g (conjSub g⁻¹ R') := (conjSub_conjSub_inv g R').symm
    _ = conjSub g R := by rw [h3]

theorem USet.conj (hΩ : ConjInvariant Ω) {U : Subgroup G} (hU : U ∈ USet Ω) (g : G) :
    conjSub g U ∈ USet Ω := by
  obtain ⟨R, hR, hUR, hcyc, hidx⟩ := hU
  refine ⟨conjSub g R, RSet.conj hΩ hR g, conjSub_mono hUR, ?_, ?_⟩
  · let e := Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact (MulEquiv.isCyclic e).mp hcyc
  · show (U.map (MulAut.conj g).toMonoidHom).relIndex (R.map (MulAut.conj g).toMonoidHom) = 2
    rw [Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hidx

theorem omegaNbr_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ omegaNbr Ω K) (g : G) :
    conjSub g J ∈ omegaNbr Ω (conjSub g K) := by
  obtain ⟨hJ, hne, R, hR, hRJ, hRN⟩ := h
  refine ⟨hΩ g J hJ, fun h' => hne ((conjSub_inj g).mp h'), conjSub g R, RSet.conj hΩ hR g,
    conjSub_mono hRJ, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  exact (mem_normalizer_conjSub_iff g x K).mpr (hRN hx)

theorem omegaStarNbr_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ omegaStarNbr Ω K)
    (g : G) : conjSub g J ∈ omegaStarNbr Ω (conjSub g K) := by
  obtain ⟨hJ, hne, U, hU, hUJ, hUN⟩ := h
  refine ⟨hΩ g J hJ, fun h' => hne ((conjSub_inj g).mp h'), conjSub g U, USet.conj hΩ hU g,
    conjSub_mono hUJ, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  exact (mem_normalizer_conjSub_iff g x K).mpr (hUN hx)

theorem twinSet_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ twinSet Ω K) (g : G) :
    conjSub g J ∈ twinSet Ω (conjSub g K) := by
  obtain ⟨hJ, z, hK, hJz⟩ := h
  exact ⟨hΩ g J hJ, g * z * g⁻¹, hK.conj g, hJz.conj g⟩

theorem dstarAdj_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : dstarAdj Ω K J) (g : G) :
    dstarAdj Ω (conjSub g K) (conjSub g J) := by
  obtain ⟨hJ, h | h⟩ := h
  · exact ⟨hΩ g J hJ, Or.inl (omegaStarNbr_conj hΩ h g)⟩
  · exact ⟨hΩ g J hJ, Or.inr (omegaStarNbr_conj hΩ h g)⟩

theorem dstarComp_conj (hΩ : ConjInvariant Ω) {K J : Subgroup G} (h : J ∈ dstarComp Ω K) (g : G) :
    conjSub g J ∈ dstarComp Ω (conjSub g K) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (dstarAdj_conj hΩ hbc g)

end CFSG.ClassicalInvolution.Asc77

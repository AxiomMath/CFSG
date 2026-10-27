module

public import CFSG.LocalAnalysis.ComponentClassification.GSLitReach
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitSetup

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Config

omit [Finite X] in
theorem false_of_noncyclic_le (h : Config t L) {E : Subgroup X} (hE : IsPGroup 2 E)
    (hEc : ¬ IsCyclic E) (hEK : E ≤ coreActionKernel L) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := E.subgroupOf (coreActionKernel L) with hE'
  have hE'2 : IsPGroup 2 E' :=
    hE.comap_of_injective (coreActionKernel L).subtype (subtype_injective _)
  obtain ⟨P, hP⟩ := hE'2.exists_le_sylow
  have hPc := h.isCyclic P
  have : IsCyclic E' := Subgroup.isCyclic_of_le hP
  exact hEc ((subgroupOfEquivOfLe hEK).isCyclic.mp this)

theorem exists_fourGroup (h : Config t L) :
    ∃ E : Subgroup X, E ≤ L ∧ Open.IsElemAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E, -, hE, hcard⟩ := SectionRank.exists_pRank (p := 2) (by norm_num) (⊤ : Subgroup L)
  rw [h.pRank_eq_two] at hcard
  refine ⟨E.map L.subtype, ?_, SectionRank.isElemAbelian_map hE _, ?_⟩
  · rintro _ ⟨e, -, rfl⟩
    exact e.2
  · rw [card_map_of_injective L.subtype_injective, hcard]
    norm_num

omit [Finite X] in
theorem not_isCyclic_of_elemAbelian_four {E : Subgroup X} (hE : Open.IsElemAbelian 2 E)
    (hcard : Nat.card E = 4) : ¬ IsCyclic E := by
  intro hc
  obtain ⟨g, hg⟩ := hc.exists_generator
  have hgo : orderOf g = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have h2 : (g : X) ^ 2 = 1 := hE.2 g g.2
  have : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h2))
  rw [hgo] at this
  norm_num at this

theorem le_normalizer (h : Config t L) :
    centralizer ({t} : Set X) ≤ normalizer (L : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Cx := centralizer ({t} : Set X) with hCx
  by_contra hN
  obtain ⟨c, hc, hcN⟩ := IsConcreteLE.not_le_iff_exists.mp hN
  set φ : X ≃* X := MulAut.conj c⁻¹ with hφ
  have hφx : φ t = t := by
    rw [hφ, MulAut.conj_apply, inv_inv]
    have hcx : c * t = t * c := mem_centralizer_singleton_iff.mp hc
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hcx]
      _ = t := by group
  obtain ⟨hL'x, hL'⟩ := GSLit.isPComponent_map_centralizer φ h.le_centralizer h.isPComponent
  rw [hφx] at hL'x hL'
  set L' := L.map φ.toMonoidHom with hL'def
  have hne : L.subgroupOf Cx ≠ L'.subgroupOf Cx := by
    intro heq
    rw [subgroupOf_inj, inf_of_le_left h.le_centralizer, inf_of_le_left hL'x] at heq
    exact hcN (mem_normalizer_of_conjugate_eq heq.symm)
  obtain ⟨hN1, -, hcomm, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _
      h.isPComponent hL').2 hne
  have hL'C : L' ≤ coreActionKernel L := by
    intro g hg
    have hg' : (⟨g, hL'x hg⟩ : Cx) ∈ L'.subgroupOf Cx := hg
    refine ⟨mem_normalizer_of_subgroupOf h.le_centralizer (hN1 hg'), fun j hj => ?_⟩
    have hj' : (⟨j, h.le_centralizer hj⟩ : Cx) ∈ L.subgroupOf Cx := hj
    have h1 := hcomm (commutator_mem_commutator (inv_mem hj') (inv_mem hg'))
    have h2 := mem_map_of_mem Cx.subtype (mem_inf.mp h1).1
    rw [pPrimeCore_map_subgroupOf 2 L Cx h.le_centralizer] at h2
    simpa [commutatorElement_def] using h2
  obtain ⟨E, hEL, hE, hcard⟩ := h.exists_fourGroup
  have hE'L' : E.map φ.toMonoidHom ≤ L' := map_mono hEL
  have hE' : Open.IsElemAbelian 2 (E.map φ.toMonoidHom) := SectionRank.isElemAbelian_map hE _
  have hcard' : Nat.card (E.map φ.toMonoidHom) = 4 := by
    rw [card_map_of_injective φ.injective, hcard]
  exact h.false_of_noncyclic_le (IsPGroup.of_card (n := 2) (by rw [hcard']; norm_num))
    (not_isCyclic_of_elemAbelian_four hE' hcard') (hE'L'.trans hL'C)

end Config

end CFSG.ComponentClassification.HSFLit

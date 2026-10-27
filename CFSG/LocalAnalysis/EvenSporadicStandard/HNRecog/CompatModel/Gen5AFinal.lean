module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpInputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Gen5ASpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.CompatModel

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section4

theorem gen5a_transport {G : Type} [Group G] {a x : G} {M : Type} [Group M]
    (Φ : ↥(Gxy a x) ≃* M) {t₀ t₀' : M} (ho : orderOf t₀ = 2) (ho' : orderOf t₀' = 2)
    (hne : t₀ ≠ t₀') (hcomm : t₀ * t₀' = t₀' * t₀)
    (hcl : Subgroup.closure ((Subgroup.centralizer ({t₀} : Set M) : Set M) ∪
      (Subgroup.centralizer ({t₀'} : Set M) : Set M)) = ⊤) :
    ∃ t t' : G, t ∈ InvIn (Gxy a x) ∧ t' ∈ InvIn (Gxy a x) ∧ t ≠ t' ∧ t * t' = t' * t ∧
      Subgroup.closure ((Gxyz a t x : Set G) ∪ (Gxyz a t' x : Set G)) = Gxy a x := by
  have hcommG : ∀ {p q : M}, p * q = q * p →
      (Φ.symm p : G) * (Φ.symm q : G) = (Φ.symm q : G) * (Φ.symm p : G) := by
    intro p q h
    have := congrArg (fun r => (Φ.symm r : G)) h
    simpa only [map_mul, Subgroup.coe_mul] using this
  have hmem : ∀ {p t₁ : M}, p * t₁ = t₁ * p → (Φ.symm p : G) ∈ Gxyz a (Φ.symm t₁ : G) x := by
    intro p t₁ h
    exact mem_Gxyz.2 ⟨(mem_Gxy.1 (Φ.symm p).2).1, mem_Gx.2 (hcommG h.symm),
      (mem_Gxy.1 (Φ.symm p).2).2⟩
  refine ⟨(Φ.symm t₀ : G), (Φ.symm t₀' : G), ⟨(Φ.symm t₀).2, ?_⟩, ⟨(Φ.symm t₀').2, ?_⟩,
    fun e => hne (Φ.symm.injective (Subtype.ext e)), hcommG hcomm, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ho
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact ho'
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro g (hg | hg)
    · exact mem_Gxy.2 ⟨(mem_Gxyz.1 hg).1, (mem_Gxyz.1 hg).2.2⟩
    · exact mem_Gxy.2 ⟨(mem_Gxyz.1 hg).1, (mem_Gxyz.1 hg).2.2⟩
  · intro g hg
    let f : M →* G := (Gxy a x).subtype.comp Φ.symm.toMonoidHom
    have hle : Subgroup.closure ((Subgroup.centralizer ({t₀} : Set M) : Set M) ∪
        (Subgroup.centralizer ({t₀'} : Set M) : Set M)) ≤
        (Subgroup.closure ((Gxyz a (Φ.symm t₀ : G) x : Set G) ∪
          (Gxyz a (Φ.symm t₀' : G) x : Set G))).comap f := by
      refine (Subgroup.closure_le _).2 ?_
      rintro p (hp | hp)
      · exact Subgroup.subset_closure (Or.inl (hmem (Subgroup.mem_centralizer_singleton_iff.1 hp)))
      · exact Subgroup.subset_closure (Or.inr (hmem (Subgroup.mem_centralizer_singleton_iff.1 hp)))
    have hg' : Φ ⟨g, hg⟩ ∈ Subgroup.closure ((Subgroup.centralizer ({t₀} : Set M) : Set M) ∪
        (Subgroup.centralizer ({t₀'} : Set M) : Set M)) := by
      rw [hcl]
      exact Subgroup.mem_top _
    simpa [f] using hle hg'

end CFSG.EvenSporadicStandard.HNRecog.CompatModel

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.CompatModel CFSG.EvenSporadicStandard.HNRecog.Simple2S5

section Cert


theorem gen5a_holds : Gen5A := by
  intro G _ a z h x hx
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e⟩ := h.loc.tableVII.self.shape_5A x hx
  obtain ⟨f⟩ := nonempty_psu3_mulEquiv_i50
  obtain ⟨t₀, t₀', ho, ho', hne, hcomm, hcl⟩ := gen5a_model
  exact gen5a_transport (e.trans f) ho ho' hne hcomm hcl

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4

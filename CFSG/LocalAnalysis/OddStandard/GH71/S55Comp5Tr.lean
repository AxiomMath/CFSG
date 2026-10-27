module

public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Gen

public section

namespace CFSG.OddStandard.GH71.S55

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 C5

variable {Y Y' : Type} [Group Y] [Group Y']

theorem rFree_map (e : Y ≃* Y') {r : ℕ} {y : Y} (h : RFree r y) : RFree r (e y) := by
  intro E hE hEy
  have h1 : E.comap e.toMonoidHom = ⊥ := by
    refine h _ (hE.comap_of_injective e.toMonoidHom e.injective) ?_
    intro x hx
    rw [mem_comap] at hx ⊢
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, map_inv] using hEy _ hx
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective E, h1,
    Subgroup.map_bot]

theorem noR_congr (e : Y ≃* Y') {r : ℕ} : NoR r Y ↔ NoR r Y' := by
  constructor
  · intro h K _ _ hK ⟨e'⟩
    exact h K hK ⟨e'.trans e.symm⟩
  · intro h K _ _ hK ⟨e'⟩
    exact h K hK ⟨e'.trans e⟩

theorem pairSL2_map (e : Y ≃* Y') {p : ℕ} {y g : Y} (h : PairSL2 p y g) :
    PairSL2 p (e y) (e g) := by
  obtain ⟨F, _, _, hF, h⟩ := h
  have hcl : (closure ({y, g * y * g⁻¹} : Set Y)).map e.toMonoidHom =
      closure ({e y, e g * e y * (e g)⁻¹} : Set Y') := by
    rw [MonoidHom.map_closure, Set.image_pair]
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
  let ψ : ↥(closure ({y, g * y * g⁻¹} : Set Y)) ≃*
      ↥(closure ({e y, e g * e y * (e g)⁻¹} : Set Y')) :=
    ((Subgroup.closure ({y, g * y * g⁻¹} : Set Y)).equivMapOfInjective e.toMonoidHom
      e.injective).trans
      (MulEquiv.subgroupCongr hcl)
  refine ⟨F, inferInstance, inferInstance, hF, ?_⟩
  rcases h with ⟨φ, hφ⟩ | ⟨hR, φ, hφ⟩
  · exact Or.inl ⟨φ.comp ψ.symm.toMonoidHom, hφ.comp ψ.symm.surjective⟩
  · exact Or.inr ⟨fun h' => hR ((noR_congr e).mpr h'), φ.comp ψ.symm.toMonoidHom,
      hφ.comp ψ.symm.surjective⟩

theorem comp5Concl_of_map (e : Y ≃* Y') {r : ℕ} {y : Y} (h : Comp5Concl r (e y)) :
    Comp5Concl r y := by
  obtain ⟨L', hLt, hq, hc, hn, hcomm⟩ := h
  have hmap : (L'.comap e.toMonoidHom).map e.toMonoidHom = L' :=
    Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective L'
  let f : ↥(L'.comap e.toMonoidHom) ≃* ↥L' :=
    ((L'.comap e.toMonoidHom).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hmap)
  refine ⟨L'.comap e.toMonoidHom, ?_, LocalCores.isQuasisimple_of_mulEquiv f.symm hq,
    oddChev_congr (centerQuotCongr f.symm) hc, ?_, ?_⟩
  · intro htop
    apply hLt
    rw [← hmap, htop, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [mem_normalizer_iff]
    intro x
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    exact mem_normalizer_iff.mp hn (e x)
  · intro hb
    apply hcomm
    have h1 := congrArg (Subgroup.map e.toMonoidHom) hb
    rwa [Subgroup.map_commutator, hmap, MonoidHom.map_zpowers, Subgroup.map_bot] at h1

theorem comp5Concl_of_mulEquiv (e : Y ≃* Y') {r p : ℕ} {y g : Y}
    (h : orderOf (e y) = p → RFree r (e y) → PairSL2 p (e y) (e g) → Comp5Concl r (e y))
    (hy : orderOf y = p) (hyr : RFree r y) (hJ : PairSL2 p y g) : Comp5Concl r y :=
  comp5Concl_of_map e (h ((MulEquiv.orderOf_eq e y).trans hy) (rFree_map e hyr)
    (pairSL2_map e hJ))

end CFSG.OddStandard.GH71.S55

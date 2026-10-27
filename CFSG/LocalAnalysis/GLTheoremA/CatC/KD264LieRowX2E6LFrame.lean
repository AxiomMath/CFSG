module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX2E6Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

open CFSG.Open

@[expose] def FrameSubP (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop) (S : Type)
    [Group S] [Finite S] (P : Subgroup (MulAut S)) : Prop :=
  ∃ (V : Subgroup (MulAut S)) (φ : V ≃* Multiplicative (Fin 6 → ZMod 3))
    (ρ : P →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)),
    (∀ v ∈ V, v ∈ P) ∧
    (∀ x : P, ∀ v : V, ∃ w : V, (x : MulAut S) * (v : MulAut S) * (x : MulAut S)⁻¹ = (w : MulAut S)) ∧
    (∀ (x : P) (v w : V),
        (x : MulAut S) * (v : MulAut S) * (x : MulAut S)⁻¹ = (w : MulAut S) →
        Multiplicative.toAdd (φ w) =
          Matrix.mulVec (ρ x : Matrix (Fin 6) (Fin 6) (ZMod 3)) (Multiplicative.toAdd (φ v))) ∧
    (∀ x : P, ρ x = 1 ↔ (x : MulAut S) ∈ V) ∧
    (∀ x : P, ρ x ∈ W3) ∧
    (∀ G : Subgroup (Multiplicative (Fin 6 → ZMod 3)), Sel G →
      RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) '' (G : Set _)) →
        IsGood 3 ((G.map φ.symm.toMonoidHom).map V.subtype))

theorem frameSubP_of_embedding (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop)
    {S : Type} [Group S] [Finite S] {Q : Type} [Group Q] (ι : Q →* MulAut S) (hι : Function.Injective ι)
    (U : Subgroup Q) (c : U ≃* Multiplicative (Fin 6 → ZMod 3))
    (r : Q →* Matrix.GeneralLinearGroup (Fin 6) (ZMod 3))
    (hU : ∀ (x : Q) (u : U), x * (u : Q) * x⁻¹ ∈ U)
    (hc : ∀ (x : Q) (u w : U), x * (u : Q) * x⁻¹ = (w : Q) →
      Multiplicative.toAdd (c w) =
        Matrix.mulVec (r x : Matrix (Fin 6) (Fin 6) (ZMod 3)) (Multiplicative.toAdd (c u)))
    (hker : ∀ x : Q, r x = 1 ↔ x ∈ U) (hW : ∀ x : Q, r x ∈ W3)
    (hgood : ∀ G : Subgroup (Multiplicative (Fin 6 → ZMod 3)), Sel G →
      RootGood ((fun g : Multiplicative (Fin 6 → ZMod 3) => Multiplicative.toAdd g) ''
        (G : Set _)) →
        IsGood 3 ((G.map c.symm.toMonoidHom).map (ι.comp U.subtype))) :
    FrameSubP Sel S ι.range := by
  let eU : U ≃* U.map ι := U.equivMapOfInjective ι hι
  let eP : Q ≃* ι.range := MonoidHom.ofInjective hι
  have hU' : ∀ u : U, ((eU u : U.map ι) : MulAut S) = ι (u : Q) := fun u => rfl
  have hP' : ∀ q : Q, ((eP q : ι.range) : MulAut S) = ι q := fun q => rfl
  have hv : ∀ v : U.map ι, (v : MulAut S) = ι ((eU.symm v : U) : Q) := fun v => by
    rw [← hU', MulEquiv.apply_symm_apply]
  have hx : ∀ x : ι.range, (x : MulAut S) = ι (eP.symm x) := fun x => by
    rw [← hP', MulEquiv.apply_symm_apply]
  refine ⟨U.map ι, eU.symm.trans c, r.comp eP.symm.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro v ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  · intro x v
    refine ⟨eU ⟨eP.symm x * (eU.symm v : U) * (eP.symm x)⁻¹, hU _ _⟩, ?_⟩
    rw [hU', hx x, hv v]
    simp [map_mul, map_inv]
  · intro x v w h
    rw [hx x, hv v, hv w, ← map_inv, ← map_mul, ← map_mul] at h
    have h2 := hι h
    exact hc (eP.symm x) (eU.symm v) (eU.symm w) h2
  · intro x
    show r (eP.symm x) = 1 ↔ _
    rw [hker]
    constructor
    · intro hq
      refine ⟨eP.symm x, hq, ?_⟩
      exact (hx x).symm
    · rintro ⟨q', hq', hq''⟩
      have : q' = eP.symm x := hι (hq''.trans (hx x))
      rw [← this]
      exact hq'
  · intro x
    exact hW _
  · intro G hS hG
    have := hgood G hS hG
    convert this using 2
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1

theorem frameSubP_map_mulEquiv (Sel : Subgroup (Multiplicative (Fin 6 → ZMod 3)) → Prop)
    {S T : Type} [Group S] [Finite S] [Group T] [Finite T]
    (e : S ≃* T) {P : Subgroup (MulAut S)} (h : FrameSubP Sel S P) :
    FrameSubP Sel T (P.map (MulAut.congr e).toMonoidHom) := by
  obtain ⟨V, φ, ρ, h1, h2, h3, h4, h5, h6⟩ := h
  have hVP : V ≤ P := fun v hv => h1 v hv
  let ι : P →* MulAut T := (MulAut.congr e).toMonoidHom.comp P.subtype
  have hι : Function.Injective ι := fun a b hab =>
    Subtype.ext ((MulAut.congr e).injective hab)
  let c : V.subgroupOf P ≃* Multiplicative (Fin 6 → ZMod 3) :=
    (Subgroup.subgroupOfEquivOfLe hVP).trans φ
  have hrange : ι.range = P.map (MulAut.congr e).toMonoidHom := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  refine frameSubP_of_embedding Sel ι hι (V.subgroupOf P) c ρ ?_ ?_ ?_ ?_ ?_
  · intro x u
    obtain ⟨w, hw⟩ := h2 x ⟨((u : P) : MulAut S), Subgroup.mem_subgroupOf.1 u.2⟩
    rw [Subgroup.mem_subgroupOf]
    show (x : MulAut S) * ((u : P) : MulAut S) * (x : MulAut S)⁻¹ ∈ V
    rw [hw]
    exact w.2
  · intro x u w huw
    have := h3 x ⟨((u : P) : MulAut S), Subgroup.mem_subgroupOf.1 u.2⟩
      ⟨((w : P) : MulAut S), Subgroup.mem_subgroupOf.1 w.2⟩ (congrArg Subtype.val huw)
    exact this
  · intro x
    rw [h4 x, Subgroup.mem_subgroupOf]
  · intro x
    exact h5 x
  · intro G hS hG
    have := (RowXUn.isGood_iff_map_mulEquiv e _).1 (h6 G hS hG)
    convert this using 1
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X2E6

end

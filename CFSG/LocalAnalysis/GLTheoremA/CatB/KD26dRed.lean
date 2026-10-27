module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KD26
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38Model3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.RankThree.PartTwo.Sec4.Item434U38
open CFSG.ComponentClassification.OuterAutomorphisms (inner_map_congr)

@[expose] def U38MeetsX : Prop :=
  ∀ E : Subgroup U38G, IsElemAbelian 3 E → Nat.card E = 9 →
    ∃ x ∈ E, x ≠ 1 ∧ (x : Equiv.Perm (Fin 513)) ∈ X'

@[expose] def U38SylowMeetsX : Prop :=
  ∃ Q : Sylow 3 U38G, ∀ E : Subgroup U38G, E ≤ (Q : Subgroup U38G) → IsElemAbelian 3 E →
    Nat.card E = 9 → ∃ x ∈ E, x ≠ 1 ∧ (x : Equiv.Perm (Fin 513)) ∈ X'

section Reduction


theorem u38MeetsX_of_sylow (h : U38SylowMeetsX) : U38MeetsX := by
  intro E hE hcard
  obtain ⟨Q, hQ⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun y => ⟨1, by simpa using Subtype.ext (hE.2 (y : U38G) y.2)⟩
  obtain ⟨P, hEP⟩ := hE3.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq U38G P Q
  have hconj : ∀ e ∈ E, g * e * g⁻¹ ∈ (Q : Subgroup U38G) := by
    intro e he
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨e, hEP he, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  let E' : Subgroup U38G := E.map (MulAut.conj g).toMonoidHom
  have hE'Q : E' ≤ (Q : Subgroup U38G) := by
    rintro _ ⟨e, he, rfl⟩
    exact hconj e he
  have hE'ab : IsElemAbelian 3 E' := hE.map (MulAut.conj g).toMonoidHom
  have hE'card : Nat.card E' = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]
  obtain ⟨x, hxE', hx1, hxX⟩ := hQ E' hE'Q hE'ab hE'card
  obtain ⟨e, he, rfl⟩ := hxE'
  refine ⟨e, he, ?_, ?_⟩
  · rintro rfl
    exact hx1 (by simp)
  ·
    have hn : ((g : Equiv.Perm (Fin 513))⁻¹) ∈
        Subgroup.normalizer (X' : Set (Equiv.Perm (Fin 513))) :=
      U38G_le_normalizer (U38G.inv_mem g.2)
    have h1 := (Subgroup.mem_normalizer_iff.1 hn
      ((g : Equiv.Perm (Fin 513)) * (e : Equiv.Perm (Fin 513)) * (g : Equiv.Perm (Fin 513))⁻¹)).1
      (by simpa [MulAut.conj_apply] using hxX)
    simpa [mul_assoc] using h1

theorem kd26d_of_u38MeetsX (h : U38MeetsX) : CFSG.LocalAnalysis.GLTheoremA.KD26d := by
  intro S _ _ hS D hD hcard
  have hcat : catalogIs S S9.isU3eight := by
    obtain ⟨i, hi, hf⟩ := hS
    refine ⟨i, ?_, hf⟩
    cases i with
    | cyclic p hp => simp [onLie] at hi
    | alternating n hn => simp [onLie] at hi
    | sporadic s => simp [onLie] at hi
    | lie idx =>
      obtain ⟨d, hv⟩ := idx
      cases d with
      | twistedA r q =>
        simp only [onLie, isLnEps] at hi
        obtain ⟨hr, hq⟩ := hi
        have hr2 : r = 2 := by omega
        subst hr2
        simpa [S9.isU3eight, onLie] using hq
      | _ => simp [onLie, isLnEps] at hi
  have hX : Nonempty (S ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    obtain ⟨e⟩ := bridge_u3eight hcat
    have hP : CFSG.PGLModel.projImage (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 6)) =
        CFSG.PGLModel.projSU 3 2 3 :=
      CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 2 3
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage _ hP)⟩
  obtain ⟨eX⟩ := nonempty_equiv_X' hX
  let ρ' : U38G ≃* MulAut X' := MulEquiv.ofBijective rhoU38 (rhoU38_bijective hX)
  let κ : MulAut S →* U38G :=
    ρ'.symm.toMonoidHom.comp (MulAut.congr eX).toMonoidHom
  have hκinj : Function.Injective κ := ρ'.symm.injective.comp (MulAut.congr eX).injective
  have hE : IsElemAbelian 3 (D.map κ) := hD.map κ
  have hEcard : Nat.card (D.map κ) = 9 := by
    rw [Subgroup.card_map_of_injective hκinj, hcard]
  obtain ⟨x, hxE, hx1, hxX⟩ := h _ hE hEcard
  obtain ⟨d, hdD, rfl⟩ := Subgroup.mem_map.1 hxE
  refine ⟨d, Subgroup.mem_inf.2 ⟨hdD, ?_⟩, ?_⟩
  ·
    have h1 : ρ' (κ d) = MulAut.congr eX d := by
      change ρ' (ρ'.symm (MulAut.congr eX d)) = MulAut.congr eX d
      exact ρ'.apply_symm_apply _
    have h2 : ρ' (κ d) = MulAut.conj (⟨(κ d : Equiv.Perm (Fin 513)), hxX⟩ : X') := by
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      rw [MulAut.conj_apply]
      exact rhoU38_apply _ _
    have h3 : MulAut.congr eX d ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner X' := by
      rw [← h1, h2]
      exact ⟨_, rfl⟩
    rw [← inner_map_congr eX] at h3
    obtain ⟨d', hd', hd'eq⟩ := h3
    have : d' = d := (MulAut.congr eX).injective hd'eq
    rw [← this]
    exact hd'
  · intro hd
    apply hx1
    rw [hd, map_one]

end Reduction

end CFSG.LocalAnalysis.GLTheoremA.CatB

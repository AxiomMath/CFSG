module

public import CFSG.GH74.Generic.BProg.B2.GenLocL3Blk
public import CFSG.GH74.Generic.BProg.B2.GenLocL2SLAll
public import CFSG.GH74.Generic.BProg.B2.GenLocL3NF
public import CFSG.GH74.Generic.BProg.B2.GenLocL5Out

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

namespace GenLocL3Lin

theorem genProp_of_mulEquiv {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (h : GenProp J) :
    GenProp J' := by
  intro A _ _ α' hA
  let α : A →* MulAut J := (MulAut.congr e.symm).toMonoidHom.comp α'
  have hc : ∀ a x, α' a (e x) = e (α a x) := by
    intro a x
    simp [α, MulAut.congr_apply]
  rw [GenLocBasic.gammaAct_map_equiv e α α' hc, h A α hA,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem gammaAct_eq_top_of_conj {J : Type} [Group J] {A : Type} [Group A] (α : A →* MulAut J)
    (β : MulAut J) (h : gammaAct ((MulAut.conj β).toMonoidHom.comp α) = ⊤) : gammaAct α = ⊤ := by
  let α' : A →* MulAut J := (MulAut.conj β).toMonoidHom.comp α
  have hc : ∀ a x, α' a (β x) = β (α a x) := by
    intro a x
    change (β * α a * β⁻¹) (β x) = β (α a x)
    simp
  have h2 := GenLocBasic.gammaAct_map_equiv (β : J ≃* J) α α' hc
  have h4 : (gammaAct α).map (β : J ≃* J).toMonoidHom = ⊤ := h2.symm.trans h
  have h5 := Subgroup.comap_map_eq_self_of_injective (f := (β : J ≃* J).toMonoidHom)
    (β : J ≃* J).injective (gammaAct α)
  rw [h4, Subgroup.comap_top] at h5
  exact h5.symm

end GenLocL3Lin

section L32

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_eq_top_of_le_frameStab
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h11 : 11 ≤ p ^ f)
    (α : A →* MulAut (LinearFlag.projectiveSL 3 K)) (hA : IsRank23 A)
    (hα : α.range ≤ frameStab 3 K) : gammaAct α = ⊤ := by
  have hex : ∀ i : Fin 2, ∃ β : A →* MulAut SL(2, K), ∀ (a : A) (g : SL(2, K)),
      α a (GenLocL3Blk.phi i g) = GenLocL3Blk.phi i (β a g) := fun i =>
    GenLocL3Blk.exists_restrict_action (GenLocL3Blk.phi i) (GenLocL3Blk.phi_injective i) α
      fun a g => GenLocL3Blk.stable_phi (hα ⟨a, rfl⟩) i g
  choose β hβ using hex
  refine gammaAct_eq_top_of_equivariant α (fun _ : Fin 2 => SL(2, K)) (fun i => GenLocL3Blk.phi i) β
    (fun i a g => hβ i a g) ?_ fun i => gammaAct_sl2_of_ge11 hp hp2 hK h11 (β i) hA
  rw [eq_top_iff, ← GenLocL3Blk.range_phi_sup]
  exact sup_le (le_iSup (fun i : Fin 2 => (GenLocL3Blk.phi (K := K) i).range) 0)
    (le_iSup (fun i : Fin 2 => (GenLocL3Blk.phi (K := K) i).range) 1)

end L32

namespace GenLocL3Lin

theorem genProp_projectiveSL3
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h11 : 11 ≤ p ^ f) :
    GenProp (LinearFlag.projectiveSL 3 K) := by
  intro A _ _ α hA
  have hD : CFSG.IsElementaryAbelian 2 ↥α.range :=
    GenLocBasic.isEA_of_surjective hA.1 α.rangeRestrict α.rangeRestrict_surjective
  obtain ⟨β, hβ⟩ := exists_conj_le_frameStab hp hp2 hK α.range hD
  refine gammaAct_eq_top_of_conj α β ?_
  refine gammaAct_eq_top_of_le_frameStab hp hp2 hK h11 _ hA ?_
  rintro _ ⟨a, rfl⟩
  exact hβ ⟨α a, ⟨a, rfl⟩, rfl⟩

end GenLocL3Lin

section PSL3

theorem genProp_psl3_lin
    {J : Type} [Group J] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h11 : 11 ≤ p ^ f) (hJ : LieModel J .PSL 3 p f) : GenProp J := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hJ
  let ψ : J ≃* LinearFlag.projectiveSL 3 F :=
    e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.trans
      (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL
        3 F))
  exact GenLocL3Lin.genProp_of_mulEquiv ψ.symm
    (GenLocL3Lin.genProp_projectiveSL3 hp hp2 hF h11)

end PSL3

end CFSG.GH74.Generic.BProg.B2

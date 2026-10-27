module

public import CFSG.GH74.GLS.LU.Local.FiveModelLeaf
public import CFSG.GH74.GLS.Stage2.Final.ModelDisjoint
public import CFSG.GH74.GLS.LU.Local.FiveL66a

public section

open Subgroup CFSG CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace CFSG.GH74.GLS.LU.Local.Five

section Symm

variable {G Gs : Type} [Group G] [Group Gs] {z : G} {S : Sylow 2 G} {z' : Gs} {S' : Sylow 2 Gs}

noncomputable def CompatIso.symm' (I : CompatIso G z S z' S') : CompatIso Gs z' S' z S where
  ψ := I.ψ.symm
  mem_S x := by
    have h := I.mem_S (I.ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at h
    exact h.symm
  fusion x y hx hy hxo hyo := by
    have hord : ∀ w : ↥(layerTimesSylow z' (S' : Subgroup Gs)), orderOf (w : Gs) = 2 →
        orderOf (((I.ψ.symm w : ↥(layerTimesSylow z (S : Subgroup G))) : G)) = 2 := by
      intro w hw
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hw
    have hx' : ((I.ψ.symm x : ↥(layerTimesSylow z (S : Subgroup G))) : G) ∈ (S : Subgroup G) :=
      (I.mem_S (I.ψ.symm x)).mpr (by rw [MulEquiv.apply_symm_apply]; exact hx)
    have hy' : ((I.ψ.symm y : ↥(layerTimesSylow z (S : Subgroup G))) : G) ∈ (S : Subgroup G) :=
      (I.mem_S (I.ψ.symm y)).mpr (by rw [MulEquiv.apply_symm_apply]; exact hy)
    have h := I.fusion (I.ψ.symm x) (I.ψ.symm y) hx' hy' (hord x hxo) (hord y hyo)
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    exact h.symm

end Symm

section PullPull

variable {G Gs : Type*} [Group G] [Group Gs] {X : Subgroup G} {X' : Subgroup Gs}

theorem pull_symm_pull (ψ : ↥X ≃* ↥X') {L : Subgroup G} (hL : L ≤ X) :
    pull ψ (pull ψ.symm L) = L := by
  ext x
  constructor
  · intro h
    obtain ⟨hx, h1⟩ := (mem_pull_iff ψ _).mp h
    have h2 := (mem_pull ψ.symm L (ψ ⟨x, hx⟩).2).mp h1
    simpa using h2
  · intro h
    have hx := hL h
    rw [mem_pull ψ _ hx, mem_pull ψ.symm L (ψ ⟨x, hx⟩).2]
    simpa using h

theorem pull_equivOfEq {Y : Subgroup G} {Y' : Subgroup Gs} (ψ : ↥X ≃* ↥X') (h1 : X = Y)
    (h2 : X' = Y') (E : Subgroup Gs) :
    pull (((MulEquiv.subgroupCongr h1.symm).trans ψ).trans (MulEquiv.subgroupCongr h2)) E = pull ψ E := by
  subst h1
  subst h2
  rfl

end PullPull

section Layer

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem FiveCtx.layer_eq (c : FiveCtx G p f z S K₁ K₂ t u) :
    layerTimesSylow z (S : Subgroup G) = Cz z := by
  apply le_antisymm
  · exact sup_le (Lay_le z) c.hs.S_le_Cz
  · rw [c.Cz_eq]
    exact sup_le_sup_right (sup_le (le_layer_of_isCompIn c.hc.comp₁)
      (le_layer_of_isCompIn c.hc.comp₂)) _

end Layer

section Pic

variable {G : Type} [Group G] {Gs : Type} [Group Gs]

theorem mem_Cz_self (z : G) : z ∈ Cz z := Subgroup.mem_centralizer_singleton_iff.mpr rfl

structure ModelPic (z t u : G) (K₁ K₂ : Subgroup G) (ht : t ∈ Cz z) (hu : u ∈ Cz z) (z' : Gs)
    (S' : Sylow 2 Gs) (K₁' K₂' : Subgroup Gs) (t' u' : Gs) (ψ : ↥(Cz z) ≃* ↥(Cz z')) : Prop where
  psi_z : ((ψ ⟨z, mem_Cz_self z⟩ : ↥(Cz z')) : Gs) = z'
  psi_t : ((ψ ⟨t, ht⟩ : ↥(Cz z')) : Gs) = t'
  psi_u : ((ψ ⟨u, hu⟩ : ↥(Cz z')) : Gs) = u'
  K₁_eq : pull ψ K₁' = K₁
  K₂_eq : pull ψ K₂' = K₂
  K₁'_le : K₁' ≤ Cz z'
  K₂'_le : K₂' ≤ Cz z'
  facts : FiveModelFacts z' S' K₁' K₂' t' u'

end Pic

section ExistsPic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
  {t u : G}

theorem FiveCtx.t_mem_Cz (c : FiveCtx G p f z S K₁ K₂ t u) : t ∈ Cz z :=
  Subgroup.mem_centralizer_singleton_iff.mpr c.hs.zt_comm.symm

theorem FiveCtx.u_mem_Cz (c : FiveCtx G p f z S K₁ K₂ t u) : u ∈ Cz z :=
  Subgroup.mem_centralizer_singleton_iff.mpr c.hs.zu_comm.symm

def FiveModelPart (G : Type) [Group G] (z : G) (S : Sylow 2 G) : Prop :=
  ∃ (Gs : Type) (_ : Group Gs) (S' : Sylow 2 Gs) (z' : Gs),
    LieModel Gs .PSL 4 5 1 ∧
      (center ↥(S' : Subgroup Gs)).map (S' : Subgroup Gs).subtype = zpowers z' ∧ orderOf z' = 2 ∧
      Nonempty (CompatIso G z S z' S')

theorem exists_model_pic_aux (hB : FiveModelBaseLeaf) (hM : FiveModelLeaf)
    (hmod : FiveModelPart G z S) (c : FiveCtx G p f z S K₁ K₂ t u) :
    ∃ (Gs : Type) (_ : Group Gs) (z' : Gs) (S' : Sylow 2 Gs) (K₁' K₂' : Subgroup Gs) (t' u' : Gs)
      (ψ : ↥(Cz z) ≃* ↥(Cz z')), ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ := by
  classical
  obtain ⟨Gs, _inst, S', z', hL, hz', hz'2, ⟨I⟩⟩ := hmod
  have : Finite Gs := by
    obtain ⟨-, F, _, fF, -, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psl_unpack hL
    have : Finite (StatedProj (StatedSL 4 F)) := inferInstance
    exact Finite.of_equiv _ e.symm.toEquiv
  have B := hB Gs hL z' S' hz' hz'2
  have hz : (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype = zpowers z := c.hs.z_cen
  have hcyc' : IsCyclic ↥(A0 z') := by rw [B.A0_bot]; infer_instance
  have hcomps := LUComps.transport (CompatIso.symm' I) hz' hz hcyc' c.hc5 c.hs.z_inv
  obtain ⟨t₁, u₁, ht₁, hu₁, hψt, hψu, hsyl⟩ := LUSyl.transport (CompatIso.symm' I) hz' hz c.hc5 c.hs
  have F := hM Gs hL z' S' _ _ t₁ u₁ hcomps hsyl
  have h1 : layerTimesSylow z (S : Subgroup G) = Cz z := c.layer_eq
  have h2 : layerTimesSylow z' (S' : Subgroup Gs) = Cz z' := B.lay_eq
  let ψ : ↥(Cz z) ≃* ↥(Cz z') :=
    ((MulEquiv.subgroupCongr h1.symm).trans I.ψ).trans (MulEquiv.subgroupCongr h2)
  have hK₁X : K₁ ≤ layerTimesSylow z (S : Subgroup G) :=
    (le_layer_of_isCompIn c.hc5.comp₁).trans le_sup_left
  have hK₂X : K₂ ≤ layerTimesSylow z (S : Subgroup G) :=
    (le_layer_of_isCompIn c.hc5.comp₂).trans le_sup_left
  refine ⟨Gs, inferInstance, z', S', pull I.ψ.symm K₁, pull I.ψ.symm K₂, t₁, u₁, ψ, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, F⟩
  · exact I.psi_z hz hz' hz'2
  · have e : (I.ψ.symm ⟨t₁, ht₁⟩ : ↥(layerTimesSylow z (S : Subgroup G))) = ⟨t, h1 ▸ c.t_mem_Cz⟩ :=
      Subtype.ext hψt
    have := congrArg (fun a => ((I.ψ a : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs)) e
    simp only [MulEquiv.apply_symm_apply] at this
    exact this.symm
  · have e : (I.ψ.symm ⟨u₁, hu₁⟩ : ↥(layerTimesSylow z (S : Subgroup G))) = ⟨u, h1 ▸ c.u_mem_Cz⟩ :=
      Subtype.ext hψu
    have := congrArg (fun a => ((I.ψ a : ↥(layerTimesSylow z' (S' : Subgroup Gs))) : Gs)) e
    simp only [MulEquiv.apply_symm_apply] at this
    exact this.symm
  · rw [pull_equivOfEq I.ψ h1 h2]
    exact pull_symm_pull I.ψ hK₁X
  · rw [pull_equivOfEq I.ψ h1 h2]
    exact pull_symm_pull I.ψ hK₂X
  · rw [← h2]; exact pull_le I.ψ.symm K₁
  · rw [← h2]; exact pull_le I.ψ.symm K₂

theorem exists_model_pic (hB : FiveModelBaseLeaf) (hM : FiveModelLeaf)
    (c : FiveCtx G p f z S K₁ K₂ t u) :
    ∃ (Gs : Type) (_ : Group Gs) (z' : Gs) (S' : Sylow 2 Gs) (K₁' K₂' : Subgroup Gs) (t' u' : Gs)
      (ψ : ↥(Cz z) ≃* ↥(Cz z')), ModelPic z t u K₁ K₂ c.t_mem_Cz c.u_mem_Cz z' S' K₁' K₂' t' u' ψ :=
  exists_model_pic_aux hB hM c.extra.model c

end ExistsPic

end CFSG.GH74.GLS.LU.Local.Five

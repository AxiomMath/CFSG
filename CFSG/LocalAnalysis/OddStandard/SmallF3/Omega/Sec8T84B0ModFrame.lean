module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModAct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModBlk
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84B0ModRes
public import Certificates.Data.Asc82NormA6

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace T84Mod

open Matrix Certificates.Asc82NormA6
open Certificates.A5GL42 (Mat4)

structure Frame {G : Type} [Group G] (E B : Subgroup G) (hBE : B ≤ E) (u : MulAut ↥E)
    (hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B) (A : Subgroup (MulAut ↥E))
    (hAu : ∀ a ∈ A, a * u = u * a) where
  eB : ↥B ≃* Multiplicative (Fin 4 → ZMod 2)
  ψ : ↥A ≃* alternatingGroup (Fin 6)
  θ : ↥E ≃* Multiplicative (Fin 4 ⊕ Fin 4 → ZMod 2)
  res_acts : ∀ (a : ↥A) (b : ↥B),
    Multiplicative.toAdd (eB (resB hBE u hfix (a : MulAut ↥E) (hAu a a.2) b)) =
      rho ((ψ a : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) *ᵥ Multiplicative.toAdd (eB b)
  θ_emb : ∀ b : ↥B, θ (embB hBE b) =
    Multiplicative.ofAdd (Sum.elim (Multiplicative.toAdd (eB b)) 0)
  θ_u : Acts θ u (blk 1 1)

noncomputable def matHom {ι : Type} [Fintype ι] [DecidableEq ι] {W : Type} [Group W]
    (θ : W ≃* Multiplicative (ι → ZMod 2)) : MulAut W →* Matrix ι ι (ZMod 2) :=
  { toFun := fun g => Classical.choose (exists_acts θ g),
    map_one' := Acts.matrix_eq (Classical.choose_spec (exists_acts θ 1)) (acts_one θ),
    map_mul' := fun g g' => Acts.matrix_eq (Classical.choose_spec (exists_acts θ (g * g')))
      (Acts.mul (Classical.choose_spec (exists_acts θ g))
        (Classical.choose_spec (exists_acts θ g'))) }

private theorem matHom_apply {ι : Type} [Fintype ι] [DecidableEq ι] {W : Type} [Group W]
    (θ : W ≃* Multiplicative (ι → ZMod 2)) (g : MulAut W) :
    matHom θ g = Classical.choose (exists_acts θ g) := rfl

theorem matHom_acts {ι : Type} [Fintype ι] [DecidableEq ι] {W : Type} [Group W]
    (θ : W ≃* Multiplicative (ι → ZMod 2)) (g : MulAut W) : Acts θ g (matHom θ g) := by
  rw [matHom_apply θ g]
  exact Classical.choose_spec (exists_acts θ g)

theorem matHom_eq {ι : Type} [Fintype ι] [DecidableEq ι] {W : Type} [Group W]
    {θ : W ≃* Multiplicative (ι → ZMod 2)} {g : MulAut W} {M : Matrix ι ι (ZMod 2)}
    (h : Acts θ g M) : matHom θ g = M :=
  Acts.matrix_eq (matHom_acts θ g) h

variable {G : Type} [Group G] {E B : Subgroup G} {hBE : B ≤ E} {u : MulAut ↥E}
  {hfix : ∀ e : ↥E, u e = e ↔ (e : G) ∈ B} {A : Subgroup (MulAut ↥E)}
  {hAu : ∀ a ∈ A, a * u = u * a}

private theorem embB_injective (hBE' : B ≤ E) : Function.Injective (embB hBE') := by
  intro b₁ b₂ h
  exact Subtype.ext (congrArg (fun e : ↥E => (e : G)) h)

theorem Frame.exists_blk (F : Frame E B hBE u hfix A hAu) (g : MulAut ↥E) (hg : g * u = u * g) :
    ∃ α U : Mat4, Acts F.θ g (blk α U) ∧ ∀ b : ↥B,
      Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b)) =
        α *ᵥ Multiplicative.toAdd (F.eB b) := by
  obtain ⟨M, hM⟩ := exists_acts F.θ g
  have hcomm : M * blk 1 1 = blk 1 1 * M := by
    have h1 : Acts F.θ (g * u) (M * blk 1 1) := hM.mul F.θ_u
    have h2 : Acts F.θ (g * u) (blk 1 1 * M) := by
      have h2' : Acts F.θ (u * g) (blk 1 1 * M) := F.θ_u.mul hM
      rw [hg.symm] at h2'
      exact h2'
    exact Acts.matrix_eq h1 h2
  obtain ⟨α, U, hMU⟩ := eq_blk_of_comm hcomm
  refine ⟨α, U, ?_, ?_⟩
  · rw [← hMU]
    exact hM
  · intro b
    have h1 : Multiplicative.toAdd (F.θ (g (embB hBE b)))
        = Sum.elim (Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b))) 0 := by
      rw [← embB_resB hBE u hfix g hg b, F.θ_emb]
      rfl
    have h2 : Multiplicative.toAdd (F.θ (g (embB hBE b)))
        = blk α U *ᵥ Sum.elim (Multiplicative.toAdd (F.eB b)) 0 := by
      rw [hM (embB hBE b), F.θ_emb b, hMU]
      simp
    have h3 : Sum.elim (Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b))) 0
        = blk α U *ᵥ Sum.elim (Multiplicative.toAdd (F.eB b)) 0 := h1.symm.trans h2
    rw [blk_mulVec, Matrix.mulVec_zero, add_zero] at h3
    funext i
    exact congrFun h3 (Sum.inl i)

theorem Frame.card_fix_B (F : Frame E B hBE u hfix A hAu) (g : MulAut ↥E) (hg : g * u = u * g)
    (X : Mat4) (hX : ∀ b : ↥B,
      Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b)) = X *ᵥ Multiplicative.toAdd (F.eB b)) :
    Nat.card {e : ↥E // (e : G) ∈ B ∧ g e = e} =
      (Finset.univ.filter fun x : Fin 4 → ZMod 2 => X *ᵥ x = x).card := by
  classical
  have key : ∀ b : ↥B, resB hBE u hfix g hg b = b ↔
      X *ᵥ Multiplicative.toAdd (F.eB b) = Multiplicative.toAdd (F.eB b) := by
    intro b
    constructor
    · intro hb
      have h := hX b
      rw [hb] at h
      exact h.symm
    · intro hb
      apply F.eB.injective
      apply Multiplicative.toAdd.injective
      rw [hX b, hb]
  let sB : {e : ↥E // (e : G) ∈ B} ≃ ↥B :=
    { toFun := fun e => ⟨(e.1 : G), e.2⟩,
      invFun := fun b => ⟨embB hBE b, b.2⟩,
      left_inv := fun e => Subtype.ext (Subtype.ext rfl),
      right_inv := fun b => Subtype.ext rfl }
  have hP : ∀ a : {e : ↥E // (e : G) ∈ B}, (g a.1 = a.1) ↔
      (resB hBE u hfix g hg (sB a) = sB a) := by
    intro a
    have he : embB hBE (sB a) = a.1 := Subtype.ext rfl
    constructor
    · intro ha
      apply embB_injective hBE
      rw [embB_resB, he]
      exact ha
    · intro ha
      have h := congrArg (fun b : ↥B => embB hBE b) ha
      rw [embB_resB, he] at h
      exact h
  have hequiv : {e : ↥E // (e : G) ∈ B ∧ g e = e} ≃
      {x : Fin 4 → ZMod 2 // X *ᵥ x = x} :=
    (((Equiv.subtypeSubtypeEquivSubtypeInter (fun e : ↥E => (e : G) ∈ B)
      (fun e : ↥E => g e = e)).symm).trans (Equiv.subtypeEquiv sB hP)).trans
      (Equiv.subtypeEquiv (F.eB.toEquiv.trans Multiplicative.toAdd) fun b => key b)
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem Frame.matrix_unique (F : Frame E B hBE u hfix A hAu) (g : MulAut ↥E) (hg : g * u = u * g)
    (X X' : Mat4)
    (hX : ∀ b : ↥B,
      Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b)) = X *ᵥ Multiplicative.toAdd (F.eB b))
    (hX' : ∀ b : ↥B,
      Multiplicative.toAdd (F.eB (resB hBE u hfix g hg b)) = X' *ᵥ Multiplicative.toAdd (F.eB b)) :
    X = X' := by
  have hv : ∀ v : Fin 4 → ZMod 2, X *ᵥ v = X' *ᵥ v := by
    intro v
    obtain ⟨b, hb⟩ := F.eB.surjective (Multiplicative.ofAdd v)
    have hb' : Multiplicative.toAdd (F.eB b) = v := by rw [hb]; rfl
    rw [← hb', ← hX b, hX' b]
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by simpa using hv v)

end T84Mod

end CFSG.OddStandard.SmallF3.Omega

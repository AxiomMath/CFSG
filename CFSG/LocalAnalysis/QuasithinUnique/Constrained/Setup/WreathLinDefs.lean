module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerConj

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Wreath

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.Quasithin.B6
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

@[expose] def linWreath {ι : Type*} (W : Submodule k V) (I : ι → Submodule k V)
    (P : Subgroup (Equiv.Perm ι)) : Subgroup (W ≃ₗ[k] W) where
  carrier := {g | ∃ σ ∈ P, ∀ i, ∀ w : W, ((g w : W) : V) ∈ I (σ i) ↔ (w : V) ∈ I i}
  one_mem' := ⟨1, P.one_mem, fun _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro g h ⟨σ, hσ, hg⟩ ⟨τ, hτ, hh⟩
    exact ⟨σ * τ, P.mul_mem hσ hτ, fun i w => (hg (τ i) (h w)).trans (hh i w)⟩
  inv_mem' := by
    rintro g ⟨σ, hσ, hg⟩
    refine ⟨σ⁻¹, P.inv_mem hσ, fun i w => ?_⟩
    have h := hg (σ⁻¹ i) (g⁻¹ w)
    have e1 : σ (σ⁻¹ i) = i := σ.apply_symm_apply i
    rw [e1, gl_apply_inv] at h
    exact h.symm

theorem mem_linWreath_iff {ι : Type*} {W : Submodule k V} {I : ι → Submodule k V}
    {P : Subgroup (Equiv.Perm ι)} {g : W ≃ₗ[k] W} :
    g ∈ linWreath W I P ↔
      ∃ σ ∈ P, ∀ i, ∀ w : W, ((g w : W) : V) ∈ I (σ i) ↔ (w : V) ∈ I i := Iff.rfl

@[expose] def restrictPlane {W U : Submodule k V} (hUW : U ≤ W) (g : W ≃ₗ[k] W)
    (h : ∀ w : W, ((g w : W) : V) ∈ U ↔ (w : V) ∈ U) : U ≃ₗ[k] U where
  toFun u := ⟨((g ⟨u, hUW u.2⟩ : W) : V), (h _).2 u.2⟩
  map_add' x y := Subtype.ext (by
    have e : (⟨((x + y : U) : V), hUW (x + y).2⟩ : W) =
        ⟨(x : V), hUW x.2⟩ + ⟨(y : V), hUW y.2⟩ := rfl
    show ((g ⟨((x + y : U) : V), hUW (x + y).2⟩ : W) : V) = _
    rw [e, map_add]
    rfl)
  map_smul' c x := Subtype.ext (by
    have e : (⟨((c • x : U) : V), hUW (c • x).2⟩ : W) = c • ⟨(x : V), hUW x.2⟩ := rfl
    show ((g ⟨((c • x : U) : V), hUW (c • x).2⟩ : W) : V) = _
    rw [e, map_smul]
    rfl)
  invFun u := ⟨((g.symm ⟨u, hUW u.2⟩ : W) : V),
    (h (g.symm ⟨u, hUW u.2⟩)).1 (by simp)⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

theorem restrictPlane_apply {W U : Submodule k V} (hUW : U ≤ W) (g : W ≃ₗ[k] W)
    (h : ∀ w : W, ((g w : W) : V) ∈ U ↔ (w : V) ∈ U) (u : U) :
    ((restrictPlane hUW g h u : U) : V) = ((g ⟨u, hUW u.2⟩ : W) : V) := rfl

structure S3WreathData (H T N : Subgroup (V ≃ₗ[k] V)) (r : ℕ)
    (L S : Fin r → Subgroup (V ≃ₗ[k] V)) (I : Fin r → Submodule k V)
    (P : Subgroup (Equiv.Perm (Fin r))) : Prop where
  L_le : ∀ i, L i ≤ N
  card_L : ∀ i, Nat.card ↥(L i) = 3
  I_eq : ∀ i, I i = commGL (L i) ⊤
  finrank_I : ∀ i, Module.finrank k ↥(I i) = 2
  L_comm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x
  L_indep : iSupIndep L
  N_eq : ⨆ i, L i = N
  S_le : ∀ i, S i ≤ H
  S_iso : ∀ i, Nonempty (↥(S i) ≃* Matrix.GeneralLinearGroup (Fin 2) k)
  S_comm : ∀ i j, i ≠ j → ∀ x ∈ S i, ∀ y ∈ S j, x * y = y * x
  S_indep : iSupIndep S
  B_normal : ((⨆ i, S i).subgroupOf H).Normal
  B_derived : ⁅(⨆ i, S i), (⨆ i, S i)⁆ = N
  H_eq : (⨆ i, S i) ⊔ T = H
  N_odd_gen : N = Subgroup.closure {h | h ∈ H ∧ Odd (orderOf h)}
  S_action : ∀ i, ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) (S i) (I i),
    Function.Bijective (resSub (MonoidHom.id (V ≃ₗ[k] V)) (S i) (I i) hW)
  S_fix_I : ∀ i j, i ≠ j → I j ≤ fixGL (S i)
  S_fix_C : ∀ i, fixGL N ≤ fixGL (S i)
  I_indep : iSupIndep I
  V_compl : IsCompl (⨆ i, I i) (fixGL N)
  S_subnormal : ∀ i, ((S i).subgroupOf H).IsSubnormal
  T_perm : ∀ t ∈ T, ∀ i, ∃ j, conjSub t (S i) = S j ∧ conjSub t (L i) = L j ∧
    (I i).map (t : V →ₗ[k] V) = I j
  T_trans : ∀ i j, ∃ t ∈ T, conjSub t (S i) = S j ∧ conjSub t (L i) = L j ∧
    (I i).map (t : V →ₗ[k] V) = I j
  W_eq : commGL N ⊤ = ⨆ i, I i
  faithful : ∀ h ∈ H, (∀ w ∈ commGL N ⊤, h w = w) → h = 1
  P_two : IsPGroup 2 ↥P
  P_trans : ∀ i j, ∃ σ ∈ P, σ i = j
  image_eq : ∃ hW : Offender.IsInvariant (MonoidHom.id (V ≃ₗ[k] V)) H (commGL N ⊤),
    (resSub (MonoidHom.id (V ≃ₗ[k] V)) H (commGL N ⊤) hW).range = linWreath (commGL N ⊤) I P
  r_pow : ∃ m : ℕ, r = 2 ^ m

structure S3Wreath (H T N : Subgroup (V ≃ₗ[k] V)) : Prop where
  card_k : Nat.card k = 2
  exists_data : ∃ (r : ℕ) (_ : 1 ≤ r) (L S : Fin r → Subgroup (V ≃ₗ[k] V))
    (I : Fin r → Submodule k V) (P : Subgroup (Equiv.Perm (Fin r))), S3WreathData H T N r L S I P

end CFSG.QuasithinUnique.Setup.Wreath

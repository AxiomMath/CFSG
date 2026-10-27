module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDRho

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

section Uniqueness

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem eq_zero_of_hfm_piI (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F))
    {w : Fin n → L} (hw : w ∈ Vf s b F f.1)
    (h : ∀ q ∈ Vf s b F (piI H f).1, hfm τ q w = 0) : w = 0 := by
  apply hfm_nondeg τ w
  intro z
  have hz : hfm τ w z = hfm τ w (∑ g ∈ Fset s b F, Pmat s b F g *ᵥ z) := by
    rw [sum_Pmat_mulVec H z]
  rw [hz, hfm_sum_right, Finset.sum_eq_single (piI H f).1]
  · rw [hfm_comm_tau H.hτ, h _ (Pmat_mem_Vf H (piI H f) z), map_zero]
  · intro g hg hne
    exact hfm_block_zero H f ⟨g, hg⟩ (fun h' => hne (congrArg Subtype.val h')) hw
      (Pmat_mem_Vf H ⟨g, hg⟩ z)
  · intro h'
    exact absurd (piI H f).2 h'

theorem resU_mul' {f : L[X]} [Fact (∀ x ∈ Vf s b F f, aeval s f *ᵥ x = 0)] (g h : (Vend L n)ˣ)
    (hg : g ∈ Glin τ s) (hh : h ∈ Glin τ s) (hgh : g * h ∈ Glin τ s) :
    resU (F := F) (b := b) (f := f) (g * h) hgh =
      resU (F := F) (b := b) (f := f) g hg * resU (F := F) (b := b) (f := f) h hh := by
  apply Units.ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  simp only [Units.val_mul, Module.End.mul_apply, coe_resU]

end Uniqueness

section Partner

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}
  [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]

theorem natUnit_one (H : PrimaryHyp τ s m F a b) (src tgt : ↥(Fset s b F))
    (hpair : adjM τ (Pmat s b F tgt.1) = Pmat s b F src.1) :
    natUnit H src tgt hpair 1 = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  show (natLU H src tgt 1 y : Fin n → L) = (y : Fin n → L)
  rw [natLU_one]
  rfl

theorem natUnit_eq_of_partner (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F))
    (g : (Vend L n)ˣ) (hg : g ∈ Glin τ s)
    (u : (Vf s b F (piI H f).1 →ₗ[AdjoinRoot (piI H f).1] Vf s b F (piI H f).1)ˣ)
    (hu : ∀ p : Vf s b F (piI H f).1,
      ((u.val p : Vf s b F (piI H f).1) : Fin n → L) = (g.val : Vend L n) (p : Fin n → L))
    (y : Vf s b F f.1) :
    ((natUnit H (piI H f) f (adjM_piI H f) u).val y : Fin n → L) =
      (g.val : Vend L n) (y : Fin n → L) := by
  have hgy : (g.val : Vend L n) (y : Fin n → L) ∈ Vf s b F f.1 := by
    have hc := Pmat_comm_of_comm (Glin_comm hg) (b f.1 * gcF F f.1) (y : Fin n → L)
    have hPy : aeval s (b f.1 * gcF F f.1) *ᵥ (y : Fin n → L) = (y : Fin n → L) :=
      mem_Vf.mp y.2
    rw [hPy] at hc
    exact mem_Vf.mpr hc.symm
  have hzero : (g.val : Vend L n) (y : Fin n → L) -
      ((natUnit H (piI H f) f (adjM_piI H f) u).val y : Fin n → L) = 0 := by
    apply eq_zero_of_hfm_piI H f (Submodule.sub_mem _ hgy ((natUnit H (piI H f) f
      (adjM_piI H f) u).val y).2)
    intro q hq
    obtain ⟨p, hpq⟩ : ∃ p : Vf s b F (piI H f).1, u.val p = ⟨q, hq⟩ :=
      ⟨u⁻¹.val ⟨q, hq⟩, by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Module.End.one_apply]⟩
    have key : hfm τ q ((g.val : Vend L n) (y : Fin n → L) -
        ((natUnit H (piI H f) f (adjM_piI H f) u).val y : Fin n → L)) =
          hfm τ ((u.val p : Vf s b F (piI H f).1) : Fin n → L) ((g.val : Vend L n) (y : Fin n → L) -
            ((natUnit H (piI H f) f (adjM_piI H f) u).val y : Fin n → L)) := by
      rw [hpq]
    rw [key, hfm_sub_right', sub_eq_zero]
    have h1 : hfm τ ((u.val p : Vf s b F (piI H f).1) : Fin n → L)
        ((g.val : Vend L n) (y : Fin n → L)) = hfm τ (p : Fin n → L) (y : Fin n → L) := by
      rw [hu p]
      exact hg.2 _ _
    exact h1.trans (hfm_natUnit H H.hτ (piI H f) f (adjM_piI H f) u p y)
  exact (sub_eq_zero.mp hzero).symm

theorem natUnit_resU_apply (H : PrimaryHyp τ s m F a b) (g : (Vend L n)ˣ) (hg : g ∈ Glin τ s)
    (f : ↥(Fset s b F)) (y : Vf s b F f.1) :
    ((natUnit H (piI H f) f (adjM_piI H f) (resU (f := (piI H f).1) g hg)).val y :
        Fin n → L) = (g.val : Vend L n) (y : Fin n → L) :=
  natUnit_eq_of_partner H f g hg _ (fun p => coe_resU g hg p) y

end Partner

section Equiv

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}
  [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]

theorem resU_mem_Bl (H : PrimaryHyp τ s m F a b) (g : (Vend L n)ˣ) (hg : g ∈ Glin τ s)
    (f : ↥(Fset s b F)) (hf : IsAct H f) : resU (f := f.1) g hg ∈ Bl H f := by
  by_cases hsd : piI H f = f
  · rw [Bl_of_selfDual H hsd]
    exact fun x y => by
      rw [coe_resU, coe_resU]
      exact hg.2 _ _
  · rw [Bl_of_isRep H (hf.resolve_left hsd)]
    exact Subgroup.mem_top _

@[expose] noncomputable def theta (H : PrimaryHyp τ s m F a b) (g : ↥(Glin τ s)) :
    (f : Activ H) → ↥(Bl H f.1) :=
  fun f => ⟨resU (f := f.1.1) g.1 g.2, resU_mem_Bl H g.1 g.2 f.1 f.2⟩

theorem theta_mul (H : PrimaryHyp τ s m F a b) (g h : ↥(Glin τ s)) :
    theta H (g * h) = theta H g * theta H h := by
  funext f
  apply Subtype.ext
  exact resU_mul' (F := F) (b := b) (f := f.1.1) g.1 h.1 g.2 h.2 (g * h).2

theorem rhoG_theta (H : PrimaryHyp τ s m F a b) (g : ↥(Glin τ s)) :
    rhoG H (theta H g) = g := by
  apply Subtype.ext
  apply Units.ext
  have hcomm : ∀ (f : ↥(Fset s b F)) (x : Fin n → L),
      Pmat s b F f.1 *ᵥ (g.1.val x) = g.1.val (Pmat s b F f.1 *ᵥ x) :=
    fun f x => (Pmat_comm_of_comm (Glin_comm g.2) (b f.1 * gcF F f.1) x).symm
  show rhoU H (fullW H (theta H g)) = g.1.val
  rw [rho_restrict H g.1.val hcomm]
  unfold rhoU
  congr 1
  funext f
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  by_cases hA : IsAct H f
  · rw [fullW_act H (theta H g) hA]
    exact coe_resU g.1 g.2 y
  · rw [fullW_nact H (theta H g) hA]
    exact natUnit_resU_apply H g.1 g.2 f y

theorem theta_rhoG (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1)) :
    theta H (rhoG H w) = w := by
  funext f
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro y
  apply Subtype.ext
  show (((resU (F := F) (b := b) (f := f.1.1) (rhoG H w).1 (rhoG H w).2).val y :
      Vf s b F f.1.1) : Fin n → L) = (((w f).1.val y : Vf s b F f.1.1) : Fin n → L)
  rw [coe_resU]
  show rhoU H (fullW H w) (y : Fin n → L) = (((w f).1.val y : Vf s b F f.1.1) : Fin n → L)
  rw [rhoU_apply_block H (fullW H w) f.1 y, fullW_act H w f.2]

@[expose] noncomputable def glinEquivBlocks (H : PrimaryHyp τ s m F a b) :
    ↥(Glin τ s) ≃* ((f : Activ H) → ↥(Bl H f.1)) where
  toFun := theta H
  invFun := rhoG H
  left_inv := rhoG_theta H
  right_inv := theta_rhoG H
  map_mul' := theta_mul H

end Equiv

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end

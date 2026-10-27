module

public import CFSG.LieType.SemisimpleCentralizers.HeldUCDAssemble
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDSelfDual

public section

open CFSG.LocalAnalysis.ComponentInitial

namespace CFSG.LieType.SemisimpleCentralizers.HeldUCD

open Matrix Polynomial

open scoped _root_.Classical

variable {L : Type} [Field L] {n : ℕ}

section Form

variable {τ : L ≃+* L}

theorem hfm_comm_tau (hτ : ∀ x, τ (τ x) = x) (x y : Fin n → L) :
    hfm τ x y = τ (hfm τ y x) :=
  (hfm_symm τ hτ y x).symm

theorem hfm_sum_left' {ι' : Type*} (t : Finset ι') (v : ι' → Fin n → L) (y : Fin n → L) :
    hfm τ (∑ i ∈ t, v i) y = ∑ i ∈ t, hfm τ (v i) y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [hfm]
  | insert j t hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, hfm_add_left, ih]

theorem hfm_sum_sum {ι' : Type*} (t : Finset ι') (A B : ι' → Fin n → L) :
    hfm τ (∑ i ∈ t, A i) (∑ j ∈ t, B j) = ∑ i ∈ t, ∑ j ∈ t, hfm τ (A i) (B j) := by
  rw [hfm_sum_left']
  exact Finset.sum_congr rfl fun i _ => by rw [hfm_sum_right]

end Form

section Activity

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem ordI_eq_iff (f g : ↥(Fset s b F)) : ordI f = ordI g ↔ f = g := by
  unfold ordI
  exact ⟨fun h => (Fintype.equivFin _).injective (Fin.ext h), fun h => by rw [h]⟩

@[expose] noncomputable def IsRep (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) : Prop :=
  ordI f < ordI (piI H f)

@[expose] noncomputable def IsAct (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) : Prop :=
  piI H f = f ∨ IsRep H f

abbrev Activ (H : PrimaryHyp τ s m F a b) : Type := {f : ↥(Fset s b F) // IsAct H f}

theorem piI_ne_of_isRep (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (hr : IsRep H f) :
    piI H f ≠ f := by
  intro h
  unfold IsRep at hr
  rw [h] at hr
  exact lt_irrefl _ hr

theorem isRep_piI_iff (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (hne : piI H f ≠ f) :
    IsRep H (piI H f) ↔ ¬ IsRep H f := by
  have h1 : ordI f ≠ ordI (piI H f) := fun h => hne ((ordI_eq_iff _ _).mp h).symm
  unfold IsRep
  rw [piI_piI]
  constructor <;> intro h <;> omega

theorem isAct_piI (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (hf : ¬ IsAct H f) :
    IsAct H (piI H f) :=
  Or.inr ((isRep_piI_iff H fun h => hf (Or.inl h)).mpr fun h => hf (Or.inr h))

theorem not_isAct_piI (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (hf : IsRep H f) :
    ¬ IsAct H (piI H f) := by
  rintro (h | h)
  · rw [piI_piI] at h
    exact piI_ne_of_isRep H hf h.symm
  · exact (isRep_piI_iff H (piI_ne_of_isRep H hf)).mp h hf

theorem hpair_of (H : PrimaryHyp τ s m F a b) {g f : ↥(Fset s b F)} (hf : piI H g = f) :
    adjM τ (Pmat s b F f.1) = Pmat s b F g.1 := by
  subst hf
  rw [adjM_piI H (piI H g), piI_piI]

end Activity

section Vanish

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}

theorem hfm_block_zero (H : PrimaryHyp τ s m F a b) (f g : ↥(Fset s b F)) (hg : g ≠ piI H f)
    {p q : Fin n → L} (hp : p ∈ Vf s b F f.1) (hq : q ∈ Vf s b F g.1) : hfm τ p q = 0 := by
  have hne : (piI H f).1 ≠ g.1 := fun h => hg (Subtype.ext h.symm)
  have hp' : Pmat s b F f.1 *ᵥ p = p := mem_Vf.mp hp
  have hq' : Pmat s b F g.1 *ᵥ q = q := mem_Vf.mp hq
  calc hfm τ p q = hfm τ (Pmat s b F f.1 *ᵥ p) (Pmat s b F g.1 *ᵥ q) := by rw [hp', hq']
    _ = hfm τ p (adjM τ (Pmat s b F f.1) *ᵥ (Pmat s b F g.1 *ᵥ q)) := by rw [hfm_mulVec]
    _ = hfm τ p (Pmat s b F (piI H f).1 *ᵥ (Pmat s b F g.1 *ᵥ q)) := by rw [adjM_piI H f]
    _ = 0 := by
      rw [Matrix.mulVec_mulVec, H.Pmat_orth (mem_Fset.mp (piI H f).2).1 (mem_Fset.mp g.2).1 hne,
        Matrix.zero_mulVec]
      simp [hfm]

theorem Pmat_mem_Vf (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) (x : Fin n → L) :
    Pmat s b F f.1 *ᵥ x ∈ Vf s b F f.1 :=
  mem_Vf.mpr (Pmat_idem_index H f x)

theorem sum_Pmat_index (H : PrimaryHyp τ s m F a b) (x : Fin n → L) :
    x = ∑ f : ↥(Fset s b F), Pmat s b F f.1 *ᵥ x := by
  rw [Finset.sum_coe_sort (Fset s b F) (fun g => Pmat s b F g *ᵥ x), sum_Pmat_mulVec H x]

theorem coe_prjB (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) (x : Fin n → L) :
    ((prjB H f x : Vf s b F f.1) : Fin n → L) = Pmat s b F f.1 *ᵥ x :=
  rfl

end Vanish

section Blocks

variable {τ : L ≃+* L} {m : ℕ} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]}
  {a b : L[X] → L[X]}
  [hK : ∀ f : ↥(Fset s b F), Fact (∀ x ∈ Vf s b F f.1, aeval s f.1 *ᵥ x = 0)]

@[expose] noncomputable def Bl (H : PrimaryHyp τ s m F a b) (f : ↥(Fset s b F)) :
    Subgroup (LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :=
  by
    classical
    exact if piI H f = f then unitaryBlock τ s b F f.1 else if IsRep H f then ⊤ else ⊥

theorem Bl_of_selfDual (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (h : piI H f = f) :
    Bl H f = unitaryBlock τ s b F f.1 :=
  if_pos h

theorem Bl_of_isRep (H : PrimaryHyp τ s m F a b) {f : ↥(Fset s b F)} (hr : IsRep H f) :
    Bl H f = ⊤ := by
  rw [Bl, if_neg (piI_ne_of_isRep H hr), if_pos hr]

@[expose] noncomputable def fullW (H : PrimaryHyp τ s m F a b)
    (w : (f : Activ H) → ↥(Bl H f.1)) (f : ↥(Fset s b F)) :
    LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1) :=
  by
    classical
    exact if h : IsAct H f then (w ⟨f, h⟩).1
      else natUnit H (piI H f) f (adjM_piI H f) (w ⟨piI H f, isAct_piI H h⟩).1

theorem fullW_act (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    {f : ↥(Fset s b F)} (h : IsAct H f) : fullW H w f = (w ⟨f, h⟩).1 := by
  unfold fullW
  rw [dif_pos h]

theorem fullW_nact (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    {f : ↥(Fset s b F)} (h : ¬ IsAct H f) :
    fullW H w f = natUnit H (piI H f) f (adjM_piI H f) (w ⟨piI H f, isAct_piI H h⟩).1 := by
  unfold fullW
  rw [dif_neg h]

theorem natUnit_index_eq (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    {z g t : ↥(Fset s b F)} (hz : z = g) (hzA : IsAct H z) (hgA : IsAct H g)
    (h1 : adjM τ (Pmat s b F t.1) = Pmat s b F z.1)
    (h2 : adjM τ (Pmat s b F t.1) = Pmat s b F g.1) :
    natUnit H z t h1 (w ⟨z, hzA⟩).1 = natUnit H g t h2 (w ⟨g, hgA⟩).1 := by
  subst hz
  rfl

theorem fullW_partner (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    {g f : ↥(Fset s b F)} (hg : IsRep H g) (hf : piI H g = f) :
    fullW H w f = natUnit H g f (hpair_of H hf) (fullW H w g) := by
  subst hf
  have hgA : IsAct H g := Or.inr hg
  rw [fullW_nact H w (not_isAct_piI H hg), fullW_act H w hgA]
  exact natUnit_index_eq H w (piI_piI H g) (isAct_piI H (not_isAct_piI H hg)) hgA _ _

theorem fullW_hS (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1))
    (f : ↥(Fset s b F)) (hf : piI H f = f) (x y : Vf s b F f.1) :
    hfm τ ((fullW H w f).1 x : Fin n → L) ((fullW H w f).1 y : Fin n → L) =
      hfm τ (x : Fin n → L) (y : Fin n → L) := by
  have hA : IsAct H f := Or.inl hf
  have key : ∀ g ∈ Bl H f, ∀ (x y : Vf s b F f.1),
      hfm τ ((g.1 x : Vf s b F f.1) : Fin n → L) ((g.1 y : Vf s b F f.1) : Fin n → L) =
        hfm τ (x : Fin n → L) (y : Fin n → L) := by
    intro g hg
    rw [Bl_of_selfDual H hf] at hg
    exact fun x y => hg x y
  rw [fullW_act H w hA]
  exact key _ (w ⟨f, hA⟩).2 x y

@[expose] noncomputable def rhoU (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :
    (Fin n → L) →ₗ[L] (Fin n → L) :=
  rhoL H (fun f => (W f).1.restrictScalars L)

theorem rhoU_apply_sum (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))
    (z : Fin n → L) :
    rhoU H W z = ∑ f : ↥(Fset s b F), ((W f).1 (prjB H f z) : Fin n → L) := by
  unfold rhoU rhoL
  rw [LinearMap.sum_apply]
  rfl

theorem rhoU_apply_block (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))
    (f : ↥(Fset s b F)) (y : Vf s b F f.1) :
    rhoU H W (y : Fin n → L) = ((W f).1 y : Fin n → L) :=
  rhoL_apply_block H (fun f => (W f).1.restrictScalars L) f y

theorem rhoU_comm_s (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))
    (x : Fin n → L) : rhoU H W (s *ᵥ x) = s *ᵥ rhoU H W x := by
  rw [rhoU_apply_sum, rhoU_apply_sum, Matrix.mulVec_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hpr : prjB H f (s *ᵥ x) = AdjoinRoot.root f.1 • prjB H f x := by
    apply Subtype.ext
    rw [coe_root_smul, coe_prjB, coe_prjB, Pmat_mulVec_s]
  rw [hpr, map_smul, coe_root_smul]

theorem rhoU_mul (H : PrimaryHyp τ s m F a b)
    (W W' : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :
    rhoU H (fun f => W f * W' f) = rhoU H W ∘ₗ rhoU H W' := by
  unfold rhoU
  rw [rhoL_comp]
  congr 1

theorem rhoU_one (H : PrimaryHyp τ s m F a b) :
    rhoU H (fun _ => 1) = 1 := by
  unfold rhoU
  exact rhoL_one H

theorem rhoU_mul_inv (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :
    rhoU H W * rhoU H (fun f => (W f)⁻¹) = 1 := by
  have h1 : rhoU H W * rhoU H (fun f => (W f)⁻¹) = rhoU H (fun f => W f * (W f)⁻¹) := by
    rw [Module.End.mul_eq_comp, rhoU_mul]
  rw [h1]
  have h : (fun f => W f * (W f)⁻¹) = fun _ => 1 := funext fun f => mul_inv_cancel (W f)
  rw [h]
  exact rhoU_one H

theorem rhoU_inv_mul (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :
    rhoU H (fun f => (W f)⁻¹) * rhoU H W = 1 := by
  have h1 : rhoU H (fun f => (W f)⁻¹) * rhoU H W = rhoU H (fun f => (W f)⁻¹ * W f) := by
    rw [Module.End.mul_eq_comp, rhoU_mul]
  rw [h1]
  have h : (fun f => (W f)⁻¹ * W f) = fun _ => 1 := funext fun f => inv_mul_cancel (W f)
  rw [h]
  exact rhoU_one H

@[expose] noncomputable def rhoUnit (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1)) :
    ((Fin n → L) →ₗ[L] (Fin n → L))ˣ :=
  Units.mk (rhoU H W) (rhoU H (fun f => (W f)⁻¹)) (rhoU_mul_inv H W) (rhoU_inv_mul H W)

theorem natUnit_hfm_bwd (H : PrimaryHyp τ s m F a b) (hτ : ∀ x, τ (τ x) = x)
    (src tgt : ↥(Fset s b F)) (hpair : adjM τ (Pmat s b F tgt.1) = Pmat s b F src.1)
    (u : (Vf s b F src.1 →ₗ[AdjoinRoot src.1] Vf s b F src.1)ˣ)
    (p : Vf s b F tgt.1) (q : Vf s b F src.1) :
    hfm τ ((natUnit H src tgt hpair u).val p : Fin n → L) ((u.val q : Vf s b F src.1) : Fin n → L) =
      hfm τ (p : Fin n → L) (q : Fin n → L) := by
  calc hfm τ ((natUnit H src tgt hpair u).val p : Fin n → L) ((u.val q : Vf s b F src.1) : Fin n → L)
      = τ (hfm τ ((u.val q : Vf s b F src.1) : Fin n → L)
          ((natUnit H src tgt hpair u).val p : Fin n → L)) := hfm_comm_tau hτ _ _
    _ = τ (hfm τ (q : Fin n → L) (p : Fin n → L)) := by
        rw [← hfm_natUnit H hτ src tgt hpair u q p]
    _ = hfm τ (p : Fin n → L) (q : Fin n → L) := (hfm_comm_tau hτ _ _).symm

theorem rhoU_hfm (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))
    (hS : ∀ (f : ↥(Fset s b F)), piI H f = f → ∀ (x y : Vf s b F f.1),
      hfm τ ((W f).1 x : Fin n → L) ((W f).1 y : Fin n → L) = hfm τ (x : Fin n → L) (y : Fin n → L))
    (hP : ∀ (g f : ↥(Fset s b F)) (hf : piI H g = f), IsRep H g →
      W f = natUnit H g f (hpair_of H hf) (W g))
    (x y : Fin n → L) : hfm τ (rhoU H W x) (rhoU H W y) = hfm τ x y := by
  have hcore : ∀ f : ↥(Fset s b F),
      hfm τ ((W f).1 (prjB H f x) : Fin n → L) ((W (piI H f)).1 (prjB H (piI H f) y) : Fin n → L) =
        hfm τ (prjB H f x : Fin n → L) (prjB H (piI H f) y : Fin n → L) := by
    intro f
    by_cases hsd : piI H f = f
    · rw [hsd]
      exact hS f hsd (prjB H f x) (prjB H f y)
    · by_cases hr : IsRep H f
      · rw [hP f (piI H f) rfl hr]
        exact (hfm_natUnit H H.hτ f (piI H f) (hpair_of H rfl) (W f) (prjB H f x)
          (prjB H (piI H f) y)).symm
      · have hrep : IsRep H (piI H f) := (isRep_piI_iff H hsd).mpr hr
        rw [hP (piI H f) f (piI_piI H f) hrep]
        exact natUnit_hfm_bwd H H.hτ (piI H f) f (hpair_of H (piI_piI H f)) (W (piI H f))
          (prjB H f x) (prjB H (piI H f) y)
  have hL : ∀ f : ↥(Fset s b F),
      ∑ g : ↥(Fset s b F), hfm τ ((W f).1 (prjB H f x) : Fin n → L)
          ((W g).1 (prjB H g y) : Fin n → L) =
        hfm τ ((W f).1 (prjB H f x) : Fin n → L) ((W (piI H f)).1 (prjB H (piI H f) y) : Fin n → L) := by
    intro f
    apply Finset.sum_eq_single (piI H f)
    · intro g _ hg
      exact hfm_block_zero H f g hg ((W f).1 (prjB H f x)).2 ((W g).1 (prjB H g y)).2
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hR : ∀ f : ↥(Fset s b F),
      ∑ g : ↥(Fset s b F), hfm τ (prjB H f x : Fin n → L) (prjB H g y : Fin n → L) =
        hfm τ (prjB H f x : Fin n → L) (prjB H (piI H f) y : Fin n → L) := by
    intro f
    apply Finset.sum_eq_single (piI H f)
    · intro g _ hg
      exact hfm_block_zero H f g hg (prjB H f x).2 (prjB H g y).2
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hRHS : hfm τ x y = ∑ f : ↥(Fset s b F), ∑ g : ↥(Fset s b F),
      hfm τ (prjB H f x : Fin n → L) (prjB H g y : Fin n → L) := by
    have hxs : x = ∑ f : ↥(Fset s b F), (prjB H f x : Fin n → L) := sum_Pmat_index H x
    have hys : y = ∑ g : ↥(Fset s b F), (prjB H g y : Fin n → L) := sum_Pmat_index H y
    calc hfm τ x y = hfm τ (∑ f : ↥(Fset s b F), (prjB H f x : Fin n → L))
          (∑ g : ↥(Fset s b F), (prjB H g y : Fin n → L)) := by rw [← hxs, ← hys]
      _ = _ := hfm_sum_sum _ _ _
  rw [rhoU_apply_sum H W x, rhoU_apply_sum H W y, hfm_sum_sum]
  rw [Finset.sum_congr rfl fun f _ => hL f, Finset.sum_congr rfl fun f _ => hcore f, hRHS]
  exact Finset.sum_congr rfl fun f _ => (hR f).symm

theorem rhoUnit_mem_Glin (H : PrimaryHyp τ s m F a b)
    (W : (f : ↥(Fset s b F)) → LinearMap.GeneralLinearGroup (AdjoinRoot f.1) (Vf s b F f.1))
    (hS : ∀ (f : ↥(Fset s b F)), piI H f = f → ∀ (x y : Vf s b F f.1),
      hfm τ ((W f).1 x : Fin n → L) ((W f).1 y : Fin n → L) = hfm τ (x : Fin n → L) (y : Fin n → L))
    (hP : ∀ (g f : ↥(Fset s b F)) (hf : piI H g = f), IsRep H g →
      W f = natUnit H g f (hpair_of H hf) (W g)) :
    rhoUnit H W ∈ Glin τ s :=
  ⟨rhoU_comm_s H W, rhoU_hfm H W hS hP⟩

theorem fullW_hS' (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1)) :
    ∀ (f : ↥(Fset s b F)), piI H f = f → ∀ (x y : Vf s b F f.1),
      hfm τ ((fullW H w f).1 x : Fin n → L) ((fullW H w f).1 y : Fin n → L) =
        hfm τ (x : Fin n → L) (y : Fin n → L) :=
  fun f hf x y => fullW_hS H w f hf x y

theorem fullW_hP' (H : PrimaryHyp τ s m F a b) (w : (f : Activ H) → ↥(Bl H f.1)) :
    ∀ (g f : ↥(Fset s b F)) (hf : piI H g = f), IsRep H g →
      fullW H w f = natUnit H g f (hpair_of H hf) (fullW H w g) :=
  fun _ _ hf hg => fullW_partner H w hg hf

@[expose] noncomputable def rhoG (H : PrimaryHyp τ s m F a b)
    (w : (f : Activ H) → ↥(Bl H f.1)) : ↥(Glin τ s) :=
  ⟨rhoUnit H (fullW H w), rhoUnit_mem_Glin H (fullW H w) (fullW_hS' H w) (fullW_hP' H w)⟩

end Blocks

end CFSG.LieType.SemisimpleCentralizers.HeldUCD

end

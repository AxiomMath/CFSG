module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidEigen
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidOmegaFour

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

section Frame

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm K (ι → K)}

omit [DecidableEq ι] in
theorem exists_hyperbolic_dual (hnd : Q.polarBilin.Nondegenerate) {S C : Submodule K (ι → K)}
    (hSC : S ⊔ C = ⊤) (hperp : ∀ s ∈ S, ∀ c ∈ C, Q.polarBilin s c = 0)
    {x : Fin 2 → ι → K} (hxS : ∀ i, x i ∈ S) (hli : LinearIndependent K x)
    (hQx : ∀ i, Q (x i) = 0) (hBx : ∀ i j, Q.polarBilin (x i) (x j) = 0) :
    ∃ y : Fin 2 → ι → K, (∀ j, y j ∈ S) ∧
      (∀ i j, Q.polarBilin (x i) (y j) = if i = j then 1 else 0) ∧
      (∀ i j, Q.polarBilin (y i) (y j) = 0) ∧ ∀ j, Q (y j) = 0 := by
  obtain ⟨w, hw⟩ := exists_polar_dual Q hnd x hli
  have hdec : ∀ j, ∃ s ∈ S, ∃ c ∈ C, s + c = w j := fun j =>
    Submodule.mem_sup.mp (hSC ▸ Submodule.mem_top)
  choose s hs c hc hsc using hdec
  have hdual : ∀ i j, Q.polarBilin (x i) (s j) = if i = j then 1 else 0 := fun i j => by
    rw [← hw i j, ← hsc j, map_add, hperp _ (hxS i) _ (hc j), add_zero]
  obtain ⟨y, hy1, hy2, hy3, hy4⟩ := exists_singular_dual Q x s hQx hBx hdual
  refine ⟨y, fun j => ?_, hy1, hy2, hy3⟩
  obtain ⟨d, hd⟩ := hy4 j
  rw [hd]
  exact add_mem (hs j) (Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (hxS m))

omit [CharP K 2] [Fintype ι] [DecidableEq ι] in
theorem linearIndependent_of_hyperbolic {v : Fin 2 ⊕ Fin 2 → ι → K}
    (hxy : ∀ i j, Q.polarBilin (v (.inl i)) (v (.inr j)) = if i = j then 1 else 0)
    (hxx : ∀ i j, Q.polarBilin (v (.inl i)) (v (.inl j)) = 0)
    (hyy : ∀ i j, Q.polarBilin (v (.inr i)) (v (.inr j)) = 0) : LinearIndependent K v := by
  have hsymm : ∀ a b, Q.polarBilin a b = Q.polarBilin b a := polarBilin_comm Q
  rw [Fintype.linearIndependent_iff]
  intro g hg c
  have hpair : ∀ z, Q.polarBilin (∑ d, g d • v d) z = 0 := fun z => by
    rw [hg, map_zero, LinearMap.zero_apply]
  rcases c with k | k
  · have h1 := hpair (v (.inr k))
    rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hxy, hyy, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const_zero,
      add_zero] at h1
    exact h1
  · have h1 := hpair (v (.inl k))
    rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type] at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hxx] at h1
    have h2 : ∀ d, Q.polarBilin (v (.inr d)) (v (.inl k)) = if k = d then 1 else 0 := fun d => by
      rw [hsymm, hxy]
    simp only [h2, mul_zero, Finset.sum_const_zero, zero_add, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte] at h1
    exact h1

theorem exists_isometryGL_family (hnd : Q.polarBilin.Nondegenerate) {k : ℕ}
    (u u' : Fin k → ι → K) (hu : LinearIndependent K u) (hu' : LinearIndependent K u')
    (hQu : ∀ i, Q (u' i) = Q (u i))
    (hpol : ∀ i j, Q.polarBilin (u' i) (u' j) = Q.polarBilin (u i) (u j)) :
    ∃ G : GL ι K, (∀ v, Q ((G : Matrix ι ι K) *ᵥ v) = Q v) ∧
      ∀ i, (G : Matrix ι ι K) *ᵥ u i = u' i := by
  obtain ⟨g, hg, hgu⟩ := CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq
    hnd u u' hu hu' hQu fun i j => by
      rw [← polarBilin_apply_apply, ← polarBilin_apply_apply]
      exact hpol i j
  set G := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm g
  have hGv : ∀ v, (G : Matrix ι ι K) *ᵥ v = g v := fun v => by
    rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, MulEquiv.apply_symm_apply]
  refine ⟨G, fun v => ?_, fun i => ?_⟩
  · rw [hGv]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg v
  · rw [hGv]
    exact hgu i

end Frame

section Fix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def fixVec (H : Subgroup (GL ι K)) : Submodule K (ι → K) where
  carrier := {w | ∀ Y ∈ H, (Y : Matrix ι ι K) *ᵥ w = w}
  add_mem' {a b} ha hb Y hY := by rw [mulVec_add, ha Y hY, hb Y hY]
  zero_mem' Y _ := mulVec_zero _
  smul_mem' c a ha Y hY := by rw [mulVec_smul, ha Y hY]

theorem mem_fixVec {H : Subgroup (GL ι K)} {w : ι → K} :
    w ∈ fixVec H ↔ ∀ Y ∈ H, (Y : Matrix ι ι K) *ᵥ w = w :=
  Iff.rfl

theorem fixVec_anti {H H' : Subgroup (GL ι K)} (h : H ≤ H') : fixVec H' ≤ fixVec H :=
  fun _ hw Y hY => hw Y (h hY)

theorem mem_fixVec_zpowers {h : GL ι K} {w : ι → K} (hw : (h : Matrix ι ι K) *ᵥ w = w) :
    w ∈ fixVec (Subgroup.zpowers h) := by
  have hinv : ((h⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w = w := by
    conv_lhs => rw [← hw]
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hn : ∀ n : ℕ, ((h ^ n : GL ι K) : Matrix ι ι K) *ᵥ w = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Units.val_mul, ← mulVec_mulVec, hw, ih]
  have hn' : ∀ n : ℕ, (((h⁻¹) ^ n : GL ι K) : Matrix ι ι K) *ᵥ w = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Units.val_mul, ← mulVec_mulVec, hinv, ih]
  intro Y hY
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hY
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact hn m
  · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact hn' m

end Fix

section Semisimple

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [CharP K 2] in
theorem eq_zero_of_fixed_of_sub {h : Matrix ι ι K} (hord : h ^ (Fintype.card K - 1) = 1)
    {y : ι → K} (hx : h *ᵥ (h *ᵥ y - y) = h *ᵥ y - y) : h *ᵥ y - y = 0 := by
  set x := h *ᵥ y - y
  have hy : h *ᵥ y = y + x := by simp [x]
  have hk : ∀ k : ℕ, (h ^ k) *ᵥ y = y + (k : K) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_add, mulVec_smul, hx, hy]
      push_cast
      rw [add_smul, one_smul]
      abel
  have h1 := hk (Fintype.card K - 1)
  rw [hord, one_mulVec, Nat.cast_sub Fintype.card_pos, FiniteField.cast_card_eq_zero,
    Nat.cast_one, zero_sub, neg_one_smul] at h1
  have h2 : -x = 0 := by
    have := congrArg (fun z => z - y) h1
    simpa using this.symm
  exact neg_eq_zero.mp h2

end Semisimple

section Module

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {ι₃ ι₂ : Type}
  [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}

variable (oe₂) in
@[expose] noncomputable def oY₂ : Subgroup (GL ι₂ K) :=
  (oRhoTwoGL oe₂).range ⊔ (oRhoOneGL oe₂).range

variable (oe₂) in
@[expose] noncomputable def oInnerGL : GL (Fin 2 ⊕ Fin 2) K →* GL ι₂ K :=
  (oblkGL oe₂).comp (MonoidHom.inr _ _)

omit [Fintype K] [DecidableEq K] [CharP K 2] in
theorem coe_oInnerGL (X : GL (Fin 2 ⊕ Fin 2) K) :
    ((oInnerGL oe₂ X : GL ι₂ K) : Matrix ι₂ ι₂ K) = oblk oe₂ 1 (X : Matrix _ _ K) :=
  rfl

omit [Fintype K] [DecidableEq K] [CharP K 2] in
theorem oInnerGL_injective : Function.Injective (oInnerGL (K := K) oe₂) := by
  intro X X' h
  have h1 := congrArg (fun g : GL ι₂ K => (g : Matrix ι₂ ι₂ K)) h
  simp only [coe_oInnerGL] at h1
  exact Units.ext (oblk_injective h1).2

omit [Fintype K] [DecidableEq K] [CharP K 2] in
theorem eq_oblk_of_fix_preserve {M : Matrix ι₂ ι₂ K}
    (h3 : ∀ w : ι₃ → K, M *ᵥ oVec oe₂ w 0 = oVec oe₂ w 0)
    (h1 : ∀ (u : Fin 2 ⊕ Fin 2 → K) (a : ι₃), (M *ᵥ oVec oe₂ 0 u) (oe₂ (.inl a)) = 0) :
    M = oblk oe₂ 1 (M.submatrix (fun b => oe₂ (.inr b)) (fun b => oe₂ (.inr b))) := by
  refine Matrix.ext_iff_mulVec.mpr fun v => ?_
  have hv : v = oVec oe₂ (fun a => v (oe₂ (.inl a))) 0 + oVec oe₂ 0 (fun b => v (oe₂ (.inr b))) :=
    oVec_ext oe₂ (fun a => by simp [oVec_apply_inl]) (fun b => by simp [oVec_apply_inr])
  refine oVec_ext oe₂ (fun a => ?_) (fun b => ?_)
  · rw [oblk_mulVec_inl, one_mulVec]
    conv_lhs => rw [hv]
    rw [mulVec_add, h3, Pi.add_apply, oVec_apply_inl, h1, add_zero]
  · rw [oblk_mulVec_inr]
    conv_lhs => rw [hv]
    rw [mulVec_add, h3, Pi.add_apply, oVec_apply_inr, Pi.zero_apply, zero_add]
    simp only [mulVec, dotProduct, submatrix_apply]
    rw [← Equiv.sum_comp oe₂, Fintype.sum_sum_type]
    simp [oVec_apply_inl, oVec_apply_inr]

end Module

section Main

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {ι₃ ι₂ : Type}
  [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}

omit [Fintype K] [DecidableEq K] [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] in
theorem polarBilin_self_eq_zero (v : ι₂ → K) : Q₂.polarBilin v v = 0 := by
  rw [polarBilin_apply_apply, QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

variable (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
  (hnd : Q₂.polarBilin.Nondegenerate)
include hQ₂ hnd

omit [Fintype K] [DecidableEq K] [Fintype ι₃] [DecidableEq ι₃] in
theorem exists_isometry_frame {S C : Submodule K (ι₂ → K)} (hSCtop : S ⊔ C = ⊤)
    (hperp : ∀ s ∈ S, ∀ c ∈ C, Q₂.polarBilin s c = 0) (hS4 : Module.finrank K S = 4)
    {x : Fin 2 → ι₂ → K} (hxS : ∀ i, x i ∈ S) (hli : LinearIndependent K x)
    (hQx : ∀ i, Q₂ (x i) = 0) (hBx : ∀ i j, Q₂.polarBilin (x i) (x j) = 0) :
    ∃ G : GL ι₂ K, (∀ w, Q₂ ((G : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) ∧
      (∀ u, (G : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u ∈ S) ∧
      (∀ w, (G : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ w 0 ∈ C) ∧
      ∀ s ∈ S, ∃ u, s = (G : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u := by
  obtain ⟨y, hyS, hxy, hyy, hQy⟩ := exists_hyperbolic_dual hnd hSCtop hperp hxS hli hQx hBx
  set v : Fin 2 ⊕ Fin 2 → ι₂ → K := Sum.elim x y with hv
  set e : Fin 2 ⊕ Fin 2 → ι₂ → K := fun c => oVec oe₂ 0 (Pi.single c 1) with he
  have hsymm : ∀ a b, Q₂.polarBilin a b = Q₂.polarBilin b a := polarBilin_comm Q₂
  have heB : ∀ c c', Q₂.polarBilin (e c) (e c') = (quadPlus 2 K).polarBilin (Pi.single c 1)
      (Pi.single c' 1) := fun c c' => polarBilin_oVec_inr_inr hQ₂ _ _
  have hq : ∀ c c' : Fin 2 ⊕ Fin 2, (quadPlus 2 K).polarBilin (Pi.single c 1) (Pi.single c' 1) =
      match c, c' with
      | .inl s, .inr t => if s = t then 1 else 0
      | .inr s, .inl t => if s = t then 1 else 0
      | _, _ => 0 := by
    intro c c'
    rcases c with s | s <;> rcases c' with t | t
    · exact polarBilin_uE_inl_inl s t
    · exact polarBilin_uE_inl_inr s t
    · rw [polarBilin_comm, polarBilin_uE_inl_inr]
      simp [eq_comm]
    · rw [polarBilin_quadPlus_uE_inr]
      simp
  have hvB : ∀ c c', Q₂.polarBilin (v c) (v c') =
      (quadPlus 2 K).polarBilin (Pi.single c 1) (Pi.single c' 1) := by
    intro c c'
    rw [hq]
    rcases c with s | s <;> rcases c' with t | t
    · exact hBx s t
    · exact hxy s t
    · show Q₂.polarBilin (y s) (x t) = _
      rw [hsymm, hxy]
      simp [eq_comm]
    · exact hyy s t
  have heQ : ∀ c, Q₂ (e c) = 0 := fun c => by
    rw [he, quad_oVec_inr hQ₂, quadPlus_apply]
    rcases c with s | s <;> simp [Pi.single_apply]
  have hvQ : ∀ c, Q₂ (v c) = 0 := fun c => by
    rcases c with s | s
    · exact hQx s
    · exact hQy s
  have hfrom : ∀ w : Fin 2 ⊕ Fin 2 → ι₂ → K,
      (∀ i j, Q₂.polarBilin (w (.inl i)) (w (.inr j)) = if i = j then 1 else 0) →
      (∀ i j, Q₂.polarBilin (w (.inl i)) (w (.inl j)) = 0) →
      (∀ i j, Q₂.polarBilin (w (.inr i)) (w (.inr j)) = 0) → LinearIndependent K w :=
    fun w h1 h2 h3 => linearIndependent_of_hyperbolic h1 h2 h3
  have heli : LinearIndependent K e := hfrom e (fun i j => by rw [heB, hq])
    (fun i j => by rw [heB, hq]) (fun i j => by rw [heB, hq])
  have hvli : LinearIndependent K v := hfrom v (fun i j => by rw [hvB, hq])
    (fun i j => by rw [hvB, hq]) (fun i j => by rw [hvB, hq])
  set σ : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  obtain ⟨G, hGQ, hGe⟩ := exists_isometryGL_family hnd (e ∘ σ) (v ∘ σ)
    (heli.comp σ σ.injective) (hvli.comp σ σ.injective)
    (fun i => by simp only [Function.comp_apply, heQ, hvQ])
    (fun i j => by simp only [Function.comp_apply, heB, hvB])
  have hGev : ∀ c, (G : Matrix ι₂ ι₂ K) *ᵥ e c = v c := fun c => by
    have := hGe (σ.symm c)
    simpa using this
  have hvS : ∀ c, v c ∈ S := fun c => by
    rcases c with s | s
    · exact hxS s
    · exact hyS s
  have hoVec : ∀ u : Fin 2 ⊕ Fin 2 → K, oVec oe₂ 0 u = ∑ c, u c • e c := fun u => by
    refine oVec_ext oe₂ (fun a => ?_) (fun b => ?_)
    · simp [he, oVec_apply_inl, Finset.sum_apply]
    · simp [he, oVec_apply_inr, Finset.sum_apply, Pi.single_apply]
  have hGU₁ : ∀ u, (G : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u = ∑ c, u c • v c := fun u => by
    rw [hoVec, mulVec_sum]
    simp only [mulVec_smul, hGev]
  have hspan : Submodule.span K (Set.range v) = S := by
    refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.mpr ?_) ?_
    · rintro _ ⟨c, rfl⟩
      exact hvS c
    · rw [finrank_span_eq_card hvli, hS4]
      simp
  refine ⟨G, hGQ, fun u => ?_, fun w => ?_, fun s hs => ?_⟩
  · rw [hGU₁]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hvS c)
  ·
    set g := (G : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ w 0
    have hgv : ∀ c, Q₂.polarBilin g (v c) = 0 := fun c => by
      have h0 : (fun b => oVec oe₂ w 0 (oe₂ (.inr b))) = 0 := funext fun b => by
        rw [oVec_apply_inr, Pi.zero_apply]
      rw [← hGev, polarBilin_mulVec_of_isometry Q₂ hGQ, he, polarBilin_oVec_inr hQ₂, h0, map_zero,
        LinearMap.zero_apply]
    have hgS : ∀ s ∈ S, Q₂.polarBilin g s = 0 := by
      intro s hs
      rw [← hspan] at hs
      induction hs using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨c, rfl⟩ := hz
        exact hgv c
      | zero => exact map_zero _
      | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
      | smul r a _ ha => rw [map_smul, ha, smul_zero]
    obtain ⟨s, hs, c, hc, hsc⟩ := Submodule.mem_sup.mp (hSCtop ▸ Submodule.mem_top (x := g))
    have hs0 : s = 0 := by
      refine hnd.1 s fun z => ?_
      obtain ⟨s', hs', c', hc', rfl⟩ := Submodule.mem_sup.mp (hSCtop ▸ Submodule.mem_top (x := z))
      rw [map_add, hperp s hs c' hc', add_zero]
      have h1 := hgS s' hs'
      rw [← hsc, map_add, LinearMap.add_apply, hsymm c s', hperp s' hs' c hc, add_zero] at h1
      exact h1
    rw [← hsc, hs0, zero_add]
    exact hc
  ·
    rw [← hspan] at hs
    induction hs using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      refine ⟨Pi.single c 1, ?_⟩
      rw [hGU₁]
      simp [Pi.single_apply]
    | zero => exact ⟨0, by rw [hGU₁]; simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, rfl⟩ := ha
      obtain ⟨u', rfl⟩ := hb
      exact ⟨u + u', by rw [hGU₁, hGU₁, hGU₁, ← Finset.sum_add_distrib]; simp [add_smul]⟩
    | smul r a _ ha =>
      obtain ⟨u, rfl⟩ := ha
      exact ⟨r • u, by rw [hGU₁, hGU₁, Finset.smul_sum]; simp [smul_smul]⟩

end Main

section Conj

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {ι₃ ι₂ : Type}
  [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}

omit [Fintype K] [DecidableEq K] [CharP K 2] in
theorem exists_oInnerGL_of_fix_preserve {M : GL ι₂ K}
    (h3 : ∀ w : ι₃ → K, (M : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ w 0 = oVec oe₂ w 0)
    (h1 : ∀ (u : Fin 2 ⊕ Fin 2 → K) (a : ι₃),
      ((M : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u) (oe₂ (.inl a)) = 0)
    (h3' : ∀ w : ι₃ → K, ((M⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ w 0 = oVec oe₂ w 0)
    (h1' : ∀ (u : Fin 2 ⊕ Fin 2 → K) (a : ι₃),
      (((M⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u) (oe₂ (.inl a)) = 0) :
    ∃ X : GL (Fin 2 ⊕ Fin 2) K, M = oInnerGL oe₂ X := by
  have hM := eq_oblk_of_fix_preserve h3 h1
  have hM' := eq_oblk_of_fix_preserve h3' h1'
  set X₁ := (M : Matrix ι₂ ι₂ K).submatrix (fun b => oe₂ (.inr b)) (fun b => oe₂ (.inr b))
  set X₂ := ((M⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K).submatrix (fun b => oe₂ (.inr b))
    (fun b => oe₂ (.inr b))
  have h12 : X₁ * X₂ = 1 := by
    have h := congrArg Units.val (mul_inv_cancel M)
    rw [Units.val_mul, Units.val_one, hM, hM', oblk_mul, Matrix.one_mul,
      ← oblk_one (oe := oe₂)] at h
    exact (oblk_injective h).2
  have h21 : X₂ * X₁ = 1 := by
    have h := congrArg Units.val (inv_mul_cancel M)
    rw [Units.val_mul, Units.val_one, hM, hM', oblk_mul, Matrix.one_mul,
      ← oblk_one (oe := oe₂)] at h
    exact (oblk_injective h).2
  refine ⟨⟨X₁, X₂, h12, h21⟩, Units.ext ?_⟩
  rw [coe_oInnerGL]
  exact hM

variable (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
include hQ₂

omit [Fintype K] [DecidableEq K] [CharP K 2] in
theorem isometry_of_oInnerGL {X : GL (Fin 2 ⊕ Fin 2) K}
    (hX : ∀ w, Q₂ (((oInnerGL oe₂ X : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (u : Fin 2 ⊕ Fin 2 → K) :
    StatedQuadPlus 2 K ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) =
      StatedQuadPlus 2 K u := by
  have h := hX (oVec oe₂ 0 u)
  rw [coe_oInnerGL, oblk_mulVec_eq, hQ₂, hQ₂] at h
  simpa [oVec_apply_inl, oVec_apply_inr] using h

end Conj

section Final

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2] {ι₃ ι₂ : Type}
  [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}
  (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
  (hnd : Q₂.polarBilin.Nondegenerate)
include hQ₂ hnd

theorem exists_conj_eq_oY₂ {H : Subgroup (GL ι₂ K)} (hHΩ : H ≤ StatedOmega ⇑Q₂)
    (hHperf : ⁅H, H⁆ = H) (hcard : Nat.card H = Nat.card (oY₂ (K := K) oe₂)) {h : GL ι₂ K}
    (hh : h ∈ H) (hord : h ^ (Fintype.card K - 1) = 1)
    (hC : Module.finrank K (fixVec H) = Fintype.card ι₃)
    (hCh : Module.finrank K (fixVec (Subgroup.zpowers h)) = Fintype.card ι₃) :
    ∃ G : GL ι₂ K, (∀ w, Q₂ ((G : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) ∧
      H = (oY₂ oe₂).map (MulAut.conj G).toMonoidHom := by
  have hcardι : Fintype.card ι₂ = Fintype.card ι₃ + 4 := by
    rw [← Fintype.card_congr oe₂, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin]
  have hfix_iff : ∀ w, w ∈ fixVec H ↔ (h : Matrix ι₂ ι₂ K) *ᵥ w = w := by
    have hCCh : fixVec H = fixVec (Subgroup.zpowers h) :=
      Submodule.eq_of_le_of_finrank_eq (fixVec_anti (Subgroup.zpowers_le.mpr hh)) (by rw [hC, hCh])
    intro w
    rw [hCCh]
    exact ⟨fun hw => hw h (Subgroup.mem_zpowers h), mem_fixVec_zpowers⟩
  set C := fixVec H with hCdef
  set f : Module.End K (ι₂ → K) := Matrix.toLin' (h : Matrix ι₂ ι₂ K) with hfdef
  have hfv : ∀ v, f v = (h : Matrix ι₂ ι₂ K) *ᵥ v := fun v => Matrix.toLin'_apply _ v
  set S := LinearMap.range (f - 1) with hSdef
  have hSmem : ∀ y, (f - 1) y = (h : Matrix ι₂ ι₂ K) *ᵥ y - y := fun y => by
    rw [LinearMap.sub_apply, Module.End.one_apply, hfv]
  have hker : LinearMap.ker (f - 1) = C := by
    ext w
    rw [LinearMap.mem_ker, hSmem, sub_eq_zero, hfix_iff]
  have hS4 : Module.finrank K S = 4 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (f - 1)
    rw [hker, hC, Module.finrank_fintype_fun_eq_card, hcardι] at h1
    show Module.finrank K (LinearMap.range (f - 1)) = 4
    omega
  have hhpow : (h : Matrix ι₂ ι₂ K) ^ (Fintype.card K - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hord, Units.val_one]
  have hSC : S ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨y, rfl⟩, hyC⟩
    rw [Submodule.mem_bot, hSmem]
    have hyC' := (hfix_iff _).mp hyC
    rw [hSmem] at hyC'
    exact eq_zero_of_fixed_of_sub hhpow hyC'
  have hSCtop : S ⊔ C = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq S C
    rw [hSC, finrank_bot, add_zero, hS4, hC] at h1
    rw [h1, Module.finrank_fintype_fun_eq_card, hcardι, add_comm]
  have hhQ : ∀ w, Q₂ ((h : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w :=
    quad_mulVec_of_mem_statedOmega (hHΩ hh)
  have hsymm : ∀ a b, Q₂.polarBilin a b = Q₂.polarBilin b a := polarBilin_comm Q₂
  have hperp : ∀ s ∈ S, ∀ c ∈ C, Q₂.polarBilin s c = 0 := by
    rintro _ ⟨y, rfl⟩ c hc
    have hc' := (hfix_iff c).mp hc
    have h1 := polarBilin_mulVec_of_isometry Q₂ hhQ y c
    rw [hc'] at h1
    rw [hSmem, map_sub, LinearMap.sub_apply, h1, sub_self]
  have hfS : ∀ v ∈ S, f v ∈ S := by
    rintro _ ⟨y, rfl⟩
    refine ⟨f y, ?_⟩
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
      map_sub]
  have hfixS : ∀ v ∈ S, f v = v → v = 0 := fun v hvS hv => by
    have hvC : v ∈ C := by rw [hfix_iff, ← hfv, hv]
    have hmem : v ∈ S ⊓ C := ⟨hvS, hvC⟩
    rwa [hSC, Submodule.mem_bot] at hmem
  have hford : f ^ (Fintype.card K - 1) = 1 := by
    refine LinearMap.ext fun v => ?_
    have hpow : ∀ n : ℕ, (f ^ n) v = ((h : Matrix ι₂ ι₂ K) ^ n) *ᵥ v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, hfv, pow_succ', mulVec_mulVec]
    rw [hpow, hhpow, one_mulVec, Module.End.one_apply]
  have hfQ : ∀ v, Q₂ (f v) = Q₂ v := fun v => by rw [hfv]; exact hhQ v
  obtain ⟨x₀, hx₀, x₁, hx₁, hli, hQx₀, hQx₁, hBx⟩ :=
    exists_totallySingular_pair hford hfQ hfS (by omega) hfixS
  obtain ⟨G, hGQ, hGU₁, hGU₃, hGS⟩ := exists_isometry_frame hQ₂ hnd hSCtop hperp hS4
    (x := ![x₀, x₁]) (fun i => by fin_cases i <;> assumption) hli
    (fun i => by fin_cases i <;> assumption)
    (fun i j => by
      fin_cases i <;> fin_cases j
      · exact polarBilin_self_eq_zero x₀
      · exact hBx
      · rw [hsymm]
        exact hBx
      · exact polarBilin_self_eq_zero x₁)
  have hYS : ∀ Y ∈ H, ∀ s ∈ S, (Y : Matrix ι₂ ι₂ K) *ᵥ s ∈ S := by
    intro Y hY s hs
    have hYQ := quad_mulVec_of_mem_statedOmega (hHΩ hY)
    obtain ⟨s', hs', c', hc', hsc⟩ :=
      Submodule.mem_sup.mp (hSCtop ▸ Submodule.mem_top (x := (Y : Matrix ι₂ ι₂ K) *ᵥ s))
    have hc0 : c' = 0 := by
      refine hnd.1 c' fun z => ?_
      obtain ⟨s'', hs'', c'', hc'', rfl⟩ :=
        Submodule.mem_sup.mp (hSCtop ▸ Submodule.mem_top (x := z))
      rw [map_add, hsymm c' s'', hperp s'' hs'' c' hc', zero_add]
      have h1 := polarBilin_mulVec_of_isometry Q₂ hYQ s c''
      rw [show (Y : Matrix ι₂ ι₂ K) *ᵥ c'' = c'' from hc'' Y hY, ← hsc, map_add,
        LinearMap.add_apply, hperp s' hs' c'' hc'', zero_add, hperp s hs c'' hc''] at h1
      exact h1
    rw [← hsc, hc0, add_zero]
    exact hs'
  have hG1 : ∀ w, ((G⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ ((G : Matrix ι₂ ι₂ K) *ᵥ w) = w :=
    fun w => by rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hconjv : ∀ Y : GL ι₂ K, (((MulAut.conj G⁻¹).toMonoidHom Y : GL ι₂ K) :
      Matrix ι₂ ι₂ K) = ((G⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) * (Y : Matrix ι₂ ι₂ K) *
        (G : Matrix ι₂ ι₂ K) := fun Y => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul, Units.val_mul]
  have hfp : ∀ Y ∈ H, (∀ w : ι₃ → K,
      (((MulAut.conj G⁻¹).toMonoidHom Y : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ w 0 =
        oVec oe₂ w 0) ∧ ∀ (u : Fin 2 ⊕ Fin 2 → K) (a : ι₃),
      ((((MulAut.conj G⁻¹).toMonoidHom Y : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ oVec oe₂ 0 u)
        (oe₂ (.inl a)) = 0 := by
    intro Y hY
    refine ⟨fun w => ?_, fun u a => ?_⟩
    · rw [hconjv, ← mulVec_mulVec, ← mulVec_mulVec, hGU₃ w Y hY, hG1]
    · rw [hconjv, ← mulVec_mulVec, ← mulVec_mulVec]
      obtain ⟨u', hu'⟩ := hGS _ (hYS Y hY _ (hGU₁ u))
      rw [hu', hG1, oVec_apply_inl, Pi.zero_apply]
  set P := H.map (MulAut.conj G⁻¹).toMonoidHom with hP
  have hPblk : ∀ M ∈ P, ∃ X : GL (Fin 2 ⊕ Fin 2) K, M = oInnerGL oe₂ X := by
    rintro _ ⟨Y, hY, rfl⟩
    obtain ⟨h3, h1⟩ := hfp Y hY
    obtain ⟨h3', h1'⟩ := hfp Y⁻¹ (inv_mem hY)
    rw [map_inv] at h3' h1'
    exact exists_oInnerGL_of_fix_preserve h3 h1 h3' h1'
  have hGi : ∀ v, Q₂ (((G⁻¹ : GL ι₂ K) : Matrix ι₂ ι₂ K) *ᵥ v) = Q₂ v := fun v => by
    rw [← hGQ, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hHperf]
  set O₁ := closure {X : GL (Fin 2 ⊕ Fin 2) K | ∀ u, StatedQuadPlus 2 K
    ((X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u) = StatedQuadPlus 2 K u}
  have hPO : P ≤ O₁.map (oInnerGL oe₂) := by
    intro M hM
    obtain ⟨X, rfl⟩ := hPblk M hM
    refine ⟨X, subset_closure (isometry_of_oInnerGL hQ₂ fun w => ?_), rfl⟩
    obtain ⟨Y, hY, hYM⟩ := hM
    rw [← hYM, hconjv, ← mulVec_mulVec, ← mulVec_mulVec, hGi,
      quad_mulVec_of_mem_statedOmega (hHΩ hY), hGQ]
  have hPle : P ≤ oY₂ oe₂ := by
    rw [← hPperf]
    refine (commutator_mono hPO hPO).trans ?_
    rw [← Subgroup.map_commutator]
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨B, A, hBA⟩ := exists_rho_of_mem_statedOmega_quadPlus_two (K := K) (Y := X) hX
    have hX' : oInnerGL oe₂ X = oRhoOneGL oe₂ B * oRhoTwoGL oe₂ A := by
      apply Units.ext
      rw [coe_oInnerGL, hBA, Units.val_mul, coe_oRhoOneGL, coe_oRhoTwoGL, oblk_mul,
        Matrix.one_mul]
    rw [hX']
    exact mul_mem (mem_sup_right ⟨B, rfl⟩) (mem_sup_left ⟨A, rfl⟩)
  have hPeq : P = oY₂ oe₂ := by
    refine Subgroup.eq_of_le_of_card_ge hPle ?_
    rw [← hcard, hP, Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective]
  refine ⟨G, hGQ, ?_⟩
  rw [← hPeq, hP, Subgroup.map_map]
  have hid : ((MulAut.conj G).toMonoidHom.comp (MulAut.conj G⁻¹).toMonoidHom) =
      MonoidHom.id (GL ι₂ K) := by
    ext g : 1
    simp [MulAut.conj_apply, mul_assoc]
  rw [hid, Subgroup.map_id]

end Final

end CFSG.ComponentClassification.RankTwoClassical.ORigid

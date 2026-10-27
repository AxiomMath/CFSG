module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotPlusEightF6Levi
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthBasic

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap Module CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus regular_coordinateQuadPlus)

section P

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem rootLevi_matrix (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) :
    g (Pi.single a 1) = (g (Pi.single a 1)) a • Pi.single a 1 +
        (g (Pi.single a 1)) b • Pi.single b 1 ∧
      g (Pi.single b 1) = (g (Pi.single b 1)) a • Pi.single a 1 +
        (g (Pi.single b 1)) b • Pi.single b 1 ∧
      (g (Pi.single a 1)) a * (g (Pi.single b 1)) b -
        (g (Pi.single b 1)) a * (g (Pi.single a 1)) b = 1 := by
  obtain ⟨h1, h2⟩ := rootLevi_apply_e_eq hi hj hd hgM
  have hdet := det_coeff_eq_one (hi.orth hj hd) hgM.1.1 (mem_centralizer_singleton_iff.mp hgM.1.2)
  simp only [IsHypCoord.hypPair_e, IsHypCoord.hypPair_f] at hdet
  rw [polar_comm Q _ (Pi.single a' 1), polar_comm Q _ (Pi.single b' 1),
    polar_comm Q _ (Pi.single a' 1), polar_comm Q _ (Pi.single b' 1), hi.polar_right,
    hj.polar_right, hi.polar_right, hj.polar_right] at hdet
  exact ⟨h1, h2, hdet⟩

theorem rootLevi_sq_e (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) :
    g (g (Pi.single a 1)) = ((g (Pi.single a 1)) a + (g (Pi.single b 1)) b) •
        g (Pi.single a 1) - Pi.single a 1 ∧
      g (g (Pi.single b 1)) = ((g (Pi.single a 1)) a + (g (Pi.single b 1)) b) •
        g (Pi.single b 1) - Pi.single b 1 := by
  obtain ⟨h1, h2, hdet⟩ := rootLevi_matrix hi hj hd hgM
  set A := (g (Pi.single a 1)) a
  set C := (g (Pi.single a 1)) b
  set B := (g (Pi.single b 1)) a
  set D := (g (Pi.single b 1)) b
  constructor
  · conv_lhs => rw [h1]
    rw [map_add, map_smul, map_smul, h1, h2]
    linear_combination (norm := module) (-hdet) • (Pi.single a (1 : K) : Fin d → K)
  · conv_lhs => rw [h2]
    rw [map_add, map_smul, map_smul, h1, h2]
    linear_combination (norm := module) (-hdet) • (Pi.single b (1 : K) : Fin d → K)

end P

section Eigen

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}
  {a a' b b' : Fin d}

theorem rootLevi_exists_alpha (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) (hodd : Odd (orderOf g))
    (hgq : g ^ Nat.card K = g)
    (hnfix : ¬ (g (Pi.single a 1) = Pi.single a 1 ∧ g (Pi.single b 1) = Pi.single b 1)) :
    ∃ α : Kˣ, α * α ≠ 1 ∧
      g (g (Pi.single a 1)) = ((α : K) + ((α⁻¹ : Kˣ) : K)) • g (Pi.single a 1) - Pi.single a 1 ∧
      g (g (Pi.single b 1)) = ((α : K) + ((α⁻¹ : Kˣ) : K)) • g (Pi.single b 1) -
        Pi.single b 1 := by
  classical
  have := Fintype.ofFinite K
  have h₁₂ := hi.orth hj hd
  have hgO := hgM.1.1
  have hc := mem_centralizer_singleton_iff.mp hgM.1.2
  obtain ⟨h1, h2, -⟩ := rootLevi_matrix hi hj hd hgM
  obtain ⟨hs1, hs2⟩ := rootLevi_sq_e hi hj hd hgM
  set τ := (g (Pi.single a 1)) a + (g (Pi.single b 1)) b with hτ
  set P := Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1} with hPdef
  have hea : (Pi.single a (1 : K) : Fin d → K) ∈ P := Submodule.subset_span (by simp)
  have heb : (Pi.single b (1 : K) : Fin d → K) ∈ P := Submodule.subset_span (by simp)
  have hP : ∀ x ∈ P, g x ∈ P := by
    intro x hx
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
    rw [map_add, map_smul, map_smul, h1, h2]
    exact P.add_mem (P.smul_mem _ (P.add_mem (P.smul_mem _ hea) (P.smul_mem _ heb)))
      (P.smul_mem _ (P.add_mem (P.smul_mem _ hea) (P.smul_mem _ heb)))
  set T : Module.End K P := LinearMap.restrict g.toLinearMap hP with hT
  have hTk : ∀ k : ℕ, ∀ x : P, ((T ^ k) x : Fin d → K) = (g ^ k) (x : Fin d → K) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', LinearEquiv.mul_apply, ← ih]
      rfl
  have hTq : T ^ Fintype.card K = T := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hTk, ← Nat.card_eq_fintype_card, hgq]
    rfl
  have hea0 : (Pi.single a (1 : K) : Fin d → K) ≠ 0 := fun h => by
    have := congrFun h a
    simp at this
  have : Nontrivial P := ⟨⟨⟨_, hea⟩, 0, fun h => hea0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, v, hv0, hTv⟩ := exists_eigen_of_pow_card_eq T hTq
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp v.2
  have hgv : g (v : Fin d → K) = μ • (v : Fin d → K) := congrArg Subtype.val hTv
  have hv0' : (v : Fin d → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hab : a ≠ b := hd.left_ne_left.symm
  have hst0 : s ≠ 0 ∨ t ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hv0'
    rw [← hst, hcon.1, hcon.2, zero_smul, zero_smul, add_zero]
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    rw [one_smul, ← hst] at hgv
    obtain ⟨hq1, hq2⟩ := sq_fix_of_fixed h₁₂ hgO hc hgv hst0
    exact hnfix ⟨apply_eq_self_of_sq_of_pow hq1 hodd (pow_orderOf_eq_one g),
      apply_eq_self_of_sq_of_pow hq2 hodd (pow_orderOf_eq_one g)⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgv
    exact hv0' (g.injective (hgv.trans (map_zero g).symm))
  have hCH : g (g (v : Fin d → K)) = τ • g (v : Fin d → K) - (v : Fin d → K) := by
    rw [← hst, map_add, map_smul, map_smul, map_add, map_smul, map_smul, hs1, hs2]
    module
  rw [hgv, map_smul, hgv, smul_smul, smul_smul] at hCH
  have hμτ : μ * μ - τ * μ + 1 = 0 := by
    have h' : (μ * μ - τ * μ + 1) • (v : Fin d → K) = 0 := by
      rw [add_smul, sub_smul, hCH, one_smul]
      abel
    exact (smul_eq_zero.mp h').resolve_right hv0'
  set α : Kˣ := Units.mk0 μ hμ0 with hα
  have hτα : τ = (α : K) + ((α⁻¹ : Kˣ) : K) := by
    rw [hα, Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    linear_combination -hμτ
  refine ⟨α, fun h => mul_self_ne_one_of_ne_one hμ1 ?_, ?_, ?_⟩
  · have := congrArg Units.val h
    simpa [hα] using this
  · rw [← hτα]
    exact hs1
  · rw [← hτα]
    exact hs2

end Eigen

section Dual

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem mem_rootLevi_symm (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    {g : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) :
    g ∈ rootLevi Q hi.symm.hypPair hj.symm.hypPair :=
  ⟨⟨hgM.1.1, hgM.2⟩, hgM.1.2⟩

theorem rootLevi_apply_f_mem (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {x : Fin d → K}
    (hx : x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1}) :
    g x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1} := by
  obtain ⟨k1, k2⟩ := rootLevi_apply_e_eq hi.symm hj.symm hd.swap_left.swap_right
    (mem_rootLevi_symm hi hj hgM)
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smul, map_smul, k1, k2]
  exact Submodule.mem_span_pair.mpr ⟨s * (g (Pi.single a' 1)) a' + t * (g (Pi.single b' 1)) a',
    s * (g (Pi.single a' 1)) b' + t * (g (Pi.single b' 1)) b', by module⟩

theorem rootLevi_apply_e_mem (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {x : Fin d → K}
    (hx : x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1}) :
    g x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1} := by
  obtain ⟨k1, k2⟩ := rootLevi_apply_e_eq hi hj hd hgM
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [map_add, map_smul, map_smul, k1, k2]
  exact Submodule.mem_span_pair.mpr ⟨s * (g (Pi.single a 1)) a + t * (g (Pi.single b 1)) a,
    s * (g (Pi.single a 1)) b + t * (g (Pi.single b 1)) b, by module⟩

theorem rootLevi_sq_f (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {τ : K}
    (he1 : g (g (Pi.single a 1)) = τ • g (Pi.single a 1) - Pi.single a 1)
    (he2 : g (g (Pi.single b 1)) = τ • g (Pi.single b 1) - Pi.single b 1) :
    g (g (Pi.single a' 1)) = τ • g (Pi.single a' 1) - Pi.single a' 1 ∧
      g (g (Pi.single b' 1)) = τ • g (Pi.single b' 1) - Pi.single b' 1 := by
  have hgO := hgM.1.1
  have hpol : ∀ x y : Fin d → K, polar Q x (g y) = polar Q (g⁻¹ x) y := fun x y => by
    have h := polar_map_of_mem hgO (g⁻¹ x) y
    rwa [LinearEquiv.apply_inv_apply'] at h
  have hinv : ∀ e : Fin d → K, g (g e) = τ • g e - e → g⁻¹ (g⁻¹ e) = τ • g⁻¹ e - e := by
    intro e he
    have h := congrArg (fun z => g⁻¹ (g⁻¹ z)) he
    simp only [LinearEquiv.inv_apply_apply', map_sub, map_smul] at h
    linear_combination (norm := module) h
  have hz : ∀ e : Fin d → K, g (g e) = τ • g e - e → ∀ f : Fin d → K,
      polar Q e (g (g f) - τ • g f + f) = 0 := by
    intro e he f
    rw [polar_add_right, polar_sub_right, polar_smul_right, hpol e (g f), hpol (g⁻¹ e) f,
      hpol e f, hinv e he, polar_sub_left, polar_smul_left]
    ring
  have key : ∀ f ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1},
      g (g f) - τ • g f + f = 0 := by
    intro f hf
    have hX : g (g f) - τ • g f + f ∈
        Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1} :=
      Submodule.add_mem _ (Submodule.sub_mem _
        (rootLevi_apply_f_mem hi hj hd hgM (rootLevi_apply_f_mem hi hj hd hgM hf))
        (Submodule.smul_mem _ _ (rootLevi_apply_f_mem hi hj hd hgM hf))) hf
    obtain ⟨c₁, c₂, hc⟩ := Submodule.mem_span_pair.mp hX
    have h1 := hz _ he1 f
    have h2 := hz _ he2 f
    rw [hi.polar_left, ← hc] at h1
    rw [hj.polar_left, ← hc] at h2
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne hd.right_ne_right.symm, Pi.single_eq_of_ne hd.right_ne_right,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at h1 h2
    rw [← hc, h1, h2, zero_smul, zero_smul, add_zero]
  have hf₁ := key (Pi.single a' 1) (Submodule.subset_span (by simp))
  have hf₂ := key (Pi.single b' 1) (Submodule.subset_span (by simp))
  constructor
  · rw [← sub_eq_zero, ← hf₁]
    abel
  · rw [← sub_eq_zero, ← hf₂]
    abel

end Dual

section W

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem polar_eq_zero_of_span_of_mem_subW (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    {w : Fin d → K} (hw : w ∈ subW K a a' b b') {x : Fin d → K}
    (hx : x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1} ∨
      x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1}) :
    polar Q x w = 0 := by
  obtain ⟨⟨hwa, hwa'⟩, hwb, hwb'⟩ := hw
  rcases hx with hx | hx <;> obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  · rw [polar_add_left, polar_smul_left, polar_smul_left, hi.polar_left, hj.polar_left, hwa', hwb']
    ring
  · rw [polar_add_left, polar_smul_left, polar_smul_left, hi.polar_right, hj.polar_right, hwa, hwb]
    ring

theorem rootLevi_apply_mem_subW (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {w : Fin d → K}
    (hw : w ∈ subW K a a' b b') : g w ∈ subW K a a' b b' := by
  have hgO := hgM.1.1
  have hgM' : g⁻¹ ∈ rootLevi Q hi.hypPair hj.hypPair := inv_mem hgM
  have hpol : ∀ x : Fin d → K, polar Q x (g w) = polar Q (g⁻¹ x) w := fun x => by
    have h := polar_map_of_mem hgO (g⁻¹ x) w
    rwa [LinearEquiv.apply_inv_apply'] at h
  have hE : ∀ x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1},
      polar Q x (g w) = 0 := fun x hx => by
    rw [hpol]
    exact polar_eq_zero_of_span_of_mem_subW hi hj hw
      (Or.inl (rootLevi_apply_e_mem hi hj hd hgM' hx))
  have hF : ∀ x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1},
      polar Q x (g w) = 0 := fun x hx => by
    rw [hpol]
    exact polar_eq_zero_of_span_of_mem_subW hi hj hw
      (Or.inr (rootLevi_apply_f_mem hi hj hd hgM' hx))
  have h1 := hF _ (Submodule.subset_span (by simp) : (Pi.single a' (1 : K) : Fin d → K) ∈ _)
  have h2 := hE _ (Submodule.subset_span (by simp) : (Pi.single a (1 : K) : Fin d → K) ∈ _)
  have h3 := hF _ (Submodule.subset_span (by simp) : (Pi.single b' (1 : K) : Fin d → K) ∈ _)
  have h4 := hE _ (Submodule.subset_span (by simp) : (Pi.single b (1 : K) : Fin d → K) ∈ _)
  rw [hi.polar_right] at h1
  rw [hi.polar_left] at h2
  rw [hj.polar_right] at h3
  rw [hj.polar_left] at h4
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem piW_eq_zero_of_span (hd : PairDisjoint a a' b b') (haa : a ≠ a') (hbb : b ≠ b')
    {x : Fin d → K}
    (hx : x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1} ∨
      x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1}) :
    piW a a' b b' x = 0 := by
  rcases hx with hx | hx <;> obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
  · rw [piW_add, piW_smul, piW_smul, piW_single_of_mem (Or.inl rfl) hd haa hbb,
      piW_single_of_mem (Or.inr (Or.inr (Or.inl rfl))) hd haa hbb, smul_zero, smul_zero, add_zero]
  · rw [piW_add, piW_smul, piW_smul, piW_single_of_mem (Or.inr (Or.inl rfl)) hd haa hbb,
      piW_single_of_mem (Or.inr (Or.inr (Or.inr rfl))) hd haa hbb, smul_zero, smul_zero, add_zero]

theorem rootLevi_piW_comm (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) (v : Fin d → K) :
    piW a a' b b' (g v) = g (piW a a' b b' v) := by
  have hz : ∀ x, (x ∈ Submodule.span K {(Pi.single a (1 : K) : Fin d → K), Pi.single b 1} ∨
      x ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1}) →
      piW a a' b b' (g x) = 0 := fun x hx => by
    refine piW_eq_zero_of_span hd hi.ne hj.ne ?_
    rcases hx with hx | hx
    · exact Or.inl (rootLevi_apply_e_mem hi hj hd hgM hx)
    · exact Or.inr (rootLevi_apply_f_mem hi hj hd hgM hx)
  have hW := rootLevi_apply_mem_subW hi hj hd hgM (piW_mem hi hj hd v)
  conv_lhs => rw [eq_coord hd v]
  rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, piW_add,
    piW_add, piW_add, piW_add, piW_smul, piW_smul, piW_smul, piW_smul,
    hz _ (Or.inl (Submodule.subset_span (by simp))), hz _ (Or.inr (Submodule.subset_span (by simp))),
    hz _ (Or.inl (Submodule.subset_span (by simp))), hz _ (Or.inr (Submodule.subset_span (by simp))),
    piW_eq_self hW]
  simp

end W

section DualEigen

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem rootLevi_not_scalar_f (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {β : K} (hβ : β * β ≠ 1)
    (h1 : g (Pi.single a' 1) = β • Pi.single a' 1) (h2 : g (Pi.single b' 1) = β • Pi.single b' 1) :
    False := by
  have hgO := hgM.1.1
  obtain ⟨-, -, hdet⟩ := rootLevi_matrix hi hj hd hgM
  have p11 := polar_map_of_mem hgO (Pi.single a 1) (Pi.single a' 1)
  have p12 := polar_map_of_mem hgO (Pi.single a 1) (Pi.single b' 1)
  have p21 := polar_map_of_mem hgO (Pi.single b 1) (Pi.single a' 1)
  have p22 := polar_map_of_mem hgO (Pi.single b 1) (Pi.single b' 1)
  rw [h1, polar_smul_right, polar_comm, hi.polar_right, hi.polar_left, Pi.single_eq_same,
    smul_eq_mul] at p11
  rw [h2, polar_smul_right, polar_comm, hj.polar_right, hi.polar_left,
    Pi.single_eq_of_ne hd.right_ne_right.symm, smul_eq_mul] at p12
  rw [h1, polar_smul_right, polar_comm, hi.polar_right, hj.polar_left,
    Pi.single_eq_of_ne hd.right_ne_right, smul_eq_mul] at p21
  rw [h2, polar_smul_right, polar_comm, hj.polar_right, hj.polar_left, Pi.single_eq_same,
    smul_eq_mul] at p22
  have hβ0 : β ≠ 0 := by
    rintro rfl
    simp at p11
  have hC : (g (Pi.single a 1)) b = 0 := (mul_eq_zero.mp p12).resolve_left hβ0
  have hB : (g (Pi.single b 1)) a = 0 := (mul_eq_zero.mp p21).resolve_left hβ0
  apply hβ
  have : β * β * ((g (Pi.single a 1)) a * (g (Pi.single b 1)) b -
      (g (Pi.single b 1)) a * (g (Pi.single a 1)) b) = 1 := by
    rw [hB, hC]
    linear_combination (β * (g (Pi.single b 1)) b) * p11 + p22
  rwa [hdet, mul_one] at this

theorem rootLevi_eigen_f_line (hi : IsHypCoord Q a a') (hj : IsHypCoord Q b b')
    (hd : PairDisjoint a a' b b') {g : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hgM : g ∈ rootLevi Q hi.hypPair hj.hypPair) {β : K} (hβ : β * β ≠ 1) {u₁ u₂ : Fin d → K}
    (hu₁ : u₁ ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1})
    (hu₂ : u₂ ∈ Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1})
    (h₁ : g u₁ = β • u₁) (h₂ : g u₂ = β • u₂) :
    ∃ q : Fin d → K, g q = β • q ∧ ∃ c₁ c₂ : K, u₁ = c₁ • q ∧ u₂ = c₂ • q := by
  obtain ⟨x₁, y₁, rfl⟩ := Submodule.mem_span_pair.mp hu₁
  obtain ⟨x₂, y₂, rfl⟩ := Submodule.mem_span_pair.mp hu₂
  by_cases hdet : x₁ * y₂ - x₂ * y₁ = 0
  · by_cases h0 : x₁ = 0 ∧ y₁ = 0
    · obtain ⟨rfl, rfl⟩ := h0
      exact ⟨_, h₂, 0, 1, by simp, by simp⟩
    · by_cases hx : x₁ = 0
      · have hy : y₁ ≠ 0 := fun hy => h0 ⟨hx, hy⟩
        have hx₂ : x₂ = 0 := by
          rw [hx, zero_mul, zero_sub, neg_eq_zero] at hdet
          exact (mul_eq_zero.mp hdet).resolve_right hy
        refine ⟨_, h₁, 1, y₂ / y₁, by simp, ?_⟩
        rw [hx, hx₂, zero_smul, zero_add, zero_add, smul_smul, div_mul_cancel₀ _ hy]
      · refine ⟨_, h₁, 1, x₂ / x₁, by simp, ?_⟩
        have hy₂ : y₂ = x₂ / x₁ * y₁ := by
          field_simp
          linear_combination hdet
        rw [hy₂, smul_add, smul_smul, smul_smul, div_mul_cancel₀ _ hx]
  · exfalso
    have hD : (x₁ * y₂ - x₂ * y₁)⁻¹ * (x₁ * y₂ - x₂ * y₁) = 1 := inv_mul_cancel₀ hdet
    have hf1 : (Pi.single a' (1 : K) : Fin d → K) =
        (x₁ * y₂ - x₂ * y₁)⁻¹ • (y₂ • (x₁ • Pi.single a' 1 + y₁ • Pi.single b' 1) -
          y₁ • (x₂ • Pi.single a' 1 + y₂ • Pi.single b' 1)) := by
      linear_combination (norm := module) (-hD) • (Pi.single a' (1 : K) : Fin d → K)
    have hf2 : (Pi.single b' (1 : K) : Fin d → K) =
        (x₁ * y₂ - x₂ * y₁)⁻¹ • (x₁ • (x₂ • Pi.single a' 1 + y₂ • Pi.single b' 1) -
          x₂ • (x₁ • Pi.single a' 1 + y₁ • Pi.single b' 1)) := by
      linear_combination (norm := module) (-hD) • (Pi.single b' (1 : K) : Fin d → K)
    refine rootLevi_not_scalar_f hi hj hd hgM hβ ?_ ?_
    · conv_lhs => rw [hf1]
      rw [map_smul, map_sub, map_smul, map_smul, h₁, h₂]
      conv_rhs => rw [hf1]
      module
    · conv_lhs => rw [hf2]
      rw [map_smul, map_sub, map_smul, map_smul, h₁, h₂]
      conv_rhs => rw [hf2]
      module

end DualEigen

section Count

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {a a' b b' : Fin d}

theorem eigen_split {V : Type*} [AddCommGroup V] [Module K V] {g : V ≃ₗ[K] V} {α : Kˣ}
    (hα : α * α ≠ 1) {x : V}
    (hx : g (g x) = ((α : K) + ((α⁻¹ : Kˣ) : K)) • g x - x) :
    x = ((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • (g x - ((α⁻¹ : Kˣ) : K) • x) +
        ((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • ((α : K) • x - g x) ∧
      g (((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • (g x - ((α⁻¹ : Kˣ) : K) • x)) =
        (α : K) • (((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • (g x - ((α⁻¹ : Kˣ) : K) • x)) ∧
      g (((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • ((α : K) • x - g x)) =
        ((α⁻¹ : Kˣ) : K) • (((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ • ((α : K) • x - g x)) := by
  have hne : (α : K) - ((α⁻¹ : Kˣ) : K) ≠ 0 :=
    sub_ne_zero.mpr (units_ne_inv_of_mul_self_ne_one' hα)
  have h1 : ((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹ * ((α : K) - ((α⁻¹ : Kˣ) : K)) = 1 :=
    inv_mul_cancel₀ hne
  have h2 : (α : K) * ((α⁻¹ : Kˣ) : K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (norm := module) (-h1) • x
  · rw [map_smul, map_sub, map_smul, hx]
    linear_combination (norm := module) ((((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹) * h2) • x
  · rw [map_smul, map_sub, map_smul, hx]
    linear_combination (norm := module) ((-((α : K) - ((α⁻¹ : Kˣ) : K))⁻¹) * h2) • x

variable [Finite K] in
theorem card_rootRadical_inf_centralizer_le_eigen (hi : IsHypCoord Q a a')
    (hj : IsHypCoord Q b b') (hd : PairDisjoint a a' b b') (g : orthDerived Q)
    (hgM : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ∈ rootLevi Q hi.hypPair hj.hypPair)
    {α : Kˣ} (hα : α * α ≠ 1)
    (hf1 : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((g : (Fin d → K) ≃ₗ[K] (Fin d → K))
      (Pi.single a' 1)) = ((α : K) + ((α⁻¹ : Kˣ) : K)) •
        (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a' 1) - Pi.single a' 1)
    (hf2 : (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((g : (Fin d → K) ≃ₗ[K] (Fin d → K))
      (Pi.single b' 1)) = ((α : K) + ((α⁻¹ : Kˣ) : K)) •
        (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single b' 1) - Pi.single b' 1) :
    Nat.card ((rootRadical Q hi.hypPair hj.hypPair).subgroupOf (orthDerived Q) ⊓
        centralizer ({g} : Set (orthDerived Q)) : Subgroup (orthDerived Q)) ≤
      Nat.card ↥(subW K a a' b b' ⊓ eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (α : K)) *
        Nat.card ↥(subW K a a' b b' ⊓
          eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((α⁻¹ : Kˣ) : K)) * Nat.card K := by
  classical
  have hαK : (α : K) * (α : K) ≠ 1 := fun h =>
    hα (Units.ext (by rw [Units.val_mul, h, Units.val_one]))
  have hα'K : ((α⁻¹ : Kˣ) : K) * ((α⁻¹ : Kˣ) : K) ≠ 1 := by
    intro h
    apply hαK
    have h2 : (α : K) * ((α⁻¹ : Kˣ) : K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (α : K) * (α : K) = ((α : K) * (α : K)) * (((α⁻¹ : Kˣ) : K) * ((α⁻¹ : Kˣ) : K)) := by
          rw [h, mul_one]
      _ = ((α : K) * ((α⁻¹ : Kˣ) : K)) * ((α : K) * ((α⁻¹ : Kˣ) : K)) := by ring
      _ = 1 := by rw [h2, mul_one]
  obtain ⟨s1, p1, m1⟩ := eigen_split hα hf1
  obtain ⟨s2, p2, m2⟩ := eigen_split hα hf2
  have hfa : (Pi.single a' (1 : K) : Fin d → K) ∈
      Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1} :=
    Submodule.subset_span (by simp)
  have hfb : (Pi.single b' (1 : K) : Fin d → K) ∈
      Submodule.span K {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1} :=
    Submodule.subset_span (by simp)
  have hgf := fun {f} (hf : f ∈ Submodule.span K
      {(Pi.single a' (1 : K) : Fin d → K), Pi.single b' 1}) => rootLevi_apply_f_mem hi hj hd hgM hf
  obtain ⟨qp, hqp, c₁, c₂, hc₁, hc₂⟩ := rootLevi_eigen_f_line hi hj hd hgM hαK
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgf hfa) (Submodule.smul_mem _ _ hfa)))
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hgf hfb) (Submodule.smul_mem _ _ hfb))) p1 p2
  obtain ⟨qm, hqm, c₁', c₂', hc₁', hc₂'⟩ := rootLevi_eigen_f_line hi hj hd hgM hα'K
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hfa) (hgf hfa)))
    (Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hfb) (hgf hfb))) m1 m2
  rw [hc₁, hc₁'] at s1
  rw [hc₂, hc₂'] at s2
  set A := (rootRadical Q hi.hypPair hj.hypPair).subgroupOf (orthDerived Q) ⊓
    centralizer ({g} : Set (orthDerived Q)) with hA
  have hcomm : ∀ x : A, ∀ v, ((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))
      ((g : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) =
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (((x : orthDerived Q) :
        (Fin d → K) ≃ₗ[K] (Fin d → K)) v) := by
    intro x v
    have h := mem_centralizer_singleton_iff.mp (mem_inf.mp x.2).2
    have := congrArg (fun z : orthDerived Q => (z : (Fin d → K) ≃ₗ[K] (Fin d → K)) v) h
    simpa only [Subgroup.coe_mul, LinearEquiv.mul_apply] using this
  have hmem : ∀ x : A, ∀ (q : Fin d → K) (β : K),
      (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) q = β • q →
      piW a a' b b' (((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) q) ∈
        subW K a a' b b' ⊓ eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) β := by
    intro x q β hq
    refine ⟨piW_mem hi hj hd _, mem_eigenSub.2 ?_⟩
    rw [← rootLevi_piW_comm hi hj hd hgM, ← hcomm, hq, map_smul, piW_smul]
  let Φ : A → ↥(subW K a a' b b' ⊓ eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (α : K)) ×
      ↥(subW K a a' b b' ⊓ eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((α⁻¹ : Kˣ) : K)) × K :=
    fun x => (⟨_, hmem x qp _ hqp⟩, ⟨_, hmem x qm _ hqm⟩,
      (((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K)) (Pi.single a' 1)) b)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    simp only [Φ, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    have hx := mem_subgroupOf.mp (mem_inf.mp x.2).1
    have hy := mem_subgroupOf.mp (mem_inf.mp y.2).1
    have hW : ∀ (c c' : K), piW a a' b b' (((x : orthDerived Q) : (Fin d → K) ≃ₗ[K] (Fin d → K))
        (c • qp + c' • qm)) = piW a a' b b' (((y : orthDerived Q) :
          (Fin d → K) ≃ₗ[K] (Fin d → K)) (c • qp + c' • qm)) := by
      intro c c'
      rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, piW_add, piW_add, piW_smul,
        piW_smul, piW_smul, piW_smul, h1, h2]
    apply Subtype.ext
    apply Subtype.ext
    refine eq_of_rootRadical_triple hi hj hd hx hy ?_ ?_ h3
    · rw [s1]
      exact hW c₁ c₁'
    · rw [s2]
      exact hW c₂ c₂'
  calc Nat.card A ≤ Nat.card (↥(subW K a a' b b' ⊓
        eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) (α : K)) ×
        ↥(subW K a a' b b' ⊓ eigenSub (g : (Fin d → K) ≃ₗ[K] (Fin d → K)) ((α⁻¹ : Kˣ) : K)) ×
          K) := Nat.card_le_card_of_injective Φ hΦ
    _ = _ := by rw [Nat.card_prod, Nat.card_prod, mul_assoc]

end Count

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
theorem fixSpace_bot {d : ℕ} {Q : QuadraticForm K (Fin d → K)} :
    fixSpace (⊥ : Subgroup (orthDerived Q)) = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true]
  intro g hg
  rw [Subgroup.mem_bot] at hg
  subst hg
  rfl

theorem plusFourGLLeviEigenInput_holds : PlusFourGLLeviEigenInput := by
  intro K _ _ _ hq i j k hij hik hjk Y hYM hYc hYcard hYB hcard g hYz
  classical
  have hi := isHypCoord_coordinateQuadPlus (K := K) (n := 4) i
  have hj := isHypCoord_coordinateQuadPlus (K := K) (n := 4) j
  have hk := isHypCoord_coordinateQuadPlus (K := K) (n := 4) k
  have hd := pairDisjoint_plus (n := 4) hij
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hρ := projHom_injective (Q := coordinateQuadPlus 4 K) hi.exists_ne_zero
  have hgY : projHom _ g ∈ Y := by
    rw [hYz]
    exact mem_zpowers _
  have hgM : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ∈
      rootLevi (coordinateQuadPlus 4 K) hi.hypPair hj.hypPair := by
    obtain ⟨X, hX, hXg⟩ := hYM hgY
    rw [hρ hXg] at hX
    exact mem_subgroupOf.mp hX
  have hord : orderOf (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) = Nat.card K - 1 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective _ hρ g, ← Nat.card_zpowers, ← hYz, hYcard]
  obtain ⟨f, hf⟩ := exists_card_eq_two_pow (K := K)
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [hf, pow_zero] at hq
    omega
  have hodd : Odd (orderOf (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))) := by
    rw [hord, hf]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.mpr ⟨even_two, hf0⟩) odd_one
  have hgq : (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ^ Nat.card K = g := by
    rw [show Nat.card K = (Nat.card K - 1) + 1 by omega, pow_succ, ← hord, pow_orderOf_eq_one,
      one_mul]
  have hnfix : ¬ ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
      (Pi.single (plusIndexEquiv 4 (.inl i)) 1) = Pi.single (plusIndexEquiv 4 (.inl i)) 1 ∧
      (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
        (Pi.single (plusIndexEquiv 4 (.inl j)) 1) = Pi.single (plusIndexEquiv 4 (.inl j)) 1) := by
    rintro ⟨h1, h2⟩
    obtain ⟨hf1, hf2⟩ := apply_f_of_mem_rootLevi (hi.orth hj hd) hgM h1 h2
    apply hYB
    rw [hYz, zpowers_le]
    exact ⟨g, mem_subgroupOf.mpr ⟨⟨h1, hf1⟩, h2, hf2⟩, rfl⟩
  obtain ⟨α, hα, he1, he2⟩ := rootLevi_exists_alpha hi hj hd hgM hodd hgq hnfix
  obtain ⟨hf1, hf2⟩ := rootLevi_sq_f hi hj hd hgM he1 he2
  have hbound := card_rootRadical_inf_centralizer_le_eigen hi hj hd g hgM hα hf1 hf2
  have hcY : Nat.card (plusRadical K i j ⊓ centralizer (Y : Set (matrixProjectiveDerived
      (coordinateQuadPlus 4 K))) : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) =
      Nat.card ((rootRadical (coordinateQuadPlus 4 K) hi.hypPair hj.hypPair).subgroupOf
        (orthDerived (coordinateQuadPlus 4 K)) ⊓
        centralizer ({g} : Set (orthDerived (coordinateQuadPlus 4 K))) :
          Subgroup (orthDerived (coordinateQuadPlus 4 K))) := by
    have h := map_inf_centralizer_of_injective hρ
      ((rootRadical (coordinateQuadPlus 4 K) hi.hypPair hj.hypPair).subgroupOf
        (orthDerived (coordinateQuadPlus 4 K))) (zpowers g)
    rw [MonoidHom.map_zpowers, ← hYz] at h
    rw [plusRadical, rootRadicalBar, ← h, card_map_of_injective hρ, zpowers_eq_closure,
      centralizer_closure]
  have hXB : pairTorus (K := K) k ≤ stabPairsBar (coordinateQuadPlus 4 K)
      (plusIndexEquiv 4 (.inl i)) (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j))
      (plusIndexEquiv 4 (.inr j)) :=
    pairTorusOf_le_stabPairsBar (pairDisjoint_plus hik) (pairDisjoint_plus hjk)
  have hq0 : 0 < Nat.card K := by omega
  have hcX : Nat.card (plusRadical K i j ⊓ centralizer (pairTorus (K := K) k :
      Set (matrixProjectiveDerived (coordinateQuadPlus 4 K))) :
        Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K))) = Nat.card K ^ 5 := by
    rw [card_rootRadicalBar_inf_centralizer hQ hT hi hj hd hXB]
    have hFX := card_fixSpace_eq hi hj hd
      (B := (pairTorus (K := K) k).comap (projHom (coordinateQuadPlus 4 K)))
      fun g' hg' => mem_stabSub_of_projHom_mem hi hXB hg'
    have hFX' : Nat.card ↥(fixSpace ((pairTorus (K := K) k).comap
        (projHom (coordinateQuadPlus 4 K)))) = Nat.card K ^ (2 * 4 - 2) :=
      card_fixSpace_comap_pairTorusOf hk (by omega)
    rw [hFX'] at hFX
    have h2 : Nat.card ↥(fixSpace ((pairTorus (K := K) k).comap
        (projHom (coordinateQuadPlus 4 K))) ⊓ subW K (plusIndexEquiv 4 (.inl i))
          (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j))) =
        Nat.card K ^ 2 := by
      have h6 : Nat.card K ^ (2 * 4 - 2) = Nat.card K ^ 4 * Nat.card K ^ 2 := by
        rw [← pow_add]
      rw [h6] at hFX
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) hFX).symm
    rw [h2]
    ring
  have hle : Nat.card K ^ 5 ≤ Nat.card ↥(subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (α : K)) *
      Nat.card ↥(subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ((α⁻¹ : Kˣ) : K)) *
      Nat.card K := by
    rw [← hcX, ← hcard, hcY]
    exact hbound
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (α : K))),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ((α⁻¹ : Kˣ) : K))),
    ← pow_add, ← pow_succ] at hle
  have hdim := (Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card K)).mp hle
  have hinf : (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (α : K)) ⊓
      (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ((α⁻¹ : Kˣ) : K)) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, h1⟩, -, h2⟩
    rw [Submodule.mem_bot]
    have h : ((α : K) - ((α⁻¹ : Kˣ) : K)) • x = 0 := by
      rw [sub_smul, ← mem_eigenSub.1 h1, ← mem_eigenSub.1 h2, sub_self]
    exact (smul_eq_zero.mp h).resolve_left
      (sub_ne_zero.mpr (units_ne_inv_of_mul_self_ne_one' hα))
  have hW4 : finrank K (subW K (plusIndexEquiv 4 (.inl i)) (plusIndexEquiv 4 (.inr i))
      (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j))) = 4 := by
    have h := card_fixSpace_eq hi hj hd (B := ⊥) fun g' hg' => by
      rw [Subgroup.mem_bot] at hg'
      subst hg'
      exact ⟨⟨rfl, rfl⟩, rfl, rfl⟩
    rw [fixSpace_bot, top_inf_eq,
      Module.natCard_eq_pow_finrank (K := K) (V := ↥(⊤ : Submodule K (Fin (2 * 4) → K))),
      finrank_top, Module.finrank_fin_fun,
      Module.natCard_eq_pow_finrank (K := K) (V := ↥(subW K (plusIndexEquiv 4 (.inl i))
        (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)))),
      ← pow_add] at h
    have := Nat.pow_right_injective (by omega : 2 ≤ Nat.card K) h
    omega
  have hsup : (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (α : K)) ⊔
      (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ((α⁻¹ : Kˣ) : K)) =
      subW K (plusIndexEquiv 4 (.inl i)) (plusIndexEquiv 4 (.inr i))
        (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) := by
    apply Submodule.eq_of_le_of_finrank_le (sup_le inf_le_left inf_le_left)
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) (α : K))
      (subW K (plusIndexEquiv 4 (.inl i))
      (plusIndexEquiv 4 (.inr i)) (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)) ⊓
        eigenSub (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) ((α⁻¹ : Kˣ) : K))
    rw [hinf, finrank_bot, add_zero] at h
    omega
  have h2 : (α : K) * ((α⁻¹ : Kˣ) : K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNW : ∀ w ∈ subW K (plusIndexEquiv 4 (.inl i)) (plusIndexEquiv 4 (.inr i))
      (plusIndexEquiv 4 (.inl j)) (plusIndexEquiv 4 (.inr j)),
      (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
        ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) w) =
        ((α : K) + ((α⁻¹ : Kˣ) : K)) • (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) w - w := by
    intro w hw
    rw [← hsup] at hw
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
    have e1 := mem_eigenSub.1 hw₁.2
    have e2 := mem_eigenSub.1 hw₂.2
    rw [map_add, map_add, e1, e2, map_smul, map_smul, e1, e2]
    linear_combination (norm := module) (-h2) • (w₁ + w₂)
  have hN : ∀ x, (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K))
      ((g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x) =
      ((α : K) + ((α⁻¹ : Kˣ) : K)) • (g : (Fin (2 * 4) → K) ≃ₗ[K] (Fin (2 * 4) → K)) x - x := by
    intro x
    have hw := hNW _ (piW_mem hi hj hd x)
    rw [eq_coord hd x]
    simp only [map_add, map_smul]
    rw [he1, he2, hf1, hf2, hw]
    module
  exact ⟨α, hα, fun x => ⟨_, _, (eigen_split hα (hN x)).1, (eigen_split hα (hN x)).2.1,
    (eigen_split hα (hN x)).2.2⟩⟩

theorem plusFourRefinedF6OffInput_holds : PlusFourRefinedF6OffInput :=
  plusFourRefinedF6OffInput_of_eigen plusFourGLLeviEigenInput_holds

theorem plusFourRefinedF6Input_holds : PlusFourRefinedF6Input :=
  plusFourRefinedF6Input_of_off plusFourRefinedF6OffInput_holds

end Main

end CFSG.SeitzReduction.OmegaPilot

module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.ClassicalInvolution.Phan.AutSU2
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Intrinsic

public section

namespace CFSG.ClassicalInvolution.Models.SymplecticPairs

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.ClassicalInvolution.WeakCT (torusHom diagTorus2 mem_diagTorus2_iff coe_torusHom)
open CFSG.LieType.Steinberg (diagGL coe_diagGL)
open scoped MatrixGroups commutatorElement

variable {K : Type} [Field K] {n m : ℕ}

section Frame

theorem form_sum_left {ι : Type*} (s : Finset ι) (v : ι → Fin n ⊕ Fin n → K)
    (w : Fin n ⊕ Fin n → K) : form (∑ x ∈ s, v x) w = ∑ x ∈ s, form (v x) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [form_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, form_add_left, ih]

structure IsPlaneFrame (u w : Fin m → Fin m ⊕ Fin m → K) : Prop where
  pair : ∀ k l, form (u k) (w l) = if k = l then 1 else 0
  uu : ∀ k l, form (u k) (u l) = 0
  ww : ∀ k l, form (w k) (w l) = 0

namespace IsPlaneFrame

variable {u w : Fin m → Fin m ⊕ Fin m → K}

theorem linearIndependent (h : IsPlaneFrame u w) : LinearIndependent K (Sum.elim u w) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hwu : ∀ k l, form (w k) (u l) = if k = l then -1 else 0 := fun k l => by
    rw [form_antisymm, h.pair l k]
    by_cases hkl : k = l
    · simp [hkl]
    · simp [hkl, Ne.symm hkl]
  have h1 : ∀ l, c (Sum.inl l) = 0 := fun l => by
    have := congrArg (fun v => form v (w l)) hc
    simp only [form_sum_left, form_smul_left, form_zero_left] at this
    rw [Fintype.sum_sum_type] at this
    simpa [h.pair, h.ww] using this
  have h2 : ∀ l, c (Sum.inr l) = 0 := fun l => by
    have := congrArg (fun v => form v (u l)) hc
    simp only [form_sum_left, form_smul_left, form_zero_left] at this
    rw [Fintype.sum_sum_type] at this
    simpa [h.uu, hwu] using this
  intro x
  rcases x with l | l
  · exact h1 l
  · exact h2 l

theorem exists_sp_apply (h : IsPlaneFrame u w) :
    ∃ g : StatedSp m K, ∀ k, mat m K g *ᵥ Pi.single (Sum.inl k) 1 = u k ∧
      mat m K g *ᵥ Pi.single (Sum.inr k) 1 = w k := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨1, fun k => k.elim0⟩
  have : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, hm⟩⟩
  let b : Module.Basis (Fin m ⊕ Fin m) K (Fin m ⊕ Fin m → K) :=
    basisOfLinearIndependentOfCardEqFinrank h.linearIndependent (by simp [Fintype.card_sum])
  have hb : ∀ x, b x = Sum.elim u w x := fun x => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hgram : ∀ x y, form (b x) (b y) = gram K m x y := by
    intro x y
    rw [hb, hb, gram_apply]
    rcases x with k | k <;> rcases y with l | l <;> simp only [Sum.elim_inl, Sum.elim_inr]
    · simp [h.uu]
    · simp [h.pair, par, eq_comm]
    · rw [form_antisymm, h.pair]
      by_cases hkl : k = l
      · simp [hkl, par, sgn]
      · simp [Ne.symm hkl, par]
    · simp [h.ww]
  refine ⟨ofSymplecticBasis b hgram, fun k => ⟨?_, ?_⟩⟩
  · rw [mat_ofSymplecticBasis_mulVec_single, hb]; rfl
  · rw [mat_ofSymplecticBasis_mulVec_single, hb]; rfl

end IsPlaneFrame

theorem exists_conj_planeGroup {P : Fin m → Submodule K (Fin m ⊕ Fin m → K)}
    (hP : ∀ k, IsHyperbolicPlane (P k))
    (horth : ∀ k l, k ≠ l → ∀ x ∈ P k, ∀ y ∈ P l, form x y = 0) :
    ∃ g : StatedSp m K, ∀ k, P k = Submodule.span K {mat m K g *ᵥ Pi.single (Sum.inl k) 1,
        mat m K g *ᵥ Pi.single (Sum.inr k) 1} ∧
      planeGroup (P k) = (longBlock K m k).range.map (MulAut.conj g).toMonoidHom := by
  choose u w hu hspan using hP
  have hmemu : ∀ k, u k ∈ P k := fun k => by
    rw [hspan k]; exact Submodule.subset_span (by simp)
  have hmemw : ∀ k, w k ∈ P k := fun k => by
    rw [hspan k]; exact Submodule.subset_span (by simp)
  have hframe : IsPlaneFrame u w :=
    { pair := fun k l => by
        by_cases hkl : k = l
        · subst hkl; simp [hu k]
        · simp [hkl, horth k l hkl _ (hmemu k) _ (hmemw l)]
      uu := fun k l => by
        by_cases hkl : k = l
        · subst hkl; exact form_self _
        · exact horth k l hkl _ (hmemu k) _ (hmemu l)
      ww := fun k l => by
        by_cases hkl : k = l
        · subst hkl; exact form_self _
        · exact horth k l hkl _ (hmemw k) _ (hmemw l) }
  obtain ⟨g, hg⟩ := hframe.exists_sp_apply
  refine ⟨g, fun k => ?_⟩
  have hk : P k = Submodule.span K {mat m K g *ᵥ Pi.single (Sum.inl k) 1,
      mat m K g *ᵥ Pi.single (Sum.inr k) 1} := by
    rw [(hg k).1, (hg k).2]
    exact hspan k
  refine ⟨hk, ?_⟩
  rw [hk, planeGroup_span_conj]
  exact congrArg _ (planeGroup_stdPlane k)

end Frame

section Commuting

theorem forall_form_eq_zero_of_commute_planeGroup (h2 : (2 : K) ≠ 0)
    {P Q : Submodule K (Fin n ⊕ Fin n → K)} (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q)
    (hne : planeGroup P ≠ planeGroup Q)
    (hc : ∀ x ∈ planeGroup P, ∀ y ∈ planeGroup Q, x * y = y * x) :
    ∀ u ∈ P, ∀ v ∈ Q, form u v = 0 := by
  obtain ⟨i₁, h₁, hP'⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
  obtain ⟨i₂, h₂', hQ'⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hQ
  have hne' : i₁ ≠ i₂ := by
    rintro rfl
    exact hne (congrArg planeGroup (hP'.symm.trans hQ'))
  have hcomm : Commute i₁ i₂ := (h₁.commute_iff_forall_commute h2 h₂' hne').2 hc
  intro u hu v hv
  rw [← hP'] at hu
  rw [← hQ'] at hv
  exact h₁.form_eq_zero_of_commute h2 h₂' hcomm hne' hu hv

theorem commutator_eq_bot_of_perfect {G : Type*} [Group G] {A B : Subgroup G}
    (hA : A ≤ ⁅A, A⁆) (hc : ⁅A, B⁆ ≤ Subgroup.center G) : ⁅A, B⁆ = ⊥ := by
  have h1 : ⁅⁅A, B⁆, A⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hc.trans (Subgroup.center_le_centralizer _))
  have h2 : ⁅⁅B, A⁆, A⁆ = ⊥ := by
    rw [Subgroup.commutator_comm B A]
    exact h1
  have h3 : ⁅⁅A, A⁆, B⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  exact eq_bot_iff.2 ((Subgroup.commutator_mono hA le_rfl).trans h3.le)

theorem longRootSp2_le_commutator (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) (k : Fin n) :
    longRootSp2 K n k ≤ ⁅longRootSp2 K n k, longRootSp2 K n k⁆ := by
  obtain ⟨a, ha⟩ := hex
  have hperf : (⊤ : Subgroup SL(2, K)) = ⁅(⊤ : Subgroup SL(2, K)), ⊤⁆ :=
    (Matrix.SL2.commutator_eq_top a.ne_zero (sq_ne_one_of_ne_inv_unit ha)).symm
  show (longBlock K n k).range ≤ ⁅(longBlock K n k).range, (longBlock K n k).range⁆
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
  exact Subgroup.map_mono hperf.le

theorem planeGroup_le_commutator (h2 : (2 : K) ≠ 0) (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K))
    {P : Submodule K (Fin n ⊕ Fin n → K)} (hP : IsHyperbolicPlane P) :
    planeGroup P ≤ ⁅planeGroup P, planeGroup P⁆ := by
  obtain ⟨i, hi, -⟩ := exists_isLongRootSp2_of_isHyperbolicPlane h2 hP
  obtain ⟨k, g, hL, -⟩ := hi
  rw [hL, ← Subgroup.map_commutator]
  exact Subgroup.map_mono (longRootSp2_le_commutator hex k)

theorem forall_form_eq_zero_of_commutator_mem_center (h2 : (2 : K) ≠ 0)
    (hex : ∃ a : Kˣ, (a : K) ≠ ((a⁻¹ : Kˣ) : K)) {P Q : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : IsHyperbolicPlane P) (hQ : IsHyperbolicPlane Q) (hne : planeGroup P ≠ planeGroup Q)
    (hc : ⁅planeGroup P, planeGroup Q⁆ ≤ Subgroup.center (StatedSp n K)) :
    ∀ u ∈ P, ∀ v ∈ Q, form u v = 0 := by
  refine forall_form_eq_zero_of_commute_planeGroup h2 hP hQ hne fun x hx y hy => ?_
  have h0 := commutator_eq_bot_of_perfect (planeGroup_le_commutator h2 hex hP) hc
  have : ⁅x, y⁆ = 1 := by
    have := Subgroup.commutator_mem_commutator hx hy
    rw [h0] at this
    exact this
  rw [commutatorElement_def] at this
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [this, one_mul]

end Commuting

section Single

theorem exists_sp_apply_eq_at (k : Fin n) (u w : Fin n ⊕ Fin n → K) (h : form u w = 1) :
    ∃ g : StatedSp n K, mat n K g *ᵥ Pi.single (Sum.inl k) 1 = u ∧
      mat n K g *ᵥ Pi.single (Sum.inr k) 1 = w := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := k.2; omega⟩
  obtain ⟨g₁, h1u, h1w⟩ := exists_sp_apply_eq u w h
  obtain ⟨g₂, h2u, h2w⟩ := exists_sp_apply_eq
    (Pi.single (Sum.inl k) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K) (Pi.single (Sum.inr k) 1)
    (by rw [form_single_right]; simp)
  refine ⟨g₁ * g₂⁻¹, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 h2u, h1u]
  · rw [map_mul, ← Matrix.mulVec_mulVec, ← (mulVec_eq_iff g₂ _ _).1 h2w, h1w]

theorem exists_planeGroup_eq_conj_longBlock {P : Submodule K (Fin n ⊕ Fin n → K)}
    (hP : IsHyperbolicPlane P) (k : Fin n) :
    ∃ g : StatedSp n K, planeGroup P = (longBlock K n k).range.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u, w, huw, rfl⟩ := hP
  obtain ⟨g, hu, hw⟩ := exists_sp_apply_eq_at k u w huw
  refine ⟨g, ?_⟩
  rw [← hu, ← hw, planeGroup_span_conj]
  exact congrArg _ (planeGroup_stdPlane k)

theorem exists_planeGroup_eq_map_conj_longBlock (g : StatedSp n K) (k : Fin n) :
    ∃ P : Submodule K (Fin n ⊕ Fin n → K), IsHyperbolicPlane P ∧
      (longBlock K n k).range.map (MulAut.conj g).toMonoidHom = planeGroup P := by
  refine ⟨Submodule.span K {mat n K g *ᵥ Pi.single (Sum.inl k) 1,
    mat n K g *ᵥ Pi.single (Sum.inr k) 1}, ⟨_, _, ?_, rfl⟩, ?_⟩
  · rw [form_mulVec]
    exact form_single_inl_inr k
  · rw [planeGroup_span_conj]
    exact congrArg _ (planeGroup_stdPlane k).symm

theorem exists_conj_longBlock_iff (k : Fin n) (R : Subgroup (StatedSp n K)) :
    (∃ g : StatedSp n K, R = (longBlock K n k).range.map (MulAut.conj g).toMonoidHom) ↔
      ∃ P, IsHyperbolicPlane P ∧ R = planeGroup P := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨P, hP, h⟩ := exists_planeGroup_eq_map_conj_longBlock g k
    exact ⟨P, hP, h⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨g, hg⟩ := exists_planeGroup_eq_conj_longBlock hP k
    exact ⟨g, hg⟩

end Single

section Center

theorem exists_scalar_of_mem_center {g : StatedSp n K} (hg : g ∈ Subgroup.center (StatedSp n K)) :
    ∃ c : Kˣ, (g : GL (Fin n ⊕ Fin n) K) = Matrix.GeneralLinearGroup.scalar (Fin n ⊕ Fin n) c := by
  have hsp := CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := n) (K := K)
  have hmem : (⟨(g : GL (Fin n ⊕ Fin n) K), by rw [← hsp]; exact g.2⟩ :
      TauCeti.GLSymplectic (Fin n) K) ∈ Subgroup.center (TauCeti.GLSymplectic (Fin n) K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have h' : (h : GL (Fin n ⊕ Fin n) K) ∈ StatedSp n K := by rw [hsp]; exact h.2
    have := Subgroup.mem_center_iff.1 hg ⟨h, h'⟩
    apply Subtype.ext
    have h3 := congrArg Subtype.val this
    simpa using h3
  rw [CFSG.ClassicalGroups.Symplectic.center_GLSymplectic_eq, Subgroup.mem_subgroupOf] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

theorem eq_one_of_mem_center_of_mem_suppGroup {S : Set (Fin n ⊕ Fin n)} {g : StatedSp n K}
    (hg : g ∈ Subgroup.center (StatedSp n K)) (hS : g ∈ suppGroup S) {t : Fin n ⊕ Fin n}
    (ht : t ∉ S) : g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hg
  have h1 : mat n K g t t = 1 := by
    rw [hS t t (fun h => ht h.1)]
    simp
  have h2 : ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) t t =
      (c : K) := by
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
    simp
  have hc1 : (c : K) = 1 := h2.symm.trans h1
  apply Subtype.ext
  rw [hc, show c = 1 from Units.ext hc1, map_one]
  rfl

theorem mul_self_eq_one_of_mem_center (hn : 1 ≤ n) {g : StatedSp n K}
    (hg : g ∈ Subgroup.center (StatedSp n K)) : g * g = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_center hg
  have hmat : mat n K g = Matrix.diagonal (fun _ => (c : K)) := by
    change ((g : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = _
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have h1 := congrFun (congrFun (mat_transpose_mul_gram_mul g) (Sum.inl ⟨0, hn⟩))
    (Sum.inr ⟨0, hn⟩)
  rw [hmat, Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have hg1 : (gram K n) (Sum.inl ⟨0, hn⟩) (Sum.inr ⟨0, hn⟩) = 1 := by
    rw [gram_apply]
    simp [par, sgn]
  rw [hg1] at h1
  have hcc : (c : K) * (c : K) = 1 := by linear_combination h1
  apply mat_injective
  rw [map_mul, hmat, Matrix.diagonal_mul_diagonal, map_one]
  ext a b
  simp [Matrix.diagonal_apply, Matrix.one_apply, hcc]

theorem injOn_suppGroup_of_ker_le_center {Y : Type*} [Group Y] (φ : StatedSp n K →* Y)
    (hφ : φ.ker ≤ Subgroup.center (StatedSp n K)) {S : Set (Fin n ⊕ Fin n)}
    {t : Fin n ⊕ Fin n} (ht : t ∉ S) :
    ∀ x ∈ suppGroup S, φ x = 1 → x = 1 :=
  fun _ hx h => eq_one_of_mem_center_of_mem_suppGroup (hφ h) hx ht

end Center

section Torus

theorem toGL_injective' :
    Function.Injective (Matrix.SpecialLinearGroup.toGL : SL(2, K) → GL (Fin 2) K) :=
  fun _ _ h => Subtype.ext (congrArg Units.val h)

theorem toGL_map_torusHom (ψ : K ≃+* K) (s : Kˣ) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (ψ : K →+* K) (torusHom K s)) =
      Matrix.SpecialLinearGroup.toGL (torusHom K (Units.map (ψ : K →* K) s)) := by
  refine Units.ext ?_
  ext x y
  fin_cases x <;> fin_cases y <;> simp [coe_torusHom, Matrix.SpecialLinearGroup.map_apply_coe]

theorem diagGL_comm_torusHom (d : Fin 2 → Kˣ) (s : Kˣ) :
    diagGL d * Matrix.SpecialLinearGroup.toGL (torusHom K s) =
      Matrix.SpecialLinearGroup.toGL (torusHom K s) * diagGL d := by
  refine Units.ext ?_
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [coe_diagGL, coe_torusHom, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem exists_conj_diagTorus [Finite K] (α : MulAut SL(2, K)) :
    ∃ c : SL(2, K), (diagTorus2 K).map α.toMonoidHom =
      (diagTorus2 K).map (MulAut.conj c).toMonoidHom := by
  obtain ⟨G, ψ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  set δ : Kˣ := Matrix.GeneralLinearGroup.det G with hδ
  set c₀ : GL (Fin 2) K := G * diagGL ![δ⁻¹, 1] with hc₀
  have hdet : ((c₀ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    have hGd : ((G : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
      simpa using (Matrix.GeneralLinearGroup.det G).ne_zero
    rw [hc₀, Units.val_mul, Matrix.det_mul, coe_diagGL, Matrix.det_diagonal]
    simp [hδ, Fin.prod_univ_two, hGd]
  set c : SL(2, K) := ⟨(c₀ : Matrix (Fin 2) (Fin 2) K), hdet⟩ with hc
  have hcGL : Matrix.SpecialLinearGroup.toGL c = c₀ := Units.ext rfl
  have key : ∀ s : Kˣ, α (torusHom K s) =
      c * torusHom K (Units.map (ψ : K →* K) s) * c⁻¹ := by
    intro s
    apply toGL_injective'
    have hcomm := diagGL_comm_torusHom (K := K) ![δ⁻¹, 1] (Units.map (ψ : K →* K) s)
    have e : G * diagGL ![δ⁻¹, 1] * Matrix.SpecialLinearGroup.toGL
        (torusHom K (Units.map (ψ : K →* K) s)) =
        G * Matrix.SpecialLinearGroup.toGL (torusHom K (Units.map (ψ : K →* K) s)) *
          diagGL ![δ⁻¹, 1] := by
      rw [mul_assoc, hcomm, ← mul_assoc]
    rw [hG, toGL_map_torusHom, map_mul, map_mul, map_inv, hcGL, hc₀, e]
    group
  refine ⟨c, ?_⟩
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := mem_diagTorus2_iff.1 hy
    exact ⟨torusHom K (Units.map (ψ : K →* K) s), ⟨_, rfl⟩, (key s).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨s, rfl⟩ := mem_diagTorus2_iff.1 hy
    refine ⟨torusHom K (Units.map (ψ.symm : K →* K) s), ⟨_, rfl⟩, ?_⟩
    have hψ : Units.map (ψ : K →* K) (Units.map (ψ.symm : K →* K) s) = s :=
      Units.ext (by simp)
    rw [key, hψ]

end Torus

end CFSG.ClassicalInvolution.Models.SymplecticPairs

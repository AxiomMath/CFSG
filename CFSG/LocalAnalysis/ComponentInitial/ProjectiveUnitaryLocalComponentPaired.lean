module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.LinearPairedCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Module Matrix CFSG.ComponentClassification

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
  {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E}

theorem exists_sesq_eq_of_pairing [FiniteDimensional E V] {W₁ W₂ : Submodule E V}
    (hpair : ∀ w ∈ W₂, (∀ v ∈ W₁, B w v = 0) → w = 0) (hdim : finrank E W₂ = finrank E W₁)
    (φ : W₁ →ₗ[E] E) : ∃ w ∈ W₂, ∀ v : W₁, B w v = φ v := by
  have := h.finite
  have : Finite W₂ := Module.finite_of_finite E
  have : Finite (W₁ →ₗ[E] E) := Module.finite_of_finite E
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : W₂ → (W₁ →ₗ[E] E), Ψ = fun w : W₂ => (B (w : V)).comp W₁.subtype :=
    ⟨_, rfl⟩
  have hΨapp : ∀ (w : W₂) (v : W₁), Ψ w v = B (w : V) (v : V) := fun w v => by rw [hΨ]; rfl
  have hinj : Function.Injective Ψ := by
    intro w w' hww'
    have h1 : ∀ v ∈ W₁, B ((w : V) - w') v = 0 := fun v hv => by
      have := congrArg (fun φ : W₁ →ₗ[E] E => φ ⟨v, hv⟩) hww'
      simp only [hΨapp] at this
      rw [map_sub, LinearMap.sub_apply, this, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (hpair _ (sub_mem w.2 w'.2) h1))
  have hcard : Nat.card W₂ = Nat.card (W₁ →ₗ[E] E) := by
    rw [Module.natCard_eq_pow_finrank (K := E) (V := W₂),
      Module.natCard_eq_pow_finrank (K := E) (V := W₁ →ₗ[E] E), Subspace.dual_finrank_eq,
      hdim]
  obtain ⟨w, hw⟩ := ((Nat.bijective_iff_injective_and_card Ψ).mpr ⟨hinj, hcard⟩).2 φ
  exact ⟨w, w.2, fun v => by rw [← hΨapp, hw]⟩

section Frame

variable {m : ℕ} {b d : Fin m → V}

theorem sesq_left_sum (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (c : Fin m ⊕ Fin m → E) (i : Fin m) :
    B (b i) (∑ a, c a • Sum.elim b d a) = c (Sum.inr i) := by
  simp [map_sum, Fintype.sum_sum_type, hbb, hbd]

theorem sesq_right_sum (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (c : Fin m ⊕ Fin m → E) (i : Fin m) :
    B (d i) (∑ a, c a • Sum.elim b d a) = c (Sum.inl i) := by
  simp [map_sum, Fintype.sum_sum_type, hdd, hdb]

theorem linearIndependent_sumElim (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) :
    LinearIndependent E (Sum.elim b d) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  rcases a with i | i
  · rw [← sesq_right_sum hdd hdb c i, hc, map_zero]
  · rw [← sesq_left_sum hbb hbd c i, hc, map_zero]

variable {bV : Basis (Fin m ⊕ Fin m) E V}

theorem repr_inl (hdd : ∀ i j, B (d i) (d j) = 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inl i) = B (d i) v := by
  have h1 := sesq_right_sum hdd hdb (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  exact h1.symm

theorem repr_inr (hbb : ∀ i j, B (b i) (b j) = 0)
    (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d) (v : V)
    (i : Fin m) : bV.repr v (Sum.inr i) = B (b i) v := by
  have h1 := sesq_left_sum hbb hbd (bV.repr v) i
  rw [← hbV, bV.sum_repr] at h1
  exact h1.symm

theorem pairedHermForm_eq_sesq (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d)
    (u v : Fin m ⊕ Fin m → E) :
    pairedHermForm h.bar m u v = B (bV.equivFun.symm u) (bV.equivFun.symm v) := by
  have key : ∀ (x : Fin m ⊕ Fin m → E) (w : V), B (∑ a, x a • Sum.elim b d a) w =
      ∑ i, (h.bar (x (Sum.inl i)) * B (b i) w + h.bar (x (Sum.inr i)) * B (d i) w) := by
    intro x w
    rw [map_sum, LinearMap.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.smul_apply,
      Sum.elim_inl, Sum.elim_inr, smul_eq_mul, smul_eq_mul]
  rw [pairedHermForm_eq, Basis.equivFun_symm_apply, Basis.equivFun_symm_apply, hbV, key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sesq_left_sum hbb hbd, sesq_right_sum hdd hdb]

@[expose] noncomputable def frameMatrix (bV : Basis (Fin m ⊕ Fin m) E V) :
    LinearMap.GeneralLinearGroup E V ≃* GL (Fin m ⊕ Fin m) E :=
  Units.mapEquiv (LinearMap.toMatrixAlgEquiv bV).toMulEquiv

theorem frameMatrix_coe (g : LinearMap.GeneralLinearGroup E V) :
    ((frameMatrix bV g : GL (Fin m ⊕ Fin m) E) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E) =
      LinearMap.toMatrix bV bV (g : Module.End E V) :=
  rfl

theorem toMatrix_mulVec_eq (g : Module.End E V) (u : Fin m ⊕ Fin m → E) :
    LinearMap.toMatrix bV bV g *ᵥ u = bV.equivFun (g (bV.equivFun.symm u)) := by
  have h1 : ⇑(bV.repr (bV.equivFun.symm u)) = u := by
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [Basis.equivFun_apply, ← LinearMap.toMatrix_mulVec_repr bV bV, h1]

theorem toMatrix_mem_pairedUnitaryGroup (hbb : ∀ i j, B (b i) (b j) = 0)
    (hdd : ∀ i j, B (d i) (d j) = 0) (hbd : ∀ i j, B (b i) (d j) = if i = j then 1 else 0)
    (hdb : ∀ i j, B (d i) (b j) = if i = j then 1 else 0) (hbV : ⇑bV = Sum.elim b d)
    {g : LinearMap.GeneralLinearGroup E V} (hg : g ∈ sesqUnitaryGroup B) :
    frameMatrix bV g ∈ pairedUnitaryGroup h.bar m := by
  rw [mem_pairedUnitaryGroup]
  intro u v
  rw [frameMatrix_coe, toMatrix_mulVec_eq, toMatrix_mulVec_eq,
    pairedHermForm_eq_sesq hbb hdd hbd hdb hbV, pairedHermForm_eq_sesq hbb hdd hbd hdb hbV,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, hg]

end Frame

theorem map_transpose_mul_eq_one_of_fromBlocks {m : ℕ} {σ : E →+* E}
    {X Y : Matrix (Fin m) (Fin m) E}
    (hXY : ∀ u v, pairedHermForm σ m (fromBlocks X 0 0 Y *ᵥ u) (fromBlocks X 0 0 Y *ᵥ v) =
      pairedHermForm σ m u v) :
    (X.map σ)ᵀ * Y = 1 := by
  ext i j
  have h1 := hXY (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1)
  simp [pairedHermForm_eq, Pi.single_apply] at h1
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  rw [h1, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

theorem paired_case (hp : p ≠ 2) [FiniteDimensional E V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {T : sesqUnitaryGroup B} {l : E} (hl0 : l ≠ 0)
    (hAA : unitaryOp T * unitaryOp T = (l ^ 2) • 1) (hN : h.norm l = -1)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    {R : Subgroup (sesqUnitaryGroup B)}
    (hR : R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
      Subgroup (sesqUnitaryGroup B)) : Set (sesqUnitaryGroup B)))
    (hRp : ⁅R, R⁆ = R) : R = ⊥ := by
  have := h.finite
  obtain ⟨hisoP, hisoM, hdimeq, h2m, -, hpairMP, e, he, -, -⟩ :=
    exists_paired_centralizer_equiv hp hB hBl hl0 hAA hN
  obtain ⟨m, hm⟩ : ∃ m, finrank E (eigenPlus l (unitaryOp T)) = m := ⟨_, rfl⟩
  obtain ⟨b⟩ : Nonempty (Basis (Fin m) E (eigenPlus l (unitaryOp T))) :=
    ⟨Module.finBasisOfFinrankEq E _ hm⟩
  obtain ⟨F, hF⟩ : ∃ F : Subgroup.centralizer {T} ≃* GL (Fin m) E,
      F = e.trans (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv) := ⟨_, rfl⟩
  have hFapp : ∀ (x : Subgroup.centralizer {T}) (i j : Fin m),
      ((F x : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) i j =
        b.repr (((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T))) (b j)) i := by
    intro x i j
    rw [hF]
    exact LinearMap.toMatrixAlgEquiv_apply b _ i j
  have hL' : CFSG.IsComponent (L.map F.toMonoidHom) := isComponent_map_of_isComponent F hL
  have : Group.IsPerfect (L.map F.toMonoidHom) := hL'.1.1
  have : Nontrivial (L.map F.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  obtain ⟨hm2, hSL⟩ : 2 ≤ m ∧
      L.map F.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange m E := by
    by_cases hs : m = 0 ∨ m = 1 ∨ m = 2 ∧ (Nat.card E = 2 ∨ Nat.card E = 3)
    · exfalso
      have : Group.IsSolvable (GL (Fin m) E) := by
        rcases hs with rfl | hs
        · infer_instance
        · exact CatalogueBGeneralLinear.generalLinear_small_solvable m E hs
      exact Group.IsPerfect.not_isSolvable (L.map F.toMonoidHom) inferInstance
    · obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters m E (by omega)
        fun h' => hs (Or.inr h')
      exact ⟨hm2, CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m E hm2 h22 h23
        _ hL'.2⟩
  have hpair : ∀ w ∈ eigenMinus l (unitaryOp T),
      (∀ v ∈ eigenPlus l (unitaryOp T), B w v = 0) → w = 0 := fun w hw h0 =>
    hpairMP w hw fun v hv => by rw [← hB.eq w v, h0 v hv, map_zero]
  have hex : ∀ j : Fin m, ∃ w ∈ eigenMinus l (unitaryOp T),
      ∀ v : eigenPlus l (unitaryOp T), B w v = b.coord j v := fun j =>
    exists_sesq_eq_of_pairing hpair hdimeq.symm (b.coord j)
  choose d hdM hdB using hex
  have hbb : ∀ i j, B (b i : V) (b j : V) = 0 := fun i j => hisoP _ (b i).2 _ (b j).2
  have hdd : ∀ i j, B (d i) (d j) = 0 := fun i j => hisoM _ (hdM i) _ (hdM j)
  have hdb : ∀ i j, B (d i) (b j : V) = if i = j then 1 else 0 := fun i j => by
    rw [hdB i (b j), Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
    exact if_congr eq_comm rfl rfl
  have hbd : ∀ i j, B (b i : V) (d j) = if i = j then 1 else 0 := fun i j => by
    rw [← hB.eq, hdb j i]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  obtain ⟨bV, hbV⟩ : ∃ bV : Basis (Fin m ⊕ Fin m) E V,
      ⇑bV = Sum.elim (fun i => (b i : V)) d :=
    ⟨basisOfLinearIndependentOfCardEqFinrank' _
      (linearIndependent_sumElim (b := fun i => (b i : V)) hbb hdd hbd hdb)
      (by rw [Fintype.card_sum, Fintype.card_fin, ← h2m, hm]; ring),
      coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _⟩
  have hψU : ∀ g : sesqUnitaryGroup B,
      frameMatrix bV (g : LinearMap.GeneralLinearGroup E V) ∈ pairedUnitaryGroup h.bar m :=
    fun g => toMatrix_mem_pairedUnitaryGroup (b := fun i => (b i : V)) hbb hdd hbd hdb hbV g.2
  have hcover : ∀ M : SpecialLinearGroup (Fin m) E, ∃ x ∈ L,
      frameMatrix bV ((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) =
        pairedSLHom h.bar m M := by
    intro M
    have hM : SpecialLinearGroup.toGL M ∈ L.map F.toMonoidHom := by
      rw [hSL]
      exact ⟨M, rfl⟩
    obtain ⟨x, hx, hxM⟩ := hM
    have hxM' : F x = SpecialLinearGroup.toGL M := hxM
    refine ⟨x, hx, ?_⟩
    obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E,
        P = ((frameMatrix bV ((x : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) :
          GL (Fin m ⊕ Fin m) E) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) E) := ⟨_, rfl⟩
    have hPe : ∀ a c, P a c = bV.repr (unitaryOp (x : sesqUnitaryGroup B) (bV c)) a :=
      fun a c => by rw [hP, frameMatrix_coe, LinearMap.toMatrix_apply]
    have h11 : P.toBlocks₁₁ = (M : Matrix (Fin m) (Fin m) E) := by
      ext i j
      change P (Sum.inl i) (Sum.inl j) = _
      rw [hPe, hbV, Sum.elim_inl, repr_inl (b := fun i => (b i : V)) hdd hdb hbV]
      have h2 : ((((e x : LinearMap.GeneralLinearGroup E (eigenPlus l (unitaryOp T))) :
          Module.End E (eigenPlus l (unitaryOp T))) (b j) : eigenPlus l (unitaryOp T)) : V) =
          unitaryOp (x : sesqUnitaryGroup B) (b j) :=
        LinearMap.congr_fun (he x) (b j)
      rw [← h2, hdB, Basis.coord_apply, ← hFapp, hxM']
      rfl
    have h12 : P.toBlocks₁₂ = 0 := by
      ext i j
      change P (Sum.inl i) (Sum.inr j) = 0
      rw [hPe, hbV, Sum.elim_inr, repr_inl (b := fun i => (b i : V)) hdd hdb hbV]
      exact hisoM _ (hdM i) _ (mapsTo_ker_add_one_of_mem_centralizer l x.2 (hdM j))
    have h21 : P.toBlocks₂₁ = 0 := by
      ext i j
      change P (Sum.inr i) (Sum.inl j) = 0
      rw [hPe, hbV, Sum.elim_inl, repr_inr (b := fun i => (b i : V)) hbb hbd hbV]
      exact hisoP _ (b i).2 _ (mapsTo_ker_sub_one_of_mem_centralizer l x.2 (b j).2)
    have hblocks : fromBlocks (M : Matrix (Fin m) (Fin m) E) 0 0 P.toBlocks₂₂ = P := by
      calc fromBlocks (M : Matrix (Fin m) (Fin m) E) 0 0 P.toBlocks₂₂ =
          fromBlocks P.toBlocks₁₁ P.toBlocks₁₂ P.toBlocks₂₁ P.toBlocks₂₂ := by
            rw [h11, h12, h21]
        _ = P := fromBlocks_toBlocks P
    have hPU : ∀ u v, pairedHermForm h.bar m
        (fromBlocks (M : Matrix (Fin m) (Fin m) E) 0 0 P.toBlocks₂₂ *ᵥ u)
        (fromBlocks (M : Matrix (Fin m) (Fin m) E) 0 0 P.toBlocks₂₂ *ᵥ v) =
          pairedHermForm h.bar m u v := by
      rw [hblocks, hP]
      exact (mem_pairedUnitaryGroup h.bar m).mp (hψU x)
    have hSLU := pairedSLHom_range_le_pairedUnitaryGroup (σ := h.bar) (m := m) h.bar_bar
      ⟨M, rfl⟩
    rw [mem_pairedUnitaryGroup, pairedSLHom_coe] at hSLU
    have h22 : P.toBlocks₂₂ =
        (((SpecialLinearGroup.map h.bar M)⁻¹ : SpecialLinearGroup (Fin m) E) :
          Matrix (Fin m) (Fin m) E)ᵀ :=
      (Matrix.inv_eq_right_inv (map_transpose_mul_eq_one_of_fromBlocks hPU)).symm.trans
        (Matrix.inv_eq_right_inv (map_transpose_mul_eq_one_of_fromBlocks hSLU))
    apply Units.ext
    rw [← hP, ← hblocks, h22, pairedSLHom_coe]
  obtain ⟨-, -, hab⟩ := paired_unitary_special_linear_centralizer_abelian h hm2
  have hRcent : ∀ r ∈ R, (⟨frameMatrix bV (r : LinearMap.GeneralLinearGroup E V), hψU r⟩ :
      pairedUnitaryGroup h.bar m) ∈ Subgroup.centralizer
        (((pairedSLHom h.bar m).range.subgroupOf (pairedUnitaryGroup h.bar m)) :
          Set (pairedUnitaryGroup h.bar m)) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨y, hyU⟩ hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    obtain ⟨M, rfl⟩ := hy
    obtain ⟨x, hx, hxM⟩ := hcover M
    have hxr := Subgroup.mem_centralizer_iff.mp (hR hr) _ (Subgroup.mem_map_of_mem _ hx)
    apply Subtype.ext
    change pairedSLHom h.bar m M * frameMatrix bV (r : LinearMap.GeneralLinearGroup E V) =
      frameMatrix bV (r : LinearMap.GeneralLinearGroup E V) * pairedSLHom h.bar m M
    rw [← hxM, ← map_mul, ← map_mul]
    exact congrArg (fun z : sesqUnitaryGroup B => frameMatrix bV
      (z : LinearMap.GeneralLinearGroup E V)) hxr
  have hRcomm : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁ := by
    intro r₁ h₁ r₂ h₂
    have h3 := hab.is_comm.comm ⟨_, hRcent r₁ h₁⟩ ⟨_, hRcent r₂ h₂⟩
    have h4 : frameMatrix bV ((r₁ * r₂ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) =
        frameMatrix bV ((r₂ * r₁ : sesqUnitaryGroup B) : LinearMap.GeneralLinearGroup E V) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (congrArg Subtype.val h3)
    exact Subtype.ext ((frameMatrix bV).injective h4)
  have hRle : R ≤ Subgroup.centralizer (R : Set (sesqUnitaryGroup B)) := fun r hr =>
    Subgroup.mem_centralizer_iff.mpr fun s hs => hRcomm s hs r hr
  rw [← hRp, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hRle]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

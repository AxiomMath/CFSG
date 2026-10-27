module

public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameCyclic
public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.LocalAnalysis.StandardType.GGOppositeRadicalOmegaPlusModel

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Models.OrthogonalPairs
  QuadraticMap Matrix CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalInvolution.ModelFacts.OrthAut CFSG.LieType.Universal.Spin
  CFSG.LieType.SeitzGeneration OrthBlk CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)
open scoped MatrixGroups

section Local

open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem odd_mem_mulSub_charTwo
    {T : Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K}
    (hT : T ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) {N : ℕ} (hN : Odd N)
    (hTN : T ^ N = 1) :
    T ∈ mulSub (leftGrp (K := K)) rightGrp commute_leftGrp_rightGrp := by
  classical
  let g : DeterminantIsometries K :=
    ⟨T, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun X => by
      have h := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hT X
      rw [determinantForm_apply, determinantForm_apply, ← detQ_apply, ← detQ_apply]
      exact h⟩
  have hgN : g ^ N = 1 := Subtype.ext (by simpa using hTN)
  have hS : (specialImage K).Normal := inferInstance
  have htt : ∀ x : DeterminantIsometries K, tau * (tau * x) = x := fun x => by
    rw [← mul_assoc, tau_mul_tau, one_mul]
  have hgS : g ∈ specialImage K := by
    rcases CFSG.Quasithin.G11.P3Ortho.Om4.mem_specialImage_or_mul_tau g with h | h
    · exact h
    · have hg2 : g * g ∈ specialImage K := by
        have e : g * g = (g * tau) * (tau * (g * tau) * tau⁻¹) := by
          rw [tau_inv]
          simp only [mul_assoc, tau_mul_tau, mul_one, htt]
        rw [e]
        exact (specialImage K).mul_mem h (hS.conj_mem _ h tau)
      obtain ⟨k, hk⟩ := hN
      have : g = (g * g) ^ (k + 1) := by
        rw [← _root_.sq, ← pow_mul]
        calc g = g * g ^ (2 * k + 1) := by rw [← hk, hgN, mul_one]
          _ = g ^ (2 * (k + 1)) := by rw [← pow_succ']; exact congrArg _ (by omega)
      rw [this]
      exact Subgroup.pow_mem _ hg2 _
  obtain ⟨z, hz⟩ := hgS
  refine ⟨lmulEquiv z.1, lmulEquiv_mem_leftGrp _, rmulEquiv z.2⁻¹, rmulEquiv_mem_rightGrp _, ?_⟩
  refine LinearEquiv.ext fun X => ?_
  have h1 : T X = (z.1 : Matrix (Fin 2) (Fin 2) K) * X *
      ((z.2⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
    rw [← specialRho_apply]
    exact (congrArg (fun y : DeterminantIsometries K => y.val X) hz).symm
  show T X = (z.1 : Matrix (Fin 2) (Fin 2) K) *
    (X * ((z.2⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K))
  rw [h1, Matrix.mul_assoc]

end Local

section Transport

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

section Basic

variable (F : Frame Q)

theorem incl_transport_of_span {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (Y : Matrix (Fin 2) (Fin 2) K) : F.incl (F.transport g Y) = g (F.incl Y) :=
  ((Frame.mem_span_iff F).mp (hs _ ⟨Y, rfl⟩)).symm

theorem transport_mul_of_span {g h : V ≃ₗ[K] V} (hh : ∀ x ∈ F.span, h x ∈ F.span) :
    F.transport (g * h) = F.transport g * F.transport h := by
  refine LinearMap.ext fun Y => ?_
  rw [Module.End.mul_apply, F.transport_apply g (F.transport h Y), incl_transport_of_span F hh Y]
  rfl

@[expose] noncomputable def transportEquivOf {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) :
    Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K :=
  LinearEquiv.ofLinearMap (F.transport g) (F.transport g⁻¹)
    (by
      rw [← Module.End.mul_eq_comp, ← transport_mul_of_span F hs', mul_inv_cancel,
        Frame.transport_one]
      rfl)
    (by
      rw [← Module.End.mul_eq_comp, ← transport_mul_of_span F hs, inv_mul_cancel,
        Frame.transport_one]
      rfl)

theorem transportEquivOf_apply {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) (Y : Matrix (Fin 2) (Fin 2) K) :
    transportEquivOf F hs hs' Y = F.transport g Y :=
  rfl

theorem transportEquivOf_mem_orthogonalGroup {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) :
    transportEquivOf F hs hs' ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun Y => ?_
  rw [detQ_apply, detQ_apply, ← F.Q_incl, ← F.Q_incl, transportEquivOf_apply,
    incl_transport_of_span F hs, map_of_mem hgO]

theorem transportEquivOf_pow {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) (k : ℕ) (Y : Matrix (Fin 2) (Fin 2) K) :
    (transportEquivOf F hs hs' ^ k) Y = F.transport (g ^ k) Y := by
  induction k generalizing Y with
  | zero =>
    rw [pow_zero, pow_zero, Frame.transport_one]
    rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', LinearEquiv.mul_apply, ih, transportEquivOf_apply,
      F.transport_apply g, incl_transport_of_span F (OrthBlk.pow_apply_mem hs k) Y,
      F.transport_apply (g * g ^ k)]
    rfl

theorem embGrp_transportEquivOf_apply_span {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) {x : V} (hx : x ∈ F.span) :
    F.embGrp (transportEquivOf F hs hs') x = g x := by
  have hx' : x = F.incl (F.coords x) := (Frame.mem_span_iff F).mp hx
  rw [Frame.embGrp_apply, Frame.embLin_apply_eq, ← hx', sub_self, add_zero]
  change F.incl (F.transport g (F.coords x)) = g x
  rw [incl_transport_of_span F hs, ← hx']

theorem embGrp_transportEquivOf_apply_perp {g : V ≃ₗ[K] V} (hs : ∀ x ∈ F.span, g x ∈ F.span)
    (hs' : ∀ x ∈ F.span, g⁻¹ x ∈ F.span) {x : V} (hx : x ∈ F.perp) :
    F.embGrp (transportEquivOf F hs hs') x = x := by
  have h0 : F.coords x = 0 := (Frame.mem_perp_iff F).mp hx
  rw [Frame.embGrp_apply, Frame.embLin_apply_eq, h0, map_zero, map_zero, sub_zero, zero_add]

end Basic

end Transport

section Block

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_blockElem_charTwo [Finite K] [CharP K 2] [FiniteDimensional K V] (F : Frame Q)
    {N : ℕ} (hN : Odd N) {f : V ≃ₗ[K] V} (hfO : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfN : f ^ N = 1) (hfs : ∀ x ∈ F.span, f x ∈ F.span) :
    ∃ T : V ≃ₗ[K] V, T ∈ F.La.range ⊔ F.swap.La.range ∧ (∀ x ∈ F.span, T x = f x) ∧
      ∀ x ∈ F.perp, T x = x := by
  classical
  have hfs' : ∀ x ∈ F.span, f⁻¹ x ∈ F.span := symm_mem_of_mem f F.span hfs
  set σ := transportEquivOf F hfs hfs' with hσ
  have hσO : σ ∈ TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K)) :=
    transportEquivOf_mem_orthogonalGroup F hfO hfs hfs'
  have hσN : σ ^ N = 1 := by
    refine LinearEquiv.ext fun Y => ?_
    rw [transportEquivOf_pow F hfs hfs' N Y, hfN, Frame.transport_one]
    rfl
  obtain ⟨l, hl, r, hr, hlr⟩ := mem_mulSub.mp (odd_mem_mulSub_charTwo hσO hN hσN)
  refine ⟨F.embGrp σ, ?_, fun x hx => embGrp_transportEquivOf_apply_span F hfs hfs' hx,
    fun x hx => embGrp_transportEquivOf_apply_perp F hfs hfs' hx⟩
  rw [hlr, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [Frame.La_range_eq_map]
    exact ⟨l, hl, rfl⟩
  · rw [Frame.swap_La_range_eq_map]
    exact ⟨r, hr, rfl⟩

theorem mem_iSup_of_blocks [FiniteDimensional K V] {m : ℕ} (Fr : Fin m → Frame Q)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ (Fr i).span, ∀ y ∈ (Fr j).span, polar Q x y = 0)
    (hspan : ⨆ i, (Fr i).span = ⊤) {f : V ≃ₗ[K] V}
    (hfs : ∀ i, ∀ x ∈ (Fr i).span, f x ∈ (Fr i).span) (H : Fin m → Subgroup (V ≃ₗ[K] V))
    (T : Fin m → V ≃ₗ[K] V) (hTspan : ∀ i, ∀ x ∈ (Fr i).span, T i x = f x)
    (hTperp : ∀ i, ∀ x ∈ (Fr i).perp, T i x = x) (hH : ∀ i, T i ∈ H i) : f ∈ ⨆ i, H i := by
  classical
  have hTfix : ∀ j k, j ≠ k → ∀ x ∈ (Fr k).span, T j x = x := by
    intro j k hjk x hx
    apply hTperp j x
    rw [Frame.mem_perp_iff_forall_incl]
    intro Y
    rw [polar_comm]
    exact horth j k hjk _ ⟨Y, rfl⟩ x hx
  have hlist : ∀ l : List (Fin m), l.Nodup → ∀ k, ∀ x ∈ (Fr k).span,
      ((l.map T).prod) x = if k ∈ l then f x else x := by
    intro l hl
    induction l with
    | nil => intro k x hx; simp
    | cons j l ih =>
      intro k x hx
      rw [List.nodup_cons] at hl
      rw [List.map_cons, List.prod_cons, LinearEquiv.mul_apply, ih hl.2 k x hx]
      by_cases hkl : k ∈ l
      · have hjk : j ≠ k := fun h => hl.1 (h ▸ hkl)
        simp only [hkl, if_true, List.mem_cons, or_true]
        exact hTfix j k hjk (f x) (hfs k x hx)
      · by_cases hjk : j = k
        · subst hjk
          simp [hkl, hTspan j x hx]
        · simp [hkl, hjk, hTfix j k hjk x hx, Ne.symm hjk]
  have hprod : ((List.finRange m).map T).prod = f := by
    refine LinearEquiv.ext fun x => ?_
    have hx : x ∈ ⨆ i, (Fr i).span := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (fun i => (Fr i).span)
      (motive := fun x => (((List.finRange m).map T).prod) x = f x) hx
      (fun k y hy => ?_) (by simp) (fun a b ha hb => by rw [map_add, map_add, ha, hb])
    rw [hlist _ (List.nodup_finRange m) k y hy]
    simp
  rw [← hprod]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
  exact (le_iSup H i) (hH i)

theorem mem_iSup_La_swapLa_of_odd_charTwo [Finite K] [CharP K 2] [FiniteDimensional K V] {m : ℕ}
    (Fr : Fin m → Frame Q)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ (Fr i).span, ∀ y ∈ (Fr j).span, polar Q x y = 0)
    (hspan : ⨆ i, (Fr i).span = ⊤) {N : ℕ} (hN : Odd N) {f : V ≃ₗ[K] V}
    (hfO : f ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfN : f ^ N = 1)
    (hfs : ∀ i, ∀ x ∈ (Fr i).span, f x ∈ (Fr i).span) :
    f ∈ ⨆ i, ((Fr i).La.range ⊔ (Fr i).swap.La.range) := by
  choose T hTH hTspan hTperp using fun i => exists_blockElem_charTwo (Fr i) hN hfO hfN (hfs i)
  exact mem_iSup_of_blocks Fr horth hspan hfs (fun i => (Fr i).La.range ⊔ (Fr i).swap.La.range) T
    hTspan hTperp hTH

end Block

section HypForm

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V} {m : ℕ}

theorem map_hypComb_charFree {v : Fin m → Bool → V} (hv : IsHypFam Q v)
    (c : Fin m × Bool → F) : Q (hypComb v c) = ∑ i, c (i, true) * c (i, false) := by
  classical
  set x : Fin m → V := fun i => c (i, true) • v i true + c (i, false) • v i false with hx
  have hsum : hypComb v c = ∑ i, x i := by
    rw [hypComb_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
  have hQx : ∀ i, Q (x i) = c (i, true) * c (i, false) := by
    intro i
    rw [hx]
    dsimp only
    rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, hv.1 i true,
      hv.1 i false, polar_smul_left, polar_smul_right]
    have := hv.2.2 i true
    simp only [Bool.not_true] at this
    rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, this]
    simp
  have hpol : ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 := by
    intro i j hij
    rw [hx]
    dsimp only
    simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
      hv.2.1 i j hij, smul_zero, add_zero]
  have key : ∀ s : Finset (Fin m), Q (∑ i ∈ s, x i) = ∑ i ∈ s, Q (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, QuadraticMap.map_add Q, ih]
      have : polar Q (x a) (∑ i ∈ s, x i) = 0 := by
        have h1 : polar Q (x a) (∑ i ∈ s, x i) = ∑ i ∈ s, polar Q (x a) (x i) := by
          simp only [← polarBilin_apply_apply, map_sum]
        rw [h1]
        exact Finset.sum_eq_zero fun i hi => hpol a i (ne_of_mem_of_not_mem hi ha).symm
      rw [this, add_zero]
  rw [hsum, key]
  exact Finset.sum_congr rfl fun i _ => hQx i

theorem exists_isometry_of_fullHypFam [FiniteDimensional F V] (hdim : Module.finrank F V = 2 * m)
    {v v' : Fin m → Bool → V} (hv : IsHypFam Q v) (hv' : IsHypFam Q v') :
    ∃ ω : V ≃ₗ[F] V, ω ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ ∀ i s, ω (v i s) = v' i s := by
  classical
  have hcard : Module.finrank F (Fin m × Bool → F) = Module.finrank F V := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      hdim, mul_comm]
  have hb : Function.Bijective (hypComb (F := F) v) :=
    ⟨hypComb_injective hv, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard).mp
      (hypComb_injective hv)⟩
  have hb' : Function.Bijective (hypComb (F := F) v') :=
    ⟨hypComb_injective hv', (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hcard).mp
      (hypComb_injective hv')⟩
  let e := LinearEquiv.ofBijective (hypComb (F := F) v) hb
  let e' := LinearEquiv.ofBijective (hypComb (F := F) v') hb'
  refine ⟨e.symm.trans e', TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_,
    fun i s => ?_⟩
  · obtain ⟨c, rfl⟩ := e.surjective x
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    change Q (hypComb v' c) = Q (hypComb v c)
    rw [map_hypComb_charFree hv', map_hypComb_charFree hv]
  · have h1 : e (Pi.single (i, s) 1) = v i s := hypComb_single v i s
    have h2 : e' (Pi.single (i, s) 1) = v' i s := hypComb_single v' i s
    rw [← h1, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, h2]

end HypForm

section SpinNormalization

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_spin_normalization_charTwo {n : ℕ} (hn : 3 ≤ n)
    {v v' : Fin n → Bool → (Fin n ⊕ Fin n → K)} (hv : IsHypFam (quadPlus n K) v)
    (hv' : IsHypFam (quadPlus n K) v') (j₀ : Fin n) :
    ∃ (x : spinGroup (quadPlus n K)) (h : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)),
      (∀ y ∈ Submodule.span K {v j₀ true, v j₀ false},
        h y ∈ Submodule.span K {v j₀ true, v j₀ false}) ∧
      (∀ z, (∀ y ∈ Submodule.span K {v j₀ true, v j₀ false}, polar (quadPlus n K) y z = 0) →
        h z = z) ∧
      ∀ i s, v' i s = spinAction (quadPlus n K) x (h (v i s)) := by
  classical
  set Q := quadPlus n K with hQdef
  have hQ : (polarBilin Q).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  have hdim : Module.finrank K (Fin n ⊕ Fin n → K) = 2 * n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  obtain ⟨ω, hωO, hωv⟩ := exists_isometry_of_fullHypFam hdim hv hv'
  by_cases hev : Even (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace ω))
  · obtain ⟨x, hx⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus
      hn (g := ω) (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hωO, hev⟩)
    refine ⟨x, 1, fun y hy => hy, fun z _ => rfl, fun i s => ?_⟩
    rw [hx, ← hωv i s]
    rfl
  · set P : Submodule K (Fin n ⊕ Fin n → K) := Submodule.span K {v j₀ true, v j₀ false} with hP
    set a : Fin n ⊕ Fin n → K := v j₀ true + v j₀ false with ha
    have haP : a ∈ P := P.add_mem (Submodule.subset_span (by simp))
      (Submodule.subset_span (by simp))
    have hQa : Q a = 1 := by
      rw [ha, QuadraticMap.map_add Q, hv.1 j₀ true, hv.1 j₀ false]
      have := hv.2.2 j₀ true
      simp only [Bool.not_true] at this
      rw [this]
      simp
    have hQa0 : Q a ≠ 0 := by rw [hQa]; exact one_ne_zero
    let _ : Invertible (Q a) := invertibleOfNonzero hQa0
    set t := reflect Q a with ht
    have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := reflect_mem_orthogonalGroup Q a
    have htc : Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace t) = 1 := by
      rw [ht, reflect_eq_reflection]
      exact CFSG.RankThree.OrthogonalInvolutions.finrank_commSpace_reflection hQ a
    have hmul := CFSG.RankThree.OrthogonalInvolutions.natCast_finrank_commSpace_mul hQ hωO htO
    have h1 : ((Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace ω) : ℕ) :
        ZMod 2) = 1 := by
      rcases Nat.even_or_odd (Module.finrank K (CFSG.RankThree.OrthogonalInvolutions.commSpace ω))
        with h | h
      · exact absurd h hev
      · exact (ZMod.natCast_eq_one_iff_odd).mpr h
    have hevm : Even (Module.finrank K
        (CFSG.RankThree.OrthogonalInvolutions.commSpace (ω * t))) := by
      rw [← ZMod.natCast_eq_zero_iff_even, hmul, htc, h1, Nat.cast_one]
      exact CharTwo.add_self_eq_zero _
    obtain ⟨x, hx⟩ := CFSG.StandardType.GGOppRadOmega.exists_spinAction_eq_of_mem_omegaGroup_plus
      hn (g := ω * t) (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr
        ⟨mul_mem hωO htO, hevm⟩)
    refine ⟨x, t, fun y hy => ?_, fun z hz => ?_, fun i s => ?_⟩
    · rw [ht, reflect_apply hQa0]
      exact P.sub_mem hy (P.smul_mem _ haP)
    · exact reflect_apply_of_polar_eq_zero (hz a haP)
    · have htt : t * t = 1 := reflect_mul_self Q a
      rw [hx, LinearEquiv.mul_apply, ← LinearEquiv.mul_apply t t, htt]
      show v' i s = ω (v i s)
      rw [hωv]

end SpinNormalization

section Frames

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_frames_of_goodPlanes_charTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Set (V ≃ₗ[K] V)} (hSO : ∀ g ∈ S, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hSp : ∀ g ∈ S, g ^ p = 1) {k : ℕ} {Pl : Fin (2 * k) → Submodule K V}
    (hGP : GoodPlanes Q S Pl) :
    ∃ Fr : Fin k → Frame Q,
      (∀ a b, a ≠ b → ∀ x ∈ (Fr a).span, ∀ y ∈ (Fr b).span, polar Q x y = 0) ∧
      ⨆ a, (Fr a).span = ⊤ ∧ ∀ g ∈ S, g ∈ ⨆ a, omegaGrp (Fr a) := by
  classical
  obtain ⟨hreg, hdim, haniso, horth, hspan, hst⟩ := hGP
  obtain ⟨Fr, e, hFr, hFrorth, hFrspan⟩ := exists_frames_of_planes (ι := Fin (2 * k))
    (k := k) (by simp) Pl hreg hdim haniso horth hspan
  refine ⟨Fr, hFrorth, hFrspan, fun g hg => ?_⟩
  have hxs : ∀ a, ∀ y ∈ (Fr a).span, g y ∈ (Fr a).span := by
    intro a y hy
    rw [hFr a] at hy ⊢
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem_sup (hst g hg _ y₁ hy₁) (hst g hg _ y₂ hy₂)
  exact mem_iSup_La_swapLa_of_odd_charTwo Fr hFrorth hFrspan (hp.odd_of_ne_two hp2) (hSO g hg)
    (hSp g hg) hxs

end Frames

section SpinMain

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_spin_conj_of_goodPlanes_charTwo {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hexp : ∀ x ∈ Ep, x ^ p = 1)
    {Pl : Fin (2 * k) → Submodule K (Fin n ⊕ Fin n → K)}
    (hGP : GoodPlanes (quadPlus n K) {g | ∃ e ∈ Ep, g = spinAction (quadPlus n K) e} Pl) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hinj : Function.Injective (spinAction (quadPlus n K)) :=
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective
  obtain ⟨Fr, horth, hspan, hFE⟩ := exists_frames_of_goodPlanes_charTwo hp hp2
    (S := {g | ∃ e ∈ Ep, g = spinAction (quadPlus n K) e})
    (by
      rintro g ⟨e, he, rfl⟩
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ e w)
    (by
      rintro g ⟨e, he, rfl⟩
      rw [← map_pow, hexp e he, map_one]) hGP
  set v := frameFam Fr ι with hvdef
  have hv : IsHypFam (quadPlus n K) v := isHypFam_frameFam Fr ι horth
  have hv' : IsHypFam (quadPlus n K) (plusFrame n K hn).vec :=
    ⟨(plusFrame n K hn).map_vec, fun i j hij s t => (plusFrame n K hn).polar_vec_of_ne hij s t,
      (plusFrame n K hn).polar_vec_not⟩
  have hvι : ∀ a b s, v (ι (a, b)) s = pairVec (Fr a) b s := by
    intro a b s
    simp [hvdef, frameFam]
  set j₀ : Fin n := ι (⟨k - 1, by omega⟩, true) with hj₀
  set P : Submodule K (Fin n ⊕ Fin n → K) := Submodule.span K {v j₀ true, v j₀ false} with hPdef
  obtain ⟨hPreg, hPdim⟩ := polarNondegOn_span_hyp (Q := quadPlus n K) (e := v j₀ true)
    (f := v j₀ false) (by simpa using hv.2.2 j₀ true) (hv.1 j₀ true) (hv.1 j₀ false)
  obtain ⟨x, h, hhP, hhfix, hxv⟩ := exists_spin_normalization_charTwo hn hv hv' j₀
  set g : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) := spinAction (quadPlus n K) x with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ x w
  have hpair : ∀ j : Fin n, (Submodule.span K {v j true, v j false}).map (g : _ →ₗ[K] _) =
      Submodule.span K {(plusFrame n K hn).vec j true, (plusFrame n K hn).vec j false} := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      have hmapP : P.map (h : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) = P :=
        Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact hhP y hy)
          (by rw [LinearEquiv.finrank_map_eq])
      have e1 : Submodule.span K {v j₀ true, v j₀ false} = P := rfl
      rw [e1]
      calc P.map (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) =
          ((P.map (h : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))).map
            (g : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))) := by rw [hmapP]
        _ = _ := by
          rw [hPdef, map_span_pair, map_span_pair]
          simp only [LinearEquiv.coe_coe]
          rw [← hxv j₀ true, ← hxv j₀ false]
    · have hfix : ∀ s, h (v j s) = v j s := by
        intro s
        apply hhfix
        intro y hy
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hy
        rw [polar_add_left, polar_smul_left, polar_smul_left, hv.polar_eq, hv.polar_eq,
          if_neg (fun hh => hj hh.1.symm), if_neg (fun hh => hj hh.1.symm)]
        simp
      have hgv : ∀ s, g (v j s) = (plusFrame n K hn).vec j s := fun s => by
        rw [hg, hxv j s, hfix s]
      rw [map_span_pair]
      simp only [LinearEquiv.coe_coe, hgv]
  have hFrspan : ∀ a, (Fr a).span =
      Submodule.span K {v (ι (a, false)) true, v (ι (a, false)) false} ⊔
        Submodule.span K {v (ι (a, true)) true, v (ι (a, true)) false} := by
    intro a
    rw [frame_span_eq_pairs]
    simp only [hvι]
    rw [span_pair_eq (Fr a) false, span_pair_eq (Fr a) true]
    simp
  have hFr'span : ∀ a, ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true).span =
      Submodule.span K {(plusFrame n K hn).vec (ι (a, false)) true,
        (plusFrame n K hn).vec (ι (a, false)) false} ⊔
        Submodule.span K {(plusFrame n K hn).vec (ι (a, true)) true,
          (plusFrame n K hn).vec (ι (a, true)) false} :=
    fun a => frame_span_eq_pairs _
  have hspanmap : ∀ a, ((Fr a).map hgO).span =
      ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true).span := by
    intro a
    rw [span_map, hFrspan a, Submodule.map_sup, hpair, hpair, hFr'span a]
  have hmapΩ : ∀ a, (omegaGrp (Fr a)).map (MulAut.conj g).toMonoidHom =
      omegaGrp ((plusFrame n K hn).toFrame (ne_of_pairing ι a) true true) := fun a => by
    rw [← omegaGrp_map _ hgO, omegaGrp_eq_of_span_eq (hspanmap a)]
  refine ⟨x, fun e he => ?_⟩
  have hmem : spinAction (quadPlus n K) (x * e * x⁻¹) ∈
      (spinFrameGroup n K hn ι).map (spinAction (quadPlus n K)) := by
    rw [map_spinFrameGroup n hn ι, map_mul, map_mul, map_inv]
    have h0 : spinAction (quadPlus n K) e ∈ ⨆ a, omegaGrp (Fr a) := hFE _ ⟨e, he, rfl⟩
    have h2' : g * (spinAction (quadPlus n K) e) * g⁻¹ ∈
        (⨆ a, omegaGrp (Fr a)).map (MulAut.conj g).toMonoidHom := ⟨_, h0, rfl⟩
    rw [Subgroup.map_iSup] at h2'
    exact (iSup_mono (fun a => le_of_eq (hmapΩ a))) h2'
  obtain ⟨b, hb, hbeq⟩ := Subgroup.mem_map.mp hmem
  rw [← hinj hbeq]
  exact hb

theorem exists_spin_conj_frameGroup_charTwo {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (Ep : Subgroup (spinGroup (quadPlus n K))) (hexp : ∀ x ∈ Ep, x ^ p = 1)
    (hcard : Nat.card Ep = p ^ 2)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ e ∈ Ep, ∀ v ∈ T, spinAction (quadPlus n K) e v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), ∀ e ∈ Ep, x * e * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd : (polarBilin (quadPlus n K)).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  have hinj : Function.Injective (spinAction (quadPlus n K)) :=
    CFSG.StandardType.RootCentOmega.spinAction_quadPlus_injective
  have hrange : (spinAction (quadPlus n K)).range = orthDerived (quadPlus n K) :=
    range_spinAction_quadPlus_eq_commutator hn
  let sa : spinGroup (quadPlus n K) →* orthDerived (quadPlus n K) :=
    (spinAction (quadPlus n K)).codRestrict (orthDerived (quadPlus n K))
      (fun x => by rw [← hrange]; exact ⟨x, rfl⟩)
  have hsainj : Function.Injective sa := fun x y hxy => hinj (congrArg Subtype.val hxy)
  have hdisj : Disjoint Ep sa.ker := by
    rw [(MonoidHom.ker_eq_bot_iff sa).mpr hsainj]
    exact disjoint_bot_right
  set E : Subgroup (orthDerived (quadPlus n K)) := Ep.map sa with hE
  have hcardE : Nat.card E = p ^ 2 := by
    rw [hE, card_map_of_disjoint_ker sa hdisj, hcard]
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hcomm' := IsPGroup.isMulCommutative_of_card_eq_prime_sq (G := Ep) hcard
  have hcommEp : ∀ a ∈ Ep, ∀ b ∈ Ep, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm'.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcommEp a ha b hb]
  have hexpE : ∀ x ∈ E, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hexp a ha, map_one]
  have hNSE : OrthNoInvariantSingular (quadPlus n K) E := fun T hTi hTs =>
    hNS T (fun e he v hv => hTi (sa e) ⟨e, he, rfl⟩ v hv) hTs
  have hk : Module.finrank K (Fin n ⊕ Fin n → K) = 4 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes hQnd hp hp5 hpl hord E hcommE hexpE hcardE hNSE hk
  exact exists_spin_conj_of_goodPlanes_charTwo hn hnk ι hp (by omega) Ep hexp
    (hGP.mono (by
      rintro g ⟨e, he, rfl⟩
      exact ⟨sa e, ⟨e, he, rfl⟩, rfl⟩))

theorem exists_spin_conj_frameGroup_cyclic_charTwo {n : ℕ} (hn : 3 ≤ n) {k : ℕ}
    (hnk : n = 2 * k) (ι : Fin k × Bool ≃ Fin n) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2)
    (b : spinGroup (quadPlus n K)) (hb : b ^ p = 1)
    (hNS : ∀ T : Submodule K (Fin n ⊕ Fin n → K),
      (∀ v ∈ T, spinAction (quadPlus n K) b v ∈ T) →
      (∀ v ∈ T, quadPlus n K v = 0) → T = ⊥) :
    ∃ x : spinGroup (quadPlus n K), x * b * x⁻¹ ∈ spinFrameGroup n K hn ι := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hQnd : (polarBilin (quadPlus n K)).Nondegenerate := nondegenerate_polarBilin_quadPlus n K
  haveI : Finite (spinGroup (quadPlus n K)) :=
    finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  set g := spinAction (quadPlus n K) b with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus n K) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun w => map_spinAction _ b w
  have hgp : g ^ p = 1 := by rw [hg, ← map_pow, hb, map_one]
  have hk : Module.finrank K (Fin n ⊕ Fin n → K) = 4 * k := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨Pl, hGP⟩ := exists_goodPlanes_cyclic hQnd hp hp5 hpl hord hgO hgp
    (fun T hTi hTs => hNS T hTi hTs) hk
  obtain ⟨x, hx⟩ := exists_spin_conj_of_goodPlanes_charTwo hn hnk ι hp (by omega)
    (Subgroup.zpowers b) (by
      intro y hy
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hb,
        _root_.one_zpow])
    (hGP.mono (by
      rintro h ⟨e, he, rfl⟩
      obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr he)
      exact ⟨i, by rw [← hi, map_pow]⟩))
  exact ⟨x, hx b (Subgroup.mem_zpowers b)⟩

end SpinMain

end CFSG.LieType.SeitzGeneration.ExcHigh

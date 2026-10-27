module

public import CFSG.ClassicalInvolution.RouteD.GapsFrChain
public import CFSG.ClassicalInvolution.ModelFacts.OrthAutWitt
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpinBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.ModelFacts (map_conj_map map_longSL2_range La_range_eq_map_conj)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam exists_spin_normalization)
open scoped MatrixGroups

section Family

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {m : ℕ}

@[expose] def famVec (P : Fin m → HypPair Q) : Fin m → Bool → V := fun i s =>
  cond s (P i).e (P i).f

theorem isHypFam_famVec (P : Fin m → HypPair Q) (h : ∀ i j, i ≠ j → (P i).Orth (P j)) :
    IsHypFam Q (famVec P) := by
  refine ⟨fun i s => ?_, fun i j hij s t => ?_, fun i s => ?_⟩
  · cases s
    · exact (P i).Q_f
    · exact (P i).Q_e
  · have := h i j hij
    cases s <;> cases t
    · exact this.ff
    · exact this.fe
    · exact this.ef
    · exact this.ee
  · cases s
    · exact HypPair.polar_fe (P i)
    · exact (P i).polar_ef

theorem isHypFam_hypFrame (F : HypFrame Q m) : IsHypFam Q F.vec :=
  ⟨F.map_vec, fun _ _ hij s t => F.polar_vec_of_ne hij s t, F.polar_vec_not⟩

theorem hypPair_ext {P P' : HypPair Q} (he : P.e = P'.e) (hf : P.f = P'.f) : P = P' := by
  cases P
  cases P'
  simp_all

@[expose] noncomputable def rootSL2 (F₀ : HypFrame Q m) (a b : ℕ) (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (s t : Bool) : Subgroup (spinGroup Q) :=
  (F₀.longSL2 (i := ⟨a, ha⟩) (j := ⟨b, hb⟩) (fun h => hab (congrArg Fin.val h)) s t).range

end Family

section Spin

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

omit [Finite K] [FiniteDimensional K V] in
theorem finrank_hypPlane (P : HypPair Q) : Module.finrank K (hypPlane P) = 2 := by
  have hli : LinearIndependent K ![P.e, P.f] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => polar Q v P.f) hab
    have h2 := congrArg (fun v => polar Q v P.e) hab
    simp only [polar_add_left, polar_smul_left_eq, P.polar_ef, HypPair.polar_ff, HypPair.polar_ee,
      HypPair.polar_fe, polar_zero_left] at h1 h2
    simp only [mul_zero, zero_add, mul_one, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have h := finrank_span_eq_card hli
  rw [show Set.range ![P.e, P.f] = {P.e, P.f} from by
    ext x
    simp [or_comm]] at h
  rw [Fintype.card_fin] at h
  exact h

theorem exists_spin_family (hodd : Odd (Nat.card K)) (hQ : Q.Nondegenerate) (F₀ : HypFrame Q m)
    {P : Fin m → HypPair Q} (hP : ∀ i j, i ≠ j → (P i).Orth (P j)) (i₁ : Fin m) :
    ∃ x : spinGroup Q, (∀ i, i ≠ i₁ → (P i).e = spinAction Q x (F₀.vec i true) ∧
        (P i).f = spinAction Q x (F₀.vec i false)) ∧
      ∃ a b c d : K, (P i₁).e = spinAction Q x (a • F₀.vec i₁ true + b • F₀.vec i₁ false) ∧
        (P i₁).f = spinAction Q x (c • F₀.vec i₁ true + d • F₀.vec i₁ false) := by
  let P₁ : HypPair Q := ⟨F₀.vec i₁ true, F₀.vec i₁ false, F₀.map_vec _ _, F₀.map_vec _ _,
    by simpa using F₀.polar_vec_not i₁ true⟩
  have : Nontrivial V := ⟨⟨P₁.e, 0, P₁.e_ne_zero⟩⟩
  have : Invertible (2 : K) := invertibleOfNonzero (IsFundamental.two_ne_zero_of_odd hodd)
  have hnd : PolarNondegOn Q (hypPlane P₁) := polarNondegOn_hypPlane P₁
  obtain ⟨x, h, hhP, hhfix, hv⟩ := exists_spin_normalization hodd hQ (isHypFam_hypFrame F₀)
    (isHypFam_famVec P hP) (P := hypPlane P₁)
    (QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hnd))
    (by rw [finrank_hypPlane])
  refine ⟨x, fun i hi => ?_, ?_⟩
  · have hperp : ∀ s, ∀ y ∈ hypPlane P₁, polar Q y (F₀.vec i s) = 0 := by
      intro s y hy
      obtain ⟨a, b, rfl⟩ := (mem_hypPlane_iff P₁).mp hy
      simp only [polar_add_left, polar_smul_left_eq]
      show a * polar Q (F₀.vec i₁ true) (F₀.vec i s) + b * polar Q (F₀.vec i₁ false) (F₀.vec i s) = 0
      rw [F₀.polar_vec_of_ne (Ne.symm hi), F₀.polar_vec_of_ne (Ne.symm hi)]
      ring
    have e1 := hv i true
    have e2 := hv i false
    rw [hhfix _ (hperp true)] at e1
    rw [hhfix _ (hperp false)] at e2
    exact ⟨e1, e2⟩
  · have h1 : h (F₀.vec i₁ true) ∈ hypPlane P₁ := hhP _ (e_mem_hypPlane P₁)
    have h2 : h (F₀.vec i₁ false) ∈ hypPlane P₁ := hhP _ (f_mem_hypPlane P₁)
    obtain ⟨a, b, hab⟩ := (mem_hypPlane_iff P₁).mp h1
    obtain ⟨c, d, hcd⟩ := (mem_hypPlane_iff P₁).mp h2
    have e1 : (P i₁).e = spinAction Q x (h (F₀.vec i₁ true)) := hv i₁ true
    have e2 : (P i₁).f = spinAction Q x (h (F₀.vec i₁ false)) := hv i₁ false
    rw [hab] at e1
    rw [hcd] at e2
    exact ⟨a, b, c, d, e1, e2⟩

omit [Finite K] [FiniteDimensional K V] in
theorem La_range_eq_of_pairs (F₀ : HypFrame Q m) {a b : ℕ} (ha : a < m) (hb : b < m) (hab : a ≠ b)
    (s t : Bool) (x : spinGroup Q) {P P' : HypPair Q} (h : P.Orth P')
    (hP : P.e = spinAction Q x (F₀.vec ⟨a, ha⟩ s) ∧ P.f = spinAction Q x (F₀.vec ⟨a, ha⟩ (!s)))
    (hP' : P'.e = spinAction Q x (F₀.vec ⟨b, hb⟩ t) ∧
      P'.f = spinAction Q x (F₀.vec ⟨b, hb⟩ (!t))) :
    (mkFrame P P' h).La.range =
      ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom).map (spinAction Q) := by
  have hij : (⟨a, ha⟩ : Fin m) ≠ ⟨b, hb⟩ := fun h => hab (congrArg Fin.val h)
  have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
  have hP1 : P = ((F₀.toFrame hij s t).map hg).P := hypPair_ext hP.1 hP.2
  have hP2 : P' = ((F₀.toFrame hij s t).map hg).P' := hypPair_ext hP'.1 hP'.2
  have hfr : mkFrame P P' h = (F₀.toFrame hij s t).map hg := by
    unfold mkFrame
    generalize (F₀.toFrame hij s t).map hg = F at hP1 hP2 ⊢
    cases F
    subst hP1 hP2
    rfl
  have hLa : ∀ A : SL(2, K), (mkFrame P P' h).La A =
      spinAction Q x * (F₀.toFrame hij s t).La A * (spinAction Q x)⁻¹ := fun A => by
    rw [hfr]
    exact Frame.map_La _ hg A
  rw [La_range_eq_map_conj hLa, map_conj_map]
  unfold rootSL2
  rw [map_longSL2_range]

end Spin

section Combined

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {r m : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}

@[expose] def imgPair (F₀ : HypFrame Q m) (j : Fin m) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : HypPair Q :=
  ⟨g (F₀.vec j true), g (F₀.vec j false), by rw [map_of_mem hg]; exact F₀.map_vec j true,
    by rw [map_of_mem hg]; exact F₀.map_vec j false,
    by rw [polar_map_of_mem hg]; exact F₀.polar_vec_not j true⟩

omit [Finite K] [FiniteDimensional K V] in
theorem chainPlane_le_some (hr : 1 ≤ r) {a : ℕ} (ha : a ≤ r) :
    ∃ b < r, chainPlane r i a ≤ negSpace (i b) := by
  by_cases h : a < r
  · exact ⟨a, h, chainPlane_le_right h⟩
  · have : a = r := by omega
    subst this
    exact ⟨a - 1, by omega, chainPlane_le_left hr (by omega) le_rfl⟩

end Combined

section Chain

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {r m : ℕ} {L : ℕ → Subgroup (V ≃ₗ[K] V)} {i : ℕ → V ≃ₗ[K] V}

theorem exists_spin_chain (hodd : Odd (Nat.card K)) (hQ : Q.Nondegenerate) {F₀ : HypFrame Q m}
    {s : ℕ} (hm : m = s + 4) (hs : s + 1 = r) (hr : 2 ≤ r) (hc : VChain Q r L i)
    {LM : Subgroup (V ≃ₗ[K] V)} {iM : V ≃ₗ[K] V} (hM : IsFundamental Q LM iM)
    (hMorth : ∀ a < r, ∀ x ∈ negSpace iM, ∀ y ∈ negSpace (i a), polar Q x y = 0)
    {Ltw : Subgroup (V ≃ₗ[K] V)} (hLtw : IsFundamental Q Ltw (i s)) (hne : Ltw ≠ L s) :
    ∃ x : spinGroup Q,
      (∀ a (ha : a < r), L a = ((rootSL2 F₀ a (a + 1) (by omega) (by omega) (by omega) true
        false).map (MulAut.conj x).toMonoidHom).map (spinAction Q)) ∧
      Ltw = ((rootSL2 F₀ s (s + 1) (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom).map (spinAction Q) ∧
      ∃ t : Bool, LM = ((rootSL2 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
        (MulAut.conj x).toMonoidHom).map (spinAction Q) := by
  subst hm
  subst hs
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨p, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hc hr
  obtain ⟨FM, hLM, hiM⟩ := hM
  have hMspan : negSpace iM = hypPlane FM.P ⊔ hypPlane FM.P' := by
    rw [hiM, negSpace_La_neg_one h2, frame_span_eq]
  have hMp : ∀ a ≤ s + 1, ∀ Y : HypPair Q, hypPlane Y ≤ negSpace iM → (p a).Orth Y := by
    intro a ha Y hY
    obtain ⟨c, hc', hle⟩ := chainPlane_le_some (i := i) (by omega) ha
    refine orth_of_polar_hypPlane fun x hx y hy => ?_
    rw [hpl a ha] at hx
    rw [polar_comm]
    exact hMorth c hc' y (hY hy) x (hle hx)
  have hP1 : hypPlane FM.P ≤ negSpace iM := by rw [hMspan]; exact le_sup_left
  have hP2 : hypPlane FM.P' ≤ negSpace iM := by rw [hMspan]; exact le_sup_right
  let P : Fin (s + 4) → HypPair Q := fun a =>
    if a.val ≤ s + 1 then p a.val else if a.val = s + 2 then FM.P else FM.P'
  have hPo : ∀ a b : Fin (s + 4), a ≠ b → (P a).Orth (P b) := by
    intro a b hab
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have ha3 := a.isLt
    have hb3 := b.isLt
    by_cases ha : a.val ≤ s + 1
    · have e1 : P a = p a.val := by simp [P, ha]
      by_cases hb : b.val ≤ s + 1
      · have e2 : P b = p b.val := by simp [P, hb]
        rw [e1, e2]
        exact horth a.val b.val ha hb hab'
      · rw [e1]
        by_cases hb1 : b.val = s + 2
        · have e2 : P b = FM.P := by simp [P, hb1]
          rw [e2]
          exact hMp a.val ha FM.P hP1
        · have e2 : P b = FM.P' := by simp [P, hb, hb1]
          rw [e2]
          exact hMp a.val ha FM.P' hP2
    · by_cases hb : b.val ≤ s + 1
      · have e2 : P b = p b.val := by simp [P, hb]
        rw [e2]
        by_cases ha1 : a.val = s + 2
        · have e1 : P a = FM.P := by simp [P, ha1]
          rw [e1]
          exact (hMp b.val hb FM.P hP1).symm
        · have e1 : P a = FM.P' := by simp [P, ha, ha1]
          rw [e1]
          exact (hMp b.val hb FM.P' hP2).symm
      · by_cases ha1 : a.val = s + 2
        · have hb1 : b.val ≠ s + 2 := by omega
          have e1 : P a = FM.P := by simp [P, ha1]
          have e2 : P b = FM.P' := by simp [P, hb, hb1]
          rw [e1, e2]
          exact FM.orth
        · have hb1 : b.val = s + 2 := by omega
          have e1 : P a = FM.P' := by simp [P, ha, ha1]
          have e2 : P b = FM.P := by simp [P, hb1]
          rw [e1, e2]
          exact FM.orth.symm
  obtain ⟨x, hx1, a', b', c', d', he, hf⟩ :=
    exists_spin_family hodd hQ F₀ hPo (⟨s + 3, by omega⟩ : Fin (s + 4))
  have hPc : ∀ a (ha : a ≤ s + 1), (p a).e = spinAction Q x (F₀.vec ⟨a, by omega⟩ true) ∧
      (p a).f = spinAction Q x (F₀.vec ⟨a, by omega⟩ false) := by
    intro a ha
    have hne : (⟨a, by omega⟩ : Fin (s + 4)) ≠ ⟨s + 3, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    have h1 := hx1 _ hne
    have e : P ⟨a, by omega⟩ = p a := by simp [P, ha]
    rw [e] at h1
    exact h1
  have hPM : (FM.P).e = spinAction Q x (F₀.vec ⟨s + 2, by omega⟩ true) ∧
      (FM.P).f = spinAction Q x (F₀.vec ⟨s + 2, by omega⟩ false) := by
    have hne : (⟨s + 2, by omega⟩ : Fin (s + 4)) ≠ ⟨s + 3, by omega⟩ := fun h => by
      have := congrArg Fin.val h
      simp at this
    have h1 := hx1 _ hne
    have e : P ⟨s + 2, by omega⟩ = FM.P := by simp [P]
    rw [e] at h1
    exact h1
  refine ⟨x, fun a ha => ?_, ?_, ?_⟩
  · have := La_range_eq_of_pairs F₀ (a := a) (b := a + 1) (by omega) (by omega) (by omega) true
      false x (orth_swapPair (horth a (a + 1) ha.le ha (by omega))) (hPc a ha.le)
      ⟨(hPc (a + 1) ha).2, (hPc (a + 1) ha).1⟩
    rw [hLp a ha]
    exact this
  · have hspan : hypPlane (p s) ⊔ hypPlane (p (s + 1)) = negSpace (i s) := by
      rw [hpl s (by omega), hpl (s + 1) le_rfl]
      exact ((chainPlane_sup hodd hc hr (a := s) (by omega)).1).symm
    have hor := La_range_orientE true h2 hLtw (horth s (s + 1) (by omega) le_rfl (by omega)) hspan
    rcases hor with h | h
    · exact absurd (h.trans (hLp s (by omega)).symm) hne
    · rw [h]
      exact La_range_eq_of_pairs F₀ (a := s) (b := s + 1) (by omega) (by omega) (by omega) true
        true x _ (hPc s (by omega)) (hPc (s + 1) le_rfl)
  · have hg : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ x v
    have hMf : IsFundamental Q LM iM := ⟨FM, hLM, hiM⟩
    let Pb : HypPair Q := imgPair F₀ ⟨s + 3, by omega⟩ hg
    have eP : P ⟨s + 3, by omega⟩ = FM.P' := by simp [P]
    rw [eP] at he hf
    have hPb : hypPlane FM.P' = hypPlane Pb := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [finrank_hypPlane, finrank_hypPlane])
      rw [hypPlane, Submodule.span_le]
      rintro _ (rfl | rfl)
      · refine (mem_hypPlane_iff Pb).mpr ⟨a', b', ?_⟩
        rw [he]
        show _ = a' • spinAction Q x (F₀.vec _ true) + b' • spinAction Q x (F₀.vec _ false)
        rw [map_add, map_smul, map_smul]
      · refine (mem_hypPlane_iff Pb).mpr ⟨c', d', ?_⟩
        rw [hf]
        show _ = c' • spinAction Q x (F₀.vec _ true) + d' • spinAction Q x (F₀.vec _ false)
        rw [map_add, map_smul, map_smul]
    have hO : FM.P.Orth Pb := by
      refine orth_of_polar_hypPlane fun u hu v hv => ?_
      rw [← hPb] at hv
      exact polar_hypPlane_of_orth FM.orth u hu v hv
    have hspan : hypPlane FM.P ⊔ hypPlane Pb = negSpace iM := by
      rw [← hPb, hMspan]
    have hor := La_range_orient h2 hMf hO hspan
    rcases hor with h | h
    · refine ⟨true, ?_⟩
      rw [h]
      exact La_range_eq_of_pairs F₀ (a := s + 2) (b := s + 3) (by omega) (by omega) (by omega)
        true true x hO hPM ⟨rfl, rfl⟩
    · refine ⟨false, ?_⟩
      rw [h]
      exact La_range_eq_of_pairs F₀ (a := s + 2) (b := s + 3) (by omega) (by omega) (by omega)
        true false x (orth_swapPair hO) hPM ⟨rfl, rfl⟩

end Chain

end CFSG.ClassicalInvolution.RouteD.Gaps

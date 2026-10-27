module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173MixedSplit
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankTorus

import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankRot
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173UniVanish
import CFSG.ClassicalGroups.Orthogonal.MinusPlaneFrames
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.RankThree.PartOne.KFR4.DerivedLe

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T173M

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.GroupTheory.WeirSylow CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.GLTheoremA.S172C.Rank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.GLTheoremA.S172C.Cent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {l : ℕ} {U : Fin l → Submodule F V}
  {ρ : Fin l → ↥(orthDerived Q)} {i j : Fin l} {A : Subgroup ↥(orthDerived Q)}

structure IsMixedFrame (Q : QuadraticForm F V) (p : ℕ) {l : ℕ} (U : Fin l → Submodule F V)
    (ρ : Fin l → ↥(orthDerived Q)) (i j : Fin l) (A : Subgroup ↥(orthDerived Q)) : Prop where
  frame : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))
  iSup_eq_top : ⨆ k, U k = ⊤
  ne : i ≠ j
  eq_closure : A = Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j}))
  plane : ∃ W : Submodule F V, W ≠ ⊥ ∧ W ≤ U i ⊔ U j ∧ (∀ x ∈ W, Q x = 0) ∧
    ∀ a ∈ A, ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W

theorem IsMixedFrame.le_torus (hM : IsMixedFrame Q p U ρ i j A) :
    A ≤ Subgroup.closure (Set.range ρ) := by
  rw [hM.eq_closure, Subgroup.closure_le]
  rintro _ (rfl | ⟨k, -, rfl⟩)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)
  · exact Subgroup.subset_closure ⟨k, rfl⟩

theorem IsMixedFrame.rho_mem (hM : IsMixedFrame Q p U ρ i j A) {k : Fin l} (hki : k ≠ i) (hkj : k ≠ j) :
    ρ k ∈ A := by
  rw [hM.eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert_of_mem _ ⟨k, ⟨hki, hkj⟩, rfl⟩)

theorem IsMixedFrame.pair_mem (hM : IsMixedFrame Q p U ρ i j A) : ρ i * ρ j ∈ A := by
  rw [hM.eq_closure]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem eq_one_of_pow_eq_one_of_dvd_card_add_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) {c : F}
    (hc : c ^ p = 1) : c = 1 := by
  by_cases hc0 : c = 0
  · rw [hc0, zero_pow hp.ne_zero] at hc
    exact (one_ne_zero hc.symm).elim
  · have hpow : c ^ (Nat.card F - 1) = 1 := by
      haveI : Fintype F := Fintype.ofFinite F
      have h := FiniteField.pow_card_sub_one_eq_one c hc0
      rw [Nat.card_eq_fintype_card]
      exact h
    have hdvd_p : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.2 hc
    have hdvd_q : orderOf c ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.2 hpow
    rcases hp.eq_one_or_self_of_dvd (orderOf c) hdvd_p with h1 | hpord
    · exact orderOf_eq_one_iff.1 h1
    · exfalso
      have hpdvd : p ∣ Nat.card F - 1 := hpord ▸ hdvd_q
      have hsub : p ∣ (Nat.card F + 1) - (Nat.card F - 1) :=
        (Nat.dvd_sub_iff_left (by omega) hpdvd).2 hpq
      have hqpos : 1 ≤ Nat.card F := by
        haveI : Fintype F := Fintype.ofFinite F
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.2 ⟨c⟩
      have h2 : p ∣ 2 := by
        rwa [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hsub
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)

private theorem IsMixedFrame.aeval_eq_zero_iff_aux1 {P : Submodule F V} {L : V →ₗ[F] V}
    (hL : ∀ x ∈ P, L x = x) (f : Polynomial F) {x : V} (hx : x ∈ P) :
    Polynomial.aeval L f x = f.eval 1 • x := by
  have hpow : ∀ n : ℕ, (L ^ n) x = x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hL x hx]; exact ih
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, LinearMap.add_apply, Polynomial.eval_add, add_smul, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, one_pow, mul_one,
      Module.End.mul_apply, hpow n, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]

private theorem IsMixedFrame.aeval_eq_zero_iff_aux2
    {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ Bb) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {a : ↥(orthDerived Q)} (ha : a ∈ Bb) (f : Polynomial F) (j : Fin m)
    (hUjmap : ∀ x ∈ U j, (a : V ≃ₗ[F] V) x ∈ U j)
    (hML : ∀ x, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f ((a : V ≃ₗ[F] V) x)
        = (a : V ≃ₗ[F] V) (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f x))
    (hfree : ∀ x ∈ U j, (a : V ≃ₗ[F] V) x = x → x = 0)
    (hKne : LinearMap.ker (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f) ⊓ U j ≠ ⊥) :
    ∀ y ∈ U j, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y = 0 := by
  set M : V →ₗ[F] V := Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f with hMdef
  by_cases hKU : LinearMap.ker M ⊓ U j = U j
  · intro y hy
    have hyK : y ∈ LinearMap.ker M ⊓ U j := by rw [hKU]; exact hy
    exact hyK.1
  · exfalso
    have hle1 : Module.finrank F ↥(LinearMap.ker M ⊓ U j) ≤ 1 := by
      have hfr := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_right hKU)
      rw [hF.finrank_eq j] at hfr; omega
    obtain ⟨v, hv⟩ := (Submodule.finrank_le_one_iff_isPrincipal (LinearMap.ker M ⊓ U j)).1 hle1
    have hvK : v ∈ LinearMap.ker M ⊓ U j := by rw [hv]; exact Submodule.mem_span_singleton_self v
    have hv0 : v ≠ 0 := fun h0 => hKne (by rw [hv, h0, Submodule.span_singleton_eq_bot])
    have havK : (a : V ≃ₗ[F] V) v ∈ LinearMap.ker M ⊓ U j :=
      ⟨LinearMap.mem_ker.2 (by rw [hML]; simp [LinearMap.mem_ker.1 hvK.1]), hUjmap v hvK.2⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (by rw [← hv]; exact havK)
    have hap : (a : V ≃ₗ[F] V) ^ p = 1 :=
      by simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) (hF.isElemAbelian.2 a ha)
    have hcpow : ∀ n : ℕ, ((a : V ≃ₗ[F] V) ^ n) v = c ^ n • v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, ih, LinearEquiv.map_smul, ← hc, smul_smul, pow_succ]
    have hcp : c ^ p = 1 := by
      have h1 : c ^ p • v = v := by rw [← hcpow p, hap]; rfl
      exact sub_eq_zero.mp ((smul_eq_zero_iff_left hv0).1 (by rw [sub_smul, one_smul, h1, sub_self]))
    exact hv0 (hfree v hvK.2 (by rw [← hc, eq_one_of_pow_eq_one_of_dvd_card_add_one hp hp2 hpq hcp, one_smul]))

private theorem IsMixedFrame.aeval_eq_zero_iff_aux3 {m : ℕ} {U : Fin m → Submodule F V}
    {a : ↥(orthDerived Q)} (f : Polynomial F) (j : Fin m)
    (hid : ∀ x ∈ U j, (a : V ≃ₗ[F] V) x = x)
    (hKne : LinearMap.ker (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f) ⊓ U j ≠ ⊥) :
    ∀ y ∈ U j, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y = 0 := by
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKne
  have hscal : f.eval 1 = 0 := by
    have h1 : f.eval 1 • v = 0 := by
      rw [← IsMixedFrame.aeval_eq_zero_iff_aux1 hid f hvK.2]
      exact LinearMap.mem_ker.1 hvK.1
    exact (smul_eq_zero_iff_left hv0).1 h1
  intro y hy
  rw [IsMixedFrame.aeval_eq_zero_iff_aux1 hid f hy, hscal, zero_smul]

private theorem IsMixedFrame.aeval_eq_zero_iff_aux4
    {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ Bb)
    {a : ↥(orthDerived Q)} (ha : a ∈ Bb) (j : Fin m) :
    ∀ z ∈ U j, (a : V ≃ₗ[F] V) z ∈ U j := by
  obtain ⟨k, hk⟩ := hF.exists_pow_apply_eq ha j
  have hpow : ∀ n : ℕ, ∀ z ∈ U j, ((ρ j : V ≃ₗ[F] V) ^ n) z ∈ U j := by
    intro n
    induction n with
    | zero => intro z hz; simpa using hz
    | succ n ih => intro z hz; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hF.maps_to j z hz)
  intro z hz
  rw [hk z hz]
  exact hpow k z hz

private theorem IsMixedFrame.aeval_eq_zero_iff_aux5 {a : ↥(orthDerived Q)} (f : Polynomial F) :
    ∀ z, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f ((a : V ≃ₗ[F] V) z)
      = (a : V ≃ₗ[F] V) (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f z) := by
  have hcomm : (a : V ≃ₗ[F] V).toLinearMap * Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f
      = Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f * (a : V ≃ₗ[F] V).toLinearMap := by
    have h := congrArg (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap) (mul_comm Polynomial.X f)
    rwa [Polynomial.aeval_mul, Polynomial.aeval_mul, Polynomial.aeval_X] at h
  intro z
  have h := congrArg (fun g : V →ₗ[F] V => g z) hcomm
  simpa [Module.End.mul_apply] using h.symm

private theorem IsMixedFrame.aeval_eq_zero_iff_aux6
    {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ Bb)
    (i j : Fin m) {a : ↥(orthDerived Q)} (ha : a ∈ Bb) (f : Polynomial F)
    {W : Submodule F V} (hWne : W ≠ ⊥) (hWsup : W ≤ U i ⊔ U j)
    (hWTS : ∀ x ∈ W, Q x = 0) (hWinv : ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W)
    (hker : ∀ x ∈ U i, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f x = 0) :
    LinearMap.ker (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f) ⊓ U j ≠ ⊥ := by
  have hbot_i : W ⊓ U i = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact eq_zero_of_map_eq_zero_of_mem_plane hF.toIsPlaneSystem i hz.2 (hWTS z hz.1)
  have hbot_j : W ⊓ U j = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact eq_zero_of_map_eq_zero_of_mem_plane hF.toIsPlaneSystem j hz.2 (hWTS z hz.1)
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  obtain ⟨x, hxUi, y, hyUj, hxy⟩ := Submodule.mem_sup.1 (hWsup hwW)
  have hy0 : y ≠ 0 := by
    intro hy
    have hwK : w ∈ W ⊓ U i := ⟨hwW, by rw [← hxy, hy, add_zero]; exact hxUi⟩
    rw [hbot_i, Submodule.mem_bot] at hwK
    exact hw0 hwK
  have hMy0 : Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y = 0 := by
    have hEq : Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y
        = Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f w := by
      rw [← hxy, map_add, hker x hxUi, zero_add]
    have hMwW : Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f w ∈ W :=
      Polynomial.aeval_apply_smul_mem_of_le_comap hwW f (a : V ≃ₗ[F] V).toLinearMap hWinv
    have hMyUj : Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y ∈ U j :=
      Polynomial.aeval_apply_smul_mem_of_le_comap hyUj f (a : V ≃ₗ[F] V).toLinearMap
        (IsMixedFrame.aeval_eq_zero_iff_aux4 hF ha j)
    have hmem : Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y ∈ W ⊓ U j :=
      ⟨hEq.symm ▸ hMwW, hMyUj⟩
    rwa [hbot_j, Submodule.mem_bot] at hmem
  intro hbot
  have hyK : y ∈ LinearMap.ker (Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f) ⊓ U j :=
    ⟨LinearMap.mem_ker.2 hMy0, hyUj⟩
  rw [hbot, Submodule.mem_bot] at hyK
  exact hy0 hyK

private theorem IsMixedFrame.aeval_eq_zero_iff_aux7
    {m : ℕ} {U : Fin m → Submodule F V} {ρ : Fin m → ↥(orthDerived Q)}
    {Bb : Subgroup ↥(orthDerived Q)} (hF : IsPlaneFrame Q p U ρ Bb) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) (i j : Fin m) {a : ↥(orthDerived Q)} (ha : a ∈ Bb) (f : Polynomial F)
    {W : Submodule F V} (hWne : W ≠ ⊥) (hWsup : W ≤ U i ⊔ U j)
    (hWTS : ∀ x ∈ W, Q x = 0) (hWinv : ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W)
    (hker : ∀ x ∈ U i, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f x = 0) :
    ∀ y ∈ U j, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y = 0 := by
  have hKne := IsMixedFrame.aeval_eq_zero_iff_aux6 hF i j ha f hWne hWsup hWTS hWinv hker
  rcases hF.apply_eq_or_eq_zero hp ha j with hid | hfree
  · exact IsMixedFrame.aeval_eq_zero_iff_aux3 f j hid hKne
  · exact IsMixedFrame.aeval_eq_zero_iff_aux2 hF hp hp2 hpq ha f j
      (IsMixedFrame.aeval_eq_zero_iff_aux4 hF ha j) (IsMixedFrame.aeval_eq_zero_iff_aux5 f)
      hfree hKne

theorem IsMixedFrame.aeval_eq_zero_iff (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {a : ↥(orthDerived Q)} (ha : a ∈ A) (f : Polynomial F) :
    (∀ x ∈ U i, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f x = 0) ↔
      ∀ y ∈ U j, Polynomial.aeval (a : V ≃ₗ[F] V).toLinearMap f y = 0 := by
  obtain ⟨W, hWne, hWsup, hWTS, hWinvtot⟩ := hM.plane
  have hWinv : ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W := fun x hx => hWinvtot a ha x hx
  constructor
  · intro hker
    exact IsMixedFrame.aeval_eq_zero_iff_aux7 hM.frame hp hp2 hpq i j (hM.le_torus ha) f
      hWne hWsup hWTS hWinv hker
  · intro hker
    exact IsMixedFrame.aeval_eq_zero_iff_aux7 hM.frame hp hp2 hpq j i (hM.le_torus ha) f
      hWne (hWsup.trans (le_of_eq (sup_comm (U i) (U j)))) hWTS hWinv hker

theorem IsMixedFrame.apply_eq_iff (hM : IsMixedFrame Q p U ρ i j A) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card F + 1) {a : ↥(orthDerived Q)} (ha : a ∈ A) :
    (∀ x ∈ U i, (a : V ≃ₗ[F] V) x = x) ↔ ∀ x ∈ U j, (a : V ≃ₗ[F] V) x = x := by
  have h := hM.aeval_eq_zero_iff hp hp2 hpq ha (Polynomial.X - 1)
  simpa [sub_eq_zero] using h

theorem IsMixedFrame.isElemAbelian (hM : IsMixedFrame Q p U ρ i j A) : IsElemAbelian p A := by
  have hB := hM.frame.isElemAbelian
  haveI : IsMulCommutative (Subgroup.closure (Set.range ρ)) := hB.1
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_, fun x hx => hB.2 x (hM.le_torus hx)⟩
  exact setLike_mul_comm (hM.le_torus x.2) (hM.le_torus y.2)

theorem card_torus_eq (hp : p.Prime) (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) :
    Nat.card (Subgroup.closure (Set.range ρ)) = p ^ l := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative (Subgroup.closure (Set.range ρ)) := hF.isElemAbelian.1
  have hcomm : ∀ i j, Commute (ρ i) (ρ j) := fun i j =>
    setLike_mul_comm
      (Subgroup.subset_closure (show ρ i ∈ Set.range ρ from ⟨i, rfl⟩))
      (Subgroup.subset_closure (show ρ j ∈ Set.range ρ from ⟨j, rfl⟩))
  have hindep : ∀ i, ρ i ∉ Subgroup.closure (ρ '' {j | j ≠ i}) := by
    choose x hx hx0 using fun i => exists_ne_zero_mem_of_finrank_eq_two (U i) (hF.finrank_eq i)
    refine CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.not_mem_closure_image_of_smul_ne
      (orthDerived Q).subtype ρ x (fun i => ?_) (fun i j hij => ?_)
    · intro h
      exact hx0 i (hF.eq_zero_of_apply_eq i (x i) (hx i) h)
    · exact hF.apply_of_perp j (x i) (mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp i j hij (x i) (hx i) y hy)
  exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.isElemAbelian_card_closure_range
    ρ hcomm hF.orderOf_eq hindep).2

private noncomputable abbrev card_closure_pair_eq_aux1 (hU : IsPlaneSystem Q U) (k : Fin l) : V :=
  Classical.choose (exists_ne_zero_mem_of_finrank_eq_two (U k) (hU.finrank_eq k))

private theorem card_closure_pair_eq_aux2 (hU : IsPlaneSystem Q U) (k : Fin l) :
    card_closure_pair_eq_aux1 hU k ∈ U k :=
  (Classical.choose_spec (exists_ne_zero_mem_of_finrank_eq_two (U k) (hU.finrank_eq k))).1

private theorem card_closure_pair_eq_aux3 (hU : IsPlaneSystem Q U) (k : Fin l) :
    card_closure_pair_eq_aux1 hU k ≠ 0 :=
  (Classical.choose_spec (exists_ne_zero_mem_of_finrank_eq_two (U k) (hU.finrank_eq k))).2

private abbrev card_closure_pair_eq_aux4 (ρ : Fin l → ↥(orthDerived Q)) (i j : Fin l) :
    Option {k : Fin l // k ≠ i ∧ k ≠ j} → ↥(orthDerived Q) :=
  fun a => match a with
    | none => ρ i * ρ j
    | some ⟨k, _⟩ => ρ k

private noncomputable abbrev card_closure_pair_eq_aux5 (hU : IsPlaneSystem Q U) (i j : Fin l) :
    Option {k : Fin l // k ≠ i ∧ k ≠ j} → V :=
  fun a => match a with
    | none => card_closure_pair_eq_aux1 hU i
    | some ⟨k, _⟩ => card_closure_pair_eq_aux1 hU k

private theorem card_closure_pair_eq_aux6
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (hij : i ≠ j) :
    ∀ a, (orthDerived Q).subtype (card_closure_pair_eq_aux4 ρ i j a) •
        card_closure_pair_eq_aux5 hF.toIsPlaneSystem i j a ≠
      card_closure_pair_eq_aux5 hF.toIsPlaneSystem i j a := by
  intro a
  rcases a with _ | ⟨k, hk⟩
  · change ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (card_closure_pair_eq_aux1 hF.toIsPlaneSystem i) ≠
      card_closure_pair_eq_aux1 hF.toIsPlaneSystem i
    intro h
    have hvj : (ρ j : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem i) =
        card_closure_pair_eq_aux1 hF.toIsPlaneSystem i :=
      hF.apply_of_perp j _ (mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp i j hij _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem i) y hy)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hvj] at h
    exact card_closure_pair_eq_aux3 hF.toIsPlaneSystem i
      (hF.eq_zero_of_apply_eq i _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem i) h)
  · change (ρ k : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem k) ≠
      card_closure_pair_eq_aux1 hF.toIsPlaneSystem k
    intro h
    exact card_closure_pair_eq_aux3 hF.toIsPlaneSystem k
      (hF.eq_zero_of_apply_eq k _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem k) h)

private theorem card_closure_pair_eq_aux7
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (hij : i ≠ j) :
    ∀ a b, a ≠ b →
      (orthDerived Q).subtype (card_closure_pair_eq_aux4 ρ i j b) •
        card_closure_pair_eq_aux5 hF.toIsPlaneSystem i j a =
      card_closure_pair_eq_aux5 hF.toIsPlaneSystem i j a := by
  intro a b hab
  rcases a with _ | ⟨ka, hka⟩ <;> rcases b with _ | ⟨kb, hkb⟩
  · exact absurd rfl hab
  · change (ρ kb : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem i) =
        card_closure_pair_eq_aux1 hF.toIsPlaneSystem i
    exact hF.apply_of_perp kb _ (mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp i kb (Ne.symm hkb.1) _
        (card_closure_pair_eq_aux2 hF.toIsPlaneSystem i) y hy)
  · change ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V)
        (card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka) =
      card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka
    have hvi : (ρ i : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka) =
        card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka :=
      hF.apply_of_perp i _ (mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp ka i hka.1 _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem ka) y hy)
    have hvj : (ρ j : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka) =
        card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka :=
      hF.apply_of_perp j _ (mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp ka j hka.2 _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem ka) y hy)
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hvj, hvi]
  · have hne : ka ≠ kb := fun h => hab (congrArg some (Subtype.ext h))
    change (ρ kb : V ≃ₗ[F] V) (card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka) =
        card_closure_pair_eq_aux1 hF.toIsPlaneSystem ka
    exact hF.apply_of_perp kb _ (mem_polarPerp_iff.2 fun y hy => by
      rw [QuadraticMap.polar_comm]
      exact hF.perp ka kb hne _ (card_closure_pair_eq_aux2 hF.toIsPlaneSystem ka) y hy)

private theorem card_closure_pair_eq_aux8 (hp : p.Prime)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) (hij : i ≠ j) :
    orderOf (ρ i * ρ j) = p := by
  have hmem : ρ i * ρ j ∈ Subgroup.closure (Set.range ρ) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)
  have hpow : (ρ i * ρ j) ^ p = 1 := hF.isElemAbelian.2 _ hmem
  have hne : ρ i * ρ j ≠ 1 := by
    intro h1
    obtain ⟨v, hv, hv0⟩ := exists_ne_zero_mem_of_finrank_eq_two (U i) (hF.finrank_eq i)
    have hvj : (ρ j : V ≃ₗ[F] V) v = v :=
      hF.apply_of_perp j v (mem_polarPerp_iff.2 fun y hy => by
        rw [QuadraticMap.polar_comm]
        exact hF.perp i j hij v hv y hy)
    have h2 : ((ρ i * ρ j : ↥(orthDerived Q)) : V ≃ₗ[F] V) v = v := by rw [h1]; rfl
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, hvj] at h2
    exact hv0 (hF.eq_zero_of_apply_eq i v hv h2)
  rcases hp.eq_one_or_self_of_dvd (orderOf (ρ i * ρ j))
    (orderOf_dvd_iff_pow_eq_one.2 hpow) with h1 | h1
  · exact absurd (orderOf_eq_one_iff.1 h1) hne
  · exact h1

private theorem card_closure_pair_eq_aux9 (i j : Fin l) :
    Set.range (card_closure_pair_eq_aux4 ρ i j) =
      insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j}) := by
  ext g; constructor
  · rintro ⟨a, rfl⟩
    rcases a with _ | ⟨k, hk⟩
    · exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨k, hk, rfl⟩
  · intro hg
    rw [Set.mem_insert_iff] at hg
    rcases hg with rfl | ⟨k, hk, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨k, hk⟩, rfl⟩

private theorem card_closure_pair_eq_aux10 {l : ℕ} {i j : Fin l} (hij : i ≠ j) :
    Fintype.card (Option {k : Fin l // k ≠ i ∧ k ≠ j}) = l - 1 := by
  classical
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hsub : Fintype.card {k : Fin l // k ≠ i ∧ k ≠ j} = l - 2 := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter (fun k : Fin l => k ≠ i ∧ k ≠ j)) =
        ({i, j} : Finset (Fin l))ᶜ := by
      ext k; simp [not_or]
    rw [hset, Finset.card_compl, Fintype.card_fin]
    have h2 : ({i, j} : Finset (Fin l)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa using hij), Finset.card_singleton]
    rw [h2]
  rw [Fintype.card_option, hsub]
  have hi := i.isLt; have hj := j.isLt
  omega

theorem card_closure_pair_eq (hp : p.Prime) (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    (hij : i ≠ j) :
    Nat.card (Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j}))) = p ^ (l - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsMulCommutative (Subgroup.closure (Set.range ρ)) := hF.isElemAbelian.1
  let ι := Option {k : Fin l // k ≠ i ∧ k ≠ j}
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let e' : Fin (Fintype.card ι) → ↥(orthDerived Q) := fun a =>
    card_closure_pair_eq_aux4 ρ i j (σ.symm a)
  let x' : Fin (Fintype.card ι) → V := fun a =>
    card_closure_pair_eq_aux5 hF.toIsPlaneSystem i j (σ.symm a)
  have hmem : ∀ a : ι, card_closure_pair_eq_aux4 ρ i j a ∈ Subgroup.closure (Set.range ρ) := by
    intro a; rcases a with _ | ⟨k, _⟩
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)
    · exact Subgroup.subset_closure ⟨k, rfl⟩
  have hcomm' : ∀ a b, Commute (e' a) (e' b) := fun a b =>
    setLike_mul_comm (hmem (σ.symm a)) (hmem (σ.symm b))
  have hord' : ∀ a, orderOf (e' a) = p := by
    intro a
    change orderOf (card_closure_pair_eq_aux4 ρ i j (σ.symm a)) = p
    rcases σ.symm a with _ | ⟨k, hk⟩
    · change orderOf (ρ i * ρ j) = p
      exact card_closure_pair_eq_aux8 hp hF hij
    · change orderOf (ρ k) = p
      exact hF.orderOf_eq k
  have hmove' : ∀ a, (orthDerived Q).subtype (e' a) • x' a ≠ x' a :=
    fun a => card_closure_pair_eq_aux6 hF hij (σ.symm a)
  have hfix' : ∀ a b, a ≠ b → (orthDerived Q).subtype (e' b) • x' a = x' a :=
    fun a b hab => card_closure_pair_eq_aux7 hF hij (σ.symm a) (σ.symm b)
      (fun h => hab (σ.symm.injective h))
  have hindep' : ∀ a, e' a ∉ Subgroup.closure (e' '' {b | b ≠ a}) :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.not_mem_closure_image_of_smul_ne
      (orthDerived Q).subtype e' x' hmove' hfix'
  have hres := CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.isElemAbelian_card_closure_range
    e' hcomm' hord' hindep'
  have hcardι : Fintype.card ι = l - 1 := card_closure_pair_eq_aux10 hij
  have hrange : Set.range e' = insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j}) := by
    have h1 : Set.range e' = Set.range (card_closure_pair_eq_aux4 ρ i j) := by
      show Set.range ((card_closure_pair_eq_aux4 ρ i j) ∘ σ.symm) =
        Set.range (card_closure_pair_eq_aux4 ρ i j)
      rw [Set.range_comp, Set.range_eq_univ.mpr σ.symm.surjective, Set.image_univ]
    rw [h1, card_closure_pair_eq_aux9 (ρ := ρ) i j]
  rw [hrange, hcardι] at hres
  exact hres.2

theorem IsMixedFrame.card_eq (hp : p.Prime) (hM : IsMixedFrame Q p U ρ i j A) :
    Nat.card A = p ^ (l - 1) := by
  rw [hM.eq_closure]
  exact card_closure_pair_eq hp hM.frame hM.ne

theorem exists_graph_plane {l : ℕ} {U : Fin l → Submodule F V} (hU : IsPlaneSystem Q U) {i j : Fin l} (hij : i ≠ j)
    {σ : V ≃ₗ[F] V} (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσU : Submodule.map σ.toLinearMap (U i) = U j) {A' : Subgroup ↥(orthDerived Q)}
    (hA' : ∀ a ∈ A', ∀ x ∈ U i, (a : V ≃ₗ[F] V) x ∈ U i)
    (hequiv : ∀ a ∈ A', ∀ x ∈ U i, (a : V ≃ₗ[F] V) (σ x) = σ ((a : V ≃ₗ[F] V) x)) :
    ∃ W : Submodule F V, Module.finrank F W = 2 ∧ W ≤ U i ⊔ U j ∧ (∀ x ∈ W, Q x = 0) ∧
      ∀ a ∈ A', ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W := by
  let f : V →ₗ[F] V := (LinearMap.id : V →ₗ[F] V) + σ.toLinearMap
  let g : U i →ₗ[F] V := f.comp (U i).subtype
  have hg_apply : ∀ x : U i, g x = (x : V) + σ (x : V) := fun _ => rfl
  have hσ_mem : ∀ x : U i, σ (x : V) ∈ U j := by
    intro x
    have h := Submodule.mem_map_of_mem (f := σ.toLinearMap) (p := U i) x.2
    rwa [hσU] at h
  have hd_bot : U i ⊓ U j = ⊥ := by
    have h := hU.disjoint_biSup (Q := Q) (a := i) (s := {j}) (by simp [Finset.mem_singleton, hij])
    exact disjoint_iff.mp (by simpa [Finset.iSup_singleton] using h)
  have hg_inj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hx' : (x : V) + σ (x : V) = 0 := hx
    have hneg : σ (x : V) = -(x : V) := by
      rw [← add_eq_zero_iff_eq_neg, add_comm]
      exact hx'
    have hmem : σ (x : V) ∈ U i ⊓ U j :=
      Submodule.mem_inf.2 ⟨by rw [hneg]; exact neg_mem x.2, hσ_mem x⟩
    rw [hd_bot, Submodule.mem_bot] at hmem
    refine Subtype.ext ?_
    rw [hmem, add_zero] at hx'
    exact hx'
  refine ⟨LinearMap.range g, ?_, ?_, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hg_inj, hU.finrank_eq i]
  · intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [hg_apply]
    exact add_mem (Submodule.mem_sup_left x.2) (Submodule.mem_sup_right (hσ_mem x))
  · intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [hg_apply, QuadraticMap.map_add Q, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hσ (x : V),
      hU.perp i j hij (x : V) x.2 (σ (x : V)) (hσ_mem x), add_zero]
    exact CharTwo.add_self_eq_zero (Q (x : V))
  · intro a ha y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [hg_apply, map_add, hequiv a ha x x.2]
    exact LinearMap.mem_range.mpr ⟨⟨(a : V ≃ₗ[F] V) (x : V), hA' a ha x x.2⟩, rfl⟩

private theorem exists_twoGroup_of_totallySingular_aux1 {W : Submodule F V}
    (hTS : ∀ x ∈ W, Q x = 0) : ∀ x ∈ W, ∀ y ∈ W, polar Q x y = 0 := by
  intro x hx y hy
  have hxy : x + y ∈ W := W.add_mem hx hy
  have h := hTS (x + y) hxy
  rw [QuadraticMap.map_add Q, hTS x hx, hTS y hy] at h
  simpa using h

private theorem exists_twoGroup_of_totallySingular_aux2 {W : Submodule F V}
    (hTS : ∀ x ∈ W, Q x = 0) : ∀ y ∈ eichlerGroupOn Q W, y * y = 1 := by
  have hpol := exists_twoGroup_of_totallySingular_aux1 (Q := Q) (W := W) hTS
  let S : Set (V ≃ₗ[F] V) := {g | ∃ e ∈ W, ∃ w ∈ W, g = eichler Q e w}
  have hS : eichlerGroupOn Q W = Subgroup.closure S := rfl
  have hcomm_gen : S.Pairwise Commute := by
    intro x hx y hy _
    obtain ⟨e, he, w, hw, rfl⟩ := hx
    obtain ⟨e', he', w', hw', rfl⟩ := hy
    have hxfix : eichler Q e w e' = e' :=
      eichler_apply_of_polar_eq_zero (hpol e' he' e he) (hpol e' he' w hw)
    have hyfix : eichler Q e w w' = w' :=
      eichler_apply_of_polar_eq_zero (hpol w' hw' e he) (hpol w' hw' w hw)
    have hconj := eichler_conj (eichler_mem_orthogonalGroup Q e w) e' w'
    rw [hxfix, hyfix] at hconj
    rw [commute_iff_eq]
    calc eichler Q e w * eichler Q e' w'
        = (eichler Q e w * eichler Q e' w' * (eichler Q e w)⁻¹) * eichler Q e w := by
          rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = eichler Q e' w' * eichler Q e w := by rw [hconj]
  haveI : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hcomm_gen
  rw [hS]
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨e, he, w, hw, rfl⟩ := hz
      rw [eichler_mul (hpol e he w hw) (hpol e he w hw)]
      have hww : w + w = 0 := by rw [← two_smul F w, CharTwo.two_eq_zero, zero_smul]
      rw [hww]
      exact eichler_zero_right Q e
  | one => rfl
  | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := by
        have := mul_comm' (⟨a, ha⟩ : Subgroup.closure S) (⟨b, hb⟩ : Subgroup.closure S)
        exact Subtype.ext_iff.mp this
      calc (a * b) * (a * b) = a * (b * (a * b)) := by rw [mul_assoc]
        _ = a * ((b * a) * b) := by rw [mul_assoc]
        _ = a * ((a * b) * b) := by rw [← hab]
        _ = a * (a * (b * b)) := by rw [mul_assoc]
        _ = (a * a) * (b * b) := by rw [mul_assoc]
        _ = 1 := by rw [iha, ihb, one_mul]
  | inv a _ iha => rw [inv_eq_of_mul_eq_one_right iha, iha]

private theorem exists_twoGroup_of_totallySingular_aux3 (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {W : Submodule F V} (hW : Module.finrank F W = 2) (hTS : ∀ x ∈ W, Q x = 0) :
    ∃ y ∈ eichlerGroupOn Q W, y ≠ 1 := by
  have hpol := exists_twoGroup_of_totallySingular_aux1 (Q := Q) (W := W) hTS
  obtain ⟨w1, hw1W, hw10⟩ := exists_ne_zero_mem_of_finrank_eq_two W hW
  obtain ⟨w2, hw2W, hw2span⟩ : ∃ w2 ∈ W, w2 ∉ Submodule.span F {w1} := by
    by_contra h
    push Not at h
    have hle : Module.finrank F W ≤ Module.finrank F (Submodule.span F {w1}) :=
      Submodule.finrank_mono fun x hx => h x hx
    rw [finrank_span_singleton hw10, hW] at hle
    omega
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hw10
  let c : F := polar Q w1 y
  have hc : c ≠ 0 := hy
  let f : V := c⁻¹ • y
  have hfw1 : polar Q f w1 = 1 := by
    show polar Q (c⁻¹ • y) w1 = 1
    rw [polar_smul_left_eq, polar_comm]
    exact inv_mul_cancel₀ hc
  refine ⟨eichler Q w1 w2, eichler_mem_eichlerGroupOn hw1W hw2W, ?_⟩
  intro h1
  have hEf : eichler Q w1 w2 f = f := by rw [h1]; rfl
  rw [eichler_apply (hTS w1 hw1W) (hpol w1 hw1W w2 hw2W) f, hfw1] at hEf
  simp only [one_smul] at hEf
  have hw2eq : w2 = (polar Q f w2 + Q w2 * 1) • w1 := by
    rw [sub_eq_iff_eq_add] at hEf
    exact add_left_cancel hEf
  exact hw2span (Submodule.mem_span_singleton.2 ⟨_, hw2eq.symm⟩)

theorem exists_twoGroup_of_totallySingular (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) {W : Submodule F V} (hW : Module.finrank F W = 2)
    (hTS : ∀ x ∈ W, Q x = 0) :
    ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
      ∀ g : ↥(orthDerived Q), (∀ x ∈ W, (g : V ≃ₗ[F] V) x ∈ W) → g ∈ Subgroup.normalizer (T : Set ↥(orthDerived Q)) := by
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  haveI : Finite ↥(orthDerived Q) := Finite.of_injective (fun x : ↥(orthDerived Q) => (x : V ≃ₗ[F] V))
    fun a b h => Subtype.ext h
  let T : Subgroup ↥(orthDerived Q) := (eichlerGroupOn Q W).subgroupOf (orthDerived Q)
  haveI : Finite T := Finite.of_injective (fun x : T => (x : V ≃ₗ[F] V))
    fun a b h => Subtype.ext (Subtype.ext h)
  have hle : eichlerGroupOn Q W ≤ orthDerived Q :=
    eichlerGroupOn_le fun e _ w _ => T173U.eichler_mem_orthDerived (Q := Q) (n := l) hQ (by omega) hdim e w
  have hsq : ∀ y ∈ eichlerGroupOn Q W, y * y = 1 :=
    exists_twoGroup_of_totallySingular_aux2 (Q := Q) (W := W) hTS
  have hTne : T ≠ ⊥ := by
    obtain ⟨y, hy, hy1⟩ := exists_twoGroup_of_totallySingular_aux3 (Q := Q) hQ hW hTS
    intro hbot
    have hyΩ : y ∈ orthDerived Q := hle hy
    have : (⟨y, hyΩ⟩ : ↥(orthDerived Q)) = 1 := by
      have hmem : (⟨y, hyΩ⟩ : ↥(orthDerived Q)) ∈ T := Subgroup.mem_subgroupOf.2 hy
      rw [hbot] at hmem
      simpa using hmem
    exact hy1 (Subtype.ext_iff.mp this)
  have hT2 : IsPGroup 2 T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [IsPGroup.iff_orderOf]
    intro g
    have hgg : g * g = 1 := by
      apply Subtype.ext; apply Subtype.ext
      exact hsq _ (Subgroup.mem_subgroupOf.1 g.2)
    have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hgg)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact ⟨0, by rw [h]; rfl⟩
    · exact ⟨1, by rw [h]; rfl⟩
  refine ⟨T, hTne, hT2, ?_⟩
  intro g hgW
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  have hnE : (n : V ≃ₗ[F] V) ∈ eichlerGroupOn Q W := Subgroup.mem_subgroupOf.1 hn
  have hgO : (g : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    Subgroup.commutator_le_self _ g.2
  exact Subgroup.mem_subgroupOf.2
    (T173U.conj_mem_eichlerGroupOn (W := W) (g := (g : V ≃ₗ[F] V)) hgO hgW hnE)

private theorem exists_planeSystem_of_type_aux1 {V₁ : Type} [AddCommGroup V₁] [Module F V₁]
    [FiniteDimensional F V₁] {Q₁ : QuadraticForm F V₁} {r : ℕ} {W₁ : Submodule F V₁}
    {U₁ : Fin r → Submodule F W₁} (hU₁ : IsPlaneSystem (Q₁.comp W₁.subtype) U₁) :
    IsPlaneSystem Q₁ (fun j => (U₁ j).map W₁.subtype) := by
  have hiso : ∀ j, ((Q₁.comp W₁.subtype).comp (U₁ j).subtype).IsometryEquiv
      (Q₁.comp ((U₁ j).map W₁.subtype).subtype) := fun j =>
    { toLinearEquiv := Submodule.equivMapOfInjective W₁.subtype W₁.subtype_injective (U₁ j)
      map_app' := fun _ => rfl }
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa using hU₁.finrank_eq j
  · intro j
    refine nondegenerate_polarBilin_restrict ?_
    intro x hx hxorth
    obtain ⟨x', hx'U, rfl⟩ := Submodule.mem_map.1 hx
    have hx'0 : x' = 0 := by
      have h := (hU₁.nondeg j).1 ⟨x', hx'U⟩ fun y' => by
        have hy : (W₁.subtype y' : V₁) ∈ (U₁ j).map W₁.subtype := ⟨y', y'.2, rfl⟩
        have hh := hxorth (W₁.subtype y') hy
        rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
        exact hh
      exact congrArg (fun z : ↥(U₁ j) => (z : W₁)) h
    simpa [hx'0] using congrArg W₁.subtype hx'0
  · intro j hplus
    exact hU₁.not_isPlusType j ((isPlusType_congr (hiso j)).2 hplus)
  · intro i j hij x hx y hy
    obtain ⟨x', hx'U, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨y', hy'U, rfl⟩ := Submodule.mem_map.1 hy
    have h := hU₁.perp i j hij x' hx'U y' hy'U
    rw [polar_comp_subtype_cent] at h
    exact h

private theorem exists_planeSystem_of_type_aux2 {V₁ : Type} [AddCommGroup V₁] [Module F V₁]
    [FiniteDimensional F V₁] {Q₁ : QuadraticForm F V₁} {r : ℕ} {P₁ : Submodule F V₁}
    {U₁ : Fin r → Submodule F V₁} (hU₁ : IsPlaneSystem Q₁ U₁)
    (hle : ∀ j, U₁ j ≤ polarPerp Q₁ P₁) (hP₂ : Module.finrank F P₁ = 2)
    (hPreg : (QuadraticMap.polarBilin (Q₁.comp P₁.subtype)).Nondegenerate)
    (hPm : ¬ IsPlusType (Q₁.comp P₁.subtype)) :
    IsPlaneSystem Q₁ (Fin.cons P₁ U₁) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    induction j using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hP₂
    | succ j => rw [Fin.cons_succ]; exact hU₁.finrank_eq j
  · intro j
    induction j using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hPreg
    | succ j => rw [Fin.cons_succ]; exact hU₁.nondeg j
  · intro j
    induction j using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hPm
    | succ j => rw [Fin.cons_succ]; exact hU₁.not_isPlusType j
  · intro i j hij x hx y hy
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j =>
        simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
        exact (mem_polarPerp_iff.1 (hle j hy)) x hx
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero, Fin.cons_succ] at hx hy
        rw [QuadraticMap.polar_comm]
        exact (mem_polarPerp_iff.1 (hle i hx)) y hy
      | succ j =>
        simp only [Fin.cons_succ] at hx hy
        exact hU₁.perp i j (fun h => hij (by rw [h])) x hx y hy

private theorem exists_planeSystem_of_type_aux3 {V₁ : Type} [AddCommGroup V₁] [Module F V₁]
    [FiniteDimensional F V₁] {Q₁ : QuadraticForm F V₁} {n : ℕ} {a b : V₁}
    (hQ : (QuadraticMap.polarBilin Q₁).Nondegenerate)
    (hdim : Module.finrank F V₁ = 2 * ((n + 1) + 1))
    (htype : IsPlusType Q₁ ↔ Even ((n + 1) + 1)) (hab : IsAnisoPair Q₁ a b) :
    IsPlusType (Q₁.comp (polarPerp Q₁ (Submodule.span F {a, b})).subtype) ↔ Even (n + 1) := by
  have hiso : (Q₁.restrict (polarPerp Q₁ (Submodule.span F {a, b}))).IsometryEquiv
      (Q₁.comp (polarPerp Q₁ (Submodule.span F {a, b})).subtype) :=
    { toLinearEquiv := LinearEquiv.refl F (polarPerp Q₁ (Submodule.span F {a, b}))
      map_app' := fun _ => rfl }
  have h1 : IsPlusType (Q₁.comp (polarPerp Q₁ (Submodule.span F {a, b})).subtype) ↔
      ¬ IsPlusType Q₁ :=
    (isPlusType_congr hiso).symm.trans (by
      have h := show IsPlusType Q₁ ↔
          ¬ IsPlusType (Q₁.restrict (polarPerp Q₁ (Submodule.span F {a, b}))) from
        hab.isPlusType_iff_restrict_orthPerp hQ (k := n) (by omega)
      constructor
      · intro hc' hq; exact h.1 hq hc'
      · intro hnq; by_contra hc'; exact hnq (h.2 hc'))
  rw [h1, htype]
  have h2 : Even (n + 2) ↔ ¬ Even (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.even_add_one]
  rw [h2]; tauto

private theorem exists_planeSystem_of_type_aux4 {V₁ : Type} [AddCommGroup V₁] [Module F V₁]
    [FiniteDimensional F V₁] {Q₁ : QuadraticForm F V₁} {r : ℕ} {P₁ : Submodule F V₁}
    (hc : IsCompl P₁ (polarPerp Q₁ P₁))
    {U' : Fin r → Submodule F ↥(polarPerp Q₁ P₁)}
    (hU'sys : IsPlaneSystem (Q₁.comp (polarPerp Q₁ P₁).subtype) U')
    (hU'top : (⨆ j, U' j) = ⊤) (hP2 : Module.finrank F P₁ = 2)
    (hPreg : (QuadraticMap.polarBilin (Q₁.comp P₁.subtype)).Nondegenerate)
    (hPm : ¬ IsPlusType (Q₁.comp P₁.subtype)) :
    ∃ U : Fin (r + 1) → Submodule F V₁, IsPlaneSystem Q₁ U ∧ ⨆ k, U k = ⊤ := by
  have hsys : IsPlaneSystem Q₁ (fun j => (U' j).map (polarPerp Q₁ P₁).subtype) :=
    exists_planeSystem_of_type_aux1 hU'sys
  have hle : ∀ j, (U' j).map (polarPerp Q₁ P₁).subtype ≤ polarPerp Q₁ P₁ := fun j => by
    rintro x ⟨y, hy, rfl⟩; exact y.2
  have hcons : IsPlaneSystem Q₁ (Fin.cons P₁ (fun j => (U' j).map (polarPerp Q₁ P₁).subtype)) :=
    exists_planeSystem_of_type_aux2 hsys hle hP2 hPreg hPm
  have hsup : (⨆ j, (U' j).map (polarPerp Q₁ P₁).subtype) = polarPerp Q₁ P₁ := by
    rw [← Submodule.map_iSup, hU'top, Submodule.map_subtype_top]
  refine ⟨Fin.cons P₁ (fun j => (U' j).map (polarPerp Q₁ P₁).subtype), hcons, ?_⟩
  rw [eq_top_iff, ← hc.sup_eq_top]
  refine sup_le ?_ ?_
  · simpa [Fin.cons_zero] using
      le_iSup (Fin.cons P₁ (fun j => (U' j).map (polarPerp Q₁ P₁).subtype)) 0
  · exact hsup.ge.trans (iSup_le fun j => by
      simpa [Fin.cons_succ] using
        le_iSup (Fin.cons P₁ (fun j => (U' j).map (polarPerp Q₁ P₁).subtype)) j.succ)

private theorem exists_planeSystem_of_type_aux5 :
    ∀ (n : ℕ) {V₁ : Type} [AddCommGroup V₁] [Module F V₁] [FiniteDimensional F V₁]
      {Q₁ : QuadraticForm F V₁}, (QuadraticMap.polarBilin Q₁).Nondegenerate →
      Module.finrank F V₁ = 2 * (n + 1) → (IsPlusType Q₁ ↔ Even (n + 1)) →
      ∃ U₀ : Fin (n + 1) → Submodule F V₁, IsPlaneSystem Q₁ U₀ ∧ ⨆ k, U₀ k = ⊤ := by
  intro n
  induction n with
  | zero =>
    intro V₁ _ _ _ Q₁ hQ hdim htype
    refine ⟨fun _ => ⊤, ⟨?_, ?_, ?_, ?_⟩, iSup_const⟩
    · intro j; simpa using hdim
    · intro j; exact nondegenerate_polarBilin_restrict (polarNondegOn_top hQ)
    · intro j hplus
      exact Nat.not_even_one (htype.1 ((isPlusType_congr
        { toLinearEquiv := Submodule.topEquiv.symm, map_app' := fun _ => rfl }).2 hplus))
    · intro i j hij; exact absurd (Fin.ext (by omega)) hij
  | succ n ih =>
    intro V₁ _ _ _ Q₁ hQ hdim htype
    obtain ⟨a, b, hab⟩ := exists_isAnisoPair hQ (m := n + 2) (by omega) (by omega)
    let P₁ : Submodule F V₁ := Submodule.span F {a, b}
    have hP2 : Module.finrank F P₁ = 2 := hab.finrank_span_pair
    have hPreg : (QuadraticMap.polarBilin (Q₁.comp P₁.subtype)).Nondegenerate :=
      nondegenerate_polarBilin_restrict hab.polarNondegOn
    have hPm : ¬ IsPlusType (Q₁.comp P₁.subtype) := by
      intro hplus
      have hiff := CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_restrict_iff_of_finrank_two
        (Q := Q₁) (W := P₁) hP2
      obtain ⟨w, hw, hw0, hQw⟩ := hiff.1 (show IsPlusType (Q₁.restrict P₁) from hplus)
      exact hw0 (hab.eq_zero_of_mem_span_pair hw hQw)
    have hc : IsCompl P₁ (polarPerp Q₁ P₁) := hab.isCompl_span_orthPerp
    have hWreg : (QuadraticMap.polarBilin (Q₁.comp (polarPerp Q₁ P₁).subtype)).Nondegenerate :=
      nondegenerate_polarBilin_restrict (polarNondegOn_orthPerp hQ hc)
    have hWdim : Module.finrank F (polarPerp Q₁ P₁) = 2 * (n + 1) := by
      have h := Submodule.finrank_add_eq_of_isCompl hc
      rw [hP2, hdim] at h
      omega
    have hWtype : IsPlusType (Q₁.comp (polarPerp Q₁ P₁).subtype) ↔ Even (n + 1) :=
      exists_planeSystem_of_type_aux3 hQ hdim htype hab
    obtain ⟨U', hU'sys, hU'top⟩ :=
      ih (V₁ := ↥(polarPerp Q₁ P₁)) (Q₁ := Q₁.comp (polarPerp Q₁ P₁).subtype) hWreg hWdim hWtype
    exact exists_planeSystem_of_type_aux4 hc hU'sys hU'top hP2 hPreg hPm

theorem exists_planeSystem_of_type (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 2 ≤ l) (htype : IsPlusType Q ↔ Even l) :
    ∃ U : Fin l → Submodule F V, IsPlaneSystem Q U ∧ ⨆ k, U k = ⊤ := by
  have hl1 : 1 ≤ l := by omega
  rw [show l = (l - 1) + 1 from (Nat.sub_add_cancel hl1).symm]
  exact exists_planeSystem_of_type_aux5 (l - 1) (V₁ := V) (Q₁ := Q) hQ
    (by rw [Nat.sub_add_cancel hl1]; exact hdim)
    (by rw [Nat.sub_add_cancel hl1]; exact htype)

private theorem exists_rotation_of_mem_plane_aux0 (hU : IsPlaneSystem Q U) (k : Fin l) {x y : V}
    (hxU : x ∈ U k) (hyU : y ∈ U k) (hx : Q x ≠ 0) (hy : Q y ≠ 0) :
    ∀ u ∈ U k, (reflect Q x * reflect Q y) u ∈ U k := by
  have hmapx : ∀ u ∈ U k, (reflect Q x) u ∈ U k := fun u hu => by
    rw [reflect_apply hx]
    exact Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hxU)
  have hmapy : ∀ u ∈ U k, (reflect Q y) u ∈ U k := fun u hu => by
    rw [reflect_apply hy]
    exact Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hyU)
  intro u hu
  rw [LinearEquiv.mul_apply]
  exact hmapx _ (hmapy u hu)

private theorem exists_rotation_of_mem_plane_aux1 (hU : IsPlaneSystem Q U) (k : Fin l) {x y : V}
    (hxU : x ∈ U k) (hyU : y ∈ U k) (hx : Q x ≠ 0) (hy : Q y ≠ 0) (hxy : polar Q x y ≠ 0)
    {z : V} (hzU : z ∈ U k) (hz0 : z ≠ 0)
    (hzfix : (reflect Q x * reflect Q y) z = z) :
    ∀ w ∈ U k, (reflect Q x * reflect Q y) ((reflect Q x * reflect Q y) w) = w := by
  have hmap := exists_rotation_of_mem_plane_aux0 hU k hxU hyU hx hy
  have hRO : (reflect Q x * reflect Q y) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (reflect_mem_orthogonalGroup Q x) (reflect_mem_orthogonalGroup Q y)
  have hsub : Submodule.map (reflect Q x * reflect Q y).toLinearMap (U k) = U k := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨u, hu, rfl⟩; exact hmap u hu
    · rw [LinearEquiv.finrank_map_eq (reflect Q x * reflect Q y) (U k)]
  let g : U k ≃ₗ[F] U k := (reflect Q x * reflect Q y).ofSubmodules (U k) (U k) hsub
  have hg_apply : ∀ u : U k, ((g u : U k) : V) = (reflect Q x * reflect Q y) (u : V) :=
    fun _ => rfl
  have hgz : g ⟨z, hzU⟩ = ⟨z, hzU⟩ := by
    apply Subtype.ext
    show ((g ⟨z, hzU⟩ : U k) : V) = z
    rw [hg_apply, hzfix]
  have hg1 : g ≠ 1 := by
    intro h1
    have key : (reflect Q x * reflect Q y) x = x := by
      have := congrArg (fun (g : U k ≃ₗ[F] U k) => ((g ⟨x, hxU⟩ : U k) : V)) h1
      simpa [LinearEquiv.coe_one, hg_apply] using this
    exact reflect_mul_reflect_apply_ne hx hy hxy key
  have hQz : (Q.comp (U k).subtype) ⟨z, hzU⟩ ≠ 0 := fun hq =>
    hz0 (eq_zero_of_map_eq_zero_of_mem_plane hU k hzU hq)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (U k).subtype) := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun u => ?_
    show Q ((g u : U k) : V) = Q (u : V)
    rw [hg_apply u]
    exact map_of_mem hRO (u : V)
  rcases CFSG.LocalAnalysis.ComponentInitial.orthogonal_char_two_plane_vector_stabilizer
    (hU.finrank_eq k) (hU.nondeg k) hQz hgO hgz with h1 | h1
  · exact (hg1 h1).elim
  · intro w hw
    have hg2 : g * g = 1 := by rw [h1]; exact reflect_mul_self (Q.comp (U k).subtype) ⟨z, hzU⟩
    have key : ((g * g) ⟨w, hw⟩ : V) = w := by
      have := congrArg (fun (g : U k ≃ₗ[F] U k) => ((g ⟨w, hw⟩ : U k) : V)) hg2
      simpa only [LinearEquiv.coe_one, id_eq] using this
    rw [LinearEquiv.mul_apply] at key
    rw [hg_apply (g ⟨w, hw⟩), hg_apply ⟨w, hw⟩] at key
    exact key

private theorem exists_rotation_of_mem_plane_aux2 {R : V ≃ₗ[F] V} (k : Fin l) {x : V}
    (hRxU : R x ∈ U k) (hsq : ∀ w ∈ U k, R (R w) = w) (hrp : R ^ p = 1) (hp : p.Prime)
    (hp2 : p ≠ 2) (hrx : R x ≠ x) : False := by
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := hp.odd_of_ne_two hp2
  have h2m : ∀ m, ∀ w ∈ U k, ((R ^ 2) ^ m) w = w := by
    intro m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      rw [pow_succ, LinearEquiv.mul_apply]
      rw [show (R ^ 2) w = w from by rw [pow_two, LinearEquiv.mul_apply]; exact hsq w hw]
      exact ih w hw
  have hxfix : R x = x := by
    have h1 : ((R ^ 2) ^ m * R) x = x := by
      have hpow : (R ^ 2) ^ m * R = 1 := by
        rw [← pow_mul, ← pow_succ, ← hm]; exact hrp
      rw [hpow]; rfl
    rw [LinearEquiv.mul_apply, h2m m (R x) hRxU] at h1
    exact h1
  exact hrx hxfix

theorem exists_rotation_of_mem_plane (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (hU : IsPlaneSystem Q U) (k : Fin l) :
    ∃ r : ↥(orthDerived Q), orderOf r = p ∧ (∀ x ∈ U k, (r : V ≃ₗ[F] V) x ∈ U k) ∧
      (∀ x ∈ U k, (r : V ≃ₗ[F] V) x = x → x = 0) ∧ ∀ x ∈ polarPerp Q (U k), (r : V ≃ₗ[F] V) x = x := by
  have han : ∀ x ∈ U k, Q x = 0 → x = 0 := fun x hx hq =>
    eq_zero_of_map_eq_zero_of_mem_plane hU k hx hq
  obtain ⟨x, hxU, y, hyU, hx, hy, hord⟩ :=
    exists_orderOf_reflect_mul_reflect_eq (U := U k) (hU.finrank_eq k) han hp hp2 hpq
  have hxy : polar Q x y ≠ 0 := polar_ne_zero_of_orderOf_reflect_mul_reflect hp hp2 hord
  have hmap := exists_rotation_of_mem_plane_aux0 hU k hxU hyU hx hy
  have hrp : (reflect Q x * reflect Q y) ^ p = 1 := by
    rw [← hord]; exact pow_orderOf_eq_one _
  refine ⟨⟨reflect Q x * reflect Q y, reflect_mul_reflect_mem_orthDerived hQ hx hy⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk]; exact hord
  · intro u hu
    change (reflect Q x * reflect Q y) u ∈ U k
    exact hmap u hu
  · intro z hzU hzfix
    by_contra hz0
    have hsq := exists_rotation_of_mem_plane_aux1 hU k hxU hyU hx hy hxy hzU hz0 hzfix
    exact exists_rotation_of_mem_plane_aux2 k (hmap x hxU) hsq hrp hp hp2
      (reflect_mul_reflect_apply_ne hx hy hxy)
  · intro v hv
    change (reflect Q x * reflect Q y) v = v
    exact reflect_mul_reflect_apply_of_polar_eq_zero
      (mem_polarPerp_iff.mp hv x hxU) (mem_polarPerp_iff.mp hv y hyU)

private theorem exists_swapFrame_aux1 {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {r : V ≃ₗ[F] V}
    (hr : r ∈ orthDerived Q) : σ * r * σ⁻¹ ∈ orthDerived Q := by
  rw [← CFSG.RankThree.PartOne.KFR4.DLe.map_conj_orthDerived Q hσ]
  exact ⟨r, hr, by simp [MulAut.conj_apply]⟩

private theorem exists_swapFrame_aux2 (hU : IsPlaneSystem Q U) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσU : Submodule.map σ.toLinearMap (U i) = U j) :
    polarPerp Q (U j) ≤ Submodule.map σ.toLinearMap (polarPerp Q (U i)) := by
  intro x hx
  refine ⟨σ.symm x, mem_polarPerp_iff.2 ?_, σ.apply_symm_apply x⟩
  intro u hu
  rw [← CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem hσ u (σ.symm x),
    LinearEquiv.apply_symm_apply]
  exact mem_polarPerp_iff.1 hx (σ u)
    (hσU ▸ Submodule.mem_map_of_mem (f := σ.toLinearMap) hu)

private def exists_swapFrame_aux3 {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (r : ↥(orthDerived Q)) : ↥(orthDerived Q) :=
  ⟨σ * (r : V ≃ₗ[F] V) * σ⁻¹, exists_swapFrame_aux1 hσ r.2⟩

private theorem exists_swapFrame_aux4 (hU : IsPlaneSystem Q U) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσU : Submodule.map σ.toLinearMap (U i) = U j) {r : ↥(orthDerived Q)}
    (hord : orderOf r = p) (hrU : ∀ x ∈ U i, (r : V ≃ₗ[F] V) x ∈ U i)
    (hrfree : ∀ x ∈ U i, (r : V ≃ₗ[F] V) x = x → x = 0)
    (hrperp : ∀ x ∈ polarPerp Q (U i), (r : V ≃ₗ[F] V) x = x) :
    orderOf (exists_swapFrame_aux3 hσ r) = p ∧
      (∀ x ∈ polarPerp Q (U j), (exists_swapFrame_aux3 hσ r : V ≃ₗ[F] V) x = x) ∧
      (∀ x ∈ U j, (exists_swapFrame_aux3 hσ r : V ≃ₗ[F] V) x ∈ U j) ∧
      (∀ x ∈ U j, (exists_swapFrame_aux3 hσ r : V ≃ₗ[F] V) x = x → x = 0) := by
  have hcoe : (exists_swapFrame_aux3 hσ r : V ≃ₗ[F] V) = σ * (r : V ≃ₗ[F] V) * σ⁻¹ := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : orderOf (exists_swapFrame_aux3 hσ r) = orderOf (σ * (r : V ≃ₗ[F] V) * σ⁻¹) := by
      rw [← Subgroup.orderOf_coe (exists_swapFrame_aux3 hσ r), hcoe]
    rw [h1, ← MulAut.conj_apply, MulEquiv.orderOf_eq, Subgroup.orderOf_coe]
    exact hord
  · intro x hx
    obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.1 (exists_swapFrame_aux2 hU hσ hσU hx)
    rw [← hvx]
    change (σ * (r : V ≃ₗ[F] V) * σ.symm) (σ v) = σ v
    simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
    exact congrArg σ (hrperp v hv)
  · intro x hx
    obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.1 (hσU ▸ hx)
    rw [← hvx]
    change (σ * (r : V ≃ₗ[F] V) * σ.symm) (σ v) ∈ U j
    simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
    rw [← hσU]
    exact Submodule.mem_map_of_mem (f := σ.toLinearMap) (hrU v hv)
  · intro x hx hxx
    obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.1 (hσU ▸ hx)
    have hvv : (r : V ≃ₗ[F] V) v = v := by
      apply σ.injective
      rw [← hvx] at hxx
      change (σ * (r : V ≃ₗ[F] V) * σ.symm) (σ v) = σ v at hxx
      simpa only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply] using hxx
    rw [← hvx, hrfree v hv hvv, map_zero]

private theorem exists_swapFrame_aux5 (hU : IsPlaneSystem Q U) {a : Fin l} {g e : ↥(orthDerived Q)}
    (hgU : ∀ x ∈ U a, (g : V ≃ₗ[F] V) x = x)
    (heU : ∀ x ∈ U a, (e : V ≃ₗ[F] V) x ∈ U a)
    (heP : ∀ x ∈ polarPerp Q (U a), (e : V ≃ₗ[F] V) x = x) :
    g * e = e * g := by
  apply Subtype.ext
  exact commute_of_apply_eq (hU.nondeg a)
    (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Q g.2) hgU heU heP

private theorem exists_swapFrame_aux6 (hU : IsPlaneSystem Q U) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσU : Submodule.map σ.toLinearMap (U i) = U j)
    {r : Fin l → ↥(orthDerived Q)}
    (hr : ∀ k, orderOf (r k) = p ∧ (∀ x ∈ U k, (r k : V ≃ₗ[F] V) x ∈ U k) ∧
      (∀ x ∈ U k, (r k : V ≃ₗ[F] V) x = x → x = 0) ∧
      ∀ x ∈ polarPerp Q (U k), (r k : V ≃ₗ[F] V) x = x)
    {ρ : Fin l → ↥(orthDerived Q)} (hρj : ρ j = exists_swapFrame_aux3 hσ (r i))
    (hρ : ∀ k, k ≠ j → ρ k = r k) :
    (∀ k, orderOf (ρ k) = p) ∧
      (∀ k, ∀ x ∈ polarPerp Q (U k), (ρ k : V ≃ₗ[F] V) x = x) ∧
      (∀ k, ∀ x ∈ U k, (ρ k : V ≃ₗ[F] V) x ∈ U k) ∧
      (∀ k, ∀ x ∈ U k, (ρ k : V ≃ₗ[F] V) x = x → x = 0) ∧
      (∀ k m, ρ k * ρ m = ρ m * ρ k) := by
  have h4 := exists_swapFrame_aux4 hU hσ hσU (hr i).1 (hr i).2.1 (hr i).2.2.1 (hr i).2.2.2
  have horder_eq : ∀ k, orderOf (ρ k) = p := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hρj]; exact h4.1
    · rw [hρ k hk]; exact (hr k).1
  have hfix : ∀ k, ∀ x ∈ polarPerp Q (U k), (ρ k : V ≃ₗ[F] V) x = x := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hρj]; exact h4.2.1
    · rw [hρ k hk]; exact (hr k).2.2.2
  have hmaps : ∀ k, ∀ x ∈ U k, (ρ k : V ≃ₗ[F] V) x ∈ U k := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hρj]; exact h4.2.2.1
    · rw [hρ k hk]; exact (hr k).2.1
  have hfree : ∀ k, ∀ x ∈ U k, (ρ k : V ≃ₗ[F] V) x = x → x = 0 := by
    intro k
    by_cases hk : k = j
    · subst hk; rw [hρj]; exact h4.2.2.2
    · rw [hρ k hk]; exact (hr k).2.2.1
  have hcomm : ∀ k m, ρ k * ρ m = ρ m * ρ k := by
    intro k m
    by_cases hkm : k = m
    · subst hkm; rfl
    · have hUk : U k ≤ polarPerp Q (U m) := fun x hx =>
        mem_polarPerp_iff.2 fun y hy => hU.perp m k (Ne.symm hkm) y hy x hx
      exact (exists_swapFrame_aux5 (a := k) hU (fun x hx => hfix m x (hUk hx))
        (hmaps k) (hfix k)).symm
  exact ⟨horder_eq, hfix, hmaps, hfree, hcomm⟩

theorem exists_swapFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (htype : IsPlusType Q ↔ Even l) (hij : i ≠ j) :
    ∃ (U : Fin l → Submodule F V) (ρ : Fin l → ↥(orthDerived Q)) (σ : V ≃ₗ[F] V),
      IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)) ∧ ⨆ k, U k = ⊤ ∧
      σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ Submodule.map σ.toLinearMap (U i) = U j ∧
      ∀ x ∈ U i, (ρ j : V ≃ₗ[F] V) (σ x) = σ ((ρ i : V ≃ₗ[F] V) x) := by
  obtain ⟨U, hU, htop⟩ := exists_planeSystem_of_type hQ hdim (by omega) htype
  obtain ⟨σ, hσ, hσU, -⟩ := T173U.exists_swap_isometry hU hij
  choose r hr using fun k => exists_rotation_of_mem_plane hQ hdim hl hp hp2 hpq hU k
  let ρ : Fin l → ↥(orthDerived Q) :=
    fun k => if k = j then exists_swapFrame_aux3 hσ (r i) else r k
  have hρi : ρ i = r i := by simp [ρ, hij]
  have hρj : ρ j = exists_swapFrame_aux3 hσ (r i) := by simp [ρ]
  have hρ : ∀ k, k ≠ j → ρ k = r k := by intro k hk; simp [ρ, hk]
  obtain ⟨horder_eq, hfix, hmaps, hfree, hcomm⟩ :=
    exists_swapFrame_aux6 hU hσ hσU hr hρj hρ
  refine ⟨U, ρ, σ, ?_, htop, hσ, hσU, ?_⟩
  · refine
      { toIsPlaneSystem := hU
        orderOf_eq := horder_eq
        apply_of_perp := hfix
        maps_to := hmaps
        eq_zero_of_apply_eq := hfree
        isElemAbelian := ?_
        closure_eq := rfl }
    refine IsElemAbelian.closure_of_commute (fun a ha b hb => ?_) (fun a ha => ?_)
    · obtain ⟨k, rfl⟩ := ha; obtain ⟨m, rfl⟩ := hb; exact hcomm k m
    · obtain ⟨k, rfl⟩ := ha
      simpa [horder_eq k] using pow_orderOf_eq_one (ρ k)
  · intro x hx
    rw [hρj, hρi]
    change (σ * (r i : V ≃ₗ[F] V) * σ.symm) (σ x) = σ ((r i : V ≃ₗ[F] V) x)
    simp only [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]

private theorem swap_equivariant_aux1 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {k m : Fin l} (hkm : k ≠ m) : ∀ x ∈ U m, (ρ k : V ≃ₗ[F] V) x = x := by
  intro x hx
  exact hF.apply_of_perp k x (mem_polarPerp_iff.mpr (fun y hy => hF.perp k m hkm y hy x hx))

private theorem swap_equivariant_aux2 :
    Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j})) ≤
      Subgroup.closure (Set.range ρ) := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [Set.mem_insert_iff] at hg
  rcases hg with h | h
  · rw [h]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) (Subgroup.subset_closure ⟨j, rfl⟩)
  · rcases h with ⟨k, -, rfl⟩
    exact Subgroup.subset_closure ⟨k, rfl⟩

private theorem swap_equivariant_aux3 (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    {d : ↥(orthDerived Q)} (hd : d ∈ Subgroup.closure (Set.range ρ)) (k : Fin l) :
    ∀ x ∈ U k, (d : V ≃ₗ[F] V) x ∈ U k := by
  intro x hx
  obtain ⟨n, hn⟩ := hF.exists_pow_apply_eq hd k
  rw [hn x hx]
  have hpow : ∀ n, ∀ x ∈ U k, ((ρ k : V ≃ₗ[F] V) ^ n) x ∈ U k := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ, LinearEquiv.mul_apply]; exact ih _ (hF.maps_to k x hx)
  exact hpow n x hx

theorem swap_equivariant {l : ℕ} {U : Fin l → Submodule F V} {ρ : Fin l → ↥(orthDerived Q)} {i j : Fin l} (hij : i ≠ j)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ))) {σ : V ≃ₗ[F] V}
    (hσU : Submodule.map σ.toLinearMap (U i) = U j)
    (hσρ : ∀ x ∈ U i, (ρ j : V ≃ₗ[F] V) (σ x) = σ ((ρ i : V ≃ₗ[F] V) x)) :
    ∀ a ∈ Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j})),
      ∀ x ∈ U i, (a : V ≃ₗ[F] V) (σ x) = σ ((a : V ≃ₗ[F] V) x) := by
  intro a ha
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    rw [Set.mem_insert_iff] at hg
    rcases hg with hg1 | hg2
    · rw [hg1]
      intro x hx
      change (ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) (σ x)) =
        σ ((ρ i : V ≃ₗ[F] V) ((ρ j : V ≃ₗ[F] V) x))
      have hσim : (σ : V ≃ₗ[F] V) ((ρ i : V ≃ₗ[F] V) x) ∈ U j :=
        hσU ▸ Submodule.mem_map.mpr ⟨(ρ i : V ≃ₗ[F] V) x, hF.maps_to i x hx, rfl⟩
      rw [hσρ x hx, swap_equivariant_aux1 hF hij (σ ((ρ i : V ≃ₗ[F] V) x)) hσim,
        swap_equivariant_aux1 hF hij.symm x hx]
    · obtain ⟨k, hk, hkg⟩ := hg2
      rw [← hkg]
      intro x hx
      change (ρ k : V ≃ₗ[F] V) (σ x) = σ ((ρ k : V ≃ₗ[F] V) x)
      have hσxU : (σ : V ≃ₗ[F] V) x ∈ U j :=
        hσU ▸ Submodule.mem_map.mpr ⟨x, hx, rfl⟩
      rw [swap_equivariant_aux1 hF hk.2 (σ x) hσxU, swap_equivariant_aux1 hF hk.1 x hx]
  | one => intro x _; rfl
  | mul a b ha hb iha ihb =>
    intro x hx
    change (a : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) (σ x)) =
      σ ((a : V ≃ₗ[F] V) ((b : V ≃ₗ[F] V) x))
    have hbU : (b : V ≃ₗ[F] V) x ∈ U i :=
      swap_equivariant_aux3 hF (swap_equivariant_aux2 hb) i x hx
    rw [ihb x hx, iha _ hbU]
  | inv a ha iha =>
    intro x hx
    change ((a : V ≃ₗ[F] V)⁻¹) (σ x) = σ (((a : V ≃ₗ[F] V)⁻¹) x)
    have h1 : (a : V ≃ₗ[F] V) (σ (((a : V ≃ₗ[F] V)⁻¹) x)) = σ x := by
      have hmem : ((a : V ≃ₗ[F] V)⁻¹) x ∈ U i :=
        swap_equivariant_aux3 hF (swap_equivariant_aux2 (Subgroup.inv_mem _ ha)) i x hx
      rw [iha ((a : V ≃ₗ[F] V)⁻¹ x) hmem]
      exact congrArg σ (LinearEquiv.apply_symm_apply (a : V ≃ₗ[F] V) x)
    exact ((a : V ≃ₗ[F] V).symm_apply_eq).mpr h1.symm

private theorem exists_isMixedFrame_aux1 {T : Subgroup ↥(orthDerived Q)}
    (hF : IsPlaneFrame Q p U ρ T) (k : Fin l) (n : ℕ) :
    ∀ x ∈ U k, ((ρ k : V ≃ₗ[F] V) ^ n) x ∈ U k := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih =>
    intro x hx
    rw [pow_succ, LinearEquiv.mul_apply]
    exact ih _ (hF.maps_to k x hx)

private theorem exists_isMixedFrame_aux2 (hU : IsPlaneSystem Q U) {σ : V ≃ₗ[F] V}
    (hσ : σ ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hσU : Submodule.map σ.toLinearMap (U i) = U j)
    (hF : IsPlaneFrame Q p U ρ (Subgroup.closure (Set.range ρ)))
    (hσρ : ∀ x ∈ U i, (ρ j : V ≃ₗ[F] V) (σ x) = σ ((ρ i : V ≃ₗ[F] V) x))
    (hij : i ≠ j) :
    ∃ W : Submodule F V, Module.finrank F W = 2 ∧ W ≠ ⊥ ∧ W ≤ U i ⊔ U j ∧
      (∀ x ∈ W, Q x = 0) ∧
      ∀ a ∈ Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j})),
        ∀ x ∈ W, (a : V ≃ₗ[F] V) x ∈ W := by
  have hAle : Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j})) ≤
      Subgroup.closure (Set.range ρ) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | ⟨k, -, rfl⟩)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩)
        (Subgroup.subset_closure ⟨j, rfl⟩)
    · exact Subgroup.subset_closure ⟨k, rfl⟩
  have hAi : ∀ a ∈ Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j})),
      ∀ x ∈ U i, (a : V ≃ₗ[F] V) x ∈ U i := by
    intro a ha x hx
    obtain ⟨n, hn⟩ := hF.exists_pow_apply_eq (hAle ha) i
    rw [hn x hx]
    exact exists_isMixedFrame_aux1 hF i n x hx
  obtain ⟨W, hW2, hWle, hWTS, hWinv⟩ :=
    exists_graph_plane hU hij hσ hσU hAi (swap_equivariant hij hF hσU hσρ)
  refine ⟨W, hW2, ?_, hWle, hWTS, hWinv⟩
  intro hbot
  have h0 : Module.finrank F W = 0 := by rw [hbot]; simp
  omega

theorem exists_isMixedFrame (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank F V = 2 * l) (hl : 4 ≤ l) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1)
    (htype : IsPlusType Q ↔ Even l) :
    ∃ (U : Fin l → Submodule F V) (ρ : Fin l → ↥(orthDerived Q)) (i j : Fin l) (A : Subgroup ↥(orthDerived Q)),
      IsMixedFrame Q p U ρ i j A ∧ ∃ T : Subgroup ↥(orthDerived Q), T ≠ ⊥ ∧ IsPGroup 2 T ∧
        A ≤ Subgroup.normalizer (T : Set ↥(orthDerived Q)) := by
  let i : Fin l := ⟨0, by omega⟩
  let j : Fin l := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, j] at hval
  obtain ⟨U, ρ, σ, hF, htop, hσ, hσU, hσρ⟩ :=
    exists_swapFrame hQ hdim hl hp hp2 hpq htype hij
  let A : Subgroup ↥(orthDerived Q) :=
    Subgroup.closure (insert (ρ i * ρ j) (ρ '' {k | k ≠ i ∧ k ≠ j}))
  obtain ⟨W, hW2, hWne, hWle, hWTS, hWinv⟩ :=
    exists_isMixedFrame_aux2 hF.toIsPlaneSystem hσ hσU hF hσρ hij
  have hMixed : IsMixedFrame Q p U ρ i j A :=
    { frame := hF
      iSup_eq_top := htop
      ne := hij
      eq_closure := rfl
      plane := ⟨W, hWne, hWle, hWTS, hWinv⟩ }
  obtain ⟨T, hTne, hT2, hTnorm⟩ := exists_twoGroup_of_totallySingular hQ hdim hl hW2 hWTS
  exact ⟨U, ρ, i, j, A, hMixed, T, hTne, hT2, fun a ha => hTnorm a (hWinv a ha)⟩

end CFSG.LocalAnalysis.GLTheoremA.T173M

end

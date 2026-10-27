module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieLTTwin

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

set_option linter.unusedSectionVars false

open CFSG.LieType.Universal.Spin CliffordAlgebra QuadraticMap
open CFSG.ClassicalInvolution.Generic
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.Universal (UniversalRootDatum LieUniversal)
open scoped MatrixGroups

namespace LTOrth

section Frame

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n)

noncomputable def signFlip {j k : Fin n} (hjk : j ≠ k) : spinGroup Q :=
  F.longWeyl hjk true true * F.longWeyl hjk true false

theorem spinAction_signFlip_vec_aux {j k : Fin n} (hjk : j ≠ k) :
    spinAction Q (signFlip F hjk) (F.vec j true) = -F.vec j false ∧
    spinAction Q (signFlip F hjk) (F.vec j false) = -F.vec j true ∧
    spinAction Q (signFlip F hjk) (F.vec k true) = -F.vec k false ∧
    spinAction Q (signFlip F hjk) (F.vec k false) = -F.vec k true := by
  have a1 := F.spinAction_longWeyl_vec_left hjk true false
  have a2 := F.spinAction_longWeyl_vec_left_not hjk true false
  have a3 := F.spinAction_longWeyl_vec_right_not hjk true false
  have a4 := F.spinAction_longWeyl_vec_right hjk true false
  have b1 := F.spinAction_longWeyl_vec_left hjk true true
  have b2 := F.spinAction_longWeyl_vec_left_not hjk true true
  have b3 := F.spinAction_longWeyl_vec_right_not hjk true true
  have b4 := F.spinAction_longWeyl_vec_right hjk true true
  simp only [Bool.not_true, Bool.not_false] at a1 a2 a3 a4 b1 b2 b3 b4
  unfold signFlip
  simp only [map_mul, LinearEquiv.mul_apply, map_neg, a1, a2, a3, a4, b1, b2, b3, b4, and_self]

theorem spinAction_signFlip_vec_left {j k : Fin n} (hjk : j ≠ k) (r : Bool) :
    spinAction Q (signFlip F hjk) (F.vec j r) = -F.vec j (!r) := by
  obtain ⟨h1, h2, -, -⟩ := spinAction_signFlip_vec_aux F hjk
  cases r
  · simpa using h2
  · simpa using h1

theorem spinAction_signFlip_vec_of_ne {j k m : Fin n} (hjk : j ≠ k) (hmj : m ≠ j) (hmk : m ≠ k)
    (r : Bool) : spinAction Q (signFlip F hjk) (F.vec m r) = F.vec m r := by
  unfold signFlip
  rw [map_mul, LinearEquiv.mul_apply, F.spinAction_longWeyl_vec_of_ne hjk true false hmj hmk,
    F.spinAction_longWeyl_vec_of_ne hjk true true hmj hmk]

theorem signFlip_conj_longRoot {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) (c : K) :
    signFlip F hjk * F.longRoot hij s t (.ofAdd c) * (signFlip F hjk)⁻¹ =
      F.longRoot hij s (!t) (.ofAdd (-c)) := by
  have h := F.conj_longRoot (signFlip F hjk) hij s t hij s (!t) (l := 1) (m := -1)
    (by rw [one_smul]; exact spinAction_signFlip_vec_of_ne F hjk hij hik s)
    (by rw [spinAction_signFlip_vec_left F hjk t, neg_smul, one_smul]) c
  rw [h]
  congr 2
  ring

theorem signFlip_conj_longRoot_neg {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) (c : K) :
    signFlip F hjk * F.longRoot hij.symm (!t) (!s) (.ofAdd c) * (signFlip F hjk)⁻¹ =
      F.longRoot hij.symm t (!s) (.ofAdd (-c)) := by
  have h := F.conj_longRoot (signFlip F hjk) hij.symm (!t) (!s) hij.symm t (!s) (l := -1) (m := 1)
    (by rw [spinAction_signFlip_vec_left F hjk (!t), Bool.not_not, neg_smul, one_smul])
    (by rw [one_smul]; exact spinAction_signFlip_vec_of_ne F hjk hij hik (!s)) c
  rw [h]
  congr 2
  ring

noncomputable def rankOneSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) : Subgroup (spinGroup Q) :=
  (F.longRoot hij s t).range ⊔ (F.longRoot hij.symm (!t) (!s)).range

theorem longSL2_mem_rankOneSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (M : Matrix.SpecialLinearGroup (Fin 2) K) : F.longSL2 hij s t M ∈ rankOneSL2 F hij s t := by
  refine (Subgroup.closure_le _).mpr ?_ (mem_closure_upperSL2_lowerSL2 (F.longSL2 hij s t) M)
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact Subgroup.mem_sup_left ⟨.ofAdd a, (F.longSL2_upperSL2 hij s t a).symm⟩
  · exact Subgroup.mem_sup_right ⟨.ofAdd a, (F.longSL2_lowerSL2 hij s t a).symm⟩

theorem range_longSL2_eq_rankOneSL2 {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    (F.longSL2 hij s t).range = rankOneSL2 F hij s t := by
  refine le_antisymm (fun x ⟨M, hM⟩ => hM ▸ longSL2_mem_rankOneSL2 F hij s t M) (sup_le ?_ ?_)
  · rintro _ ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective c
    exact ⟨upperSL2 a, F.longSL2_upperSL2 hij s t a⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective c
    exact ⟨lowerSL2 a, F.longSL2_lowerSL2 hij s t a⟩

theorem commute_of_sup {G : Type*} [Group G] {A B A' B' : Subgroup G}
    (h1 : ∀ a ∈ A, ∀ a' ∈ A', Commute a a') (h2 : ∀ a ∈ A, ∀ b' ∈ B', Commute a b')
    (h3 : ∀ b ∈ B, ∀ a' ∈ A', Commute b a') (h4 : ∀ b ∈ B, ∀ b' ∈ B', Commute b b') :
    ∀ x ∈ A ⊔ B, ∀ y ∈ A' ⊔ B', Commute x y := by
  have hgen : ∀ g : G, (∀ a' ∈ A', Commute g a') → (∀ b' ∈ B', Commute g b') →
      ∀ y ∈ A' ⊔ B', Commute g y := by
    intro g ha hb
    have : A' ⊔ B' ≤ Subgroup.centralizer ({g} : Set G) :=
      sup_le (fun a' h => Subgroup.mem_centralizer_singleton_iff.mpr (ha a' h).eq.symm)
        (fun b' h => Subgroup.mem_centralizer_singleton_iff.mpr (hb b' h).eq.symm)
    intro y hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm
  intro x hx y hy
  have : A ⊔ B ≤ Subgroup.centralizer ({y} : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
        (hgen a (h1 a ha) (h2 a ha) y hy).eq)
      (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
        (hgen b (h3 b hb) (h4 b hb) y hy).eq)
  exact Subgroup.mem_centralizer_singleton_iff.mp (this hx)

theorem commute_signFlip_rankOneSL2 {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) :
    ∀ a ∈ rankOneSL2 F hij s t, ∀ b ∈ rankOneSL2 F hij s t,
      Commute (signFlip F hjk * a * (signFlip F hjk)⁻¹) b := by
  have hconj : ∀ a ∈ rankOneSL2 F hij s t,
      signFlip F hjk * a * (signFlip F hjk)⁻¹ ∈
        (F.longRoot hij s (!t)).range ⊔ (F.longRoot hij.symm t (!s)).range := by
    have hle : rankOneSL2 F hij s t ≤ ((F.longRoot hij s (!t)).range ⊔
        (F.longRoot hij.symm t (!s)).range).comap (MulAut.conj (signFlip F hjk)).toMonoidHom := by
      refine sup_le ?_ ?_
      · rintro _ ⟨c, rfl⟩
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective c
        rw [Subgroup.mem_comap]
        change signFlip F hjk * _ * (signFlip F hjk)⁻¹ ∈ _
        rw [signFlip_conj_longRoot F hij hik hjk]
        exact Subgroup.mem_sup_left ⟨.ofAdd (-a), rfl⟩
      · rintro _ ⟨c, rfl⟩
        obtain ⟨a, rfl⟩ := Multiplicative.ofAdd.surjective c
        rw [Subgroup.mem_comap]
        change signFlip F hjk * _ * (signFlip F hjk)⁻¹ ∈ _
        rw [signFlip_conj_longRoot_neg F hij hik hjk]
        exact Subgroup.mem_sup_right ⟨.ofAdd (-a), rfl⟩
    exact fun a ha => hle ha
  have hswap : ∀ (s' t' : Bool) (c : K),
      F.longRoot hij s' t' (.ofAdd c) = F.longRoot hij.symm t' s' (.ofAdd (-c)) :=
    fun s' t' c => F.longRoot_swap hij s' t' c
  refine fun a ha b hb => commute_of_sup (A := (F.longRoot hij s (!t)).range)
    (B := (F.longRoot hij.symm t (!s)).range) (A' := (F.longRoot hij s t).range)
    (B' := (F.longRoot hij.symm (!t) (!s)).range) ?_ ?_ ?_ ?_ _ (hconj a ha) b hb
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective c
    obtain ⟨b', rfl⟩ := Multiplicative.ofAdd.surjective d
    exact F.commute_longRoot_longRoot_left hij hij s (!t) t a' b'
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective c
    obtain ⟨b', rfl⟩ := Multiplicative.ofAdd.surjective d
    rw [hswap]
    exact F.commute_longRoot_longRoot_left hij.symm hij.symm (!t) s (!s) _ b'
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective c
    obtain ⟨b', rfl⟩ := Multiplicative.ofAdd.surjective d
    rw [hswap s t b']
    exact F.commute_longRoot_longRoot_left hij.symm hij.symm t (!s) s a' _
  · rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    obtain ⟨a', rfl⟩ := Multiplicative.ofAdd.surjective c
    obtain ⟨b', rfl⟩ := Multiplicative.ofAdd.surjective d
    exact F.commute_longRoot_longRoot_right hij.symm hij.symm t (!s) (!t) a' b'

theorem inv_longRoot_ofAdd {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    (F.longRoot hij s t (.ofAdd c))⁻¹ = F.longRoot hij s t (.ofAdd (-c)) := by
  rw [← map_inv]
  rfl

theorem signFlip_mul_longWeyl_mul_inv {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) :
    signFlip F hjk * F.longWeyl hij s t * (signFlip F hjk)⁻¹ = (F.longWeyl hij s (!t))⁻¹ := by
  rw [F.longWeyl_eq hij s t, F.longWeyl_eq hij s (!t)]
  have e : ∀ a b c : spinGroup Q, signFlip F hjk * (a * b * c) * (signFlip F hjk)⁻¹ =
      (signFlip F hjk * a * (signFlip F hjk)⁻¹) * (signFlip F hjk * b * (signFlip F hjk)⁻¹) *
        (signFlip F hjk * c * (signFlip F hjk)⁻¹) := fun a b c => by group
  have e' : ∀ a b c : spinGroup Q, (a * b * c)⁻¹ = c⁻¹ * b⁻¹ * a⁻¹ := fun a b c => by group
  rw [e, signFlip_conj_longRoot F hij hik hjk, signFlip_conj_longRoot_neg F hij hik hjk, e']
  simp only [Bool.not_not, inv_longRoot_ofAdd, neg_neg]

theorem signFlip_conj_longTorus {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) :
    signFlip F hjk * F.longTorus hij s t (-1) * (signFlip F hjk)⁻¹ =
      (F.longTorus hij s (!t) (-1))⁻¹ := by
  rw [← F.longWeyl_mul_self hij s t, ← F.longWeyl_mul_self hij s (!t)]
  have h := signFlip_mul_longWeyl_mul_inv F hij hik hjk s t
  calc signFlip F hjk * (F.longWeyl hij s t * F.longWeyl hij s t) * (signFlip F hjk)⁻¹
      = (signFlip F hjk * F.longWeyl hij s t * (signFlip F hjk)⁻¹) *
        (signFlip F hjk * F.longWeyl hij s t * (signFlip F hjk)⁻¹) := by group
    _ = (F.longWeyl hij s (!t))⁻¹ * (F.longWeyl hij s (!t))⁻¹ := by rw [h]
    _ = (F.longWeyl hij s (!t) * F.longWeyl hij s (!t))⁻¹ := by group

theorem longTorus_neg_one_sq {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longTorus hij s t (-1) * F.longTorus hij s t (-1) = 1 := by
  rw [← map_mul]
  simp

theorem spinAction_longTorus_neg_one_not {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    spinAction Q (F.longTorus hij s (!t) (-1)) = spinAction Q (F.longTorus hij s t (-1)) := by
  ext v
  rw [F.spinAction_longTorus, F.spinAction_longTorus]
  simp only [Bool.not_not, Units.val_neg, Units.val_one, inv_neg, inv_one]
  module

theorem torus_twin_mem_ker {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (s t : Bool) :
    signFlip F hjk * F.longTorus hij s t (-1) * (signFlip F hjk)⁻¹ *
        (F.longTorus hij s t (-1))⁻¹ ∈ (spinAction Q).ker := by
  have hS : spinAction Q (F.longTorus hij s t (-1)) * spinAction Q (F.longTorus hij s t (-1)) =
      1 := by
    rw [← map_mul, longTorus_neg_one_sq F hij s t, map_one]
  rw [MonoidHom.mem_ker, signFlip_conj_longTorus F hij hik hjk, map_mul, map_inv, map_inv,
    spinAction_longTorus_neg_one_not F hij s t, ← mul_inv_rev, hS, inv_one]

theorem longTorus_neg_one_ne_one (h2 : (2 : K) ≠ 0) {i j : Fin n} (hij : i ≠ j) (s t : Bool) :
    F.longTorus hij s t (-1) ≠ 1 := by
  intro h
  have h1 := F.spinAction_longTorus_vec hij s t (-1) i s
  have hc : longCoroot i j s t i s = 1 := by simp [longCoroot, hij]
  rw [h, map_one, hc] at h1
  have h3 : F.vec i s + F.vec i s = 0 := by
    have : F.vec i s = -F.vec i s := by simpa using h1
    exact eq_neg_iff_add_eq_zero.mp this
  rw [← two_smul K] at h3
  rcases smul_eq_zero.mp h3 with h6 | h6
  · exact h2 h6
  · have := F.polar_vec_not i s
    rw [h6] at this
    simp at this

theorem exists_twin {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (s t : Bool) :
    (∀ a ∈ rankOneSL2 F hij s t, ∀ b ∈ rankOneSL2 F hij s t,
      Commute (signFlip F hjk * a * (signFlip F hjk)⁻¹) b) ∧
    signFlip F hjk * F.longTorus hij s t (-1) * (signFlip F hjk)⁻¹ *
        (F.longTorus hij s t (-1))⁻¹ ∈ Subgroup.center (spinGroup Q) :=
  ⟨commute_signFlip_rankOneSL2 F hij hik hjk s t,
    ker_spinAction_le_center Q (torus_twin_mem_ker F hij hik hjk s t)⟩

end Frame

section Datum

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  {Q : QuadraticForm (GaloisField 3 1) V} {m : ℕ} (F : HypFrame Q m)

theorem twin_of_datum {τ : StatedLieTag} {i j k : Fin m} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (s t : Bool) (D : UniversalRootDatum (spinGroup Q))
    (hsl2 : ∀ R ∈ fundamentalSubgroups τ D, Nonempty (R ≃* SL(2, GaloisField 3 1)))
    (hnc : ∀ R ∈ fundamentalSubgroups τ D, ∀ r ∈ R,
      (∀ y : spinGroup Q, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (spinGroup Q)) → r = 1)
    (hsingle : FundamentalSingleClass τ D) (hR₀ : rankOneSL2 F hij s t ∈ fundamentalSubgroups τ D)
    {X : Type} [Group X] (ψ : spinGroup Q →* X) (hker : ψ.ker = Subgroup.center (spinGroup Q)) :
    ∀ R ∈ fundamentalSubgroups τ D, ∀ u : X, u ∈ R.map ψ → orderOf u = 2 →
      ∃ w ∈ Subgroup.centralizer ({u} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
        a * (w * b * w⁻¹) = (w * b * w⁻¹) * a := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  obtain ⟨hcomm, hzw⟩ := exists_twin F hij hik hjk s t
  exact LTTwin.twin_of_family ψ hker (fundamentalSubgroups τ D) hsl2 hnc
    (R₀ := rankOneSL2 F hij s t) (fun R hR => hsingle _ hR₀ R hR)
    (z₀ := F.longTorus hij s t (-1)) (w₀ := signFlip F hjk)
    (by rw [F.longTorus_apply]; exact longSL2_mem_rankOneSL2 F hij s t _)
    (longTorus_neg_one_sq F hij s t) (longTorus_neg_one_ne_one F h2 hij s t) hzw hcomm

end Datum

@[expose] def TwinFor (τ : StatedLieTag) (M : LieUniversal) : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (ψ : M.K →* X), Function.Surjective ψ →
    ψ.ker = Subgroup.center _ → ∀ R ∈ fundamentalSubgroups τ M.D, ∀ u : X, u ∈ R.map ψ →
      orderOf u = 2 → ∃ w ∈ Subgroup.centralizer ({u} : Set X), ∀ a ∈ R.map ψ, ∀ b ∈ R.map ψ,
        a * (w * b * w⁻¹) = (w * b * w⁻¹) * a

end LTOrth

open CFSG.ClassicalInvolution.ModelFacts (nonempty_equiv_sl2_of_mem_fundamentalSubgroups
  fundNoncentral_generic fundamentalSingleClass isLongestRoot_single)
open CFSG.LieType.Universal.Spin (oddFrame oddDatum oddRootGroup rootB negRootB plusFrame plusDatum
  quadOdd quadPlus quadMinus)
open CFSG.LieType.Universal.Spin.Twisted (minusFrame minusDatum minusRootGroup
  rankOne_minusRootGroup_of_lt)
open CFSG.LieType.Universal (minusCoeffs minusCoeffs_irr lieUniversal)
open CFSG.LieType.CurtisTits (rankOne)


theorem LTOrth.kill3At_of_twinFor {τ : StatedLieTag} {n : ℕ}
    (h : LTOrth.TwinFor τ (modelUniv τ n 3 1 Nat.prime_three)) : Kill3At τ n :=
  fun X _ _ ψ hψ hker R hR t ht ht2 _ => Or.inl (h X ψ hψ hker R hR t ht ht2)

theorem kill3At_POmegaOdd (n : ℕ) (hn : 3 ≤ n) : Kill3At .POmegaOdd n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : IsFundTag .POmegaOdd := trivial
  have ha : StatedLieAdmissible .POmegaOdd n 3 1 := ⟨Nat.prime_three, le_rfl, hn, by norm_num⟩
  have hne : ¬ (StatedLieTag.POmegaOdd = .PSL ∧ n = 2) := fun h => by cases h.1
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D, Nonempty (R ≃* SL(2, GaloisField 3 1)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (e := 1) (by norm_num) hf
      ha (by decide) (by decide) hR
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D, ∀ r ∈ R,
        (∀ y : (modelUniv .POmegaOdd n 3 1 Nat.prime_three).K,
          r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center _) → r = 1 :=
    fun R hR r hr hc => fundNoncentral_generic 3 .POmegaOdd n 1 hf ha hne R hR r hr hc
  have hsingle : FundamentalSingleClass .POmegaOdd
      (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaOdd n 3 1 Nat.prime_three hf ha (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D.rank, k.val + 1 < n →
      IsLongestRoot (modelUniv .POmegaOdd n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaOdd n 3 1 Nat.prime_three hf ha k hk
  have hM : modelUniv .POmegaOdd n 3 1 Nat.prime_three =
      ⟨spinGroup (quadOdd n (GaloisField 3 1)), oddDatum n (GaloisField 3 1)⟩ := rfl
  refine LTOrth.kill3At_of_twinFor ?_
  rw [hM] at hsl2 hnc hsingle hlong ⊢
  intro X _ _ ψ hψ hker R hR u hu hu2
  let k₀ : Fin n := ⟨0, by omega⟩
  let j₀ : Fin n := ⟨1, by omega⟩
  let l₀ : Fin n := ⟨2, by omega⟩
  have hij : k₀ ≠ j₀ := fun h => by simpa [k₀, j₀] using congrArg Fin.val h
  have hik : k₀ ≠ l₀ := fun h => by simpa [k₀, l₀] using congrArg Fin.val h
  have hjk : j₀ ≠ l₀ := fun h => by simpa [j₀, l₀] using congrArg Fin.val h
  have hk₀ : k₀.val + 1 < n := by show 0 + 1 < n; omega
  have hR₀ : LTOrth.rankOneSL2 (oddFrame n (GaloisField 3 1)).toHypFrame hij true false ∈
      fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField 3 1)) := by
    refine ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ hk₀), ?_⟩
    show _ = conjSub 1 (oddRootGroup n (GaloisField 3 1) (Pi.single k₀ 1) ⊔
      oddRootGroup n (GaloisField 3 1) (-Pi.single k₀ 1))
    rw [conjSub_one, oddRootGroup_single, oddRootGroup_neg_single,
      rootB_of_lt (GaloisField 3 1) hk₀ (j := j₀) rfl hij,
      negRootB_of_lt (GaloisField 3 1) hk₀ (j := j₀) rfl hij.symm]
    rfl
  exact LTOrth.twin_of_datum (oddFrame n (GaloisField 3 1)).toHypFrame hij hik hjk true false
    (oddDatum n (GaloisField 3 1)) hsl2 hnc hsingle hR₀ ψ hker R hR u hu hu2

theorem kill3At_POmegaPlus (n : ℕ) (hn : 4 ≤ n) : Kill3At .POmegaPlus n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn3 : 3 ≤ n := by omega
  have hf : IsFundTag .POmegaPlus := trivial
  have ha : StatedLieAdmissible .POmegaPlus n 3 1 := ⟨Nat.prime_three, le_rfl, hn⟩
  have hne : ¬ (StatedLieTag.POmegaPlus = .PSL ∧ n = 2) := fun h => by cases h.1
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D, Nonempty (R ≃* SL(2, GaloisField 3 1)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (e := 1) (by norm_num) hf
      ha (by decide) (by decide) hR
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D, ∀ r ∈ R,
        (∀ y : (modelUniv .POmegaPlus n 3 1 Nat.prime_three).K,
          r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center _) → r = 1 :=
    fun R hR r hr hc => fundNoncentral_generic 3 .POmegaPlus n 1 hf ha hne R hR r hr hc
  have hsingle : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaPlus n 3 1 Nat.prime_three hf ha (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k => isLongestRoot_single .POmegaPlus n 3 1 Nat.prime_three hf ha k trivial
  have hM : modelUniv .POmegaPlus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadPlus n (GaloisField 3 1)), plusDatum n (GaloisField 3 1) hn3⟩ := by
    simp only [modelUniv, lieUniversal, hn3, ↓reduceDIte]
  refine LTOrth.kill3At_of_twinFor ?_
  rw [hM] at hsl2 hnc hsingle hlong ⊢
  intro X _ _ ψ hψ hker R hR u hu hu2
  let k₀ : Fin n := ⟨0, by omega⟩
  have hij := rootIdxD_ne n (by omega : 2 ≤ n) k₀
  obtain ⟨l₀, hl1, hl2⟩ := exists_ne_and_ne hn3 (rootIdxD n k₀) (rootIdxD' n k₀)
  have hR₀ : LTOrth.rankOneSL2 (plusFrame n (GaloisField 3 1) hn3) hij true (rootSignD n k₀) ∈
      fundamentalSubgroups .POmegaPlus (plusDatum n (GaloisField 3 1) hn3) := by
    refine ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀), ?_⟩
    show _ = conjSub 1 (rankOne (plusRootGroup n (GaloisField 3 1) hn3) k₀)
    rw [conjSub_one, CFSG.LieType.Universal.Spin.PlusCT.rankOne_plusRootGroup hn3 k₀]
    exact (LTOrth.range_longSL2_eq_rankOneSL2 (plusFrame n (GaloisField 3 1) hn3) hij true
      (rootSignD n k₀)).symm
  exact LTOrth.twin_of_datum (plusFrame n (GaloisField 3 1) hn3) hij hl1.symm hl2.symm true
    (rootSignD n k₀) (plusDatum n (GaloisField 3 1) hn3) hsl2 hnc hsingle hR₀ ψ hker R hR u hu hu2

theorem kill3At_POmegaMinus (n : ℕ) (hn : 4 ≤ n) : Kill3At .POmegaMinus n := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : IsFundTag .POmegaMinus := trivial
  have ha : StatedLieAdmissible .POmegaMinus n 3 1 := ⟨Nat.prime_three, le_rfl, hn⟩
  have hne : ¬ (StatedLieTag.POmegaMinus = .PSL ∧ n = 2) := fun h => by cases h.1
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D, Nonempty (R ≃* SL(2, GaloisField 3 1)) :=
    fun R hR => nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (e := 1) (by norm_num) hf
      ha (by decide) (by decide) hR
  have hnc : ∀ R ∈ fundamentalSubgroups .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D, ∀ r ∈ R,
        (∀ y : (modelUniv .POmegaMinus n 3 1 Nat.prime_three).K,
          r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center _) → r = 1 :=
    fun R hR r hr hc => fundNoncentral_generic 3 .POmegaMinus n 1 hf ha hne R hR r hr hc
  have hsingle : FundamentalSingleClass .POmegaMinus
      (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D :=
    fundamentalSingleClass .POmegaMinus n 3 1 Nat.prime_three hf ha (by decide) (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D.rank, k.val + 2 < n →
      IsLongestRoot (modelUniv .POmegaMinus n 3 1 Nat.prime_three).D (Pi.single k 1) :=
    fun k hk => isLongestRoot_single .POmegaMinus n 3 1 Nat.prime_three hf ha k hk
  have hirr := minusCoeffs_irr 3 1
  have hM : modelUniv .POmegaMinus n 3 1 Nat.prime_three =
      ⟨spinGroup (quadMinus n (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
        minusDatum n hirr⟩ := by
    simp only [modelUniv, lieUniversal]
  refine LTOrth.kill3At_of_twinFor ?_
  rw [hM] at hsl2 hnc hsingle hlong ⊢
  intro X _ _ ψ hψ hker R hR u hu hu2
  have hk₀ : (0 : ℕ) + 1 < n - 1 := by omega
  let k₀ : Fin (n - 1) := ⟨0, by omega⟩
  let j₀ : Fin (n - 1) := ⟨k₀.val + 1, hk₀⟩
  let l₀ : Fin (n - 1) := ⟨2, by omega⟩
  have hij : k₀ ≠ j₀ := fun h => by simpa [k₀, j₀] using congrArg Fin.val h
  have hik : k₀ ≠ l₀ := fun h => by simpa [k₀, l₀] using congrArg Fin.val h
  have hjk : j₀ ≠ l₀ := fun h => by simpa [k₀, j₀, l₀] using congrArg Fin.val h
  have hR₀ : LTOrth.rankOneSL2 (minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame
      hij true false ∈ fundamentalSubgroups .POmegaMinus (minusDatum n hirr) := by
    refine ⟨1, Pi.single k₀ 1, Or.inl (hlong k₀ (by show 0 + 2 < n; omega)), ?_⟩
    show _ = conjSub 1 (rankOne (minusRootGroup n hirr) k₀)
    rw [conjSub_one, rankOne_minusRootGroup_of_lt n hirr hk₀]
    exact (LTOrth.range_longSL2_eq_rankOneSL2
      (minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame hij true false).symm
  exact LTOrth.twin_of_datum
    (minusFrame n (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame hij hik hjk true false
    (minusDatum n hirr) hsl2 hnc hsingle hR₀ ψ hker R hR u hu hu2

end CFSG.CGT.PushingUpLit.SolKNA

module

public import CFSG.RankThree.OrthogonalInvolutions.Dickson
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Rank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2SpComm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Module

section Two

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eq_add_smul_of_not_mem {W : Submodule K V} (hW : finrank K W = 2) {u y : V}
    (hu : u ∈ W) (hy : y ∈ W) (hu0 : u ≠ 0) (hyu : ∀ c : K, y ≠ c • u) :
    ∀ w ∈ W, ∃ s t : K, w = s • u + t • y := by
  have hli : LinearIndependent K ![u, y] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right hu0, rfl⟩
    · exfalso
      apply hyu (-(t⁻¹ * s))
      have h1 : t • y = -(s • u) := eq_neg_of_add_eq_zero_right hst
      calc y = t⁻¹ • (t • y) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = (-(t⁻¹ * s)) • u := by rw [h1, smul_neg, smul_smul, neg_smul]
  have : FiniteDimensional K W := Module.finite_of_finrank_eq_succ hW
  have hle : Submodule.span K (Set.range ![u, y]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hu
    · exact hy
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_eq_card hli, hW]; rfl)
  intro w hw
  rw [← heq, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨c, hc⟩ := hw
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  rfl

variable (hK : Nat.card K = 2)
include hK

theorem two_smul_eq_zero_of_card (v : V) : v + v = 0 := by
  have : CharP K 2 := charP_two_of_card hK
  exact two_smul_eq_zero K v

theorem eq_of_add_eq_zero_of_card {a b : V} (h : a + b = 0) : a = b := by
  have h2 := two_smul_eq_zero_of_card hK b
  rw [← add_zero a, ← h2, ← add_assoc, h, zero_add]

theorem eq_of_commute_of_cyc3 {W : Submodule K V} (hW : finrank K W = 2) {X G : V →ₗ[K] V}
    (hXW : ∀ w ∈ W, X w ∈ W) (hGW : ∀ w ∈ W, G w ∈ W)
    (hX : ∀ w ∈ W, X (X w) + X w + w = 0) (hGX : ∀ w ∈ W, G (X w) = X (G w))
    (hGinj : ∀ w ∈ W, G w = 0 → w = 0) {k : ℕ} (hk : Nat.Coprime 3 k)
    (hGk : ∀ w ∈ W, (G ^ k) w = w) : ∀ w ∈ W, G w = w := by
  have h2 : ∀ v : V, v + v = 0 := two_smul_eq_zero_of_card hK
  have hXX : ∀ w ∈ W, X (X w) = X w + w := fun w hw =>
    eq_of_add_eq_zero_of_card hK (by rw [← add_assoc]; exact hX w hw)
  have hX3 : ∀ w ∈ W, X (X (X w)) = w := fun w hw => by
    rw [hXX w hw, map_add, hXX w hw, add_comm (X w) w, add_assoc, h2, add_zero]
  obtain ⟨w₀, hw₀, hw₀0⟩ : ∃ w ∈ W, w ≠ 0 := by
    have : W ≠ ⊥ := fun h => by rw [h, finrank_bot] at hW; omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hXw₀ : ∀ c : K, X w₀ ≠ c • w₀ := by
    intro c hc
    rcases eq_zero_or_one_of_card hK c with rfl | rfl
    · rw [zero_smul] at hc
      have h := hXX w₀ hw₀
      rw [hc, map_zero, zero_add] at h
      exact hw₀0 h.symm
    · rw [one_smul] at hc
      have h := hX w₀ hw₀
      rw [hc, hc, h2, zero_add] at h
      exact hw₀0 h
  have hbasis := eq_add_smul_of_not_mem hW hw₀ (hXW w₀ hw₀) hw₀0 hXw₀
  obtain ⟨a, b, hab⟩ := hbasis _ (hGW w₀ hw₀)
  have hGform : ∀ w ∈ W, G w = a • w + b • X w := by
    intro w hw
    obtain ⟨s, t, rfl⟩ := hbasis w hw
    simp only [map_add, map_smul, hGX w₀ hw₀, hab]
    module
  have hG3 : ∀ w ∈ W, G (G (G w)) = w := by
    intro w hw
    have hXw := hXW w hw
    have hXXw := hXW _ hXw
    rcases eq_zero_or_one_of_card hK a with rfl | rfl <;>
      rcases eq_zero_or_one_of_card hK b with rfl | rfl
    · exfalso
      apply hw₀0
      refine hGinj w₀ hw₀ ?_
      rw [hab, zero_smul, zero_smul, add_zero]
    · have hG : ∀ v ∈ W, G v = X v := fun v hv => by
        rw [hGform v hv, zero_smul, one_smul, zero_add]
      rw [hG w hw, hG _ hXw, hG _ hXXw, hX3 w hw]
    · have hG : ∀ v ∈ W, G v = v := fun v hv => by
        rw [hGform v hv, zero_smul, one_smul, add_zero]
      rw [hG w hw, hG w hw, hG w hw]
    · have hG : ∀ v ∈ W, G v = X (X v) := fun v hv => by
        rw [hGform v hv, one_smul, one_smul, hXX v hv, add_comm]
      rw [hG w hw, hG _ hXXw, hX3 _ hXw, hG _ hXw, hX3 w hw]
  have hiter : ∀ (n : ℕ), ∀ w ∈ W, (G ^ n) w ∈ W := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply]
      exact hGW _ (ih w hw)
  have hpow3 : ∀ (j : ℕ), ∀ w ∈ W, (G ^ (3 * j)) w = w := by
    intro j
    induction j with
    | zero => intro w _; simp
    | succ j ih =>
      intro w hw
      rw [show 3 * (j + 1) = 3 * j + 3 by ring, pow_add, Module.End.mul_apply, pow_three,
        Module.End.mul_apply, Module.End.mul_apply, hG3 w hw]
      exact ih w hw
  have hpowk : ∀ (m : ℕ), ∀ w ∈ W, (G ^ (k * m)) w = w := by
    intro m
    induction m with
    | zero => intro w _; simp
    | succ m ih =>
      intro w hw
      rw [mul_add, mul_one, pow_add, Module.End.mul_apply, hGk w hw]
      exact ih w hw
  have hk3 : k % 3 = 1 ∨ k % 3 = 2 := by
    have h0 : k % 3 ≠ 0 := by
      intro h0
      have := Nat.Coprime.eq_one_of_dvd hk (Nat.dvd_of_mod_eq_zero h0)
      norm_num at this
    omega
  obtain ⟨j, hj⟩ : ∃ j, k * (k % 3) = 3 * j + 1 := by
    refine ⟨k * (k % 3) / 3, ?_⟩
    have : k * (k % 3) % 3 = 1 := by
      rcases hk3 with h | h <;> rw [Nat.mul_mod, h]
    omega
  intro w hw
  have h1 := hpowk (k % 3) w hw
  rw [hj, pow_succ, Module.End.mul_apply, hpow3 j (G w) (hGW w hw)] at h1
  exact h1

theorem cyc3_of_no_fixed {W : Submodule K V} (hW : finrank K W = 2) {G : V →ₗ[K] V}
    (hGW : ∀ w ∈ W, G w ∈ W) (hGinj : ∀ w ∈ W, G w = 0 → w = 0)
    (hfix : ∀ w ∈ W, G w = w → w = 0) : ∀ w ∈ W, G (G w) + G w + w = 0 := by
  have h2 : ∀ v : V, v + v = 0 := two_smul_eq_zero_of_card hK
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero, map_zero, add_zero, add_zero]
  have hGw := hGW w hw
  have hGGw := hGW _ hGw
  have hne : ∀ c : K, G w ≠ c • w := by
    intro c hc
    rcases eq_zero_or_one_of_card hK c with rfl | rfl
    · rw [zero_smul] at hc
      exact hw0 (hGinj w hw hc)
    · rw [one_smul] at hc
      exact hw0 (hfix w hw hc)
  obtain ⟨a, b, hab⟩ := eq_add_smul_of_not_mem hW hw hGw hw0 hne _ hGGw
  rcases eq_zero_or_one_of_card hK a with rfl | rfl <;>
    rcases eq_zero_or_one_of_card hK b with rfl | rfl
  · rw [zero_smul, zero_smul, add_zero] at hab
    exact absurd (hGinj w hw (hGinj _ hGw hab)) hw0
  · rw [zero_smul, one_smul, zero_add] at hab
    exact absurd (hGinj w hw (hfix _ hGw hab)) hw0
  · rw [one_smul, zero_smul, add_zero] at hab
    exfalso
    have h1 : G (w + G w) = w + G w := by rw [map_add, hab, add_comm]
    have h3 := hfix _ (W.add_mem hw hGw) h1
    exact hw0 (hfix w hw (eq_of_add_eq_zero_of_card hK h3).symm)
  · rw [one_smul, one_smul] at hab
    rw [hab, add_assoc w, h2, add_zero, h2]

end Two

section Dickson

variable {K : Type*} [Field K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

open CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.Classical2 in
theorem even_finrank_commSpace_of_mem_orthDerived
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q) :
    Even (finrank K (commSpace g)) := by
  have hle : orthDerived Q ≤ omegaGroup Q hQ := by
    rw [orthDerived, Subgroup.commutator_le]
    intro a ha b hb
    set a' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨a, ha⟩
    set b' : TauCeti.QuadraticMap.orthogonalGroup Q := ⟨b, hb⟩
    have hker : a' * b' * a'⁻¹ * b'⁻¹ ∈ (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker, ← commutatorElement_def, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hker
    rw [commutatorElement_def]
    exact hker
  exact (hle hg).2

end Dickson

section Group

theorem exists_mulEquiv_z3_two {G : Type*} [CommGroup G] [Finite G] (h3 : ∀ g : G, g ^ 3 = 1)
    (hc : Nat.card G = 9) : Nonempty (G ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  have : Fintype G := Fintype.ofFinite G
  have h : ∀ x : Additive G, (3 : ℕ) • x = 0 := fun x => h3 (Additive.toMul x)
  let _ : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule h
  have hcard : Fintype.card (Additive G) = Fintype.card (ZMod 3) ^ finrank (ZMod 3) (Additive G) :=
    Module.card_eq_pow_finrank
  have hfr : finrank (ZMod 3) (Additive G) = 2 := by
    rw [ZMod.card, Fintype.card_additive, ← Nat.card_eq_fintype_card, hc] at hcard
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hcard :
        3 ^ 2 = 3 ^ finrank (ZMod 3) (Additive G)) |>.symm
  let b := Module.finBasisOfFinrankEq (ZMod 3) (Additive G) hfr
  let e : Additive G ≃+ (Fin 2 → ZMod 3) := b.equivFun.toAddEquiv
  exact ⟨{ toFun := fun g => Multiplicative.ofAdd (e (Additive.ofMul g))
           invFun := fun z => Additive.toMul (e.symm (Multiplicative.toAdd z))
           left_inv := fun g => by simp
           right_inv := fun z => by simp
           map_mul' := fun g h => by simp [ofAdd_add] }⟩

end Group

end CFSG.HardMathSupport.Timmesfeld.CrossChar

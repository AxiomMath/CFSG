module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivM12
public import CFSG.RankThree.PartOne.KS.J2FiveStructure
public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import Certificates.Certificate15083

public section

namespace CFSG.ComponentClassification.AS81.Sec2

open Subgroup CFSG.Open CFSG.ABGLocalTools

theorem j2Norm_check : j2NormCheck = true :=
  Certificates.certificate15083

@[expose] def fiveTau (v : Fin 5 × Fin 5) : Fin 5 × Fin 5 := (-v.2, v.1 - v.2)

@[expose] def fiveSmul (k : Fin 5) (v : Fin 5 × Fin 5) : Fin 5 × Fin 5 := (k * v.1, k * v.2)

theorem eq_of_fiveOrbit {f : Fin 5 → Fin 5 → ℕ}
    (hk : ∀ i j k : Fin 5, k ≠ 0 → f (k * i) (k * j) = f i j)
    (hτ : ∀ i j, f (-j) (i - j) = f i j) (k : Fin 5) (hk0 : k ≠ 0) (n : ℕ)
    (r v : Fin 5 × Fin 5) (hv : v = fiveSmul k (fiveTau^[n] r)) : f v.1 v.2 = f r.1 r.2 := by
  subst hv
  rw [fiveSmul, hk _ _ k hk0]
  clear hk0
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    rw [ih (fiveTau r)]
    exact hτ r.1 r.2

theorem false_of_fiveOrbit_sum (f : Fin 5 → Fin 5 → ℕ) (h00 : f 0 0 = 256)
    (hval : ∀ i j, ¬ (i = 0 ∧ j = 0) → f i j = 1 ∨ f i j = 16)
    (hk : ∀ i j k : Fin 5, k ≠ 0 → f (k * i) (k * j) = f i j)
    (hτ : ∀ i j, f (-j) (i - j) = f i j)
    (hsum : 25 ∣ ∑ i, ∑ j, f i j) : False := by
  have e01 : f 0 1 = f 1 0 := eq_of_fiveOrbit hk hτ 1 (by decide) 1 (1, 0) (0, 1) (by decide)
  have e02 : f 0 2 = f 1 0 := eq_of_fiveOrbit hk hτ 2 (by decide) 1 (1, 0) (0, 2) (by decide)
  have e03 : f 0 3 = f 1 0 := eq_of_fiveOrbit hk hτ 3 (by decide) 1 (1, 0) (0, 3) (by decide)
  have e04 : f 0 4 = f 1 0 := eq_of_fiveOrbit hk hτ 4 (by decide) 1 (1, 0) (0, 4) (by decide)
  have e10 : f 1 0 = f 1 0 := eq_of_fiveOrbit hk hτ 1 (by decide) 0 (1, 0) (1, 0) (by decide)
  have e11 : f 1 1 = f 1 0 := eq_of_fiveOrbit hk hτ 4 (by decide) 2 (1, 0) (1, 1) (by decide)
  have e12 : f 1 2 = f 1 2 := eq_of_fiveOrbit hk hτ 1 (by decide) 0 (1, 2) (1, 2) (by decide)
  have e13 : f 1 3 = f 1 2 := eq_of_fiveOrbit hk hτ 2 (by decide) 1 (1, 2) (1, 3) (by decide)
  have e14 : f 1 4 = f 1 2 := eq_of_fiveOrbit hk hτ 1 (by decide) 2 (1, 2) (1, 4) (by decide)
  have e20 : f 2 0 = f 1 0 := eq_of_fiveOrbit hk hτ 2 (by decide) 0 (1, 0) (2, 0) (by decide)
  have e21 : f 2 1 = f 1 2 := eq_of_fiveOrbit hk hτ 4 (by decide) 1 (1, 2) (2, 1) (by decide)
  have e22 : f 2 2 = f 1 0 := eq_of_fiveOrbit hk hτ 3 (by decide) 2 (1, 0) (2, 2) (by decide)
  have e23 : f 2 3 = f 1 2 := eq_of_fiveOrbit hk hτ 2 (by decide) 2 (1, 2) (2, 3) (by decide)
  have e24 : f 2 4 = f 1 2 := eq_of_fiveOrbit hk hτ 2 (by decide) 0 (1, 2) (2, 4) (by decide)
  have e30 : f 3 0 = f 1 0 := eq_of_fiveOrbit hk hτ 3 (by decide) 0 (1, 0) (3, 0) (by decide)
  have e31 : f 3 1 = f 1 2 := eq_of_fiveOrbit hk hτ 3 (by decide) 0 (1, 2) (3, 1) (by decide)
  have e32 : f 3 2 = f 1 2 := eq_of_fiveOrbit hk hτ 3 (by decide) 2 (1, 2) (3, 2) (by decide)
  have e33 : f 3 3 = f 1 0 := eq_of_fiveOrbit hk hτ 2 (by decide) 2 (1, 0) (3, 3) (by decide)
  have e34 : f 3 4 = f 1 2 := eq_of_fiveOrbit hk hτ 1 (by decide) 1 (1, 2) (3, 4) (by decide)
  have e40 : f 4 0 = f 1 0 := eq_of_fiveOrbit hk hτ 4 (by decide) 0 (1, 0) (4, 0) (by decide)
  have e41 : f 4 1 = f 1 2 := eq_of_fiveOrbit hk hτ 4 (by decide) 2 (1, 2) (4, 1) (by decide)
  have e42 : f 4 2 = f 1 2 := eq_of_fiveOrbit hk hτ 3 (by decide) 1 (1, 2) (4, 2) (by decide)
  have e43 : f 4 3 = f 1 2 := eq_of_fiveOrbit hk hτ 4 (by decide) 0 (1, 2) (4, 3) (by decide)
  have e44 : f 4 4 = f 1 0 := eq_of_fiveOrbit hk hτ 1 (by decide) 2 (1, 0) (4, 4) (by decide)
  simp only [Fin.sum_univ_five] at hsum
  rw [h00, e01, e02, e03, e04, e10, e11, e12, e13, e14, e20, e21, e22, e23, e24, e30, e31, e32,
    e33, e34, e40, e41, e42, e43, e44] at hsum
  rcases hval 1 0 (by decide) with h1 | h1 <;> rcases hval 1 2 (by decide) with h2 | h2 <;>
    rw [h1, h2] at hsum <;> norm_num at hsum

section Aut

variable {M : Type} [Group M]

@[expose] def autFix (σ : MulAut M) : Subgroup M :=
  MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id M)

theorem mem_autFix {σ : MulAut M} {w : M} : w ∈ autFix σ ↔ σ w = w := Iff.rfl

theorem autPow_apply_of_fixed {σ : MulAut M} {w : M} (h : σ w = w) : ∀ n : ℕ, (σ ^ n) w = w
  | 0 => rfl
  | n + 1 => by rw [pow_succ, MulAut.mul_apply, h, autPow_apply_of_fixed h n]

theorem autFix_pow {σ : MulAut M} (h5 : σ ^ 5 = 1) {k : ℕ} (hk : k % 5 ≠ 0) :
    autFix (σ ^ k) = autFix σ := by
  ext w
  rw [mem_autFix, mem_autFix]
  constructor
  · intro h
    obtain ⟨m, hm⟩ : ∃ m, (k * m) % 5 = 1 := by
      have : k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
      rcases this with h1 | h1 | h1 | h1
      · exact ⟨1, by omega⟩
      · exact ⟨3, by omega⟩
      · exact ⟨2, by omega⟩
      · exact ⟨4, by omega⟩
    have e : σ = (σ ^ k) ^ m := by
      rw [← pow_mul, pow_eq_pow_mod (k * m) h5, hm, pow_one]
    rw [e]
    exact autPow_apply_of_fixed h m
  · intro h
    exact autPow_apply_of_fixed h k

theorem card_autFix_conj (γ σ : MulAut M) :
    Nat.card (autFix (γ * σ * γ⁻¹)) = Nat.card (autFix σ) := by
  have hto : ∀ w : M, (γ * σ * γ⁻¹) w = w → σ (γ⁻¹ w) = γ⁻¹ w := fun w h => by
    rw [MulAut.mul_apply, MulAut.mul_apply] at h
    have := congrArg (fun x => (γ⁻¹ : MulAut M) x) h
    simpa using this
  have hinv : ∀ w : M, σ w = w → (γ * σ * γ⁻¹) (γ w) = γ w := fun w h => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h]
  exact Nat.card_congr
    { toFun := fun w => ⟨γ⁻¹ w, hto w w.2⟩
      invFun := fun w => ⟨γ w, hinv w w.2⟩
      left_inv := fun w => Subtype.ext (by simp)
      right_inv := fun w => Subtype.ext (by simp) }

theorem card_autFix_of_pow_five [Finite M] (hM : Nat.card M = 256) {σ : MulAut M}
    (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) : Nat.card (autFix σ) = 1 ∨ Nat.card (autFix σ) = 16 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : Nat.card (autFix σ) ∣ 2 ^ 8 := by
    rw [show (2 : ℕ) ^ 8 = 256 by norm_num, ← hM]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨k, hk8, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hp : IsPGroup 5 (Subgroup.zpowers σ) := by
    have h := orderOf_dvd_of_pow_eq_one h5
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h' | h'
    · exact IsPGroup.of_card (p := 5) (n := 0) (by rw [Nat.card_zpowers, h', pow_zero])
    · exact IsPGroup.of_card (p := 5) (n := 1) (by rw [Nat.card_zpowers, h', pow_one])
  have hmod := hp.card_modEq_card_fixedPoints M
  have hfix : MulAction.fixedPoints (Subgroup.zpowers σ) M = (autFix σ : Set M) := by
    ext w
    simp only [MulAction.mem_fixedPoints, SetLike.mem_coe, mem_autFix]
    constructor
    · intro h
      exact h ⟨σ, Subgroup.mem_zpowers σ⟩
    · intro h g
      have hst : Subgroup.zpowers σ ≤ MulAction.stabilizer (MulAut M) w :=
        Subgroup.zpowers_le.mpr h
      exact hst g.2
  rw [hfix] at hmod
  change Nat.card M ≡ Nat.card (autFix σ) [MOD 5] at hmod
  rw [hM, hk] at hmod
  have h2k : 2 ^ k % 5 = 1 := by
    have := hmod.symm
    unfold Nat.ModEq at this
    omega
  have hk8' : k ≠ 8 := by
    rintro rfl
    apply h1
    have htop : autFix σ = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hM]; norm_num)
    refine MulEquiv.ext fun w => ?_
    have hw : w ∈ autFix σ := htop ▸ Subgroup.mem_top w
    exact hw
  rw [hk]
  interval_cases k <;> simp_all


theorem false_of_aut_five_three [Finite M] (hM : Nat.card M = 256) {α β γ : MulAut M}
    (hα5 : α ^ 5 = 1) (hβ5 : β ^ 5 = 1) (hαβ : α * β = β * α)
    (hind : ∀ i j : ℕ, i < 5 → j < 5 → α ^ i * β ^ j = 1 → i = 0 ∧ j = 0)
    (hγα : γ * α * γ⁻¹ = β) (hγβ : γ * β * γ⁻¹ = (α * β)⁻¹) : False := by
  classical
  have hc : Commute α β := hαβ
  have hnf : ∀ a b c d : ℕ, a % 5 = c % 5 → b % 5 = d % 5 →
      α ^ a * β ^ b = α ^ c * β ^ d := by
    intro a b c d h1 h2
    rw [pow_eq_pow_mod a hα5, pow_eq_pow_mod b hβ5, pow_eq_pow_mod c hα5,
      pow_eq_pow_mod d hβ5, h1, h2]
  have hmul : ∀ a b c d : ℕ, α ^ a * β ^ b * (α ^ c * β ^ d) = α ^ (a + c) * β ^ (b + d) := by
    intro a b c d
    have h := (hc.pow_pow c b).eq
    rw [pow_add, pow_add]
    calc α ^ a * β ^ b * (α ^ c * β ^ d) = α ^ a * (β ^ b * α ^ c) * β ^ d := by group
      _ = α ^ a * (α ^ c * β ^ b) * β ^ d := by rw [h]
      _ = α ^ a * α ^ c * (β ^ b * β ^ d) := by group
  let e : Fin 5 × Fin 5 → MulAut M := fun v => α ^ (v.1 : ℕ) * β ^ (v.2 : ℕ)
  have he_inv : ∀ v : Fin 5 × Fin 5, (e v)⁻¹ = e (-v) := by
    intro v
    refine inv_eq_of_mul_eq_one_left ?_
    simp only [e, Prod.fst_neg, Prod.snd_neg]
    rw [hmul, hnf _ _ 0 0 (by rw [Fin.val_neg']; omega) (by rw [Fin.val_neg']; omega), pow_zero,
      pow_zero, one_mul]
  have he_mul : ∀ v w : Fin 5 × Fin 5, e v * e w = e (v + w) := by
    intro v w
    simp only [e, Prod.fst_add, Prod.snd_add]
    rw [hmul, hnf ((v.1 : ℕ) + w.1) ((v.2 : ℕ) + w.2) ((v.1 + w.1 : Fin 5) : ℕ)
      ((v.2 + w.2 : Fin 5) : ℕ) (by rw [Fin.val_add]; omega) (by rw [Fin.val_add]; omega)]
  have he_inj : Function.Injective e := by
    intro v w h
    have h1 : e (v + -w) = 1 := by rw [← he_mul, ← he_inv, h, mul_inv_cancel]
    obtain ⟨h1', h2'⟩ := hind _ _ (v + -w).1.2 (v + -w).2.2 h1
    have e1 : v.1 = w.1 := by
      have := congrArg Fin.val (show (v + -w).1 = 0 from Fin.ext h1')
      simp only [Prod.fst_add, Prod.fst_neg] at this
      rw [Fin.val_add, Fin.val_neg'] at this
      exact Fin.ext (by omega)
    have e2 : v.2 = w.2 := by
      have := congrArg Fin.val (show (v + -w).2 = 0 from Fin.ext h2')
      simp only [Prod.snd_add, Prod.snd_neg] at this
      rw [Fin.val_add, Fin.val_neg'] at this
      exact Fin.ext (by omega)
    exact Prod.ext e1 e2
  have he_pow : ∀ (v : Fin 5 × Fin 5) (k : ℕ),
      e v ^ k = α ^ ((v.1 : ℕ) * k) * β ^ ((v.2 : ℕ) * k) :=
    fun v k => by
      simp only [e]
      rw [(hc.pow_pow _ _).mul_pow, ← pow_mul, ← pow_mul]
  have he5 : ∀ v, e v ^ 5 = 1 := fun v => by
    rw [he_pow, hnf _ _ 0 0 (by omega) (by omega), pow_zero, pow_zero, one_mul]
  let A := Subgroup.closure ({α, β} : Set (MulAut M))
  have hαA : α ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hβA : β ∈ A := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hmemA : ∀ v, e v ∈ A := fun v => A.mul_mem (A.pow_mem hαA _) (A.pow_mem hβA _)
  have hsurj : ∀ x ∈ A, ∃ v, e v = x := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨(1, 0), by simp [e]⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨(0, 1), by simp [e]⟩
    | one => exact ⟨0, by simp [e]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨v, rfl⟩ := hx
      obtain ⟨w, rfl⟩ := hy
      exact ⟨v + w, (he_mul v w).symm⟩
    | inv x _ hx =>
      obtain ⟨v, rfl⟩ := hx
      exact ⟨-v, (he_inv v).symm⟩
  let E : Fin 5 × Fin 5 → ↥A := fun v => ⟨e v, hmemA v⟩
  have hE : Function.Bijective E := ⟨fun v w h => he_inj (congrArg Subtype.val h), fun x => by
    obtain ⟨v, hv⟩ := hsurj x x.2
    exact ⟨v, Subtype.ext hv⟩⟩
  let : Fintype ↥A := Fintype.ofBijective E hE
  let : Fintype M := Fintype.ofFinite M
  have hcardA : Fintype.card ↥A = 25 := by
    rw [← Fintype.card_of_bijective hE]
    simp
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (↥A) M
  rw [hcardA] at hB
  have hfixE : ∀ v, Fintype.card (MulAction.fixedBy M (E v)) = Nat.card (autFix (e v)) := by
    intro v
    rw [← Nat.card_eq_fintype_card]
    rfl
  let f : Fin 5 → Fin 5 → ℕ := fun i j => Nat.card (autFix (e (i, j)))
  have hsum : 25 ∣ ∑ i, ∑ j, f i j := by
    have h1 := Fintype.sum_bijective E hE (fun v => Nat.card (autFix (e v)))
      (fun g => Fintype.card (MulAction.fixedBy M g)) (fun v => (hfixE v).symm)
    have h2 : ∑ i, ∑ j, f i j = ∑ v : Fin 5 × Fin 5, Nat.card (autFix (e v)) :=
      (Fintype.sum_prod_type' _).symm
    rw [h2, h1, hB]
    exact Dvd.intro_left _ rfl
  have h00 : f 0 0 = 256 := by
    have : e (0, 0) = 1 := by simp [e]
    simp only [f, this]
    rw [← hM]
    have htop : autFix (1 : MulAut M) = ⊤ := by
      ext w
      simp [mem_autFix]
    rw [htop, Subgroup.card_top]
  have hval : ∀ i j, ¬ (i = 0 ∧ j = 0) → f i j = 1 ∨ f i j = 16 := by
    intro i j hij
    refine card_autFix_of_pow_five hM (he5 _) fun h => hij ?_
    obtain ⟨h1, h2⟩ := hind _ _ i.2 j.2 h
    exact ⟨Fin.ext h1, Fin.ext h2⟩
  have hk : ∀ i j k : Fin 5, k ≠ 0 → f (k * i) (k * j) = f i j := by
    intro i j k hk0
    have hkv : (k : ℕ) % 5 ≠ 0 := by
      have : (k : ℕ) ≠ 0 := fun h => hk0 (Fin.ext h)
      have := k.2
      omega
    have e1 : e (k * i, k * j) = e (i, j) ^ (k : ℕ) := by
      rw [he_pow]
      simp only [e]
      exact hnf _ _ _ _ (by rw [Fin.val_mul]; simp [Nat.mul_comm])
        (by rw [Fin.val_mul]; simp [Nat.mul_comm])
    simp only [f]
    rw [e1, autFix_pow (he5 _) hkv]
  have hτ : ∀ i j : Fin 5, f (-j) (i - j) = f i j := by
    intro i j
    have hai : α⁻¹ = α ^ 4 := inv_eq_of_mul_eq_one_left (by rw [← pow_succ, hα5])
    have hbi : β⁻¹ = β ^ 4 := inv_eq_of_mul_eq_one_left (by rw [← pow_succ, hβ5])
    have hconj : γ * e (i, j) * γ⁻¹ = e (-j, i - j) := by
      have h1 : γ * e (i, j) * γ⁻¹ = (γ * α * γ⁻¹) ^ (i : ℕ) * (γ * β * γ⁻¹) ^ (j : ℕ) := by
        simp only [e, ← MulAut.conj_apply, map_mul, map_pow]
      rw [h1, hγα, hγβ, mul_inv_rev, hai, hbi, ← (hc.pow_pow 4 4).eq,
        (hc.pow_pow 4 4).mul_pow, ← pow_mul, ← pow_mul]
      have h2 : β ^ (i : ℕ) * (α ^ (4 * (j : ℕ)) * β ^ (4 * (j : ℕ))) =
          α ^ (4 * (j : ℕ)) * β ^ ((i : ℕ) + 4 * j) := by
        rw [← mul_assoc, ← (hc.pow_pow (4 * (j : ℕ)) i).eq, mul_assoc, ← pow_add]
      rw [h2]
      exact hnf _ _ _ _ (by rw [Fin.val_neg']; omega) (by rw [Fin.val_sub]; omega)
    simp only [f]
    rw [← hconj, card_autFix_conj]
  exact false_of_fiveOrbit_sum f h00 hval hk hτ hsum

end Aut


section Lift

variable {G : Type} [Group G] [Finite G] {W : Subgroup G} (hW : IsElemAbelian 2 W)
  (hW256 : Nat.card W = 256)
  (hCW : ∀ x ∈ centralizer (W : Set G), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ W)
include hW hW256 hCW

theorem false_of_five_three_quot {a b c : normOddQuot W} (ha5 : a ^ 5 = 1) (ha1 : a ≠ 1)
    (hab : a * b = b * a) (hb : b ∉ zpowers a) (hca : c * a * c⁻¹ = b)
    (hcb : c * b * c⁻¹ = (a * b)⁻¹) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hπρ : ∀ n, normConj W n = 1 → oddQuotMap W n = 1 := fun n hn =>
    oddQuotMap_eq_one_of_mem_ker hW hCW (MonoidHom.mem_ker.mpr hn)
  have hb5 : b ^ 5 = 1 := by
    rw [← hca, conj_pow, ha5, mul_one, mul_inv_cancel]
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have hoa : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hob : orderOf b = 5 := orderOf_eq_prime hb5 hb1
  set F := zpowers a ⊔ zpowers b with hFdef
  have haF : a ∈ F := mem_sup_left (mem_zpowers a)
  have hbF : b ∈ F := mem_sup_right (mem_zpowers b)
  have hFa : F ≤ centralizer ({a} : Set (normOddQuot W)) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab.symm))
  have hFb : F ≤ centralizer ({b} : Set (normOddQuot W)) :=
    sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hab))
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    have hdvd : Nat.card (zpowers a ⊓ zpowers b : Subgroup _) ∣ 5 := by
      rw [← hob, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have heq : zpowers a ⊓ zpowers b = zpowers b := Subgroup.eq_of_le_of_card_ge inf_le_right
        (by rw [h, Nat.card_zpowers, hob])
      have hb' : b ∈ zpowers a ⊓ zpowers b := by
        rw [heq]
        exact mem_zpowers b
      exact hb hb'.1
  have hFcard : Nat.card F = 25 := by
    have hN : zpowers b ≤ normalizer (zpowers a : Set (normOddQuot W)) := by
      refine zpowers_le.mpr (mem_normalizer_iff.mpr fun x => ?_)
      have hcx : ∀ y ∈ zpowers a, b * y * b⁻¹ = y := fun y hy => by
        have := mem_centralizer_singleton_iff.mp (hFb (mem_sup_left hy))
        rw [← this, mul_inv_cancel_right]
      constructor
      · intro hx
        rw [hcx x hx]
        exact hx
      · intro hx
        have h2 : b⁻¹ * (b * x * b⁻¹) * b = b * x * b⁻¹ := by
          calc b⁻¹ * (b * x * b⁻¹) * b = b⁻¹ * (b * (b * x * b⁻¹) * b⁻¹) * b := by
                rw [hcx _ hx]
            _ = b * x * b⁻¹ := by group
        have e : x = b⁻¹ * (b * x * b⁻¹) * b := by group
        rw [e, h2]
        exact hx
    have h := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hN
    rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hoa, hob] at h
    exact h
  have hindF : ∀ i j : ℕ, i < 5 → j < 5 → a ^ i * b ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi hj h
    have hbj : b ^ j = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
    have hbj1 : b ^ j = 1 := by
      have hmem : b ^ j ∈ zpowers a ⊓ zpowers b := by
        refine ⟨?_, (zpowers b).pow_mem (mem_zpowers b) j⟩
        rw [hbj]
        exact (zpowers a).inv_mem ((zpowers a).pow_mem (mem_zpowers a) i)
      rwa [hinf, mem_bot] at hmem
    have hj0 : j = 0 := by
      have := orderOf_dvd_of_pow_eq_one hbj1
      rw [hob] at this
      omega
    subst hj0
    rw [pow_zero, mul_one] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hoa] at this
    exact ⟨by omega, rfl⟩
  have hcF : ∀ x ∈ F, c * x * c⁻¹ ∈ F := by
    intro x hx
    have hle : F ≤ F.comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · show c * a * c⁻¹ ∈ F
        rw [hca]
        exact hbF
      · show c * b * c⁻¹ ∈ F
        rw [hcb]
        exact inv_mem (mul_mem haF hbF)
    exact hle hx
  set M := F.comap (oddQuotMap W) with hMdef
  obtain ⟨S, hS⟩ := exists_isSylowOf 5 M
  have hSM : S ≤ M := hS.le
  have hlift : ∀ x ∈ F, ∃ s ∈ S, oddQuotMap W s = x := by
    obtain ⟨Qs, hQs⟩ := hS.exists_sylow_eq_subgroupOf
    let f : ↥M →* ↥F := ((oddQuotMap W).comp M.subtype).codRestrict F fun m => m.2
    have hf : Function.Surjective f := fun x => by
      obtain ⟨n, hn⟩ := oddQuotMap_surjective W x
      exact ⟨⟨n, show oddQuotMap W n ∈ F from hn ▸ x.2⟩, Subtype.ext hn⟩
    have hFp : IsPGroup 5 (⊤ : Subgroup ↥F) :=
      IsPGroup.of_card (n := 2) (by rw [Subgroup.card_top, hFcard]; norm_num)
    have htop : (⊤ : Subgroup ↥F) = (Qs.mapSurjective hf : Subgroup ↥F) :=
      (Qs.mapSurjective hf).is_maximal' hFp le_top
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥F) ∈ (Qs.mapSurjective hf : Subgroup ↥F) := htop ▸ mem_top _
    rw [Sylow.coe_mapSurjective] at hx'
    obtain ⟨m, hmQ, hm⟩ := mem_map.mp hx'
    have hmS : (m : ↥(normalizer (W : Set G))) ∈ S := by
      have : m ∈ S.subgroupOf M := hQs ▸ hmQ
      exact this
    exact ⟨m, hmS, congrArg Subtype.val hm⟩
  have hker : ∀ s ∈ S, oddQuotMap W s = 1 → normConj W s = 1 := by
    let πS := (oddQuotMap W).comp S.subtype
    let ρS := (normConj W).comp S.subtype
    have hrangeπ : Nat.card πS.range = 25 := by
      have : πS.range = F := by
        refine le_antisymm ?_ fun x hx => ?_
        · rintro _ ⟨s, rfl⟩
          exact hSM s.2
        · obtain ⟨s, hs, rfl⟩ := hlift x hx
          exact ⟨⟨s, hs⟩, rfl⟩
      rw [this, hFcard]
    have hrangeρ : Nat.card ρS.range ≤ 25 := by
      refine card_le_twentyfive_of_isPGroup hW hW256 ?_
      rw [MonoidHom.range_eq_map]
      exact (hS.isPGroup.to_subgroup ⊤).map ρS
    have h1 : Nat.card S = Nat.card πS.range * Nat.card πS.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup πS.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange πS).toEquiv]
    have h2 : Nat.card S = Nat.card ρS.range * Nat.card ρS.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρS.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ρS).toEquiv]
    have hle : ρS.ker ≤ πS.ker := fun s hs => hπρ _ hs
    have hpos : 0 < Nat.card ρS.ker := Nat.card_pos
    have hpos' : 0 < Nat.card πS.ker := Nat.card_pos
    have hcard : Nat.card πS.ker ≤ Nat.card ρS.ker := by
      rw [hrangeπ] at h1
      nlinarith
    have heq : ρS.ker = πS.ker := Subgroup.eq_of_le_of_card_ge hle hcard
    intro s hs h
    have hsk : (⟨s, hs⟩ : ↥S) ∈ πS.ker := h
    rw [← heq] at hsk
    exact hsk
  obtain ⟨a', ha'S, ha'⟩ := hlift a haF
  obtain ⟨b', hb'S, hb'⟩ := hlift b hbF
  have hα5 : normConj W a' ^ 5 = 1 := by
    rw [← map_pow]
    exact hker _ (S.pow_mem ha'S 5) (by rw [map_pow, ha', ha5])
  have hβ5 : normConj W b' ^ 5 = 1 := by
    rw [← map_pow]
    exact hker _ (S.pow_mem hb'S 5) (by rw [map_pow, hb', hb5])
  have hαβ : normConj W a' * normConj W b' = normConj W b' * normConj W a' := by
    have h := hker (a' * b' * a'⁻¹ * b'⁻¹)
      (S.mul_mem (S.mul_mem (S.mul_mem ha'S hb'S) (S.inv_mem ha'S)) (S.inv_mem hb'S))
      (by rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha', hb', hab, mul_inv_cancel_right,
        mul_inv_cancel])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h
    calc normConj W a' * normConj W b'
        = (normConj W a' * normConj W b' * (normConj W a')⁻¹ * (normConj W b')⁻¹) *
          (normConj W b' * normConj W a') := by group
      _ = normConj W b' * normConj W a' := by rw [h, one_mul]
  have hind : ∀ i j : ℕ, i < 5 → j < 5 →
      normConj W a' ^ i * normConj W b' ^ j = 1 → i = 0 ∧ j = 0 := by
    intro i j hi hj h
    have h' : oddQuotMap W (a' ^ i * b' ^ j) = 1 :=
      hπρ _ (by rw [map_mul, map_pow, map_pow]; exact h)
    rw [map_mul, map_pow, map_pow, ha', hb'] at h'
    exact hindF i j hi hj h'
  obtain ⟨c₀, hc₀⟩ := oddQuotMap_surjective W c
  set S₁ := S.map (MulAut.conj c₀).toMonoidHom
  have hS₁M : S₁ ≤ M := by
    rintro _ ⟨s, hs, rfl⟩
    show oddQuotMap W (c₀ * s * c₀⁻¹) ∈ F
    rw [map_mul, map_mul, map_inv, hc₀]
    exact hcF _ (hSM hs)
  have hS₁ : IsSylowOf 5 S₁ M := by
    refine isSylowOf_of_card hS₁M ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj c₀).injective, hS.card_eq]
  obtain ⟨k, hkM, hk⟩ := hS.exists_mem_conj hS₁
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = k⁻¹ * c₀ := ⟨_, rfl⟩
  have hcS : ∀ s ∈ S, cc * s * cc⁻¹ ∈ S := by
    intro s hs
    have h1 : c₀ * s * c₀⁻¹ ∈ S₁ := ⟨s, hs, rfl⟩
    have h2 := (hk _).mp h1
    have e : cc * s * cc⁻¹ = k⁻¹ * (c₀ * s * c₀⁻¹) * k := by rw [hcc]; group
    rw [e]
    exact h2
  have hk' : oddQuotMap W k ∈ F := hkM
  have hka : oddQuotMap W k * a = a * oddQuotMap W k :=
    mem_centralizer_singleton_iff.mp (hFa hk')
  have hkb : oddQuotMap W k * b = b * oddQuotMap W k :=
    mem_centralizer_singleton_iff.mp (hFb hk')
  have hπc : oddQuotMap W cc = (oddQuotMap W k)⁻¹ * c := by
    rw [hcc, map_mul, map_inv, hc₀]
  have hγα : normConj W cc * normConj W a' * (normConj W cc)⁻¹ = normConj W b' := by
    have h := hker (cc * a' * cc⁻¹ * b'⁻¹)
      (S.mul_mem (hcS _ ha'S) (S.inv_mem hb'S)) (by
        simp only [map_mul, map_inv, hπc, ha', hb']
        calc (oddQuotMap W k)⁻¹ * c * a * ((oddQuotMap W k)⁻¹ * c)⁻¹ * b⁻¹
            = (oddQuotMap W k)⁻¹ * (c * a * c⁻¹) * oddQuotMap W k * b⁻¹ := by group
          _ = (oddQuotMap W k)⁻¹ * (b * oddQuotMap W k) * b⁻¹ := by rw [hca]; group
          _ = (oddQuotMap W k)⁻¹ * (oddQuotMap W k * b) * b⁻¹ := by rw [hkb]
          _ = 1 := by group)
    simp only [map_mul, map_inv] at h
    exact mul_inv_eq_one.mp h
  have hγβ : normConj W cc * normConj W b' * (normConj W cc)⁻¹ =
      (normConj W a' * normConj W b')⁻¹ := by
    have h := hker (cc * b' * cc⁻¹ * (a' * b'))
      (S.mul_mem (hcS _ hb'S) (S.mul_mem ha'S hb'S)) (by
        simp only [map_mul, map_inv, hπc, ha', hb']
        have hkab : oddQuotMap W k * (a * b) = a * b * oddQuotMap W k := by
          rw [← mul_assoc, hka, mul_assoc, hkb, mul_assoc]
        calc (oddQuotMap W k)⁻¹ * c * b * ((oddQuotMap W k)⁻¹ * c)⁻¹ * (a * b)
            = (oddQuotMap W k)⁻¹ * (c * b * c⁻¹) * (oddQuotMap W k * (a * b)) := by group
          _ = (oddQuotMap W k)⁻¹ * (a * b)⁻¹ * (a * b * oddQuotMap W k) := by rw [hcb, hkab]
          _ = 1 := by group)
    simp only [map_mul, map_inv] at h
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul] at h ⊢; simpa [mul_assoc] using h)
  exact false_of_aut_five_three hW256 hα5 hβ5 hαβ hind hγα hγβ

end Lift

section Model

open CFSG.RankThree.PartOne CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier

theorem j2_five_three_model :
    ∃ a ∈ j2P, ∃ b ∈ j2P, ∃ c ∈ j2P, a ^ 5 = 1 ∧ a ≠ 1 ∧ a * b = b * a ∧
      b ∉ Subgroup.zpowers a ∧ c * a * c⁻¹ = b ∧ c * b * c⁻¹ = (a * b)⁻¹ := by
  have hchk := j2Norm_check
  simp only [j2NormCheck, Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hv20, hv21⟩, hv22⟩, hv50⟩, hv51⟩, hvC⟩, hB⟩, hcomm⟩, hrel⟩ := hchk
  have r20 := rep_of_validA hv20
  have r21 := rep_of_validA hv21
  have r22 := rep_of_validA hv22
  have r50 := rep_of_validA hv50
  have r51 := rep_of_validA hv51
  set C := permOfArr 315 (j2NormD2 0) * permOfArr 315 (j2NormD2 2) * permOfArr 315 (j2NormD2 1) *
    permOfArr 315 (j2NormD2 1) * (permOfArr 315 (j2NormD5 0) * permOfArr 315 (j2NormD5 1) *
      permOfArr 315 (j2NormD5 0) * permOfArr 315 (j2NormD5 1) * permOfArr 315 (j2NormD5 1))
    with hCdef
  have rC : Rep 315 j2NormC C :=
    rep_compA (rep_compA (rep_compA (rep_compA r20 r22) r21) r21)
      (rep_compA (rep_compA (rep_compA (rep_compA r50 r51) r50) r51) r51)
  have hCeq : permOfArr 315 j2NormC = C := (rep_of_validA hvC).unique rC
  have rCi : Rep 315 (invCand 315 j2NormC) C⁻¹ := hCeq ▸ rep_inv_of_validA hvC
  have rx0 : Rep 315 (j2NormX 0) (j2FiveLine 0) := rep_j2FiveLine 0
  have rx1 : Rep 315 (j2NormX 1) (j2FiveLine 1) := rep_j2FiveLine 1
  have rB : Rep 315 j2NormB (C * j2FiveLine 0 * C⁻¹) := rep_compA (rep_compA rC rx0) rCi
  have hB' : C * j2FiveLine 0 * C⁻¹ = j2FiveLine 1 * (j2FiveLine 1 * j2FiveLine 1) :=
    eq_of_eqA rB (rep_compA rx1 (rep_compA rx1 rx1)) hB
  have hcomm' : j2FiveLine 0 * j2FiveLine 1 = j2FiveLine 1 * j2FiveLine 0 :=
    eq_of_eqA (rep_compA rx0 rx1) (rep_compA rx1 rx0) hcomm
  have hrel' : C * (C * j2FiveLine 0 * C⁻¹) * C⁻¹ * (j2FiveLine 0 * (C * j2FiveLine 0 * C⁻¹)) =
      1 := eq_of_eqA (rep_compA (rep_compA (rep_compA rC rB) rCi) (rep_compA rx0 rB)) rep_idA hrel
  have hD2 : j2FiveD 2 ≤ j2P :=
    (j2FiveBad_structure (i := 2) (by norm_num) j2Five_cent_check_2
      j2Five_bad_check_2).2.2.2.2.2.1
  have hD5 : j2FiveD 5 ≤ j2P :=
    (j2FiveBad_structure (i := 5) (by norm_num) j2Five_cent_check_5
      j2Five_bad_check_5).2.2.2.2.2.1
  have hm2 : ∀ k < 3, permOfArr 315 (j2NormD2 k) ∈ j2P := fun k hk =>
    hD2 (Subgroup.subset_closure ⟨k, show k < (j2FiveDG 2).size by
      rw [show (j2FiveDG 2).size = 3 by rfl]; exact hk, rfl⟩)
  have hm5 : ∀ k < 2, permOfArr 315 (j2NormD5 k) ∈ j2P := fun k hk =>
    hD5 (Subgroup.subset_closure ⟨k, show k < (j2FiveDG 5).size by
      rw [show (j2FiveDG 5).size = 2 by rfl]; exact hk, rfl⟩)
  have hCP : C ∈ j2P := by
    rw [hCdef]
    exact j2P.mul_mem (j2P.mul_mem (j2P.mul_mem (j2P.mul_mem (hm2 0 (by norm_num))
      (hm2 2 (by norm_num))) (hm2 1 (by norm_num))) (hm2 1 (by norm_num)))
      (j2P.mul_mem (j2P.mul_mem (j2P.mul_mem (j2P.mul_mem (hm5 0 (by norm_num))
        (hm5 1 (by norm_num))) (hm5 0 (by norm_num))) (hm5 1 (by norm_num))) (hm5 1 (by norm_num)))
  have haP : j2FiveLine 0 ∈ j2P := j2FiveQ_le_P (j2FiveLine_mem_Q 0)
  refine ⟨j2FiveLine 0, haP, C * j2FiveLine 0 * C⁻¹,
    j2P.mul_mem (j2P.mul_mem hCP haP) (j2P.inv_mem hCP), C, hCP, j2FiveLine_pow_five 0,
    j2FiveLine_ne_one 0, ?_, ?_, rfl, eq_inv_of_mul_eq_one_left hrel'⟩
  · rw [hB']
    have h1 : j2FiveLine 0 * (j2FiveLine 1 * j2FiveLine 1) =
        j2FiveLine 1 * j2FiveLine 1 * j2FiveLine 0 := by
      rw [← mul_assoc, hcomm', mul_assoc, hcomm', ← mul_assoc]
    rw [← mul_assoc, hcomm', mul_assoc, h1, ← mul_assoc]
  ·
    intro hb
    have hx1 : j2FiveLine 1 = (C * j2FiveLine 0 * C⁻¹) ^ 2 := by
      rw [hB', ← pow_three, ← pow_mul]
      show j2FiveLine 1 = j2FiveLine 1 ^ 6
      rw [pow_succ, j2FiveLine_pow_five, one_mul]
    have hx1' : j2FiveLine 1 ∈ Subgroup.zpowers (j2FiveLine 0) := hx1 ▸ pow_mem hb 2
    have hle : Subgroup.zpowers (j2FiveLine 1) ≤ Subgroup.zpowers (j2FiveLine 0) :=
      Subgroup.zpowers_le.mpr hx1'
    have heq : Subgroup.zpowers (j2FiveLine 1) = Subgroup.zpowers (j2FiveLine 0) :=
      Subgroup.eq_of_le_of_card_ge hle (by
        rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_j2FiveLine, orderOf_j2FiveLine])
    have h10 := j2FiveQ_lines.2 heq
    exact absurd h10 (by decide)

end Model

theorem not_isSporadic_M12_J2_of_elem256
    {G : Type} [Group G] [Finite G] {W : Subgroup G}
    (hW : IsElemAbelian 2 W) (hW256 : Nat.card W = 256)
    (hCW : ∀ x ∈ centralizer (W : Set G), (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ W) :
    let N := normalizer (W : Set G); let Q := ↥N ⧸ W.subgroupOf N;
    ∀ X : Subgroup (Q ⧸ CFSG.Open.standardComponentOddCore Q),
      ¬ CFSG.Blueprint.NativeSporadic.IsSporadic ↥X .M12 ∧
        ¬ CFSG.Blueprint.NativeSporadic.IsSporadic ↥X .J2 := by
  intro N Q X
  refine ⟨not_isSporadic_M12_of_elem256 hW hW256 hCW X, ?_⟩
  rintro ⟨e⟩
  obtain ⟨a, ha, b, hb, c, hc, ha5, ha1, hab, hbz, hca, hcb⟩ := j2_five_three_model
  let φ : ↥CFSG.Sporadic.Schreier.j2P ≃* ↥X :=
    (e.trans CFSG.Sporadic.Schreier.j2PermEquiv).symm
  let ι : ↥X →* normOddQuot W := X.subtype
  have hι : ∀ x y, ι (φ x) = ι (φ y) → x = y := fun x y h => φ.injective (Subtype.ext h)
  have hmap : ∀ x y, ι (φ x) * ι (φ y) = ι (φ (x * y)) := fun x y => by
    rw [map_mul, map_mul]
  refine false_of_five_three_quot hW hW256 hCW (a := ι (φ ⟨a, ha⟩)) (b := ι (φ ⟨b, hb⟩))
    (c := ι (φ ⟨c, hc⟩)) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, ← map_pow]
    have : (⟨a, ha⟩ : ↥CFSG.Sporadic.Schreier.j2P) ^ 5 = 1 := Subtype.ext ha5
    rw [this, map_one, map_one]
  · intro h
    apply ha1
    have : (⟨a, ha⟩ : ↥CFSG.Sporadic.Schreier.j2P) = 1 := hι _ _ (by rw [h, map_one, map_one])
    exact congrArg Subtype.val this
  · rw [hmap, hmap]
    congr 2
    exact Subtype.ext hab
  · intro hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    apply hbz
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have : (⟨a, ha⟩ : ↥CFSG.Sporadic.Schreier.j2P) ^ k = ⟨b, hb⟩ := hι _ _ (by
      rw [map_zpow, map_zpow]
      exact hk)
    exact congrArg Subtype.val this
  · rw [← map_inv, ← map_inv, hmap, hmap]
    congr 2
    exact Subtype.ext hca
  · rw [← map_inv, ← map_inv, hmap, hmap, hmap, ← map_inv, ← map_inv]
    congr 2
    exact Subtype.ext (by simp [hcb])

end CFSG.ComponentClassification.AS81.Sec2

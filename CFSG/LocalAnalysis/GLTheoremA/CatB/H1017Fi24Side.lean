module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017SylowQ
public import Certificates.Data.Fi24Rank.Common
public import CFSG.Sporadic.FischerOddCore.Fi24R2Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24Side

open CFSG.Open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative
open CFSG.Sporadic.FischerOddCore (exists_famHom famInv_closure conjPerm conjPerm_apply)

theorem rep_powA {n : ℕ} {t : Array ℕ} {σ : Equiv.Perm (Fin n)} (ht : Rep n t σ) :
    ∀ e, Rep n (Fi24RankNative.powA n t e) (σ ^ e)
  | 0 => by
    rw [Fi24RankNative.powA, pow_zero]
    exact rep_idA
  | e + 1 => by
    rw [Fi24RankNative.powA, pow_succ']
    exact rep_compA ht (rep_powA ht e)

@[expose] noncomputable def iotaP (n : ℕ) (A : Array (Array ℕ)) (i : ℕ) : Equiv.Perm (Fin n) :=
  permOfArr n A[0]! ^ dig i 0 * (permOfArr n A[1]! ^ dig i 1 * (permOfArr n A[2]! ^ dig i 2 *
    (permOfArr n A[3]! ^ dig i 3 * permOfArr n A[4]! ^ dig i 4)))

theorem anyLt_iff {n : ℕ} {p : ℕ → Bool} : anyLt n p = true ↔ ∃ i < n, p i = true := by
  rw [anyLt, Bool.not_eq_true', ← Bool.not_eq_true, allLt_iff]
  push Not
  simp

theorem addD_lt (i j : ℕ) : addD i j < 243 := by
  unfold addD
  have := Nat.mod_lt (dig i 0 + dig j 0) (by norm_num : 0 < 3)
  have := Nat.mod_lt (dig i 1 + dig j 1) (by norm_num : 0 < 3)
  have := Nat.mod_lt (dig i 2 + dig j 2) (by norm_num : 0 < 3)
  have := Nat.mod_lt (dig i 3 + dig j 3) (by norm_num : 0 < 3)
  have := Nat.mod_lt (dig i 4 + dig j 4) (by norm_num : 0 < 3)
  omega

theorem negD_lt (i : ℕ) : negD i < 243 := by
  unfold negD
  have := Nat.mod_lt (3 - dig i 0) (by norm_num : 0 < 3)
  have := Nat.mod_lt (3 - dig i 1) (by norm_num : 0 < 3)
  have := Nat.mod_lt (3 - dig i 2) (by norm_num : 0 < 3)
  have := Nat.mod_lt (3 - dig i 3) (by norm_num : 0 < 3)
  have := Nat.mod_lt (3 - dig i 4) (by norm_num : 0 < 3)
  omega

theorem addD_comm (i j : ℕ) : addD i j = addD j i := by
  unfold addD
  simp only [Nat.add_comm (dig i _)]

theorem card_fix_eq {N : ℕ} (p : Fin N → Prop) [DecidablePred p] (b : Fin N → Bool)
    (hp : ∀ v, p v ↔ b v = true) : Nat.card {v // p v} = (List.finRange N).countP b := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fin.univ_def]
  show Multiset.card (Multiset.filter p ↑(List.finRange N)) = _
  rw [Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter]
  congr 1
  exact List.filter_congr fun v _ => by simp [hp v]

theorem getElem!_ofFn' {α : Type*} [Inhabited α] {m : ℕ} (f : Fin m → α) {i : ℕ} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem iotaP_zero {n : ℕ} {A : Array (Array ℕ)} : iotaP n A 0 = 1 := by
  simp [iotaP, dig]

theorem iotaP_basis {n : ℕ} {A : Array (Array ℕ)} {k : ℕ} (hk : k < 5) :
    iotaP n A (3 ^ k) = permOfArr n A[k]! := by
  interval_cases k <;> simp [iotaP, dig]

theorem pow_mod_three {M : Type*} [Monoid M] {x : M} (hx : x ^ 3 = 1) (m : ℕ) :
    x ^ (m % 3) = x ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem dig_sum5 {s₀ s₁ s₂ s₃ s₄ : ℕ} (h₀ : s₀ < 3) (h₁ : s₁ < 3) (h₂ : s₂ < 3) (h₃ : s₃ < 3)
    (h₄ : s₄ < 3) {k : ℕ} (hk : k < 5) :
    dig (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) k = [s₀, s₁, s₂, s₃, s₄].getD k 0 := by
  unfold dig
  interval_cases k
  · show (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) / 1 % 3 = s₀
    omega
  · show (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) / 3 % 3 = s₁
    omega
  · show (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) / 9 % 3 = s₂
    omega
  · show (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) / 27 % 3 = s₃
    omega
  · show (s₀ + 3 * s₁ + 9 * s₂ + 27 * s₃ + 81 * s₄) / 81 % 3 = s₄
    omega

theorem dig_addD {i j k : ℕ} (hk : k < 5) : dig (addD i j) k = (dig i k + dig j k) % 3 := by
  unfold addD
  rw [dig_sum5 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hk]
  interval_cases k <;> rfl

theorem dig_lt (i k : ℕ) : dig i k < 3 := Nat.mod_lt _ (by norm_num)

theorem dig_negD {i k : ℕ} (hk : k < 5) : (dig i k + dig (negD i) k) % 3 = 0 := by
  unfold negD
  rw [dig_sum5 (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
    (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) hk]
  have := dig_lt i k
  interval_cases k <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega

@[expose] def prod5 {M : Type*} [Monoid M] (x : Fin 5 → M) (a : ℕ → ℕ) : M :=
  x 0 ^ a 0 * (x 1 ^ a 1 * (x 2 ^ a 2 * (x 3 ^ a 3 * x 4 ^ a 4)))

theorem prod5_mul {B : Type*} [CommGroup B] (x : Fin 5 → B) (hx : ∀ k, x k ^ 3 = 1)
    (a b c : ℕ → ℕ) (hc : ∀ k < 5, c k = (a k + b k) % 3) :
    prod5 x a * prod5 x b = prod5 x c := by
  have e : ∀ (k : Fin 5), x k ^ c k.val = x k ^ a k.val * x k ^ b k.val := fun k => by
    rw [hc k k.2, pow_mod_three (hx k), pow_add]
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at e0 e1 e2
  unfold prod5
  rw [e0, e1, e2, show c 3 = c (3 : Fin 5).val from rfl, e3, show c 4 = c (4 : Fin 5).val from rfl, e4]
  simp only [mul_comm, mul_assoc, mul_left_comm]
  rfl

theorem prod5_mul_of_commute {G : Type*} [Group G] (y : Fin 5 → G)
    (hc : ∀ k l, y k * y l = y l * y k) (h3 : ∀ k, y k ^ 3 = 1) (a b c : ℕ → ℕ)
    (habc : ∀ k < 5, c k = (a k + b k) % 3) : prod5 y a * prod5 y b = prod5 y c := by
  let B := Subgroup.closure (Set.range y)
  letI : CommGroup B := Subgroup.closureCommGroupOfComm (by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩ _
    exact hc k l)
  let x : Fin 5 → B := fun k => ⟨y k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  have hx : ∀ k, x k ^ 3 = 1 := fun k => Subtype.ext (h3 k)
  have h := prod5_mul x hx a b c habc
  have hv : ∀ d, ((prod5 x d : B) : G) = prod5 y d := fun _ => rfl
  rw [← hv, ← hv, ← hv, ← h]
  rfl

section Side

variable {n : ℕ} {A G mus : Array (Array ℕ)} {p₀ sz : ℕ}

theorem sideOK_parts (h : sideOK n A G mus p₀ sz = true) :
    permsOK n A G mus = true ∧ p₀ < n ∧ multOK n A = true ∧
      injOK (iotas n A) p₀ = true ∧ conjOK n (iotas n A) G mus = true ∧ pbOK mus sz = true ∧
      fixOK mus sz = true := by
  unfold sideOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem permsOK_parts (h : permsOK n A G mus = true) :
    (∀ k < 5, isInvA n A[k]! (invCand n A[k]!) = true) ∧
      (∀ l < 2, isInvA n G[l]! (invCand n G[l]!) = true) ∧
      (∀ l < 2, isInvA 243 mus[l]! (invCand 243 mus[l]!) = true) := by
  unfold permsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨allLt_iff.1 h.1.1.2, allLt_iff.1 h.1.2, allLt_iff.1 h.2⟩

variable (hside : sideOK n A G mus p₀ sz = true)
include hside

theorem rep_A {k : ℕ} (hk : k < 5) : Rep n A[k]! (permOfArr n A[k]!) :=
  (rep_permOfArr ((permsOK_parts (sideOK_parts hside).1).1 k hk)).1

theorem rep_G {l : ℕ} (hl : l < 2) : Rep n G[l]! (permOfArr n G[l]!) :=
  (rep_permOfArr ((permsOK_parts (sideOK_parts hside).1).2.1 l hl)).1

theorem rep_Ginv {l : ℕ} (hl : l < 2) : Rep n (invCand n G[l]!) (permOfArr n G[l]!)⁻¹ :=
  (rep_permOfArr ((permsOK_parts (sideOK_parts hside).1).2.1 l hl)).2

theorem rep_mu {l : ℕ} (hl : l < 2) : Rep 243 mus[l]! (permOfArr 243 mus[l]!) :=
  (rep_permOfArr ((permsOK_parts (sideOK_parts hside).1).2.2 l hl)).1

theorem rep_iotaA (i : ℕ) : Rep n (iotaA n A i) (iotaP n A i) := by
  unfold iotaA iotaP
  exact rep_compA (rep_powA (rep_A hside (by norm_num)) _) (rep_compA
    (rep_powA (rep_A hside (by norm_num)) _) (rep_compA (rep_powA (rep_A hside (by norm_num)) _)
      (rep_compA (rep_powA (rep_A hside (by norm_num)) _) (rep_powA (rep_A hside (by norm_num)) _))))

theorem rep_iotas {i : ℕ} (hi : i < 243) : Rep n (iotas n A)[i]! (iotaP n A i) := by
  rw [iotas, getElem!_ofFn' _ hi]
  exact rep_iotaA hside i

omit hside in
theorem iotaP_eq_prod5 (i : ℕ) :
    iotaP n A i = prod5 (fun k : Fin 5 => permOfArr n A[k.val]!) (dig i) := rfl

theorem iotaP_gens :
    (∀ k l : Fin 5, permOfArr n A[k.val]! * permOfArr n A[l.val]! =
      permOfArr n A[l.val]! * permOfArr n A[k.val]!) ∧
    ∀ k : Fin 5, permOfArr n A[k.val]! ^ 3 = 1 := by
  have h := (sideOK_parts hside).2.2.1
  unfold multOK at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun k l => ?_, fun k => ?_⟩
  · exact eq_of_eqA (rep_compA (rep_A hside k.2) (rep_A hside l.2))
      (rep_compA (rep_A hside l.2) (rep_A hside k.2)) (allLt_iff.1 (allLt_iff.1 h.1 k k.2) l l.2)
  · exact eq_of_eqA (rep_powA (rep_A hside k.2) 3) rep_idA (allLt_iff.1 h.2 k k.2)

theorem iotaP_mul {i j : ℕ} (_hi : i < 243) (_hj : j < 243) :
    iotaP n A i * iotaP n A j = iotaP n A (addD i j) := by
  rw [iotaP_eq_prod5, iotaP_eq_prod5, iotaP_eq_prod5]
  exact prod5_mul_of_commute _ (iotaP_gens hside).1 (iotaP_gens hside).2 _ _ _
    fun k hk => dig_addD hk

theorem iotaP_mul_neg {i : ℕ} (_hi : i < 243) : iotaP n A i * iotaP n A (negD i) = 1 := by
  rw [iotaP_eq_prod5, iotaP_eq_prod5,
    prod5_mul_of_commute _ (iotaP_gens hside).1 (iotaP_gens hside).2 _ _ (fun _ => 0)
      fun k hk => (dig_negD hk).symm]
  simp [prod5]

theorem iotaP_comm {i j : ℕ} (hi : i < 243) (hj : j < 243) :
    iotaP n A i * iotaP n A j = iotaP n A j * iotaP n A i := by
  rw [iotaP_mul hside hi hj, iotaP_mul hside hj hi, addD_comm]

theorem iotaP_injective {i j : ℕ} (hi : i < 243) (hj : j < 243)
    (h : iotaP n A i = iotaP n A j) : i = j := by
  have hc := allLt_iff.1 (allLt_iff.1 (sideOK_parts hside).2.2.2.1 i hi) j hj
  have hp := (sideOK_parts hside).2.1
  rw [Bool.or_eq_true, beq_iff_eq, bne_iff_ne] at hc
  rcases hc with hc | hc
  · exact hc
  · exfalso
    apply hc
    rw [(rep_iotas hside hi).apply hp, (rep_iotas hside hj).apply hp, h]

theorem iotaP_conj {l i : ℕ} (hl : l < 2) (hi : i < 243) :
    (mus[l]!)[i]! < 243 ∧ permOfArr n G[l]! * iotaP n A i * (permOfArr n G[l]!)⁻¹ =
      iotaP n A ((mus[l]!)[i]!) := by
  have h := allLt_iff.1 (allLt_iff.1 (sideOK_parts hside).2.2.2.2.1 l hl) i hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1, ?_⟩
  rw [mul_assoc]
  exact eq_of_eqA (rep_compA (rep_G hside hl) (rep_compA (rep_iotas hside hi) (rep_Ginv hside hl)))
    (rep_iotas hside h.1) h.2

theorem mu_apply {l i : ℕ} (hl : l < 2) (hi : i < 243) :
    ((permOfArr 243 mus[l]! ⟨i, hi⟩ : Fin 243) : ℕ) = (mus[l]!)[i]! :=
  ((rep_mu hside hl).apply hi).symm

@[expose] noncomputable def LP (mus : Array (Array ℕ)) (r : ℕ) : Equiv.Perm (Fin 243) :=
  permOfArr 243 (pbBFS mus).1[r]!

theorem pbOK_parts :
    (pbBFS mus).1.size = sz ∧ eqA 243 (pbBFS mus).1[0]! (idA 243) = true ∧
    (∀ k < sz, isInvA 243 (pbBFS mus).1[k]! (invCand 243 (pbBFS mus).1[k]!) = true) ∧
    (∀ k < sz, k = 0 ∨ ((pbBFS mus).2.1[k]! < k ∧ (pbBFS mus).2.2[k]! < 2 ∧
      eqA 243 (pbBFS mus).1[k]! (compA 243 (pbBFS mus).1[(pbBFS mus).2.1[k]!]!
        mus[(pbBFS mus).2.2[k]!]!) = true)) ∧
    (∀ l < 2, ∃ r < sz, eqA 243 mus[l]! (pbBFS mus).1[r]! = true) ∧
    (∀ k < sz, ∀ l < sz, ∃ r < sz,
      eqA 243 (compA 243 (pbBFS mus).1[k]! (pbBFS mus).1[l]!) (pbBFS mus).1[r]! = true) ∧
    (∀ k < sz, ∃ r < sz,
      eqA 243 (compA 243 (pbBFS mus).1[k]! (pbBFS mus).1[r]!) (idA 243) = true) ∧
    (∀ k < sz, ∀ l < sz, k = l ∨ eqA 243 (pbBFS mus).1[k]! (pbBFS mus).1[l]! = false) := by
  have h := (sideOK_parts hside).2.2.2.2.2.1
  unfold pbOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, allLt_iff.1 h3, fun k hk => ?_, fun l hl => anyLt_iff.1 (allLt_iff.1 h5 l hl),
    fun k hk l hl => anyLt_iff.1 (allLt_iff.1 (allLt_iff.1 h6 k hk) l hl),
    fun k hk => anyLt_iff.1 (allLt_iff.1 h7 k hk), fun k hk l hl => ?_⟩
  · have := allLt_iff.1 h4 k hk
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at this
    tauto
  · have := allLt_iff.1 (allLt_iff.1 h8 k hk) l hl
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    exact this

theorem rep_LP {r : ℕ} (hr : r < sz) : Rep 243 (pbBFS mus).1[r]! (LP mus r) :=
  (rep_permOfArr ((pbOK_parts hside).2.2.1 r hr)).1

theorem LP_zero (hsz : 0 < sz) : LP mus 0 = 1 :=
  eq_of_eqA (rep_LP hside hsz) rep_idA (pbOK_parts hside).2.1

theorem LP_mul {k l : ℕ} (hk : k < sz) (hl : l < sz) : ∃ r < sz, LP mus k * LP mus l = LP mus r := by
  obtain ⟨r, hr, he⟩ := (pbOK_parts hside).2.2.2.2.2.1 k hk l hl
  exact ⟨r, hr, eq_of_eqA (rep_compA (rep_LP hside hk) (rep_LP hside hl)) (rep_LP hside hr) he⟩

theorem LP_inv {k : ℕ} (hk : k < sz) : ∃ r < sz, (LP mus k)⁻¹ = LP mus r := by
  obtain ⟨r, hr, he⟩ := (pbOK_parts hside).2.2.2.2.2.2.1 k hk
  refine ⟨r, hr, (inv_eq_of_mul_eq_one_right ?_)⟩
  exact eq_of_eqA (rep_compA (rep_LP hside hk) (rep_LP hside hr)) rep_idA he

theorem mu_mem_L {l : ℕ} (hl : l < 2) : ∃ r < sz, permOfArr 243 mus[l]! = LP mus r := by
  obtain ⟨r, hr, he⟩ := (pbOK_parts hside).2.2.2.2.1 l hl
  exact ⟨r, hr, eq_of_eqA (rep_mu hside hl) (rep_LP hside hr) he⟩

theorem LP_injective {k l : ℕ} (hk : k < sz) (hl : l < sz) (h : LP mus k = LP mus l) : k = l := by
  rcases (pbOK_parts hside).2.2.2.2.2.2.2 k hk l hl with h' | h'
  · exact h'
  · rw [(eqA_iff (rep_LP hside hk) (rep_LP hside hl)).2 h] at h'
    exact absurd h' (by simp)

theorem LP_parent {k : ℕ} (hk : k < sz) (hk0 : k ≠ 0) :
    (pbBFS mus).2.1[k]! < k ∧ ∃ l < 2, LP mus k = LP mus ((pbBFS mus).2.1[k]!) * permOfArr 243 mus[l]! := by
  rcases (pbOK_parts hside).2.2.2.1 k hk with h | ⟨h1, h2, h3⟩
  · exact absurd h hk0
  · exact ⟨h1, _, h2, eq_of_eqA (rep_LP hside hk)
      (rep_compA (rep_LP hside (h1.trans hk)) (rep_mu hside h2)) h3⟩

omit hside in
theorem card_fix1 {t : Array ℕ} {x : Equiv.Perm (Fin 243)} (ht : Rep 243 t x) :
    Nat.card {v // x v = v} = fix1 t := by
  refine card_fix_eq _ (fun v => t[v.val]! == v.val) fun v => ?_
  rw [beq_iff_eq, ht v, Fin.val_inj]

omit hside in
theorem card_fix2 {t u : Array ℕ} {x y : Equiv.Perm (Fin 243)} (ht : Rep 243 t x)
    (hu : Rep 243 u y) : Nat.card {v // x v = v ∧ y v = v} = fix2 t u := by
  refine card_fix_eq _ (fun v => t[v.val]! == v.val && u[v.val]! == v.val) fun v => ?_
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ht v, hu v, Fin.val_inj, Fin.val_inj]

omit hside in
theorem card_fix3 {t u w : Array ℕ} {x y z : Equiv.Perm (Fin 243)} (ht : Rep 243 t x)
    (hu : Rep 243 u y) (hw : Rep 243 w z) :
    Nat.card {v // x v = v ∧ y v = v ∧ z v = v} = fix3 t u w := by
  refine card_fix_eq _
    (fun v => t[v.val]! == v.val && u[v.val]! == v.val && w[v.val]! == v.val) fun v => ?_
  rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq, beq_iff_eq, ht v, hu v, hw v,
    Fin.val_inj, Fin.val_inj, Fin.val_inj, and_assoc]

theorem commA_eq_true {k l : ℕ} (hk : k < sz) (hl : l < sz)
    (h : LP mus k * LP mus l = LP mus l * LP mus k) :
    commA (pbBFS mus).1[k]! (pbBFS mus).1[l]! = true :=
  (eqA_iff (rep_compA (rep_LP hside hk) (rep_LP hside hl))
    (rep_compA (rep_LP hside hl) (rep_LP hside hk))).2 h

omit hside in
theorem eqA_eq_false {t u : Array ℕ} {x y : Equiv.Perm (Fin 243)} (ht : Rep 243 t x)
    (hu : Rep 243 u y) (h : x ≠ y) : eqA 243 t u = false := by
  by_contra h'
  rw [Bool.not_eq_false] at h'
  exact h ((eqA_iff ht hu).1 h')

omit hside in
theorem pairEx_eq {t u : Array ℕ} : pairEx t u = (eqA 243 t (idA 243) || !commA t u ||
    eqA 243 u (idA 243) || eqA 243 u t || eqA 243 u (compA 243 t t)) := rfl

theorem fixOK_parts :
    (∀ k < sz, eqA 243 (pbBFS mus).1[k]! (idA 243) = true ∨ fix1 (pbBFS mus).1[k]! ≤ 27) ∧
    (∀ k < sz, ∀ l < sz, pairEx (pbBFS mus).1[k]! (pbBFS mus).1[l]! = true ∨
      fix2 (pbBFS mus).1[k]! (pbBFS mus).1[l]! ≤ 9) ∧
    (∀ k < sz, ∀ l < sz, pairEx (pbBFS mus).1[k]! (pbBFS mus).1[l]! = true ∨ ∀ r < sz,
      commA (pbBFS mus).1[k]! (pbBFS mus).1[r]! = false ∨
      commA (pbBFS mus).1[l]! (pbBFS mus).1[r]! = false ∨
      (∃ i < 3, ∃ j < 3, eqA 243 (pbBFS mus).1[r]! (compA 243
        (Fi24RankNative.powA 243 (pbBFS mus).1[k]! i)
        (Fi24RankNative.powA 243 (pbBFS mus).1[l]! j)) = true) ∨
      fix3 (pbBFS mus).1[k]! (pbBFS mus).1[l]! (pbBFS mus).1[r]! ≤ 3) := by
  have h := (sideOK_parts hside).2.2.2.2.2.2
  unfold fixOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k hk => ?_, fun k hk l hl => ?_, fun k hk l hl => ?_⟩
  · have := allLt_iff.1 h1 k hk
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using this
  · have := allLt_iff.1 (allLt_iff.1 h2 k hk) l hl
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using this
  · have := allLt_iff.1 (allLt_iff.1 h3 k hk) l hl
    rw [Bool.or_eq_true] at this
    rcases this with h | h
    · exact Or.inl h
    · refine Or.inr fun r hr => ?_
      have h' := allLt_iff.1 h r hr
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h'
      rcases h' with ((h | h) | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · obtain ⟨i, hi, hj⟩ := anyLt_iff.1 h
        obtain ⟨j, hj', he⟩ := anyLt_iff.1 hj
        exact Or.inr (Or.inr (Or.inl ⟨i, hi, j, hj', he⟩))
      · exact Or.inr (Or.inr (Or.inr h))

theorem pairEx_false {k l : ℕ} (hk : k < sz) (hl : l < sz)
    (hc : LP mus k * LP mus l = LP mus l * LP mus k) (h1 : LP mus k ≠ 1) (h2 : LP mus l ≠ 1)
    (h3 : LP mus l ≠ LP mus k) (h4 : LP mus l ≠ LP mus k * LP mus k) :
    pairEx (pbBFS mus).1[k]! (pbBFS mus).1[l]! = false := by
  rw [pairEx_eq, commA_eq_true hside hk hl hc,
    eqA_eq_false (rep_LP hside hk) rep_idA h1, eqA_eq_false (rep_LP hside hl) rep_idA h2,
    eqA_eq_false (rep_LP hside hl) (rep_LP hside hk) h3,
    eqA_eq_false (rep_LP hside hl) (rep_compA (rep_LP hside hk) (rep_LP hside hk)) h4]
  rfl

theorem fix_checks :
    (∀ k < sz, LP mus k ≠ 1 → Nat.card {v // LP mus k v = v} ≤ 27) ∧
    (∀ k < sz, ∀ l < sz, LP mus k * LP mus l = LP mus l * LP mus k → LP mus k ≠ 1 →
      LP mus l ≠ 1 → LP mus l ≠ LP mus k → LP mus l ≠ LP mus k * LP mus k →
      Nat.card {v // LP mus k v = v ∧ LP mus l v = v} ≤ 9) ∧
    (∀ k < sz, ∀ l < sz, ∀ r < sz, LP mus k * LP mus l = LP mus l * LP mus k →
      LP mus k * LP mus r = LP mus r * LP mus k → LP mus l * LP mus r = LP mus r * LP mus l →
      LP mus k ≠ 1 → LP mus l ≠ 1 → LP mus l ≠ LP mus k → LP mus l ≠ LP mus k * LP mus k →
      (∀ i < 3, ∀ j < 3, LP mus r ≠ LP mus k ^ i * LP mus l ^ j) →
      Nat.card {v // LP mus k v = v ∧ LP mus l v = v ∧ LP mus r v = v} ≤ 3) := by
  obtain ⟨f1, f2, f3⟩ := fixOK_parts hside
  refine ⟨fun k hk h1 => ?_, fun k hk l hl hc h1 h2 h3 h4 => ?_,
    fun k hk l hl r hr hc1 hc2 hc3 h1 h2 h3 h4 h5 => ?_⟩
  · rw [card_fix1 (rep_LP hside hk)]
    rcases f1 k hk with h | h
    · exact absurd ((eqA_iff (rep_LP hside hk) rep_idA).1 h) h1
    · exact h
  · rw [card_fix2 (rep_LP hside hk) (rep_LP hside hl)]
    rcases f2 k hk l hl with h | h
    · rw [pairEx_false hside hk hl hc h1 h2 h3 h4] at h
      exact absurd h (by simp)
    · exact h
  · rw [card_fix3 (rep_LP hside hk) (rep_LP hside hl) (rep_LP hside hr)]
    rcases f3 k hk l hl with h | h
    · rw [pairEx_false hside hk hl hc1 h1 h2 h3 h4] at h
      exact absurd h (by simp)
    · rcases h r hr with h | h | ⟨i, hi, j, hj, h⟩ | h
      · rw [commA_eq_true hside hk hr hc2] at h; exact absurd h (by simp)
      · rw [commA_eq_true hside hl hr hc3] at h; exact absurd h (by simp)
      · exact absurd ((eqA_iff (rep_LP hside hr) (rep_compA (rep_powA (rep_LP hside hk) i)
          (rep_powA (rep_LP hside hl) j))).1 h) (h5 i hi j hj)
      · exact h

theorem nonab_of (h : nonabOK mus sz = true) :
    ∃ k < sz, ∃ l < sz, LP mus k * LP mus l ≠ LP mus l * LP mus k := by
  unfold nonabOK at h
  obtain ⟨k, hk, h'⟩ := anyLt_iff.1 h
  obtain ⟨l, hl, h''⟩ := anyLt_iff.1 h'
  refine ⟨k, hk, l, hl, fun he => ?_⟩
  rw [commA_eq_true hside hk hl he] at h''
  exact absurd h'' (by simp)

omit hside in
theorem stabs_get {I : Array (Array ℕ)} {q : ℕ} (hq : q < n) : (stabs n I)[q]! = stabList I q := by
  rw [stabs, getElem!_ofFn' _ hq]

theorem apply_eq_of_uniqAt {p : ℕ} (hp : p < n)
    (hu : uniqAt n (iotas n A) (stabs n (iotas n A)) p = true) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ i < 243, σ * iotaP n A i = iotaP n A i * σ) (hσ2 : σ * σ = 1) :
    σ ⟨p, hp⟩ = ⟨p, hp⟩ := by
  unfold uniqAt at hu
  simp only [Bool.and_eq_true] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have hfixI : ∀ {i : ℕ} (hi : i < 243) (x : Fin n),
      (((iotas n A)[i]!)[x.val]! == x.val) = true ↔ iotaP n A i x = x := fun hi x => by
    rw [beq_iff_eq, rep_iotas hside hi x, Fin.val_inj]
  refine apply_eq_of_unique_stab (fun v : Fin 243 => iotaP n A v) (fun v => hσ v v.2) hσ2
    ⟨p, hp⟩ (fun q hq => ?_) (fun v hv => ?_)
  · have h := allLt_iff.1 hu1 q q.2
    rw [Bool.or_eq_true, bne_iff_ne] at h
    rcases h with h | h
    · exfalso
      apply h
      rw [stabs_get q.2, stabs_get hp]
      unfold stabList
      refine List.filter_congr fun i hi => ?_
      have hi' : i < 243 := List.mem_range.1 hi
      have e1 := hfixI hi' q
      have e2 := hfixI hi' ⟨p, hp⟩
      have e3 := hq ⟨i, hi'⟩
      simp only at e3
      exact Bool.eq_iff_iff.2 (e1.trans (e3.symm.trans e2.symm))
    · obtain ⟨i, hi, he⟩ := anyLt_iff.1 h
      refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
      rw [← (rep_iotas hside hi).apply hp]
      exact beq_iff_eq.1 he
  · have h := allLt_iff.1 hu2 v v.2
    rw [Bool.or_eq_true, bne_iff_ne, beq_iff_eq] at h
    rcases h with h | h
    · exfalso
      apply h
      rw [(rep_iotas hside v.2).apply hp, (rep_iotas hside v.2).apply ((iotaP n A v ⟨p, hp⟩).2)]
      exact congrArg Fin.val hv
    · apply Fin.ext
      rw [← (rep_iotas hside v.2).apply hp]
      exact h

end Side

section Group

variable {n : ℕ} {A G mus : Array (Array ℕ)} {p₀ sz m : ℕ}
  (X : Subgroup (Equiv.Perm (Fin n)))
  (hside : sideOK n A G mus p₀ sz = true)
  (hAX : ∀ k < 5, permOfArr n A[k]! ∈ X) (hGX : ∀ l < 2, permOfArr n G[l]! ∈ X)

include hAX in
theorem iotaP_mem (i : ℕ) : iotaP n A i ∈ X := by
  unfold iotaP
  exact X.mul_mem (X.pow_mem (hAX 0 (by norm_num)) _) (X.mul_mem (X.pow_mem (hAX 1 (by norm_num)) _)
    (X.mul_mem (X.pow_mem (hAX 2 (by norm_num)) _) (X.mul_mem (X.pow_mem (hAX 3 (by norm_num)) _)
      (X.pow_mem (hAX 4 (by norm_num)) _))))

include hside hAX hGX

set_option maxHeartbeats 1000000 in
theorem side_conj [Finite X] (hsz : sz = 3 ^ m) (hX : ¬ 3 ^ (5 + m + 1) ∣ Nat.card X)
    (hsmall : sz ≤ 27 ∨ (sz = 81 ∧ nonabOK mus sz = true)) (E : Subgroup X)
    (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 5 ∧ (Nat.card E = 3 ^ 5 → ∃ g : X, ∀ x : X, x ∈ E ↔ ∃ i < 243,
      ((g⁻¹ * x * g : X) : Equiv.Perm (Fin n)) = iotaP n A i) := by
  classical
  let ι : Fin 243 → X := fun i => ⟨iotaP n A i, iotaP_mem X hAX i⟩
  have hιv : ∀ i, ((ι i : X) : Equiv.Perm (Fin n)) = iotaP n A i := fun _ => rfl
  have hιinj : Function.Injective ι := fun i j h =>
    Fin.ext (iotaP_injective hside i.2 j.2 (congrArg Subtype.val h))
  let aX : Fin 5 → X := fun k => ⟨permOfArr n A[k.val]!, hAX k k.2⟩
  let gX : Fin 2 → X := fun l => ⟨permOfArr n G[l.val]!, hGX l l.2⟩
  have haι : ∀ k : Fin 5, aX k = ι ⟨3 ^ k.val, by have := k.2; interval_cases (k : ℕ) <;> norm_num⟩ :=
    fun k => Subtype.ext (iotaP_basis k.2).symm
  set Aset : Subgroup X := Subgroup.closure (Set.range aX) with hAsetdef
  have hmulι : ∀ i j : Fin 243, ι i * ι j = ι ⟨addD i j, addD_lt _ _⟩ := fun i j =>
    Subtype.ext (iotaP_mul hside i.2 j.2)
  have hinvι : ∀ i : Fin 243, (ι i)⁻¹ = ι ⟨negD i, negD_lt _⟩ := fun i =>
    (inv_eq_of_mul_eq_one_right (Subtype.ext (iotaP_mul_neg hside i.2)))
  have hA : ∀ x : X, x ∈ Aset ↔ ∃ i, ι i = x := by
    intro x
    constructor
    · intro hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact ⟨_, (haι k).symm⟩
      | one => exact ⟨⟨0, by norm_num⟩, Subtype.ext iotaP_zero⟩
      | mul y z _ _ hy hz =>
        obtain ⟨i, rfl⟩ := hy
        obtain ⟨j, rfl⟩ := hz
        exact ⟨_, (hmulι i j).symm⟩
      | inv y _ hy =>
        obtain ⟨i, rfl⟩ := hy
        exact ⟨_, (hinvι i).symm⟩
    · rintro ⟨i, rfl⟩
      have h : ι i = aX 0 ^ dig i 0 * (aX 1 ^ dig i 1 * (aX 2 ^ dig i 2 *
          (aX 3 ^ dig i 3 * aX 4 ^ dig i 4))) := Subtype.ext rfl
      rw [h]
      have hm : ∀ k, aX k ∈ Aset := fun k => Subgroup.subset_closure ⟨k, rfl⟩
      exact Aset.mul_mem (Aset.pow_mem (hm 0) _) (Aset.mul_mem (Aset.pow_mem (hm 1) _)
        (Aset.mul_mem (Aset.pow_mem (hm 2) _) (Aset.mul_mem (Aset.pow_mem (hm 3) _)
          (Aset.pow_mem (hm 4) _))))
  have hAc : ∀ a ∈ Aset, ∀ b ∈ Aset, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := (hA a).1 ha
    obtain ⟨j, rfl⟩ := (hA b).1 hb
    exact Subtype.ext (iotaP_comm hside i.2 j.2)
  set T : Set X := Set.range aX ∪ Set.range gX with hT
  set P₀ : Subgroup X := Subgroup.closure T with hP₀def
  have hAP : Aset ≤ P₀ := Subgroup.closure_mono Set.subset_union_left
  have hgι : ∀ (l : Fin 2) (j : Fin 243), gX l * ι j * (gX l)⁻¹ =
      ι ⟨(mus[l.val]!)[j.val]!, (iotaP_conj hside l.2 j.2).1⟩ := fun l j =>
    Subtype.ext (iotaP_conj hside l.2 j.2).2
  have hTinv : ∀ t ∈ T, ∀ j, ∃ j', ι j' = conjPerm t (ι j) := by
    rintro t (⟨k, rfl⟩ | ⟨l, rfl⟩) j
    · refine ⟨j, ?_⟩
      rw [conjPerm_apply, hAc _ (Subgroup.subset_closure ⟨k, rfl⟩) _ ((hA _).2 ⟨j, rfl⟩),
        mul_inv_cancel_right]
    · exact ⟨_, by rw [conjPerm_apply, hgι]⟩
  obtain ⟨μ, hμ⟩ := exists_famHom (conjPerm.comp P₀.subtype) hιinj
    (fun h j => famInv_closure conjPerm hιinj hTinv h.2 j)
  have hμ' : ∀ (g : P₀) j, ι (μ g j) = (g : X) * ι j * (g : X)⁻¹ := fun g j => by
    rw [hμ g j]
    rfl
  have hμa : ∀ k : Fin 5, μ ⟨aX k, Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)⟩ = 1 := fun k =>
    Equiv.ext fun j => hιinj (by
      rw [hμ', Equiv.Perm.one_apply]
      show aX k * ι j * (aX k)⁻¹ = ι j
      rw [hAc _ (Subgroup.subset_closure ⟨k, rfl⟩) _ ((hA _).2 ⟨j, rfl⟩), mul_inv_cancel_right])
  have hμg : ∀ l : Fin 2, μ ⟨gX l, Subgroup.subset_closure (Or.inr ⟨l, rfl⟩)⟩ =
      permOfArr 243 mus[l.val]! := fun l =>
    Equiv.ext fun j => hιinj (by
      rw [hμ']
      show gX l * ι j * (gX l)⁻¹ = _
      rw [hgι]
      congr 1
      exact Fin.ext (mu_apply hside l.2 j.2).symm)
  have hsz0 : 0 < sz := by rw [hsz]; exact pow_pos (by norm_num) _
  have hrange1 : ∀ g : P₀, ∃ r < sz, μ g = LP mus r := by
    rintro ⟨g, hg⟩
    induction hg using Subgroup.closure_induction with
    | mem t ht =>
      rcases ht with ⟨k, rfl⟩ | ⟨l, rfl⟩
      · exact ⟨0, hsz0, by rw [hμa, LP_zero hside hsz0]⟩
      · obtain ⟨r, hr, he⟩ := mu_mem_L hside l.2
        exact ⟨r, hr, by rw [hμg, he]⟩
    | one => exact ⟨0, hsz0, by rw [LP_zero hside hsz0]; exact map_one μ⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨r, hr, hre⟩ := ihx
      obtain ⟨s, hs, hse⟩ := ihy
      obtain ⟨t, ht, hte⟩ := LP_mul hside hr hs
      refine ⟨t, ht, ?_⟩
      have : (⟨x * y, P₀.mul_mem hx hy⟩ : P₀) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [this, map_mul, hre, hse, hte]
    | inv x hx ihx =>
      obtain ⟨r, hr, hre⟩ := ihx
      obtain ⟨t, ht, hte⟩ := LP_inv hside hr
      refine ⟨t, ht, ?_⟩
      have : (⟨x⁻¹, P₀.inv_mem hx⟩ : P₀) = (⟨x, hx⟩ : P₀)⁻¹ := rfl
      rw [this, map_inv, hre, hte]
  have hrange2 : ∀ r < sz, LP mus r ∈ μ.range := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr
      by_cases hr0 : r = 0
      · subst hr0
        rw [LP_zero hside hsz0]
        exact μ.range.one_mem
      · obtain ⟨hp, l, hl, he⟩ := LP_parent hside hr hr0
        rw [he]
        refine μ.range.mul_mem (ih _ hp (hp.trans hr)) ⟨⟨gX ⟨l, hl⟩, Subgroup.subset_closure
          (Or.inr ⟨⟨l, hl⟩, rfl⟩)⟩, hμg ⟨l, hl⟩⟩
  have hmemR : ∀ x, x ∈ μ.range ↔ ∃ r < sz, x = LP mus r := by
    intro x
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨r, hr, he⟩ := hrange1 g
      exact ⟨r, hr, he⟩
    · rintro ⟨r, hr, rfl⟩
      exact hrange2 r hr
  have hcardR : Nat.card μ.range = sz := by
    have e : Fin sz ≃ μ.range := Equiv.ofBijective (fun r => ⟨LP mus r, hrange2 r r.2⟩)
      ⟨fun r s h => Fin.ext (LP_injective hside r.2 s.2 (congrArg Subtype.val h)), fun x => by
        obtain ⟨r, hr, he⟩ := (hmemR x).1 x.2
        exact ⟨⟨r, hr⟩, Subtype.ext he.symm⟩⟩
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hrange : Nat.card μ.range = 3 ^ m := hsz ▸ hcardR
  obtain ⟨c1, c2, c3⟩ := fix_checks hside
  have hR : ∀ x ∈ μ.range, ∃ r < sz, x = LP mus r := fun x hx => (hmemR x).1 hx
  have hbound : ∀ H : Subgroup (Equiv.Perm (Fin 243)), H ≤ μ.range → IsElemAbelian 3 H →
      H ≠ ⊥ → Nat.card H * Nat.card {v // ∀ h ∈ H, h v = v} < 3 ^ 5 := by
    refine card_mul_fix_lt_of_checks μ.range ?_ ?_ ?_ ?_
    · intro H hHR hH
      rcases hsmall with hs | ⟨hs, hna⟩
      · exact (Subgroup.card_le_of_le hHR).trans (hcardR.trans_le hs)
      · obtain ⟨k, hk, l, hl, hkl⟩ := nonab_of hside hna
        have hne : Nat.card H ≠ 81 := fun h81 => by
          have hHeq : H = μ.range := Subgroup.eq_of_le_of_card_ge hHR (by rw [hcardR, h81, hs])
          exact hkl (comm_of_isElemAbelian' hH (hHeq ▸ hrange2 k hk) (hHeq ▸ hrange2 l hl))
        have hdvd : Nat.card H ∣ 3 ^ 4 := by
          rw [show (3 : ℕ) ^ 4 = sz by rw [hs]; norm_num]
          exact hcardR ▸ Subgroup.card_dvd_of_le hHR
        obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
        have hj4 : j ≠ 4 := fun h => hne (by rw [hj', h]; norm_num)
        rw [hj']
        calc 3 ^ j ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 27 := by norm_num
    · intro x hx h1
      obtain ⟨r, hr, rfl⟩ := hR x hx
      exact c1 r hr h1
    · intro x hx y hy hxy h1 h2 h3 h4
      obtain ⟨r, hr, rfl⟩ := hR x hx
      obtain ⟨s, hs, rfl⟩ := hR y hy
      exact c2 r hr s hs hxy h1 h2 h3 h4
    · intro x hx y hy z hz hxy hxz hyz h1 h2 h3 h4 h5
      obtain ⟨r, hr, rfl⟩ := hR x hx
      obtain ⟨s, hs, rfl⟩ := hR y hy
      obtain ⟨t, ht, rfl⟩ := hR z hz
      exact c3 r hr s hs t ht hxy hxz hyz h1 h2 h3 h4 h5
  obtain ⟨h1, h2⟩ := elemAbelian_le_of_conj_action (n := 5) (m := m) Aset P₀ hAP hAc ι hιinj hA
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num) μ hμ' hrange hX hbound E hE
  refine ⟨h1, fun hcard => ?_⟩
  obtain ⟨g, hg⟩ := h2 hcard
  refine ⟨g, fun x => ?_⟩
  rw [hg, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨i, rfl⟩ := (hA y).1 hy
    refine ⟨i, i.2, ?_⟩
    have e : g⁻¹ * (MulAut.conj g).toMonoidHom (ι i) * g = ι i := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e, hιv]
  · rintro ⟨i, hi, hx⟩
    have h : g⁻¹ * x * g = ι ⟨i, hi⟩ := Subtype.ext (hx.trans (hιv ⟨i, hi⟩).symm)
    refine ⟨ι ⟨i, hi⟩, (hA _).2 ⟨_, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← h]
    group

theorem side_facts [Finite X] (hsz : sz = 3 ^ m) (hX : ¬ 3 ^ (5 + m + 1) ∣ Nat.card X)
    (hsmall : sz ≤ 27 ∨ (sz = 81 ∧ nonabOK mus sz = true))
    (hfix : ∀ σ ∈ X, σ * σ = 1 → (∀ i < 243, σ * iotaP n A i = iotaP n A i * σ) → σ = 1) :
    (∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 5) ∧
      (∀ E : Subgroup X, IsElemAbelian 3 E → Nat.card E = 3 ^ 5 → ∀ σ : X, σ * σ = 1 →
        (∀ e ∈ E, σ * e = e * σ) → σ = 1) := by
  refine ⟨fun E hE => (side_conj X hside hAX hGX hsz hX hsmall E hE).1,
    fun E hE hcard σ hσ2 hσE => ?_⟩
  obtain ⟨g, hg⟩ := (side_conj X hside hAX hGX hsz hX hsmall E hE).2 hcard
  let ι : Fin 243 → X := fun i => ⟨iotaP n A i, iotaP_mem X hAX i⟩
  set σ' : X := g⁻¹ * σ * g with hσ'
  have hσ'A : ∀ i : Fin 243, σ' * ι i = ι i * σ' := by
    intro i
    have hmem : g * ι i * g⁻¹ ∈ E := (hg _).2 ⟨i, i.2,
      congrArg Subtype.val (show g⁻¹ * (g * ι i * g⁻¹) * g = ι i by group)⟩
    have h := hσE _ hmem
    rw [hσ']
    calc g⁻¹ * σ * g * ι i = g⁻¹ * (σ * (g * ι i * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * ι i * g⁻¹) * σ) * g := by rw [h]
      _ = ι i * (g⁻¹ * σ * g) := by group
  have hσ'2 : σ' * σ' = 1 := by
    rw [hσ']
    calc g⁻¹ * σ * g * (g⁻¹ * σ * g) = g⁻¹ * (σ * σ) * g := by group
      _ = 1 := by rw [hσ2]; group
  have h1 : (σ' : Equiv.Perm (Fin n)) = 1 := hfix _ σ'.2 (congrArg Subtype.val hσ'2)
    (fun i hi => congrArg Subtype.val (hσ'A ⟨i, hi⟩))
  have h1' : σ' = 1 := Subtype.ext h1
  rw [hσ'] at h1'
  calc σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
    _ = 1 := by rw [h1']; group

end Group

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24Side

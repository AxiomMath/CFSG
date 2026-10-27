module

public import Certificates.Data.Kernel.Spor.Pc2Base
public import CFSG.Certificates.Kernel.Spor.CommBaseSound
public import CFSG.Certificates.Kernel.Common.PcChain

public section

namespace CFSG.KC.Pc2Base

open CFSG.KC.Enum CFSG.KC.CommBase CFSG.KC.PcChain CFSG.KS CFSG.KS.Raw.Orb

theorem bit_eq (e k : ℕ) : bit e k = e.testBit k := by
  unfold bit
  have h1 : Nat.land (Nat.shiftRight e k) 1 = e / 2 ^ k % 2 := by
    rw [← Nat.shiftRight_eq_div_pow]
    exact Nat.and_one_is_mod _
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ k) with h | h <;> rw [h] <;> rfl

theorem p2_eq (k : ℕ) : p2 k = 2 ^ k := by
  change 1 <<< k = 2 ^ k
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem hiOnly_iff (e k : ℕ) : hiOnly e k = true ↔ e % 2 ^ k = 0 := by
  unfold hiOnly
  rw [Nat.beq_eq, p2_eq]
  change e &&& 2 ^ k - 1 = 0 ↔ _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem testBit_of_hiOnly {e k : ℕ} (h : hiOnly e k = true) {i : ℕ} (hi : i < k) :
    e.testBit i = false := by
  have h0 := (hiOnly_iff e k).1 h
  have := Nat.testBit_mod_two_pow e k i
  rw [h0, Nat.zero_testBit] at this
  simp only [hi, decide_true, Bool.true_and] at this
  exact this.symm

theorem wW_succ (e k m : ℕ) :
    wW e k (m + 1) = if e.testBit k then k :: wW e (k + 1) m else wW e (k + 1) m := by
  rw [← bit_eq]
  change Bool.rec (motive := fun _ => List Nat) (wW e (k + 1) m) (k :: wW e (k + 1) m) (bit e k) = _
  cases bit e k <;> rfl

theorem wW_mem (e : ℕ) : ∀ (m k z : ℕ), z ∈ wW e k m → k ≤ z ∧ z < k + m
  | 0, _, _, h => absurd h List.not_mem_nil
  | m + 1, k, z, h => by
    rw [wW_succ] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := wW_mem e m (k + 1) z h
        omega
    · have := wW_mem e m (k + 1) z h
      omega

variable {N w n : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin N)} {B : List ℕ}
  {H : Subgroup (Equiv.Perm (Fin N))}

theorem word_cons (z : ℕ) (W : List ℕ) : word ℓ (z :: W) = ℓ z * word ℓ W := by
  simp only [word, List.map_cons, List.prod_cons]

theorem word_wW (e : ℕ) : ∀ (m k : ℕ), word ℓ (wW e k m) = wfrom ℓ e k m
  | 0, _ => rfl
  | m + 1, k => by
    rw [wW_succ, wfrom_succ]
    by_cases h : e.testBit k
    · rw [if_pos h, if_pos h, word_cons, word_wW e m (k + 1)]
    · rw [if_neg h, if_neg h, word_wW e m (k + 1)]

theorem word_mem (hH : ∀ k < n, ℓ k ∈ H) {W : List ℕ} (hW : ∀ z ∈ W, z < n) :
    word ℓ W ∈ H := by
  change (W.map ℓ).prod ∈ H
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hg
  exact hH z (hW z hz)

theorem eq_of_wEq (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
    (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {U V : List ℕ} (hU : ∀ z ∈ U, z < n) (hV : ∀ z ∈ V, z < n)
    (h : wEq w (mask w) L B U V = true) : word ℓ U = word ℓ V := by
  rw [wEq, allL_iff] at h
  have hg := hB ((word ℓ V)⁻¹ * word ℓ U)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ (word_mem hH hV)) (word_mem hH hU)) fun b hb hbN => by
      have e := Nat.eq_of_beq_eq_true (h b hb)
      have e' : (word ℓ U ⟨b, hbN⟩ : ℕ) = word ℓ V ⟨b, hbN⟩ := by
        rw [← wapp_eq hL hU, ← wapp_eq hL hV]
        exact e
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
      exact Fin.ext e'
  exact (inv_mul_eq_one.1 hg).symm

theorem wW_lt (e n : ℕ) : ∀ z ∈ wW e 0 n, z < n := fun z hz => by
  have := wW_mem e n 0 z hz
  omega

theorem rel_eqs (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
    (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {R : List (List ℕ)} (h : relOK w (mask w) L B R n = true) :
    (∀ k < n, ℓ k * ℓ k = wfrom ℓ (rel R k k) 0 n) ∧
    (∀ k j, k < j → j < n → ℓ k * ℓ j = wfrom ℓ (rel R k j) 0 n * ℓ k) := by
  rw [relOK, allN_iff] at h
  refine ⟨fun k hk => ?_, fun k j hkj hj => ?_⟩
  · have hk' := allN_iff.1 (h k hk) k hk
    beta_reduce at hk'
    rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), bIf_eq, if_pos (by rw [Nat.beq_eq])] at hk'
    have e := eq_of_wEq hL hH hB (U := [k, k]) (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      omega) (wW_lt _ n) hk'
    rw [word_wW] at e
    rw [← e, word_cons, word_cons]
    simp [word]
  · have hk' := allN_iff.1 (h k (by omega)) j hj
    beta_reduce at hk'
    rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), bIf_eq, if_neg (by rw [Nat.beq_eq]; omega)]
      at hk'
    have hV : ∀ z ∈ List.append (wW (rel R k j) 0 n) [k], z < n := fun z hz => by
      rcases List.mem_append.1 hz with hz | hz
      · exact wW_lt _ n z hz
      · rw [List.mem_singleton.1 hz]
        omega
    have e := eq_of_wEq hL hH hB (U := [k, j]) (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      omega) hV hk'
    have e2 : word ℓ (List.append (wW (rel R k j) 0 n) [k]) = wfrom ℓ (rel R k j) 0 n * ℓ k := by
      change ((wW (rel R k j) 0 n ++ [k]).map ℓ).prod = _
      rw [List.map_append, List.prod_append]
      change word ℓ (wW (rel R k j) 0 n) * _ = _
      rw [word_wW]
      simp
    rw [← e2, ← e, word_cons, word_cons]
    simp [word]

theorem shape_facts {R : List (List ℕ)} {m : ℕ} (h : shapeOK R n m = true) {k j : ℕ} (hkj : k ≤ j)
    (hj : j < n) :
    rel R k j < 2 ^ n ∧ (∀ i ≤ k, (rel R k j).testBit i = false) ∧
    (k < m → m ≤ j → ∀ i < m, (rel R k j).testBit i = false) ∧
    (m ≤ k → j = k → rel R k j = 0) ∧ (m ≤ k → k < j → rel R k j = 2 ^ j) := by
  rw [shapeOK, allN_iff] at h
  have h1 := allN_iff.1 (h k (by omega)) j hj
  beta_reduce at h1
  rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), strictB_eq] at h1
  beta_reduce at h1
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, p2_eq] at h1
  obtain ⟨hlt, hhi, hc⟩ := h1
  refine ⟨hlt, fun i hi => testBit_of_hiOnly hhi (by change i < k + 1; omega),
    fun hkm hmj i hi => ?_,
    fun hmk hjk => ?_, fun hmk hkj' => ?_⟩
  · rw [bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hkm), bIf_eq,
      if_neg (by rw [Nat.blt_eq]; omega)] at hc
    exact testBit_of_hiOnly hc hi
  · rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), bIf_eq, if_pos (by rw [Nat.beq_eq]; exact hjk),
      Nat.beq_eq] at hc
    exact hc
  · rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; omega), bIf_eq, if_neg (by rw [Nat.beq_eq]; omega),
      Nat.beq_eq, p2_eq] at hc
    exact hc

theorem wfrom_mem_of_low {e k : ℕ} (hk : k < n) (he : ∀ i ≤ k, e.testBit i = false) :
    wfrom ℓ e 0 n ∈ Subgroup.closure (ℓ '' Set.Ico (k + 1) n) := by
  have hn : k + 1 + (n - (k + 1)) = n := by omega
  have e1 : wfrom ℓ e 0 n = wfrom ℓ e (0 + (k + 1)) (n - (k + 1)) := by
    rw [← wfrom_skip ℓ e (k + 1) 0 (n - (k + 1)) fun j _ hj => he j (by omega), hn]
  rw [e1, Nat.zero_add]
  exact wfrom_mem' ℓ e (by omega)

theorem pcRel_of_checks (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
    (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {R : List (List ℕ)} {m : ℕ} (hs : shapeOK R n m = true) (hr : relOK w (mask w) L B R n = true) :
    PcRel ℓ n := by
  obtain ⟨hsq, hcj⟩ := rel_eqs hL hH hB hr
  refine ⟨fun k hk => ?_, fun k j hkj hj => ?_⟩
  · rw [hsq k hk]
    exact wfrom_mem_of_low hk (shape_facts hs le_rfl hk).2.1
  · rw [hcj k j hkj hj, mul_inv_cancel_right]
    exact wfrom_mem_of_low (by omega) (shape_facts hs hkj.le hj).2.1

theorem memL_iff {O : List ℕ} {y : ℕ} : memL O y = true ↔ y ∈ O := by
  rw [memL, anyL_iff]
  constructor
  · rintro ⟨o, ho, e⟩
    rwa [← Nat.eq_of_beq_eq_true e]
  · intro hy
    exact ⟨y, hy, Nat.beq_refl y⟩

theorem inv_mem_of_closed {g : Equiv.Perm (Fin N)} {S : Set (Fin N)} (h : ∀ y ∈ S, g y ∈ S) :
    ∀ y ∈ S, g⁻¹ y ∈ S := by
  have hp : ∀ t : ℕ, ∀ y ∈ S, (g ^ t) y ∈ S := by
    intro t
    induction t with
    | zero => intro y hy; simpa using hy
    | succ t ih =>
      intro y hy
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact h _ (ih y hy)
  have e : g⁻¹ = g ^ (orderOf g - 1) := by
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
  intro y hy
  rw [e]
  exact hp _ y hy

theorem ne_wfrom_of_sepK (hL : ∀ z < n, PRep N w (L z) (ℓ z)) {k v x : ℕ} {O : List ℕ}
    (hk : k < n) (h : sepK N w (mask w) L n k v x O = true) (e : ℕ) :
    ℓ k ≠ wfrom ℓ e (k + 1) (n - (k + 1)) := by
  rw [sepK, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Nat.beq_eq, memL_iff, Nat.blt_eq, allL_iff] at h
  obtain ⟨hv, hvO, hxO, hxN, hcl⟩ := h
  have hxO' : x ∉ O := fun hx => by
    have h1 := notB_true hxO
    rw [(memL_iff (O := O) (y := x)).2 hx] at h1
    exact absurd h1 (by decide)
  let S : Set (Fin N) := {y | (y : ℕ) ∈ O}
  have hS : ∀ y ∈ S, ∀ j, k < j → j < n → (ℓ j)⁻¹ • y ∈ S := by
    intro y hy j hkj hj
    rw [Equiv.Perm.smul_def]
    refine inv_mem_of_closed (g := ℓ j) (fun y hy => ?_) y hy
    have hy' := hcl (y : ℕ) hy
    beta_reduce at hy'
    rw [bAnd_eq, Bool.and_eq_true, allN_iff] at hy'
    have hj' := hy'.2 j hj
    beta_reduce at hj'
    rw [bIf_eq, if_pos (by rw [Nat.blt_eq]; exact hkj), memL_iff, hL j hj y] at hj'
    exact hj'
  have hv' : ℓ k ⟨x, hxN⟩ ∈ S := by
    change ((ℓ k ⟨x, hxN⟩ : Fin N) : ℕ) ∈ O
    rw [← hL k hk ⟨x, hxN⟩]
    change pg w (mask w) (L k) x ∈ O
    rw [hv]
    exact hvO
  refine ne_wfrom_of_orbit ℓ S hk hS hv' ?_ e
  have e1 : (ℓ k)⁻¹ (ℓ k ⟨x, hxN⟩) = ⟨x, hxN⟩ := by simp
  rw [Equiv.Perm.smul_def, e1]
  exact hxO'

theorem card_of_checks (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
    (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {R : List (List ℕ)} {m : ℕ} {SEP : List (ℕ × ℕ × List ℕ)} (hs : shapeOK R n m = true)
    (hr : relOK w (mask w) L B R n = true) (hp : sepOK N w (mask w) L n SEP = true) :
    Nat.card (Subgroup.closure (ℓ '' Set.Ico 0 n)) = 2 ^ n := by
  refine card_closure (pcRel_of_checks hL hH hB hs hr) fun k hk e => ?_
  rw [sepOK, allN_iff] at hp
  exact ne_wfrom_of_sepK hL hk (hp k hk) e

theorem pc2OK_parts {N w mk : ℕ} {L : ℕ → ℕ} {B : List ℕ} {n m uI dI : ℕ} {R : List (List ℕ)}
    {SEP : List (ℕ × ℕ × List ℕ)} {CO : List (ℕ × ℕ)} {wit : ℕ}
    (h : pc2OK N w mk L B n m uI dI R SEP CO wit = true) :
    m ≤ dI ∧ dI < n ∧ m ≤ uI ∧ uI < n ∧ uI ≠ dI ∧ shapeOK R n m = true ∧
    relOK w mk L B R n = true ∧ sepOK N w mk L n SEP = true ∧ coOK w mk L B R n m dI CO = true ∧
    cenOK R n m uI dI = true ∧ witOK w mk L B n uI dI wit = true := by
  simp only [pc2OK, bAnd_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, fun e => ?_, h6, h7, h8, h9, h10, h11⟩
  rw [e, Nat.beq_refl] at h5
  exact absurd h5 (by decide)

theorem card_of_pc2OK (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
    (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {m uI dI : ℕ} {R : List (List ℕ)} {SEP : List (ℕ × ℕ × List ℕ)} {CO : List (ℕ × ℕ)} {wit : ℕ}
    (h : pc2OK N w (mask w) L B n m uI dI R SEP CO wit = true) :
    Nat.card (Subgroup.closure (ℓ '' Set.Ico 0 n)) = 2 ^ n := by
  obtain ⟨-, -, -, -, -, hs, hr, hp, -⟩ := pc2OK_parts h
  exact card_of_checks hL hH hB hs hr hp

section NormalForms

variable {G : Type*} [Group G]

theorem wfrom_split (x : ℕ → G) (e : ℕ) :
    ∀ (a b k : ℕ), wfrom x e k (a + b) = wfrom x e k a * wfrom x e (k + a) b
  | 0, b, k => by simp [wfrom_zero]
  | a + 1, b, k => by
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    have h2 : k + 1 + a = k + (a + 1) := by omega
    rw [h1, wfrom_succ, wfrom_succ, wfrom_split x e a b (k + 1), h2]
    split <;> simp [mul_assoc]

theorem wfrom_shift (x : ℕ → G) (e m : ℕ) :
    ∀ (K k : ℕ), wfrom x e (m + k) K = wfrom (fun i => x (m + i)) (e / 2 ^ m) k K
  | 0, _ => rfl
  | K + 1, k => by
    have ih := wfrom_shift x e m K (k + 1)
    rw [wfrom_succ, wfrom_succ, Nat.testBit_div_two_pow, Nat.add_comm k m, ← ih, Nat.add_assoc]

theorem wfrom_eq_one (x : ℕ → G) {e : ℕ} :
    ∀ (K k : ℕ), (∀ j, k ≤ j → j < k + K → e.testBit j = false) → wfrom x e k K = 1 := by
  intro K k h
  rw [wfrom_congr x (e' := 0) K k fun j h1 h2 => by rw [h j h1 h2, Nat.zero_testBit]]
  exact wfrom_zero_e x K k

theorem wfrom_two_pow (x : ℕ → G) {j : ℕ} :
    ∀ (K k : ℕ), k ≤ j → j < k + K → wfrom x (2 ^ j) k K = x j
  | 0, _, h1, h2 => by omega
  | K + 1, k, h1, h2 => by
    rw [wfrom_succ, Nat.testBit_two_pow]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos (by simp), wfrom_eq_one x K (j + 1) fun i h3 _ => by
        rw [Nat.testBit_two_pow]
        simp only [decide_eq_false_iff_not]
        omega, mul_one]
    · rw [if_neg (by simp only [decide_eq_true_eq]; exact hjk)]
      exact wfrom_two_pow x K (k + 1) (by omega) (by omega)

theorem mod_two_pow_succ_xor (v t : ℕ) :
    v % 2 ^ (t + 1) = v % 2 ^ t ^^^ (if v.testBit t then 2 ^ t else 0) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  split
  · rw [Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i t with h | h | h
    · have h1 : i < t + 1 := by omega
      have h2 : t ≠ i := by omega
      simp [h, h1, h2]
    · subst h
      simp_all
    · have h1 : ¬ i < t := by omega
      have h2 : ¬ i < t + 1 := by omega
      have h3 : t ≠ i := by omega
      simp [h1, h2, h3]
  · rename_i hb
    rw [Nat.zero_testBit, Bool.xor_false]
    rcases Nat.lt_trichotomy i t with h | h | h
    · have h1 : i < t + 1 := by omega
      simp [h, h1]
    · subst h
      simp_all
    · have h1 : ¬ i < t := by omega
      have h2 : ¬ i < t + 1 := by omega
      simp [h1, h2]

end NormalForms

section Abelian

variable {G : Type*} [Group G] (x : ℕ → G) (m K : ℕ)

@[expose] def av (v : ℕ) : G := wfrom (fun i => x (m + i)) v 0 K

@[expose] noncomputable def foldX (c : ℕ → ℕ) (v t : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (nIf(bit v i, c i, nat_lit 0))) t

theorem foldX_succ (c : ℕ → ℕ) (v t : ℕ) :
    foldX c v (t + 1) = foldX c v t ^^^ (if v.testBit t then c t else 0) := by
  change Nat.xor (foldX c v t) (nIf(bit v t, c t, nat_lit 0)) = _
  rw [nIf_eq, bit_eq]
  rfl

theorem mx_eq (R : List (List ℕ)) (n m k v : ℕ) :
    mx R n m k v = foldX (fun i => Nat.shiftRight (rel R k (m + i)) m) v (n - m) := rfl

variable {x m K}
variable (hsq : ∀ i < K, x (m + i) * x (m + i) = 1)
  (hc : ∀ i < K, ∀ j < K, x (m + i) * x (m + j) = x (m + j) * x (m + i))
include hsq hc

theorem av_xor (a b : ℕ) : av x m K a * av x m K b = av x m K (a ^^^ b) :=
  wfrom_mul_xor a b K 0 (fun i j _ hi _ hj => hc i (by omega) j (by omega))
    fun i _ hi => hsq i (by omega)

omit hsq hc in
theorem av_zero : av x m K 0 = 1 := wfrom_zero_e _ K 0

omit hsq hc in
theorem av_two_pow {i : ℕ} (hi : i < K) : av x m K (2 ^ i) = x (m + i) :=
  wfrom_two_pow _ K 0 (Nat.zero_le i) (by omega)

omit hsq hc in
theorem av_mod (v : ℕ) : av x m K (v % 2 ^ K) = av x m K v :=
  wfrom_congr _ K 0 fun j _ hj => by
    have hjK : j < K := by omega
    rw [Nat.testBit_mod_two_pow]
    simp [hjK]

theorem av_mul_self (a : ℕ) : av x m K a * av x m K a = 1 := by
  rw [av_xor hsq hc, Nat.xor_self, av_zero]

theorem av_comm (a b : ℕ) : av x m K a * av x m K b = av x m K b * av x m K a := by
  rw [av_xor hsq hc, av_xor hsq hc, Nat.xor_comm]

theorem av_inv (a : ℕ) : (av x m K a)⁻¹ = av x m K a :=
  inv_eq_of_mul_eq_one_right (av_mul_self hsq hc a)

theorem hom_av (φ : G →* G) {c : ℕ → ℕ} (hφ : ∀ i < K, φ (x (m + i)) = av x m K (c i)) (v : ℕ) :
    φ (av x m K v) = av x m K (foldX c v K) := by
  have key : ∀ t ≤ K, φ (av x m K (v % 2 ^ t)) = av x m K (foldX c v t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [pow_zero, Nat.mod_one]
      change φ (av x m K 0) = av x m K 0
      rw [av_zero, map_one]
    | succ t ih =>
      intro ht
      rw [mod_two_pow_succ_xor, ← av_xor hsq hc, map_mul, ih (by omega), foldX_succ,
        ← av_xor hsq hc]
      congr 1
      split
      · rw [av_two_pow (by omega), hφ t (by omega)]
      · rw [av_zero, map_one]
  rw [← key K le_rfl, av_mod]

end Abelian

theorem testBit_ite (p : Bool) (c i : ℕ) : (if p = true then c else 0).testBit i = (p && c.testBit i) := by
  cases p <;> simp

theorem foldX_xor (c : ℕ → ℕ) (a b : ℕ) :
    ∀ t, foldX c (a ^^^ b) t = foldX c a t ^^^ foldX c b t
  | 0 => (Nat.xor_zero 0).symm
  | t + 1 => by
    rw [foldX_succ, foldX_succ, foldX_succ, foldX_xor c a b t]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, testBit_ite]
    cases (foldX c a t).testBit i <;> cases (foldX c b t).testBit i <;> cases a.testBit t <;>
      cases b.testBit t <;> cases (c t).testBit i <;> rfl

theorem foldX_lt {c : ℕ → ℕ} {K : ℕ} (v : ℕ) :
    ∀ t, (∀ i < t, c i < 2 ^ K) → foldX c v t < 2 ^ K
  | 0, _ => Nat.two_pow_pos K
  | t + 1, hc => by
    rw [foldX_succ]
    refine Nat.xor_lt_two_pow (foldX_lt v t fun i hi => hc i (by omega)) ?_
    split
    · exact hc t (by omega)
    · exact Nat.two_pow_pos K

theorem mw_xor (R : List (List ℕ)) (n m : ℕ) (a b : ℕ) :
    ∀ W : List ℕ, mw R n m W (a ^^^ b) = mw R n m W a ^^^ mw R n m W b
  | [] => rfl
  | z :: W => by
    change mx R n m z (mw R n m W (a ^^^ b)) = mx R n m z (mw R n m W a) ^^^ mx R n m z (mw R n m W b)
    rw [mw_xor R n m a b W, mx_eq, mx_eq, mx_eq, foldX_xor]

theorem mw_lt {R : List (List ℕ)} {n m : ℕ} (hmn : m ≤ n)
    (hR : ∀ k < m, ∀ i < n - m, rel R k (m + i) < 2 ^ n) {v : ℕ}
    (hv : v < 2 ^ (n - m)) : ∀ W : List ℕ, (∀ z ∈ W, z < m) → mw R n m W v < 2 ^ (n - m)
  | [], _ => hv
  | z :: W, hW => by
    change mx R n m z (mw R n m W v) < _
    rw [mx_eq]
    refine foldX_lt _ _ fun i hi => ?_
    change rel R z (m + i) >>> m < 2 ^ (n - m)
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_lt_of_lt_mul (by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hmn]
      exact hR z (hW z List.mem_cons_self) i hi)

theorem dt_succ (K φ b : ℕ) :
    dt (K + 1) φ b = (dt K φ b ^^ (φ.testBit K && b.testBit K)) := by
  change Bool.rec (motive := fun _ => Bool) (dt K φ b) (CFSG.KC.CommBase.notB (dt K φ b)) (bit (Nat.land φ b) K) = _
  rw [bit_eq]
  change Bool.rec (motive := fun _ => Bool) (dt K φ b) (CFSG.KC.CommBase.notB (dt K φ b)) ((φ &&& b).testBit K) = _
  rw [Nat.testBit_and]
  cases dt K φ b <;> cases φ.testBit K <;> cases b.testBit K <;> rfl

theorem dt_xor (φ a b : ℕ) : ∀ K, dt K φ (a ^^^ b) = (dt K φ a ^^ dt K φ b)
  | 0 => rfl
  | K + 1 => by
    rw [dt_succ, dt_succ, dt_succ, dt_xor φ a b K, Nat.testBit_xor]
    cases dt K φ a <;> cases dt K φ b <;> cases φ.testBit K <;> cases a.testBit K <;>
      cases b.testBit K <;> rfl

theorem dt_zero (φ : ℕ) : ∀ K, dt K φ 0 = false
  | 0 => rfl
  | K + 1 => by rw [dt_succ, dt_zero φ K, Nat.zero_testBit, Bool.and_false]; rfl

theorem dt_lin {f : ℕ → ℕ} (hf : ∀ a b, f (a ^^^ b) = f a ^^^ f b) {K φ : ℕ}
    (h : ∀ j < K, dt K φ (f (2 ^ j)) = false) {v : ℕ} (hv : v < 2 ^ K) : dt K φ (f v) = false := by
  have f0 : f 0 = 0 := by
    have := hf 0 0
    rw [Nat.xor_self] at this
    have e2 : f 0 ^^^ f 0 = 0 := Nat.xor_self _
    rw [← this] at e2
    exact e2
  have key : ∀ t ≤ K, dt K φ (f (v % 2 ^ t)) = false := by
    intro t
    induction t with
    | zero => intro _; rw [pow_zero, Nat.mod_one, f0, dt_zero]
    | succ t ih =>
      intro ht
      rw [mod_two_pow_succ_xor, hf, dt_xor, ih (by omega)]
      split
      · rw [h t (by omega)]
        rfl
      · rw [f0, dt_zero]
        rfl
  have := key K le_rfl
  rwa [Nat.mod_eq_of_lt hv] at this

theorem coOK_rec {w mk : ℕ} {L : ℕ → ℕ} {B : List ℕ} {R : List (List ℕ)} {n m dI : ℕ}
    {CO : List (ℕ × ℕ)} (h : coOK w mk L B R n m dI CO = true) {e : ℕ} (he : e < 2 ^ m) :
    (CO.getD e (0, 0)).1 < 2 ^ n ∧
    (∀ b ∈ B, wapp w mk L (wW e 0 m) (wapp w mk L (wW e 0 m) b) =
      wapp w mk L (wW (CO.getD e (0, 0)).1 0 n) b) ∧
    (hiOnly (CO.getD e (0, 0)).1 m = true →
      (∀ j < n - m, dt (n - m) (CO.getD e (0, 0)).2
        (mw R n m (wW e 0 m) (2 ^ j) ^^^ 2 ^ j) = false) ∧
      dt (n - m) (CO.getD e (0, 0)).2 (2 ^ (dI - m) ^^^ (CO.getD e (0, 0)).1 >>> m) = true) := by
  rw [coOK, allN_iff] at h
  have h1 := h e (by rw [p2_eq]; exact he)
  beta_reduce at h1
  rw [coK, bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, p2_eq, allL_iff,
    bIf_eq] at h1
  obtain ⟨hf, hb, hc⟩ := h1
  refine ⟨hf, fun b hb' => Nat.eq_of_beq_eq_true (hb b hb'), fun hlo => ?_⟩
  rw [if_pos hlo, bAnd_eq, Bool.and_eq_true, allN_iff] at hc
  obtain ⟨hc1, hc2⟩ := hc
  refine ⟨fun j hj => ?_, ?_⟩
  · have := hc1 j hj
    beta_reduce at this
    rw [p2_eq] at this
    exact notB_true this
  · rw [p2_eq] at hc2
    exact hc2

theorem inZ_iff (m uI dI a : ℕ) : inZ m uI dI a = true ↔
    (a = 0 ∨ a = 2 ^ (uI - m) ∨ a = 2 ^ (dI - m) ∨ a = 2 ^ (uI - m) ^^^ 2 ^ (dI - m)) := by
  unfold inZ
  simp only [bIf_eq, Nat.beq_eq, p2_eq]
  split_ifs <;> simp_all

theorem cenOK_facts {R : List (List ℕ)} {n m uI dI : ℕ} (hd1 : m ≤ dI) (hd2 : dI < n)
    (h : cenOK R n m uI dI = true) :
    (∀ e < 2 ^ m, e ≠ 0 → ∃ j < n - m, mw R n m (wW e 0 m) (2 ^ j) ≠ 2 ^ j) ∧
    (∀ a < 2 ^ (n - m), (∀ k < m, mx R n m k a = a) →
      (a = 0 ∨ a = 2 ^ (uI - m) ∨ a = 2 ^ (dI - m) ∨ a = 2 ^ (uI - m) ^^^ 2 ^ (dI - m))) ∧
    (∀ k < m, mx R n m k (2 ^ (dI - m)) = 2 ^ (dI - m)) := by
  rw [cenOK, bAnd_eq, Bool.and_eq_true, allN_iff, allN_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hfix : ∀ a < 2 ^ (n - m), ((∀ k < m, mx R n m k a = a) ↔ inZ m uI dI a = true) := by
    intro a ha
    have := h2 a (by rw [p2_eq]; exact ha)
    beta_reduce at this
    rw [bIf_eq] at this
    have e1 : allN m (fun k => Nat.beq (mx R n m k a) a) = true ↔ ∀ k < m, mx R n m k a = a := by
      rw [allN_iff]
      exact forall₂_congr fun k _ => by rw [Nat.beq_eq]
    rw [← e1]
    split_ifs at this with hh
    · exact ⟨fun _ => this, fun _ => hh⟩
    · have := notB_true this
      constructor
      · intro hx
        exact absurd hx hh
      · intro hx
        rw [hx] at this
        exact absurd this (by decide)
  refine ⟨fun e he he0 => ?_, fun a ha hk => (inZ_iff m uI dI a).1 ((hfix a ha).1 hk), ?_⟩
  · have := h1 e (by rw [p2_eq]; exact he)
    beta_reduce at this
    rw [bIf_eq, if_neg (by rw [Nat.beq_eq]; exact he0)] at this
    have h3 := notB_true this
    by_contra hall
    push Not at hall
    have : allN (Nat.sub n m) (fun j => Nat.beq (mw R n m (wW e 0 m) (p2 j)) (p2 j)) = true := by
      rw [allN_iff]
      intro j hj
      rw [Nat.beq_eq, p2_eq]
      exact hall j hj
    rw [this] at h3
    exact absurd h3 (by decide)
  · intro k hk
    exact (hfix _ (Nat.pow_lt_pow_right (by norm_num) (by omega))).2
      ((inZ_iff m uI dI _).2 (Or.inr (Or.inr (Or.inl rfl)))) k hk

section Group

variable {N w n : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin N)} {B : List ℕ}
  {H : Subgroup (Equiv.Perm (Fin N))}

theorem eq_of_base (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
    {g h : Equiv.Perm (Fin N)} (hg : g ∈ H) (hh : h ∈ H)
    (he : ∀ b ∈ B, ∀ hb : b < N, (g ⟨b, hb⟩ : ℕ) = h ⟨b, hb⟩) : g = h := by
  have := hB (h⁻¹ * g) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh) hg) fun b hb hbN => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
    exact Fin.ext (he b hb hbN)
  exact (inv_mul_eq_one.1 this).symm

variable (hL : ∀ z < n, PRep N w (L z) (ℓ z)) (hH : ∀ k < n, ℓ k ∈ H)
  (hB : ∀ g ∈ H, (∀ b ∈ B, ∀ h : b < N, g ⟨b, h⟩ = ⟨b, h⟩) → g = 1)
  {m uI dI : ℕ} {R : List (List ℕ)} {SEP : List (ℕ × ℕ × List ℕ)} {CO : List (ℕ × ℕ)} {wit : ℕ}
  (hc : pc2OK N w (mask w) L B n m uI dI R SEP CO wit = true)
include hL hH hB hc

theorem uniq_of_pc2OK {e e' : ℕ} (h : wfrom ℓ e 0 n = wfrom ℓ e' 0 n) {j : ℕ} (hj : j < n) :
    e.testBit j = e'.testBit j := by
  obtain ⟨-, -, -, -, -, hs, hr, hp, -⟩ := pc2OK_parts hc
  have hsep : ∀ k < n, ∀ e, ℓ k ≠ wfrom ℓ e (k + 1) (n - (k + 1)) := fun k hk e => by
    rw [sepOK, allN_iff] at hp
    exact ne_wfrom_of_sepK hL hk (hp k hk) e
  exact testBit_eq_of_wfrom_eq (pcRel_of_checks hL hH hB hs hr) hsep n le_rfl e e'
    (by rw [Nat.sub_self]; exact h) j (by omega) hj

theorem abelian_of_pc2OK :
    (∀ i < n - m, ℓ (m + i) * ℓ (m + i) = 1) ∧
    (∀ i < n - m, ∀ j < n - m, ℓ (m + i) * ℓ (m + j) = ℓ (m + j) * ℓ (m + i)) := by
  obtain ⟨-, -, -, -, -, hs, hr, -⟩ := pc2OK_parts hc
  obtain ⟨hsq, hcj⟩ := rel_eqs hL hH hB hr
  have hc2 : ∀ a b, m ≤ a → a < b → b < n → ℓ a * ℓ b = ℓ b * ℓ a := by
    intro a b ha hab hb
    rw [hcj a b hab hb, (shape_facts hs hab.le hb).2.2.2.2 ha hab,
      wfrom_two_pow ℓ n 0 (Nat.zero_le b) (by omega)]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · rw [hsq (m + i) (by omega), (shape_facts hs le_rfl (by omega)).2.2.2.1 (by omega) rfl]
    exact wfrom_zero_e ℓ n 0
  · rcases Nat.lt_trichotomy i j with h | rfl | h
    · exact hc2 _ _ (by omega) (by omega) (by omega)
    · rfl
    · exact (hc2 _ _ (by omega) (by omega) (by omega)).symm

theorem low_of_pc2OK {e : ℕ} (he : ∀ i < m, e.testBit i = false) :
    wfrom ℓ e 0 n = av ℓ m (n - m) (e / 2 ^ m) := by
  obtain ⟨hmd, hdn, -⟩ := pc2OK_parts hc
  have hn : n = m + (n - m) := by omega
  rw [hn, wfrom_split, wfrom_eq_one ℓ m 0 fun j _ hj => he j (by omega), one_mul, Nat.zero_add,
    ← Nat.add_zero m, wfrom_shift, Nat.add_zero, ← hn]
  rfl

theorem av_eq_wfrom (v : ℕ) : av ℓ m (n - m) v = wfrom ℓ (v * 2 ^ m) 0 n := by
  rw [low_of_pc2OK hL hH hB hc fun i hi => ?_, Nat.mul_div_cancel v (Nat.two_pow_pos m)]
  rw [← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
  simp only [ge_iff_le, Bool.and_eq_false_imp, decide_eq_true_eq]
  intro h
  omega

theorem av_inj {a b : ℕ} (ha : a < 2 ^ (n - m)) (hb : b < 2 ^ (n - m))
    (h : av ℓ m (n - m) a = av ℓ m (n - m) b) : a = b := by
  obtain ⟨hmd, hdn, -⟩ := pc2OK_parts hc
  rw [av_eq_wfrom hL hH hB hc, av_eq_wfrom hL hH hB hc] at h
  apply Nat.eq_of_testBit_eq
  intro i
  rcases Nat.lt_or_ge i (n - m) with hi | hi
  · have := uniq_of_pc2OK hL hH hB hc h (j := m + i) (by omega)
    rw [← Nat.shiftLeft_eq, ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft] at this
    simpa using this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hi)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hi))]

theorem conj_of_pc2OK {k : ℕ} (hk : k < m) (v : ℕ) :
    ℓ k * av ℓ m (n - m) v * (ℓ k)⁻¹ = av ℓ m (n - m) (mx R n m k v) := by
  obtain ⟨hmd, hdn, -, -, -, hs, hr, -⟩ := pc2OK_parts hc
  obtain ⟨hsqA, hcA⟩ := abelian_of_pc2OK hL hH hB hc
  obtain ⟨-, hcj⟩ := rel_eqs hL hH hB hr
  have hφ : ∀ i < n - m, (MulAut.conj (ℓ k)).toMonoidHom (ℓ (m + i)) =
      av ℓ m (n - m) (Nat.shiftRight (rel R k (m + i)) m) := by
    intro i hi
    change ℓ k * ℓ (m + i) * (ℓ k)⁻¹ = _
    rw [hcj k (m + i) (by omega) (by omega), mul_inv_cancel_right,
      low_of_pc2OK hL hH hB hc ((shape_facts hs (by omega) (by omega)).2.2.1 hk (by omega))]
    change _ = av ℓ m (n - m) (rel R k (m + i) >>> m)
    rw [Nat.shiftRight_eq_div_pow]
  have := hom_av hsqA hcA (MulAut.conj (ℓ k)).toMonoidHom hφ v
  rw [mx_eq]
  exact this

theorem mw_conj_of_pc2OK (v : ℕ) :
    ∀ W : List ℕ, (∀ z ∈ W, z < m) →
      word ℓ W * av ℓ m (n - m) v * (word ℓ W)⁻¹ = av ℓ m (n - m) (mw R n m W v)
  | [], _ => by simp [word, mw]
  | z :: W, hW => by
    have ih := mw_conj_of_pc2OK v W fun a ha => hW a (List.mem_cons_of_mem z ha)
    change _ = av ℓ m (n - m) (mx R n m z (mw R n m W v))
    rw [← conj_of_pc2OK hL hH hB hc (hW z List.mem_cons_self), ← ih, word_cons]
    group

theorem mem_of_wfrom (e : ℕ) : wfrom ℓ e 0 n ∈ Subgroup.closure (ℓ '' Set.Ico 0 n) :=
  wfrom_mem' ℓ e (by omega)

omit hL hH hB hc in
theorem mem_of_lt {k : ℕ} (hk : k < n) : ℓ k ∈ Subgroup.closure (ℓ '' Set.Ico 0 n) :=
  Subgroup.subset_closure ⟨k, ⟨Nat.zero_le k, hk⟩, rfl⟩

theorem split_of_pc2OK {s : Equiv.Perm (Fin N)} (hs : s ∈ Subgroup.closure (ℓ '' Set.Ico 0 n)) :
    ∃ e < 2 ^ m, ∃ v < 2 ^ (n - m), s = word ℓ (wW e 0 m) * av ℓ m (n - m) v := by
  obtain ⟨hmd, hdn, -, -, -, hs', hr, -⟩ := pc2OK_parts hc
  obtain ⟨e', he'⟩ := exists_wfrom (pcRel_of_checks hL hH hB hs' hr) n le_rfl s
    (by rw [Nat.sub_self]; exact hs)
  rw [Nat.sub_self] at he'
  refine ⟨e' % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m), (e' / 2 ^ m) % 2 ^ (n - m),
    Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
  have hn : n = m + (n - m) := by omega
  rw [he', av_mod, word_wW, hn, wfrom_split, Nat.zero_add, ← hn]
  congr 1
  · refine wfrom_congr ℓ m 0 fun j _ hj => ?_
    have hjm : j < m := by omega
    rw [Nat.testBit_mod_two_pow]
    simp [hjm]
  · rw [← Nat.add_zero m, wfrom_shift, Nat.add_zero]
    rfl

omit hL hH hB hc in
theorem word_lt {e : ℕ} (hmn : m ≤ n) : ∀ z ∈ wW e 0 m, z < n := fun z hz => by
  have := wW_mem e m 0 z hz
  omega

theorem relBound_of_pc2OK : ∀ k < m, ∀ i < n - m, rel R k (m + i) < 2 ^ n := by
  obtain ⟨hmd, hdn, -, -, -, hs, -⟩ := pc2OK_parts hc
  intro k hk i hi
  exact (shape_facts hs (by omega) (by omega)).1

theorem facts_of_pc2OK :
    Nat.card (Subgroup.closure (ℓ '' Set.Ico 0 n)) = 2 ^ n ∧ ℓ dI * ℓ dI = 1 ∧ ℓ dI ≠ 1 ∧
    ℓ dI ≠ ℓ uI ∧ (∀ s ∈ Subgroup.closure (ℓ '' Set.Ico 0 n), s * ℓ dI = ℓ dI * s) ∧
    (∀ s ∈ Subgroup.closure (ℓ '' Set.Ico 0 n),
      (∀ x ∈ Subgroup.closure (ℓ '' Set.Ico 0 n), s * x = x * s) →
        s = 1 ∨ s = ℓ uI ∨ s = ℓ dI ∨ s = ℓ uI * ℓ dI) ∧
    (∀ s ∈ Subgroup.closure (ℓ '' Set.Ico 0 n), s * s ≠ ℓ dI) ∧
    (∃ s ∈ Subgroup.closure (ℓ '' Set.Ico 0 n), s * s = ℓ uI * ℓ dI) := by
  obtain ⟨hmd, hdn, hmu, hun, hud, hs, hr, hp, hco, hcen, hwit⟩ := pc2OK_parts hc
  obtain ⟨hsqA, hcA⟩ := abelian_of_pc2OK hL hH hB hc
  obtain ⟨cen1, cen2, cen3⟩ := cenOK_facts hmd hdn hcen
  have hR := relBound_of_pc2OK hL hH hB hc
  have hmn : m ≤ n := by omega
  have hWm0 : ∀ e, ∀ z ∈ wW e 0 m, z < m := fun e z hz => by
    have := (wW_mem e m 0 z hz).2
    omega
  have hdA : ℓ dI = av ℓ m (n - m) (2 ^ (dI - m)) := by
    rw [av_two_pow (by omega), Nat.add_sub_cancel' hmd]
  have huA : ℓ uI = av ℓ m (n - m) (2 ^ (uI - m)) := by
    rw [av_two_pow (by omega), Nat.add_sub_cancel' hmu]
  have hδ : 2 ^ (dI - m) < 2 ^ (n - m) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hx1 : ∀ j < n, ℓ j = wfrom ℓ (2 ^ j) 0 n := fun j hj =>
    (wfrom_two_pow ℓ n 0 (Nat.zero_le j) (by omega)).symm
  have hwm : ∀ e, word ℓ (wW e 0 m) ∈ H := fun e => word_mem hH (word_lt hmn)
  have hgen : ∀ k < n, ℓ k * ℓ dI = ℓ dI * ℓ k := by
    intro k hk
    rcases Nat.lt_or_ge k m with hkm | hkm
    · have e1 := conj_of_pc2OK hL hH hB hc hkm (2 ^ (dI - m))
      rw [cen3 k hkm, ← hdA] at e1
      exact mul_inv_eq_iff_eq_mul.1 e1
    · have := hcA (k - m) (by omega) (dI - m) (by omega)
      rwa [Nat.add_sub_cancel' hkm, Nat.add_sub_cancel' hmd] at this
  refine ⟨card_of_pc2OK hL hH hB hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := hsqA (dI - m) (by omega)
    rwa [Nat.add_sub_cancel' hmd] at this
  · intro h1
    have e1 : wfrom ℓ (2 ^ dI) 0 n = wfrom ℓ 0 0 n := by
      rw [← hx1 dI hdn, wfrom_zero_e, h1]
    have := uniq_of_pc2OK hL hH hB hc e1 hdn
    rw [Nat.testBit_two_pow_self, Nat.zero_testBit] at this
    exact absurd this (by decide)
  · intro h1
    have e1 : wfrom ℓ (2 ^ dI) 0 n = wfrom ℓ (2 ^ uI) 0 n := by
      rw [← hx1 dI hdn, ← hx1 uI hun, h1]
    have := uniq_of_pc2OK hL hH hB hc e1 hdn
    rw [Nat.testBit_two_pow_self, Nat.testBit_two_pow] at this
    exact hud (of_decide_eq_true this.symm)
  · intro s hs'
    induction hs' using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      exact hgen k hk.2
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb => exact Commute.mul_left ha hb
    | inv a _ ha => exact Commute.inv_left ha
  · intro s hs' hcen'
    obtain ⟨e, he, v, hv, rfl⟩ := split_of_pc2OK hL hH hB hc hs'
    have hrA : ∀ i < n - m, word ℓ (wW e 0 m) * av ℓ m (n - m) (2 ^ i) * (word ℓ (wW e 0 m))⁻¹ =
        av ℓ m (n - m) (2 ^ i) := by
      intro i hi
      have h1 := hcen' (ℓ (m + i)) (mem_of_lt (by omega))
      rw [← av_two_pow (x := ℓ) (m := m) (K := n - m) hi] at h1
      have h2 := av_comm hsqA hcA v (2 ^ i)
      have h3 : word ℓ (wW e 0 m) * av ℓ m (n - m) (2 ^ i) = av ℓ m (n - m) (2 ^ i) * word ℓ (wW e 0 m) := by
        refine mul_right_cancel (b := av ℓ m (n - m) v) ?_
        rw [mul_assoc, ← h2, ← mul_assoc, h1, mul_assoc]
      rw [h3, mul_inv_cancel_right]
    have he0 : e = 0 := by
      by_contra hne
      obtain ⟨j, hj, hj'⟩ := cen1 e he hne
      apply hj'
      have := hrA j hj
      rw [mw_conj_of_pc2OK hL hH hB hc _ _ (hWm0 e)] at this
      exact av_inj hL hH hB hc (mw_lt hmn hR (Nat.pow_lt_pow_right (by norm_num) hj) _
        (hWm0 e)) (Nat.pow_lt_pow_right (by norm_num) hj) this
    subst he0
    have hr1 : word ℓ (wW 0 0 m) = 1 := by rw [word_wW, wfrom_zero_e]
    rw [hr1, one_mul]
    rw [hr1, one_mul] at hcen'
    have hfix : ∀ k < m, mx R n m k v = v := by
      intro k hk
      have h1 := hcen' (ℓ k) (mem_of_lt (by omega))
      have h2 := conj_of_pc2OK hL hH hB hc hk v
      rw [← h1, mul_inv_cancel_right] at h2
      exact (av_inj hL hH hB hc hv (mw_lt hmn hR hv [k] fun z hz => by
        rw [List.mem_singleton.1 hz]
        exact hk) h2).symm
    rcases cen2 v hv hfix with h | h | h | h
    · left
      rw [h, av_zero]
    · right; left
      rw [h, ← huA]
    · right; right; left
      rw [h, ← hdA]
    · right; right; right
      rw [h, huA, hdA, av_xor hsqA hcA]
  · intro s hs' hsq'
    obtain ⟨e, he, v, hv, rfl⟩ := split_of_pc2OK hL hH hB hc hs'
    obtain ⟨hf, hbase, hφ⟩ := coOK_rec hco he
    set f := (CO.getD e (0, 0)).1
    set W := wW e 0 m
    have hW : ∀ z ∈ W, z < n := word_lt hmn
    have hWm : ∀ z ∈ W, z < m := hWm0 e
    have hrr : word ℓ W * word ℓ W = wfrom ℓ f 0 n := by
      rw [← word_wW]
      refine eq_of_base hB (Subgroup.mul_mem _ (hwm e) (hwm e)) (word_mem hH (wW_lt f n))
        fun b hb hbN => ?_
      rw [Equiv.Perm.mul_apply, ← wapp_eq hL hW, ← wapp_eq hL (wW_lt f n)]
      rw [← wapp_eq hL hW ⟨b, hbN⟩]
      exact hbase b hb
    have hconj := mw_conj_of_pc2OK hL hH hB hc v W hWm
    have hmwlt := mw_lt hmn hR hv W hWm
    have key : word ℓ W * av ℓ m (n - m) v * (word ℓ W * av ℓ m (n - m) v) =
        word ℓ W * av ℓ m (n - m) v * (word ℓ W)⁻¹ * (word ℓ W * word ℓ W) * av ℓ m (n - m) v := by group
    rw [key, hconj, hrr] at hsq'
    by_cases hlo : hiOnly f m = true
    · obtain ⟨hφ1, hφ2⟩ := hφ hlo
      rw [low_of_pc2OK hL hH hB hc fun i hi => testBit_of_hiOnly hlo hi, av_xor hsqA hcA,
        av_xor hsqA hcA, hdA] at hsq'
      have hflt : f / 2 ^ m < 2 ^ (n - m) := Nat.div_lt_of_lt_mul (by
        rw [← Nat.pow_add, Nat.add_sub_cancel' hmn]
        exact hf)
      have hX := av_inj hL hH hB hc (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hmwlt hflt) hv) hδ hsq'
      have hlin : dt (n - m) (CO.getD e (0, 0)).2 (mw R n m W v ^^^ v) = false := by
        refine dt_lin (f := fun a => mw R n m W a ^^^ a) (fun a b => ?_) hφ1 hv
        rw [mw_xor]
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_xor]
        cases (mw R n m W a).testBit i <;> cases (mw R n m W b).testBit i <;> cases a.testBit i <;>
          cases b.testBit i <;> rfl
      have e2 : 2 ^ (dI - m) ^^^ f >>> m = mw R n m W v ^^^ v := by
        rw [← hX, Nat.shiftRight_eq_div_pow]
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_xor]
        cases (mw R n m W v).testBit i <;> cases (f / 2 ^ m).testBit i <;> cases v.testBit i <;> rfl
      rw [e2, hlin] at hφ2
      exact absurd hφ2 (by decide)
    · apply hlo
      have hrr' : wfrom ℓ f 0 n =
          av ℓ m (n - m) ((mw R n m W v ^^^ 2 ^ (dI - m)) ^^^ v) := by
        have e3 : wfrom ℓ f 0 n = (av ℓ m (n - m) (mw R n m W v))⁻¹ * ℓ dI * (av ℓ m (n - m) v)⁻¹ := by
          rw [← hsq']
          group
        rw [e3, av_inv hsqA hcA, av_inv hsqA hcA, hdA, av_xor hsqA hcA, av_xor hsqA hcA]
      rw [av_eq_wfrom hL hH hB hc] at hrr'
      rw [hiOnly_iff]
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
      by_cases hi : i < m
      · rw [uniq_of_pc2OK hL hH hB hc hrr' (by omega), ← Nat.shiftLeft_eq, Nat.testBit_shiftLeft]
        simp [hi]
      · simp [hi]
  · refine ⟨wfrom ℓ wit 0 n, mem_of_wfrom hL hH hB hc wit, ?_⟩
    rw [← word_wW]
    refine eq_of_base hB (Subgroup.mul_mem _ (word_mem hH (wW_lt wit n))
      (word_mem hH (wW_lt wit n))) (Subgroup.mul_mem _ (hH uI hun) (hH dI hdn)) fun b hb hbN => ?_
    rw [witOK, allL_iff] at hwit
    have h1 := Nat.eq_of_beq_eq_true (hwit b hb)
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← wapp_eq hL (wW_lt wit n),
      ← wapp_eq hL (wW_lt wit n), ← hL uI hun, ← hL dI hdn]
    exact h1

end Group

end CFSG.KC.Pc2Base

end

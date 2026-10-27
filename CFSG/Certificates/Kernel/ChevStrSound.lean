module

public import Certificates.Data.Kernel.ChevStrK
public import CFSG.Blueprint.ChevalleyStringsInputs

public section

namespace CFSG.KC.ChevStr

open CFSG.Blueprint.Chevalley

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by cases a <;> rfl

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem eqB_eq (a b : Bool) : eqB a b = (a == b) := by cases a <;> cases b <;> rfl

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    change andB (allN n f) (f n) = true ↔ _
    rw [andB_eq, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h1 i h
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

theorem lenL_eq (L : List Nat) : lenL L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih => exact congrArg Nat.succ ih

theorem dig_eq (c j : Nat) : dig c j = c / 16 ^ j % 16 := rfl

theorem verL_spec (X : Nat) (L : List Nat) :
    ∀ k₀, verL X L k₀ = true → ∀ k < L.length, lane X (k₀ + k) = L.getD k 0 := by
  induction L with
  | nil => intro _ _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | cons a L ih =>
    intro k₀ h k hk
    change andB (Nat.beq (lane X k₀) a) (verL X L (Nat.succ k₀)) = true at h
    rw [andB_eq, Bool.and_eq_true, Nat.beq_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := ih _ h.2 k (by simpa using hk)
      rw [Nat.succ_add_eq_add_succ] at this
      simpa using this

theorem mod_pow_eq_iff {a b : Nat} :
    ∀ r, a % 16 ^ r = b % 16 ^ r ↔ ∀ j < r, a / 16 ^ j % 16 = b / 16 ^ j % 16
  | 0 => by simp [Nat.mod_one]
  | r + 1 => by
    have hp : 0 < 16 ^ r := by positivity
    have split : ∀ x, x % 16 ^ (r + 1) % 16 ^ r = x % 16 ^ r ∧
        x % 16 ^ (r + 1) / 16 ^ r = x / 16 ^ r % 16 := fun x => by
      rw [Nat.mod_pow_succ]
      refine ⟨by simp [Nat.mod_mod], ?_⟩
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp), Nat.zero_add]
    constructor
    · intro h j hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · have h1 : a % 16 ^ r = b % 16 ^ r := by rw [← (split a).1, ← (split b).1, h]
        exact (mod_pow_eq_iff r).1 h1 j hj
      · rw [← (split a).2, ← (split b).2, h]
    · intro h
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ,
        (mod_pow_eq_iff r).2 fun j hj => h j (Nat.lt_succ_of_lt hj), h r (Nat.lt_succ_self r)]

theorem digit_split {lo e h i : Nat} (hlo : lo < 16 ^ i) (he : e < 16) (j : Nat) :
    (lo + 16 ^ i * (e + 16 * h)) / 16 ^ j % 16 =
      if j < i then lo / 16 ^ j % 16 else if j = i then e else h / 16 ^ (j - i - 1) % 16 := by
  by_cases hji : j < i
  · rw [if_pos hji]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hji
    have hpj : 0 < 16 ^ j := by positivity
    have : 16 ^ (j + m + 1) * (e + 16 * h) = 16 ^ j * (16 * (16 ^ m * (e + 16 * h))) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_one]
      ac_rfl
    rw [this, Nat.add_mul_div_left _ _ hpj, Nat.add_mul_mod_self_left]
  · rw [if_neg hji]
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hji)
    have hpi : 0 < 16 ^ i := by positivity
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hpi,
      Nat.div_eq_of_lt hlo, Nat.zero_add]
    cases l with
    | zero => simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]
    | succ l =>
      rw [if_neg (by omega), Nat.pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt he, Nat.zero_add,
        show i + (l + 1) - i - 1 = l by omega]

theorem digit_replace (c i e j : Nat) (he : e < 16) :
    (c - c / 16 ^ i % 16 * 16 ^ i + e * 16 ^ i) / 16 ^ j % 16 =
      if j = i then e else c / 16 ^ j % 16 := by
  have hpi : 0 < 16 ^ i := by positivity
  have hc : c = c % 16 ^ i + 16 ^ i * (c / 16 ^ i % 16 + 16 * (c / 16 ^ i / 16)) := by
    rw [Nat.mod_add_div (c / 16 ^ i) 16, Nat.mod_add_div]
  have key : ∀ lo d h, c = lo + 16 ^ i * (d + 16 * h) →
      c - d * 16 ^ i + e * 16 ^ i = lo + 16 ^ i * (e + 16 * h) := by
    intro lo d h hc
    subst hc
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_comm d, Nat.mul_comm e]
    omega
  have hlo := Nat.mod_lt c hpi
  have hd := Nat.mod_lt (c / 16 ^ i) (show 0 < 16 by decide)
  have hcj : c / 16 ^ j % 16 = if j < i then c % 16 ^ i / 16 ^ j % 16 else if j = i then
      c / 16 ^ i % 16 else c / 16 ^ i / 16 / 16 ^ (j - i - 1) % 16 := by
    conv_lhs => rw [hc]
    exact digit_split hlo hd j
  rw [key _ _ _ hc, digit_split hlo he, hcj]
  by_cases hji : j < i
  · simp [hji, Nat.ne_of_lt hji]
  · by_cases h : j = i <;> simp [hji, h]

theorem lookup_spec {r P len R T x : Nat} :
    lookup r P len R T x = true ↔ (0 < lane8 T (x % 16 ^ r % P) ∧ lane8 T (x % 16 ^ r % P) ≤ len)
      ∧ lane R (lane8 T (x % 16 ^ r % P) - 1) % 16 ^ r = x % 16 ^ r := by
  change andB (andB (Nat.blt 0 (lane8 T (x % 16 ^ r % P))) (Nat.ble (lane8 T (x % 16 ^ r % P)) len))
    (Nat.beq (lane R (lane8 T (x % 16 ^ r % P) - 1) % 16 ^ r) (x % 16 ^ r)) = true ↔ _
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.beq_eq]

theorem basisLike_spec {r c i e : Nat} (h : basisLike r c i e = true) :
    ∀ j < r, c / 16 ^ j % 16 = if j = i then e else 8 := by
  intro j hj
  have := (allN_iff.1 h) j hj
  rw [Nat.beq_eq, dig_eq] at this
  rw [this]
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl, Nat.beq_refl]
  · have hb : Nat.beq j i = false := Bool.eq_false_iff.2 fun h => hji (Nat.eq_of_beq_eq_true h)
    rw [if_neg hji, hb]

theorem strOK_spec {r P len W R T c s i : Nat} (h : strOK r P len W R T c s i = true) :
    dig s i / 4 + dig s i % 4 ≤ 3 ∧ ∀ n < 2 * W + 1,
      ((W ≤ dig c i + n ∧ dig c i + n < W + 16) ∧
        lookup r P len R T (c - dig c i * 16 ^ i + (dig c i + n - W) * 16 ^ i) = true) ↔
      (W ≤ n + dig s i % 4 ∧ n ≤ W + dig s i / 4) := by
  change andB (Nat.ble (dig s i / 4 + dig s i % 4) 3) (allN (2 * W + 1) fun n => eqB
    (andB (andB (Nat.ble W (dig c i + n)) (Nat.blt (dig c i + n) (W + 16)))
      (lookup r P len R T (c - dig c i * 16 ^ i + (dig c i + n - W) * 16 ^ i)))
    (andB (Nat.ble W (n + dig s i % 4)) (Nat.ble n (W + dig s i / 4)))) = true at h
  rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, allN_iff] at h
  refine ⟨h.1, fun n hn => ?_⟩
  have := Bool.eq_iff_iff.1 (beq_iff_eq.1 ((eqB_eq _ _).symm.trans (h.2 n hn)))
  simpa only [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] using this

theorem top_spec {r P W : Nat} {roots strings : List Nat} (h : top r P W roots strings = true) :
    ∃ R SL T, (∀ k < roots.length, lane R k = roots.getD k 0) ∧
      (∀ k < strings.length, lane SL k = strings.getD k 0) ∧ strings.length = roots.length ∧
      (∀ k < roots.length, lane8 T (key r P (lane R k)) = k + 1) ∧
      mainK r P roots.length W R SL T = true := by
  refine ⟨pack roots, pack strings, hashT r P roots 0, ?_⟩
  change andB (andB (andB (andB (verL (pack roots) roots 0) (verL (pack strings) strings 0))
    (Nat.beq (lenL strings) (lenL roots)))
    (allN (lenL roots) fun k => Nat.beq (lane8 (hashT r P roots 0) (key r P (lane (pack roots) k)))
      (Nat.succ k)))
    (mainK r P (lenL roots) W (pack roots) (pack strings) (hashT r P roots 0)) = true at h
  simp only [andB_eq, Bool.and_eq_true, Nat.beq_eq, lenL_eq, allN_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun k hk => by simpa using verL_spec _ _ 0 h1 k hk,
    fun k hk => by simpa using verL_spec _ _ 0 h2 k hk, h3, h4, h5⟩

variable {τ : Tag} {S : StringData τ} {C : RootCertificate τ}

theorem root_apply (k : Nat) (j : Fin τ.rank) :
    C.root k j = ((C.roots.getD k 0 / 16 ^ (j : Nat) % 16 : Nat) : ℤ) - 8 := rfl

theorem memDec_iff_exists (hb : S.checkBuckets C = true) (hbb : S.checkBucketBounds C = true)
    {v : Fin τ.rank → ℤ} : S.memDec C v = true ↔ ∃ k < C.roots.length, C.root k = v := by
  simp only [StringData.checkBuckets, List.all_eq_true, List.mem_range,
    List.contains_iff_mem] at hb
  simp only [StringData.checkBucketBounds, List.all_eq_true, decide_eq_true_eq] at hbb
  constructor
  · intro h
    simp only [StringData.memDec, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨k, hk, hkv⟩ := h
    refine ⟨k, ?_, RootCertificate.eq_of_ofFn_beq (beq_iff_eq.2 hkv)⟩
    simp only [StringData.bucket] at hk
    split_ifs at hk with hr
    · rw [List.getD_eq_getElem?_getD] at hk
      generalize (height v + S.maxHeight).toNat = idx at hk
      cases hx : S.buckets[idx]? with
      | none => simp [hx] at hk
      | some x =>
        rw [hx] at hk
        exact hbb x (List.mem_of_getElem? hx) k hk
    · simp at hk
  · rintro ⟨k, hk, rfl⟩
    simp only [StringData.memDec, List.any_eq_true, beq_iff_eq]
    exact ⟨k, hb k hk, rfl⟩

theorem exists_root_add_iff {P R T : Nat}
    (hR : ∀ k < C.roots.length, lane R k = C.roots.getD k 0)
    (hT : ∀ k < C.roots.length, lane8 T (key τ.rank P (lane R k)) = k + 1)
    (k : Nat) (i : Fin τ.rank) (n W : Nat) :
    (∃ k' < C.roots.length, C.root k' = C.root k + ((n : ℤ) - W) • Pi.single i 1) ↔
      ((W ≤ dig (C.roots.getD k 0) i + n ∧ dig (C.roots.getD k 0) i + n < W + 16) ∧
        lookup τ.rank P C.roots.length R T (C.roots.getD k 0 - dig (C.roots.getD k 0) i * 16 ^ (i : Nat)
          + (dig (C.roots.getD k 0) i + n - W) * 16 ^ (i : Nat)) = true) := by
  set c := C.roots.getD k 0 with hc
  rw [dig_eq]
  set d := c / 16 ^ (i : Nat) % 16 with hd
  set x := c - d * 16 ^ (i : Nat) + (d + n - W) * 16 ^ (i : Nat) with hx
  have hd16 : d < 16 := Nat.mod_lt _ (by decide)
  have hv : ∀ j : Fin τ.rank, (C.root k + ((n : ℤ) - W) • Pi.single i 1 : Fin τ.rank → ℤ) j =
      ((c / 16 ^ (j : Nat) % 16 : Nat) : ℤ) - 8 + if j = i then (n : ℤ) - W else 0 := by
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one,
      mul_zero, root_apply]
    rfl
  constructor
  · rintro ⟨k', hk', hroot⟩
    have hcoord : ∀ j : Fin τ.rank, ((C.roots.getD k' 0 / 16 ^ (j : Nat) % 16 : Nat) : ℤ) - 8 =
        ((c / 16 ^ (j : Nat) % 16 : Nat) : ℤ) - 8 + if j = i then (n : ℤ) - W else 0 := by
      intro j
      rw [← root_apply, hroot, hv]
    have hi := hcoord i
    rw [if_pos rfl] at hi
    have hlt := Nat.mod_lt (C.roots.getD k' 0 / 16 ^ (i : Nat)) (show 0 < 16 by decide)
    have hrange : W ≤ d + n ∧ d + n < W + 16 := by omega
    refine ⟨hrange, ?_⟩
    have hdig : ∀ j < τ.rank, C.roots.getD k' 0 / 16 ^ j % 16 = x / 16 ^ j % 16 := by
      intro j hj
      rw [hx, digit_replace c i (d + n - W) j (by omega)]
      have := hcoord ⟨j, hj⟩
      by_cases hji : j = (i : Nat)
      · subst hji
        rw [if_pos rfl]
        rw [if_pos rfl] at this
        dsimp only at this
        omega
      · rw [if_neg hji]
        rw [if_neg (fun h => hji (congrArg Fin.val h))] at this
        dsimp only at this
        omega
    have hmod := (mod_pow_eq_iff τ.rank).2 hdig
    have hT' := hT k' hk'
    rw [hR k' hk'] at hT'
    change lane8 T (C.roots.getD k' 0 % 16 ^ τ.rank % P) = k' + 1 at hT'
    rw [hmod] at hT'
    rw [lookup_spec, hT', Nat.add_sub_cancel, hR k' hk', hmod]
    exact ⟨⟨Nat.succ_pos k', hk'⟩, rfl⟩
  · rintro ⟨hrange, hl⟩
    rw [lookup_spec] at hl
    obtain ⟨⟨h0, hlen⟩, heq⟩ := hl
    refine ⟨lane8 T (x % 16 ^ τ.rank % P) - 1, by omega, ?_⟩
    rw [hR _ (by omega)] at heq
    have hdig := (mod_pow_eq_iff τ.rank).1 heq
    funext j
    rw [root_apply, hv, hdig j j.isLt, hx, digit_replace c i (d + n - W) j (by omega)]
    by_cases hji : (j : Nat) = i
    · rw [if_pos hji, if_pos (Fin.ext hji), hji, ← hd]
      push_cast [Nat.cast_sub hrange.1]
      ring
    · rw [if_neg hji, if_neg (fun h => hji (congrArg Fin.val h))]
      ring

theorem checkCoords_of_coordsK (h : coordsK τ.rank S.maxCoord C.roots = true) :
    S.checkCoords C = true := by
  change andB (verL (pack C.roots) C.roots 0) (allN (lenL C.roots) fun k => allN τ.rank fun j =>
    andB (Nat.ble 8 (dig (lane (pack C.roots) k) j + S.maxCoord))
      (Nat.ble (dig (lane (pack C.roots) k) j) (8 + S.maxCoord))) = true at h
  generalize pack C.roots = R at h
  rw [andB_eq, Bool.and_eq_true, lenL_eq, allN_iff] at h
  obtain ⟨h1, h2⟩ := h
  rw [StringData.checkCoords, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [List.all_eq_true]
  intro j _
  have hj := (allN_iff.1 (h2 k hk)) j j.isLt
  have hRk := verL_spec _ _ 0 h1 k hk
  rw [Nat.zero_add] at hRk
  rw [andB_eq, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq, dig_eq, hRk] at hj
  rw [decide_eq_true_eq, root_apply, abs_le]
  omega

theorem checkStrings_of_top (P : Nat) (hb : S.checkBuckets C = true)
    (hbb : S.checkBucketBounds C = true)
    (h : top τ.rank P (2 * S.maxCoord + 1) C.roots S.strings = true) :
    S.checkStrings C = true := by
  obtain ⟨R, SL, T, hR, hSL, hlen, hT, hm⟩ := top_spec h
  rw [StringData.checkStrings, List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  rw [List.all_eq_true]
  intro i _
  have hk' := (allN_iff.1 hm) k hk
  have hki := (allN_iff.1 hk') i i.isLt
  rw [orB_eq, orB_eq, hR k hk, hSL k (hlen ▸ hk)] at hki
  rw [Bool.or_eq_true, Bool.or_eq_true] at hki
  rcases hki with (h9 | h7) | hs
  · have he : C.root k = Pi.single i 1 := funext fun j => by
      rw [root_apply, basisLike_spec h9 j j.isLt, Pi.single_apply]
      by_cases hji : (j : Nat) = i
      · rw [if_pos hji, if_pos (Fin.ext hji)]
        rfl
      · rw [if_neg hji, if_neg (fun h => hji (congrArg Fin.val h))]
        rfl
    simp [he]
  · have he : C.root k = -Pi.single i 1 := funext fun j => by
      rw [root_apply, basisLike_spec h7 j j.isLt, Pi.neg_apply, Pi.single_apply]
      by_cases hji : (j : Nat) = i
      · rw [if_pos hji, if_pos (Fin.ext hji)]
        rfl
      · rw [if_neg hji, if_neg (fun h => hji (congrArg Fin.val h))]
        rfl
    simp [he]
  · obtain ⟨hs1, hs2⟩ := strOK_spec hs
    have hup : S.up k i = dig (S.strings.getD k 0) i / 4 := rfl
    have hdn : S.down k i = dig (S.strings.getD k 0) i % 4 := rfl
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true, decide_eq_true_eq, hup, hdn]
    refine ⟨hs1, ?_⟩
    rw [StringData.window, List.all_map, List.all_eq_true]
    intro n hn
    rw [List.mem_range] at hn
    rw [Function.comp_apply, beq_iff_eq]
    apply Bool.eq_iff_iff.2
    rw [memDec_iff_exists hb hbb, decide_eq_true_eq]
    have hW : ((2 * S.maxCoord + 1 : Nat) : ℤ) = 2 * (S.maxCoord : ℤ) + 1 := by push_cast; ring
    rw [← hW, exists_root_add_iff hR hT k i n (2 * S.maxCoord + 1), hs2 n hn]
    omega

end CFSG.KC.ChevStr

end

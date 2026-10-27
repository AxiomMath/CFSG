module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBasic
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToralDefs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Steinberg


set_option linter.unusedSectionVars false

theorem e8PlaneDN_getD {n : ℕ} (hn : n < 6561) :
    (e8PlaneDN ()).getD n [] = e8PlaneDigits n := by
  unfold e8PlaneDN
  exact toArray_map_range_getD e8PlaneDigits [] hn

theorem cast_dotL_digits (v : Fin Tag.E8.rank → ℤ) (n : ℕ) :
    ((dotL (List.ofFn v) (e8PlaneDigits n) : ℤ) : ZMod 3) =
      triPairing (vec3OfIndex (τ := .E8) n) v := by
  unfold dotL triPairing
  rw [sum_zipWith_ofFn_left, Int.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h := congrFun (vec3_digits3 (τ := .E8) n) x
  simp only [vec3] at h
  rw [Int.cast_mul, e8PlaneDigits, getD_map_natCast, Int.cast_natCast, ← h, mul_comm]

theorem e8PlaneKill_iff {n r : ℕ} (hn : n < 6561) (hr : r < 240) :
    e8PlaneKill (e8PlaneRL ()) ((e8PlaneDN ()).getD n []) r = true ↔
      triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root r) = 0 := by
  unfold e8PlaneKill
  rw [e8PlaneDN_getD hn, e8PlaneRL_getD hr, decide_eq_true_iff, ← cast_dotL_digits]
  constructor
  · intro h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 (by exact_mod_cast Int.dvd_of_emod_eq_zero h)
  · intro h
    exact Int.emod_eq_zero_of_dvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h)

theorem testBit_e8PlaneMaskOf (p : ℕ → Bool) (k n : ℕ) :
    (e8PlaneMaskOf p k).testBit n = (decide (n < k) && p n) := by
  induction k with
  | zero => simp [e8PlaneMaskOf]
  | succ k ih =>
    rw [e8PlaneMaskOf, Nat.testBit_or, ih]
    by_cases hp : p k
    · have h1 : (if p k then 1 <<< k else 0) = 2 ^ k := by simp [hp, Nat.one_shiftLeft]
      rw [h1, Nat.testBit_two_pow]
      by_cases h : n < k
      · simp [h, show k ≠ n by omega, show n < k + 1 by omega]
      · by_cases h' : n = k
        · subst h'
          simp [hp]
        · simp [h, h', show ¬ n < k + 1 by omega, show k ≠ n by omega]
    · have h1 : (if p k then 1 <<< k else 0) = 0 := by simp [hp]
      rw [h1, Nat.zero_testBit]
      by_cases h : n < k
      · simp [h, show n < k + 1 by omega]
      · by_cases h' : n = k
        · subst h'
          simp [hp]
        · simp [h, show ¬ n < k + 1 by omega]

theorem testBit_e8PlaneKM {n r : ℕ} (hn : n < 6561) :
    ((e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n 0).testBit r = true ↔
      r < 240 ∧ triPairing (vec3OfIndex (τ := .E8) n) (e8Certificate.root r) = 0 := by
  unfold e8PlaneKM
  rw [toArray_map_range_getD _ _ hn, testBit_e8PlaneMaskOf]
  by_cases hr : r < 240
  · simp only [hr, decide_true, Bool.true_and, true_and]
    exact e8PlaneKill_iff hn hr
  · simp [hr]

theorem ncard_eq_length_filter (p : (Fin Tag.E8.rank → ℤ) → Prop) (q : ℕ → Bool)
    (hq : ∀ r < 240, q r = true ↔ p (e8Certificate.root r)) :
    {α | IsRoot Tag.E8 α ∧ p α}.ncard = ((List.range 240).filter q).length := by
  have hset : {α | IsRoot Tag.E8 α ∧ p α} =
      ↑((((List.range 240).filter q).map e8Certificate.root).toFinset) := by
    ext α
    simp only [Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map, List.mem_filter,
      List.mem_range]
    constructor
    · rintro ⟨hα, hp⟩
      obtain ⟨r, hr, rfl⟩ := e8Certificate_exists_root hα
      exact ⟨r, ⟨hr, (hq r hr).2 hp⟩, rfl⟩
    · rintro ⟨r, ⟨hr, hqr⟩, rfl⟩
      exact ⟨e8Certificate_isRoot hr, (hq r hr).1 hqr⟩
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
  exact e8Certificate_root_inj (List.mem_range.1 (List.mem_filter.1 ha).1)
    (List.mem_range.1 (List.mem_filter.1 hb).1) hab

theorem e8PlaneCnt_getD {n : ℕ} (hn : n < 6561) :
    (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())).getD n 0 =
      {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧ triPairing (vec3OfIndex n) α = 0}.ncard := by
  unfold e8PlaneCnt
  rw [toArray_map_range_getD _ _ hn]
  exact (ncard_eq_length_filter (fun α => triPairing (vec3OfIndex (τ := .E8) n) α = 0) _
    (fun r hr => e8PlaneKill_iff hn hr)).symm

theorem foldr_range_add {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) (init : M) :
    (List.range m).foldr (fun j acc => f j + acc) init = ∑ j ∈ Finset.range m, f j + init := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, ih,
      Finset.sum_range_succ, add_assoc]

theorem e8PlaneCombo_eq_sum (n₀ n₁ c₀ c₁ : ℕ) :
    e8PlaneCombo n₀ n₁ c₀ c₁ = ∑ j ∈ Finset.range 8,
      (c₀ * (n₀ / 3 ^ j % 3) + c₁ * (n₁ / 3 ^ j % 3)) % 3 * 3 ^ j := by
  unfold e8PlaneCombo
  exact (foldr_range_add (fun j => (c₀ * (n₀ / 3 ^ j % 3) + c₁ * (n₁ / 3 ^ j % 3)) % 3 * 3 ^ j)
    8 0).trans (add_zero _)

theorem sum_digits_lt (e : ℕ → ℕ) (he : ∀ j, e j < 3) (m : ℕ) :
    ∑ j ∈ Finset.range m, e j * 3 ^ j < 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h2 : e m * 3 ^ m ≤ 2 * 3 ^ m := Nat.mul_le_mul_right _ (by have := he m; omega)
    omega

theorem sum_digits_div_mod (e : ℕ → ℕ) (he : ∀ j, e j < 3) (m k : ℕ) (hk : k < m) :
    (∑ j ∈ Finset.range m, e j * 3 ^ j) / 3 ^ k % 3 = e k := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hA := sum_digits_lt e he m
    by_cases hkm : k < m
    · obtain ⟨d, hd⟩ : ∃ d, m = k + d + 1 := ⟨m - k - 1, by omega⟩
      have h1 : e m * 3 ^ m = 3 ^ k * (3 * (3 ^ d * e m)) := by
        rw [hd, pow_succ, pow_add]
        ring
      rw [h1, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih hkm
    · have hkm' : k = m := by omega
      subst hkm'
      rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hA, zero_add]
      exact Nat.mod_eq_of_lt (he k)

theorem e8PlaneCombo_lt (n₀ n₁ c₀ c₁ : ℕ) : e8PlaneCombo n₀ n₁ c₀ c₁ < 6561 := by
  rw [e8PlaneCombo_eq_sum]
  have := sum_digits_lt (fun j => (c₀ * (n₀ / 3 ^ j % 3) + c₁ * (n₁ / 3 ^ j % 3)) % 3)
    (fun j => Nat.mod_lt _ (by norm_num)) 8
  simpa using this

theorem vec3OfIndex_e8PlaneCombo (n₀ n₁ c₀ c₁ : ℕ) :
    vec3OfIndex (τ := .E8) (e8PlaneCombo n₀ n₁ c₀ c₁) =
      (c₀ : ZMod 3) • vec3OfIndex n₀ + (c₁ : ZMod 3) • vec3OfIndex n₁ := by
  funext j
  have hj : (j : ℕ) < 8 := j.2
  have key := sum_digits_div_mod
    (fun j => (c₀ * (n₀ / 3 ^ j % 3) + c₁ * (n₁ / 3 ^ j % 3)) % 3)
    (fun j => Nat.mod_lt _ (by norm_num)) 8 j hj
  simp only [vec3OfIndex, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e8PlaneCombo_eq_sum, key, ZMod.natCast_mod]
  push_cast
  ring

theorem e8PlaneK78_spec {n₀ n₁ : ℕ}
    (h : e8PlaneK78 (e8PlaneCnt (e8PlaneRL ()) (e8PlaneDN ())) n₀ n₁ = true)
    (c : Fin 2 → ZMod 3) (hc : c ≠ 0) :
    {α : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 α ∧
      triPairing (c 0 • vec3OfIndex n₀ + c 1 • vec3OfIndex n₁) α = 0}.ncard = 78 := by
  have hne : (c 0).val ≠ 0 ∨ (c 1).val ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not, ZMod.val_eq_zero, ZMod.val_eq_zero] at hcon
    exact hc (funext fun i => by fin_cases i <;> simp [hcon.1, hcon.2])
  have hlt0 : (c 0).val < 3 := ZMod.val_lt _
  have hlt1 : (c 1).val < 3 := ZMod.val_lt _
  unfold e8PlaneK78 at h
  rw [List.all_eq_true] at h
  have hk := h ((c 0).val + 3 * (c 1).val - 1) (List.mem_range.2 (by omega))
  have e1 : ((c 0).val + 3 * (c 1).val - 1 + 1) % 3 = (c 0).val := by omega
  have e2 : ((c 0).val + 3 * (c 1).val - 1 + 1) / 3 = (c 1).val := by omega
  rw [e1, e2, beq_iff_eq, e8PlaneCnt_getD (e8PlaneCombo_lt _ _ _ _),
    vec3OfIndex_e8PlaneCombo, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hk
  exact hk

theorem e8PlaneFix_of_mem {n : ℕ} (hn : n < 6561) {rv : List (List ℤ)} {w : WeylGroup Tag.E8}
    (hrv : ∀ j : Fin Tag.E8.rank,
      rv.getD j [] = List.ofFn (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)))
    (hw : ∀ x, triPairing (vec3OfIndex (τ := .E8) n) (w • x) =
      triPairing (vec3OfIndex n) x) :
    e8PlaneFix rv ((e8PlaneDN ()).getD n []) = true := by
  unfold e8PlaneFix
  rw [List.all_eq_true]
  intro j hj
  have hj8 : j < Tag.E8.rank := List.mem_range.1 hj
  have hrj : rv.getD j [] = List.ofFn (w • (Pi.single (⟨j, hj8⟩ : Fin Tag.E8.rank) 1 :
      Fin Tag.E8.rank → ℤ)) := hrv ⟨j, hj8⟩
  rw [decide_eq_true_iff, e8PlaneDN_getD hn, hrj]
  apply Int.emod_eq_zero_of_dvd
  have h1 := cast_dotL_digits (w • (Pi.single (⟨j, hj8⟩ : Fin Tag.E8.rank) 1 :
    Fin Tag.E8.rank → ℤ)) n
  rw [hw] at h1
  have h2 := triPairing_zsmul_single (vec3OfIndex (τ := .E8) n) 1 ⟨j, hj8⟩
  rw [one_smul, Int.cast_one, mul_one] at h2
  have h3 : (((e8PlaneDigits n).getD j 0 : ℤ) : ZMod 3) = vec3OfIndex (τ := .E8) n ⟨j, hj8⟩ := by
    have h := congrFun (vec3_digits3 (τ := .E8) n) ⟨j, hj8⟩
    simp only [vec3] at h
    rw [e8PlaneDigits, getD_map_natCast, Int.cast_natCast]
    exact h
  have h4 : (((dotL (List.ofFn (w • (Pi.single (⟨j, hj8⟩ : Fin Tag.E8.rank) 1 :
      Fin Tag.E8.rank → ℤ))) (e8PlaneDigits n) - (e8PlaneDigits n).getD j 0 : ℤ)) : ZMod 3) =
      0 := by
    rw [Int.cast_sub, h1, h2, h3, sub_self]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 h4

@[expose] def sigSet (σ : ℕ) : Set (Fin Tag.E8.rank → ℤ) :=
  {α | ∃ k ∈ e8PlaneSig σ, e8Certificate.root k = α}

theorem mem_e8PlaneSig {σ k : ℕ} : k ∈ e8PlaneSig σ ↔ k < 240 ∧ σ.testBit k = true := by
  simp [e8PlaneSig, List.mem_filter, List.mem_range]

theorem mem_sigSet {σ : ℕ} {α : Fin Tag.E8.rank → ℤ} :
    α ∈ sigSet σ ↔ ∃ k < 240, σ.testBit k = true ∧ e8Certificate.root k = α := by
  simp only [sigSet, Set.mem_setOf_eq, mem_e8PlaneSig]
  constructor
  · rintro ⟨k, ⟨hk, hb⟩, rfl⟩
    exact ⟨k, hk, hb, rfl⟩
  · rintro ⟨k, hk, hb, rfl⟩
    exact ⟨k, ⟨hk, hb⟩, rfl⟩

theorem sigSet_KM_and {n₀ n₁ : ℕ} (h0 : n₀ < 6561) (h1 : n₁ < 6561) :
    sigSet ((e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n₀ 0 &&&
        (e8PlaneKM (e8PlaneRL ()) (e8PlaneDN ())).getD n₁ 0) =
      {α | IsRoot Tag.E8 α ∧ triPairing (vec3OfIndex (τ := .E8) n₀) α = 0 ∧
        triPairing (vec3OfIndex (τ := .E8) n₁) α = 0} := by
  ext α
  rw [mem_sigSet]
  simp only [Nat.testBit_and, Bool.and_eq_true, testBit_e8PlaneKM h0, testBit_e8PlaneKM h1,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, ⟨⟨-, hp0⟩, ⟨-, hp1⟩⟩, rfl⟩
    exact ⟨e8Certificate_isRoot hk, hp0, hp1⟩
  · rintro ⟨hα, hp0, hp1⟩
    obtain ⟨k, hk, rfl⟩ := e8Certificate_exists_root hα
    exact ⟨k, hk, ⟨⟨hk, hp0⟩, ⟨hk, hp1⟩⟩, rfl⟩

theorem ncard_sigSet (σ : ℕ) : (sigSet σ).ncard = (e8PlaneSig σ).length := by
  have hset : sigSet σ = ↑(((e8PlaneSig σ).map e8Certificate.root).toFinset) := by
    ext α
    simp only [sigSet, Set.mem_setOf_eq, Finset.mem_coe, List.mem_toFinset, List.mem_map]
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup, List.length_map]
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) (List.nodup_range.filter _)
  exact e8Certificate_root_inj (mem_e8PlaneSig.1 ha).1 (mem_e8PlaneSig.1 hb).1 hab

@[expose] def PermOf8 (P : Array ℕ) (w : WeylGroup Tag.E8) : Prop :=
  ∀ k, k < 240 → P.getD k 0 < 240 ∧ e8Certificate.root (P.getD k 0) = w • e8Certificate.root k

@[expose] def GramOf8 (G : Array ℤ) : Prop :=
  ∀ a b, a < 240 → b < 240 →
    G.getD (240 * a + b) 0 = iform (e8Certificate.root a) (e8Certificate.root b)

theorem gramOf8_e8PlaneGram : GramOf8 (e8PlaneGram (e8PlaneRL ()) (e8PlaneRA ())) :=
  fun _ _ ha hb => e8PlaneGram_getD ha hb

theorem e8PlaneD3_sound {P : Array ℕ} {G : Array ℤ} {σ : ℕ} {w : WeylGroup Tag.E8}
    (hP : PermOf8 P w) (hG : GramOf8 G) (h : e8PlaneD3 P G σ = true) :
    (sigSet σ).ncard = 24 ∧ (∀ γ ∈ sigSet σ, w • γ = γ ∨ iform γ (w • γ) = 0) ∧
      ∃ d ∈ sigSet σ, iform d (w • d) = 0 ∧ iform d (w ^ 2 • d) = 0 ∧
        iform (w • d) (w ^ 2 • d) = 0 := by
  unfold e8PlaneD3 at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
    Bool.or_eq_true] at h
  obtain ⟨⟨hlen, hall⟩, d, hd, ⟨h01, h02⟩, h12⟩ := h
  refine ⟨by rw [ncard_sigSet]; exact hlen, ?_, ?_⟩
  · rintro γ ⟨k, hk, rfl⟩
    have hk240 := (mem_e8PlaneSig.1 hk).1
    obtain ⟨hPk, hroot⟩ := hP k hk240
    rcases hall k hk with h1 | h1
    · left
      rw [← hroot, h1]
    · right
      rw [← hroot, ← hG k _ hk240 hPk]
      exact h1
  · have hd240 := (mem_e8PlaneSig.1 hd).1
    obtain ⟨hd1, hroot1⟩ := hP d hd240
    obtain ⟨hd2, hroot2⟩ := hP _ hd1
    have hw2 : w ^ 2 • e8Certificate.root d = e8Certificate.root (P.getD (P.getD d 0) 0) := by
      rw [hroot2, hroot1, pow_two, mul_smul]
    refine ⟨e8Certificate.root d, ⟨d, hd, rfl⟩, ?_, ?_, ?_⟩
    · rw [← hroot1, ← hG _ _ hd240 hd1]
      exact h01
    · rw [hw2, ← hG _ _ hd240 hd2]
      exact h02
    · rw [← hroot1, hw2, ← hG _ _ hd1 hd2]
      exact h12

theorem getD_ofFn_eq {n : ℕ} (f : Fin n → ℤ) (j : Fin n) : (List.ofFn f).getD j 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem e8PlaneTri_sound {P : Array ℕ} {w : WeylGroup Tag.E8} (hP : PermOf8 P w)
    (h : e8PlaneTri (e8PlaneRL ()) P = true) : E8D4Triangles w := by
  unfold e8PlaneTri at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨hfix, hsum⟩ := h
  refine ⟨fun α hα hwα => ?_, ?_⟩
  · obtain ⟨k, hk, rfl⟩ := e8Certificate_exists_root hα
    obtain ⟨hPk, hroot⟩ := hP k hk
    apply hfix k hk
    rw [e8PlaneRL_getD hPk, e8PlaneRL_getD hk, hroot, hwα]
  · have hs := foldr_range_add (fun j => ((e8PlaneRL ()).getD (P.getD j 0) []).getD j 0) 8 0
    rw [hsum, add_zero] at hs
    have hs' : ∑ j ∈ Finset.range Tag.E8.rank,
        ((e8PlaneRL ()).getD (P.getD j 0) []).getD j 0 = -4 := hs.symm
    rw [← hs', Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj8 : (j : ℕ) < 8 := j.2
    obtain ⟨hPj, hroot⟩ := hP j (by omega)
    rw [e8PlaneRL_getD hPj, getD_ofFn_eq, hroot, e8Certificate_root_single]

theorem existsUnique_of_sum_ite (p : Fin 3 → Prop) [DecidablePred p]
    (h : (if p 0 then 1 else 0) + (if p 1 then 1 else 0) + (if p 2 then 1 else 0) = (1 : ℕ)) :
    ∃! j, p j := by
  have h' : (Finset.univ.filter p).card = 1 := by
    rw [Finset.card_filter, Fin.sum_univ_three]
    exact h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h'
  refine ⟨a, ?_, fun y hy => ?_⟩
  · have : a ∈ Finset.univ.filter p := by
      rw [ha]
      exact Finset.mem_singleton_self a
    exact (Finset.mem_filter.1 this).2
  · have : y ∈ Finset.univ.filter p := Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩
    rw [ha] at this
    exact Finset.mem_singleton.1 this

theorem blk_iff_of_count (a0 a1 a2 : ℤ)
    (hc : (if ¬a0 = 0 then 1 else 0) + (if ¬a1 = 0 then 1 else 0) +
      (if ¬a2 = 0 then 1 else 0) = (1 : ℕ)) :
    ((if ¬a0 = 0 then 0 else if ¬a1 = 0 then 1 else 2 : ℕ) = 0 ↔ ¬a0 = 0) ∧
    ((if ¬a0 = 0 then 0 else if ¬a1 = 0 then 1 else 2 : ℕ) = 1 ↔ ¬a1 = 0) ∧
    ((if ¬a0 = 0 then 0 else if ¬a1 = 0 then 1 else 2 : ℕ) = 2 ↔ ¬a2 = 0) := by
  by_cases h0 : a0 = 0 <;> by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;>
    simp [h0, h1, h2] at hc ⊢

theorem e8PlaneD2_sound {P : Array ℕ} {G : Array ℤ} {σ : ℕ} {w : WeylGroup Tag.E8}
    (hP : PermOf8 P w) (hG : GramOf8 G) (h : e8PlaneD2 P G σ = true) :
    ∃ γ : Fin 3 → Fin Tag.E8.rank → ℤ, (∀ j, γ j ∈ sigSet σ) ∧
      (∀ α ∈ sigSet σ, ∃! j, iform α (γ j) ≠ 0) ∧
      (∀ α ∈ sigSet σ, ∀ δ ∈ sigSet σ, ∀ j, iform α (γ j) ≠ 0 →
        (iform δ (γ j) ≠ 0 ↔ iform α δ ≠ 0)) ∧
      (∀ j : Fin 3, iform (w • γ j) (γ (j + 1)) ≠ 0) := by
  unfold e8PlaneD2 at h
  dsimp only at h
  generalize hS : e8PlaneSig σ = S at h
  generalize hg0 : S.headD 0 = g₀ at h
  generalize hg1 : P.getD g₀ 0 = g₁ at h
  generalize hg2 : P.getD g₁ 0 = g₂ at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hT0, hT1⟩, hT2⟩, hcount⟩, hpair⟩, hlast⟩ := h
  simp only [List.all_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hcount hpair hlast
  have hS' : ∀ k, k ∈ S ↔ k < 240 ∧ σ.testBit k = true := fun k => by
    rw [← hS]
    exact mem_e8PlaneSig
  have hg0lt : g₀ < 240 := by
    rw [← hg0]
    rcases hSnil : S with _ | ⟨a, l⟩
    · simp
    · have : a ∈ S := by rw [hSnil]; simp
      simpa using ((hS' a).1 this).1
  have hg0S : g₀ ∈ S := (hS' g₀).2 ⟨hg0lt, hT0⟩
  obtain ⟨hg1lt, hr1⟩ := hP g₀ hg0lt
  rw [hg1] at hg1lt hr1
  have hg1S : g₁ ∈ S := (hS' g₁).2 ⟨hg1lt, hT1⟩
  obtain ⟨hg2lt, hr2⟩ := hP g₁ hg1lt
  rw [hg2] at hg2lt hr2
  have hg2S : g₂ ∈ S := (hS' g₂).2 ⟨hg2lt, hT2⟩
  have hlast' : iform (e8Certificate.root (P.getD g₂ 0)) (e8Certificate.root g₀) ≠ 0 := by
    rw [← hG _ _ (hP g₂ hg2lt).1 hg0lt]
    exact hlast
  obtain ⟨gi, hgi0, hgi1, hgi2⟩ : ∃ gi : Fin 3 → ℕ, gi 0 = g₀ ∧ gi 1 = g₁ ∧ gi 2 = g₂ :=
    ⟨![g₀, g₁, g₂], rfl, rfl, rfl⟩
  have hgi_lt : ∀ j, gi j < 240 := fun j => by
    fin_cases j
    · exact hgi0 ▸ hg0lt
    · exact hgi1 ▸ hg1lt
    · exact hgi2 ▸ hg2lt
  have hgi_S : ∀ j, gi j ∈ S := fun j => by
    fin_cases j
    · exact hgi0 ▸ hg0S
    · exact hgi1 ▸ hg1S
    · exact hgi2 ▸ hg2S
  obtain ⟨blkF, hblkF⟩ : ∃ blkF : ℕ → ℕ, ∀ x, blkF x =
      (if ¬G.getD (240 * x + g₀) 0 = 0 then 0
        else if ¬G.getD (240 * x + g₁) 0 = 0 then 1 else 2) := ⟨_, fun _ => rfl⟩
  have hblk : ∀ x ∈ S, ∀ j : Fin 3, blkF x = (j : ℕ) ↔ ¬G.getD (240 * x + gi j) 0 = 0 := by
    intro x hx j
    obtain ⟨c0, c1, c2⟩ := blk_iff_of_count _ _ _ (hcount x hx)
    rw [hblkF]
    fin_cases j
    · simpa [hgi0] using c0
    · simpa [hgi1] using c1
    · simpa [hgi2] using c2
  have hpair' : ∀ x ∈ S, ∀ y ∈ S, (¬G.getD (240 * x + y) 0 = 0 ↔ blkF x = blkF y) := by
    intro x hx y hy
    have h1 := hpair x hx y hy
    simp only [Bool.and_eq_true] at h1
    have h4 := beq_iff_eq.1 h1.1.1
    rw [hblkF x, hblkF y]
    constructor
    · intro hne
      have h5 : (G.getD (240 * x + y) 0 != 0) = true := bne_iff_ne.2 hne
      rw [h4] at h5
      exact beq_iff_eq.1 h5
    · intro hb
      have h5 : ((if ¬G.getD (240 * x + g₀) 0 = 0 then 0
          else if ¬G.getD (240 * x + g₁) 0 = 0 then 1 else 2) ==
          (if ¬G.getD (240 * y + g₀) 0 = 0 then 0
          else if ¬G.getD (240 * y + g₁) 0 = 0 then 1 else 2)) = true := beq_iff_eq.2 hb
      rw [← h4] at h5
      exact bne_iff_ne.1 h5
  have hmem : ∀ α ∈ sigSet σ, ∃ a ∈ S, e8Certificate.root a = α := by
    rintro α ⟨a, ha, rfl⟩
    exact ⟨a, by rw [← hS]; exact ha, rfl⟩
  have hunique : ∀ a ∈ S, ∃! j : Fin 3, ¬G.getD (240 * a + gi j) 0 = 0 := by
    intro a ha
    have := hcount a ha
    rw [← hgi0, ← hgi1, ← hgi2] at this
    exact existsUnique_of_sum_ite (fun j => ¬G.getD (240 * a + gi j) 0 = 0) this
  refine ⟨fun j => e8Certificate.root (gi j), fun j => ⟨gi j, by rw [hS]; exact hgi_S j, rfl⟩,
    ?_, ?_, ?_⟩
  · intro α hα
    obtain ⟨a, ha, rfl⟩ := hmem α hα
    have ha240 := ((hS' a).1 ha).1
    refine (existsUnique_congr fun j => ?_).1 (hunique a ha)
    rw [hG a (gi j) ha240 (hgi_lt j)]
  · intro α hα δ hδ j hj
    obtain ⟨a, ha, rfl⟩ := hmem α hα
    obtain ⟨b, hb, rfl⟩ := hmem δ hδ
    have ha240 := ((hS' a).1 ha).1
    have hb240 := ((hS' b).1 hb).1
    have hja : blkF a = (j : ℕ) := by
      rw [hblk a ha j, hG a (gi j) ha240 (hgi_lt j)]
      exact hj
    rw [← hG b (gi j) hb240 (hgi_lt j), ← hG a b ha240 hb240]
    simp only [ne_eq]
    rw [← hblk b hb j, hpair' a ha b hb, hja]
    exact eq_comm
  · intro j
    have hroot : ∀ k, k < 240 → e8Certificate.root k ≠ 0 := fun k hk =>
      (e8Certificate_isRoot hk).ne_zero
    fin_cases j
    · show iform (w • e8Certificate.root (gi 0)) (e8Certificate.root (gi 1)) ≠ 0
      rw [hgi0, hgi1, ← hr1]
      exact (iform_self_pos (hroot g₁ hg1lt)).ne'
    · show iform (w • e8Certificate.root (gi 1)) (e8Certificate.root (gi 2)) ≠ 0
      rw [hgi1, hgi2, ← hr2]
      exact (iform_self_pos (hroot g₂ hg2lt)).ne'
    · show iform (w • e8Certificate.root (gi 2)) (e8Certificate.root (gi 0)) ≠ 0
      rw [hgi2, hgi0, ← (hP g₂ hg2lt).2]
      exact hlast'

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8NonToral.E8Plane

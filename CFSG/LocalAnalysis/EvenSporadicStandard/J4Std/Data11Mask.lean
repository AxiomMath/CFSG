module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Data11Native
public import CFSG.Sporadic.J4.QTElem

public section

namespace CFSG.EvenSporadicStandard.J4Std.Data11

open CFSG.Sporadic.J4.QT
open CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs (duadMasks)

structure MaskData : Prop where
  word : ∀ j < 11, pWord.foldr act (2 ^ j) = pRow j
  row_lt : ∀ j < 11, pRow j < 2 ^ 11
  ne : pMap 2 ≠ 2
  fix_u0 : pMap u0Mask = u0Mask
  fix : ∀ c < 2 ^ 11, pMap c = c → c = 0 ∨ c = u0Mask
  nodup : ((List.range (2 ^ 11)).map (evAt 1)).Nodup
  comm : ∀ f < 2 ^ 11, ∀ k < 11, evAt (evAt 1 f) f = pPow k 1 → ∃ m < 11, evAt 1 f = pPow m 1
  cent : ∀ f < 2 ^ 11, (∀ g < 2 ^ 11, evAt 1 g ∈ duadMasks → evAt (evAt 1 f) g ∈ duadMasks) →
    ∃ m < 11, evAt 1 f = pPow m 1

theorem MaskFacts.toData (h : MaskFacts) : MaskData := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem maskData_of_chk (h : chkMask = true) : MaskData :=
  (of_decide_eq_true h : MaskFacts).toData

theorem rowsXor_lt {r : ℕ → ℕ} {n : ℕ} {m : ℕ} (h : ∀ j < m, r j < 2 ^ n) (c : ℕ) :
    rowsXor r m c < 2 ^ n := by
  induction m with
  | zero => rw [rowsXor_zero]; exact Nat.two_pow_pos n
  | succ m ih =>
    rw [rowsXor_succ]
    refine Nat.xor_lt_two_pow (ih fun j hj => h j (by omega)) ?_
    split_ifs
    · exact h m (by omega)
    · exact Nat.two_pow_pos n

section Masks

variable (hm : MaskData)
include hm

theorem pMap_lt (c : ℕ) : pMap c < 2 ^ 11 := rowsXor_lt (fun j hj => hm.row_lt j hj) c

theorem pPow_lt (k : ℕ) {c : ℕ} (hc : c < 2 ^ 11) : pPow k c < 2 ^ 11 := by
  cases k with
  | zero => exact hc
  | succ k => exact pMap_lt hm _

theorem evAt_lt {y : ℕ} (hy : y < 2 ^ 11) (f : ℕ) : evAt y f < 2 ^ 11 :=
  rowsXor_lt (fun i _ => pPow_lt hm i hy) f

theorem exists_evAt {c : ℕ} (hc : c < 2 ^ 11) : ∃ f < 2 ^ 11, evAt 1 f = c := by
  set l := (List.range (2 ^ 11)).map (evAt 1) with hl
  have hlt : ∀ x ∈ l, x < 2 ^ 11 := by
    intro x hx
    obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
    exact evAt_lt hm (by norm_num) f
  have hsub : l.toFinset ⊆ Finset.range (2 ^ 11) := fun x hx =>
    Finset.mem_range.2 (hlt x (List.mem_toFinset.1 hx))
  have hcard : l.toFinset.card = (Finset.range (2 ^ 11)).card := by
    rw [List.toFinset_card_of_nodup hm.nodup, List.length_map, List.length_range,
      Finset.card_range]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hmem : c ∈ l.toFinset := by rw [heq]; exact Finset.mem_range.2 hc
  obtain ⟨f, hf, hfc⟩ := List.mem_map.1 (List.mem_toFinset.1 hmem)
  exact ⟨f, List.mem_range.1 hf, hfc⟩

end Masks

section Conj

variable {G : Type*} [Group G] {E : ℕ → G}

theorem conj_rowsXor (hE0 : E 0 = 1) (hE : ∀ a b, E (a ^^^ b) = E a * E b) (s : G) {r r' : ℕ → ℕ}
    {m : ℕ} (h : ∀ j < m, s * E (r j) * s⁻¹ = E (r' j)) (f : ℕ) :
    s * E (rowsXor r m f) * s⁻¹ = E (rowsXor r' m f) := by
  induction m with
  | zero => simp [rowsXor_zero, hE0]
  | succ m ih =>
    rw [rowsXor_succ, rowsXor_succ, hE, hE]
    have e : s * (E (rowsXor r m f) * E (if f.testBit m = true then r m else 0)) * s⁻¹ =
        (s * E (rowsXor r m f) * s⁻¹) * (s * E (if f.testBit m = true then r m else 0) * s⁻¹) := by
      group
    rw [e, ih fun j hj => h j (by omega)]
    congr 1
    split_ifs
    · exact h m (by omega)
    · simp [hE0]

structure MaskSetup (E : ℕ → G) (p : G) : Prop where
  zero : E 0 = 1
  xor : ∀ a b, E (a ^^^ b) = E a * E b
  inj : ∀ a < 2 ^ 11, ∀ b < 2 ^ 11, E a = E b → a = b
  conj : ∀ c, p * E c * p⁻¹ = E (pMap c)
  pow_eleven : p ^ 11 = 1

theorem MaskSetup.map {J : Type*} [Group J] {E' : ℕ → J} {p' : J} (h : MaskSetup E' p')
    (ι : J →* G) (hι : Function.Injective ι) : MaskSetup (fun c => ι (E' c)) (ι p') where
  zero := by simp [h.zero]
  xor := fun a b => by simp [h.xor]
  inj := fun a ha b hb e => h.inj a ha b hb (hι e)
  conj := fun c => by rw [← map_inv, ← map_mul, ← map_mul, h.conj]
  pow_eleven := by rw [← map_pow, h.pow_eleven, map_one]

variable {p : G} (hs : MaskSetup E p)

include hs

theorem conj_pPow (k c : ℕ) : p ^ k * E c * (p ^ k)⁻¹ = E (pPow k c) := by
  induction k with
  | zero => simp [pPow]
  | succ k ih =>
    rw [pPow, ← hs.conj, ← ih, pow_succ']
    group

theorem conj_pPow_mod (k c : ℕ) : E (pPow k c) = E (pPow (k % 11) c) := by
  rw [← conj_pPow hs, ← conj_pPow hs, pow_eq_pow_mod k hs.pow_eleven]

theorem conj_evAt {s : G} (hsp : s * p = p * s) {y : ℕ} (hy : s * E 1 * s⁻¹ = E y) (f : ℕ) :
    s * E (evAt 1 f) * s⁻¹ = E (evAt y f) := by
  refine conj_rowsXor hs.zero hs.xor s (fun i _ => ?_) f
  have hc : Commute s (p ^ i) := (show Commute s p from hsp).pow_right i
  have hcc : (p ^ i)⁻¹ * s⁻¹ = s⁻¹ * (p ^ i)⁻¹ := (hc.inv_inv).symm.eq
  rw [← conj_pPow hs, ← conj_pPow hs, ← hy]
  calc s * (p ^ i * E 1 * (p ^ i)⁻¹) * s⁻¹
      = (s * p ^ i) * E 1 * ((p ^ i)⁻¹ * s⁻¹) := by group
    _ = (p ^ i * s) * E 1 * (s⁻¹ * (p ^ i)⁻¹) := by rw [hc.eq, hcc]
    _ = p ^ i * (s * E 1 * s⁻¹) * (p ^ i)⁻¹ := by group

theorem conj_evAt_pow (m f : ℕ) :
    p ^ m * E (evAt 1 f) * (p ^ m)⁻¹ = E (evAt (pPow m 1) f) :=
  conj_evAt hs ((Commute.refl p).pow_left m).eq (conj_pPow hs m 1) f

theorem conj_eq_of_pPow (hm : MaskData) {s : G} (hsp : s * p = p * s) {m : ℕ}
    (hy : s * E 1 * s⁻¹ = E (pPow m 1)) {c : ℕ} (hc : c < 2 ^ 11) :
    s * E c * s⁻¹ = p ^ m * E c * (p ^ m)⁻¹ := by
  obtain ⟨f, -, rfl⟩ := exists_evAt hm hc
  rw [conj_evAt hs hsp hy f, conj_evAt_pow hs m f]

variable (hm : MaskData)
include hm

theorem conj_comm_pow {s : G} (hsp : s * p = p * s) {y : ℕ} (hy : s * E 1 * s⁻¹ = E y)
    (hy_lt : y < 2 ^ 11) {k : ℕ} (hk : s * (s * E 1 * s⁻¹) * s⁻¹ = p ^ k * E 1 * (p ^ k)⁻¹) :
    ∃ m < 11, s * E 1 * s⁻¹ = E (pPow m 1) := by
  obtain ⟨f, hf, hfy⟩ := exists_evAt hm hy_lt
  have h1 : s * E y * s⁻¹ = E (evAt y f) := by
    have := conj_evAt hs hsp hy f
    rwa [hfy] at this
  rw [hy, h1, conj_pPow hs] at hk
  have h2 : evAt y f = pPow k 1 :=
    hs.inj _ (evAt_lt hm hy_lt f) _ (pPow_lt hm k (by norm_num)) hk
  have h3 : evAt (evAt 1 f) f = pPow (k % 11) 1 := by
    rw [hfy, h2]
    exact hs.inj _ (pPow_lt hm k (by norm_num)) _ (pPow_lt hm _ (by norm_num))
      (conj_pPow_mod hs k 1)
  obtain ⟨m, hm11, hmy⟩ := hm.comm f hf (k % 11) (Nat.mod_lt _ (by norm_num)) h3
  exact ⟨m, hm11, by rw [hy, ← hfy, hmy]⟩

theorem conj_cent_pow {s : G} (hsp : s * p = p * s) {y : ℕ} (hy : s * E 1 * s⁻¹ = E y)
    (hy_lt : y < 2 ^ 11)
    (hD : ∀ d ∈ duadMasks, d < 2 ^ 11 → ∃ d' ∈ duadMasks, d' < 2 ^ 11 ∧ s * E d * s⁻¹ = E d') :
    ∃ m < 11, s * E 1 * s⁻¹ = E (pPow m 1) := by
  obtain ⟨f, hf, hfy⟩ := exists_evAt hm hy_lt
  have hD' : ∀ g < 2 ^ 11, evAt 1 g ∈ duadMasks → evAt y g ∈ duadMasks := by
    intro g hg hgD
    obtain ⟨d', hd', hd'lt, hdd⟩ := hD _ hgD (evAt_lt hm (by norm_num) g)
    rw [conj_evAt hs hsp hy g] at hdd
    rwa [hs.inj _ (evAt_lt hm hy_lt g) _ hd'lt hdd]
  obtain ⟨m, hm11, hmy⟩ := hm.cent f hf (by rwa [hfy])
  exact ⟨m, hm11, by rw [hy, ← hfy, hmy]⟩

end Conj

end CFSG.EvenSporadicStandard.J4Std.Data11

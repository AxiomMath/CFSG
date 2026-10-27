module

public import CFSG.Certificates.Kernel.Co2HeavyK.Sound
public import CFSG.Certificates.Kernel.Co2InvS.Enum
public import CFSG.Sporadic.Co2Heavy
public import Certificates.Data.CFSGNative.Co2Heavy.Core

public section

namespace CFSG.KC.Co2HeavyK

open CFSG.KC.Co2InvS CFSG.KC.Co1F2 CFSG.Sporadic.Co2Inv CFSG.Sporadic.Co2Heavy
  CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Blueprint
  CFSG.QuasithinUnique.Lin2.RankCert

set_option linter.unusedSectionVars false


section Entries

variable {CF G Y FW : ℕ → ℕ} (hR : Recs CF G Y FW sOrder)
include hR

theorem hRow_eq_Lf {k : ℕ} (hk : k < sOrder) : hRow k = Lf CF k :=
  (enum_facts hR).2.1 k hk

theorem eltS_mul_val {a b : ℕ} (ha : a < sOrder) (hb : b < sOrder) :
    (eltS a * eltS b).val.val = rowsMatrix 22 (unpackR 22 (mulV (elemAt CF a) (elemAt CF b))) := by
  rw [val_val_mul, eltS_val_hRow ha, eltS_val_hRow hb, ← rowsMatrix_mulRows, hRow_eq_Lf hR ha,
    hRow_eq_Lf hR hb, Lf, Lf, mulRows_unpack]

theorem mulV_iff {a b c d : ℕ} (ha : a < sOrder) (hb : b < sOrder) (hc : c < sOrder)
    (hd : d < sOrder) :
    mulV (elemAt CF a) (elemAt CF b) = mulV (elemAt CF c) (elemAt CF d) ↔
      eltS a * eltS b = eltS c * eltS d := by
  constructor
  · intro h
    apply eq_of_val_val
    rw [eltS_mul_val hR ha hb, eltS_mul_val hR hc hd, h]
  · intro h
    apply unpack_inj (mulV_lt _ _) (mulV_lt _ _)
    apply eq_of_rowsMatrix_eq (wfRows_unpack _) (wfRows_unpack _)
    rw [← eltS_mul_val hR ha hb, ← eltS_mul_val hR hc hd, h]

theorem sq_iff {k : ℕ} (hk : k < sOrder) :
    mulV (elemAt CF k) (elemAt CF k) = IDP ↔ eltS k * eltS k = 1 := by
  constructor
  · intro h
    apply eq_of_val_val
    rw [eltS_mul_val hR hk hk, h, ← idRows_eq, rowsMatrix_idRows, val_val_one]
  · intro h
    apply unpack_inj (mulV_lt _ _) IDP_lt
    apply eq_of_rowsMatrix_eq (wfRows_unpack _) (wfRows_unpack _)
    rw [← eltS_mul_val hR hk hk, h, ← idRows_eq, rowsMatrix_idRows, val_val_one]

end Entries

theorem exists_eq_of_injective_finset {α : Type*} [Finite α] (T : Finset ℕ) (φ : α → ℕ)
    (hφ : Function.Injective φ) (hmem : ∀ x, φ x ∈ T) (hcard : T.card ≤ Nat.card α) :
    ∀ j ∈ T, ∃ x, φ x = j := by
  intro j hj
  by_contra hne
  have hne : ∀ x, φ x ≠ j := fun x hx => hne ⟨x, hx⟩
  have h1 := card_le_card_finset (T.erase j) φ hφ (fun x => by
    rw [Finset.mem_erase]
    exact ⟨hne x, hmem x⟩)
  have h3 := Finset.card_pos.2 ⟨j, hj⟩
  rw [Finset.card_erase_of_mem hj] at h1
  omega

section Checks

variable {CF G Y FW SQ W RP CA : ℕ → ℕ}

theorem exists_pos (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true) {x : NativeSporadic.Co2}
    (hx : x ∈ sylowS) (hx2 : x * x = 1) : ∃ i < 6144, eltS (pOf (wAt W i)) = x := by
  obtain ⟨k, hk, rfl⟩ := exists_eltS_of_mem hx
  obtain ⟨i, hi, hik⟩ := sq_complete hb hc hca k hk ((sq_iff hR hk).2 hx2)
  exact ⟨i, hi, by rw [hik]⟩

theorem card_le_filter {E : Subgroup NativeSporadic.Co2} {h : NativeSporadic.Co2}
    (Q : ℕ → Prop) [DecidablePred Q]
    (hmap : ∀ z ∈ E, ∃ i < 6144, Q i ∧ eltS (pOf (wAt W i)) = h * z * h⁻¹) :
    Nat.card E ≤ ((Finset.range 6144).filter Q).card := by
  choose i hi hQ he using fun z : E => hmap z z.2
  have hinj : Function.Injective i := by
    intro z z' hzz
    have h1 : h * (z : NativeSporadic.Co2) * h⁻¹ = h * z' * h⁻¹ := by
      rw [← he z, ← he z', hzz]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  exact card_le_card_finset _ i hinj fun z =>
    Finset.mem_filter.2 ⟨Finset.mem_range.2 (hi z), hQ z⟩

theorem partner_le (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    {E : Subgroup NativeSporadic.Co2} (hE : CFSG.Open.IsElemAbelian 2 E)
    {h : NativeSporadic.Co2} (hS : ∀ y ∈ E, h * y * h⁻¹ ∈ sylowS) {z : NativeSporadic.Co2}
    (hz : z ∈ E) {r : ℕ} (hr : r < sOrder) (hrz : eltS r = h * z * h⁻¹)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ y ∈ E, ∀ i < 6144, eltS (pOf (wAt W i)) = h * y * h⁻¹ →
      mulV (SQ i) (elemAt CF r) = mulV (elemAt CF r) (SQ i) → Q i) :
    Nat.card E ≤ ((Finset.range 6144).filter Q).card := by
  refine card_le_filter (W := W) (h := h) Q fun y hy => ?_
  have hy2 : h * y * h⁻¹ * (h * y * h⁻¹) = 1 := by
    rw [conj_mul_conj, mul_self_of_isElemAbelian hE hy, mul_one, mul_inv_cancel]
  obtain ⟨i, hi, hiy⟩ := exists_pos hR hb hc hca (hS y hy) hy2
  refine ⟨i, hi, hQ y hy i hi hiy ?_, hiy⟩
  rw [(bind_sound (hb i hi)).1]
  refine (mulV_iff hR (pOf_lt _) hr hr (pOf_lt _)).2 ?_
  rw [hiy, hrz, conj_mul_conj, conj_mul_conj, mul_comm_of_isElemAbelian hE hy hz]

theorem conj_of_wit (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    {h z : NativeSporadic.Co2} {i : ℕ} (hi : i < 6144)
    (hiz : eltS (pOf (wAt W i)) = h * z * h⁻¹) {s r : ℕ} (hs : s < sOrder) (hr : r < sOrder)
    (hw : mulV (elemAt CF s) (SQ i) = mulV (elemAt CF r) (elemAt CF s)) :
    eltS r = (eltS s * h) * z * (eltS s * h)⁻¹ := by
  rw [(bind_sound (hb i hi)).1] at hw
  have hconj := (mulV_iff hR hs (pOf_lt _) hr hs).1 hw
  rw [conj_conj, ← hiz]
  exact eq_conj_of_mul_eq hconj

theorem conj_mem_S {E : Subgroup NativeSporadic.Co2} {h : NativeSporadic.Co2}
    (hS : ∀ y ∈ E, h * y * h⁻¹ ∈ sylowS) (s : ℕ) :
    ∀ y ∈ E, (eltS s * h) * y * (eltS s * h)⁻¹ ∈ sylowS := by
  intro y hy
  rw [conj_conj]
  exact mul_mem (mul_mem (eltS_mem s) (hS y hy)) (inv_mem (eltS_mem s))

theorem t1_eq_one (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (hw : ∀ i < 6144, witK CF SQ W RP i = true)
    {E : Subgroup NativeSporadic.Co2} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 1024 ≤ Nat.card E) {h : NativeSporadic.Co2} (hS : ∀ y ∈ E, h * y * h⁻¹ ∈ sylowS)
    {z : NativeSporadic.Co2} (hz : z ∈ E) {i : ℕ} (hi : i < 6144)
    (hiz : eltS (pOf (wAt W i)) = h * z * h⁻¹) : t1Of (wAt W i) = 1 := by
  rcases (by have := t1Of_lt (wAt W i); omega : t1Of (wAt W i) = 0 ∨ t1Of (wAt W i) = 1)
    with h0 | h0
  · exfalso
    obtain ⟨hj, hconj⟩ := (wit_sound (hw i hi)).1 h0
    obtain ⟨hr, hcnt⟩ := part1_sound (h1 _ hj)
    have hrel := conj_of_wit hR hb hi hiz (cjOf_lt _) hr hconj
    have := partner_le hR hb hc hca hE (conj_mem_S hS _) hz hr hrel _
      fun _ _ _ _ _ hcomm => hcomm
    omega
  · exact h0

theorem t2_eq_one (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (h2 : ∀ j < 17, part2K CF SQ W RP j = true)
    (hw : ∀ i < 6144, witK CF SQ W RP i = true)
    {E : Subgroup NativeSporadic.Co2} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 1024 ≤ Nat.card E) {h : NativeSporadic.Co2} (hS : ∀ y ∈ E, h * y * h⁻¹ ∈ sylowS)
    {z : NativeSporadic.Co2} (hz : z ∈ E) {i : ℕ} (hi : i < 6144)
    (hiz : eltS (pOf (wAt W i)) = h * z * h⁻¹) : t2Of (wAt W i) = 1 := by
  have ht1 := t1_eq_one hR hb hc hca h1 hw hE hcard hS hz hi hiz
  rcases (by have := t2Of_lt (wAt W i); omega : t2Of (wAt W i) = 0 ∨ t2Of (wAt W i) = 1)
    with h0 | h0
  · exfalso
    obtain ⟨hj, hconj⟩ := (wit_sound (hw i hi)).2 ht1 h0
    obtain ⟨hr, hcnt⟩ := part2_sound (h2 _ hj)
    have hrel := conj_of_wit hR hb hi hiz (cjOf_lt _) hr hconj
    have := partner_le hR hb hc hca hE (conj_mem_S hS _) hz hr hrel
      (fun i' => t1Of (wAt W i') = 1 ∧ mulV (SQ i') (elemAt CF (RP (31 + jOf (wAt W i)))) =
        mulV (elemAt CF (RP (31 + jOf (wAt W i)))) (SQ i'))
      fun y hy i' hi' hiy hcomm =>
        ⟨t1_eq_one hR hb hc hca h1 hw hE hcard (conj_mem_S hS _) hy hi' hiy, hcomm⟩
    omega
  · exact h0

theorem exists_conj_L2 (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (h2 : ∀ j < 17, part2K CF SQ W RP j = true)
    (hw : ∀ i < 6144, witK CF SQ W RP i = true)
    {E : Subgroup NativeSporadic.Co2} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 1024 ≤ Nat.card E) :
    ∃ g : NativeSporadic.Co2, ∀ z ∈ E, ∃ i < 6144, inL2K W i = true ∧
      eltS (pOf (wAt W i)) = g * z * g⁻¹ := by
  have hEp : IsPGroup 2 E := fun x =>
    ⟨1, Subtype.ext (by simpa using hE.2 (x : NativeSporadic.Co2) x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS_of_isPGroup hEp
  refine ⟨g, fun z hz => ?_⟩
  have hz2 : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
    rw [conj_mul_conj, mul_self_of_isElemAbelian hE hz, mul_one, mul_inv_cancel]
  obtain ⟨i, hi, hiz⟩ := exists_pos hR hb hc hca (hg z hz) hz2
  refine ⟨i, hi, inL2K_iff.2 ⟨hi, t1_eq_one hR hb hc hca h1 hw hE hcard hg hz hi hiz,
    t2_eq_one hR hb hc hca h1 h2 hw hE hcard hg hz hi hiz⟩, hiz⟩

theorem card_le_1024 (hR : Recs CF G Y FW sOrder) (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (h2 : ∀ j < 17, part2K CF SQ W RP j = true)
    (hw : ∀ i < 6144, witK CF SQ W RP i = true) (hl2 : l2K W = true)
    {E : Subgroup NativeSporadic.Co2} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 1024 ≤ Nat.card E) : Nat.card E ≤ 1024 := by
  obtain ⟨g, hg⟩ := exists_conj_L2 hR hb hc hca h1 h2 hw hE hcard
  have := card_le_filter (h := g) (fun i => inL2K W i = true) hg
  rwa [l2_sound hl2] at this

theorem elemAbelianLt_of_K (hR : Recs CF G Y FW sOrder)
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (h2 : ∀ j < 17, part2K CF SQ W RP j = true)
    (hw : ∀ i < 6144, witK CF SQ W RP i = true) (hl2 : l2K W = true) :
    ElemAbelianLt NativeSporadic.Co2 (2 ^ 11) := by
  intro E hE
  by_contra hlt
  have hlt : 2 ^ 11 ≤ Nat.card E := not_lt.1 hlt
  have := card_le_1024 hR hb hc hca h1 h2 hw hl2 hE (by omega)
  omega

@[expose] noncomputable def v0K (W : ℕ → ℕ) : Subgroup NativeSporadic.Co2 :=
  Subgroup.closure {x | ∃ i < 6144, inL2K W i = true ∧ eltS (pOf (wAt W i)) = x}

theorem exists_conj_eq_v0K (hR : Recs CF G Y FW sOrder)
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true)
    (hc : ∀ c < 64, chunkK CF CA c = true) (hca : caK CA = true)
    (h1 : ∀ j < 31, part1K CF SQ RP j = true) (h2 : ∀ j < 17, part2K CF SQ W RP j = true)
    (hw : ∀ i < 6144, witK CF SQ W RP i = true) (hl2 : l2K W = true)
    (E : Subgroup NativeSporadic.Co2) (hE : CFSG.Open.IsElemAbelian 2 E)
    (hcard : 2 ^ 10 ≤ Nat.card E) :
    ∃ g : NativeSporadic.Co2, E.map (MulAut.conj g).toMonoidHom = v0K W := by
  obtain ⟨g, hg⟩ := exists_conj_L2 hR hb hc hca h1 h2 hw hE hcard
  choose i hi hL he using fun z : E => hg z z.2
  have hinj : Function.Injective i := by
    intro z z' hzz
    have h1 : g * (z : NativeSporadic.Co2) * g⁻¹ = g * z' * g⁻¹ := by
      rw [← he z, ← he z', hzz]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hcover := exists_eq_of_injective_finset ((Finset.range 6144).filter fun i =>
    inL2K W i = true) i hinj (fun z => Finset.mem_filter.2 ⟨Finset.mem_range.2 (hi z), hL z⟩)
    (by rw [l2_sound hl2]; exact hcard)
  unfold v0K
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨i ⟨z, hz⟩, hi ⟨z, hz⟩, hL ⟨z, hz⟩, he ⟨z, hz⟩⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨j, hj, hjL, rfl⟩
    obtain ⟨z, hz⟩ := hcover j (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hjL⟩)
    rw [← hz, he z]
    exact ⟨z, z.2, rfl⟩

theorem conj_mem_gensK (hR : Recs CF G Y FW sOrder)
    (hb : ∀ i < 6144, bindK CF SQ W CA i = true) {X : ℕ}
    (hX : ∀ i, inL2K W i = true → ∃ m, inL2K W m = true ∧ mulV X (SQ i) = mulV (SQ m) X)
    {x : NativeSporadic.Co2} (hx : x.val.val = rowsMatrix 22 (unpackR 22 X)) :
    ∀ s ∈ {x : NativeSporadic.Co2 | ∃ i < 6144, inL2K W i = true ∧ eltS (pOf (wAt W i)) = x},
      x * s * x⁻¹ ∈
        {x : NativeSporadic.Co2 | ∃ i < 6144, inL2K W i = true ∧ eltS (pOf (wAt W i)) = x} := by
  rintro _ ⟨i, hi, hiL, rfl⟩
  obtain ⟨m, hmL, hm⟩ := hX i hiL
  have hm6 := (inL2K_iff.1 hmL).1
  refine ⟨m, hm6, hmL, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply eq_of_val_val
  rw [val_val_mul, val_val_mul, hx, eltS_val_hRow (pOf_lt _), eltS_val_hRow (pOf_lt _),
    hRow_eq_Lf hR (pOf_lt _), hRow_eq_Lf hR (pOf_lt _), Lf, Lf, ← (bind_sound (hb i hi)).1,
    ← (bind_sound (hb m hm6)).1, ← rowsMatrix_mulRows, ← rowsMatrix_mulRows, mulRows_unpack,
    mulRows_unpack, hm]

end Checks

end CFSG.KC.Co2HeavyK

end

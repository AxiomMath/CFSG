module

public import Certificates.Data.Kernel.S8E58K
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6S8Data

public section

namespace CFSG.KC.S8E58K

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H13 S8E

structure TabOK (CM MT FX : Nat) : Prop where
  comm : ∀ a < 44, ∀ b < 44, CommL (iv a) (iv b) ↔ cm CM a b = true
  prod : ∀ a < 44, ∀ b < 44, cm CM a b = true → mt MT a b < 44 ∧ cmp (iv a) (iv b) = iv (mt MT a b)
  fix : ∀ a < 44, ∀ p < 8, ap (iv a) p = p ↔ (fx FX a).testBit p = true
  inj : ∀ a < 44, ∀ b < 44, iv a = iv b → a = b

theorem iv43 : iv 43 = id8 := rfl

theorem fx_lt (FX a : Nat) : fx FX a < 2 ^ 8 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem lt8_of_bit {X p : Nat} (hX : X < 2 ^ 8) (h : X.testBit p = true) : p < 8 := by
  rcases Nat.lt_or_ge p 8 with hc | hc
  · exact hc
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) hc))] at h
    exact Bool.noConfusion h

theorem bit_of_ne0 {X : Nat} (h : (!(Nat.beq X 0)) = true) : ∃ p, X.testBit p = true := by
  rw [Bool.not_eq_true'] at h
  have hY : X ≠ 0 := fun e => by
    rw [e] at h
    exact Bool.noConfusion h
  exact Nat.exists_testBit_of_ne_zero hY

theorem mem_id8 {p : Nat} (h : p < 8) : p ∈ id8 := by
  unfold id8
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lt8_of_mem {p : Nat} (h : p ∈ id8) : p < 8 := by
  unfold id8 at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  omega

variable {CM MT FX : Nat} (T : TabOK CM MT FX)
include T

theorem iv_ne {a b : Nat} (ha : a < 44) (hb : b < 44) (h : a ≠ b) : iv a ≠ iv b :=
  fun e => h (T.inj a ha b hb e)

theorem iv_ne_id {a : Nat} (ha : a < 44) (h : a ≠ 43) : iv a ≠ id8 := by
  rw [← iv43]
  exact iv_ne T ha (by decide) h

theorem fpf_of {a : Nat} (ha : a < 44) (h : Nat.beq (fx FX a) 0 = true) : Fpf (iv a) := by
  intro i hi e
  have h1 := (T.fix a ha i (lt8_of_mem hi)).1 e
  rw [Nat.eq_of_beq_eq_true h, Nat.zero_testBit] at h1
  exact Bool.noConfusion h1

theorem w2_sound {a b c : Nat} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (h : w2K FX a b c = true) : W2b (iv a) (iv b) (iv c) := by
  unfold w2K at h
  rw [Bool.and_eq_true] at h
  obtain ⟨p, hp⟩ := bit_of_ne0 h.1
  obtain ⟨r, hr⟩ := bit_of_ne0 h.2
  change ((fx FX b &&& fx FX c) &&& (255 ^^^ fx FX a)).testBit p = true at hp
  change ((fx FX b &&& fx FX c) &&& fx FX a).testBit r = true at hr
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_eq_true, Bool.and_eq_true] at hp hr
  have hp8 := lt8_of_bit (fx_lt FX b) hp.1.1
  have hr8 := lt8_of_bit (fx_lt FX b) hr.1.1
  have h255 : (255 : Nat) = 2 ^ 8 - 1 := by decide
  rw [Nat.testBit_xor, h255, Nat.testBit_two_pow_sub_one] at hp
  simp only [hp8, decide_true, Bool.true_xor, Bool.not_eq_true'] at hp
  refine ⟨⟨p, mem_id8 hp8, fun e => ?_, (T.fix b hb p hp8).2 hp.1.1, (T.fix c hc p hp8).2 hp.1.2⟩,
    r, mem_id8 hr8, (T.fix a ha r hr8).2 hr.2, (T.fix b hb r hr8).2 hr.1.1,
    (T.fix c hc r hr8).2 hr.1.2⟩
  rw [(T.fix a ha p hp8).1 e] at hp
  exact Bool.noConfusion hp.2

theorem w8_sound {a b c : Nat} (ha : a < 44) (hb : b < 44) (hc : c < 44)
    (h : w8K CM MT FX a b c = true) : W8b (iv a) (iv b) (iv c) := by
  unfold w8K at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  have pab := T.prod a ha b hb h1
  have pac := T.prod a ha c hc h2
  have pbc := T.prod b hb c hc h3
  have pabc := T.prod a ha _ pbc.1 h4
  refine ⟨fpf_of T ha h5, ?_, ?_, ?_⟩
  · rw [pab.2]
    exact fpf_of T pab.1 h6
  · rw [pac.2]
    exact fpf_of T pac.1 h7
  · rw [pbc.2, pabc.2]
    exact fpf_of T pabc.1 h8

theorem w3_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) {x : Nat}
    (h : w3X CM MT FX L x = true) : W3 (L.map iv) := by
  unfold w3X w3K at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.contains_iff_mem,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨hb, h1⟩, ha⟩, h'⟩ := h
  have ha' := hL _ ha
  have hb' := hL _ hb
  exact ⟨_, List.mem_map_of_mem hb, iv_ne_id T hb' h1, _, List.mem_map_of_mem ha,
    h'.imp (w2_sound T ha' hb' hb') (w8_sound T ha' hb' hb')⟩

theorem w4_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) {x : Nat}
    (h : w4X CM MT FX L x = true) :
    ∃ b ∈ L.map iv, b ≠ id8 ∧ ∃ c ∈ L.map iv, c ≠ id8 ∧ c ≠ b ∧ ∃ a ∈ L.map iv,
      W2b a b c ∨ W8b a b c := by
  unfold w4X w4K at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, List.contains_iff_mem,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hb, h1⟩, hc⟩, h2⟩, h3⟩, ha⟩, h'⟩ := h
  have ha' := hL _ ha
  have hb' := hL _ hb
  have hc' := hL _ hc
  exact ⟨_, List.mem_map_of_mem hb, iv_ne_id T hb' h1, _, List.mem_map_of_mem hc,
    iv_ne_id T hc' h2, iv_ne T hc' hb' h3, _, List.mem_map_of_mem ha,
    h'.imp (w2_sound T ha' hb' hc') (w8_sound T ha' hb' hc')⟩

structure G3 (CM MT i j k : Nat) : Prop where
  hi : i < 44
  hj : j < 44
  hk : k < 44
  ij : cm CM i j = true
  ik : cm CM i k = true
  jk : cm CM j k = true
  ijk : cm CM i (mt MT j k) = true

theorem grp3_eq {i j k : Nat} (G : G3 CM MT i j k) :
    grp3 (iv i) (iv j) (iv k) = (g3 MT i j k).map iv := by
  have hjk := T.prod j G.hj k G.hk G.jk
  unfold grp3 g3
  rw [(T.prod i G.hi j G.hj G.ij).2, (T.prod i G.hi k G.hk G.ik).2, hjk.2,
    (T.prod i G.hi _ hjk.1 G.ijk).2]
  rfl

theorem g3_lt {i j k : Nat} (G : G3 CM MT i j k) : ∀ a ∈ g3 MT i j k, a < 44 := by
  have h1 := (T.prod i G.hi j G.hj G.ij).1
  have h2 := (T.prod i G.hi k G.hk G.ik).1
  have hjk := T.prod j G.hj k G.hk G.jk
  have h4 := (T.prod i G.hi _ hjk.1 G.ijk).1
  have h3 := hjk.1
  have := G.hi
  have := G.hj
  have := G.hk
  unfold g3
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem grp4_eq {L : List Nat} (hL : ∀ a ∈ L, a < 44) {l : Nat} (hl : l < 44)
    (h : L.all (fun f => cm CM f l) = true) : grp4 (L.map iv) (iv l) = (g4 MT L l).map iv := by
  unfold grp4 g4
  rw [List.map_append, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun f hf => ?_
  exact (T.prod f (hL f hf) l hl (List.all_eq_true.1 h f hf)).2

theorem g4_lt {L : List Nat} (hL : ∀ a ∈ L, a < 44) {l : Nat} (hl : l < 44)
    (h : L.all (fun f => cm CM f l) = true) : ∀ a ∈ g4 MT L l, a < 44 := by
  intro a ha
  unfold g4 at ha
  rcases List.mem_append.1 ha with ha | ha
  · exact hL a ha
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ha
    exact (T.prod f (hL f hf) l hl (List.all_eq_true.1 h f hf)).1

theorem contains4_false {k i j m : Nat} (hk : iv k ∉ [iv 43, iv i, iv j, iv m]) :
    [43, i, j, m].contains k = false := by
  rw [Bool.eq_false_iff]
  intro hc
  apply hk
  rw [List.contains_iff_mem] at hc
  exact List.mem_map_of_mem (f := iv) hc

theorem contains_false {L : List Nat} {l : Nat} (hl : iv l ∉ L.map iv) : L.contains l = false := by
  rw [Bool.eq_false_iff]
  intro hc
  rw [List.contains_iff_mem] at hc
  exact hl (List.mem_map_of_mem hc)

omit T in
theorem blt_t {a b : Nat} (h : a < b) : Nat.blt a b = true := by
  rw [Nat.blt_eq]
  exact h

theorem max4_of {L : List Nat} {i j k l : Nat} (hi : i < 44) (hj : j < 44) (hk : k < 44)
    (hl : l < 44) (h : max4K CM L i j k l = true) :
    ∀ n ∈ List.range 43, CommL (iv n) (iv i) → CommL (iv n) (iv j) → CommL (iv n) (iv k) →
      CommL (iv n) (iv l) → iv n ∈ L.map iv := by
  intro n hn c1 c2 c3 c4
  rw [List.mem_range] at hn
  unfold max4K at h
  have h1 := PK.allN_iff.1 h n hn
  rw [(T.comm n (by omega) i hi).1 c1, (T.comm n (by omega) j hj).1 c2,
    (T.comm n (by omega) k hk).1 c3, (T.comm n (by omega) l hl).1 c4] at h1
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h1
  exact List.mem_map_of_mem h1

theorem k34_of {R W : Nat} (h : ∀ i < 43, k34K CM MT FX R W i = true) : K34 := by
  intro i hi j hj hij hcij k hk hjk hcik hcjk hkn
  rw [List.mem_range] at hi hj hk
  have h1 := h i hi
  unfold k34K at h1
  have h2 := PK.allN_iff.1 (PK.allN_iff.1 h1 j hj) k hk
  have cij := (T.comm i (by omega) j (by omega)).1 hcij
  have cik := (T.comm i (by omega) k (by omega)).1 hcik
  have cjk := (T.comm j (by omega) k (by omega)).1 hcjk
  have hpij := T.prod i (by omega) j (by omega) cij
  have hkn' : [43, i, j, mt MT i j].contains k = false := by
    refine contains4_false T ?_
    rw [iv43, ← hpij.2]
    exact hkn
  rw [blt_t hij, blt_t hjk, cij, cik, cjk, hkn'] at h2
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h2
  have G : G3 CM MT i j k := ⟨by omega, by omega, by omega, cij, cik, cjk, h2.1⟩
  have h3 := h2.2
  simp only [PK.strictB_eq] at h3
  unfold t34K at h3
  simp only [PK.strictB_eq, Bool.and_eq_true] at h3
  rw [grp3_eq T G]
  refine ⟨w3_sound T (g3_lt T G) h3.1, ?_⟩
  intro l hl hkl cil cjl ckl hln
  rw [List.mem_range] at hl
  have h4 := PK.allN_iff.1 h3.2 l hl
  rw [blt_t hkl, (T.comm i (by omega) l (by omega)).1 cil,
    (T.comm j (by omega) l (by omega)).1 cjl, (T.comm k (by omega) l (by omega)).1 ckl,
    contains_false T hln] at h4
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    PK.strictB_eq] at h4
  obtain ⟨⟨hall, hw4⟩, hmax⟩ := h4
  rw [grp4_eq T (g3_lt T G) (by omega) hall]
  exact ⟨w4_sound T (g4_lt T (g3_lt T G) (by omega) hall) hw4,
    max4_of T (by omega) (by omega) (by omega) (by omega) hmax⟩

end CFSG.KC.S8E58K

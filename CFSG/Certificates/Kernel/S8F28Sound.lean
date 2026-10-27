module

public import Certificates.Data.Kernel.S8F28K
public import CFSG.Certificates.Kernel.Spor.PK.Basic
public import CFSG.Quasithin.Vol2.Ch12Sec6S8Facts28

public section

namespace CFSG.KC.S8F28K

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H13 S8E S8F

structure TabOK (CM MT FMK : Nat) : Prop where
  comm : ∀ a < 44, ∀ b < 44, CommL (iv a) (iv b) ↔ cm CM a b = true
  prod : ∀ a < 44, ∀ b < 44, cm CM a b = true → mt MT a b < 44 ∧ cmp (iv a) (iv b) = iv (mt MT a b)
  fix : ∀ a < 44, ∀ v < 128, FixL (iv a) (VECS.getD v []) ↔ (fk FMK a).testBit v = true
  vec : ∀ v < 128, Vec (VECS.getD v [])
  inj : ∀ a < 44, ∀ b < 44, iv a = iv b → a = b

theorem iv43 : iv 43 = id8 := rfl

theorem m128_eq : m128 = 2 ^ 128 - 1 := by decide

theorem fk_lt (FMK a : Nat) : fk FMK a < 2 ^ 128 := by
  have h : fk FMK a ≤ m128 := Nat.and_le_right
  rw [m128_eq] at h
  have : (0 : Nat) < 2 ^ 128 := Nat.two_pow_pos 128
  omega

theorem bit_and {X Y v : Nat} (h : (Nat.land X Y).testBit v = true) :
    X.testBit v = true ∧ Y.testBit v = true := by
  change (X &&& Y).testBit v = true at h
  rw [Nat.testBit_and, Bool.and_eq_true] at h
  exact h

theorem land_lt {X Y : Nat} (hY : Y < 2 ^ 128) : Nat.land X Y < 2 ^ 128 :=
  Nat.lt_of_le_of_lt Nat.and_le_right hY

theorem dz_spec {X F : Nat} (hX : X < 2 ^ 128) (h : dz X F = true) :
    ∃ v < 128, X.testBit v = true ∧ F.testBit v = false := by
  unfold dz at h
  rw [Bool.not_eq_true'] at h
  have hY : Nat.land X (Nat.xor m128 F) ≠ 0 := fun e => by
    rw [e] at h
    exact Bool.noConfusion h
  obtain ⟨v, hv⟩ := Nat.exists_testBit_of_ne_zero hY
  change (X &&& (m128 ^^^ F)).testBit v = true at hv
  rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_xor, m128_eq, Nat.testBit_two_pow_sub_one]
    at hv
  obtain ⟨h1, h2⟩ := hv
  have hv128 : v < 128 := by
    rcases Nat.lt_or_ge v 128 with hc | hc
    · exact hc
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) hc))]
        at h1
      exact Bool.noConfusion h1
  refine ⟨v, hv128, h1, ?_⟩
  simp only [hv128, decide_true, Bool.true_xor, Bool.not_eq_true'] at h2
  exact h2

theorem fAnd_clear {FMK v : Nat} (hv : v < 128) :
    ∀ L : List Nat, (fAnd FMK L).testBit v = false → ∃ a ∈ L, (fk FMK a).testBit v = false
  | [], h => by
    unfold fAnd at h
    rw [List.foldr_nil, m128_eq, Nat.testBit_two_pow_sub_one] at h
    simp [hv] at h
  | a :: L, h => by
    unfold fAnd at h
    rw [List.foldr_cons] at h
    change (fk FMK a &&& fAnd FMK L).testBit v = false at h
    rw [Nat.testBit_and, Bool.and_eq_false_iff] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hb'⟩ := fAnd_clear hv L h
      exact ⟨b, List.mem_cons_of_mem a hb, hb'⟩

variable {CM MT FMK : Nat} (T : TabOK CM MT FMK)
include T

theorem iv_ne {a b : Nat} (ha : a < 44) (hb : b < 44) (h : a ≠ b) : iv a ≠ iv b :=
  fun e => h (T.inj a ha b hb e)

theorem iv_ne_id {a : Nat} (ha : a < 44) (h : a ≠ 43) : iv a ≠ id8 := by
  rw [← iv43]
  exact iv_ne T ha (by decide) h

theorem not_mem4 {a b c d : Nat} (ha : a < 44) (hb : b < 44) (hc : c < 44) (hd : d < 44)
    (h : [43, b, c, d].contains a = false) : iv a ∉ [id8, iv b, iv c, iv d] := by
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨iv_ne_id T ha h1, iv_ne T ha hb h2, iv_ne T ha hc h3, iv_ne T ha hd h4⟩

theorem not_mem2 {a b : Nat} (ha : a < 44) (hb : b < 44) (h : [43, b].contains a = false) :
    iv a ∉ [id8, iv b] := by
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨iv_ne_id T ha h.1, iv_ne T ha hb h.2⟩

theorem sep_of {L bs : List Nat} (hL : ∀ a ∈ L, a < 44) {v : Nat} (hv : v < 128)
    (hF : (fAnd FMK L).testBit v = false) (hbs : ∀ b ∈ bs, b < 44 ∧ (fk FMK b).testBit v = true) :
    SepW (bs.map iv) (L.map iv) (VECS.getD v []) := by
  refine ⟨T.vec v hv, ?_, ?_⟩
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
    exact (T.fix b' (hbs b' hb').1 v hv).2 (hbs b' hb').2
  · obtain ⟨a, ha, ha'⟩ := fAnd_clear hv L hF
    refine ⟨iv a, List.mem_map_of_mem ha, fun hfix => ?_⟩
    rw [(T.fix a (hL a ha) v hv).1 hfix] at ha'
    exact Bool.noConfusion ha'

theorem ok1_of {L : List Nat} (hL : ∀ a ∈ L, a < 44) {b : Nat} (hb : b ∈ L) (hb1 : b ≠ 43)
    (hd : dz (fk FMK b) (fAnd FMK L) = true) : ∃ u, Ok1 (L.map iv) (iv b, u) := by
  obtain ⟨v, hv, h1, h2⟩ := dz_spec (fk_lt FMK b) hd
  refine ⟨VECS.getD v [], List.mem_map_of_mem hb, iv_ne_id T (hL b hb) hb1, ?_⟩
  exact sep_of T hL hv h2 (bs := [b]) (by simpa using ⟨hL b hb, h1⟩)

theorem s1_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : s1K FMK L (fAnd FMK L) = true) :
    ∃ w, Ok1 (L.map iv) w := by
  unfold s1K at h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨u, hu⟩ := ok1_of T hL hb h.1 h.2
  exact ⟨_, hu⟩

theorem sep2_of {L : List Nat} (hL : ∀ a ∈ L, a < 44) {d e : Nat} (hd : d ∈ L) (he : e ∈ L)
    (h : dz (Nat.land (fk FMK d) (fk FMK e)) (fAnd FMK L) = true) :
    ∃ u, SepW [iv d, iv e] (L.map iv) u := by
  obtain ⟨v, hv, h1, h2⟩ := dz_spec (land_lt (fk_lt FMK e)) h
  obtain ⟨h1d, h1e⟩ := bit_and h1
  exact ⟨_, sep_of T hL hv h2 (bs := [d, e]) (by simpa using ⟨⟨hL d hd, h1d⟩, hL e he, h1e⟩)⟩

theorem s2_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : s2K FMK L (fAnd FMK L) = true) :
    ∃ w, Ok2 (L.map iv) w := by
  unfold s2K at h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨hb1, hc1⟩, hbc⟩, hd⟩ := h
  obtain ⟨v, hv, h1, h2⟩ := dz_spec (land_lt (fk_lt FMK c)) hd
  obtain ⟨h1b, h1c⟩ := bit_and h1
  refine ⟨(iv b, iv c, VECS.getD v []), List.mem_map_of_mem hb, List.mem_map_of_mem hc,
    iv_ne_id T (hL b hb) hb1, iv_ne_id T (hL c hc) hc1, iv_ne T (hL b hb) (hL c hc) hbc, ?_⟩
  exact sep_of T hL hv h2 (bs := [b, c]) (by simpa using ⟨⟨hL b hb, h1b⟩, hL c hc, h1c⟩)

theorem s3_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44)
    (h : s3K CM MT FMK L (fAnd FMK L) = true) : ∃ w, Ok3 (L.map iv) w := by
  unfold s3K at h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨hb1, hc1⟩, hbc⟩, hcm⟩, -⟩, h⟩ := h
  obtain ⟨d, hd, h⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hdn, hdz⟩ := h
  obtain ⟨v, hv, h1, h2⟩ := dz_spec (land_lt (fk_lt FMK d)) hdz
  obtain ⟨h1bc, h1d⟩ := bit_and h1
  obtain ⟨h1b, h1c⟩ := bit_and h1bc
  have hp := T.prod b (hL b hb) c (hL c hc) hcm
  refine ⟨(iv b, iv c, iv d, VECS.getD v []), List.mem_map_of_mem hb, List.mem_map_of_mem hc,
    List.mem_map_of_mem hd, iv_ne_id T (hL b hb) hb1, iv_ne_id T (hL c hc) hc1,
    iv_ne T (hL b hb) (hL c hc) hbc, ?_, ?_⟩
  · change iv d ∉ [id8, iv b, iv c, S8E.cmp (iv b) (iv c)]
    rw [hp.2]
    exact not_mem4 T (hL d hd) (hL b hb) (hL c hc) hp.1 hdn
  · exact sep_of T hL hv h2 (bs := [b, c, d])
      (by simpa using ⟨⟨hL b hb, h1b⟩, ⟨hL c hc, h1c⟩, hL d hd, h1d⟩)

theorem e3_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : e3K FMK L (fAnd FMK L) = true) :
    ∃ w, OkE3 (L.map iv) w := by
  unfold e3K at h
  obtain ⟨a, ha, h⟩ := List.any_eq_true.1 h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hab, hac⟩, hbc⟩, ha1⟩, hda⟩, hb1⟩, hdb⟩, hc1⟩, hdc⟩ := h
  obtain ⟨wa, hwa⟩ := ok1_of T hL ha ha1 hda
  obtain ⟨wb, hwb⟩ := ok1_of T hL hb hb1 hdb
  obtain ⟨wc, hwc⟩ := ok1_of T hL hc hc1 hdc
  exact ⟨((iv a, wa), (iv b, wb), (iv c, wc)), iv_ne T (hL a ha) (hL b hb) hab,
    iv_ne T (hL a ha) (hL c hc) hac, iv_ne T (hL b hb) (hL c hc) hbc, hwa, hwb, hwc⟩

theorem e4_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44)
    (h : e4K CM MT FMK L (fAnd FMK L) = true) : ∃ w, OkE4 (L.map iv) w := by
  unfold e4K at h
  obtain ⟨d, hd, h⟩ := List.any_eq_true.1 h
  rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  obtain ⟨hd1, h⟩ := h
  obtain ⟨a, ha, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨han, hda⟩, hza⟩, h⟩ := h
  obtain ⟨b, hb, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hbn, hdb⟩, hzb⟩, h⟩ := h
  obtain ⟨c, hc, h⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hcn1, hcn2⟩, hzc⟩ := h
  have hpa := T.prod d (hL d hd) a (hL a ha) hda
  have hpb := T.prod d (hL d hd) b (hL b hb) hdb
  obtain ⟨ua, hua⟩ := sep2_of T hL hd ha hza
  obtain ⟨ub, hub⟩ := sep2_of T hL hd hb hzb
  obtain ⟨uc, huc⟩ := sep2_of T hL hd hc hzc
  refine ⟨(iv d, (iv a, ua), (iv b, ub), (iv c, uc)), List.mem_map_of_mem hd,
    iv_ne_id T (hL d hd) hd1, List.mem_map_of_mem ha, List.mem_map_of_mem hb,
    List.mem_map_of_mem hc, not_mem2 T (hL a ha) (hL d hd) han, ?_, ?_, ?_, hua, hub, huc⟩
  · change iv b ∉ [id8, iv d, iv a, S8E.cmp (iv d) (iv a)]
    rw [hpa.2]
    exact not_mem4 T (hL b hb) (hL d hd) (hL a ha) hpa.1 hbn
  · change iv c ∉ [id8, iv d, iv a, S8E.cmp (iv d) (iv a)]
    rw [hpa.2]
    exact not_mem4 T (hL c hc) (hL d hd) (hL a ha) hpa.1 hcn1
  · change iv c ∉ [id8, iv d, iv b, S8E.cmp (iv d) (iv b)]
    rw [hpb.2]
    exact not_mem4 T (hL c hc) (hL d hd) (hL b hb) hpb.1 hcn2

theorem r2_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : r2K FMK L = true) :
    R2w (L.map iv) :=
  s1_sound T hL h

theorem r3_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : r3K FMK L = true) :
    R3w (L.map iv) := by
  unfold r3K at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  exact ⟨s1_sound T hL h.1, h.2.imp (s2_sound T hL) (e3_sound T hL)⟩

theorem r4_sound {L : List Nat} (hL : ∀ a ∈ L, a < 44) (h : r4K CM MT FMK L = true) :
    R4w (L.map iv) := by
  unfold r4K at h
  rw [Bool.and_eq_true, Bool.or_eq_true] at h
  exact ⟨s2_sound T hL h.1, h.2.imp (s3_sound T hL) (e4_sound T hL)⟩

theorem grp2_eq {i j : Nat} (hi : i < 44) (hj : j < 44) (h : cm CM i j = true) :
    grp2 (iv i) (iv j) = (g2 MT i j).map iv := by
  unfold grp2 g2
  rw [(T.prod i hi j hj h).2]
  rfl

theorem g2_lt {i j : Nat} (hi : i < 44) (hj : j < 44) (h : cm CM i j = true) :
    ∀ a ∈ g2 MT i j, a < 44 := by
  have := (T.prod i hi j hj h).1
  unfold g2
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

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

theorem c2w_of (h : c2K CM MT FMK = true) : C2w := by
  intro i hi j hj hij hc
  rw [List.mem_range] at hi hj
  unfold c2K at h
  have h1 := PK.allN_iff.1 (PK.allN_iff.1 h i hi) j hj
  have hcm := (T.comm i (by omega) j (by omega)).1 hc
  have hb : Nat.blt i j = true := blt_t hij
  rw [hb, hcm] at h1
  rw [grp2_eq T (by omega) (by omega) hcm]
  exact r2_sound T (g2_lt T (by omega) (by omega) hcm) (by simpa using h1)

theorem c3w_of (h : ∀ i < 43, c3K CM MT FMK i = true) : C3w := by
  intro i hi j hj hij hcij k hk hjk hcik hcjk hkn
  rw [List.mem_range] at hi hj hk
  have h1 := h i hi
  unfold c3K at h1
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
  rw [grp3_eq T G]
  exact r3_sound T (g3_lt T G) h2.2

theorem max4_of {L : List Nat} {i j k l : Nat} (hi : i < 44) (hj : j < 44) (hk : k < 44)
    (hl : l < 44) (h : max4K CM L i j k l = true) :
    Max4 (L.map iv) (iv i) (iv j) (iv k) (iv l) := by
  intro n hn c1 c2 c3 c4
  rw [List.mem_range] at hn
  unfold max4K at h
  have h1 := PK.allN_iff.1 h n hn
  rw [(T.comm n (by omega) i hi).1 c1, (T.comm n (by omega) j hj).1 c2,
    (T.comm n (by omega) k hk).1 c3, (T.comm n (by omega) l hl).1 c4] at h1
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, List.contains_iff_mem] at h1
  exact List.mem_map_of_mem h1

theorem c4w_of (h : ∀ i < 43, c4K CM MT FMK i = true) : C4w := by
  intro i hi j hj hij hcij k hk hjk hcik hcjk hkn
  rw [List.mem_range] at hi hj hk
  have h1 := h i hi
  unfold c4K at h1
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
  intro l hl hkl cil cjl ckl hln
  rw [List.mem_range] at hl
  have h3 := h2.2
  unfold t4K at h3
  have h4 := PK.allN_iff.1 h3 l hl
  rw [grp3_eq T G] at hln
  rw [blt_t hkl, (T.comm i (by omega) l (by omega)).1 cil,
    (T.comm j (by omega) l (by omega)).1 cjl, (T.comm k (by omega) l (by omega)).1 ckl,
    contains_false T hln] at h4
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h4
  obtain ⟨⟨hall, hr4⟩, hmax⟩ := h4
  rw [grp3_eq T G, grp4_eq T (g3_lt T G) (by omega) hall]
  exact ⟨r4_sound T (g4_lt T (g3_lt T G) (by omega) hall) hr4,
    max4_of T (by omega) (by omega) (by omega) (by omega) hmax⟩

end CFSG.KC.S8F28K

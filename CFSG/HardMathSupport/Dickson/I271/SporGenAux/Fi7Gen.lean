module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Base
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7MatSlp
public import Certificates.Certificate17391

public section

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.Blueprint CFSG.Sporadic.Fi24 CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Seven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open scoped commutatorElement

section Generic

theorem arr_getElem!_append_left {α : Type*} [Inhabited α] (xs ys : Array α) {i : ℕ}
    (hi : i < xs.size) : (xs ++ ys)[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp; omega), getElem!_pos xs i hi,
    Array.getElem_append_left hi]

theorem arr_getElem!_append_right {α : Type*} [Inhabited α] (xs ys : Array α) {i : ℕ}
    (hi : xs.size ≤ i) (hi' : i - xs.size < ys.size) : (xs ++ ys)[i]! = ys[i - xs.size]! := by
  rw [getElem!_pos (xs ++ ys) i (by simp; omega), getElem!_pos ys _ hi',
    Array.getElem_append_right hi]

theorem slpG_append_prefix {G : Type*} [Group G] (gensG : ℤ → G) (W E : Array (List ℤ)) :
    ∀ j < W.size, CFSG.Sporadic.Fi23.slpG gensG (W ++ E) j = CFSG.Sporadic.Fi23.slpG gensG W j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [CFSG.Sporadic.Fi23.slpG_eq gensG (W ++ E) j, CFSG.Sporadic.Fi23.slpG_eq gensG W j,
      arr_getElem!_append_left W E hj]
    congr 2
    funext z
    by_cases h2 : z.natAbs ≤ 2
    · simp only [h2, if_true]
    · simp only [h2, if_false]
      by_cases h3 : z.natAbs - 3 < j
      · simp only [h3, if_true, ih _ h3 (by omega)]
      · simp only [h3, if_false]

end Generic

section Gen


@[expose] def W7 : Array (List ℤ) := fi24SevenData.words ++ fi7Extra ()

@[expose] noncomputable def s7 (j : ℕ) : CFSG.Sporadic.Fi24.J := CFSG.Sporadic.Fi23.slpG genG W7 j

@[expose] def LM7 : Array (Array CFSG.Sporadic.Fi24.Native.W) := mLetters W7

structure Fi7Facts : Prop where
  slp : CFSG.Sporadic.Fi23.Native.slpOK W7 = true
  size_words : fi24SevenData.words.size = 1087
  size_extra : (fi7Extra ()).size = 119
  w0 : fi24SevenData.words[0]! = [1]
  w1 : fi24SevenData.words[1]! = [2]
  c91 : (fi24SevenData.conj[91]!).1 = 1
  c77 : (fi24SevenData.conj[77]!).1 = 1
  e0 : (fi7Extra ())[0]! = (fi24SevenData.conj[91]!).2.map lt2w
  e1 : (fi7Extra ())[1]! = (fi24SevenData.conj[77]!).2.map lt2w
  e2 : (fi7Extra ())[2]! = [-1090, 1088, 1090]
  e3 : (fi7Extra ())[3]! = [-1090, 1089, 1090]
  e4 : (fi7Extra ())[4]! = [-1091, 1088, 1091]
  e5 : (fi7Extra ())[5]! = [-1091, 1089, 1091]
  rules : ∀ r < 112, ∀ z ∈ W7[1093 + r]!, 3 ≤ z.natAbs ∧
    (isGen7 (z.natAbs - 3) = true ∨ (1093 ≤ z.natAbs - 3 ∧ z.natAbs - 3 < 1093 + r))
  e118 : (fi7Extra ())[118]! = [1087, 1085, 1086, 1086]
  wa : eqRows 781 LM7[2 * 1203]! LM7[0]! = true
  wb : eqRows 781 LM7[2 * 1204]! LM7[2]! = true
  comm85 : eqRows 781 (mulW LM7[2 * 1085]! LM7[2 * 67]!) (mulW LM7[2 * 67]! LM7[2 * 1085]!) = true
  comm86 : eqRows 781 (mulW LM7[2 * 1086]! LM7[2 * 67]!) (mulW LM7[2 * 67]! LM7[2 * 1086]!) = true
  comm82 : eqRows 781 (mulW LM7[2 * 1082]! LM7[2 * 66]!) (mulW LM7[2 * 66]! LM7[2 * 1082]!) = true
  comm83 : eqRows 781 (mulW LM7[2 * 1083]! LM7[2 * 66]!) (mulW LM7[2 * 66]! LM7[2 * 1083]!) = true
  comm84 : eqRows 781 (mulW LM7[2 * 1084]! LM7[2 * 66]!) (mulW LM7[2 * 66]! LM7[2 * 1084]!) = true
  pow4 : eqRows 781 (powW 781 LM7[2 * 1205]! 4) (idW 781) = true
  pow2 : eqRows 781 (powW 781 LM7[2 * 1205]! 2) (idW 781) = false


theorem fi7_facts : Fi7Facts := by
  have h := Certificates.certificate17391
  unfold fi7OK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩, h23⟩, h24⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩

theorem W7_size : W7.size = 1206 := by
  have := fi7_facts
  simp only [W7, Array.size_append, this.size_words, this.size_extra]

theorem W7_get_left {j : ℕ} (hj : j < 1087) : W7[j]! = fi24SevenData.words[j]! := by
  rw [W7, arr_getElem!_append_left _ _ (by rw [fi7_facts.size_words]; exact hj)]

theorem W7_get_right {k : ℕ} (hk : k < 119) : W7[1087 + k]! = (fi7Extra ())[k]! := by
  have hs := fi7_facts.size_words
  have hs2 := fi7_facts.size_extra
  have h1 : fi24SevenData.words.size ≤ 1087 + k := by omega
  have h2 : 1087 + k - fi24SevenData.words.size < (fi7Extra ()).size := by omega
  have h3 := arr_getElem!_append_right fi24SevenData.words (fi7Extra ()) h1 h2
  have h4 : 1087 + k - fi24SevenData.words.size = k := by omega
  rw [h4] at h3
  exact h3

theorem s7_prefix {j : ℕ} (hj : j < 1087) : s7 j = g7 j := by
  unfold s7 g7 W7
  exact slpG_append_prefix genG _ _ j (by rw [fi7_facts.size_words]; exact hj)

@[expose] noncomputable def letter7 (j : ℕ) (z : ℤ) : CFSG.Sporadic.Fi24.J :=
  if z.natAbs ≤ 2 then genG z else if z.natAbs - 3 < j then
    (if 0 < z then s7 (z.natAbs - 3) else (s7 (z.natAbs - 3))⁻¹) else 1

theorem s7_eq (j : ℕ) : s7 j = wordG (letter7 j) W7[j]! :=
  CFSG.Sporadic.Fi23.slpG_eq genG W7 j

theorem letter7_pos {j k : ℕ} (hk : k < j) : letter7 j ((k + 3 : ℕ) : ℤ) = s7 k := by
  have h3 : ¬ k + 3 ≤ 2 := by omega
  have h0 : (0 : ℤ) < ((k + 3 : ℕ) : ℤ) := by positivity
  simp only [letter7, Int.natAbs_natCast, h3, if_false, Nat.add_sub_cancel, hk, if_true, h0]

theorem letter7_neg {j k : ℕ} (hk : k < j) : letter7 j (-((k + 3 : ℕ) : ℤ)) = (s7 k)⁻¹ := by
  have h3 : ¬ k + 3 ≤ 2 := by omega
  have h0 : ¬ (0 : ℤ) < -((k + 3 : ℕ) : ℤ) := by omega
  simp only [letter7, Int.natAbs_neg, Int.natAbs_natCast, h3, if_false, Nat.add_sub_cancel, hk,
    if_true, h0]

theorem sim_s7 {j : ℕ} (hj : j < 1206) : Fi24Sim LM7[2 * j]! (s7 j) :=
  ((sim_mLetters fi7_facts.slp).2 j (by rw [W7_size]; exact hj)).1

theorem s7_eq_M7 {j t : ℕ} (hj : 1087 ≤ j) (ht : t ∈ conjTs)
    (hw : W7[j]! = (fi24SevenData.conj[t]!).2.map lt2w) : s7 j = M7 t := by
  rw [s7_eq, hw, M7]
  unfold wordG
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl' : l < 2 * 1087 := conj_letters_lt ht l hl
  have hl2 : l / 2 < 1087 := by omega
  simp only [Function.comp]
  by_cases hev : l % 2 = 0
  · have : lt2w l = ((l / 2 + 3 : ℕ) : ℤ) := by simp [lt2w, hev]
    rw [this, letter7_pos (by omega), s7_prefix hl2]
    simp [pairG, hev]
  · have : lt2w l = -((l / 2 + 3 : ℕ) : ℤ) := by simp [lt2w, hev]
    rw [this, letter7_neg (by omega), s7_prefix hl2]
    simp [pairG, hev]

theorem s7_1087 : s7 1087 = M7 91 :=
  s7_eq_M7 le_rfl (by decide) (by
    have := fi7_facts.e0
    rwa [← W7_get_right (k := 0) (by norm_num)] at this)

theorem s7_1088 : s7 1088 = M7 77 :=
  s7_eq_M7 (by norm_num) (by decide) (by
    have := fi7_facts.e1
    rwa [← W7_get_right (k := 1) (by norm_num)] at this)


theorem Y7_eq : Y7 = s7 66 := (s7_prefix (j := 66) (by norm_num)).symm

theorem C7_eq : C7 = s7 67 := (s7_prefix (j := 67) (by norm_num)).symm

theorem s7_comm {i k : ℕ} (hi : i < 1206) (hk : k < 1206)
    (e : eqRows 781 (mulW LM7[2 * i]! LM7[2 * k]!) (mulW LM7[2 * k]! LM7[2 * i]!) = true) :
    s7 i * s7 k = s7 k * s7 i :=
  sim_eq (sim_mul (sim_s7 hi) (sim_s7 hk)) (sim_mul (sim_s7 hk) (sim_s7 hi)) e

theorem s7_1085_comm : s7 1085 * C7 = C7 * s7 1085 := by
  rw [C7_eq]; exact s7_comm (by norm_num) (by norm_num) fi7_facts.comm85

theorem s7_1086_comm : s7 1086 * C7 = C7 * s7 1086 := by
  rw [C7_eq]; exact s7_comm (by norm_num) (by norm_num) fi7_facts.comm86

theorem s7_1082_comm : s7 1082 * Y7 = Y7 * s7 1082 := by
  rw [Y7_eq]; exact s7_comm (by norm_num) (by norm_num) fi7_facts.comm82

theorem s7_1083_comm : s7 1083 * Y7 = Y7 * s7 1083 := by
  rw [Y7_eq]; exact s7_comm (by norm_num) (by norm_num) fi7_facts.comm83

theorem s7_1084_comm : s7 1084 * Y7 = Y7 * s7 1084 := by
  rw [Y7_eq]; exact s7_comm (by norm_num) (by norm_num) fi7_facts.comm84

theorem s7_1089 : s7 1089 = (s7 1087)⁻¹ * s7 1085 * s7 1087 := by
  rw [s7_eq, show W7[1089]! = (fi7Extra ())[2]! from W7_get_right (k := 2) (by norm_num),
    fi7_facts.e2]
  simp [wordG, letter7, mul_assoc]

theorem s7_1090 : s7 1090 = (s7 1087)⁻¹ * s7 1086 * s7 1087 := by
  rw [s7_eq, show W7[1090]! = (fi7Extra ())[3]! from W7_get_right (k := 3) (by norm_num),
    fi7_facts.e3]
  simp [wordG, letter7, mul_assoc]

theorem s7_1091 : s7 1091 = (s7 1088)⁻¹ * s7 1085 * s7 1088 := by
  rw [s7_eq, show W7[1091]! = (fi7Extra ())[4]! from W7_get_right (k := 4) (by norm_num),
    fi7_facts.e4]
  simp [wordG, letter7, mul_assoc]

theorem s7_1092 : s7 1092 = (s7 1088)⁻¹ * s7 1086 * s7 1088 := by
  rw [s7_eq, show W7[1092]! = (fi7Extra ())[5]! from W7_get_right (k := 5) (by norm_num),
    fi7_facts.e5]
  simp [wordG, letter7, mul_assoc]

theorem s7_1205 : s7 1205 = s7 1084 * (s7 1082 * (s7 1083 * s7 1083)) := by
  rw [s7_eq, show W7[1205]! = (fi7Extra ())[118]! from W7_get_right (k := 118) (by norm_num),
    fi7_facts.e118]
  simp [wordG, letter7]

theorem s7_zero : s7 0 = CFSG.Sporadic.Fi24.a := by
  rw [s7_eq, W7_get_left (by norm_num), fi7_facts.w0]
  simp [wordG, letter7, genG]

theorem s7_one : s7 1 = CFSG.Sporadic.Fi24.b := by
  rw [s7_eq, W7_get_left (by norm_num), fi7_facts.w1]
  simp [wordG, letter7, genG]

@[expose] noncomputable def gens7 : Set CFSG.Sporadic.Fi24.J :=
  {s7 1085, s7 1086, s7 1089, s7 1090, s7 1091, s7 1092}

theorem isGen7_spec {k : ℕ} (h : isGen7 k = true) : k < 1093 ∧ s7 k ∈ gens7 := by
  simp only [isGen7, Bool.or_eq_true, beq_iff_eq] at h
  refine ⟨by omega, ?_⟩
  rcases h with ((((h | h) | h) | h) | h) | h <;> subst h <;> simp [gens7]

theorem s7_mem_closure : ∀ j, 1093 ≤ j → j < 1205 → s7 j ∈ Subgroup.closure gens7 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj1 hj2
    have hr := fi7_facts.rules (j - 1093) (by omega)
    have hjw : 1093 + (j - 1093) = j := by omega
    rw [hjw] at hr
    rw [s7_eq]
    unfold wordG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hz3, hcase⟩ := hr z hz
    unfold letter7
    rw [if_neg (by omega)]
    rcases hcase with hg | ⟨hlo, hhi⟩
    · obtain ⟨hlt, hmem⟩ := isGen7_spec hg
      rw [if_pos (by omega)]
      split_ifs
      · exact Subgroup.subset_closure hmem
      · exact Subgroup.inv_mem _ (Subgroup.subset_closure hmem)
    · rw [if_pos (by omega)]
      have hm := ih _ (by omega) hlo (by omega)
      split_ifs
      · exact hm
      · exact Subgroup.inv_mem _ hm

theorem a_mem_closure : CFSG.Sporadic.Fi24.a ∈ Subgroup.closure gens7 := by
  have h1203 : s7 1203 = s7 0 :=
    sim_eq (sim_s7 (by norm_num)) (sim_s7 (by norm_num)) fi7_facts.wa
  rw [← s7_zero, ← h1203]
  exact s7_mem_closure 1203 (by norm_num) (by norm_num)

theorem b_mem_closure : CFSG.Sporadic.Fi24.b ∈ Subgroup.closure gens7 := by
  have h1204 : s7 1204 = s7 1 :=
    sim_eq (sim_s7 (by norm_num)) (sim_s7 (by norm_num)) fi7_facts.wb
  rw [← s7_one, ← h1204]
  exact s7_mem_closure 1204 (by norm_num) (by norm_num)

theorem fi7_gens_top : Subgroup.closure gens7 = ⊤ := by
  rw [eq_top_iff, ← CFSG.Sporadic.Fi24.closure_ab, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  exacts [a_mem_closure, b_mem_closure]


theorem cube7_not_mem_zpowers {t : ℕ} (ht : t < 343) (ht0 : t / 7 ≠ 0) :
    cube7 t ∉ Subgroup.zpowers C7 := by
  intro h
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
  obtain ⟨-, -, -, -, -, hinj⟩ := fi7_cube
  have hord : orderOf C7 = 7 := orderOf_C7
  have h1 : C7 ^ (n % 7) = C7 ^ n := by
    have := zpow_mod_orderOf C7 n
    rwa [hord, Nat.cast_ofNat] at this
  have hk : 0 ≤ n % 7 := Int.emod_nonneg n (by norm_num)
  have hk7 : n % 7 < 7 := Int.emod_lt_of_pos n (by norm_num)
  obtain ⟨k, hkdef⟩ := Int.eq_ofNat_of_zero_le hk
  have hk7' : k < 7 := by omega
  have h2 : C7 ^ k = cube7 t := by
    rw [← hn, ← h1, hkdef, zpow_natCast]
  have h3 := hinj 0 0 k (t / 49) (t / 7 % 7) (t % 7) (by norm_num) (by norm_num) hk7'
    (by omega) (by omega) (by omega) (by simpa [cube7] using h2)
  omega

theorem sevenLine_cube7 {t : ℕ} (ht : t ∈ conjTs)
    (hc : (fi24SevenData.conj[t]!).1 = 1) :
    SevenLine 7 (cube7 t) (Q7.map (MulAut.conj (M7 t)⁻¹).toMonoidHom) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h := sevenLine_c.conj (M7 t)⁻¹
  have hrel := fi7_conj_rel ht
  have hif : (if (fi24SevenData.conj[t]!).1 == 0 then Y7 else C7) = C7 := by simp [hc]
  rw [hif] at hrel
  have e : (M7 t)⁻¹ * C7 * ((M7 t)⁻¹)⁻¹ = cube7 t := by
    rw [inv_inv]
    calc (M7 t)⁻¹ * C7 * M7 t = (M7 t)⁻¹ * (C7 * M7 t) := by group
      _ = (M7 t)⁻¹ * (M7 t * cube7 t) := by rw [hrel]
      _ = cube7 t := by group
  rwa [e] at h

theorem cube7_eq_conj {t : ℕ} (ht : t ∈ conjTs)
    (hc : (fi24SevenData.conj[t]!).1 = 1) : cube7 t = (M7 t)⁻¹ * C7 * M7 t := by
  have hrel := fi7_conj_rel ht
  have hif : (if (fi24SevenData.conj[t]!).1 == 0 then Y7 else C7) = C7 := by simp [hc]
  rw [hif] at hrel
  calc cube7 t = (M7 t)⁻¹ * (M7 t * cube7 t) := by group
    _ = (M7 t)⁻¹ * (C7 * M7 t) := by rw [hrel]
    _ = (M7 t)⁻¹ * C7 * M7 t := by group

theorem conj_cent {M g c : CFSG.Sporadic.Fi24.J} (hgc : g * c = c * g) :
    (M⁻¹ * g * M) * (M⁻¹ * c * M) = (M⁻¹ * c * M) * (M⁻¹ * g * M) := by
  calc M⁻¹ * g * M * (M⁻¹ * c * M) = M⁻¹ * (g * c) * M := by group
    _ = M⁻¹ * (c * g) * M := by rw [hgc]
    _ = M⁻¹ * c * M * (M⁻¹ * g * M) := by group

theorem cube7_91_good : cube7 91 ∈ Q7 ∧ cube7 91 ∉ Subgroup.zpowers C7 :=
  ⟨cube7_mem 91, cube7_not_mem_zpowers (by norm_num) (by norm_num)⟩

theorem cube7_77_good : cube7 77 ∈ Q7 ∧ cube7 77 ∉ Subgroup.zpowers C7 :=
  ⟨cube7_mem 77, cube7_not_mem_zpowers (by norm_num) (by norm_num)⟩

theorem fi7_gens_good : ∀ g ∈ gens7, g ∈ Subgroup.centralizer ({C7} : Set CFSG.Sporadic.Fi24.J) ∨
    (∃ (w : CFSG.Sporadic.Fi24.J) (F : Subgroup CFSG.Sporadic.Fi24.J), SevenLine 7 w F ∧ w ∈ Q7 ∧ w ∉ Subgroup.zpowers C7 ∧
      g ∈ Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J)) ∨
    (∃ E : Subgroup CFSG.Sporadic.Fi24.J, E ≤ Q7 ∧ IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2 ∧
      ∀ s ∈ E, g * s * g⁻¹ ∈ E) := by
  have hc91 := fi7_facts.c91
  have hc77 := fi7_facts.c77
  intro g hg
  simp only [gens7, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 s7_1085_comm)
  · exact Or.inl (Subgroup.mem_centralizer_singleton_iff.2 s7_1086_comm)
  · refine Or.inr (Or.inl ⟨cube7 91, _, sevenLine_cube7 (by decide) hc91,
      cube7_91_good.1, cube7_91_good.2, ?_⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [s7_1089, s7_1087, cube7_eq_conj (by decide) hc91]
    exact conj_cent s7_1085_comm
  · refine Or.inr (Or.inl ⟨cube7 91, _, sevenLine_cube7 (by decide) hc91,
      cube7_91_good.1, cube7_91_good.2, ?_⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [s7_1090, s7_1087, cube7_eq_conj (by decide) hc91]
    exact conj_cent s7_1086_comm
  · refine Or.inr (Or.inl ⟨cube7 77, _, sevenLine_cube7 (by decide) hc77,
      cube7_77_good.1, cube7_77_good.2, ?_⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [s7_1091, s7_1088, cube7_eq_conj (by decide) hc77]
    exact conj_cent s7_1085_comm
  · refine Or.inr (Or.inl ⟨cube7 77, _, sevenLine_cube7 (by decide) hc77,
      cube7_77_good.1, cube7_77_good.2, ?_⟩)
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rw [s7_1092, s7_1088, cube7_eq_conj (by decide) hc77]
    exact conj_cent s7_1086_comm

theorem fi7_order_four : ∃ u ∈ Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J), orderOf u = 4 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  refine ⟨s7 1205, ?_, ?_⟩
  · rw [s7_1205]
    have h82 : s7 1082 ∈ Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J) :=
      Subgroup.mem_centralizer_singleton_iff.2 s7_1082_comm
    have h83 : s7 1083 ∈ Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J) :=
      Subgroup.mem_centralizer_singleton_iff.2 s7_1083_comm
    have h84 : s7 1084 ∈ Subgroup.centralizer ({Y7} : Set CFSG.Sporadic.Fi24.J) :=
      Subgroup.mem_centralizer_singleton_iff.2 s7_1084_comm
    exact Subgroup.mul_mem _ h84 (Subgroup.mul_mem _ h82 (Subgroup.mul_mem _ h83 h83))
  · have h4 : s7 1205 ^ 4 = 1 :=
      sim_eq (sim_pow 4 (sim_s7 (by norm_num))) sim_idW fi7_facts.pow4
    have h2 : s7 1205 ^ 2 ≠ 1 :=
      sim_ne (sim_pow 2 (sim_s7 (by norm_num))) sim_idW fi7_facts.pow2
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := s7 1205) (by simpa using h2)
      (by simpa using h4)
    simpa using this

end Gen

end CFSG.HardMathSupport.Dickson.I271.Fi7

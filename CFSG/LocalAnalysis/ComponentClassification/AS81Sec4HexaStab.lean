module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaModel

public section

namespace CFSG.ComponentClassification.AS81.Hexa

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.AS81.HeSylow

@[expose] def xorF (v w : Fin 64) : Fin 64 :=
  ⟨v.val ^^^ w.val, Nat.xor_lt_two_pow (n := 6) v.2 w.2⟩

theorem val_xorF (v w : Fin 64) : (xorF v w).val = v.val ^^^ w.val := rfl

theorem xorF_comm (v w : Fin 64) : xorF v w = xorF w v := Fin.ext (Nat.xor_comm _ _)

theorem xorF_assoc (u v w : Fin 64) : xorF (xorF u v) w = xorF u (xorF v w) :=
  Fin.ext (Nat.xor_assoc _ _ _)

theorem xorF_self (v : Fin 64) : xorF v v = 0 := Fin.ext (Nat.xor_self _)

theorem xorF_zero (v : Fin 64) : xorF v 0 = v := Fin.ext (Nat.xor_zero _)

theorem zero_xorF (v : Fin 64) : xorF 0 v = v := Fin.ext (Nat.zero_xor _)

@[expose] def transl (v : Fin 64) : Equiv.Perm (Fin 64) where
  toFun w := xorF w v
  invFun w := xorF w v
  left_inv w := by simp only [xorF_assoc, xorF_self, xorF_zero]
  right_inv w := by simp only [xorF_assoc, xorF_self, xorF_zero]

theorem transl_apply (v w : Fin 64) : transl v w = xorF w v := rfl

theorem transl_xorF (v w : Fin 64) : transl (xorF v w) = transl v * transl w :=
  Equiv.ext fun u => by
    rw [Equiv.Perm.mul_apply, transl_apply, transl_apply, transl_apply, xorF_assoc, xorF_comm w v]

theorem transl_zero : transl 0 = 1 := Equiv.ext fun u => xorF_zero u

theorem transl_injective : Function.Injective transl := fun v w h => by
  have h0 := congrArg (fun t : Equiv.Perm (Fin 64) => t 0) h
  simpa only [transl_apply, zero_xorF] using h0

theorem transl_mul_self (v : Fin 64) : transl v * transl v = 1 := by
  rw [← transl_xorF, xorF_self, transl_zero]

theorem mul_transl_mul_inv {f : Equiv.Perm (Fin 64)} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (v : Fin 64) : f * transl v * f⁻¹ = transl (f v) := Equiv.ext fun u => by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, transl_apply, hf,
    show f (f⁻¹ u) = u from f.apply_symm_apply u, transl_apply]

@[expose] def translSub : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := Set.range transl
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨xorF v w, transl_xorF v w⟩
  one_mem' := ⟨0, transl_zero⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, eq_inv_of_mul_eq_one_left (transl_mul_self v)⟩

@[expose] def translR0 : Subgroup (Equiv.Perm (Fin 64)) where
  carrier := {t | ∃ v : Fin 64, v.val < 4 ∧ transl v = t}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨xorF v w, Nat.xor_lt_two_pow (n := 2) hv hw, transl_xorF v w⟩
  one_mem' := ⟨0, by decide, transl_zero⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, eq_inv_of_mul_eq_one_left (transl_mul_self v)⟩

theorem rep_translA {v : ℕ} (hv : v < 64) : Rep 64 (translA v) (transl ⟨v, hv⟩) := fun x => by
  rw [translA, getElem!_ofFn_nat _ x.2]
  rfl

@[expose] def bitF (i : ℕ) : Fin 64 := Fin.ofNat 64 (2 ^ i)

theorem eq_foldl_bits : ∀ v : Fin 64,
    (List.range 6).foldl (fun a i => if v.val.testBit i then xorF a (bitF i) else a) 0 = v := by
  decide

theorem map_zero_of_add {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) :
    f 0 = 0 := by
  have h := hf 0 0
  rwa [xorF_self, xorF_self] at h

theorem foldl_additive {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (c : ℕ → Bool) (e : ℕ → Fin 64) (L : List ℕ) (acc : Fin 64) :
    f (L.foldl (fun a i => if c i then xorF a (e i) else a) acc) =
      L.foldl (fun a i => if c i then xorF a (f (e i)) else a) (f acc) := by
  induction L generalizing acc with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    split_ifs
    · exact hf _ _
    · rfl

theorem val_foldl (c : ℕ → Bool) (e : ℕ → Fin 64) (L : List ℕ) (acc : Fin 64) :
    (L.foldl (fun a i => if c i then xorF a (e i) else a) acc).val =
      L.foldl (fun a i => if c i then a ^^^ (e i).val else a) acc.val := by
  induction L generalizing acc with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    split_ifs <;> rfl

theorem val_eq_linV {f : Fin 64 → Fin 64} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (x : Fin 64) :
    (f x).val =
      linV [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] x.val := by
  conv_lhs => rw [← eq_foldl_bits x]
  rw [foldl_additive hf, map_zero_of_add hf, val_foldl]
  unfold linV
  refine List.foldl_ext _ _ _ fun a i hi => ?_
  have hi6 : i < 6 := List.mem_range.1 hi
  interval_cases i <;> rfl

theorem rep_linA {f : Equiv.Perm (Fin 64)} (hf : ∀ v w, f (xorF v w) = xorF (f v) (f w)) :
    Rep 64 (linA [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val]) f :=
  fun x => by
    rw [linA, getElem!_ofFn_nat _ x.2]
    exact (val_eq_linV hf x).symm

theorem hexaStabCheck_parts (h : hexaStabCheck = true) :
    hexaTGens = (List.range 6).map (fun i => translA (2 ^ i)) ∧
    hexaR0Gens = [translA 1, translA 2] ∧ stabW (eltsN 64 hexaMGens) hexaStabW = true ∧
    enumCheckN 64 hexaM2Gens 2160 = true ∧ hexaM2Gens.all (inLN 64 (eltsN 64 hexaMGens)) = true ∧
    hexaM2Gens.all (fun a => eqA 64 (powN 64 a 4) (idA 64)) = true ∧ ovalCompN = true := by
  simp only [hexaStabCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

section Sound

variable (hc : hexaCheck = true) (h : hexaStabCheck = true)

include hc h in
theorem hexaT_eq : hexaT = translSub := by
  obtain ⟨hT, -⟩ := hexaCheck_parts hc
  obtain ⟨hTg, -⟩ := hexaStabCheck_parts h
  have hle : hexaT ≤ translSub := grpN_le fun a ha => by
    rw [hTg] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi6 : i < 6 := List.mem_range.1 hi
    have hi' : 2 ^ i < 64 := by
      calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi6
        _ = 64 := by norm_num
    rw [permOfArr_eq_of_rep (rep_translA hi')]
    exact ⟨_, rfl⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_grpN hT]
  have hcard : Nat.card translSub = Nat.card (Set.range transl) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [hcard, Nat.card_range_of_injective transl_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]

include h in
theorem transl_mem_hexaR0_iff (v : Fin 64) : transl v ∈ hexaR0 ↔ v.val < 4 := by
  obtain ⟨-, hR, -⟩ := hexaStabCheck_parts h
  have h1 : transl 1 ∈ hexaR0 := by
    have hm := gen_mem_grpN (n := 64) (gs := hexaR0Gens) (a := translA 1) (by rw [hR]; simp)
    rwa [permOfArr_eq_of_rep (rep_translA (v := 1) (by norm_num))] at hm
  have h2 : transl 2 ∈ hexaR0 := by
    have hm := gen_mem_grpN (n := 64) (gs := hexaR0Gens) (a := translA 2) (by rw [hR]; simp)
    rwa [permOfArr_eq_of_rep (rep_translA (v := 2) (by norm_num))] at hm
  constructor
  · intro hv
    have hle : hexaR0 ≤ translR0 := grpN_le fun a ha => by
      rw [hR] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · rw [permOfArr_eq_of_rep (rep_translA (v := 1) (by norm_num))]
        exact ⟨1, by decide, rfl⟩
      · rw [permOfArr_eq_of_rep (rep_translA (v := 2) (by norm_num))]
        exact ⟨2, by decide, rfl⟩
    obtain ⟨w, hw, hwv⟩ := hle hv
    rwa [← transl_injective hwv]
  · intro hv
    have h3 : transl 3 = transl 1 * transl 2 := by
      rw [← transl_xorF]
      rfl
    obtain ⟨v, hv64⟩ := v
    simp only at hv
    interval_cases v
    · exact transl_zero ▸ one_mem _
    · exact h1
    · exact h2
    · exact h3 ▸ mul_mem h1 h2

include hc h in
theorem mem_hexaM_of_stab {f : Equiv.Perm (Fin 64)}
    (hadd : ∀ v w, f (xorF v w) = xorF (f v) (f w))
    (hpres : ∀ L ∈ hexaOval, ∃ L' ∈ hexaOval, ∀ x : Fin 64, x.val ∈ L → (f x).val ∈ L') :
    f ∈ hexaM := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  obtain ⟨-, -, hst, -⟩ := hexaStabCheck_parts h
  have hrep := rep_linA hadd
  have hf0 := map_zero_of_add hadd
  have hlt : ∀ L ∈ hexaOval, ∀ x ∈ L, x < 64 := by decide
  have hpair : ∀ a b : Fin 64, ∀ L ∈ hexaOval, a.val ∈ L → b.val ∈ L → a ≠ 0 → b ≠ 0 → a ≠ b →
      ((f a).val, (f b).val) ∈ ovalPairs := by
    intro a b L hL ha hb ha0 hb0 hab
    obtain ⟨L', hL', hmap⟩ := hpres L hL
    have hfa : (f a).val ≠ 0 := fun h0 => ha0 (f.injective ((Fin.ext h0).trans hf0.symm))
    have hfb : (f b).val ≠ 0 := fun h0 => hb0 (f.injective ((Fin.ext h0).trans hf0.symm))
    have hfab : (f b).val ≠ (f a).val := fun he => hab (f.injective (Fin.ext he)).symm
    refine List.mem_flatMap.2 ⟨L', hL', List.mem_flatMap.2 ⟨(f a).val, ?_,
      List.mem_map.2 ⟨(f b).val, ?_, rfl⟩⟩⟩
    · exact List.mem_filter.2 ⟨hmap a ha, by simpa using hfa⟩
    · exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hmap b hb, by simpa using hfb⟩,
        by simpa using hfab⟩
  set t := linA [(f 1).val, (f 2).val, (f 4).val, (f 8).val, (f 16).val, (f 32).val] with ht
  have hcand : t ∈ stabCands :=
    List.mem_flatMap.2 ⟨_, hpair 1 2 [0, 1, 2, 3] (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), List.mem_flatMap.2 ⟨_, hpair 4 8 [0, 4, 8, 12] (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), List.mem_map.2 ⟨_,
      hpair 16 32 [0, 16, 32, 48] (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), rfl⟩⟩⟩
  have hop : ovalPresA t = true := by
    refine List.all_eq_true.2 fun L hL => ?_
    obtain ⟨L', hL', hmap⟩ := hpres L hL
    refine List.any_eq_true.2 ⟨L', hL', List.all_eq_true.2 fun x hx => ?_⟩
    have hx64 := hlt L hL x hx
    rw [hrep.apply hx64]
    exact List.contains_iff_mem.2 (hmap ⟨x, hx64⟩ hx)
  have hinj : injA t = true := by
    refine List.all_eq_true.2 fun x hx => List.all_eq_true.2 fun y hy => ?_
    have hx64 := List.mem_range.1 hx
    have hy64 := List.mem_range.1 hy
    rw [hrep.apply hx64, hrep.apply hy64]
    by_cases hxy : x = y
    · simp [hxy]
    · have hne : (f ⟨x, hx64⟩).val ≠ (f ⟨y, hy64⟩).val := fun he =>
        hxy (congrArg Fin.val (f.injective (Fin.ext he)))
      simp [hxy, hne]
  obtain ⟨c, hc, htc⟩ := List.getElem_of_mem hcand
  have hb := List.all_eq_true.1 hst c (List.mem_range.2 hc)
  rw [getElem!_pos stabCands c hc, htc, hop, hinj, Bool.and_true, Bool.not_true,
    Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨hj, he⟩ := hb
  rw [getElem!_pos (eltsN 64 hexaMGens) _ hj] at he
  exact mem_of_inLN hM (List.any_eq_true.2 ⟨_, List.getElem_mem hj, he⟩) hrep

include hc h in
theorem hexaM_le_of_pow_four {H : Subgroup (Equiv.Perm (Fin 64))}
    (hH : ∀ m ∈ hexaM, m ^ 4 = 1 → m ∈ H) : hexaM ≤ H := by
  obtain ⟨-, hM, -⟩ := hexaCheck_parts hc
  obtain ⟨-, -, -, h2, hin, hpow, -⟩ := hexaStabCheck_parts h
  have hle : grpN 64 hexaM2Gens ≤ hexaM := grpN_le_of_all hM h2 hin
  have heq : grpN 64 hexaM2Gens = hexaM :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [card_grpN hM, card_grpN h2])
  rw [← heq]
  refine grpN_le fun a ha => hH _ (hle (gen_mem_grpN ha)) ?_
  exact eq_of_eqA (rep_powN (rep_of_validA (validA_of_mem h2 ha)) 4) rep_idA
    (List.all_eq_true.1 hpow a ha)

theorem offFrame_of {x : ℕ}
    (hx : ∀ p ∈ framePairs, ∀ y ∈ hexaOval[p.1]!, ∀ z ∈ hexaOval[p.2]!, y ^^^ z ≠ x) :
    offFrame x = true := by
  refine List.all_eq_true.2 fun p hp => ?_
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hmem
  obtain ⟨y, hy, hyz⟩ := List.mem_flatMap.1 (List.contains_iff_mem.1 hmem)
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hyz
  exact hx p hp y hy z hz rfl

include h in
theorem oval_comp {a b : ℕ} (ha : a < 64) (hb : b < 64) (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hab : a ≠ b)
    (hfa : offFrame a = true) (hfb : offFrame b = true) (hfab : offFrame (a ^^^ b) = true) :
    (a ∈ hexaOval[4]! ∧ b ∈ hexaOval[4]!) ∨ (a ∈ hexaOval[5]! ∧ b ∈ hexaOval[5]!) := by
  obtain ⟨-, -, -, -, -, -, hcomp⟩ := hexaStabCheck_parts h
  have hc := List.all_eq_true.1 (List.all_eq_true.1 hcomp a (List.mem_range.2 ha)) b
    (List.mem_range.2 hb)
  have h1 : (a != 0) = true := bne_iff_ne.2 ha0
  have h2 : (b != 0) = true := bne_iff_ne.2 hb0
  have h3 : (a != b) = true := bne_iff_ne.2 hab
  simp only [h1, h2, h3, hfa, hfb, hfab, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, Bool.and_eq_true, List.contains_iff_mem] at hc
  exact hc

end Sound

end CFSG.ComponentClassification.AS81.Hexa

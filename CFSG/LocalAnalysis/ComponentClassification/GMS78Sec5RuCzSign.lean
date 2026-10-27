module

public import Certificates.Data.GMS78RuCzPres

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.CosetTable

namespace Sign

variable {G : Type*} [Group G]

@[expose] def evalC (g : ℕ → G) : List ℕ → G
  | [] => 1
  | c :: w => (if c % 2 = 0 then g (c / 2) else (g (c / 2))⁻¹) * evalC g w

@[simp] theorem evalC_nil (g : ℕ → G) : evalC g [] = 1 := rfl

theorem evalC_cons (g : ℕ → G) (c : ℕ) (w : List ℕ) :
    evalC g (c :: w) = (if c % 2 = 0 then g (c / 2) else (g (c / 2))⁻¹) * evalC g w := rfl

theorem evalC_append (g : ℕ → G) (u v : List ℕ) : evalC g (u ++ v) = evalC g u * evalC g v := by
  induction u with
  | nil => simp [evalC]
  | cons c u ih => simp only [List.cons_append, evalC, ih, mul_assoc]

theorem wordOfCodes_single : ∀ c (hc : c < 20),
    wordOfCodes 10 [c] = [(⟨c / 2, by omega⟩, c % 2 == 0)] := by
  decide

theorem ofNat_eq_mk {n : ℕ} (h : n < 10) : Fin.ofNat 10 n = ⟨n, h⟩ :=
  Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt h])

theorem lift_mk_wordOfCodes (x : Fin 10 → G) {w : List ℕ} (hw : ∀ c ∈ w, c < 20) :
    FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 w)) = evalC (fun i => x (Fin.ofNat 10 i)) w := by
  induction w with
  | nil => rfl
  | cons c w ih =>
    have hc : c < 20 := hw c List.mem_cons_self
    have hw' : ∀ c ∈ w, c < 20 := fun c' h => hw c' (List.mem_cons_of_mem _ h)
    have e : wordOfCodes 10 (c :: w) = wordOfCodes 10 [c] ++ wordOfCodes 10 w := by
      simp only [wordOfCodes, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [e, ← FreeGroup.mul_mk, map_mul, ih hw', wordOfCodes_single c hc, evalC,
      ofNat_eq_mk (show c / 2 < 10 by omega)]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one c with h2 | h2
    · simp only [h2, ↓reduceIte]
      exact FreeGroup.lift_apply_of
    · simp only [h2, one_ne_zero, ↓reduceIte]
      change FreeGroup.lift x (FreeGroup.of _)⁻¹ = _
      rw [map_inv, FreeGroup.lift_apply_of]

theorem evalC_mul_central (g c : ℕ → G) (hc : ∀ i, c i ∈ center G) (w : List ℕ) :
    evalC (fun i => g i * c i) w = evalC g w * evalC c w := by
  induction w with
  | nil => simp [evalC]
  | cons a w ih =>
    have hca := mem_center_iff.mp (hc (a / 2))
    have hci : ∀ y : G, y * (c (a / 2))⁻¹ = (c (a / 2))⁻¹ * y := fun y => by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, hca, ← mul_assoc, inv_mul_cancel, one_mul]
    simp only [evalC, ih]
    split_ifs
    · calc g (a / 2) * c (a / 2) * (evalC g w * evalC c w)
          = g (a / 2) * (c (a / 2) * evalC g w) * evalC c w := by group
        _ = g (a / 2) * (evalC g w * c (a / 2)) * evalC c w := by rw [hca]
        _ = g (a / 2) * evalC g w * (c (a / 2) * evalC c w) := by group
    · calc (g (a / 2) * c (a / 2))⁻¹ * (evalC g w * evalC c w)
          = (c (a / 2))⁻¹ * ((g (a / 2))⁻¹ * (evalC g w * evalC c w)) := by group
        _ = (g (a / 2))⁻¹ * (evalC g w * evalC c w) * (c (a / 2))⁻¹ := by rw [hci]
        _ = (g (a / 2))⁻¹ * evalC g w * (evalC c w * (c (a / 2))⁻¹) := by group
        _ = (g (a / 2))⁻¹ * evalC g w * ((c (a / 2))⁻¹ * evalC c w) := by rw [hci]

theorem evalC_twist {t : G} (ht : t * t = 1) (w : List ℕ) :
    evalC (fun i => if i = 9 then t else 1) w = t ^ (w.count 18 + w.count 19) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  induction w with
  | nil => simp [evalC]
  | cons a w ih =>
    rw [evalC, ih]
    by_cases h18 : a = 18
    · subst h18
      rw [List.count_cons_self, List.count_cons_of_ne (by decide : (18 : ℕ) ≠ 19),
        show w.count 18 + 1 + w.count 19 = (w.count 18 + w.count 19) + 1 by omega, pow_succ']
      simp
    · by_cases h19 : a = 19
      · subst h19
        rw [List.count_cons_self, List.count_cons_of_ne (by decide : (19 : ℕ) ≠ 18),
          show w.count 18 + (w.count 19 + 1) = (w.count 18 + w.count 19) + 1 by omega, pow_succ']
        simp [hti]
      · have h9 : a / 2 ≠ 9 := by omega
        rw [List.count_cons_of_ne h18, List.count_cons_of_ne h19]
        split_ifs <;> simp_all

theorem evalC_congr {g₁ g₂ : ℕ → G} {w : List ℕ} (h : ∀ c ∈ w, g₁ (c / 2) = g₂ (c / 2)) :
    evalC g₁ w = evalC g₂ w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [evalC, h a List.mem_cons_self,
      ih fun c hc => h c (List.mem_cons_of_mem _ hc)]

theorem ite_mem_center {t : G} (ht : t ∈ center G) (i : ℕ) :
    (if i = 9 then t else 1) ∈ center G := by
  split_ifs
  exacts [ht, one_mem _]

theorem codes_lt : ∀ c ∈ czP12Codes ++ czHCodes ++ czEps1Codes ++ czEps2Codes ++ czEps3Codes,
    ∀ d ∈ c, d < 20 := by decide +kernel

theorem count_p12 : ∀ c ∈ czP12Codes, c.count 18 + c.count 19 = 0 := by decide +kernel

@[expose] def rV : List ℕ := czHCodes.getD 7 []

@[expose] def rH2 : List ℕ := czHCodes.getD 8 []

@[expose] def rHW : List ℕ := czHCodes.getD 9 []

theorem czHCodes_eq : czHCodes = czHCodes.take 7 ++ [rV, rH2, rHW] := by decide +kernel

theorem czEps1Codes_eq :
    czEps1Codes = czHCodes.take 7 ++ [rV.take 3 ++ [1, 1] ++ rV.drop 3, rH2, rHW] := by
  decide +kernel

theorem czEps2Codes_eq : czEps2Codes = czHCodes.take 7 ++ [rV, [18, 18, 1], rHW] := by
  decide +kernel

theorem czEps3Codes_eq : czEps3Codes =
    czHCodes.take 7 ++ [rV.take 3 ++ [1, 1] ++ rV.drop 3, [18, 18, 1], rHW] := by
  decide +kernel

theorem rH2_eq : rH2 = [18, 18, 0] := by decide +kernel

theorem counts_h : (∀ c ∈ czHCodes.take 7, c.count 18 + c.count 19 = 2) ∧
    rV.count 18 + rV.count 19 = 2 ∧ rH2.count 18 + rH2.count 19 = 2 ∧
    rHW.count 18 + rHW.count 19 = 3 := by decide +kernel

end Sign

section Signs

open Sign

variable {H : Type*} [Group H]

theorem czSign_of
    (hb1 : ∀ y : Fin 10 → H, (∀ r ∈ czEps1Rels, FreeGroup.lift y (FreeGroup.mk r) = 1) →
      closure (Set.range y) = ⊤ → Nat.card H ≤ 122880)
    (hb2 : ∀ y : Fin 10 → H, (∀ r ∈ czEps2Rels, FreeGroup.lift y (FreeGroup.mk r) = 1) →
      closure (Set.range y) = ⊤ → Nat.card H ≤ 122880)
    (hb3 : ∀ y : Fin 10 → H, (∀ r ∈ czEps3Rels, FreeGroup.lift y (FreeGroup.mk r) = 1) →
      closure (Set.range y) = ⊤ → Nat.card H ≤ 122880)
    (hH : Nat.card H = 245760) (x : Fin 10 → H) (hz : x 0 ^ 2 ∈ center H)
    (hP12 : ∀ r ∈ czP12Codes, FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 r)) = 1)
    (hH7 : ∀ r ∈ czHCodes.take 7, FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 r)) = 1)
    (hsgn : ∀ r ∈ czHCodes.drop 7, FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 r)) = 1 ∨
      FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 r)) = x 0 ^ 2)
    (hgen : closure (Set.range x) = ⊤) :
    ∃ y : Fin 10 → H, (∀ i : Fin 10, i.val < 9 → y i = x i) ∧
      (y 9 = x 9 ∨ y 9 = x 9 * x 0 ^ 2) ∧ closure (Set.range y) = ⊤ ∧
      ∀ r ∈ czRels, FreeGroup.lift y (FreeGroup.mk r) = 1 := by
  set z := x 0 ^ 2 with hzdef
  have hlt := codes_lt
  have hP : ∀ c ∈ czP12Codes, ∀ d ∈ c, d < 20 := fun c hc => hlt c (by simp [hc])
  have hHc : ∀ c ∈ czHCodes, ∀ d ∈ c, d < 20 := fun c hc => hlt c (by simp [hc])
  obtain ⟨g, hg⟩ : ∃ g : ℕ → H, g = fun i => x (Fin.ofNat 10 i) := ⟨_, rfl⟩
  have hxv : ∀ w : List ℕ, (∀ d ∈ w, d < 20) →
      FreeGroup.lift x (FreeGroup.mk (wordOfCodes 10 w)) = evalC g w := fun w hw => by
    rw [hg]; exact lift_mk_wordOfCodes x hw
  have hg0 : g 0 = x 0 := by rw [hg]; rfl
  have hz2 : z * z = 1 := by
    have hA := hP12 [2, 2, 0, 0] (by decide +kernel)
    have hB := hP12 [2, 1, 1, 2] (by decide +kernel)
    rw [hxv _ (by decide)] at hA hB
    change g 1 * (g 1 * (g 0 * (g 0 * 1))) = 1 at hA
    change g 1 * ((g 0)⁻¹ * ((g 0)⁻¹ * (g 1 * 1))) = 1 at hB
    have h3 : g 0 * g 0 = (g 0)⁻¹ * (g 0)⁻¹ := by
      calc g 0 * g 0 = (g 1)⁻¹ * (g 1)⁻¹ * (g 1 * (g 1 * (g 0 * (g 0 * 1)))) := by group
        _ = (g 1)⁻¹ * (g 1 * ((g 0)⁻¹ * ((g 0)⁻¹ * (g 1 * 1)))) * (g 1)⁻¹ := by
          rw [hA, hB]; group
        _ = (g 0)⁻¹ * (g 0)⁻¹ := by group
    calc z * z = g 0 * g 0 * (g 0 * g 0) := by rw [hzdef, ← hg0, pow_two]
      _ = (g 0)⁻¹ * (g 0)⁻¹ * (g 0 * g 0) := by rw [← h3]
      _ = 1 := by group
  have hlV : ∀ d ∈ rV, d < 20 := hHc rV (by decide +kernel)
  have hlH2 : ∀ d ∈ rH2, d < 20 := hHc rH2 (by decide +kernel)
  have hlHW : ∀ d ∈ rHW, d < 20 := hHc rHW (by decide +kernel)
  have e7 : evalC g rV = 1 ∨ evalC g rV = z := by
    simpa only [hxv rV hlV] using hsgn rV (by decide +kernel)
  have e8 : evalC g rH2 = 1 ∨ evalC g rH2 = z := by
    simpa only [hxv rH2 hlH2] using hsgn rH2 (by decide +kernel)
  have e9 : evalC g rHW = 1 ∨ evalC g rHW = z := by
    simpa only [hxv rHW hlHW] using hsgn rHW (by decide +kernel)
  obtain ⟨t, ht2, htc, ht1, ht9⟩ : ∃ t : H, t * t = 1 ∧ t ∈ center H ∧ (t = 1 ∨ t = z) ∧
      evalC g rHW * t = 1 := by
    rcases e9 with h | h
    · exact ⟨1, mul_one 1, one_mem _, Or.inl rfl, by rw [h, mul_one]⟩
    · exact ⟨z, hz2, hz, Or.inr rfl, by rw [h, hz2]⟩
  obtain ⟨y, hy9, hyi⟩ : ∃ y : Fin 10 → H, y 9 = x 9 * t ∧ ∀ i, i ≠ 9 → y i = x i :=
    ⟨fun i => if i = 9 then x 9 * t else x i, ite_eq_left rfl, fun i hi => ite_eq_right hi⟩
  obtain ⟨gy, hgyd⟩ : ∃ gy : ℕ → H, gy = fun i => y (Fin.ofNat 10 i) := ⟨_, rfl⟩
  have hyv : ∀ w : List ℕ, (∀ d ∈ w, d < 20) →
      FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 w)) = evalC gy w := fun w hw => by
    rw [hgyd]; exact lift_mk_wordOfCodes y hw
  have hgy0 : gy 0 = x 0 := by rw [hgyd]; exact hyi _ (by decide)
  have hgy : ∀ w : List ℕ, (∀ d ∈ w, d < 20) →
      evalC gy w = evalC g w * t ^ (w.count 18 + w.count 19) := by
    intro w hw
    rw [← evalC_twist ht2, ← evalC_mul_central g _ (ite_mem_center htc)]
    refine evalC_congr fun c hc => ?_
    have hc' : c / 2 < 10 := by have := hw c hc; omega
    simp only [hgyd, hg, ofNat_eq_mk hc']
    by_cases h9 : c / 2 = 9
    · have h9' : (⟨c / 2, hc'⟩ : Fin 10) = 9 := Fin.ext h9
      rw [ite_eq_left h9, h9', hy9]
    · have h9' : (⟨c / 2, hc'⟩ : Fin 10) ≠ 9 := fun h => h9 (congrArg Fin.val h)
      rw [ite_eq_right h9, mul_one, hyi _ h9']
  have hyP : ∀ r ∈ czP12Codes, FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 r)) = 1 := by
    intro r hr
    rw [hyv r (hP r hr), hgy r (hP r hr), count_p12 r hr, pow_zero, mul_one, ← hxv r (hP r hr),
      hP12 r hr]
  have hy7 : ∀ r ∈ czHCodes.take 7, FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 r)) = 1 := by
    intro r hr
    have hr' := hHc r (List.mem_of_mem_take hr)
    rw [hyv r hr', hgy r hr', counts_h.1 r hr, ← hxv r hr', hH7 r hr, one_mul, pow_two, ht2]
  have hyV : evalC gy rV = evalC g rV := by
    rw [hgy rV hlV, counts_h.2.1, pow_two, ht2, mul_one]
  have hyH2 : evalC gy rH2 = evalC g rH2 := by
    rw [hgy rH2 hlH2, counts_h.2.2.1, pow_two, ht2, mul_one]
  have hyHW : FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 rHW)) = 1 := by
    rw [hyv rHW hlHW, hgy rHW hlHW, counts_h.2.2.2, pow_succ, pow_two, ht2, one_mul, ht9]
  have hV : evalC g rV = 1 → FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 rV)) = 1 :=
    fun h => by rw [hyv rV hlV, hyV, h]
  have hH2 : evalC g rH2 = 1 → FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 rH2)) = 1 :=
    fun h => by rw [hyv rH2 hlH2, hyH2, h]
  have hT7 : evalC g rV = z →
      FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 (rV.take 3 ++ [1, 1] ++ rV.drop 3))) = 1 := by
    intro h7
    rw [hyv _ (by decide +kernel), evalC_append, evalC_append]
    have h11 : evalC gy [1, 1] = z⁻¹ := by
      change (gy 0)⁻¹ * ((gy 0)⁻¹ * 1) = z⁻¹
      rw [hgy0, hzdef]; group
    rw [h11, mul_assoc, ← (Subgroup.mem_center_iff.mp (inv_mem hz) _), ← mul_assoc,
      ← evalC_append, List.take_append_drop, hyV, h7, mul_inv_cancel]
  have hT8 : evalC g rH2 = z →
      FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 [18, 18, 1])) = 1 := by
    intro h8
    have e : evalC gy [18, 18, 0] = z := by rw [← rH2_eq, hyH2, h8]
    change gy 9 * (gy 9 * (gy 0 * 1)) = z at e
    rw [hyv _ (by decide)]
    change gy 9 * (gy 9 * ((gy 0)⁻¹ * 1)) = 1
    rw [hgy0] at e ⊢
    calc gy 9 * (gy 9 * ((x 0)⁻¹ * 1)) = gy 9 * (gy 9 * (x 0 * 1)) * (x 0)⁻¹ * (x 0)⁻¹ := by
          group
      _ = 1 := by rw [e, hzdef]; group
  have hgeny : closure (Set.range y) = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    by_cases h9 : i = 9
    · subst h9
      have hx9 : x 9 = y 9 * t⁻¹ := by rw [hy9, mul_inv_cancel_right]
      rw [hx9]
      refine mul_mem (Subgroup.subset_closure (Set.mem_range_self 9)) (inv_mem ?_)
      rcases ht1 with h | h
      · rw [h]; exact one_mem _
      · rw [h, hzdef, ← hyi 0 (by decide)]
        exact pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) 2
    · rw [← hyi i h9]
      exact Subgroup.subset_closure (Set.mem_range_self i)
  have hEps : ∀ L : List (List ℕ),
      (∀ c ∈ L, FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 c)) = 1) →
      ∀ r ∈ (czP12Codes ++ L).map (wordOfCodes 10), FreeGroup.lift y (FreeGroup.mk r) = 1 := by
    intro L hL r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    rcases List.mem_append.mp hc with hc | hc
    · exact hyP c hc
    · exact hL c hc
  have hcases : ∀ a b : List ℕ, FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 a)) = 1 →
      FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 b)) = 1 →
      ∀ c ∈ czHCodes.take 7 ++ [a, b, rHW],
        FreeGroup.lift y (FreeGroup.mk (wordOfCodes 10 c)) = 1 := by
    intro a b ha hb c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl | rfl
    · exact hy7 c hc
    · exact ha
    · exact hb
    · exact hyHW
  have hno : ¬ Nat.card H ≤ 122880 := by omega
  refine ⟨y, fun i hi => hyi i fun h => by subst h; exact absurd hi (by decide), ?_, hgeny, ?_⟩
  · rcases ht1 with h | h
    · left; rw [hy9, h, mul_one]
    · right; rw [hy9, h]
  · rcases e7 with h7 | h7 <;> rcases e8 with h8 | h8
    · exact hEps czHCodes (by rw [czHCodes_eq]; exact hcases _ _ (hV h7) (hH2 h8))
    · refine absurd (hb2 y (hEps czEps2Codes ?_) hgeny) hno
      rw [czEps2Codes_eq]; exact hcases _ _ (hV h7) (hT8 h8)
    · refine absurd (hb1 y (hEps czEps1Codes ?_) hgeny) hno
      rw [czEps1Codes_eq]; exact hcases _ _ (hT7 h7) (hH2 h8)
    · refine absurd (hb3 y (hEps czEps3Codes ?_) hgeny) hno
      rw [czEps3Codes_eq]; exact hcases _ _ (hT7 h7) (hT8 h8)

end Signs

end CFSG.ComponentClassification.GMS78.RuCz

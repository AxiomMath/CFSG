module

public import CFSG.LocalAnalysis.StandardType.GGTWLowCheck
public import CFSG.LocalAnalysis.StandardType.GGTWLowPZA
public import CFSG.Certificates.Kernel.TWDKSound
public import CFSG.Certificates.Kernel.TWLK6Sound
public import CFSG.Certificates.Kernel.TWLKHKSound
public import Certificates.Data.Kernel.TWLKPZ

public section

namespace CFSG.StandardType.TWLK

open Certificates.TWLK Certificates.DepASmall Certificates.TwoDepSmall
open Certificates.TwoDepSmallLow CFSG.StandardType CFSG.StandardType.TWDK

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ}

theorem twlk_all2_mem {α β : Type} (t : α → β → Bool) (cs : List α) :
    ∀ is : List β, kAll2 t cs is = true → ∀ c ∈ cs, ∃ i, t c i = true := by
  induction cs with
  | nil => intro _ _ c hc; simp at hc
  | cons c cs ih =>
    intro is h c' hc'
    cases is with
    | nil => simp [kAll2] at h
    | cons i is =>
      simp only [kAll2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨i, h.1⟩
      · exact ih is h.2 c' hc'

theorem twlk_getD_map_range {α : Type} (f : ℕ → α) (d : α) {n c : ℕ} (hc : c < n) :
    ((List.range n).map f).getD c d = f c := by
  rw [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

theorem twlk_decode_lt (hp : 0 < p) : ∀ (n k : ℕ), ∀ x ∈ ggTWNDecode p n k, x < p
  | 0, _, x, hx => by simp [ggTWNDecode] at hx
  | n + 1, k, x, hx => by
    simp only [ggTWNDecode, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ hp
    · exact twlk_decode_lt hp n (k / p) x hx

theorem twlk_list_eq {n : ℕ} {l1 l2 : List ℕ} (h1 : l1.length = n) (h2 : l2.length = n)
    (hb1 : ∀ x ∈ l1, x < p) (hb2 : ∀ x ∈ l2, x < p)
    (h : ∀ j < n, ((l1.getD j 0 : ℕ) : ZMod p) = ((l2.getD j 0 : ℕ) : ZMod p)) : l1 = l2 := by
  apply List.ext_getElem (by omega)
  intro j hj1 hj2
  have hj := h j (by omega)
  rw [List.getD_eq_getElem _ _ hj1, List.getD_eq_getElem _ _ hj2] at hj
  exact twNat_eq (hb1 _ (List.getElem_mem hj1)) (hb2 _ (List.getElem_mem hj2)) hj

theorem twlk_getD_lt {l : List ℕ} (hb : ∀ x ∈ l, x < p) (hp : 0 < p) (j : ℕ) : l.getD j 0 < p := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ hj]; exact hb _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hp

theorem solH_props [Fact p.Prime] {pos : ℕ} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWNSolH p N pos tgt) :
    l.length = N - 1 ∧ (∀ x ∈ l, x < p) ∧ kOkH p N pos tgt l = true := by
  unfold ggTWNSolH at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, -, hfk⟩ := hl
  split at hfk
  · rename_i htest
    obtain rfl := Option.some.inj hfk
    refine ⟨ggTWNDecode_length _ _ _, twlk_decode_lt (Fact.out : p.Prime).pos _ _, ?_⟩
    unfold kOkH
    rw [List.all_eq_true] at htest ⊢
    intro c hc
    have := htest c hc
    rwa [twlk_getD_map_range _ _ (List.mem_range.mp hc)] at this
  · cases hfk

theorem solA_props [Fact p.Prime] {pos : ℕ} {tgt : ℕ → ℕ} {l : List ℕ}
    (hl : l ∈ ggTWNSolA p N pos tgt) :
    l.length = N - 1 ∧ (∀ x ∈ l, x < p) ∧ kOkA p N pos tgt l = true := by
  unfold ggTWNSolA at hl
  simp only [List.mem_filterMap, List.mem_range] at hl
  obtain ⟨k, -, hfk⟩ := hl
  split at hfk
  · rename_i htest
    obtain rfl := Option.some.inj hfk
    refine ⟨ggTWNDecode_length _ _ _, twlk_decode_lt (Fact.out : p.Prime).pos _ _, ?_⟩
    unfold kOkA
    rw [List.all_eq_true] at htest ⊢
    intro c hc
    have := htest c hc
    rwa [twlk_getD_map_range _ _ (List.mem_range.mp hc)] at this
  · cases hfk

theorem twlk_sum_ite (n k : ℕ) (hk : k < n) (g : Fin n → ZMod p) :
    ∑ j : Fin n, (if j.val = k then g j else 0) = g ⟨k, hk⟩ := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro hbk
    exact hb (Fin.ext hbk)
  · simp

theorem twlk_dotA (c : Fin (N - 1)) (hc : c.val + 3 ≤ N) (v : GGTWE p N) :
    ggTWdot (ggTWα p N c) v =
      (if 1 ≤ c.val then 2 * vAt (N := N - 1) v (c.val - 1) else 0) -
        (if 2 ≤ c.val then vAt (N := N - 1) v (c.val - 2) else 0) - vAt (N := N - 1) v c.val := by
  have hsplit : ∀ j : Fin (N - 1), ggTWα p N c j * v j =
      (if 1 ≤ c.val then (if j.val = c.val - 1 then 2 * v j else 0) else 0) -
        (if 2 ≤ c.val then (if j.val = c.val - 2 then v j else 0) else 0) -
          (if j.val = c.val then v j else 0) := by
    intro j
    have := j.isLt
    simp only [ggTWα]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [ggTWdot, ggDepAdot, Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, twlk_sum_ite _ _ (by omega)]
  by_cases h1 : 1 ≤ c.val <;> by_cases h2 : 2 ≤ c.val <;>
    simp only [h1, h2, if_true, if_false, Finset.sum_const_zero] <;>
    first
    | (rw [twlk_sum_ite _ _ (by omega), twlk_sum_ite _ _ (by omega), vAt_lt _ (by omega),
        vAt_lt _ (by omega), vAt_lt _ (by omega)])
    | (rw [twlk_sum_ite _ _ (by omega), vAt_lt _ (by omega), vAt_lt _ (by omega)])
    | (exfalso; omega)
    | (rw [vAt_lt _ (by omega)])

theorem twlk_dotH (c : Fin (N - 1)) (hc : 1 ≤ c.val) (v : GGTWE p N) :
    ggTWdot v (ggTWh p N c) = vAt (N := N - 1) v (c.val - 1) := by
  have hsplit : ∀ j : Fin (N - 1), v j * ggTWh p N c j = if j.val = c.val - 1 then v j else 0 := by
    intro j
    have := j.isLt
    have := c.isLt
    simp only [ggTWh]
    split_ifs <;> first | (exfalso; omega) | ring
  rw [ggTWdot, ggDepAdot, Finset.sum_congr rfl (fun j _ => hsplit j),
    twlk_sum_ite _ _ (by omega), vAt_lt _ (by omega)]

theorem twlk_vAt_toZ (l : List ℕ) {k : ℕ} (hk : k < N - 1) :
    vAt (N := N - 1) (ggTWNToZ p N l) k = ((l.getD k 0 : ℕ) : ZMod p) := by
  rw [vAt_lt _ hk]; rfl

theorem kChainH_length (tgt : ℕ → ℕ) : ∀ n c a b, (kChainH p tgt n c a b).length = n
  | 0, _, _, _ => rfl
  | n + 1, c, a, b => by simp [kChainH, kChainH_length tgt n]

theorem kChainH_lt [Fact p.Prime] (tgt : ℕ → ℕ) : ∀ n c a b, ∀ x ∈ kChainH p tgt n c a b, x < p
  | 0, _, _, _, x, hx => by simp [kChainH] at hx
  | n + 1, c, a, b, x, hx => by
    simp only [kChainH, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (Fact.out : p.Prime).pos
    · exact kChainH_lt tgt n _ _ _ x hx

theorem twlk_cast_step [Fact p.Prime] (a b k : ℕ) :
    (((2 * b + (p - a % p) + (p - k % p)) % p : ℕ) : ZMod p) =
      2 * (b : ZMod p) - (a : ZMod p) - (k : ZMod p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_add, Nat.cast_mul,
    Nat.cast_sub (Nat.mod_lt a hp).le, Nat.cast_sub (Nat.mod_lt k hp).le, ZMod.natCast_self,
    ZMod.natCast_mod, ZMod.natCast_mod]
  push_cast
  ring

theorem kChainH_cast [Fact p.Prime] (tgt : ℕ → ℕ) (g : ℕ → ZMod p) :
    ∀ (n c a b o : ℕ), (a : ZMod p) = g o → (b : ZMod p) = g (o + 1) →
      (∀ i < n, g (o + i + 2) = 2 * g (o + i + 1) - g (o + i) - (tgt (c + i) : ZMod p)) →
      ∀ i < n, (((kChainH p tgt n c a b).getD i 0 : ℕ) : ZMod p) = g (o + i + 2)
  | 0, _, _, _, _, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, c, a, b, o, ha, hb, hrec, i, hi => by
    have h0 : (((2 * b + (p - a % p) + (p - tgt c % p)) % p : ℕ) : ZMod p) = g (o + 2) := by
      rw [twlk_cast_step, ha, hb]
      have := hrec 0 (by omega)
      simpa using this.symm
    simp only [kChainH]
    cases i with
    | zero => simpa using h0
    | succ i =>
      rw [List.getD_cons_succ]
      have := kChainH_cast tgt g n (c + 1) b _ (o + 1) hb h0 (fun i' hi' => by
        have h := hrec (i' + 1) (by omega)
        rw [show o + (i' + 1) + 2 = o + 1 + i' + 2 by omega,
          show o + (i' + 1) + 1 = o + 1 + i' + 1 by omega,
          show o + (i' + 1) = o + 1 + i' by omega, show c + (i' + 1) = c + 1 + i' by omega] at h
        exact h) i (by omega)
      rw [this]
      congr 1
      omega

theorem kSolH_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (tgt : ℕ → ℕ) {l : List ℕ}
    (hl : l ∈ ggTWNSolH p N (ggTWPosNat pos) tgt) : l ∈ kSolH p N (ggTWPosNat pos) tgt := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hlen, hlt, hok⟩ := solH_props hl
  obtain ⟨-, hv⟩ := ggTWNSolH_sound hl
  refine List.mem_filter.mpr ⟨?_, hok⟩
  set F : ℕ → ZMod p := fun j => ((l.getD j 0 : ℕ) : ZMod p) with hF
  have hdot : ∀ c (hc : c + 3 ≤ N), ggTWInJ N pos c →
      (if 1 ≤ c then 2 * F (c - 1) else 0) - (if 2 ≤ c then F (c - 2) else 0) - F c =
        (tgt c : ZMod p) := by
    intro c hc hJ
    have h := hv ⟨c, by omega⟩ hJ
    rw [twlk_dotA ⟨c, by omega⟩ hc, twlk_vAt_toZ l (by omega)] at h
    by_cases h1 : 1 ≤ c <;> by_cases h2 : 2 ≤ c <;>
      simp only [h1, h2, if_true, if_false] at h ⊢ <;>
      first
      | (rw [twlk_vAt_toZ l (by omega), twlk_vAt_toZ l (by omega)] at h; exact h)
      | (rw [twlk_vAt_toZ l (by omega)] at h; exact h)
      | exact h
      | (exfalso; omega)
  set g : ℕ → ZMod p := fun k => if k = 0 then 0 else F (k - 1) with hg
  cases pos with
  | ends =>
    have hrec : ∀ i < N - 3, g (0 + i + 2) = 2 * g (0 + i + 1) - g (0 + i) -
        (tgt (1 + i) : ZMod p) := by
      intro i hi
      have h := hdot (i + 1) (by omega) (by simp only [ggTWInJ]; omega)
      simp only [hg, show 0 + i + 2 = i + 2 by omega, show 0 + i + 1 = i + 1 by omega,
        show 1 + i = i + 1 by omega, zero_add, Nat.add_sub_cancel, show i + 2 - 1 = i + 1 by omega,
        show (i + 2 = 0) = False by simp, show (i + 1 = 0) = False by simp, if_false,
        show 1 ≤ i + 1 by omega, if_true] at h ⊢
      by_cases hi0 : i = 0
      · subst hi0
        simp only [if_true, show ¬ (2 ≤ 0 + 1) by omega, if_false] at h ⊢
        linear_combination -h
      · simp only [hi0, if_false, show 2 ≤ i + 1 by omega, if_true,
          show i + 1 - 2 = i - 1 by omega] at h ⊢
        linear_combination -h
    have hch := kChainH_cast tgt g (N - 3) 1 0 (l.getD 0 0) 0 (by simp [hg])
      (by simp [hg, hF]) hrec
    have hcand : l = l.getD 0 0 :: (kChainH p tgt (N - 3) 1 0 (l.getD 0 0) ++ [l.getD (N - 2) 0]) := by
      refine twlk_list_eq (n := N - 1) hlen ?_ hlt ?_ ?_
      · simp [kChainH_length]; omega
      · intro x hx
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl
        · exact twlk_getD_lt hlt hp 0
        · exact kChainH_lt tgt _ _ _ _ x hx
        · exact twlk_getD_lt hlt hp _
      · intro j hj
        rcases (by omega : j = 0 ∨ (1 ≤ j ∧ j ≤ N - 3) ∨ j = N - 2) with rfl | ⟨h1, h2⟩ | rfl
        · rfl
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [kChainH_length]; omega),
            hch i (by omega)]
          simp [hg, hF]
        · rw [show N - 2 = (N - 3) + 1 by omega, List.getD_cons_succ,
            List.getD_append_right _ _ _ _ (by rw [kChainH_length]), kChainH_length]
          simp
    rw [hcand]
    simp only [kCandH, ggTWPosNat, if_true, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨_, twlk_getD_lt hlt hp 0, _, twlk_getD_lt hlt hp _, rfl⟩
  | adj =>
    have h00 := hdot 0 (by omega) (by simp only [ggTWInJ]; omega)
    simp only [show ¬ (1 ≤ 0) by omega, show ¬ (2 ≤ 0) by omega, if_false, zero_sub,
      sub_zero] at h00
    set v0 := (p - tgt 0 % p) % p with hv0
    have hv0F : (v0 : ZMod p) = F 0 := by
      rw [hv0, twCast_neg]; linear_combination h00
    have hrec : ∀ i < N - 4, g (0 + i + 2) = 2 * g (0 + i + 1) - g (0 + i) -
        (tgt (1 + i) : ZMod p) := by
      intro i hi
      have h := hdot (i + 1) (by omega) (by simp only [ggTWInJ]; omega)
      simp only [hg, show 0 + i + 2 = i + 2 by omega, show 0 + i + 1 = i + 1 by omega,
        show 1 + i = i + 1 by omega, zero_add, Nat.add_sub_cancel, show i + 2 - 1 = i + 1 by omega,
        show (i + 2 = 0) = False by simp, show (i + 1 = 0) = False by simp, if_false,
        show 1 ≤ i + 1 by omega, if_true] at h ⊢
      by_cases hi0 : i = 0
      · subst hi0
        simp only [if_true, show ¬ (2 ≤ 0 + 1) by omega, if_false] at h ⊢
        linear_combination -h
      · simp only [hi0, if_false, show 2 ≤ i + 1 by omega, if_true,
          show i + 1 - 2 = i - 1 by omega] at h ⊢
        linear_combination -h
    have hch := kChainH_cast tgt g (N - 4) 1 0 v0 0 (by simp [hg]) (by simp [hg, hv0F]) hrec
    have hcand : l = v0 :: (kChainH p tgt (N - 4) 1 0 v0 ++
        [l.getD (N - 3) 0, l.getD (N - 2) 0]) := by
      refine twlk_list_eq (n := N - 1) hlen ?_ hlt ?_ ?_
      · simp [kChainH_length]; omega
      · intro x hx
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | hx | rfl | rfl
        · exact Nat.mod_lt _ hp
        · exact kChainH_lt tgt _ _ _ _ x hx
        · exact twlk_getD_lt hlt hp _
        · exact twlk_getD_lt hlt hp _
      · intro j hj
        rcases (by omega : j = 0 ∨ (1 ≤ j ∧ j ≤ N - 4) ∨ j = N - 3 ∨ j = N - 2) with
          rfl | ⟨h1, h2⟩ | rfl | rfl
        · exact hv0F.symm
        · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          rw [List.getD_cons_succ, List.getD_append _ _ _ _ (by rw [kChainH_length]; omega),
            hch i (by omega)]
          simp [hg, hF]
        · rw [show N - 3 = (N - 4) + 1 by omega, List.getD_cons_succ,
            List.getD_append_right _ _ _ _ (by rw [kChainH_length]), kChainH_length]
          simp [show N - 4 + 1 = N - 3 by omega]
        · rw [show N - 2 = (N - 4) + 1 + 1 by omega, List.getD_cons_succ,
            List.getD_append_right _ _ _ _ (by rw [kChainH_length]; omega), kChainH_length]
          simp [show N - 4 + 1 + 1 = N - 2 by omega]
    rw [hcand]
    simp only [kCandH, ggTWPosNat, List.mem_flatMap, List.mem_map, List.mem_range,
      show ¬ ((1 : ℕ) = 0) by omega, if_false]
    exact ⟨_, twlk_getD_lt hlt hp _, _, twlk_getD_lt hlt hp _, rfl⟩

theorem kSolA_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (tgt : ℕ → ℕ) {l : List ℕ}
    (hl : l ∈ ggTWNSolA p N (ggTWPosNat pos) tgt) : l ∈ kSolA p N (ggTWPosNat pos) tgt := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨hlen, hlt, hok⟩ := solA_props hl
  obtain ⟨-, hv⟩ := ggTWNSolA_sound hl
  refine List.mem_filter.mpr ⟨?_, hok⟩
  have hfix : ∀ j, ggTWInJ N pos (j + 1) →
      (((tgt (j + 1) % p : ℕ)) : ZMod p) = ((l.getD j 0 : ℕ) : ZMod p) := by
    intro j hJ
    have hj1 : j + 1 < N - 1 := by cases pos <;> simp only [ggTWInJ] at hJ <;> omega
    have h := hv ⟨j + 1, hj1⟩ hJ
    rw [twlk_dotH ⟨j + 1, hj1⟩ (by simp), twlk_vAt_toZ l (by simp; omega)] at h
    rw [ZMod.natCast_mod, ← h]
    simp
  cases pos with
  | ends =>
    have hcand : l = (List.range (N - 3)).map (fun j => tgt (j + 1) % p) ++
        [l.getD (N - 3) 0, l.getD (N - 2) 0] := by
      refine twlk_list_eq (n := N - 1) hlen ?_ hlt ?_ ?_
      · simp; omega
      · intro x hx
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ⟨j, -, rfl⟩ | rfl | rfl
        · exact Nat.mod_lt _ hp
        · exact twlk_getD_lt hlt hp _
        · exact twlk_getD_lt hlt hp _
      · intro j hj
        rcases (by omega : j < N - 3 ∨ j = N - 3 ∨ j = N - 2) with h1 | rfl | rfl
        · rw [List.getD_append _ _ _ _ (by simpa using h1), twlk_getD_map_range _ _ h1]
          exact (hfix j (by simp only [ggTWInJ]; omega)).symm
        · rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp [show N - 2 - (N - 3) = 1 by omega]
    rw [hcand]
    simp only [kCandA, ggTWPosNat, if_true, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨_, twlk_getD_lt hlt hp _, _, twlk_getD_lt hlt hp _, rfl⟩
  | adj =>
    have hcand : l = (List.range (N - 4)).map (fun j => tgt (j + 1) % p) ++
        [l.getD (N - 4) 0, l.getD (N - 3) 0, l.getD (N - 2) 0] := by
      refine twlk_list_eq (n := N - 1) hlen ?_ hlt ?_ ?_
      · simp; omega
      · intro x hx
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with ⟨j, -, rfl⟩ | rfl | rfl | rfl
        · exact Nat.mod_lt _ hp
        · exact twlk_getD_lt hlt hp _
        · exact twlk_getD_lt hlt hp _
        · exact twlk_getD_lt hlt hp _
      · intro j hj
        rcases (by omega : j < N - 4 ∨ j = N - 4 ∨ j = N - 3 ∨ j = N - 2) with
          h1 | rfl | rfl | rfl
        · rw [List.getD_append _ _ _ _ (by simpa using h1), twlk_getD_map_range _ _ h1]
          exact (hfix j (by simp only [ggTWInJ]; omega)).symm
        · rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp [show N - 3 - (N - 4) = 1 by omega]
        · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp [show N - 2 - (N - 4) = 2 by omega]
    rw [hcand]
    simp only [kCandA, ggTWPosNat, List.mem_flatMap, List.mem_map, List.mem_range,
      show ¬ ((1 : ℕ) = 0) by omega, if_false]
    exact ⟨_, twlk_getD_lt hlt hp _, _, twlk_getD_lt hlt hp _, _, twlk_getD_lt hlt hp _, rfl⟩

theorem pat1_of_cover {RF : List (List ℕ)} {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool}
    {S : List KPat1} {T : List KPat2}
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1At p N RF rt S i = true)
    (posn c0 mi ni : ℕ) (hpos : posn = 0 ∨ posn = 1) (hc0 : c0 < N - 1) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) (hpat : ggTWNPat1B N posn c0 mi ni = true) :
    ∃ wits ents, kAll2 (kCell p N posn RF rt wits) (kCells1 p N posn c0 mi ni) ents = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c0 (List.mem_range.mpr hc0)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.1 mi (by rcases hmi with rfl | rfl <;> simp)
  have h4 := List.all_eq_true.mp h3 ni (by rcases hni with rfl | rfl <;> simp)
  have h5 : (posn, c0, mi, ni) ∈ S.map (·.1) := by simpa [hpat] using h4
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hS i hi
  simp only [kPat1At, List.getElem?_eq_getElem hi] at h6
  have h7 : kPat1 p N RF rt (S[i].1, S[i].2.1, S[i].2.2) = true := h6
  rw [hek] at h7
  exact ⟨_, _, h7⟩

theorem kDecode_code (c2 : Option ℕ) : kDecode (ggTWNCode c2) = c2 := by
  cases c2 <;> rfl

theorem pat2_of_cover {RF : List (List ℕ)} {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool}
    {S : List KPat1} {T : List KPat2}
    (hC : kCover N S T = true) (hT : ∀ i < T.length, kPat2At p N RF rt T i = true)
    (posn c : ℕ) (c2 : Option ℕ) (hpos : posn = 0 ∨ posn = 1) (hc : c < N - 1)
    (hc2 : c2 ∈ none :: (List.range (N - 1)).map some)
    (hpat : ggTWNPat2B N posn c c2 = true) :
    ∃ wits ents, kAll2 (kCell p N posn RF rt wits) (kCells2 p N posn c c2) ents = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.2 c2 hc2
  have h5 : (posn, c, ggTWNCode c2) ∈ T.map (·.1) := by simpa [hpat] using h3
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hT i hi
  simp only [kPat2At, List.getElem?_eq_getElem hi] at h6
  have h7 : kPat2 p N RF rt (T[i].1, T[i].2.1, T[i].2.2) = true := h6
  rw [hek] at h7
  have h8 : kAll2 (kCell p N posn RF rt T[i].2.1)
      (kCells2 p N posn c (kDecode (ggTWNCode c2))) T[i].2.2 = true := h7
  rw [kDecode_code] at h8
  exact ⟨_, _, h8⟩

@[expose] def TWLKRTSound (p N : ℕ) (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop)
    (rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool) : Prop :=
  ∀ (pos : GGTWPos) (news : List GGDepANPair) (kind k : ℕ), (∀ q ∈ news, GGTWNValid p N q) →
    kind ≠ 0 → rt (ggTWPosNat pos) news kind k = true →
    ∀ lam mu : ZMod p, (lam ≠ 0 ∨ mu ≠ 0) →
    (∀ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0) →
    (∃ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0) →
    GGTWKill .other p N pos (ggTWNNews p N news) (lam • ggTWx p N + mu • ggTWz p N pos) ∨
      (∃ c : ZMod p, c ≠ 0 ∧ GGTWPZBad p N pos (ggTWGens p N (ggTWNNews p N news))
        (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos))) ∨
      Out (ggTWGens p N (ggTWNNews p N news))

theorem twlk_hk [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (w : KHK)
    (h : kHKTest p N (ggTWPosNat pos) news (ggTWLY0 p N (ggTWPosNat pos) news) w = true)
    (lam mu : ZMod p) (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hx : ∃ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0) :
    GGTWKill .other p N pos (ggTWNNews p N news) (lam • ggTWx p N + mu • ggTWz p N pos) := by
  obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hnews lam mu hlm hfix hx
  rw [heq]
  exact (ggTWKill_other_smul pos _ _ t ht).mpr (kHKTest_sound hp hN pos hnews _ hY0len w h)

theorem twlk_end_finite [Fact p.Prime] : Finite (Module.End (ZMod p) (GGTWE p N)) :=
  Finite.of_injective (fun f : Module.End (ZMod p) (GGTWE p N) => (f : GGTWE p N → GGTWE p N))
    DFunLike.coe_injective

theorem twlk_closure_inv {M : Type*} [Monoid M] {S : Set M} (hS : ∀ s ∈ S, s * s = 1) :
    ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1 := by
  intro g hg
  induction hg using Submonoid.closure_induction with
  | mem x hx => exact ⟨x, Submonoid.subset_closure hx, hS x hx, hS x hx⟩
  | one => exact ⟨1, Submonoid.one_mem _, one_mul 1, mul_one 1⟩
  | mul x y hx hy ihx ihy =>
      obtain ⟨x', hx'mem, hxx', hx'x⟩ := ihx
      obtain ⟨y', hy'mem, hyy', hy'y⟩ := ihy
      exact ⟨y' * x', Submonoid.mul_mem _ hy'mem hx'mem,
        by rw [mul_assoc, ← mul_assoc y y' x', hyy', one_mul, hxx'],
        by rw [mul_assoc, ← mul_assoc x' x y, hx'x, one_mul, hy'y]⟩

theorem twlk_closure_inv_sub {M : Type*} [Monoid M] [Finite M] {S S' : Set M}
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1)
    (hsub : S' ⊆ Submonoid.closure S) :
    ∀ g ∈ Submonoid.closure S', ∃ g' ∈ Submonoid.closure S', g * g' = 1 ∧ g' * g = 1 := by
  intro g hg
  obtain ⟨g'', -, h1, h2⟩ := hinv g (Submonoid.closure_le.mpr hsub hg)
  have : Finite Mˣ := Finite.of_injective (fun u : Mˣ => (u : M)) (fun a b h => Units.ext h)
  let u : Mˣ := ⟨g, g'', h1, h2⟩
  have hn : 0 < orderOf u := orderOf_pos u
  have hgn : g ^ orderOf u = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one u)
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h
    exact h
  refine ⟨g ^ (orderOf u - 1), Submonoid.pow_mem _ hg _, ?_, ?_⟩
  · rw [← pow_succ', Nat.sub_add_cancel hn, hgn]
  · rw [← pow_succ, Nat.sub_add_cancel hn, hgn]

theorem twlk_card_subgroup {M : Type*} [Monoid M] {S : Set M}
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1)
    (H : Subgroup Mˣ) (hH : ∀ u : Mˣ, u ∈ H ↔ (u : M) ∈ Submonoid.closure S) :
    Nat.card ↥H = Nat.card ↥(Submonoid.closure S) := by
  apply Nat.card_eq_of_bijective
    (fun u : ↥H => (⟨(u.1 : M), (hH u.1).mp u.2⟩ : ↥(Submonoid.closure S)))
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Units.ext
    simpa using congrArg Subtype.val hab
  · intro g
    obtain ⟨g', -, hg'1, hg'2⟩ := hinv (g : M) g.2
    refine ⟨⟨⟨g, g', hg'1, hg'2⟩, (hH _).mpr g.2⟩, rfl⟩

@[expose] def twlkUnits {M : Type*} [Monoid M] (S : Set M)
    (hinv : ∀ g ∈ Submonoid.closure S, ∃ g' ∈ Submonoid.closure S, g * g' = 1 ∧ g' * g = 1) :
    Subgroup Mˣ where
  carrier := {u | (u : M) ∈ Submonoid.closure S}
  one_mem' := by
    change ((1 : Mˣ) : M) ∈ Submonoid.closure S
    rw [Units.val_one]
    exact Submonoid.one_mem _
  mul_mem' := by
    intro u v hu hv
    change ((u * v : Mˣ) : M) ∈ Submonoid.closure S
    rw [Units.val_mul]
    exact Submonoid.mul_mem _ hu hv
  inv_mem' := by
    intro u hu
    obtain ⟨g', hg'mem, hg'1, -⟩ := hinv (u : M) hu
    have hcalc : ((u⁻¹ : Mˣ) : M) = g' := by
      calc ((u⁻¹ : Mˣ) : M) = ((u⁻¹ : Mˣ) : M) * ((u : M) * g') := by rw [hg'1, mul_one]
        _ = g' := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    change ((u⁻¹ : Mˣ) : M) ∈ Submonoid.closure S
    rw [hcalc]
    exact hg'mem

theorem twlk_card_dvd [Fact p.Prime] {S S' : Set (Module.End (ZMod p) (GGTWE p N))}
    (hS : ∀ s ∈ S, s * s = 1) (hsub : S' ⊆ Submonoid.closure S) :
    Nat.card ↥(Submonoid.closure S') ∣ Nat.card ↥(Submonoid.closure S) := by
  have := twlk_end_finite (p := p) (N := N)
  have hinv := twlk_closure_inv hS
  have hinv' := twlk_closure_inv_sub hinv hsub
  have hle : twlkUnits S' hinv' ≤ twlkUnits S hinv := fun u hu =>
    (Submonoid.closure_le.mpr hsub) hu
  have hdv := Subgroup.card_dvd_of_le hle
  rwa [twlk_card_subgroup hinv' _ (fun u => Iff.rfl),
    twlk_card_subgroup hinv _ (fun u => Iff.rfl)] at hdv

theorem twlk_refl_mul_self (c f : GGTWE p N) (h : ggTWdot f c = 2) :
    ggTWRefl c f * ggTWRefl c f = 1 := by
  apply LinearMap.ext
  intro v
  have hd : ggDepAdot (N := N - 1) f (v - ggDepAdot (N := N - 1) f v • c) =
      ggDepAdot (N := N - 1) f v - ggDepAdot (N := N - 1) f v * ggDepAdot (N := N - 1) f c := by
    rw [twDot_sub_right, twDot_smul_right]
  have happ : ∀ w, ggTWRefl c f w = w - ggDepAdot (N := N - 1) f w • c := fun w => by
    simp [ggDepARefl, ggDepAform, ggDepAdot]
  have h' : ggDepAdot (N := N - 1) f c = 2 := h
  rw [Module.End.mul_apply, happ, happ, hd, h', Module.End.one_apply]
  module

theorem twlk_orbit_inv (pos : GGTWPos) (gens : Set (Module.End (ZMod p) (GGTWE p N)))
    (z : GGTWE p N) : ∀ t ∈ ggTWPZOrbit p N pos gens z, t * t = 1 := by
  have hfix : ∀ s ∈ ggTWPZFixRefl p N gens z, s * s = 1 := by
    rintro s ⟨-, ⟨c, f, hcf, rfl⟩, -⟩
    exact twlk_refl_mul_self c f hcf
  rintro t ⟨r, hrJ, g, hg, g', -, hgg', rfl⟩
  have hrr : r * r = 1 := by
    obtain ⟨c, f, hcf, rfl⟩ := hrJ.2
    exact twlk_refl_mul_self c f hcf
  obtain ⟨g'', -, h1, h2⟩ := twlk_closure_inv hfix g hg
  have hg'g : g' * g = 1 := by
    have : g' = g'' := by
      calc g' = (g'' * g) * g' := by rw [h2, one_mul]
        _ = g'' := by rw [mul_assoc, hgg', mul_one]
    rw [this, h2]
  calc (g * r * g') * (g * r * g') = g * (r * (g' * g) * r) * g' := by simp only [mul_assoc]
    _ = 1 := by rw [hg'g, mul_one, hrr, mul_one, hgg']

theorem twlk_foldl_lcm_dvd {n : ℕ} : ∀ (ms : List ℕ) (a : ℕ), a ∣ n → (∀ m ∈ ms, m ∣ n) →
    ms.foldl Nat.lcm a ∣ n
  | [], _, ha, _ => ha
  | m :: ms, a, ha, hm => twlk_foldl_lcm_dvd ms (Nat.lcm a m) (Nat.lcm_dvd ha (hm m (by simp)))
      (fun m' hm' => hm m' (List.mem_cons_of_mem _ hm'))

theorem kPZ_bad [Fact p.Prime] (pos : GGTWPos) (gens : Set (Module.End (ZMod p) (GGTWE p N)))
    (z : GGTWE p N) (T : Set (Module.End (ZMod p) (GGTWE p N))) (ms : List ℕ) (hasCen : Bool)
    (hT : T ⊆ ggTWPZOrbit p N pos gens z)
    (hms : ∀ m ∈ ms, ∃ S' ⊆ (Submonoid.closure T : Set (Module.End (ZMod p) (GGTWE p N))),
      Nat.card ↥(Submonoid.closure S') = m)
    (harith : ggTWLPZArith N (ms.foldl Nat.lcm 1) hasCen = true)
    (hcen : hasCen = true → ∃ a ∈ Submonoid.closure T, a ≠ 1 ∧ ∀ t ∈ T, a * t = t * a) :
    GGTWPZBad p N pos gens z := by
  have := twlk_end_finite (p := p) (N := N)
  set O := ggTWPZOrbit p N pos gens z with hO
  have hOi := twlk_orbit_inv pos gens z
  have hTi : ∀ t ∈ T, t * t = 1 := fun t ht => hOi t (hT ht)
  have hTO : T ⊆ Submonoid.closure O := fun t ht => Submonoid.subset_closure (hT ht)
  have hKT : ms.foldl Nat.lcm 1 ∣ Nat.card ↥(Submonoid.closure T) :=
    twlk_foldl_lcm_dvd ms 1 (one_dvd _) fun m hm => by
      obtain ⟨S', hS', rfl⟩ := hms m hm
      exact twlk_card_dvd hTi hS'
  have hTdvd : Nat.card ↥(Submonoid.closure T) ∣ Nat.card ↥(Submonoid.closure O) :=
    twlk_card_dvd hOi hTO
  intro r n c ht hlo hhi ⟨hdvd, himp⟩
  obtain ⟨rfl, rfl, hc⟩ := ggTWLPZArith_sound harith ht hlo hhi ((hKT.trans hTdvd).trans hdvd)
  have hOK := Nat.dvd_antisymm hdvd (hKT.trans hTdvd)
  have hcen1 := himp hOK
  obtain ⟨a, ha, hne, hcomm⟩ := hcen hc
  have hTK : Nat.card ↥(Submonoid.closure T) = Nat.card ↥(Submonoid.closure O) :=
    Nat.dvd_antisymm hTdvd (by rw [hOK]; exact hKT)
  have heq : ((Submonoid.closure T : Submonoid _) : Set (Module.End (ZMod p) (GGTWE p N))) =
      Submonoid.closure O := by
    apply Set.eq_of_subset_of_ncard_le (Submonoid.closure_le.mpr hTO)
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hTK.ge
  have hcommT : ∀ g ∈ Submonoid.closure T, a * g = g * a := by
    intro g hg
    induction hg using Submonoid.closure_induction with
    | mem x hx => exact hcomm x hx
    | one => rw [mul_one, one_mul]
    | mul x y _ _ ihx ihy => rw [← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]
  have haO : a ∈ Submonoid.closure O := by
    have : a ∈ ((Submonoid.closure T : Submonoid _) : Set (Module.End (ZMod p) (GGTWE p N))) := ha
    rwa [heq] at this
  unfold ggTWCentreCard at hcen1
  obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hcen1
  let x : {g : ↥(Submonoid.closure O) // ∀ h : ↥(Submonoid.closure O), g * h = h * g} :=
    ⟨⟨a, haO⟩, fun h => by
      have hT' : (h : Module.End (ZMod p) (GGTWE p N)) ∈
          ((Submonoid.closure T : Submonoid _) : Set (Module.End (ZMod p) (GGTWE p N))) := by
        rw [heq]; exact h.2
      exact Subtype.ext (hcommT h.1 hT')⟩
  let y : {g : ↥(Submonoid.closure O) // ∀ h : ↥(Submonoid.closure O), g * h = h * g} :=
    ⟨1, fun h => by rw [one_mul, mul_one]⟩
  exact hne (congrArg (fun u => (u.1 : Module.End (ZMod p) (GGTWE p N))) (hsub.elim x y))

theorem twlkPZ_toZ_add [Fact p.Prime] {a b : List ℕ} (ha : a.length = N - 1)
    (hb : b.length = N - 1) :
    ggTWNToZ p N (ggTWNAdd p a b) = ggTWNToZ p N a + ggTWNToZ p N b := by
  funext j
  have hj : j.val < N - 1 := j.isLt
  have hja : j.val < a.length := by rw [ha]; exact hj
  have hjb : j.val < b.length := by rw [hb]; exact hj
  have hjl : j.val < (a.zipWith (fun x y => (x + y) % p) b).length := by
    rw [List.length_zipWith, ha, hb, min_self]; exact hj
  simp only [ggTWNToZ, ggDepANToZ, ggTWNAdd, Pi.add_apply]
  rw [List.getD_eq_getElem (l := a.zipWith (fun x y => (x + y) % p) b) (d := 0) (n := j.val) hjl,
    List.getD_eq_getElem (l := a) (d := 0) (n := j.val) hja,
    List.getD_eq_getElem (l := b) (d := 0) (n := j.val) hjb,
    List.getElem_zipWith, ZMod.natCast_mod, Nat.cast_add]

theorem twlkPZ_add_length {M : ℕ} {a b : List ℕ} (ha : a.length = M) (hb : b.length = M) :
    (ggTWNAdd p a b).length = M := by
  simp only [ggTWNAdd, List.length_zipWith, ha, hb, min_self]

theorem twlkPZ_dot_of_valid [Fact p.Prime] {q : GGDepANPair} (h : GGTWNValid p N q) :
    ggTWdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2 := by
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 h.2.1 h.1
  rw [h.2.2, ZMod.natCast_mod] at hcast
  exact hcast.symm

theorem twlkPZ_valid_of_dot [Fact p.Prime] {q : GGDepANPair}
    (hq1 : q.1.length = N - 1) (hq2 : q.2.length = N - 1)
    (h : ggTWdot (ggTWNToZ p N q.2) (ggTWNToZ p N q.1) = 2) : GGTWNValid p N q := by
  refine ⟨hq1, hq2, ?_⟩
  have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 q.1 hq2 hq1
  have hdot : ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) q.1) = 2 := h
  rw [hdot] at hcast
  have h2 : ((ggDepANDot p q.2 q.1 : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
    rw [ZMod.natCast_mod]; exact hcast
  rw [ZMod.natCast_eq_natCast_iff'] at h2
  simpa [ggDepANDot, Nat.mod_mod] using h2

theorem twlkPZ_isRefl_of_valid [Fact p.Prime] {q : GGDepANPair} (hq : GGTWNValid p N q) :
    GGTWIsRefl (ggTWNRflOf p N q) :=
  ⟨ggTWNToZ p N q.1, ggTWNToZ p N q.2, twlkPZ_dot_of_valid hq, rfl⟩

theorem twlkPZ_rmul {r : Module.End (ZMod p) (GGTWE p N)} (hr : GGTWIsRefl r) : r * r = 1 := by
  rcases hr with ⟨c, f, h, rfl⟩
  exact twlk_refl_mul_self c f h

theorem twlkPZ_rfl_conj [Fact p.Prime] {q g : GGDepANPair} (hq : GGTWNValid p N q)
    (hg : GGTWNValid p N g) :
    ggTWNRflOf p N (ggDepANConj p q g) =
      ggTWNRflOf p N g * ggTWNRflOf p N q * ggTWNRflOf p N g := by
  have hc := l05nNC_toZ_conj (p := p) (N := N - 1) (q := q) (g := g) hq.1 hq.2.1 hg.1 hg.2.1
  change ggDepARefl (ggDepANToZ p (N - 1) (ggDepANConj p q g).1)
      (ggDepANToZ p (N - 1) (ggDepANConj p q g).2) = _
  rw [hc.1, hc.2]
  exact (l05nNC_refl_conj (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
    (ggDepANToZ p (N - 1) g.1) (ggDepANToZ p (N - 1) g.2) (twlkPZ_dot_of_valid hg)).symm

theorem twlkPZ_conj_valid [Fact p.Prime] {q g : GGDepANPair} (hq : GGTWNValid p N q)
    (hg : GGTWNValid p N g) : GGTWNValid p N (ggDepANConj p q g) := by
  have hlen := l05nNC_conj_length (p := p) (N := N - 1) hq.1 hq.2.1 hg.1 hg.2.1
  have hc := l05nNC_toZ_conj (p := p) (N := N - 1) (q := q) (g := g) hq.1 hq.2.1 hg.1 hg.2.1
  apply twlkPZ_valid_of_dot hlen.1 hlen.2
  change ggDepAdot (ggDepANToZ p (N - 1) (ggDepANConj p q g).2)
    (ggDepANToZ p (N - 1) (ggDepANConj p q g).1) = 2
  rw [hc.1, hc.2]
  exact l05nNC_conj_dot (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
    (ggDepANToZ p (N - 1) g.1) (ggDepANToZ p (N - 1) g.2) (twlkPZ_dot_of_valid hq)
    (twlkPZ_dot_of_valid hg)

theorem twlkPZ_fix_refl [Fact p.Prime] {q : GGDepANPair} {z : List ℕ} (hq : GGTWNValid p N q)
    (hz : z.length = N - 1) (h : ggDepANDot p q.2 z % p = 0) :
    ggTWNRflOf p N q (ggTWNToZ p N z) = ggTWNToZ p N z := by
  have hdot : ggDepAdot (ggDepANToZ p (N - 1) q.2) (ggDepANToZ p (N - 1) z) = 0 := by
    have hcast := ggDepANDot_cast (p := p) (N := N - 1) q.2 z hq.2.1 hz
    rw [← hcast]
    exact (ZMod.natCast_eq_zero_iff (ggDepANDot p q.2 z) p).mpr (Nat.dvd_of_mod_eq_zero h)
  change ggDepARefl (ggDepANToZ p (N - 1) q.1) (ggDepANToZ p (N - 1) q.2)
      (ggDepANToZ p (N - 1) z) = ggDepANToZ p (N - 1) z
  rw [l05nNC_refl_apply, hdot, zero_smul, sub_zero]

theorem twlkPZ_conj_fold [Fact p.Prime] (C : Submonoid (Module.End (ZMod p) (GGTWE p N)))
    (q : GGDepANPair) (hq : GGTWNValid p N q) :
    ∀ fixes : List GGDepANPair, (∀ g ∈ fixes, GGTWNValid p N g) →
      (∀ g ∈ fixes, ggTWNRflOf p N g ∈ C) →
      ∃ G ∈ C, ∃ G' ∈ C, G * G' = 1 ∧
        GGTWNValid p N (fixes.foldr (fun g acc => ggDepANConj p acc g) q) ∧
        ggTWNRflOf p N (fixes.foldr (fun g acc => ggDepANConj p acc g) q) =
          G * ggTWNRflOf p N q * G' := by
  intro fixes
  induction fixes with
  | nil =>
    intro _ _
    exact ⟨1, C.one_mem, 1, C.one_mem, by simp, by simpa [ggTWNRflOf] using hq, by simp⟩
  | cons g gs ih =>
    intro hfixv hfixmem
    have hgv : GGTWNValid p N g := hfixv g (by simp)
    have hgmem : ggTWNRflOf p N g ∈ C := hfixmem g (by simp)
    obtain ⟨G, hG, G', hG', hGG', hvrest, hEq⟩ :=
      ih (fun g' hg' => hfixv g' (by simp [hg'])) (fun g' hg' => hfixmem g' (by simp [hg']))
    refine ⟨ggTWNRflOf p N g * G, Submonoid.mul_mem _ hgmem hG,
      G' * ggTWNRflOf p N g, Submonoid.mul_mem _ hG' hgmem, ?_, ?_, ?_⟩
    · calc (ggTWNRflOf p N g * G) * (G' * ggTWNRflOf p N g)
          = ggTWNRflOf p N g * (G * G') * ggTWNRflOf p N g := by simp only [mul_assoc]
        _ = 1 := by rw [hGG', mul_one, twlkPZ_rmul (twlkPZ_isRefl_of_valid hgv)]
    · rw [List.foldr_cons]
      exact twlkPZ_conj_valid hvrest hgv
    · rw [List.foldr_cons, twlkPZ_rfl_conj hvrest hgv, hEq]
      simp only [mul_assoc]

theorem twlkPZ_word_J [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q)
    (S : Submonoid (Module.End (ZMod p) (GGTWE p N)))
    (w : List ℕ) (hw : ∀ g ∈ w, g < N - 1 + news.length)
    (hmem : ∀ g ∈ w, ggTWNRflOf p N (ggTWNGen p N news g) ∈ S)
    (q : GGDepANPair) (hq : GGTWNValid p N q) (hqm : ggTWNRflOf p N q ∈ S) :
    GGTWNValid p N (ggTWNWord p N news q w) ∧ ggTWNRflOf p N (ggTWNWord p N news q w) ∈ S := by
  induction w generalizing q with
  | nil => simpa [ggTWNWord] using ⟨hq, hqm⟩
  | cons g w ih =>
    have hwc : ggTWNWord p N news q (g :: w) =
        ggDepANConj p (ggTWNWord p N news q w) (ggTWNGen p N news g) := by
      simp [ggTWNWord]
    rw [hwc]
    obtain ⟨ihV, ihM⟩ := ih (fun g' hg' => hw g' (by simp [hg']))
      (fun g' hg' => hmem g' (by simp [hg'])) q hq hqm
    have hG : GGTWNValid p N (ggTWNGen p N news g) := ggTWNGen_valid hp hN hnews (hw g (by simp))
    refine ⟨twlkPZ_conj_valid ihV hG, ?_⟩
    rw [twlkPZ_rfl_conj ihV hG]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hmem g (by simp)) ihM) (hmem g (by simp))

theorem twlkPZ_gen_lt_of_inJ {pos : GGTWPos} {g : ℕ} (h : ggTWInJ N pos g) : g + 1 < N := by
  cases pos with
  | ends => simp only [ggTWInJ] at h; omega
  | adj => simp only [ggTWInJ] at h; omega

theorem twlkPZ_replay_length (d : ℕ) (T : List (List (List ℕ))) (par : List (Nat × Nat)) :
    (ggTWLReplay p d T par).length = par.length + 1 := by
  induction par using List.reverseRecOn with
  | nil => simp [ggTWLReplay]
  | append_singleton l e ih =>
    have hs : ggTWLReplay p d T (l ++ [e]) = ggTWLReplay p d T l ++
        [ggTWLMatMul p d ((ggTWLReplay p d T l).getD e.1 []) (T.getD e.2 [])] := by
      simp only [ggTWLReplay, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hs, List.length_append, ih]
    simp

theorem kPZTest_facts [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (y : List ℕ)
    (hy : y.length = N - 1) (e : KPZ)
    (h : kPZTest p N (ggTWPosNat pos) news y e = true) :
    (e.1.1 : ZMod p) ≠ 0 ∧ ∃ (T : Set (Module.End (ZMod p) (GGTWE p N))) (ms : List ℕ)
      (hasCen : Bool),
      T ⊆ ggTWPZOrbit p N pos (ggTWGens p N (ggTWNNews p N news))
        (ggTWx p N + (e.1.1 : ZMod p) • ggTWNToZ p N y) ∧
      (∀ m ∈ ms, ∃ S' ⊆ (Submonoid.closure T : Set (Module.End (ZMod p) (GGTWE p N))),
        Nat.card ↥(Submonoid.closure S') = m) ∧
      ggTWLPZArith N (ms.foldl Nat.lcm 1) hasCen = true ∧
      (hasCen = true → ∃ a ∈ Submonoid.closure T, a ≠ 1 ∧ ∀ t ∈ T, a * t = t * a) := by
  simp only [kPZTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  set fixP : List GGDepANPair :=
    e.1.2.1.map (fun f => ggTWNWord p N news (ggTWNGen p N news f.1) f.2) with hfixP
  set orbP : List GGDepANPair := e.1.2.2.1.map (fun f =>
      f.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], [])))
        (ggTWNWord p N news (ggTWNGen p N news f.1) f.2.1)) with horbP
  set T : List (List (List ℕ)) :=
    (e.1.2.2.2.map fun j => orbP.getD j ([], [])).map (ggTWLMatOfPair p (N - 1)) with hT
  set A : Set (Module.End (ZMod p) (GGTWE p N)) := ggTWGens p N (ggTWNNews p N news) with hA
  set zvec : GGTWE p N := ggTWx p N + (e.1.1 : ZMod p) • ggTWNToZ p N y with hzvec
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hc0, hc0p⟩, hfixs⟩, horbs⟩, hhg⟩, hfixdot⟩, hsubs⟩, hcw⟩, harith⟩
  have hsm : ggTWNToZ p N (ggDepANSmul p e.1.1 y) = (e.1.1 : ZMod p) • ggTWNToZ p N y :=
    l05nNC_toZ_smul (N := N - 1) (k := e.1.1) hy
  have hztest : ggTWNToZ p N (ggTWNAdd p (ggTWNX N) (ggDepANSmul p e.1.1 y)) = zvec := by
    rw [hzvec, twlkPZ_toZ_add (ggTWNX_length N) (l05nNC_smul_length (N := N - 1) hy), ggTWNX_toZ,
      hsm]
  refine ⟨?_, ?_⟩
  · intro hz
    have hdvd : p ∣ e.1.1 := (ZMod.natCast_eq_zero_iff e.1.1 p).mp hz
    have hle : p ≤ e.1.1 := Nat.le_of_dvd hc0 hdvd
    omega
  have hfix_all : ∀ s ∈ fixP, GGTWNValid p N s ∧ ggTWNRflOf p N s ∈ ggTWPZFixRefl p N A zvec := by
    intro s hs
    have hdotmod : ggDepANDot p s.2 (ggTWNAdd p (ggTWNX N) (ggDepANSmul p e.1.1 y)) % p = 0 :=
      beq_iff_eq.mp (hfixdot s hs)
    rw [hfixP] at hs
    rcases List.mem_map.mp hs with ⟨f, hf, rfl⟩
    obtain ⟨hf1, hf2⟩ := hfixs f hf
    have hvg : GGTWNValid p N (ggTWNGen p N news f.1) := ggTWNGen_valid hp hN hnews hf1
    have hmg : ggTWNRflOf p N (ggTWNGen p N news f.1) ∈ Submonoid.closure A :=
      ggTWNGen_mem hp hN hf1
    obtain ⟨hv, hm⟩ := ggTWNWord_valid_mem hp hN hnews hvg hmg hf2
    have hzl : (ggTWNAdd p (ggTWNX N) (ggDepANSmul p e.1.1 y)).length = N - 1 :=
      twlkPZ_add_length (ggTWNX_length N) (l05nNC_smul_length (N := N - 1) hy)
    have hfixz : ggTWNRflOf p N (ggTWNWord p N news (ggTWNGen p N news f.1) f.2) zvec = zvec := by
      rw [← hztest]
      exact twlkPZ_fix_refl hv hzl hdotmod
    exact ⟨hv, hm, twlkPZ_isRefl_of_valid hv, hfixz⟩
  have hJgen : ∀ g, ggTWNInJ N (ggTWPosNat pos) g = true →
      g < N - 1 + news.length ∧ ggTWNRflOf p N (ggTWNGen p N news g) ∈
        Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
          ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ) := by
    intro g hg
    have hgJ : ggTWInJ N pos g := (ggTWNInJ_iff pos g).mp hg
    have hglt : g + 1 < N := twlkPZ_gen_lt_of_inJ hgJ
    have hglt' : g < N - 1 := by omega
    refine ⟨by omega, ?_⟩
    have hgen : ggTWNGen p N news g = (ggTWNH p N g, ggTWNA p N g) := by
      rw [ggTWNGen, if_pos hglt]
    rw [hgen]
    refine Submonoid.subset_closure ⟨⟨⟨g, hglt'⟩, hgJ⟩, Set.mem_univ _, ?_⟩
    change ggTWRefl (ggTWh p N ⟨g, hglt'⟩) (ggTWα p N ⟨g, hglt'⟩) =
      ggTWRefl (ggTWNToZ p N (ggTWNH p N g)) (ggTWNToZ p N (ggTWNA p N g))
    rw [ggTWNH_toZ ⟨g, hglt'⟩, ggTWNA_toZ ⟨g, hglt'⟩]
  have horbit : ∀ q ∈ orbP, GGTWNValid p N q ∧ ggTWNRflOf p N q ∈ ggTWPZOrbit p N pos A zvec := by
    intro q hq
    rw [horbP] at hq
    rcases List.mem_map.mp hq with ⟨f, hf, rfl⟩
    obtain ⟨⟨hfJ, hfJw⟩, hffix⟩ := horbs f hf
    obtain ⟨hf1lt, hJmem⟩ := hJgen f.1 hfJ
    obtain ⟨hqinV, hqinM⟩ := twlkPZ_word_J hp hN hnews
      (Submonoid.closure ((fun i : {i : Fin (N - 1) // ggTWInJ N pos i.val} =>
        ggTWRefl (ggTWh p N i.1) (ggTWα p N i.1)) '' Set.univ))
      f.2.1 (fun g hg => (hJgen g (hfJw g hg)).1) (fun g hg => (hJgen g (hfJw g hg)).2)
      (ggTWNGen p N news f.1) (ggTWNGen_valid hp hN hnews hf1lt) hJmem
    have hqinJ : ggTWNRflOf p N (ggTWNWord p N news (ggTWNGen p N news f.1) f.2.1) ∈
        ggTWPZJRefl p N pos := by
      rw [ggTWPZJRefl]
      exact ⟨hqinM, twlkPZ_isRefl_of_valid hqinV⟩
    set fixes : List GGDepANPair := f.2.2.map (fun k => fixP.getD k ([], [])) with hfixes
    have hgetmem : ∀ k ∈ f.2.2, fixP.getD k ([], []) ∈ fixP := by
      intro k hk
      have hklt : k < fixP.length := hffix k hk
      rw [List.getD_eq_getElem (l := fixP) (d := ([], [])) (n := k) hklt]
      exact List.getElem_mem hklt
    have hfixe_v : ∀ g ∈ fixes, GGTWNValid p N g := by
      intro g hg
      rw [hfixes] at hg
      rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
      exact (hfix_all _ (hgetmem k hk)).1
    have hfixe_m : ∀ g ∈ fixes,
        ggTWNRflOf p N g ∈ Submonoid.closure (ggTWPZFixRefl p N A zvec) := by
      intro g hg
      rw [hfixes] at hg
      rcases List.mem_map.mp hg with ⟨k, hk, rfl⟩
      exact Submonoid.subset_closure (hfix_all _ (hgetmem k hk)).2
    obtain ⟨G, hG, G', hG', hGG', hvfold, hfold⟩ :=
      twlkPZ_conj_fold (Submonoid.closure (ggTWPZFixRefl p N A zvec)) _ hqinV
        fixes hfixe_v hfixe_m
    have hfoldmap : fixes.foldr (fun g acc => ggDepANConj p acc g)
        (ggTWNWord p N news (ggTWNGen p N news f.1) f.2.1) =
        f.2.2.foldr (fun k acc => ggDepANConj p acc (fixP.getD k ([], [])))
          (ggTWNWord p N news (ggTWNGen p N news f.1) f.2.1) :=
      List.foldr_map
    rw [hfoldmap] at hvfold hfold
    exact ⟨hvfold, ⟨_, hqinJ, G, hG, G', hG', hGG', hfold⟩⟩
  have hTWC : ∀ t ∈ T, ∃ q ∈ orbP, t = ggTWLMatOfPair p (N - 1) q := by
    intro t ht
    rw [hT] at ht
    rcases List.mem_map.mp ht with ⟨q, hq, rfl⟩
    rcases List.mem_map.mp hq with ⟨j, hj, rfl⟩
    have hjlt : j < orbP.length := hhg j hj
    refine ⟨orbP.getD j ([], []), ?_, rfl⟩
    rw [List.getD_eq_getElem (l := orbP) (d := ([], [])) (n := j) hjlt]
    exact List.getElem_mem hjlt
  have hT_valid : ∀ t ∈ T, ggTWLMatWF (N - 1) t := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := hTWC t ht
    exact (ggTWLMatOfPair_lin (horbit q hq).1).1
  set Sp : Set (Module.End (ZMod p) (GGTWE p N)) :=
    {g | ∃ t ∈ T, g = ggTWLMatLin p (N - 1) t} with hSp
  have hword : ∀ u : List ℕ, (∀ j ∈ u, j < T.length) →
      ggTWLMatWF (N - 1) (ggTWLWordMat p (N - 1) T u) ∧
        ggTWLMatLin p (N - 1) (ggTWLWordMat p (N - 1) T u) ∈ Submonoid.closure Sp := by
    intro u hu
    obtain ⟨hwf, hlin⟩ := ggTWLWordMat_lin (p := p) (d := N - 1) hT_valid hu
    refine ⟨hwf, ?_⟩
    rw [hlin]
    refine Submonoid.list_prod_mem _ fun x hx => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hkl := hu k hk
    refine Submonoid.subset_closure ⟨T.getD k [], ?_, rfl⟩
    rw [List.getD_eq_getElem _ _ hkl]
    exact List.getElem_mem hkl
  refine ⟨Sp, e.2.1.map (fun s => s.2.length + 1),
    (!ggTWLMatEq p (ggTWLWordMat p (N - 1) T e.2.2) (ggTWLMatOne (N - 1)) &&
      T.all fun t => ggTWLMatEq p (ggTWLMatMul p (N - 1) (ggTWLWordMat p (N - 1) T e.2.2) t)
        (ggTWLMatMul p (N - 1) t (ggTWLWordMat p (N - 1) T e.2.2))), ?_, ?_, ?_, ?_⟩
  · rintro s ⟨t, ht, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hTWC t ht
    rw [(ggTWLMatOfPair_lin (horbit q hq).1).2]
    exact (horbit q hq).2
  · intro m hm
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hm
    obtain ⟨hs1, hs2⟩ := hsubs s hs
    have hWs : ∀ t ∈ s.1.map (ggTWLWordMat p (N - 1) T), ggTWLMatWF (N - 1) t := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact (hword u (hs1 u hu)).1
    obtain ⟨-, -, hcard⟩ := ggTWLEnum_sound (p := p) (d := N - 1) hWs s.2 hs2
    refine ⟨{g | ∃ t ∈ s.1.map (ggTWLWordMat p (N - 1) T), g = ggTWLMatLin p (N - 1) t}, ?_, ?_⟩
    · rintro g ⟨t, ht, rfl⟩
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
      exact (hword u (hs1 u hu)).2
    · rw [hcard, twlkPZ_replay_length]
  · rw [List.foldl_map]
    exact harith
  · intro hcen
    rw [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hcen
    obtain ⟨hne, hcomm⟩ := hcen
    obtain ⟨haWF, haM⟩ := hword e.2.2 hcw
    set a := ggTWLWordMat p (N - 1) T e.2.2 with ha
    have honeWF := (ggTWLMatOne_lin (p := p) (d := N - 1)).1
    refine ⟨ggTWLMatLin p (N - 1) a, haM, fun heq => ?_, ?_⟩
    · have htrue : ggTWLMatEq p a (ggTWLMatOne (N - 1)) = true :=
        (ggTWLMatEq_iff haWF honeWF).mpr (by rw [heq, (ggTWLMatOne_lin (p := p) (d := N - 1)).2])
      rw [htrue] at hne
      exact Bool.noConfusion hne
    · rintro _ ⟨t, ht, rfl⟩
      have htWF := hT_valid t ht
      have h1 := (ggTWLMatMul_lin (p := p) (d := N - 1) haWF htWF).2
      have h2 := (ggTWLMatMul_lin (p := p) (d := N - 1) htWF haWF).2
      rw [← h1, ← h2]
      exact (ggTWLMatEq_iff (ggTWLMatMul_lin haWF htWF).1
        (ggTWLMatMul_lin htWF haWF).1).mp (hcomm t ht)

theorem twlk_pz [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N) (pos : GGTWPos)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (e : KPZ)
    (h : kPZTest p N (ggTWPosNat pos) news (ggTWLY0 p N (ggTWPosNat pos) news) e = true)
    (lam mu : ZMod p) (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hx : ∃ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0) :
    ∃ c : ZMod p, c ≠ 0 ∧ GGTWPZBad p N pos (ggTWGens p N (ggTWNNews p N news))
      (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos)) := by
  obtain ⟨hY0len, t, ht, heq⟩ := ggTWLY0_line hp hN pos hnews lam mu hlm hfix hx
  obtain ⟨hc0, T, ms, hasCen, hT, hms, harith, hcen⟩ :=
    kPZTest_facts hp hN pos hnews _ hY0len e h
  refine ⟨(e.1.1 : ZMod p) * t⁻¹, mul_ne_zero hc0 (inv_ne_zero ht), ?_⟩
  have htoz : ggTWNToZ p N (ggTWLY0 p N (ggTWPosNat pos) news) =
      t⁻¹ • (lam • ggTWx p N + mu • ggTWz p N pos) := by
    rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
  rw [htoz, smul_smul] at hT
  exact kPZ_bad pos _ _ T ms hasCen hT hms harith hcen

theorem kE8_cartan_diag (i : ℕ) : ggTWLCartanE 3 i i = 2 % 3 := by
  simp [ggTWLCartanE]

theorem kE8_cartan_cast (i j : Fin 8) :
    ((ggTWLCartanE 3 i.val j.val : ℕ) : ZMod 3) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
  fin_cases i <;> fin_cases j <;> decide

theorem kE8Test_facts {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid 3 9 q) (w : KE8)
    (h : kE8Test 3 9 news w = true) :
    ∃ hh αα : Fin 8 → GGTWE 3 9, (∀ i, ggTWdot (αα i) (hh i) = 2) ∧
      (∀ i j, ggTWdot (αα i) (hh j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)) ∧
      ggTWGens 3 9 (ggTWNNews 3 9 news) ⊆
        Submonoid.closure (Set.range fun i => ggTWRefl (hh i) (αα i)) ∧
      Set.range (fun i => ggTWRefl (hh i) (αα i)) ⊆
        Submonoid.closure (ggTWGens 3 9 (ggTWNNews 3 9 news)) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨e, gw, sw⟩ := w
  simp only [kE8Test, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc, beq_iff_eq] at h
  obtain ⟨hel, hgl, hswl, heL, hcar, hgw, hsw⟩ := h
  have he_getD (k : ℕ) (hk : k < e.length) : e.getD k ([], []) ∈ e := by
    rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk
  have hs_valq : ∀ q ∈ e, GGTWNValid 3 9 q := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
    obtain ⟨h1, h2⟩ := heL _ hq
    have hc := hcar k (by omega) k (by omega)
    rw [List.getD_eq_getElem _ _ hk] at hc
    refine ⟨h1, h2, ?_⟩
    rw [kE8_cartan_diag] at hc
    simpa [ggDepANDot, Nat.mod_mod] using hc
  have hs_val (i : Fin 8) : GGTWNValid 3 9 (e.getD i.val ([], [])) :=
    hs_valq _ (he_getD i.val (by rw [hel]; exact i.isLt))
  let s : Fin 8 → Module.End (ZMod 3) (GGTWE 3 9) := fun i =>
    ggTWNRflOf 3 9 (e.getD i.val ([], []))
  have hgen_valid : ∀ g, g < 9 - 1 + news.length → GGTWNValid 3 9 (ggTWNGen 3 9 news g) :=
    fun g hg => ggTWNGen_valid (p := 3) (N := 9) (by norm_num) (by norm_num) hnews hg
  set Sg := ggTWGens 3 9 (ggTWNNews 3 9 news) with hSg
  have hs_mem : ∀ i, s i ∈ Submonoid.closure Sg := by
    intro i
    obtain ⟨hu1, hu2, hpe⟩ := hsw i.val i.isLt
    have hword := ggTWNWord_valid_mem (p := 3) (N := 9) (by norm_num) (by norm_num) hnews
      (hgen_valid _ (by omega))
      (ggTWNGen_mem (p := 3) (N := 9) (by norm_num) (by norm_num) (by omega))
      (fun g hg => by have := hu2 g hg; omega)
    change ggTWNRflOf 3 9 (e.getD i.val ([], [])) ∈ _
    rw [← kPairEq_rfl hpe]
    exact hword.2
  have hS_mem : ∀ g, g < 9 - 1 + news.length →
      ggTWNRflOf 3 9 (ggTWNGen 3 9 news g) ∈ Submonoid.closure (Set.range s) := by
    intro g hg
    obtain ⟨hu1, hu2, hpe⟩ := hgw g (by omega)
    have he : ∀ q ∈ e, GGTWNValid 3 9 q ∧
        ggTWNRflOf 3 9 q ∈ Submonoid.closure (Set.range s) := by
      intro q hq
      refine ⟨hs_valq q hq, ?_⟩
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      refine Submonoid.subset_closure ⟨⟨k, by rw [← hel]; exact hk⟩, ?_⟩
      change ggTWNRflOf 3 9 (e.getD k ([], [])) = _
      rw [List.getD_eq_getElem _ _ hk]
    have hstart := he_getD _ (by rw [hel]; exact hu1)
    have hw := kEWord_valid_mem he _ (fun k hk => by rw [hel]; exact hu2 k hk) _
      (hs_valq _ hstart) (he _ hstart).2
    rw [← kPairEq_rfl hpe]
    exact hw.2
  refine ⟨fun i => ggTWNToZ 3 9 (e.getD i.val ([], [])).1,
    fun i => ggTWNToZ 3 9 (e.getD i.val ([], [])).2, fun i => k6_dot_of_valid (hs_val i), ?_, ?_,
    ?_⟩
  · intro i j
    have hc := hcar i.val i.isLt j.val j.isLt
    have hcast := ggDepANDot_cast (p := 3) (N := 8) (e.getD i.val ([], [])).2
      (e.getD j.val ([], [])).1 (hs_val i).2.1 (hs_val j).1
    change ggDepAdot (ggDepANToZ 3 8 _) (ggDepANToZ 3 8 _) = _
    rw [← hcast, ← ZMod.natCast_mod, hc, kE8_cartan_cast]
  · intro x hx
    rw [hSg, ggTWGens] at hx
    rcases hx with hx | hx
    · obtain ⟨i, rfl⟩ := hx
      have hiv : i.val + 1 < 9 := by have := i.isLt; omega
      have hgen : ggTWNGen 3 9 news i.val = (ggTWNH 3 9 i.val, ggTWNA 3 9 i.val) := by
        simp only [ggTWNGen, if_pos hiv]
      have h1 := hS_mem i.val (by have := i.isLt; omega)
      rw [hgen] at h1
      simp only [ggTWNRflOf] at h1
      rwa [ggTWNH_toZ, ggTWNA_toZ] at h1
    · obtain ⟨t, ht, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := ht
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
      have hgen : ggTWNGen 3 9 news (8 + k) = news[k] := by
        rw [ggTWNGen, if_neg (by omega), show 8 + k + 1 - 9 = k by omega,
          List.getD_eq_getElem _ _ hk]
      have h1 := hS_mem (8 + k) (by omega)
      rw [hgen] at h1
      exact h1
  · rintro x ⟨i, rfl⟩
    exact hs_mem i

theorem kE8Test_sound {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid 3 9 q) (w : KE8)
    (h : kE8Test 3 9 news w = true) : GGTWLowE8Outcome (ggTWGens 3 9 (ggTWNNews 3 9 news)) := by
  obtain ⟨hh, αα, h2, hc, h1, h2'⟩ := kE8Test_facts hnews w h
  exact ⟨hh, αα, h2, hc,
    le_antisymm (Submonoid.closure_le.mpr h2') (Submonoid.closure_le.mpr h1)⟩

theorem kRT8_sound (H : List KHK) (E : List KE8) :
    TWLKRTSound 3 9 GGTWLowE8Outcome (kRT8 3 9 H E) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro pos news kind k hnews _ h lam mu hlm hfix hx
  unfold kRT8 at h
  split_ifs at h
  · exact Or.inl (twlk_hk (by norm_num) (by norm_num) pos hnews _ h lam mu hlm hfix hx)
  · exact Or.inr (Or.inr (kE8Test_sound hnews _ h))

theorem kRTPZ_sound [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    (Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop) (H : List KHK) (Z : List KPZ) :
    TWLKRTSound p N Out (kRTPZ p N H Z) := by
  intro pos news kind k hnews _ h lam mu hlm hfix hx
  unfold kRTPZ at h
  split_ifs at h
  · exact Or.inl (twlk_hk hp hN pos hnews _ h lam mu hlm hfix hx)
  · exact Or.inr (Or.inl (twlk_pz hp hN pos hnews _ h lam mu hlm hfix hx))

theorem kRT6_sound {vs ws : List (List ℕ)} (hf : kFrameOK 3 6 vs ws = true) (H : List KHK)
    (Z : List KPZ) (F : List KE6) : TWLKRTSound 3 6 GGTWLowE6Outcome (kRT6 3 6 H Z F) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro pos news kind k hnews _ h lam mu hlm hfix hx
  unfold kRT6 at h
  split_ifs at h
  · exact Or.inl (twlk_hk (by norm_num) (by norm_num) pos hnews _ h lam mu hlm hfix hx)
  · exact Or.inr (Or.inl (twlk_pz (by norm_num) (by norm_num) pos hnews _ h lam mu hlm hfix hx))
  · exact Or.inr (Or.inr (kE6Test_sound hnews hf _ h))

theorem kRoots_eq {RF : List (List ℕ)} (hR : kRootsOK p N RF = true) :
    RF = ggTWNRoots p N ∧ ggTWNRootsOK p N (ggTWNRoots p N) = true := by
  unfold kRootsOK at hR
  rw [Bool.and_eq_true, beq_iff_eq] at hR
  exact ⟨hR.1, hR.1 ▸ hR.2⟩

theorem twlk_cell [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop}
    {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool} (hRT : TWLKRTSound p N Out rt)
    {RF : List (List ℕ)} (hR : kRootsOK p N RF = true) (pos : GGTWPos) (wits : List KKill)
    {news : List GGDepANPair} (hnews : ∀ q ∈ news, GGTWNValid p N q) (code : ℕ × ℕ)
    (h : kCell p N (ggTWPosNat pos) RF rt wits news code = true)
    (lam mu : ZMod p) (hlm : lam ≠ 0 ∨ mu ≠ 0)
    (hfix : ∀ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0)
    (hx : ∃ q ∈ news, ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0) :
    GGTWKill .frame p N pos (ggTWNNews p N news) (lam • ggTWx p N + mu • ggTWz p N pos) ∨
    GGTWKill .other p N pos (ggTWNNews p N news) (lam • ggTWx p N + mu • ggTWz p N pos) ∨
      (∃ c : ZMod p, c ≠ 0 ∧ GGTWPZBad p N pos (ggTWGens p N (ggTWNNews p N news))
        (ggTWx p N + c • (lam • ggTWx p N + mu • ggTWz p N pos))) ∨
      Out (ggTWGens p N (ggTWNNews p N news)) := by
  obtain ⟨hRF, hR'⟩ := kRoots_eq hR
  unfold kCell at h
  split_ifs at h with h0
  · rw [Bool.and_eq_true, hRF] at h
    exact Or.inl (ggTWNKillTest_sound hp hN hnews hR' _ h.1 h.2 pos _)
  · exact Or.inr (hRT pos news code.1 code.2 hnews h0 h lam mu hlm hfix hx)

theorem twlk_surv1 [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop}
    {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool} (hRT : TWLKRTSound p N Out rt)
    {RF : List (List ℕ)} {S : List KPat1} {T : List KPat2} (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1At p N RF rt S i = true) :
    ¬ GGTWLowSurv1 p N Out := by
  rintro ⟨pos, c0, m, n, ha, αa, lam, mu, hpat, hpair, hdot, hx, hlm, hfix, hkf, hko, hpz, hOut⟩
  obtain ⟨mi, ni, hmi, hni, rfl, rfl⟩ := twPat1_wit hpat
  have hpatB := (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr hpat
  obtain ⟨wits, ents, hchk⟩ := pat1_of_cover hC hS (ggTWPosNat pos) c0.val mi ni
    (twPosNat_mem pos) c0.isLt hmi hni hpatB
  obtain ⟨lh, la, hlh, hla, hd, hz, hvp, hnews⟩ :=
    ggTWLEnc1 hp hN pos c0 mi ni hmi hni ha αa hpair hdot hx
  have hmem : [(lh, la)] ∈ kCells1 p N (ggTWPosNat pos) c0.val mi ni := by
    simp only [kCells1, List.mem_flatMap, List.mem_filterMap]
    exact ⟨lh, kSolH_complete hN pos _ hlh, la, kSolA_complete hN pos _ hla, by simp [hd, hz]⟩
  obtain ⟨code, hcode⟩ := twlk_all2_mem _ _ ents hchk _ hmem
  have hvalid : ∀ q ∈ [(lh, la)], GGTWNValid p N q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hvp
  have hla_eq : ggTWNToZ p N la = αa := by
    have hm : (ggTWNToZ p N lh, ggTWNToZ p N la) ∈ ggTWNNews p N [(lh, la)] :=
      ⟨(lh, la), by simp, rfl⟩
    rw [hnews, Set.mem_singleton_iff] at hm
    exact congrArg Prod.snd hm
  have hfix' : ∀ q ∈ [(lh, la)],
      ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hla_eq]
    exact hfix
  have hx' : ∃ q ∈ [(lh, la)], ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0 :=
    ⟨(lh, la), by simp, by rw [hla_eq]; exact hx⟩
  rcases twlk_cell hp hN hRT hR pos wits hvalid code hcode lam mu hlm hfix' hx' with
    h | h | ⟨c, hc, h⟩ | h <;> rw [hnews] at h
  · exact hkf h
  · exact hko h
  · exact hpz c hc h
  · exact hOut h

theorem twlk_surv2 [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop}
    {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool} (hRT : TWLKRTSound p N Out rt)
    {RF : List (List ℕ)} {S : List KPat1} {T : List KPat2} (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hT : ∀ i < T.length, kPat2At p N RF rt T i = true) :
    ¬ GGTWLowSurv2 p N Out := by
  rintro ⟨pos, c, c₂, ha1, αa1, ha2, αa2, lam, mu, hpat, hpair, hx, hlm, h1, h2, hkf, hko,
    hpz, hOut⟩
  have hpatB := (ggTWNPat2B_iff pos c.val (c₂.map Fin.val)).mpr hpat
  have hc2m : c₂.map Fin.val ∈ none :: (List.range (N - 1)).map some := by
    cases c₂ with
    | none => simp
    | some c' =>
        exact List.mem_cons_of_mem none
          (List.mem_map.mpr ⟨c'.val, List.mem_range.mpr c'.isLt, rfl⟩)
  obtain ⟨wits, ents, hchk⟩ := pat2_of_cover hC hT (ggTWPosNat pos) c.val (c₂.map Fin.val)
    (twPosNat_mem pos) c.isLt hc2m hpatB
  obtain ⟨lh1, la1, lh2, la2, hlh1, hla1, hlh2, hla2, hd1, hd2, hd3, hd4, hx_list, hdet,
    hvp1, hvp2, hnews⟩ := ggTWLEnc2 hp hN pos c c₂ ha1 αa1 ha2 αa2 hpair hx lam mu hlm h1 h2
  have ht1 : kTgt1 p c.val 1 = fun c' => if c' = c.val then (p - 1) % p else 0 := by
    funext c'
    simp [kTgt1, Nat.mod_eq_of_lt (by omega : 1 < p)]
  have hmem : [(lh1, la1), (lh2, la2)] ∈ kCells2 p N (ggTWPosNat pos) c.val (c₂.map Fin.val) := by
    have H1 := kSolH_complete hN pos _ hlh1
    have A1 := kSolA_complete hN pos _ hla1
    have H2 := kSolH_complete hN pos _ hlh2
    have A2 := kSolA_complete hN pos _ hla2
    rw [← ht1] at H1 A1
    cases c₂ with
    | none =>
      simp only [Option.map_none] at H2 A2 hd2 hd4 ⊢
      simp only [kCells2, List.mem_flatMap, List.mem_filterMap]
      refine ⟨lh1, H1, la1, A1, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd1), List.mem_flatMap]
      refine ⟨lh2, H2, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd2), List.mem_filterMap]
      exact ⟨la2, A2, by simp [hd3, hd4, hx_list, hdet]⟩
    | some c' =>
      simp only [Option.map_some] at H2 A2 hd2 hd4 ⊢
      simp only [kCells2, List.mem_flatMap, List.mem_filterMap]
      refine ⟨lh1, H1, la1, A1, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd1), List.mem_flatMap]
      refine ⟨lh2, H2, ?_⟩
      rw [if_pos (beq_iff_eq.mpr hd2), List.mem_filterMap]
      exact ⟨la2, A2, by simp [hd3, hd4, hx_list, hdet]⟩
  obtain ⟨code, hcode⟩ := twlk_all2_mem _ _ ents hchk _ hmem
  have hvalid : ∀ q ∈ [(lh1, la1), (lh2, la2)], GGTWNValid p N q := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact hvp1
    · exact hvp2
  have hmem2 : ∀ q ∈ [(lh1, la1), (lh2, la2)],
      ggTWNToZ p N q.2 = αa1 ∨ ggTWNToZ p N q.2 = αa2 := by
    intro q hq
    have hm : (ggTWNToZ p N q.1, ggTWNToZ p N q.2) ∈ ggTWNNews p N [(lh1, la1), (lh2, la2)] :=
      ⟨q, hq, rfl⟩
    rw [hnews, Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with hm | hm
    · exact Or.inl (congrArg Prod.snd hm)
    · exact Or.inr (congrArg Prod.snd hm)
  have hfix' : ∀ q ∈ [(lh1, la1), (lh2, la2)],
      ggTWdot (ggTWNToZ p N q.2) (lam • ggTWx p N + mu • ggTWz p N pos) = 0 := by
    intro q hq
    rcases hmem2 q hq with he | he <;> rw [he]
    · exact h1
    · exact h2
  have hx' : ∃ q ∈ [(lh1, la1), (lh2, la2)], ggTWdot (ggTWNToZ p N q.2) (ggTWx p N) ≠ 0 := by
    have hsub : ∀ a ∈ ({(ha1, αa1), (ha2, αa2)} : Set (GGTWE p N × GGTWE p N)),
        ∃ q ∈ [(lh1, la1), (lh2, la2)], ggTWNToZ p N q.2 = a.2 := by
      intro a ha
      rw [← hnews] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      exact ⟨q, hq, rfl⟩
    rcases hx with hx1 | hx2
    · obtain ⟨q, hq, he⟩ := hsub (ha1, αa1) (Set.mem_insert _ _)
      exact ⟨q, hq, by rw [he]; exact hx1⟩
    · obtain ⟨q, hq, he⟩ := hsub (ha2, αa2) (Set.mem_insert_of_mem _ rfl)
      exact ⟨q, hq, by rw [he]; exact hx2⟩
  rcases twlk_cell hp hN hRT hR pos wits hvalid code hcode lam mu hlm hfix' hx' with
    h | h | ⟨c', hc', h⟩ | h <;> rw [hnews] at h
  · exact hkf h
  · exact hko h
  · exact hpz c' hc' h
  · exact hOut h

theorem twlk_sound [Fact p.Prime] (hp : 3 ≤ p) (hN : 5 ≤ N)
    {Out : Set (Module.End (ZMod p) (GGTWE p N)) → Prop}
    {rt : ℕ → List GGDepANPair → ℕ → ℕ → Bool} (hRT : TWLKRTSound p N Out rt)
    (RF : List (List ℕ)) (S : List KPat1) (T : List KPat2) (hR : kRootsOK p N RF = true)
    (hC : kCover N S T = true) (hS : ∀ i < S.length, kPat1At p N RF rt S i = true)
    (hT : ∀ i < T.length, kPat2At p N RF rt T i = true) : GGTWLowCells p N Out :=
  ⟨twlk_surv1 hp hN hRT hR hC hS, twlk_surv2 hp hN hRT hR hC hT⟩

end CFSG.StandardType.TWLK

end

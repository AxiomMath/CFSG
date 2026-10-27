module

public import CFSG.Certificates.Kernel.Fi24Syl.EnumSound
public import CFSG.Certificates.Kernel.Fi24Syl.LaneSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24Facts
public import CFSG.HardMathSupport.Timmesfeld.SporadicRank.Fi24Input
import all CFSG.Certificates.Kernel.Fi24Syl.EnumSound
import all CFSG.Certificates.Kernel.Spor.OrdSound
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.AGLEmbedding.CoverWeakGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaModSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeGen
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.KS.Fi24Syl

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KC.Fi24Syl CFSG.KS.Ord CFSG.AGLEmbedding.R3 Matrix
open CFSG.HardMathSupport.Timmesfeld.SporadicRank (FactsN o3SetN fixSetN matSetN fi24Matrices)

private theorem strictN_add {st y : ℕ} {k0 k1 : ℕ → ℕ} (h : ∀ N, k0 N = st + k1 N) :
    strictN y k0 = st + strictN y k1 := by
  rw [strictN_eq, strictN_eq]
  exact h y

private theorem strictN_congr {y : ℕ} {k f : ℕ → ℕ} (h : ∀ N, k N = f N) :
    strictN y k = f y := by
  rw [strictN_eq]
  exact h y

theorem stepK_add (AV La Ha L31 CMa TL T31 T32 T63 R1 M st : ℕ) :
    stepK AV La Ha L31 CMa TL T31 T32 T63 R1 M st =
      st + stepK AV La Ha L31 CMa TL T31 T32 T63 R1 M 0 := by
  have key : ∀ (N : ℕ) (b : Bool),
      nIf(b, contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N st, st) =
        st + nIf(b, contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N 0, 0) := by
    intro N b
    cases b
    · rfl
    · exact contribK_add AV La Ha L31 CMa TL T31 T32 T63 R1 N st
  unfold stepK
  exact strictN_add fun N => key N _

noncomputable def stepV (AV La Ha L31 CMa TL T31 T32 T63 R1 N : ℕ) : ℕ :=
  nIf(andB (notB (Nat.beq N 0)) (Nat.beq (mul7 (mul7 N N) N) 0),
    contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N 0, 0)

theorem stepK_zero (AV La Ha L31 CMa TL T31 T32 T63 R1 M : ℕ) :
    stepK AV La Ha L31 CMa TL T31 T32 T63 R1 M 0 =
      stepV AV La Ha L31 CMa TL T31 T32 T63 R1 (nOf M) := by
  unfold stepK
  exact strictN_congr (f := stepV AV La Ha L31 CMa TL T31 T32 T63 R1) fun N => rfl

local notation "stepC" => stepK (sumBelow 2187 35 vecRow) (rep1 6 15309)
  (Nat.mul 32 (rep1 6 15309)) (Nat.mul 31 (rep1 6 15309)) (Nat.mul 63 (rep1 42 2187))
  (Nat.shiftLeft (rep1 42 2187) 36) (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36))
  (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36)) (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36))
  (rep1 42 2187)

local notation "stepVC" => stepV (sumBelow 2187 35 vecRow) (rep1 6 15309)
  (Nat.mul 32 (rep1 6 15309)) (Nat.mul 31 (rep1 6 15309)) (Nat.mul 63 (rep1 42 2187))
  (Nat.shiftLeft (rep1 42 2187) 36) (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36))
  (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36)) (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36))
  (rep1 42 2187)

theorem chunkK_eq (Ps : List (List ℕ)) (R : ℕ) : chunkK Ps R = enumK stepC Ps R 0 := by
  unfold chunkK
  simp only [strictN_eq]

def O3 (M : ℕ) : Prop := mat7 M ≠ 1 ∧ mat7 M ^ 3 = 1

noncomputable instance (M : ℕ) : Decidable (O3 M) :=
  inferInstanceAs (Decidable (mat7 M ≠ 1 ∧ mat7 M ^ 3 = 1))

noncomputable def cv (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) : ℕ :=
  fixZ Y + ((if 243 ≤ fixC Y then fixZ Y * 2 ^ 21 else 0) + (if fixC Y ≤ 243 then 0 else 2 ^ 91854))

noncomputable def val (M : ℕ) : ℕ := if O3 M then cv (mat7 M - 1) else 0

private theorem nIf_val {b : Bool} {X : ℕ} {P : Prop} [Decidable P] (h : b = true ↔ P) :
    Bool.rec (motive := fun _ => ℕ) 0 X b = if P then X else 0 := by
  cases b
  · rw [if_neg (fun hp => Bool.noConfusion (h.2 hp))]
  · rw [if_pos (h.1 rfl)]

private theorem stepV_gen {AV La Ha L31 CMa TL T31 T32 T63 R1 N X : ℕ} {P : Prop} [Decidable P]
    (ho : andB (notB (Nat.beq N 0)) (Nat.beq (mul7 (mul7 N N) N) 0) = true ↔ P)
    (hc : contribK AV La Ha L31 CMa TL T31 T32 T63 R1 N 0 = X) :
    stepV AV La Ha L31 CMa TL T31 T32 T63 R1 N = if P then X else 0 := by
  unfold stepV
  rw [nIf_val ho, hc]

private theorem contrib_cv {M : ℕ} (hM : C7 M) :
    contribK (sumBelow 2187 35 vecRow) (rep1 6 15309)
      (Nat.mul 32 (rep1 6 15309)) (Nat.mul 31 (rep1 6 15309)) (Nat.mul 63 (rep1 42 2187))
      (Nat.shiftLeft (rep1 42 2187) 36) (Nat.mul 31 (Nat.shiftLeft (rep1 42 2187) 36))
      (Nat.mul 32 (Nat.shiftLeft (rep1 42 2187) 36))
      (Nat.mul 63 (Nat.shiftLeft (rep1 42 2187) 36)) (rep1 42 2187) (nOf M) 0 =
      cv (mat7 M - 1) := by
  obtain ⟨hN, hNm⟩ := nOf_sound hM
  unfold cv
  rw [← hNm]
  exact contrib_sound hN

theorem stepV_val {M : ℕ} (hM : C7 M) : stepVC (nOf M) = val M :=
  stepV_gen (P := O3 M) (ord3_sound hM) (contrib_cv hM)

theorem chunk_sum {Ps : List (List ℕ)} {R : ℕ} (hC : ∀ M ∈ leaves Ps R, C7 M) :
    chunkK Ps R = ((leaves Ps R).map val).sum := by
  rw [chunkK_eq, enumK_add stepC (fun M => stepC M 0)
    (fun M st => stepK_add _ _ _ _ _ _ _ _ _ _ M st), Nat.zero_add]
  congr 1
  refine List.map_congr_left fun M hM => ?_
  rw [stepK_zero, stepV_val (hC M hM)]

theorem leaves_C7 : ∀ (Ps : List (List ℕ)) (acc : ℕ), C7 acc → (∀ Pi ∈ Ps, ∀ P ∈ Pi, C7 P) →
    ∀ M ∈ leaves Ps acc, C7 M
  | [], acc, h, _, M, hM => by
    simp only [leaves, List.mem_singleton] at hM
    rw [hM]
    exact h
  | Pi :: Ps, acc, h, hP, M, hM => by
    simp only [leaves, List.mem_flatMap] at hM
    obtain ⟨P, hP', hM'⟩ := hM
    exact leaves_C7 Ps _ (mul7_sound h (hP Pi List.mem_cons_self P hP')).1
      (fun Q hQ => hP Q (List.mem_cons_of_mem _ hQ)) M hM'

theorem leaves_length : ∀ (Ps : List (List ℕ)) (acc : ℕ),
    (leaves Ps acc).length = (Ps.map List.length).prod
  | [], acc => by simp [leaves]
  | Pi :: Ps, acc => by
    simp only [leaves, List.length_flatMap, leaves_length Ps, List.map_cons, List.prod_cons,
      List.map_const', List.sum_replicate, smul_eq_mul]

theorem tops_C7 {T : ℕ → ℕ} (hT : topsOK T tops9 = true) : ∀ k < 9, C7 (T k) := by
  obtain ⟨hlen, hTk⟩ := tops_eq hT
  intro k hk
  rw [hTk k hk]
  refine (packL_sound fun x hx => tops9_lt _ ?_ x hx).1
  rw [List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

theorem pw_C7 {T : ℕ → ℕ} (hT : topsOK T tops9 = true) {k : ℕ} (hk : k < 9) :
    ∀ P ∈ pw T k, C7 P := by
  have h := tops_C7 hT k hk
  intro P hP
  simp only [pw, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with h1 | h1 | h1 <;> rw [h1]
  · exact one7_sound.1
  · exact h
  · exact (mul7_sound h h).1

theorem getD_C7 {L : List ℕ} (hL : ∀ P ∈ L, C7 P) (i : ℕ) : C7 (L.getD i 0) := by
  by_cases hi : i < L.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hL _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact canon7_zero

theorem RK_C7 {T : ℕ → ℕ} (hT : topsOK T tops9 = true) (c : ℕ) : C7 (RK T c) := by
  unfold RK
  have h8 := getD_C7 (pw_C7 hT (k := 8) (by norm_num)) (Nat.div c 9)
  have h7 := getD_C7 (pw_C7 hT (k := 7) (by norm_num)) (Nat.mod (Nat.div c 3) 3)
  have h6 := getD_C7 (pw_C7 hT (k := 6) (by norm_num)) (Nat.mod c 3)
  exact (mul7_sound (mul7_sound h8 h7).1 h6).1

theorem PsK_C7 {T : ℕ → ℕ} (hT : topsOK T tops9 = true) : ∀ Pi ∈ PsK T, ∀ P ∈ Pi, C7 P := by
  intro Pi hPi
  simp only [PsK, List.mem_cons, List.not_mem_nil, or_false] at hPi
  rcases hPi with h | h | h | h | h | h <;> rw [h] <;> exact pw_C7 hT (by norm_num)

noncomputable def lall (T : ℕ → ℕ) : List ℕ :=
  (List.range 27).flatMap fun c => leaves (PsK T) (RK T c)

theorem lall_length (T : ℕ → ℕ) : (lall T).length = 19683 := by
  unfold lall
  simp [List.length_flatMap, leaves_length, PsK, pw]

theorem flat_sum (F : ℕ → List ℕ) (g : ℕ → ℕ) : ∀ n,
    ∑ c ∈ Finset.range n, ((F c).map g).sum = (((List.range n).flatMap F).map g).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, flat_sum F g n, List.range_succ, List.flatMap_append,
      List.map_append, List.sum_append]
    simp

noncomputable def aF (M r : ℕ) : ℕ := if O3 M then zF (mat7 M - 1) r else 0

noncomputable def bF (M r : ℕ) : ℕ :=
  if O3 M ∧ 243 ≤ fixC (mat7 M - 1) then zF (mat7 M - 1) r else 0

noncomputable def pF (M : ℕ) : ℕ := if O3 M ∧ ¬ fixC (mat7 M - 1) ≤ 243 then 1 else 0

theorem zF_le (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) (r : ℕ) : zF Y r ≤ 1 := by
  unfold zF
  split <;> omega

theorem aF_le (M r : ℕ) : aF M r ≤ 1 := by
  unfold aF
  split
  · exact zF_le _ _
  · omega

theorem bF_le (M r : ℕ) : bF M r ≤ 1 := by
  unfold bF
  split
  · exact zF_le _ _
  · omega

private theorem pk_split (w n c : ℕ) (f g : ℕ → ℕ) :
    pk w n (fun r => f r + g r * c) = pk w n f + pk w n g * c := by
  unfold pk
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

private theorem val_eq (M : ℕ) :
    val M = pk 42 2187 (fun r => aF M r + bF M r * 2 ^ 21) + pF M * 2 ^ 91854 := by
  rw [pk_split]
  have hz : pk 42 2187 (zF (mat7 M - 1)) = fixZ (mat7 M - 1) := rfl
  have hz0 : pk 42 2187 (fun _ => 0) = 0 := by
    unfold pk
    simp
  unfold val cv aF bF pF
  generalize (2 : ℕ) ^ 91854 = K
  by_cases hO : O3 M
  · by_cases h1 : 243 ≤ fixC (mat7 M - 1)
    · by_cases h2 : fixC (mat7 M - 1) ≤ 243
      · simp only [hO, h1, h2, and_self, not_true_eq_false, and_false, ↓reduceIte, hz]
        ring
      · simp only [hO, h1, h2, and_self, not_false_eq_true, ↓reduceIte, hz]
        ring
    · have h2 : fixC (mat7 M - 1) ≤ 243 := by omega
      simp only [hO, h1, h2, and_false, not_true_eq_false, ↓reduceIte, hz, hz0]
      ring
  · simp only [hO, false_and, ↓reduceIte, hz0]
    ring

noncomputable def cA (T : ℕ → ℕ) (r : ℕ) : ℕ := ((lall T).map fun M => aF M r).sum

noncomputable def cB (T : ℕ → ℕ) (r : ℕ) : ℕ := ((lall T).map fun M => bF M r).sum

noncomputable def cP (T : ℕ → ℕ) : ℕ := ((lall T).map pF).sum

theorem sum_le_len {f : ℕ → ℕ} (hf : ∀ M, f M ≤ 1) : ∀ L : List ℕ, (L.map f).sum ≤ L.length
  | [] => by simp
  | M :: L => by
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := hf M
    have h2 := sum_le_len hf L
    omega

theorem cA_lt (T : ℕ → ℕ) (r : ℕ) : cA T r < 2 ^ 21 := by
  have h := sum_le_len (fun M => aF_le M r) (lall T)
  rw [lall_length] at h
  unfold cA
  omega

theorem cB_lt (T : ℕ → ℕ) (r : ℕ) : cB T r < 2 ^ 21 := by
  have h := sum_le_len (fun M => bF_le M r) (lall T)
  rw [lall_length] at h
  unfold cB
  omega

private theorem list_pk (G : ℕ → ℕ → ℕ) (H : ℕ → ℕ) (K : ℕ) : ∀ L : List ℕ,
    (L.map fun M => pk 42 2187 (G M) + H M * K).sum =
      pk 42 2187 (fun r => (L.map fun M => G M r).sum) + (L.map H).sum * K
  | [] => by
    unfold pk
    simp
  | M :: L => by
    simp only [List.map_cons, List.sum_cons, list_pk G H K L]
    rw [← pk_add]
    ring

private theorem tot_eq (T : ℕ → ℕ) : ((lall T).map val).sum =
    pk 42 2187 (fun r => cA T r + cB T r * 2 ^ 21) + cP T * 2 ^ 91854 := by
  rw [List.map_congr_left (fun M _ => val_eq M), list_pk]
  unfold cA cB cP
  generalize (2 : ℕ) ^ 91854 = K
  generalize (2 : ℕ) ^ 21 = K2
  have e : pk 42 2187 (fun r => ((lall T).map fun M => aF M r + bF M r * K2).sum) =
      pk 42 2187 (fun r => ((lall T).map fun M => aF M r).sum +
        ((lall T).map fun M => bF M r).sum * K2) :=
    pk_congr fun r _ => by rw [List.sum_map_add, List.sum_map_mul_right]
  rw [e]

private theorem andB_tt {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

private theorem ble_t {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := by
  rw [Nat.ble_eq]
  exact h

private theorem ble_f {a b : ℕ} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases e : Nat.ble a b with
  | false => rfl
  | true =>
    rw [Nat.ble_eq] at e
    exact absurd e h

theorem concl_parts {tot : ℕ} (h : concl tot = true) :
    Nat.land (Nat.shiftRight tot 91812) 0x1fffff < 6560 ∧ Nat.shiftRight tot 91854 = 0 ∧
      cntRows tot 0 2186 ≤ 26 ∧ cntRows tot 0 728 ≤ 80 ∧ cntRows tot 21 242 ≤ 242 := by
  unfold concl at h
  obtain ⟨h1, h⟩ := andB_tt h
  obtain ⟨h2, h⟩ := andB_tt h
  obtain ⟨h3, h⟩ := andB_tt h
  obtain ⟨h4, h5⟩ := andB_tt h
  exact ⟨Eq.mp Nat.blt_eq h1, Nat.eq_of_beq_eq_true h2, Eq.mp Nat.ble_eq h3, Eq.mp Nat.ble_eq h4,
    Eq.mp Nat.ble_eq h5⟩

private theorem shr2 (a b : ℕ) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

private theorem decode {A B : ℕ → ℕ} {P tot : ℕ} (hA : ∀ r, A r < 2 ^ 21) (hB : ∀ r, B r < 2 ^ 21)
    (h : tot = pk 42 2187 (fun r => A r + B r * 2 ^ 21) + P * 2 ^ 91854) :
    Nat.shiftRight tot 91854 = P ∧ (P = 0 → ∀ r < 2187,
      Nat.land (Nat.shiftRight tot (Nat.add (Nat.mul 42 r) 0)) 0x1fffff = A r ∧
      Nat.land (Nat.shiftRight tot (Nat.add (Nat.mul 42 r) 21)) 0x1fffff = B r) := by
  have e42 : (2 : ℕ) ^ 21 * 2 ^ 21 = 2 ^ 42 := by norm_num
  have hF : ∀ t < 2187, A t + B t * 2 ^ 21 < 2 ^ 42 := fun t _ => by
    have h1 := hA t
    have h2 := hB t
    rw [← e42]
    nlinarith
  have hlt := pk_lt hF
  have e1 : (42 * 2187 : ℕ) = 91854 := rfl
  rw [e1] at hlt
  have hK : 0 < (2 : ℕ) ^ 91854 := by positivity
  refine ⟨?_, fun hP r hr => ?_⟩
  · rw [h, shr2, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt hlt, Nat.zero_add]
  rw [hP, Nat.zero_mul, Nat.add_zero] at h
  have hl := lane_pk (w := 42) (n := 2187) hF hr
  unfold lane at hl
  have em : (0x1fffff : ℕ) = 2 ^ 21 - 1 := by norm_num
  have land' : ∀ a b : ℕ, Nat.land a b = a &&& b := fun _ _ => rfl
  have e0 : Nat.add (Nat.mul 42 r) 0 = 42 * r := rfl
  have e21 : Nat.add (Nat.mul 42 r) 21 = 42 * r + 21 := rfl
  rw [← h] at hl
  rw [land', land', em, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, shr2, shr2,
    e0, e21]
  constructor
  · rw [← Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by norm_num : 21 ≤ 42)), hl,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hA r)]
  · rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, ← Nat.mod_mul_right_div_self, e42, hl,
      Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (hA r), Nat.zero_add]

theorem cnt_eq {tot o t : ℕ} {C : ℕ → ℕ}
    (hC : ∀ r < 2187, Nat.land (Nat.shiftRight tot (Nat.add (Nat.mul 42 r) o)) 0x1fffff = C r) :
    cntRows tot o t = ((Finset.range 2187).filter fun r => t ≤ C r).card := by
  unfold cntRows
  rw [sumBelow_eq _ (by norm_num), Finset.card_filter]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hC r (Finset.mem_range.1 hr)]
  by_cases h : t ≤ C r
  · rw [if_pos h, ble_t h]
  · rw [if_neg h, ble_f h]

private theorem digits_sum : ∀ (k n : ℕ), n < 3 ^ k →
    n = ∑ j ∈ Finset.range k, n / 3 ^ j % 3 * 3 ^ j
  | 0, n, h => by
    simp only [pow_zero] at h
    simp only [Finset.range_zero, Finset.sum_empty]
    omega
  | k + 1, n, h => by
    rw [Finset.sum_range_succ']
    have h3 : n / 3 < 3 ^ k := by
      rw [pow_succ] at h
      omega
    have ih := digits_sum k (n / 3) h3
    have e : ∀ j, n / 3 ^ (j + 1) % 3 * 3 ^ (j + 1) = n / 3 / 3 ^ j % 3 * 3 ^ j * 3 := by
      intro j
      rw [pow_succ, Nat.mul_comm (3 ^ j) 3, ← Nat.div_div_eq_div_mul]
      ring
    simp only [e, ← Finset.sum_mul, ← ih]
    simp only [pow_zero, Nat.div_one, Nat.mul_one]
    omega

theorem vrow_inj {r r' : ℕ} (hr : r < 2187) (hr' : r' < 2187) (h : vrow r = vrow r') : r = r' := by
  have hd : ∀ j < 7, (r + 1) % 2187 / 3 ^ j % 3 = (r' + 1) % 2187 / 3 ^ j % 3 := by
    intro j hj
    have h1 := congrArg ZMod.val (congrFun h ⟨j, hj⟩)
    unfold vrow at h1
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_mod, Nat.mod_mod] at h1
  have b : ∀ n, n % 2187 < 3 ^ 7 := fun n => Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
    (by norm_num)
  have e : (r + 1) % 2187 = (r' + 1) % 2187 := by
    rw [digits_sum 7 ((r + 1) % 2187) (b _), digits_sum 7 ((r' + 1) % 2187) (b _)]
    exact Finset.sum_congr rfl fun j hj => by rw [hd j (Finset.mem_range.1 hj)]
  omega

theorem vrow_surj (v : Fin 7 → ZMod 3) : ∃ r < 2187, vrow r = v := by
  have hc : (Finset.univ : Finset (Fin 7 → ZMod 3)).card ≤ (Finset.range 2187).card := by
    simp [Finset.card_univ, Fintype.card_fun, ZMod.card]
  obtain ⟨r, hr, hv⟩ := Finset.surj_on_of_inj_on_of_card_le (fun r _ => vrow r)
    (fun _ _ => Finset.mem_univ _)
    (fun a b ha hb h => vrow_inj (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h) hc v
    (Finset.mem_univ _)
  exact ⟨r, Finset.mem_range.1 hr, hv.symm⟩

theorem card_vec (P : (Fin 7 → ZMod 3) → Prop) {dP : DecidablePred P} :
    (@Finset.filter _ P dP Finset.univ).card =
      (@Finset.filter ℕ (fun r => P (vrow r)) (fun r => dP (vrow r)) (Finset.range 2187)).card := by
  symm
  refine Finset.card_bij (fun r _ => vrow r) (fun r hr => ?_) (fun a ha b hb h => ?_)
    (fun v hv => ?_)
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hr).2⟩
  · exact vrow_inj (Finset.mem_range.1 (Finset.mem_filter.1 ha).1)
      (Finset.mem_range.1 (Finset.mem_filter.1 hb).1) h
  · obtain ⟨r, hr, rfl⟩ := vrow_surj v
    exact ⟨r, Finset.mem_filter.2 ⟨Finset.mem_range.2 hr, (Finset.mem_filter.1 hv).2⟩, rfl⟩

theorem vm_iff (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) (v : Fin 7 → ZMod 3) :
    vecMul v (Aᵀ - 1) = 0 ↔ A *ᵥ v = v := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_transpose, Matrix.vecMul_one, sub_eq_zero]

theorem zF_one {A : Matrix (Fin 7) (Fin 7) (ZMod 3)} {r : ℕ} (h : A *ᵥ vrow r = vrow r) :
    zF (Aᵀ - 1) r = 1 := by
  unfold zF
  rw [if_pos ((vm_iff A _).2 h)]

theorem zF_last (Y : Matrix (Fin 7) (Fin 7) (ZMod 3)) : zF Y 2186 = 1 := by
  have h : vrow 2186 = 0 := by
    funext j
    simp [vrow]
  unfold zF
  rw [h, Matrix.zero_vecMul, if_pos rfl]

theorem fixC_eq (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) : fixC (Aᵀ - 1) = (fixSetN 7 A).card := by
  unfold fixC fixSetN
  rw [card_vec, Finset.card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold zF
  by_cases h : A *ᵥ vrow r = vrow r
  · rw [if_pos ((vm_iff A _).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((vm_iff A _).1 h')), if_neg h]

theorem card_le_wsum {X : Type*} [DecidableEq X] (s : Finset X) (L : List ℕ) (f : ℕ → X)
    (w : ℕ → ℕ) (hs : ∀ a ∈ s, ∃ y ∈ L, f y = a ∧ 0 < w y) : s.card ≤ (L.map w).sum := by
  have h1 : s ⊆ ((L.filter fun y => 0 < w y).map f).toFinset := by
    intro a ha
    obtain ⟨y, hy, rfl, hw⟩ := hs a ha
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨y, List.mem_filter.2 ⟨hy, decide_eq_true hw⟩, rfl⟩
  have h2 : ∀ L : List ℕ, (L.filter fun y => 0 < w y).length ≤ (L.map w).sum := by
    intro L
    induction L with
    | nil => simp
    | cons y L ih =>
      by_cases hy : 0 < w y
      · rw [List.filter_cons_of_pos (by simpa using hy)]
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
      · rw [List.filter_cons_of_neg (by simpa using hy)]
        simp only [List.map_cons, List.sum_cons]
        omega
  calc s.card ≤ _ := Finset.card_le_card h1
    _ ≤ _ := List.toFinset_card_le _
    _ ≤ _ := by
      rw [List.length_map]
      exact h2 L

theorem fi24Facts_of_kc {T st : ℕ → ℕ} (hT : topsOK T tops9 = true)
    (hc : ∀ c < 27, chunkOK T c (st c) = true) (hf : concl (totK st) = true) :
    FactsN 7 fi24Matrices := by
  have hLC : ∀ M ∈ lall T, C7 M := by
    intro M hM
    unfold lall at hM
    rw [List.mem_flatMap] at hM
    obtain ⟨c, -, hM⟩ := hM
    exact leaves_C7 _ _ (RK_C7 hT c) (PsK_C7 hT) M hM
  have hcov : ∀ x ∈ fi24Matrices, ∃ M ∈ lall T, mat7 M = (toMatL 3 7 x)ᵀ := by
    intro x hx
    obtain ⟨c, hc', M, hM, -, hm⟩ := cover hT x hx
    refine ⟨M, ?_, hm⟩
    unfold lall
    exact List.mem_flatMap.2 ⟨c, List.mem_range.2 hc', hM⟩
  have htot : totK st = ((lall T).map val).sum := by
    unfold totK lall
    rw [sumBelow_eq _ (by norm_num), ← flat_sum]
    refine Finset.sum_congr rfl fun c hc' => ?_
    have h := hc c (Finset.mem_range.1 hc')
    unfold chunkOK at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact chunk_sum (leaves_C7 _ _ (RK_C7 hT c) (PsK_C7 hT))
  rw [tot_eq] at htot
  obtain ⟨h1, h2, h3, h4, h5⟩ := concl_parts hf
  obtain ⟨hP, hfld⟩ := decode (cA_lt T) (cB_lt T) htot
  have hP0 : cP T = 0 := hP.symm.trans h2
  have hfA := fun r hr => ((hfld hP0) r hr).1
  have hfB := fun r hr => ((hfld hP0) r hr).2
  have hO3 : ∀ A ∈ o3SetN 7 fi24Matrices, ∃ M ∈ lall T, O3 M ∧ mat7 M = Aᵀ := by
    intro A hA
    simp only [o3SetN, matSetN, Finset.mem_filter, List.mem_toFinset, List.mem_map] at hA
    obtain ⟨⟨x, hx, rfl⟩, ha1, ha3⟩ := hA
    obtain ⟨M, hM, hMm⟩ := hcov x hx
    refine ⟨M, hM, ⟨?_, ?_⟩, hMm⟩
    · rw [hMm]
      intro h
      apply ha1
      rw [← Matrix.transpose_transpose (toMatL 3 7 x), h, Matrix.transpose_one]
    · rw [hMm, ← Matrix.transpose_pow, ha3, Matrix.transpose_one]
  have hfix : ∀ (A : Matrix (Fin 7) (Fin 7) (ZMod 3)) v, v ∈ fixSetN 7 A ↔ A *ᵥ v = v :=
    fun A v => by simp [fixSetN]
  have hcntA : ∀ r, ((o3SetN 7 fi24Matrices).filter fun A => vrow r ∈ fixSetN 7 A).card ≤
      cA T r := by
    intro r
    refine card_le_wsum _ (lall T) (fun M => (mat7 M)ᵀ) (fun M => aF M r) fun A hA => ?_
    rw [Finset.mem_filter] at hA
    obtain ⟨M, hM, hO, hm⟩ := hO3 A hA.1
    refine ⟨M, hM, by rw [hm, Matrix.transpose_transpose], ?_⟩
    unfold aF
    rw [if_pos hO, hm, zF_one ((hfix A _).1 hA.2)]
    norm_num
  have hcntB : ∀ r, (((o3SetN 7 fi24Matrices).filter fun A => 243 ≤ (fixSetN 7 A).card).filter
      fun A => vrow r ∈ fixSetN 7 A).card ≤ cB T r := by
    intro r
    refine card_le_wsum _ (lall T) (fun M => (mat7 M)ᵀ) (fun M => bF M r) fun A hA => ?_
    rw [Finset.mem_filter, Finset.mem_filter] at hA
    obtain ⟨M, hM, hO, hm⟩ := hO3 A hA.1.1
    refine ⟨M, hM, by rw [hm, Matrix.transpose_transpose], ?_⟩
    unfold bF
    rw [if_pos ⟨hO, by rw [hm, fixC_eq]; exact hA.1.2⟩, hm, zF_one ((hfix A _).1 hA.2)]
    norm_num
  have e91812 : Nat.add (Nat.mul 42 2186) 0 = 91812 := rfl
  have hA2186 := hfA 2186 (by norm_num)
  rw [e91812] at hA2186
  refine ⟨?_, fun A hA => ?_, ?_, ?_, ?_⟩
  · calc (o3SetN 7 fi24Matrices).card ≤ cA T 2186 := by
          refine card_le_wsum _ (lall T) (fun M => (mat7 M)ᵀ) (fun M => aF M 2186) fun A hA => ?_
          obtain ⟨M, hM, hO, hm⟩ := hO3 A hA
          refine ⟨M, hM, by rw [hm, Matrix.transpose_transpose], ?_⟩
          unfold aF
          rw [if_pos hO, zF_last]
          norm_num
      _ < 6560 := by
          rw [← hA2186]
          exact h1
  · obtain ⟨M, hM, hO, hm⟩ := hO3 A hA
    have hp := List.sum_eq_zero_iff.1 hP0 (pF M) (List.mem_map_of_mem hM)
    unfold pF at hp
    rw [← fixC_eq, ← hm]
    by_contra hc'
    rw [if_pos ⟨hO, hc'⟩] at hp
    exact one_ne_zero hp
  · rw [card_vec]
    calc _ ≤ ((Finset.range 2187).filter fun r => 2186 ≤ cA T r).card := by
          refine Finset.card_le_card fun r hr => ?_
          rw [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, le_trans hr.2 (hcntA r)⟩
      _ = cntRows (totK st) 0 2186 := (cnt_eq hfA).symm
      _ ≤ 26 := h3
  · rw [card_vec]
    calc _ ≤ ((Finset.range 2187).filter fun r => 728 ≤ cA T r).card := by
          refine Finset.card_le_card fun r hr => ?_
          rw [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, le_trans hr.2 (hcntA r)⟩
      _ = cntRows (totK st) 0 728 := (cnt_eq hfA).symm
      _ ≤ 80 := h4
  · rw [card_vec]
    calc _ ≤ ((Finset.range 2187).filter fun r => 242 ≤ cB T r).card := by
          refine Finset.card_le_card fun r hr => ?_
          rw [Finset.mem_filter] at hr ⊢
          exact ⟨hr.1, le_trans hr.2 (hcntB r)⟩
      _ = cntRows (totK st) 21 242 := (cnt_eq hfB).symm
      _ ≤ 242 := h5

end CFSG.KS.Fi24Syl

end

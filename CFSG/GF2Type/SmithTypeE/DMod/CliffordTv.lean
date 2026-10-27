module

public import CFSG.GF2Type.SmithTypeE.DMod.CliffordCode
public import CFSG.GF2Type.SmithTypeE.DMod.Form
import all Certificates.Data.SmithD6Model

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.DMod

open CFSG.SmithD6

attribute [local irreducible] pairMat linePair

@[expose] def genC (k s : ℕ) : ℕ := if k < 6 then wedC k s else contrC (k - 6) s

theorem genC_xor (k a b : ℕ) : genC k (a ^^^ b) = genC k a ^^^ genC k b := by
  unfold genC
  split_ifs
  · exact wedC_xor k a b
  · exact contrC_xor (k - 6) a b

theorem genC_zero (k : ℕ) : genC k 0 = 0 := by
  have := genC_xor k 0 0
  rw [Nat.xor_self] at this
  rw [this, Nat.xor_self]

theorem genC_facts : ∀ k : Fin 12, ∀ S : Fin 64,
    genC k.val (2 ^ S.val) = (if clg k.val S.val = 64 then 0 else 2 ^ clg k.val S.val) ∧
    (clg k.val S.val ≠ 64 → clg k.val S.val < 64 ∧ par6 (clg k.val S.val) = !par6 S.val) := by
  decide

theorem evens_facts : ∀ c : Fin 32, evens[c.val]! < 64 ∧ par6 evens[c.val]! = false ∧
    evPos[evens[c.val]!]! = c.val ∧ evens[31 - c.val]! = 63 - evens[c.val]! := by
  decide

theorem evPos_facts : ∀ S : Fin 64, par6 S.val = false →
    evPos[S.val]! < 32 ∧ evens[evPos[S.val]!]! = S.val := by
  decide

@[expose] def evF (c : Fin 32) : Fin 64 := ⟨evens[c.val]!, (evens_facts c).1⟩

theorem evF_injective : Function.Injective evF := by
  intro a b h
  have h' : evens[a.val]! = evens[b.val]! := congrArg Fin.val h
  have ha := (evens_facts a).2.2.1
  have hb := (evens_facts b).2.2.1
  apply Fin.ext
  rw [← ha, ← hb, h']

theorem evF_rev (c : Fin 32) : evF (Fin.rev c) = Fin.rev (evF c) := by
  apply Fin.ext
  have h := (evens_facts c).2.2.2
  have hr : (Fin.rev c).val = 31 - c.val := by rw [Fin.val_rev]; omega
  have hr' : (Fin.rev (evF c)).val = 63 - evens[c.val]! := by
    rw [Fin.val_rev]
    change 64 - (evens[c.val]! + 1) = _
    omega
  rw [hr']
  change evens[(Fin.rev c).val]! = _
  rw [hr, h]

@[expose] noncomputable def exL : V →ₗ[ZMod 2] W64 :=
  ∑ c : Fin 32, (LinearMap.proj c : V →ₗ[ZMod 2] ZMod 2).smulRight (Pi.single (evF c) 1)

theorem exL_apply (v : V) : exL v = ∑ c : Fin 32, v c • Pi.single (evF c) (1 : ZMod 2) := by
  simp [exL, LinearMap.sum_apply]

theorem exL_single (c : Fin 32) : exL (Pi.single c 1) = Pi.single (evF c) 1 := by
  rw [exL_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem exL_apply_evF (v : V) (c : Fin 32) : exL v (evF c) = v c := by
  rw [exL_apply, Finset.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    have : evF c ≠ evF b := fun e => hb (evF_injective e).symm
    simp [Pi.single_apply, this]
  · simp

theorem exL_injective : Function.Injective exL := by
  intro v w h
  funext c
  rw [← exL_apply_evF v c, ← exL_apply_evF w c, h]

theorem betaL_exL (v w : V) : betaL (exL v) (exL w) = fModel v w := by
  have key : betaL.compl₁₂ exL exL = fModel := by
    refine LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 32)) (Pi.basisFun (ZMod 2) (Fin 32))
      fun a b => ?_
    simp only [LinearMap.compl₁₂_apply, Pi.basisFun_apply]
    rw [exL_single, exL_single, fModel_single, betaL_apply, Finset.sum_eq_single (evF a)]
    · simp only [Pi.single_eq_same, one_mul, Pi.single_apply]
      have hiff : Fin.rev (evF a) = evF b ↔ Fin.rev b = a := by
        rw [← evF_rev]
        constructor
        · intro e
          rw [← evF_injective e, Fin.rev_rev]
        · intro e
          rw [← e, Fin.rev_rev]
      by_cases h : Fin.rev b = a
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun e => h (hiff.mp e)), if_neg h]
    · intro T _ hT
      simp [Pi.single_apply, hT]
    · simp
  have := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B v w) key
  simpa using this

theorem exL_decode32_xor (a b : ℕ) :
    exL (decode32 (a ^^^ b)) = exL (decode32 a) + exL (decode32 b) := by
  rw [decode32_xor, map_add]

theorem clg2_spec {i j c : ℕ} (hi : i < 12) (hj : j < 12) (hc : c < 32) :
    clg2 i j c < 2 ^ 32 ∧
      exL (decode32 (clg2 i j c)) = decode64 (genC i (genC j (2 ^ evens[c]!))) := by
  obtain ⟨hS, hSp, -, -⟩ := evens_facts ⟨c, hc⟩
  obtain ⟨g1, g1'⟩ := genC_facts ⟨j, hj⟩ ⟨evens[c]!, hS⟩
  simp only at g1 g1'
  by_cases h1 : clg j evens[c]! = 64
  · have e : clg2 i j c = 0 := by simp [clg2, h1]
    rw [e, g1, if_pos h1, genC_zero, decode32_zero, decode64_zero, map_zero]
    exact ⟨by norm_num, rfl⟩
  · obtain ⟨hS1, hS1p⟩ := g1' h1
    obtain ⟨g2, g2'⟩ := genC_facts ⟨i, hi⟩ ⟨clg j evens[c]!, hS1⟩
    simp only at g2 g2'
    rw [g1, if_neg h1, g2]
    by_cases h2 : clg i (clg j evens[c]!) = 64
    · have e : clg2 i j c = 0 := by simp [clg2, h1, h2]
      rw [e, if_pos h2, decode32_zero, decode64_zero, map_zero]
      exact ⟨by norm_num, rfl⟩
    · obtain ⟨hS2, hS2p⟩ := g2' h2
      rw [if_neg h2]
      have hpar : par6 (clg i (clg j evens[c]!)) = false := by
        rw [hS2p, hS1p, hSp]
        rfl
      obtain ⟨hp, hpe⟩ := evPos_facts ⟨_, hS2⟩ hpar
      simp only at hp hpe
      have e : clg2 i j c = 2 ^ evPos[clg i (clg j evens[c]!)]! := by simp [clg2, h1, h2]
      rw [e]
      refine ⟨Nat.pow_lt_pow_right (by norm_num) hp, ?_⟩
      have h3 := decode32_two_pow ⟨_, hp⟩
      have h4 := decode64_two_pow ⟨_, hS2⟩
      simp only at h3 h4
      rw [h3, exL_single, h4]
      congr 1
      apply Fin.ext
      exact hpe

@[expose] def colExt (c A : ℕ) : ℕ := (A >>> (32 * c)) &&& 0xFFFFFFFF

theorem testBit_colExt (c A j : ℕ) :
    (colExt c A).testBit j = (A.testBit (32 * c + j) && decide (j < 32)) := by
  have h : (0xFFFFFFFF : ℕ) = 2 ^ 32 - 1 := by norm_num
  unfold colExt
  rw [Nat.testBit_and, Nat.testBit_shiftRight, h, Nat.testBit_two_pow_sub_one]

theorem colExt_xor (c a b : ℕ) : colExt c (a ^^^ b) = colExt c a ^^^ colExt c b := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, testBit_colExt, testBit_colExt, testBit_colExt, Nat.testBit_xor]
  cases decide (j < 32) <;> simp

theorem testBit_orFold (F : ℕ → ℕ) (hF : ∀ c < 32, F c < 2 ^ 32) {j : ℕ} (hj : j < 32) (c : ℕ) :
    ∀ n ≤ 32, ((List.range n).foldl (fun acc c => acc ||| (F c <<< (32 * c))) 0).testBit
      (32 * c + j) = (decide (c < n) && (F c).testBit j) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or,
      ih (by omega), Nat.testBit_shiftLeft]
    rcases lt_trichotomy c n with h | h | h
    · have h1 : ¬ (32 * c + j ≥ 32 * n) := by omega
      have h2 : c < n + 1 := by omega
      simp [h, h1, h2]
    · subst h
      have h1 : 32 * c + j - 32 * c = j := by omega
      simp [h1]
    · have h1 : 32 * c + j ≥ 32 * n := by omega
      have h2 : (F n).testBit (32 * c + j - 32 * n) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (hF n (by omega))
          (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have h3 : ¬ c < n := by omega
      have h4 : ¬ c < n + 1 := by omega
      simp [h3, h4, h2]

theorem colExt_pairMat {t c : ℕ} (ht : t < 144) (hc : c < 32) :
    colExt c pairMat[t]! = clg2 (t / 12) (t % 12) c := by
  have hF : ∀ c' < 32, clg2 (t / 12) (t % 12) c' < 2 ^ 32 := fun c' hc' =>
    (clg2_spec (by omega) (Nat.mod_lt _ (by norm_num)) hc').1
  have hsz : t < pairMat.size := by simp [pairMat, ht]
  rw [getElem!_pos pairMat t hsz]
  simp only [pairMat, Array.getElem_ofFn]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_colExt]
  by_cases hj : j < 32
  · rw [testBit_orFold _ hF hj c 32 le_rfl]
    simp [hc, hj]
  · have : (clg2 (t / 12) (t % 12) c).testBit j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hF c hc)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hj, this]

theorem foldl_xor_map {F : ℕ → ℕ} (hF : ∀ a b, F (a ^^^ b) = F a ^^^ F b) (f : ℕ → ℕ)
    (L : List ℕ) (a : ℕ) :
    F (L.foldl (fun acc i => acc ^^^ f i) a) = L.foldl (fun acc i => acc ^^^ F (f i)) (F a) := by
  induction L generalizing a with
  | nil => rfl
  | cons x L ih =>
    simp only [List.foldl_cons]
    rw [ih, hF]

theorem foldl_transfer {Ψ Φ : ℕ → W64} (stepF stepG : ℕ → ℕ → ℕ) (L : List ℕ)
    (h : ∀ i ∈ L, ∀ a b, Ψ a = Φ b → Ψ (stepF a i) = Φ (stepG b i)) (a b : ℕ)
    (hab : Ψ a = Φ b) : Ψ (L.foldl stepF a) = Φ (L.foldl stepG b) := by
  induction L generalizing a b with
  | nil => exact hab
  | cons x L ih =>
    simp only [List.foldl_cons]
    exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) _ _ (h x List.mem_cons_self a b hab)

theorem foldl_xor_transfer {Ψ Φ : ℕ → W64} (hΨ : ∀ a b, Ψ (a ^^^ b) = Ψ a + Ψ b)
    (hΦ : ∀ a b, Φ (a ^^^ b) = Φ a + Φ b) (f g : ℕ → ℕ) (L : List ℕ)
    (h : ∀ i ∈ L, Ψ (f i) = Φ (g i)) (a b : ℕ) (hab : Ψ a = Φ b) :
    Ψ (L.foldl (fun acc i => acc ^^^ f i) a) = Φ (L.foldl (fun acc i => acc ^^^ g i) b) := by
  induction L generalizing a b with
  | nil => exact hab
  | cons x L ih =>
    simp only [List.foldl_cons]
    refine ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) _ _ ?_
    rw [hΨ, hΦ, hab, h x List.mem_cons_self]

theorem foldl_filter_xor (p : ℕ → Bool) (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).filter p).foldl (fun acc i => acc ^^^ f i) 0 =
      xorFold n (fun i => bif p i then f i else 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.foldl_append, ih, xorFold_succ]
    cases hp : p n <;> simp [hp]

theorem xorFold_add (f : ℕ → ℕ) (n m : ℕ) :
    xorFold (n + m) f = xorFold n f ^^^ xorFold m (fun i => f (n + i)) := by
  induction m with
  | zero => simp [xorFold_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, xorFold_succ, ih, xorFold_succ, Nat.xor_assoc]

theorem foldl_bitsOf_genC (u s : ℕ) :
    (bitsOf u).foldl (fun acc i => acc ^^^ genC i s) 0 = rhoC u s := by
  unfold bitsOf
  have h12 : (12 : ℕ) = 6 + 6 := rfl
  rw [foldl_filter_xor, h12, xorFold_add]
  unfold rhoC
  refine congrArg₂ (· ^^^ ·) (xorFold_congr fun i hi => ?_) (xorFold_congr fun i _ => ?_)
  · simp [genC, hi]
  · have h1 : ¬ 6 + i < 6 := by omega
    have h2 : 6 + i - 6 = i := by omega
    simp [genC, h1, h2]

theorem foldl_bitsOf_genC2 (u w s : ℕ) :
    (bitsOf u).foldl (fun acc i => (bitsOf w).foldl (fun acc j => acc ^^^ genC i (genC j s)) acc)
      0 = rhoC u (rhoC w s) := by
  have e : (fun acc i => (bitsOf w).foldl (fun acc j => acc ^^^ genC i (genC j s)) acc) =
      fun acc i => acc ^^^ genC i (rhoC w s) := by
    funext acc i
    rw [foldl_xor_acc, ← foldl_bitsOf_genC w s, foldl_xor_map (genC_xor i), genC_zero]
  rw [e, foldl_bitsOf_genC]

theorem mem_bitsOf_lt {x i : ℕ} (h : i ∈ bitsOf x) : i < 12 := by
  unfold bitsOf at h
  exact List.mem_range.mp (List.mem_filter.mp h).1

@[expose] noncomputable def psiC (c x : ℕ) : W64 := exL (decode32 (colExt c x))

theorem psiC_xor (c a b : ℕ) : psiC c (a ^^^ b) = psiC c a + psiC c b := by
  unfold psiC
  rw [colExt_xor, exL_decode32_xor]

theorem psiC_zero (c : ℕ) : psiC c 0 = decode64 0 := by
  unfold psiC colExt
  rw [Nat.zero_shiftRight, Nat.zero_and, decode32_zero, decode64_zero, map_zero]

@[expose] def pairSum (u w : ℕ) : ℕ :=
  (bitsOf u).foldl (fun acc i => (bitsOf w).foldl (fun acc j => acc ^^^ pairMat[i * 12 + j]!) acc) 0

theorem tvCols_getElem (k : ℕ) {c : ℕ} (hc : c < 32) :
    (tvCols k)[c]! = colExt c (pairSum (linePair k).1 (linePair k).2) ^^^ 2 ^ c := by
  unfold tvCols
  rw [getElem!_pos _ c (by simp [hc]), Array.getElem_ofFn]
  rfl

theorem psiC_pairSum (u w : ℕ) {c : ℕ} (hc : c < 32) :
    psiC c (pairSum u w) = decode64 (rhoC u (rhoC w (2 ^ evens[c]!))) := by
  unfold pairSum
  rw [← foldl_bitsOf_genC2]
  refine foldl_transfer _ _ _ (fun i hi a b hab => ?_) 0 0 (psiC_zero c)
  refine foldl_xor_transfer (psiC_xor c) decode64_xor _ _ _ (fun j hj => ?_) a b hab
  have hi' := mem_bitsOf_lt hi
  have hj' := mem_bitsOf_lt hj
  have e1 : (i * 12 + j) / 12 = i := by omega
  have e2 : (i * 12 + j) % 12 = j := by omega
  have e3 := colExt_pairMat (t := i * 12 + j) (by omega) hc
  rw [e1, e2] at e3
  unfold psiC
  rw [e3]
  exact (clg2_spec hi' hj' hc).2

theorem exL_colsLin_tvCols (k : ℕ) (v : V) :
    exL (colsLin (tvCols k) v) = tlift (dec12 (linePair k).1) (dec12 (linePair k).2) (exL v) := by
  have hcol : ∀ c : Fin 32, exL (decode32 (tvCols k)[c.val]!) =
      tlift (dec12 (linePair k).1) (dec12 (linePair k).2) (Pi.single (evF c) 1) := by
    intro c
    rw [tvCols_getElem k c.isLt, exL_decode32_xor]
    have hb := psiC_pairSum (linePair k).1 (linePair k).2 c.isLt
    unfold psiC at hb
    have hS : decode64 (2 ^ evens[c.val]!) = Pi.single (evF c) 1 := decode64_two_pow (evF c)
    rw [hb, decode32_two_pow, exL_single]
    simp only [tlift, LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply]
    rw [← hS, ← decode64_rhoC, ← decode64_rhoC, add_comm]
  rw [colsLin_apply, exL_apply v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, map_smul, hcol c]

section Lift

variable {k : ℕ} (h : TsPair (dec12 (linePair k).1) (dec12 (linePair k).2))
include h

theorem colsLin_tvCols_invol (v : V) : colsLin (tvCols k) (colsLin (tvCols k) v) = v := by
  apply exL_injective
  rw [exL_colsLin_tvCols, exL_colsLin_tvCols, tlift_apply_tlift h]

theorem fModel_colsLin_tvCols (v w : V) :
    fModel (colsLin (tvCols k) v) (colsLin (tvCols k) w) = fModel v w := by
  rw [← betaL_exL, exL_colsLin_tvCols, exL_colsLin_tvCols, betaL_tlift h, betaL_exL]

theorem annSub_exL_colsLin_tvCols (s : V) :
    annSub (exL (colsLin (tvCols k) s)) =
      (annSub (exL s)).map (siegelEquiv (dec12 (linePair k).1) (dec12 (linePair k).2)).toLinearMap := by
  rw [exL_colsLin_tvCols, annSub_tlift h]

end Lift

theorem colsLin_tvCols_conj {g p v : ℕ}
    (h : tlift (dec12 (linePair v).1) (dec12 (linePair v).2) =
      tlift (dec12 (linePair g).1) (dec12 (linePair g).2) *
        tlift (dec12 (linePair p).1) (dec12 (linePair p).2) *
          tlift (dec12 (linePair g).1) (dec12 (linePair g).2)) (x : V) :
    colsLin (tvCols v) x = colsLin (tvCols g) (colsLin (tvCols p) (colsLin (tvCols g) x)) := by
  apply exL_injective
  rw [exL_colsLin_tvCols, exL_colsLin_tvCols, exL_colsLin_tvCols, exL_colsLin_tvCols, h,
    Module.End.mul_apply, Module.End.mul_apply]

end CFSG.GF2Type.SmithTypeE.DMod

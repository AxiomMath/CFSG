module

public import Certificates.Data.Kernel.O8.Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverO8Facts
import CFSG.Certificates.Kernel.O8SASound

public section

namespace CFSG.KC.O8P

open Subgroup CFSG.KC.Enum CFSG.KC.O8 CFSG.EvenSmallLie.OmegaEight
open CFSG.ComponentClassification.RankTwoHypIICover.O8

private theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

private theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

private theorem bAndI {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true :=
  (CFSG.KS.bAnd_iff a b).1 h

private theorem bImp (c t : Bool) :
    (Bool.rec (motive := fun _ => Bool) true t c = true) ↔ (c = true → t = true) := by
  cases c <;> simp

private theorem bIfT {c t e : Bool} (hc : c = true) :
    Bool.rec (motive := fun _ => Bool) e t c = t := by
  subst hc; rfl

private theorem bIfF {c t e : Bool} (hc : c = false) :
    Bool.rec (motive := fun _ => Bool) e t c = e := by
  subst hc; rfl

private theorem beqT {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a

private theorem beqF {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

private theorem fldE (q o r : Nat) :
    Nat.land (Nat.shiftRight q o) (2 ^ r - 1) = q / 2 ^ o % 2 ^ r := by
  change (q >>> o) &&& (2 ^ r - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

private theorem saAtK_saCodes (i : Nat) : saAtK saCodes i = saMat i :=
  fldE saCodes (64 * i) 64

private theorem ix13_eq (T i : Nat) : ix13 T i = T / 2 ^ (13 * i) % 8192 :=
  fldE T (13 * i) 13

private theorem lab_eq (i : Nat) :
    fld(saLabT, Nat.mul (nat_lit 3) i, nat_lit 7) = saLab i :=
  fldE saLabT (3 * i) 3

private theorem f1_le (T k : Nat) : f1 T k ≤ 1 := Nat.and_le_right

private theorem idK_eq : idK = idCode := by decide +kernel

private theorem anyBlk_spec {b : Nat} {f : Nat → Bool} : ∀ {len : Nat}, anyBlk b f len = true →
    ∃ l < len, f (Nat.add b l) = true
  | 0, h => absurd (h : false = true) Bool.false_ne_true
  | len + 1, h => by
    change Bool.rec (motive := fun _ => Bool) (anyBlk b f len) true (f (Nat.add b len)) = true
      at h
    cases e : f (Nat.add b len)
    · rw [e] at h
      obtain ⟨l, hl, hf⟩ := anyBlk_spec h
      exact ⟨l, by omega, hf⟩
    · exact ⟨len, by omega, e⟩

private theorem prodK_succ (b : Nat) (F : Nat → Nat) (n : Nat) :
    prodK b F (n + 1) = matMulM (prodK b F n) (F (Nat.add b n)) := by
  change strictN (prodK b F n) (fun a => matMulK a (F (Nat.add b n))) = _
  rw [sN, matMulK_eq]

private theorem prodRK_succ (b : Nat) (F : Nat → Nat) (n : Nat) :
    prodRK b F (n + 1) = matMulM (F (Nat.add b n)) (prodRK b F n) := by
  change strictN (prodRK b F n) (fun a => matMulK (F (Nat.add b n)) a) = _
  rw [sN, matMulK_eq]

private theorem powK_succ (x m : Nat) : powK x (m + 1) = matMulM (powK x m) x := by
  change strictN (powK x m) (fun a => matMulK a x) = _
  rw [sN, matMulK_eq]

section Acts

private theorem acts_idK : Acts 1 idK := by rw [idK_eq]; exact acts_one

private theorem eqΩ {u v : Equiv.Perm (Fin 360)} (hu : u ∈ omegaT) (hv : v ∈ omegaT) {M : ℕ}
    (au : Acts u M) (av : Acts v M) : u = v := by
  have h : omegaRes ⟨u, hu⟩ = omegaRes ⟨v, hv⟩ := by
    refine Equiv.ext fun j => Fin.ext ?_
    rw [omegaRes_apply_val, omegaRes_apply_val]
    exact (au j j.2).2.trans (av j j.2).2.symm
  exact congrArg Subtype.val (omegaRes_injective h)

private theorem comm_of {c t : Equiv.Perm (Fin 360)} {C M : ℕ} (hc : c ∈ omegaT) (ht : t ∈ autT)
    (ht2 : t * t = 1) (ac : Acts c C) (at' : Acts t M) (h : matMulM C M = matMulM M C) :
    c * t = t * c := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hm : t * c * t ∈ omegaT := by
    have := (conj_mem_omegaT ht).1 hc
    rwa [hti] at this
  have a1 : Acts (t * c * t) (matMulM (matMulM M C) M) := acts_mul (acts_mul at' ac) at'
  have a2 : Acts (c * t * t) (matMulM (matMulM M C) M) := by
    rw [← h]; exact acts_mul (acts_mul ac at') at'
  rw [mul_assoc c, ht2, mul_one] at a2
  have e := eqΩ hm hc a1 a2
  calc c * t = t * c * t * t := by rw [e]
    _ = t * c := by rw [mul_assoc (t * c), ht2, mul_one]

private theorem regs {V A B NR : Nat} (hroot : ∀ k < 8, ActsOn0 genArrs[k]! (saAtK V k))
    (hslp : ∀ k < NR, slpAt V A B k = true) :
    ∀ k < NR, ∃ c ∈ omegaT, Acts c (saAtK V k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h8 : k < 8
    · exact ⟨gen k, gen_mem_omegaT h8, acts_of_rep (rep_gen (by omega)) (hroot k h8)⟩
    · have h := hslp k hk
      unfold slpAt at h
      rw [bIfF (Bool.eq_false_iff.2 fun e => h8 (Nat.blt_eq.mp e))] at h
      simp only [sB] at h
      obtain ⟨ha, h⟩ := bAndI h
      obtain ⟨hb, he⟩ := bAndI h
      have ha' := Nat.blt_eq.mp ha
      have hb' := Nat.blt_eq.mp hb
      obtain ⟨ca, hca, aa⟩ := ih _ ha' (by omega)
      obtain ⟨cb, hcb, ab⟩ := ih _ hb' (by omega)
      refine ⟨ca * cb, mul_mem hca hcb, ?_⟩
      have := acts_mul aa ab
      rwa [← matMulK_eq, Nat.eq_of_beq_eq_true he] at this

private theorem gen9_sq (hs : SAFacts) : gen 9 * gen 9 = 1 := by
  have m9 : gen 9 ∈ sylowT := gen_mem_sylowT (l := 4) (by norm_num)
  have a9 : Acts (gen 9) (saMat (saGen 4)) := acts_gen hs (l := 4) (by norm_num)
  have a := acts_mul a9 a9
  rw [hs.closed _ (hs.gens 4 (by norm_num)).1 4 (by norm_num),
    show saMul (saGen 4) 4 = 0 by decide +kernel, hs.id0] at a
  exact eq_of_acts hs (mul_mem m9 m9) (one_mem _) idCode_lt a acts_one

private theorem bit_spec (hs : SAFacts) {CH : Nat}
    (hchi : ∀ i < 8192, chiAt saParT saLabT CH i = true) :
    ∀ i < 8192, (f1 CH i = 0 → saElt i ∈ omegaT) ∧ (f1 CH i = 1 → gen 9 * saElt i ∈ omegaT) := by
  have g9 := gen9_sq hs
  have g9A : gen 9 ∈ autT := gen_mem_autT (by norm_num)
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hc := hchi i hi
    unfold chiAt at hc
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [bIfT (Nat.beq_refl 0)] at hc
      have h0 := Nat.eq_of_beq_eq_true hc
      have e : saElt 0 = 1 := by
        rw [saElt, dif_neg fun h => absurd h.1 (Nat.lt_irrefl 0)]
      exact ⟨fun _ => e ▸ one_mem _, fun h1 => absurd (h0.symm.trans h1) (by norm_num)⟩
    · obtain ⟨hp, hl, -⟩ := hs.tree i hi hpos
      have e : saElt i = gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i) := by
        rw [saElt, dif_pos ⟨hpos, hp⟩]
      rw [bIfF (beqF (Nat.pos_iff_ne_zero.1 hpos)), lab_eq] at hc
      have hc' : f1 CH i = Nat.xor (f1 CH (saPar i))
          (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq (saLab i) 4)) := by
        have := Nat.eq_of_beq_eq_true hc
        rwa [ix13_eq] at this
      obtain ⟨ih0, ih1⟩ := ih (saPar i) hp (hp.trans hi)
      rw [e]
      have hpb := f1_le CH (saPar i)
      have hib := f1_le CH i
      by_cases h4 : saLab i = 4
      · rw [beqT h4] at hc'
        have hg : gen (sylowIdx.getD (saLab i) 0) = gen 9 := by rw [h4]; rfl
        rw [hg]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpb with hb | hb <;> rw [hb] at hc' ih0 ih1
        · refine ⟨fun h => absurd (hc'.symm.trans h) (by decide), fun _ => ?_⟩
          rw [← mul_assoc, g9, one_mul]; exact ih0 rfl
        · exact ⟨fun _ => ih1 rfl, fun h => absurd (hc'.symm.trans h) (by decide)⟩
      · rw [beqF h4] at hc'
        have hl8 : sylowIdx.getD (saLab i) 0 < 8 := by
          have : saLab i < 4 := by omega
          interval_cases (saLab i) <;> decide
        have hgm := gen_mem_omegaT hl8
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hpb with hb | hb <;> rw [hb] at hc' ih0 ih1
        · exact ⟨fun _ => mul_mem hgm (ih0 rfl), fun h => absurd (hc'.symm.trans h) (by decide)⟩
        · refine ⟨fun h => absurd (hc'.symm.trans h) (by decide), fun _ => ?_⟩
          have hconj := (conj_mem_omegaT g9A).1 hgm
          have e2 : gen 9 * (gen (sylowIdx.getD (saLab i) 0) * saElt (saPar i)) =
              gen 9 * gen (sylowIdx.getD (saLab i) 0) * (gen 9)⁻¹ * (gen 9 * saElt (saPar i)) := by
            group
          rw [e2]
          exact mul_mem hconj (ih1 rfl)

private noncomputable def mkE (Y X : Equiv.Perm (Fin 360)) (m : Nat) : Equiv.Perm (Fin 360) :=
  (if f1 m 0 = 1 then Y else 1) * (if f1 m 1 = 1 then X else 1)

private theorem actsSel {g : Equiv.Perm (Fin 360)} {M : Nat} (hg : Acts g M) (n : Nat) :
    Acts (if n = 1 then g else 1) (Bool.rec (motive := fun _ => Nat) idK M (Nat.beq n 1)) := by
  by_cases h : n = 1
  · rw [if_pos h, beqT h]; exact hg
  · rw [if_neg h, beqF h]; exact acts_idK

private theorem acts_mkE {Y X : Equiv.Perm (Fin 360)} {y x : Nat} (hY : Acts Y y) (hX : Acts X x)
    (m : Nat) : Acts (mkE Y X m) (maskK y x m) := by
  unfold maskK
  rw [matMulK_eq]
  exact acts_mul (actsSel hY _) (actsSel hX _)

private theorem mkE_mem {Y X : Equiv.Perm (Fin 360)} {E : Subgroup (Equiv.Perm (Fin 360))}
    (hY : Y ∈ E) (hX : X ∈ E) (m : Nat) : mkE Y X m ∈ E := by
  unfold mkE
  refine mul_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | assumption

private theorem mkE_sq {Y X : Equiv.Perm (Fin 360)} (hY : Y * Y = 1) (hX : X * X = 1)
    (hc : X * Y = Y * X) (m : Nat) : mkE Y X m * mkE Y X m = 1 := by
  unfold mkE
  split_ifs
  · calc Y * X * (Y * X) = Y * (X * Y) * X := by group
      _ = 1 := by rw [hc, ← mul_assoc, hY, one_mul, hX]
  · simpa using hY
  · simpa using hX
  · simp

private theorem prod_acts {S : Subgroup (Equiv.Perm (Fin 360))} {b : Nat} {F Fi : Nat → Nat} :
    ∀ n, (∀ l < n, ∃ g ∈ S, Acts g (F (Nat.add b l)) ∧ Acts g⁻¹ (Fi (Nat.add b l))) →
    ∃ g ∈ S, Acts g (prodK b F n) ∧ Acts g⁻¹ (prodRK b Fi n)
  | 0, _ => ⟨1, one_mem _, acts_idK, by rw [inv_one]; exact acts_idK⟩
  | n + 1, h => by
    obtain ⟨g, hg, a1, a2⟩ := prod_acts n fun l hl => h l (by omega)
    obtain ⟨c, hc, c1, c2⟩ := h n (by omega)
    refine ⟨g * c, mul_mem hg hc, ?_, ?_⟩
    · rw [prodK_succ]; exact acts_mul a1 c1
    · rw [prodRK_succ, mul_inv_rev]; exact acts_mul c2 a2

private theorem prod_acts' {S : Subgroup (Equiv.Perm (Fin 360))} {b : Nat} {F : Nat → Nat} :
    ∀ n, (∀ l < n, ∃ g ∈ S, Acts g (F (Nat.add b l))) → ∃ g ∈ S, Acts g (prodK b F n)
  | 0, _ => ⟨1, one_mem _, acts_idK⟩
  | n + 1, h => by
    obtain ⟨g, hg, a1⟩ := prod_acts' n fun l hl => h l (by omega)
    obtain ⟨c, hc, c1⟩ := h n (by omega)
    exact ⟨g * c, mul_mem hg hc, by rw [prodK_succ]; exact acts_mul a1 c1⟩

private theorem pow_acts {g : Equiv.Perm (Fin 360)} {x : Nat} (hg : Acts g x) :
    ∀ m, Acts (g ^ m) (powK x m)
  | 0 => by rw [pow_zero]; exact acts_idK
  | m + 1 => by rw [pow_succ, powK_succ]; exact acts_mul (pow_acts hg m) hg

end Acts

open CFSG.ComponentClassification.RankTwoSporadic CFSG.ComponentClassification.RankTwoSporadic.Cert
open scoped commutatorElement

theorem pairFacts_of_K {V A B CH PO NO : Nat} {T : ETab}
    (hroot : ∀ k < 8, ActsOn0 genArrs[k]! (saAtK V k)) (hV : T.W.G.V = V)
    (hslp : ∀ k < T.W.G.NR, slpAt V A B k = true) (hSC : T.SC = saCodes) (hYI : T.YI = yIdxT)
    (hIN : ∀ j < 38, repTypes.getD j 0 < 3 → f1 T.IN j = 1)
    (hchi : ∀ i < 8192, chiAt saParT saLabT CH i = true)
    (hscan : ∀ i < 8192, scanAt saCodes CH PO T.EI NO i = true)
    (hent : ∀ q < NO, entAt T q = true) : O8PairFacts := by
  have hs := sa_facts
  have hreg : ∀ k < T.W.G.NR, ∃ c ∈ omegaT, Acts c (saAtK T.W.G.V k) := by
    rw [hV]; exact regs hroot hslp
  have hbit := bit_spec hs hchi
  have hidK : idK < 2 ^ 64 := idK_eq ▸ idCode_lt
  intro j hj hjt Bp hB hB2 hB1 hBO hcomm
  obtain ⟨hYr, hYS⟩ := repPerm_spec hj
  have aY : Acts (repPerm j) (saMat (yIdx j)) := acts_of_rep hYr (hs.reps j hj).2
  have hY2 : repPerm j * repPerm j = 1 := by
    have := pow_orderOf_eq_one (repPerm j)
    rwa [orderOf_repPerm hj, pow_two] at this
  obtain ⟨i, hi, rfl, aB⟩ := exists_acts hs hB
  have hB2' : saElt i * saElt i = 1 := by rw [← pow_two]; exact hB2
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hB1
    rw [saElt, dif_neg fun h => absurd h.1 (Nat.lt_irrefl 0)]
  have hsq : matMulM (saMat i) (saMat i) = idCode := by
    have a := acts_mul aB aB
    rw [hB2'] at a
    exact acts_unique hs (matMulM_lt _ _) idCode_lt a acts_one
  have hbit1 : f1 CH i = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (f1_le CH i) with h | h
    · exact absurd ((hbit i hi).1 h) hBO
    · exact h
  have hmat : matMulM (saMat i) (saMat (yIdx j)) = matMulM (saMat (yIdx j)) (saMat i) := by
    have a1 := acts_mul aB aY
    rw [hcomm] at a1
    exact acts_unique hs (matMulM_lt _ _) (matMulM_lt _ _) a1 (acts_mul aY aB)
  have hsc := hscan i hi
  unfold scanAt at hsc
  simp only [sB, CFSG.KS.bAnd_iff, bImp] at hsc
  obtain ⟨hq1, hq2⟩ := hsc ⟨fun e => absurd (Nat.eq_of_beq_eq_true e) hi0,
    beqT (by rw [saAtK_saCodes, matMulK_eq, hsq, idK_eq]), beqT hbit1⟩
  have hq := Nat.blt_eq.mp hq1
  have hqi := Nat.eq_of_beq_eq_true hq2
  have hxm : saAtK T.SC (f13 T.EI (f8 PO i)) = saMat i := by rw [hSC, hqi, saAtK_saCodes]
  have hym : saAtK T.SC (ix13 T.YI j) = saMat (yIdx j) := by
    rw [hSC, hYI, saAtK_saCodes, ix13_eq]; rfl
  have he := hent _ hq
  unfold entAt at he
  simp only [sB] at he
  have hej := CFSG.KS.allN_spec he j hj
  simp only [bImp] at hej
  have hw := hej (beqT (hIN j hj hjt)) (beqT (by rw [hxm, hym, matMulK_eq, matMulK_eq]; exact hmat))
  obtain ⟨r, -, hwr⟩ := anyBlk_spec hw
  obtain ⟨-, hwit⟩ := bAndI hwr
  rw [hxm, hym] at hwit
  set E := closure ({repPerm j, saElt i} : Set (Equiv.Perm (Fin 360))) with hEdef
  have hYE : repPerm j ∈ E := subset_closure (Set.mem_insert _ _)
  have hBE : saElt i ∈ E := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hEle : E ≤ sylowT :=
    (closure_le _).2 (Set.insert_subset_iff.2 ⟨hYS, Set.singleton_subset_iff.2 hB⟩)
  have hgam : gammaE omegaT E ≤ omegaT := by
    refine iSup₂_le fun t _ => iSup_le fun _ => ?_
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    have ha' := (Subgroup.mem_inf.1 ha).1
    have hb' := (Subgroup.mem_inf.1 hb).1
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha' hb') (inv_mem ha')) (inv_mem hb')
  have hnE : nE omegaT E ≤ omegaT := by
    refine Subgroup.commutator_le.2 fun e he' g hg => ?_
    have hgO := hgam hg
    rw [commutatorElement_def]
    exact mul_mem ((conj_mem_omegaT (sylowT_le_autT (hEle he'))).1 hgO) (inv_mem hgO)
  have gfac : ∀ g, gOK T.W.G (saMat (yIdx j)) (saMat i) g = true →
      ∃ γ ∈ gammaE omegaT E, Acts γ (gVal T.W.G g) ∧ Acts γ⁻¹ (gInv T.W.G g) := by
    intro g hg
    unfold gOK at hg
    simp only [sB, CFSG.KS.bAnd_iff, bImp] at hg
    obtain ⟨ht1, ha, hai, hb, hbi, hA, hB', hAt, hBt⟩ := hg
    have at' := acts_mkE aY aB (f8 T.W.G.GT g)
    have htE := mkE_mem hYE hBE (f8 T.W.G.GT g)
    have ht2 := mkE_sq hY2 hB2' hcomm (f8 T.W.G.GT g)
    have htA := sylowT_le_autT (hEle htE)
    have hmk : maskK (saMat (yIdx j)) (saMat i) (f8 T.W.G.GT g) < 2 ^ 64 := by
      unfold maskK; rw [matMulK_eq]; exact matMulM_lt _ _
    have ht1' : mkE (repPerm j) (saElt i) (f8 T.W.G.GT g) ≠ 1 := fun e => by
      rw [e] at at'
      exact absurd (ht1 (beqT (acts_unique hs hmk hidK at' acts_idK))) (by decide)
    obtain ⟨c1, hc1, a1⟩ := hreg _ (Nat.blt_eq.mp ha)
    obtain ⟨d1, hd1, b1⟩ := hreg _ (Nat.blt_eq.mp hai)
    obtain ⟨c2, hc2, a2⟩ := hreg _ (Nat.blt_eq.mp hb)
    obtain ⟨d2, hd2, b2⟩ := hreg _ (Nat.blt_eq.mp hbi)
    have inv1 : d1 = c1⁻¹ := by
      refine eq_inv_of_mul_eq_one_right (eqΩ (mul_mem hc1 hd1) (one_mem _) ?_ acts_one)
      have := acts_mul a1 b1
      rwa [← matMulK_eq, Nat.eq_of_beq_eq_true hA, idK_eq] at this
    have inv2 : d2 = c2⁻¹ := by
      refine eq_inv_of_mul_eq_one_right (eqΩ (mul_mem hc2 hd2) (one_mem _) ?_ acts_one)
      have := acts_mul a2 b2
      rwa [← matMulK_eq, Nat.eq_of_beq_eq_true hB', idK_eq] at this
    have m1 : c1 ∈ omegaT ⊓ centralizer ({mkE (repPerm j) (saElt i) (f8 T.W.G.GT g)} :
        Set (Equiv.Perm (Fin 360))) := by
      refine Subgroup.mem_inf.2 ⟨hc1, mem_centralizer_singleton_iff.2 ?_⟩
      have := Nat.eq_of_beq_eq_true hAt
      rw [matMulK_eq, matMulK_eq] at this
      exact comm_of hc1 htA ht2 a1 at' this
    have m2 : c2 ∈ omegaT ⊓ centralizer ({mkE (repPerm j) (saElt i) (f8 T.W.G.GT g)} :
        Set (Equiv.Perm (Fin 360))) := by
      refine Subgroup.mem_inf.2 ⟨hc2, mem_centralizer_singleton_iff.2 ?_⟩
      have := Nat.eq_of_beq_eq_true hBt
      rw [matMulK_eq, matMulK_eq] at this
      exact comm_of hc2 htA ht2 a2 at' this
    have hle : centDer omegaT (mkE (repPerm j) (saElt i) (f8 T.W.G.GT g)) ≤ gammaE omegaT E :=
      le_iSup₂_of_le (f := fun t (_ : t ∈ E) => ⨆ (_ : t ≠ 1), centDer omegaT t) _ htE
        (le_iSup_of_le ht1' le_rfl)
    refine ⟨⁅c1, c2⁆, hle (commutator_mem_commutator m1 m2), ?_, ?_⟩
    · have e : ⁅c1, c2⁆ = c1 * c2 * (d1 * d2) := by rw [commutatorElement_def, inv1, inv2]; group
      rw [e]
      unfold gVal
      rw [matMulK_eq, matMulK_eq, matMulK_eq]
      exact acts_mul (acts_mul a1 a2) (acts_mul b1 b2)
    · have e : ⁅c1, c2⁆⁻¹ = c2 * c1 * (d2 * d1) := by
        rw [commutatorElement_inv, commutatorElement_def, inv1, inv2]; group
      rw [e]
      unfold gInv
      rw [matMulK_eq, matMulK_eq, matMulK_eq]
      exact acts_mul (acts_mul a2 a1) (acts_mul b2 b1)
  have nfac : ∀ f, allBlk (f16 T.W.NS f) (gOK T.W.G (saMat (yIdx j)) (saMat i)) (f8 T.W.NC f) =
      true → ∃ n ∈ nE omegaT E, Acts n (nVal T.W (saMat (yIdx j)) (saMat i) f) := by
    intro f hf
    obtain ⟨Γ, hΓ, aΓ, aΓi⟩ := prod_acts (S := gammaE omegaT E) (b := f16 T.W.NS f)
      (F := gVal T.W.G) (Fi := gInv T.W.G) (f8 T.W.NC f) fun l hl =>
        gfac _ (CFSG.KS.allBlk_spec hf l hl)
    have ae := acts_mkE aY aB (f8 T.W.NE f)
    have heE := mkE_mem hYE hBE (f8 T.W.NE f)
    have he2 := mkE_sq hY2 hB2' hcomm (f8 T.W.NE f)
    refine ⟨⁅mkE (repPerm j) (saElt i) (f8 T.W.NE f), Γ⁆, commutator_mem_commutator heE hΓ, ?_⟩
    have e : ⁅mkE (repPerm j) (saElt i) (f8 T.W.NE f), Γ⁆ =
        mkE (repPerm j) (saElt i) (f8 T.W.NE f) * Γ *
          (mkE (repPerm j) (saElt i) (f8 T.W.NE f) * Γ⁻¹) := by
      rw [commutatorElement_def, inv_eq_of_mul_eq_one_right he2]; group
    rw [e]
    unfold nVal
    simp only [sN]
    rw [matMulK_eq, matMulK_eq, matMulK_eq]
    exact acts_mul (acts_mul ae aΓ) (acts_mul ae aΓi)
  unfold witAt at hwit
  simp only [sB, CFSG.KS.bAnd_iff, bImp] at hwit
  obtain ⟨hall, hz2, hz4⟩ := hwit
  obtain ⟨W, hW, aW⟩ := prod_acts' (S := nE omegaT E) (b := f16 T.W.WS (Nat.add (f16 T.ES (f8 PO i)) r))
    (F := nVal T.W (saMat (yIdx j)) (saMat i)) _ fun l hl => nfac _ (CFSG.KS.allBlk_spec hall l hl)
  have aW' : Acts W (wVal T.W (saMat (yIdx j)) (saMat i) (Nat.add (f16 T.ES (f8 PO i)) r)) := aW
  have aZ := pow_acts aW' (f8 T.W.WM (Nat.add (f16 T.ES (f8 PO i)) r))
  set Z := W ^ f8 T.W.WM (Nat.add (f16 T.ES (f8 PO i)) r) with hZ
  have hZn : Z ∈ nE omegaT E := pow_mem hW _
  have hZO := hnE hZn
  have aZ2 := acts_mul aZ aZ
  have hZ2 : ¬ Z ^ 2 ^ 1 = 1 := fun e => by
    rw [pow_one, pow_two] at e
    rw [e] at aZ2
    have := acts_unique hs (matMulM_lt _ _) idCode_lt aZ2 acts_one
    exact absurd (hz2 (beqT (by rw [matMulK_eq, this, idK_eq]))) (by decide)
  have hZ4 : Z ^ 2 ^ (1 + 1) = 1 := by
    have a4 := acts_mul aZ2 aZ2
    have e4 := Nat.eq_of_beq_eq_true hz4
    rw [matMulK_eq, matMulK_eq, idK_eq] at e4
    rw [e4] at a4
    have := eqΩ (mul_mem (mul_mem hZO hZO) (mul_mem hZO hZO)) (one_mem _) a4 acts_one
    rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 from rfl, pow_add, pow_two]
    exact this
  refine Or.inl ⟨Z, hZn, ?_⟩
  rw [orderOf_eq_prime_pow hZ2 hZ4]
  norm_num

end CFSG.KC.O8P

end

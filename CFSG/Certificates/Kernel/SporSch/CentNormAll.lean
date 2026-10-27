module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo2Kit
public import CFSG.Certificates.Kernel.RankThree.F2Perm

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer CFSG.RankThree.Native
  CFSG.RankThree.PartOne
open CFSG.Certificates.ChainArrays

variable {n : ℕ}

theorem ptailOKQ_of_all {Q : RawSchreierDatum n} {O S : Array (Array ℕ)} {base : Array ℕ}
    {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hF : ChainCheckFacts n O S base W chunks) (hQ : ValidSchreier Q) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X) {xs : Array (Array ℕ)} {rels : List (ℕ × ℕ × ℕ)}
    {T : Array ℕ → Bool}
    (hT : ∀ (t : Array ℕ) (G : Equiv.Perm (Fin n)), Rep n t G → G ∈ Q.originalSubgroup →
      G * X = X * G → T t = true) :
    ∀ fuel i, i + fuel = Q.baseCount → ∀ (acc : Array ℕ) (A : Equiv.Perm (Fin n)), Rep n acc A →
      A ∈ Q.originalSubgroup →
      ptailOKQ n (rawLevels n S base) base x xs rels T fuel i acc = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro i _ acc A hacc hA0
    change (!(commA n acc x) || T acc) = true
    cases hc : commA n acc x
    · rfl
    · rw [Bool.not_true, Bool.false_or]
      exact hT acc A hacc hA0 ((commA_iff hacc hx).1 hc)
  | succ fuel ih =>
    intro i hi acc A hacc hA0
    change (allLt ((rawLevels n S base)[i]!).pts.size fun k =>
      !(relOK base xs rels i acc ((rawLevels n S base)[i]!).pts[k]!) ||
        ptailOKQ n (rawLevels n S base) base x xs rels T fuel (i + 1)
          (compA n acc ((rawLevels n S base)[i]!).tr[k]!)) = true
    have hib : i < Q.baseCount := by omega
    rw [allLt_iff]
    intro k hk
    have hk' : k < (lev n S base i).pts.size := hk
    have hmem : levT n S base i k ∈ Q.originalSubgroup := by
      rw [← Q.levelSubgroup_zero_eq_original hQ]
      exact Q.levelSubgroup_antitone 0 i (Nat.zero_le _) (hA.levT_mem hF hib hk')
    have h2 : ptailOKQ n (rawLevels n S base) base x xs rels T fuel (i + 1)
        (compA n acc ((rawLevels n S base)[i]!).tr[k]!) = true :=
      ih (i + 1) (by omega) _ (A * levT n S base i k) (rep_compA hacc (hA.rep_levT hF hib hk'))
        (Subgroup.mul_mem _ hA0 hmem)
    rw [h2, Bool.or_true]

theorem allLt_zero (f : ℕ → Bool) : allLt 0 f = true :=
  allLt_iff.2 fun _ hi => absurd hi (Nat.not_lt_zero _)

theorem centNormMemOKP_nil_of_all {p : ℕ} {S : Array (Array ℕ)} (hn : 1 ≤ n) (hk : 2 ≤ S.size)
    {bs : List (Fin n)} (hb : bs.Nodup) {base : Array ℕ} (hbase : base = (bs.map Fin.val).toArray)
    {W : Array (List ℤ)} {a b : Array ℕ} {A B : Equiv.Perm (Fin n)} (ha : Rep n a A)
    (hb' : Rep n b B) (hchain : caseChainOK2P n S base W a b = true) {x : Array ℕ}
    {X : Equiv.Perm (Fin n)} (hx : Rep n x X)
    (hsx : siftA n (rawLevels n S base) base 0 x = true) {M T : Array ℕ → Bool}
    (hT : ∀ (t : Array ℕ) (G : Equiv.Perm (Fin n)), Rep n t G → G ∈ closure {A, B} →
      G * X = X * G → T t = true) :
    centNormMemOKP p n S base x [] #[] M T = true := by
  subst hbase
  obtain ⟨hc, e0, e1⟩ := caseChainOK2P_parts hchain
  have hA : ChainArrays (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W) (S.extract 0 2) S
      (bs.map Fin.val).toArray W := chainArrays_ofArrays (chainCheckFacts hc).strong_inv
  have horig := originalSubgroup_ofArrays_twoP (hn := hn) (hk := hk) (hb := hb) hc ha hb' e0 e1
  have hQ := (validSchreier_of_chainOK hA (by norm_num) hc).1
  have hleaf : ∀ (t : Array ℕ) (G : Equiv.Perm (Fin n)), Rep n t G →
      G ∈ (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W).originalSubgroup → G * X = X * G →
      leafMem n #[] M T t = true := by
    intro t G ht hG hcomm
    rw [horig] at hG
    have hv : isInvA n t (invCand n t) = true := CFSG.RankThree.Native.F2.validA_of_rep ht
    have hTt := hT t G ht hG hcomm
    unfold leafMem
    simp only [hv, hTt, Bool.true_and, Bool.or_true, Bool.and_true]
    exact allLt_zero _
  have htail : ptailOKQ n (rawLevels n S (bs.map Fin.val).toArray) (bs.map Fin.val).toArray x
      (powPA p n x) [] (leafMem n #[] M T) (RawSchreierDatum.ofArrays n hn S 2 hk bs hb W).baseCount
      0 (idA n) = true :=
    ptailOKQ_of_all hA (chainCheckFacts hc) hQ hx hleaf _ 0 (Nat.zero_add _) (idA n) 1 rep_idA
      (Subgroup.one_mem _)
  rw [← hA.base_size] at htail
  have hrel : relsOKP p n (bs.map Fin.val).toArray x [] = true := List.all_nil
  unfold centNormMemOKP
  rw [hsx, htail, hrel]
  simp only [Bool.true_and, Bool.and_true]
  exact allLt_zero _

end CFSG.HardMathSupport.Dickson.I271

end

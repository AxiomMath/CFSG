module

public import CFSG.LieType.Chevalley.PinnedBridge
public import CFSG.LieType.Chevalley.RootOps.All
public import CFSG.LieType.Chevalley.BraidWalk

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.RootWalk

variable {τ : Tag}

theorem List.findIdx_congr_of_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.findIdx p = l.findIdx q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findIdx_cons, List.findIdx_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem a hx)]

theorem List.getD_idxOf {α : Type*} [BEq α] [LawfulBEq α] {l : List α} {x d : α} (h : x ∈ l) :
    l.getD (l.idxOf x) d = x := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem h), List.getElem_idxOf]

variable (τ) in
@[expose] def witnessCertPos (b : ℕ) : ℕ :=
  τ.rootCertificate.roots.idxOf (τ.witnesses.roots.getD b 0)

variable (τ) in
@[expose] def certWitnessPos (a : ℕ) : ℕ :=
  τ.witnesses.roots.idxOf (τ.rootCertificate.roots.getD a 0)

theorem witness_mem_cert
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    τ.witnesses.roots.getD b 0 ∈ τ.rootCertificate.roots := by
  obtain ⟨hwalk, -⟩ := witnessCheck_spec (τ := τ)
  have hseed : ((τ.idx (τ.witnesses.seeds.getD b 0) : Fin τ.rank) : ℕ) <
      τ.rootCertificate.roots.length :=
    lt_of_lt_of_le (Fin.is_lt _) rootCertificate_basis_table.1
  obtain ⟨hlt, -⟩ := certWalk_spec (decodeWord (τ.witnesses.words.getD b 0)) hseed
  rw [← hwalk b hb, List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

theorem witnessCertPos_lt
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    witnessCertPos τ b < τ.rootCertificate.roots.length :=
  List.idxOf_lt_length_of_mem (witness_mem_cert hb)

theorem root_witnessCertPos
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    τ.rootCertificate.root (witnessCertPos τ b) = decodeVec (τ.witnesses.roots.getD b 0) := by
  rw [RootCertificate.root, witnessCertPos, List.getD_idxOf (witness_mem_cert hb)]

theorem certWitnessPos_lt
    {a : ℕ} (ha : a < τ.rootCertificate.roots.length) :
    certWitnessPos τ a < τ.witnesses.roots.length := by
  refine List.idxOf_lt_length_of_mem ((witnessCheck_spec (τ := τ)).2 _ ?_)
  rw [List.getD_eq_getElem _ _ ha]
  exact List.getElem_mem ha

theorem decodeVec_certWitnessPos
    {a : ℕ} (ha : a < τ.rootCertificate.roots.length) :
    decodeVec (τ.witnesses.roots.getD (certWitnessPos τ a) 0) = τ.rootCertificate.root a := by
  have hmem : τ.rootCertificate.roots.getD a 0 ∈ τ.witnesses.roots := by
    refine (witnessCheck_spec (τ := τ)).2 _ ?_
    rw [List.getD_eq_getElem _ _ ha]
    exact List.getElem_mem ha
  rw [certWitnessPos, List.getD_idxOf hmem, RootCertificate.root]

theorem isRoot_decodeVec_witness
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    IsRoot τ (decodeVec (τ.witnesses.roots.getD b 0)) := by
  rw [← root_witnessCertPos hb]
  exact isRoot_rootCertificate_root (witnessCertPos_lt hb)

theorem rootPos_witness
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    RootOps.rootPos (⟨_, isRoot_decodeVec_witness hb⟩ : Root τ) = witnessCertPos τ b :=
  RootOps.rootPos_eq (witnessCertPos_lt hb) (root_witnessCertPos hb)

variable (τ) in
@[expose] def wordSignPos
    : List ℕ → ℕ → ℤ
  | [], _ => 1
  | i :: w, a => RootOps.signOf τ a (τ.idx i) *
      wordSignPos w (τ.rootCertificate.image a (τ.idx i))

theorem sign_rootOperatorFamily
    (i : Fin τ.rank) (β : Root τ) :
    (rootOperatorFamily τ).sign i β = RootOps.signOf τ (RootOps.rootPos β) i :=
  rfl

theorem wordSign_eq_wordSignPos
    (w : List ℕ) (β : Root τ) :
    (rootOperatorFamily τ).wordSign w β = wordSignPos τ w (RootOps.rootPos β) := by
  induction w generalizing β with
  | nil => rfl
  | cons i w ih =>
    rw [RootOperatorFamily.wordSign, ih, RootOps.rootPos_smul, wordSignPos,
      sign_rootOperatorFamily]

variable (τ) in
@[expose] def negBasisIndex (a : ℕ) : Option (Fin τ.rank) :=
  (List.finRange τ.rank).find? fun j => τ.rootCertificate.image j j == a

variable (τ) in
@[expose] def pinnedSignW (b : ℕ) : ℤ :=
  if witnessCertPos τ b < τ.rank then 1 else
    match negBasisIndex τ (witnessCertPos τ b) with
    | some j => -RootOps.signOf τ j j
    | none =>
      wordSignPos τ (decodeWord (τ.witnesses.words.getD
          (τ.witnesses.roots.idxOf (τ.witnesses.roots.getD b 0)) 0))
        (τ.idx (τ.witnesses.seeds.getD
          (τ.witnesses.roots.idxOf (τ.witnesses.roots.getD b 0)) 0))

theorem eq_of_decodeVec_eq
    {b m : ℕ} (hb : b < τ.witnesses.roots.length)
    (hm : m < τ.witnesses.roots.length)
    (h : decodeVec (τ := τ) (τ.witnesses.roots.getD m 0) =
      decodeVec (τ.witnesses.roots.getD b 0)) :
    τ.witnesses.roots.getD m 0 = τ.witnesses.roots.getD b 0 := by
  have hpos := rootCertificate_root_injOn (witnessCertPos_lt hm) (witnessCertPos_lt hb)
    ((root_witnessCertPos hm).trans (h.trans (root_witnessCertPos hb).symm))
  have e1 : τ.rootCertificate.roots.getD (witnessCertPos τ m) 0 = τ.witnesses.roots.getD m 0 :=
    List.getD_idxOf (witness_mem_cert hm)
  have e2 : τ.rootCertificate.roots.getD (witnessCertPos τ b) 0 = τ.witnesses.roots.getD b 0 :=
    List.getD_idxOf (witness_mem_cert hb)
  rw [← e1, ← e2, hpos]

theorem pinnedSignW_eq
    {b : ℕ} (hb : b < τ.witnesses.roots.length) :
    pinnedSignW τ b = (rootOperatorFamily τ).pinnedFamilySign
      (decodeVec (τ.witnesses.roots.getD b 0)) := by
  obtain ⟨hr, hbasis, -⟩ := rootCertificate_basis_table (τ := τ)
  have hroot := root_witnessCertPos hb
  have hlt := witnessCertPos_lt hb
  unfold pinnedSignW
  by_cases h1 : witnessCertPos τ b < τ.rank
  · rw [ite_eq_left h1]
    have hα : decodeVec (τ := τ) (τ.witnesses.roots.getD b 0) = Pi.single ⟨_, h1⟩ 1 := by
      rw [← hroot, ← hbasis ⟨_, h1⟩]
    rw [hα, RootOperatorFamily.pinnedFamilySign, pinnedData_single]
    rfl
  rw [ite_eq_right h1]
  rcases hn : negBasisIndex τ (witnessCertPos τ b) with _ | j
  ·
    have hn1 : ¬∃ j, decodeVec (τ := τ) (τ.witnesses.roots.getD b 0) = Pi.single j 1 := by
      rintro ⟨j, hj⟩
      have hj' : τ.rootCertificate.root (witnessCertPos τ b) = τ.rootCertificate.root j := by
        rw [hroot, hj, hbasis j]
      exact h1 ((rootCertificate_root_injOn hlt (lt_of_lt_of_le j.2 hr) hj') ▸ j.2)
    have hn2 : ¬∃ j, decodeVec (τ := τ) (τ.witnesses.roots.getD b 0) = -Pi.single j 1 := by
      rintro ⟨j, hj⟩
      have hj0 : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 hr
      have hj' : τ.rootCertificate.root (witnessCertPos τ b) =
          τ.rootCertificate.root (τ.rootCertificate.image j j) := by
        rw [hroot, hj, rootCertificate_root_image hj0, hbasis j, reflect_single_self]
      have heq := rootCertificate_root_injOn hlt (rootCertificate_image_lt hj0 j) hj'
      rw [negBasisIndex, List.find?_eq_none] at hn
      exact hn j (List.mem_finRange j) (by rw [heq]; exact beq_self_eq_true _)
    have hk : τ.witnesses.roots.findIdx
        (fun c => decide (decodeVec (τ := τ) c = decodeVec (τ.witnesses.roots.getD b 0))) =
          τ.witnesses.roots.idxOf (τ.witnesses.roots.getD b 0) := by
      unfold List.idxOf
      refine List.findIdx_congr_of_mem fun c hc => ?_
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
      have e : τ.witnesses.roots[m] = τ.witnesses.roots.getD m 0 :=
        (List.getD_eq_getElem _ _ hm).symm
      by_cases hceq : τ.witnesses.roots[m] = τ.witnesses.roots.getD b 0
      · rw [hceq, beq_self_eq_true]
        exact decide_eq_true rfl
      · rw [beq_false_of_ne hceq]
        refine decide_eq_false fun hdec => hceq ?_
        rw [e] at hdec ⊢
        exact eq_of_decodeVec_eq hb hm hdec
    rw [RootOperatorFamily.pinnedFamilySign, pinnedData, dite_eq_right hn1, dite_eq_right hn2]
    simp only [hk, mul_one]
    rw [wordSign_eq_wordSignPos, RootOps.rootPos_simpleRoot]
  ·
    have hj := List.find?_some hn
    simp only [beq_iff_eq] at hj
    have hj0 : (j : ℕ) < τ.rootCertificate.roots.length := lt_of_lt_of_le j.2 hr
    have hα : decodeVec (τ := τ) (τ.witnesses.roots.getD b 0) = -Pi.single j 1 := by
      rw [← hroot, ← hj, rootCertificate_root_image hj0, hbasis j, reflect_single_self]
    have hidx : τ.idx (j : ℕ) = j := Fin.ext (Nat.mod_eq_of_lt j.2)
    rw [hα, RootOperatorFamily.pinnedFamilySign, pinnedData_neg_single]
    simp only [RootOperatorFamily.wordSign, hidx, sign_rootOperatorFamily,
      RootOps.rootPos_simpleRoot, mul_one, mul_neg]

variable (τ) in
@[expose] def weylSignW
    (i : Fin τ.rank) (b : ℕ) : ℤ :=
  pinnedSignW τ b * RootOps.signOf τ (witnessCertPos τ b) i *
    pinnedSignW τ (certWitnessPos τ (τ.rootCertificate.image (witnessCertPos τ b) i))

theorem weylSignW_eq
    {b : ℕ} (hb : b < τ.witnesses.roots.length) (i : Fin τ.rank) :
    weylSignW τ i b = (rootOperatorFamily τ).pinnedFamilySign
        (decodeVec (τ.witnesses.roots.getD b 0)) *
      (rootOperatorFamily τ).sign i ⟨_, isRoot_decodeVec_witness hb⟩ *
      (rootOperatorFamily τ).pinnedFamilySign
        (reflect τ i (decodeVec (τ.witnesses.roots.getD b 0))) := by
  have hlt := witnessCertPos_lt hb
  have himg := rootCertificate_image_lt hlt i
  rw [weylSignW, pinnedSignW_eq hb, pinnedSignW_eq (certWitnessPos_lt himg),
    sign_rootOperatorFamily, rootPos_witness hb, decodeVec_certWitnessPos himg,
    rootCertificate_root_image hlt, root_witnessCertPos hb]

end CFSG.LieType.Chevalley

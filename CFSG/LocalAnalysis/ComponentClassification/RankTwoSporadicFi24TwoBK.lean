module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicSLP
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicMovedPerfect
public import CFSG.Sporadic.Th.TableSpec

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

open CFSG.Sporadic.FischerOddCore CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.Native (validA enumOK enumBfs keyA commutatorA rep_of_validA rep_of_eqA
  permsA)
open CFSG.ComponentClassification.RankTwoSporadic.Cert (regIndex inRegs powA mem_of_inRegs rep_powA)
open scoped commutatorElement

@[expose] def fi24KLetterA (z : ℤ) : Array ℕ :=
  if z = 1 then fi24KStrong[0]! else if z = -1 then invCand 504 fi24KStrong[0]!
  else if z = 2 then fi24KStrong[1]! else invCand 504 fi24KStrong[1]!

@[expose] def fi24KWordA (w : List ℤ) : Array ℕ :=
  w.foldr (fun z t => compA 504 (fi24KLetterA z) t) (idA 504)

@[expose] def fi24KdGenWords : List (List ℤ) :=
  [[1, 2, -1, -2], [1, 2, 2, -1, -2, -2], [1, 2, 2, -2, -1, -2], [1, 1, 2, -1, -2, -1],
    [2, 1, 2, -1, -2, -2]]

@[expose] def fi24KdPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

@[expose] def fi24KdChainsOK : Bool :=
  decide (5 ≤ fi24KdStrong.size) && decide (10 ≤ fi24KddStrong.size) &&
    rawChainOK 504 (fi24KdStrong.extract 0 (min 5 fi24KdStrong.size)) fi24KdStrong
      fi24KdBase.toArray fi24KdWords 4 &&
    (rawOrbitSizes 504 fi24KdStrong fi24KdBase.toArray).prod == 40131624960 &&
    rawChainOK 504 (fi24KddStrong.extract 0 (min 10 fi24KddStrong.size)) fi24KddStrong
      fi24KddBase.toArray fi24KddWords 4 &&
    (rawOrbitSizes 504 fi24KddStrong fi24KddBase.toArray).prod == 40131624960 &&
    allLt 5 (fun k => eqA 504 fi24KdStrong[k]! (fi24KWordA fi24KdGenWords[k]!)) &&
    allLt 10 (fun m => eqA 504 fi24KddStrong[m]!
      (commutatorA 504 fi24KdStrong[(fi24KdPairs[m]!).1]! fi24KdStrong[(fi24KdPairs[m]!).2]!))

@[expose] def fi24NGens : Array (Array ℕ) := (fi24NBasis.map fun j => fi24T[j]!).toArray

@[expose] def fi24NKey : List ℕ := [4, 0, 1, 2, 3, 6]

@[expose] def fi24NCert : ArrCert := enumBfs 504 fi24NGens fi24NKey 4097

@[expose] def fi24KdTreeElts (tree : Array ℕ) : Array (Array ℕ) :=
  tree.foldl (fun acc t => acc.push (compA 504 fi24KdStrong[t % 5]! acc[t / 5]!)) #[idA 504]

@[expose] def fi24Conjs (E : Array (Array ℕ)) (r : Array ℕ) : Array (Array ℕ) :=
  E.map fun g => RankThree.Native.conjA 504 g r

@[expose] def fi24KdLevels : Array Level := rawLevels 504 fi24KdStrong fi24KdBase.toArray

@[expose] def fi24NOrbElts : Array (Array (Array ℕ)) := fi24NOrbTrees.map fi24KdTreeElts

@[expose] def fi24NOrbConjs : Array (Array (Array ℕ)) :=
  (Array.range 3).map fun o => fi24Conjs fi24NOrbElts[o]! fi24NOrbReps[o]!

@[expose] def fi24NOrbIdx : Array (Std.HashMap ℕ ℕ) := fi24NOrbConjs.map (CFSG.ComponentClassification.RankTwoSporadic.Cert.regIndex 504 fi24NKey)

@[expose] def fi24NIdx : Std.HashMap ℕ ℕ := CFSG.ComponentClassification.RankTwoSporadic.Cert.regIndex 504 fi24NKey fi24NCert.pts

@[expose] def fi24ProdOK (T : Array (Array (Array ℕ))) (ix : Array (Std.HashMap ℕ ℕ))
    (o i j k : ℕ) : Bool :=
  decide (i < (T[o]!).size) && decide (j < (T[o]!).size) &&
    eqA 504 (compA 504 (T[o]!)[i]! (T[o]!)[j]!) fi24T[k]! &&
    CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey T[1]! ix[1]! fi24T[k]!

@[expose] def fi24NOK : Bool :=
  let c := fi24NCert
  let lv := fi24KdLevels
  let E := fi24NOrbTrees.map fi24KdTreeElts
  let T := (Array.range 3).map fun o => fi24Conjs E[o]! fi24NOrbReps[o]!
  let ix := T.map (CFSG.ComponentClassification.RankTwoSporadic.Cert.regIndex 504 fi24NKey)
  let ixN := CFSG.ComponentClassification.RankTwoSporadic.Cert.regIndex 504 fi24NKey c.pts
  enumOK 504 fi24NGens fi24NKey c && c.pts.size == 4096 &&
    allLt 4096 (fun i => eqA 504 (compA 504 c.pts[i]! c.pts[i]!) (idA 504)) &&
    allLt 378 (fun j => CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey c.pts ixN fi24T[j]!) &&
    allLt 12 (fun k => siftA 504 lv fi24KdBase.toArray 0 fi24NGens[k]!) &&
    allLt 3 (fun o => validA 504 fi24NOrbReps[o]! &&
      allLt (E[o]!).size fun j => validA 504 (E[o]!)[j]! &&
        siftA 504 lv fi24KdBase.toArray 0 (E[o]!)[j]!) &&
    allLt 4096 (fun i => eqA 504 c.pts[i]! (idA 504) ||
      CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey T[0]! ix[0]! c.pts[i]! || CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey T[1]! ix[1]! c.pts[i]! ||
      CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey T[2]! ix[2]! c.pts[i]!) &&
    fi24ProdOK T ix 0 0 58 340 && fi24ProdOK T ix 2 0 3 80 &&
    allLt 12 (fun k => CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey T[1]! ix[1]! fi24NGens[k]!)

@[expose] def fi24KdMover (p : ℕ) : Array ℕ := (fi24KdLevels[0]!).tr[(fi24KdLevels[0]!).pos[p]!]!

@[expose] def fi24KdStab (i : ℕ) : Array ℕ :=
  wordA 504 fi24KdStrong (rawInvs 504 fi24KdStrong) fi24KdStabWords[i]!

@[expose] def fi24KdTransOK : Bool :=
  let base := fi24KdBase.toArray
  let lv := fi24KdLevels
  let L := lv[0]!
  let w₁ := wordA 504 fi24KdStrong (rawInvs 504 fi24KdStrong) fi24KdStabWords[0]!
  let w₂ := wordA 504 fi24KdStrong (rawInvs 504 fi24KdStrong) fi24KdStabWords[1]!
  allLt 504 (fun p => validA 504 L.tr[L.pos[p]!]! && (L.tr[L.pos[p]!]!)[0]! == p &&
      siftA 504 lv base 0 L.tr[L.pos[p]!]!) &&
    validA 504 w₁ && validA 504 w₂ && siftA 504 lv base 0 w₁ && siftA 504 lv base 0 w₂ &&
    w₁[0]! == 0 && w₂[0]! == 0 && allLt 504 (fun p => p == 0 || w₁[p]! != p || w₂[p]! != p)

@[expose] def fi24QOK : Bool :=
  let c := fi24NCert
  let ixN := CFSG.ComponentClassification.RankTwoSporadic.Cert.regIndex 504 fi24NKey c.pts
  fi24QWords.all fun e => e.1.all (fun z => z == 1 || z == 2) &&
    CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey c.pts ixN (CFSG.ComponentClassification.RankTwoSporadic.Cert.powA 504 (fi24KWordA e.1) e.2)

@[expose] def fi24TwoBKCheck : Bool :=
  fi24KdChainsOK && fi24NOK && fi24KdTransOK && fi24QOK

theorem fi24TwoBKCheck_parts (h : fi24TwoBKCheck = true) :
    fi24KdChainsOK = true ∧ fi24NOK = true ∧ fi24KdTransOK = true ∧ fi24QOK = true := by
  simp only [fi24TwoBKCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem fi24KdChainsOK_facts (h : fi24KdChainsOK = true) :
    5 ≤ fi24KdStrong.size ∧ 10 ≤ fi24KddStrong.size ∧
    rawChainOK 504 (fi24KdStrong.extract 0 (min 5 fi24KdStrong.size)) fi24KdStrong
      fi24KdBase.toArray fi24KdWords 4 = true ∧
    (rawOrbitSizes 504 fi24KdStrong fi24KdBase.toArray).prod = 40131624960 ∧
    rawChainOK 504 (fi24KddStrong.extract 0 (min 10 fi24KddStrong.size)) fi24KddStrong
      fi24KddBase.toArray fi24KddWords 4 = true ∧
    (rawOrbitSizes 504 fi24KddStrong fi24KddBase.toArray).prod = 40131624960 ∧
    (∀ k < 5, eqA 504 fi24KdStrong[k]! (fi24KWordA fi24KdGenWords[k]!) = true) ∧
    ∀ m < 10, eqA 504 fi24KddStrong[m]! (commutatorA 504 fi24KdStrong[(fi24KdPairs[m]!).1]!
      fi24KdStrong[(fi24KdPairs[m]!).2]!) = true := by
  simp only [fi24KdChainsOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, fun k hk => allLt_spec h7 hk, fun m hm => allLt_spec h8 hm⟩

@[expose] noncomputable def fi24KdChain : RawSchreierDatum 504 :=
  RawSchreierDatum.ofArrays 504 (by decide) fi24KdStrong (min 5 fi24KdStrong.size)
    (Nat.min_le_right _ _) (fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7]) (by decide)
    fi24KdWords

@[expose] noncomputable def fi24Kd : Subgroup (Equiv.Perm (Fin 504)) :=
  fi24KdChain.originalSubgroup

theorem fi24KdChain_arrays (h : fi24KdChainsOK = true) : ChainArrays fi24KdChain
    (fi24KdStrong.extract 0 (min 5 fi24KdStrong.size)) fi24KdStrong fi24KdBase.toArray
      fi24KdWords := by
  have hA := chainArrays_ofArrays (n := 504) (hn := by decide) (k := min 5 fi24KdStrong.size)
    (hk := Nat.min_le_right _ _) (base := fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7])
    (hb := by decide) (W := fi24KdWords)
    (chainCheckFacts (fi24KdChainsOK_facts h).2.2.1).strong_inv
  have hb : ((fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7]).map Fin.val).toArray =
      fi24KdBase.toArray := rfl
  rw [hb] at hA
  exact hA

theorem card_fi24Kd (h : fi24KdChainsOK = true) : Nat.card fi24Kd = 40131624960 := by
  rw [fi24Kd, card_originalSubgroup_of_chainOK (fi24KdChain_arrays h) (by norm_num)
    (fi24KdChainsOK_facts h).2.2.1, (fi24KdChainsOK_facts h).2.2.2.1]

theorem mem_fi24Kd_of_siftA (h : fi24KdChainsOK = true) {g : Array ℕ}
    {G : Equiv.Perm (Fin 504)} (hG : Rep 504 g G)
    (hs : siftA 504 fi24KdLevels fi24KdBase.toArray 0 g = true) : G ∈ fi24Kd :=
  (siftA_iff_mem_originalSubgroup (fi24KdChain_arrays h) (by norm_num)
    (fi24KdChainsOK_facts h).2.2.1 hG).1 hs

theorem fi24KdStrong_valid (h : fi24KdChainsOK = true) {j : ℕ} (hj : j < fi24KdStrong.size) :
    validA 504 fi24KdStrong[j]! = true := by
  have := (chainCheckFacts (fi24KdChainsOK_facts h).2.2.1).strong_inv j hj
  rwa [rawInvs, map_getElem! hj] at this

theorem fi24Kd_eq_closure (h : fi24KdChainsOK = true) :
    fi24Kd = Subgroup.closure {g | ∃ k < 5, permOfArr 504 fi24KdStrong[k]! = g} := by
  rw [fi24Kd, RawSchreierDatum.originalSubgroup]
  congr 1
  ext g
  change g ∈ fi24KdChain.original.toList ↔ _
  rw [fi24KdChain, RawSchreierDatum.mem_ofArrays_original,
    Nat.min_eq_left (fi24KdChainsOK_facts h).1]
  rfl

theorem permOfArr_mem_fi24Kd (h : fi24KdChainsOK = true) {k : ℕ} (hk : k < 5) :
    permOfArr 504 fi24KdStrong[k]! ∈ fi24Kd := by
  rw [fi24Kd_eq_closure h]
  exact Subgroup.subset_closure ⟨k, hk, rfl⟩

@[expose] noncomputable def fi24KLetterG (z : ℤ) :
    Equiv.Perm (Fin 504) :=
  if z = 1 then fi24Sa else if z = -1 then fi24Sa⁻¹ else if z = 2 then fi24Sb else fi24Sb⁻¹

theorem rep_fi24KLetterA (z : ℤ) :
    Rep 504 (fi24KLetterA z) (fi24KLetterG z) := by
  unfold fi24KLetterA fi24KLetterG
  split_ifs
  · exact rep_fi24Sa
  · exact rep_inv_of_isInvA rep_fi24Sa (fi24K_isInvA (by norm_num))
  · exact rep_fi24Sb
  · exact rep_inv_of_isInvA rep_fi24Sb (fi24K_isInvA (by norm_num))

theorem fi24KLetterG_mem (z : ℤ) : fi24KLetterG z ∈ fi24K := by
  unfold fi24KLetterG
  split_ifs
  · exact fi24Sa_mem
  · exact fi24K.inv_mem fi24Sa_mem
  · exact fi24Sb_mem
  · exact fi24K.inv_mem fi24Sb_mem

theorem wordG_cons {G : Type*} [Group G] (g : ℤ → G) (z : ℤ) (w : List ℤ) :
    CFSG.Sporadic.Th.wordG g (z :: w) = g z * CFSG.Sporadic.Th.wordG g w := by
  simp only [CFSG.Sporadic.Th.wordG, List.map_cons, List.prod_cons]

theorem wordG_nil {G : Type*} [Group G] (g : ℤ → G) : CFSG.Sporadic.Th.wordG g [] = 1 := by
  simp only [CFSG.Sporadic.Th.wordG, List.map_nil, List.prod_nil]

theorem fi24KWordA_nil : fi24KWordA [] = idA 504 := by
  rw [fi24KWordA, List.foldr_nil]

theorem fi24KWordA_cons (z : ℤ) (w : List ℤ) :
    fi24KWordA (z :: w) = compA 504 (fi24KLetterA z) (fi24KWordA w) := by
  rw [fi24KWordA, fi24KWordA, List.foldr_cons]

theorem rep_fi24KWordA (w : List ℤ) :
    Rep 504 (fi24KWordA w) (CFSG.Sporadic.Th.wordG fi24KLetterG w) := by
  induction w with
  | nil =>
    rw [wordG_nil, fi24KWordA_nil]
    exact rep_idA
  | cons z w ih =>
    rw [wordG_cons, fi24KWordA_cons]
    exact rep_compA (rep_fi24KLetterA z) ih

theorem wordG_fi24KLetterG_mem (w : List ℤ) :
    CFSG.Sporadic.Th.wordG fi24KLetterG w ∈ fi24K := by
  induction w with
  | nil =>
    rw [wordG_nil]
    exact fi24K.one_mem
  | cons z w ih =>
    rw [wordG_cons]
    exact fi24K.mul_mem (fi24KLetterG_mem z) ih

theorem fi24KdGen_mem {k : ℕ} (hk : k < 5) :
    CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[k]! ∈ ⁅fi24K, fi24K⁆ := by
  have ha := fi24Sa_mem
  have hb := fi24Sb_mem
  have hab := fi24K.mul_mem ha hb
  have hbb := fi24K.mul_mem hb hb
  interval_cases k
  · have e : CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[0]! = ⁅fi24Sa, fi24Sb⁆ := by
      simp [fi24KdGenWords, CFSG.Sporadic.Th.wordG, fi24KLetterG, commutatorElement_def,
        mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator ha hb
  · have e : CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[1]! =
        ⁅fi24Sa, fi24Sb * fi24Sb⁆ := by
      simp [fi24KdGenWords, CFSG.Sporadic.Th.wordG, fi24KLetterG, commutatorElement_def,
        mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator ha hbb
  · have e : CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[2]! =
        ⁅fi24Sa * fi24Sb, fi24Sb⁆ := by
      simp [fi24KdGenWords, CFSG.Sporadic.Th.wordG, fi24KLetterG, commutatorElement_def,
        mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator hab hb
  · have e : CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[3]! =
        ⁅fi24Sa, fi24Sa * fi24Sb * fi24Sa⁻¹⁆ := by
      simp [fi24KdGenWords, CFSG.Sporadic.Th.wordG, fi24KLetterG, commutatorElement_def,
        mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator ha (fi24K.mul_mem hab (fi24K.inv_mem ha))
  · have e : CFSG.Sporadic.Th.wordG fi24KLetterG fi24KdGenWords[4]! =
        ⁅fi24Sb * fi24Sa * fi24Sb⁻¹, fi24Sb⁆ := by
      simp [fi24KdGenWords, CFSG.Sporadic.Th.wordG, fi24KLetterG, commutatorElement_def,
        mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator
      (fi24K.mul_mem (fi24K.mul_mem hb ha) (fi24K.inv_mem hb)) hb

theorem fi24Kd_le_commutator (h : fi24KdChainsOK = true) :
    fi24Kd ≤ ⁅fi24K, fi24K⁆ := by
  rw [fi24Kd_eq_closure h, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hv := fi24KdStrong_valid h (lt_of_lt_of_le hk (fi24KdChainsOK_facts h).1)
  rw [eq_of_eqA (rep_of_validA hv) (rep_fi24KWordA _) ((fi24KdChainsOK_facts h).2.2.2.2.2.2.1 k hk)]
  exact fi24KdGen_mem hk

theorem fi24Kd_eq (h : fi24KdChainsOK = true) :
    fi24Kd = ⁅fi24K, fi24K⁆ := by
  have hle : fi24Kd ≤ fi24K := (fi24Kd_le_commutator h).trans (Subgroup.commutator_le_self _)
  refine le_antisymm (fi24Kd_le_commutator h) (commutator_le_of_relIndex_two ?_)
  have h1 := Subgroup.card_mul_index (fi24Kd.subgroupOf fi24K)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_fi24Kd h, card_fi24K] at h1
  omega

@[expose] noncomputable def fi24KddChain : RawSchreierDatum 504 :=
  RawSchreierDatum.ofArrays 504 (by decide) fi24KddStrong (min 10 fi24KddStrong.size)
    (Nat.min_le_right _ _) (fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7]) (by decide)
    fi24KddWords

theorem fi24KddChain_arrays (h : fi24KdChainsOK = true) : ChainArrays fi24KddChain
    (fi24KddStrong.extract 0 (min 10 fi24KddStrong.size)) fi24KddStrong fi24KddBase.toArray
      fi24KddWords := by
  have hA := chainArrays_ofArrays (n := 504) (hn := by decide) (k := min 10 fi24KddStrong.size)
    (hk := Nat.min_le_right _ _) (base := fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7])
    (hb := by decide) (W := fi24KddWords)
    (chainCheckFacts (fi24KdChainsOK_facts h).2.2.2.2.1).strong_inv
  have hb : ((fi22FinList 504 (by decide) [0, 1, 2, 3, 4, 6, 7]).map Fin.val).toArray =
      fi24KddBase.toArray := rfl
  rw [hb] at hA
  exact hA

theorem fi24KdPairs_lt : ∀ m < 10, (fi24KdPairs[m]!).1 < 5 ∧ (fi24KdPairs[m]!).2 < 5 := by
  decide

theorem commutator_fi24Kd (h : fi24KdChainsOK = true) : ⁅fi24Kd, fi24Kd⁆ = fi24Kd := by
  have hf := fi24KdChainsOK_facts h
  have hcard : Nat.card fi24KddChain.originalSubgroup = 40131624960 := by
    rw [card_originalSubgroup_of_chainOK (fi24KddChain_arrays h) (by norm_num) hf.2.2.2.2.1,
      hf.2.2.2.2.2.1]
  have hle : fi24KddChain.originalSubgroup ≤ ⁅fi24Kd, fi24Kd⁆ := by
    rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro g hg
    change g ∈ fi24KddChain.original.toList at hg
    rw [fi24KddChain, RawSchreierDatum.mem_ofArrays_original, Nat.min_eq_left hf.2.1] at hg
    obtain ⟨m, hm, rfl⟩ := hg
    obtain ⟨hi, hj⟩ := fi24KdPairs_lt m hm
    have hvi := fi24KdStrong_valid h (lt_of_lt_of_le hi hf.1)
    have hvj := fi24KdStrong_valid h (lt_of_lt_of_le hj hf.1)
    have hm' : m < fi24KddStrong.size := lt_of_lt_of_le hm hf.2.1
    have hvm : validA 504 fi24KddStrong[m]! = true := by
      have := (chainCheckFacts hf.2.2.2.2.1).strong_inv m hm'
      rwa [rawInvs, map_getElem! hm'] at this
    rw [eq_of_eqA (rep_of_validA hvm) (RankThree.Native.rep_commutatorA hvi hvj)
      (hf.2.2.2.2.2.2.2 m hm)]
    exact Subgroup.commutator_mem_commutator (permOfArr_mem_fi24Kd h hi)
      (permOfArr_mem_fi24Kd h hj)
  have heq : fi24KddChain.originalSubgroup = fi24Kd :=
    Subgroup.eq_of_le_of_card_ge (hle.trans (Subgroup.commutator_le_self _))
      (by rw [hcard, card_fi24Kd h])
  exact le_antisymm (Subgroup.commutator_le_self _) (heq ▸ hle)

theorem fi24NOK_facts (h : fi24NOK = true) :
    enumOK 504 fi24NGens fi24NKey fi24NCert = true ∧ fi24NCert.pts.size = 4096 ∧
    (∀ i < 4096, eqA 504 (compA 504 fi24NCert.pts[i]! fi24NCert.pts[i]!) (idA 504) = true) ∧
    (∀ j < 378, CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey fi24NCert.pts fi24NIdx fi24T[j]! = true) ∧
    (∀ k < 12, siftA 504 fi24KdLevels fi24KdBase.toArray 0 fi24NGens[k]! = true) ∧
    (∀ o < 3, validA 504 fi24NOrbReps[o]! = true ∧ ∀ j < (fi24NOrbElts[o]!).size,
      validA 504 (fi24NOrbElts[o]!)[j]! = true ∧
        siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24NOrbElts[o]!)[j]! = true) ∧
    (∀ i < 4096, eqA 504 fi24NCert.pts[i]! (idA 504) = true ∨ ∃ o < 3,
      CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey fi24NOrbConjs[o]! fi24NOrbIdx[o]! fi24NCert.pts[i]! = true) ∧
    fi24ProdOK fi24NOrbConjs fi24NOrbIdx 0 0 58 340 = true ∧
    fi24ProdOK fi24NOrbConjs fi24NOrbIdx 2 0 3 80 = true ∧
    ∀ k < 12, CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey fi24NOrbConjs[1]! fi24NOrbIdx[1]! fi24NGens[k]! = true := by
  simp only [fi24NOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  refine ⟨h1, h2, fun i hi => allLt_spec h3 hi, fun j hj => allLt_spec h4 hj,
    fun k hk => allLt_spec h5 hk, fun o ho => ?_, fun i hi => ?_, h8, h9,
    fun k hk => allLt_spec h10 hk⟩
  · have h6o := allLt_spec h6 ho
    simp only [Bool.and_eq_true] at h6o
    refine ⟨h6o.1, fun j hj => ?_⟩
    have h6j := allLt_spec h6o.2 hj
    simp only [Bool.and_eq_true] at h6j
    exact h6j
  · have h7i := allLt_spec h7 hi
    simp only [Bool.or_eq_true] at h7i
    rcases h7i with ((h0 | h1) | h2) | h3
    · exact Or.inl h0
    · exact Or.inr ⟨0, by norm_num, h1⟩
    · exact Or.inr ⟨1, by norm_num, h2⟩
    · exact Or.inr ⟨2, by norm_num, h3⟩

theorem fi24NKey_lt : ∀ p ∈ fi24NKey, p < 504 := by decide

@[expose] noncomputable def fi24N : Subgroup (Equiv.Perm (Fin 504)) :=
  Subgroup.closure (permsA 504 fi24NGens)

theorem fi24N_spec (h : fi24NOK = true) :
    (∀ x, x ∈ fi24N ↔ ∃ i < fi24NCert.pts.size, permOfArr 504 fi24NCert.pts[i]! = x) ∧
    Nat.card fi24N = fi24NCert.pts.size ∧
    ∀ i < fi24NCert.pts.size, validA 504 fi24NCert.pts[i]! = true :=
  RankThree.Native.enumOK_spec fi24NKey_lt (fi24NOK_facts h).1

theorem card_fi24N (h : fi24NOK = true) : Nat.card fi24N = 4096 := by
  rw [(fi24N_spec h).2.1, (fi24NOK_facts h).2.1]

theorem fi24N_mul_self (h : fi24NOK = true) {x : Equiv.Perm (Fin 504)} (hx : x ∈ fi24N) :
    x * x = 1 := by
  obtain ⟨i, hi, rfl⟩ := ((fi24N_spec h).1 x).1 hx
  have hv := (fi24N_spec h).2.2 i hi
  have hi' : i < 4096 := by rw [← (fi24NOK_facts h).2.1]; exact hi
  exact eq_of_eqA (rep_compA (rep_of_validA hv) (rep_of_validA hv)) rep_idA
    ((fi24NOK_facts h).2.2.1 i hi')

theorem mem_fi24N_of_inRegs (h : fi24NOK = true) {a : Array ℕ} {X : Equiv.Perm (Fin 504)}
    (hX : Rep 504 a X) (hin : CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey fi24NCert.pts fi24NIdx a = true) :
    X ∈ fi24N := by
  obtain ⟨k, hk, he⟩ := CFSG.ComponentClassification.RankTwoSporadic.Cert.mem_of_inRegs hin
  have hv := (fi24N_spec h).2.2 k hk
  rw [eq_of_eqA hX (rep_of_validA hv) he]
  exact ((fi24N_spec h).1 _).2 ⟨k, hk, rfl⟩

theorem fi24Sj_mem_fi24N (h : fi24NOK = true) (j : Fin 378) :
    fi24Sj j ∈ fi24N :=
  mem_fi24N_of_inRegs h (rep_fi24Sj j) ((fi24NOK_facts h).2.2.2.1 j j.2)

theorem fi24NGens_size : fi24NGens.size = 12 := by
  simp [fi24NGens, fi24NBasis]

theorem fi24NGens_valid (h : fi24NOK = true) {k : ℕ} (hk : k < fi24NGens.size) :
    validA 504 fi24NGens[k]! = true :=
  RankThree.Native.enumOK_gens_valid (fi24NOK_facts h).1 hk

theorem fi24N_le_fi24Kd (hc : fi24KdChainsOK = true) (h : fi24NOK = true) : fi24N ≤ fi24Kd := by
  rw [fi24N, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < 12 := by rw [← fi24NGens_size]; exact hk
  exact mem_fi24Kd_of_siftA hc (rep_of_validA (fi24NGens_valid h hk))
    ((fi24NOK_facts h).2.2.2.2.1 k hk')

theorem fi24NOrbConjs_get {o : ℕ} (ho : o < 3) :
    fi24NOrbConjs[o]! = fi24Conjs fi24NOrbElts[o]! fi24NOrbReps[o]! := by
  rw [fi24NOrbConjs, getElem!_pos _ o (by simp [ho]), Array.getElem_map, Array.getElem_range]

theorem rep_fi24NOrbConj (hc : fi24KdChainsOK = true) (h : fi24NOK = true) {o j : ℕ}
    (ho : o < 3) (hj : j < (fi24NOrbConjs[o]!).size) :
    ∃ g ∈ fi24Kd, Rep 504 (fi24NOrbConjs[o]!)[j]! (g * permOfArr 504 fi24NOrbReps[o]! * g⁻¹) := by
  rw [fi24NOrbConjs_get ho] at hj ⊢
  have hj' : j < (fi24NOrbElts[o]!).size := by simpa [fi24Conjs] using hj
  obtain ⟨hr, he⟩ := (fi24NOK_facts h).2.2.2.2.2.1 o ho
  obtain ⟨hv, hs⟩ := he j hj'
  refine ⟨permOfArr 504 (fi24NOrbElts[o]!)[j]!, mem_fi24Kd_of_siftA hc (rep_of_validA hv) hs, ?_⟩
  rw [fi24Conjs, map_getElem! hj']
  exact RankThree.Native.rep_conjA hv (rep_of_validA hr)

theorem orbit_mem_iff (hc : fi24KdChainsOK = true) (h : fi24NOK = true)
    (M : Subgroup (Equiv.Perm (Fin 504))) (hinv : ∀ k ∈ fi24Kd, ∀ y ∈ M, k * y * k⁻¹ ∈ M)
    {o j : ℕ} (ho : o < 3) (hj : j < (fi24NOrbConjs[o]!).size) {X : Equiv.Perm (Fin 504)}
    (hX : Rep 504 (fi24NOrbConjs[o]!)[j]! X) :
    X ∈ M ↔ permOfArr 504 fi24NOrbReps[o]! ∈ M := by
  obtain ⟨g, hg, hr⟩ := rep_fi24NOrbConj hc h ho hj
  rw [hX.unique hr]
  constructor
  · intro hm
    have := hinv g⁻¹ (fi24Kd.inv_mem hg) _ hm
    rwa [inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, inv_mul_cancel,
      one_mul] at this
  · intro hm
    exact hinv g hg _ hm

theorem fi24N_irreducible (h : fi24TwoBKCheck = true) (M : Subgroup (Equiv.Perm (Fin 504)))
    (hM : M ≤ fi24N) (hinv : ∀ k ∈ fi24Kd, ∀ y ∈ M, k * y * k⁻¹ ∈ M) : M = ⊥ ∨ M = fi24N := by
  obtain ⟨hc, hN, -, -⟩ := fi24TwoBKCheck_parts h
  have hf := fi24NOK_facts hN
  have key1 : permOfArr 504 fi24NOrbReps[1]! ∈ M → fi24N ≤ M := by
    intro h1
    rw [fi24N, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 12 := by rw [← fi24NGens_size]; exact hk
    obtain ⟨j, hj, he⟩ := CFSG.ComponentClassification.RankTwoSporadic.Cert.mem_of_inRegs (hf.2.2.2.2.2.2.2.2.2 k hk')
    have hX := rep_of_eqA (rep_of_validA (fi24NGens_valid hN hk)) he
    exact (orbit_mem_iff hc hN M hinv (by norm_num) hj hX).2 h1
  have keyP : ∀ o i j k, fi24ProdOK fi24NOrbConjs fi24NOrbIdx o i j k = true → o < 3 →
      permOfArr 504 fi24NOrbReps[o]! ∈ M → permOfArr 504 fi24NOrbReps[1]! ∈ M := by
    intro o i j k hp ho hr
    simp only [fi24ProdOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨⟨⟨hi, hj⟩, he⟩, hin⟩ := hp
    obtain ⟨gi, -, hri⟩ := rep_fi24NOrbConj hc hN ho hi
    obtain ⟨gj, -, hrj⟩ := rep_fi24NOrbConj hc hN ho hj
    have hmi := (orbit_mem_iff hc hN M hinv ho hi hri).2 hr
    have hmj := (orbit_mem_iff hc hN M hinv ho hj hrj).2 hr
    have hk := rep_of_eqA (rep_compA hri hrj) he
    obtain ⟨l, hl, hel⟩ := CFSG.ComponentClassification.RankTwoSporadic.Cert.mem_of_inRegs hin
    exact (orbit_mem_iff hc hN M hinv (by norm_num) hl (rep_of_eqA hk hel)).1 (M.mul_mem hmi hmj)
  rcases M.bot_or_exists_ne_one with hbot | ⟨x, hxM, hx1⟩
  · exact Or.inl hbot
  right
  refine le_antisymm hM ?_
  obtain ⟨i, hi, rfl⟩ := ((fi24N_spec hN).1 x).1 (hM hxM)
  have hi' : i < 4096 := by rw [← hf.2.1]; exact hi
  have hv := (fi24N_spec hN).2.2 i hi
  rcases hf.2.2.2.2.2.2.1 i hi' with hid | ⟨o, ho, hin⟩
  · exact absurd (eq_of_eqA (rep_of_validA hv) rep_idA hid) hx1
  · obtain ⟨j, hj, he⟩ := CFSG.ComponentClassification.RankTwoSporadic.Cert.mem_of_inRegs hin
    have hro := (orbit_mem_iff hc hN M hinv ho hj (rep_of_eqA (rep_of_validA hv) he)).1 hxM
    apply key1
    interval_cases o
    · exact keyP 0 0 58 340 hf.2.2.2.2.2.2.2.1 (by norm_num) hro
    · exact hro
    · exact keyP 2 0 3 80 hf.2.2.2.2.2.2.2.2.1 (by norm_num) hro

theorem fi24KdTransOK_facts (h : fi24KdTransOK = true) :
    (∀ p < 504, validA 504 (fi24KdMover p) = true ∧ (fi24KdMover p)[0]! = p ∧
      siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24KdMover p) = true) ∧
    validA 504 (fi24KdStab 0) = true ∧ validA 504 (fi24KdStab 1) = true ∧
    siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24KdStab 0) = true ∧
    siftA 504 fi24KdLevels fi24KdBase.toArray 0 (fi24KdStab 1) = true ∧
    (fi24KdStab 0)[0]! = 0 ∧ (fi24KdStab 1)[0]! = 0 ∧
    ∀ p < 504, p = 0 ∨ (fi24KdStab 0)[p]! ≠ p ∨ (fi24KdStab 1)[p]! ≠ p := by
  simp only [fi24KdTransOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨fun p hp => ?_, h2, h3, h4, h5, h6, h7, fun p hp => ?_⟩
  · have := allLt_spec h1 hp
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec h8 hp
    simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
    rcases this with (h0 | h1) | h2
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)

theorem eq_one_of_commute_fi24Kd (h : fi24TwoBKCheck = true) {c : Equiv.Perm (Fin 504)}
    (hc : ∀ k ∈ fi24Kd, c * k = k * c) : c = 1 := by
  obtain ⟨hC, -, hT, -⟩ := fi24TwoBKCheck_parts h
  obtain ⟨hmov, hv1, hv2, hs1, hs2, h10, h20, hfix⟩ := fi24KdTransOK_facts hT
  have hr1 := rep_of_validA hv1
  have hr2 := rep_of_validA hv2
  have hW1 := hc _ (mem_fi24Kd_of_siftA hC hr1 hs1)
  have hW2 := hc _ (mem_fi24Kd_of_siftA hC hr2 hs2)
  have hfix0 : ∀ {W : Equiv.Perm (Fin 504)} {w : Array ℕ}, Rep 504 w W → w[0]! = 0 →
      c * W = W * c → w[(c 0 : ℕ)]! = (c 0 : ℕ) := by
    intro W w hw hw0 hcw
    have e0 : W 0 = 0 := Fin.ext (by rw [← hw 0]; simpa using hw0)
    have e := congrArg (fun f : Equiv.Perm (Fin 504) => f 0) hcw
    simp only [Equiv.Perm.mul_apply, e0] at e
    rw [hw (c 0), ← e]
  have hc0 : c 0 = 0 := by
    rcases hfix (c 0 : ℕ) (c 0).isLt with h0 | h1 | h2
    · exact Fin.ext h0
    · exact absurd (hfix0 hr1 h10 hW1) h1
    · exact absurd (hfix0 hr2 h20 hW2) h2
  ext x
  obtain ⟨hv, h0, hs⟩ := hmov x x.isLt
  have hr := rep_of_validA hv
  have hG0 : permOfArr 504 (fi24KdMover x) 0 = x :=
    Fin.ext (by rw [← hr 0]; simpa using h0)
  have e := congrArg (fun f : Equiv.Perm (Fin 504) => f 0)
    (hc _ (mem_fi24Kd_of_siftA hC hr hs))
  simp only [Equiv.Perm.mul_apply, hc0, hG0] at e
  rw [e]
  rfl

theorem fi24QOK_facts (h : fi24QOK = true) : ∀ e ∈ fi24QWords, (∀ z ∈ e.1, z = 1 ∨ z = 2) ∧
    CFSG.ComponentClassification.RankTwoSporadic.Cert.inRegs 504 fi24NKey fi24NCert.pts fi24NIdx (CFSG.ComponentClassification.RankTwoSporadic.Cert.powA 504 (fi24KWordA e.1) e.2) = true := by
  simp only [fi24QOK, List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  intro e he
  exact h e he

theorem fi24QWord_mem (h : fi24TwoBKCheck = true)
    {e : List ℤ × ℕ} (he : e ∈ fi24QWords) :
    (∀ z ∈ e.1, z = 1 ∨ z = 2) ∧ (CFSG.Sporadic.Th.wordG fi24KLetterG e.1) ^ e.2 ∈ fi24N := by
  obtain ⟨-, hN, -, hQ⟩ := fi24TwoBKCheck_parts h
  obtain ⟨h1, h2⟩ := fi24QOK_facts hQ e he
  exact ⟨h1, mem_fi24N_of_inRegs hN (CFSG.ComponentClassification.RankTwoSporadic.Cert.rep_powA (rep_fi24KWordA e.1) e.2) h2⟩

end CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime

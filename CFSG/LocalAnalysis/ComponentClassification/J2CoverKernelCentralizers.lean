module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverKernelCheck
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.ComponentClassification.J2Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.M12Cover (FourClassesLarge FourClassesLarge.of_mulEquiv
  FourClassesLarge.noNormalFour centralizerEquiv centralizerSubgroupEquiv centralizerInConjEquiv
  card_conj_eq_ncard conjClass_conj orderOf_eq_four centralizerIn_top
  card_centralizer_eq_centralizerIn)

@[expose] def OrderFourClassSizes {M : Type*} [Group M] (K : Subgroup M) (sizes : List ℕ) :
    Prop :=
  ∃ reps : List M, (∀ r ∈ reps, r ∈ K ∧ orderOf r = 4) ∧
    (∀ x ∈ K, orderOf x = 4 → ∃ r ∈ reps, x ∈ conjClass K r) ∧
    reps.Pairwise (fun r s => s ∉ conjClass K r) ∧
    reps.map (fun r => (conjClass K r).ncard) = sizes

namespace Kernel

section ClassCheck

variable {S : Array (Array ℕ)} {k : ℕ}

theorem genTbls_size (S : Array (Array ℕ)) (k : ℕ) : (genTbls S k).size = k := by
  simp [genTbls]

theorem genInvTbls_size (S : Array (Array ℕ)) (k : ℕ) : (genInvTbls S k).size = k := by
  simp [genInvTbls]

theorem genTbls_getElem! {l : ℕ} (hl : l < k) : (genTbls S k)[l]! = arrTable 315 S[l]! := by
  rw [getElem!_pos (genTbls S k) l (by rw [genTbls_size]; exact hl)]
  simp [genTbls]

theorem genInvTbls_getElem! {l : ℕ} (hl : l < k) :
    (genInvTbls S k)[l]! = arrTable 315 (invCand 315 S[l]!) := by
  rw [getElem!_pos (genInvTbls S k) l (by rw [genInvTbls_size]; exact hl)]
  simp [genInvTbls]

variable {hk : k ≤ S.size} {base : List (Fin 315)} {hb : base.Nodup} {W : Array (List ℤ)}

theorem genTbls_spec
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true) :
    ∀ l < (genTbls S k).size,
      CFSG.Sporadic.Th.Rep 315 (genTbls S k)[l]! (permOfArr 315 S[l]!) ∧
      CFSG.Sporadic.Th.Rep 315 (genInvTbls S k)[l]! (permOfArr 315 S[l]!)⁻¹ ∧
      permOfArr 315 S[l]! ∈
        (RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hb W).originalSubgroup := by
  intro l hl
  rw [genTbls_size] at hl
  have hlS : l < S.size := lt_of_lt_of_le hl hk
  have hinv := (chainCheckFacts hc).strong_inv l hlS
  rw [getElem!_rawInvs hlS] at hinv
  obtain ⟨h1, h2⟩ := rep_permOfArr hinv
  refine ⟨?_, ?_, ?_⟩
  · rw [genTbls_getElem! hl]
    exact rep_arrTable (by norm_num) h1
  · rw [genInvTbls_getElem! hl]
    exact rep_arrTable (by norm_num) h2
  · rw [ofArrays_originalSubgroup]
    exact Subgroup.subset_closure ⟨l, hl, rfl⟩

theorem orderFourClassSizes_of_classCheck
    (hc : rawChainOK 315 (S.extract 0 k) S (base.map Fin.val).toArray W 4 = true)
    {reps : List (Array ℕ)} {sizes : List ℕ}
    (h : classCheck S k (base.map Fin.val).toArray reps sizes = true) :
    OrderFourClassSizes
      (RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hb W).originalSubgroup sizes := by
  classical
  have hn : (315 : ℕ) < 2 ^ 32 := by norm_num
  set Q := RawSchreierDatum.ofArrays 315 (by norm_num) S k hk base hb W with hQdef
  set K := Q.originalSubgroup with hKdef
  have hQ : ValidSchreier Q := ofArrays_valid (by norm_num) hc
  have hg := genTbls_spec (hk := hk) (hb := hb) hc
  simp only [classCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨hok, hsz⟩, hrs⟩ := h
  have hrep : ∀ r ∈ reps, Rep 315 r (permOfArr 315 r) ∧ orderOf (permOfArr 315 r) = 4 ∧
      permOfArr 315 r ∈ K ∧
      closedOK (genTbls S k) (genInvTbls S k) (closureEntries S k r) = true := by
    intro r hr
    obtain ⟨⟨⟨hinv, hord⟩, hsift⟩, hcl⟩ := hrs r hr
    have hR := (rep_permOfArr hinv).1
    exact ⟨hR, (ordTest_iff perm_faithful (rep_arrTable hn hR) (by norm_num)).1 hord,
      (ofArrays_mem_iff (by norm_num) hc hR).1 hsift, hcl⟩
  set reps' := reps.map (permOfArr 315) with hreps'
  have htab : reps'.map toTable = reps.map (arrTable 315) := by
    rw [hreps', List.map_map]
    refine List.map_congr_left fun r hr => ?_
    rw [Function.comp_apply]
    exact toTable_eq_arrTable (hrep r hr).1
  have hcos : cosetOrderTables Q 1 4 = fourTables S (base.map Fin.val).toArray := by
    rw [cosetOrderTables, ofArrays_levelTables hc]
    rfl
  have hok' : repsOK 315 (genTbls S k) (genInvTbls S k) (cosetOrderTables Q 1 4)
      (reps'.map toTable) 4000 = true := by
    rw [htab, hcos]
    exact hok
  obtain ⟨hcov, -⟩ := exists_conj_of_repsOK hn Q hQ hg 1 (fun x hx => by simpa using hx)
    (by norm_num) reps' (fun r hr => by
      obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
      exact ⟨by simpa using (hrep r₀ hr₀).2.2.1, (hrep r₀ hr₀).2.1⟩) 4000 hok'
  simp only [repsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hok
  obtain ⟨⟨htree, hdist⟩, -⟩ := hok
  have htree' : ∀ r ∈ reps, conjTreeOK 315 (genTbls S k) (genInvTbls S k) (arrTable 315 r)
      (closureEntries S k r)
      (conjClosure 315 (genTbls S k) (genInvTbls S k) (arrTable 315 r) 4000).2.1
      (conjClosure 315 (genTbls S k) (genInvTbls S k) (arrTable 315 r) 4000).2.2 = true := by
    intro r hr
    have hmem : (arrTable 315 r,
        conjClosure 315 (genTbls S k) (genInvTbls S k) (arrTable 315 r) 4000) ∈
          List.map (fun r => (r, conjClosure 315 (genTbls S k) (genInvTbls S k) r 4000))
            (List.map (arrTable 315) reps) := by
      rw [List.mem_map]
      exact ⟨arrTable 315 r, List.mem_map_of_mem hr, rfl⟩
    have h := htree _ hmem
    dsimp only at h
    rw [closureEntries]
    exact h
  have hent : ∀ r ∈ reps, ∀ T ∈ (closureEntries S k r).toList, ∃ c ∈ K,
      CFSG.Sporadic.Th.Rep 315 T (c * permOfArr 315 r * c⁻¹) := by
    intro r hr T hT
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hT
    rw [Array.length_toList] at hj
    obtain ⟨c, hc, hrepc⟩ :=
      conjTreeOK_spec K hg (rep_arrTable hn (hrep r hr).1) (htree' r hr) j hj
    refine ⟨c, hc, ?_⟩
    rw [Array.getElem_toList]
    rwa [getElem!_pos (closureEntries S k r) j hj] at hrepc
  have hentT : ∀ r ∈ reps, ∀ T ∈ (closureEntries S k r).toList,
      CFSG.Sporadic.Th.Rep 315 T (tablePerm 315 T) := by
    intro r hr T hT
    obtain ⟨c, -, hrepc⟩ := hent r hr T hT
    rw [tablePerm_eq hrepc]
    exact hrepc
  have hzero : ∀ r ∈ reps, permOfArr 315 r ∈ (closureEntries S k r).toList.map (tablePerm 315) := by
    intro r hr
    have h := htree' r hr
    simp only [conjTreeOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h0, heq⟩, -⟩ := h
    have hrep0 := rep_of_tblEq (rep_arrTable hn (hrep r hr).1) heq
    refine List.mem_map.2 ⟨(closureEntries S k r)[0]!, ?_, tablePerm_eq hrep0⟩
    rw [getElem!_pos (closureEntries S k r) 0 h0]
    exact Array.getElem_mem_toList h0
  have hclosed : ∀ r ∈ reps, ∀ g ∈ (closureEntries S k r).toList.map (tablePerm 315), ∀ l < k,
      permOfArr 315 S[l]! * g * (permOfArr 315 S[l]!)⁻¹ ∈
        (closureEntries S k r).toList.map (tablePerm 315) ∧
      (permOfArr 315 S[l]!)⁻¹ * g * permOfArr 315 S[l]! ∈
        (closureEntries S k r).toList.map (tablePerm 315) := by
    intro r hr g hgm l hl
    obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hgm
    have hcl := (hrep r hr).2.2.2
    simp only [closedOK, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
      List.mem_range] at hcl
    have hl' : l < (genTbls S k).size := by rw [genTbls_size]; exact hl
    obtain ⟨⟨y₁, hy₁, he₁⟩, ⟨y₂, hy₂, he₂⟩⟩ := hcl T hT l hl'
    obtain ⟨hgl, hgil, -⟩ := hg l hl'
    have hTrep := hentT r hr T hT
    have h1 := rep_of_tblEq (rep_conjT hgl hgil hTrep) he₁
    have h2 := rep_of_tblEq (rep_conjT hgil (by rw [inv_inv]; exact hgl) hTrep) he₂
    rw [inv_inv] at h2
    exact ⟨List.mem_map.2 ⟨y₁, hy₁, tablePerm_eq h1⟩, List.mem_map.2 ⟨y₂, hy₂, tablePerm_eq h2⟩⟩
  have hconjK : ∀ r ∈ reps, ∀ c ∈ K, ∀ g ∈ (closureEntries S k r).toList.map (tablePerm 315),
      c * g * c⁻¹ ∈ (closureEntries S k r).toList.map (tablePerm 315) ∧
      c⁻¹ * g * c ∈ (closureEntries S k r).toList.map (tablePerm 315) := by
    intro r hr c hc
    rw [hKdef, hQdef, ofArrays_originalSubgroup] at hc
    induction hc using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      exact fun g hg => hclosed r hr g hg l hl
    | one =>
      intro g hg
      simp only [inv_one, mul_one, one_mul]
      exact ⟨hg, hg⟩
    | mul x y _ _ hx hy =>
      intro g hg
      refine ⟨?_, ?_⟩
      · have h := (hx _ (hy g hg).1).1
        rwa [show x * (y * g * y⁻¹) * x⁻¹ = x * y * g * (x * y)⁻¹ by group] at h
      · have h := (hy _ (hx g hg).2).2
        rwa [show y⁻¹ * (x⁻¹ * g * x) * y = (x * y)⁻¹ * g * (x * y) by group] at h
    | inv x _ hx =>
      intro g hg
      refine ⟨?_, ?_⟩
      · rw [inv_inv]
        exact (hx g hg).2
      · rw [inv_inv]
        exact (hx g hg).1
  have hclass : ∀ r ∈ reps, ∀ g, g ∈ conjClass K (permOfArr 315 r) ↔
      g ∈ (closureEntries S k r).toList.map (tablePerm 315) := by
    intro r hr g
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (hconjK r hr c hc _ (hzero r hr)).1
    · intro hg
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hg
      obtain ⟨c, hc, hrepc⟩ := hent r hr T hT
      exact ⟨c, hc, tablePerm_eq hrepc⟩
  have hUeq : (((reps.map (arrTable 315)).map fun T =>
      (T, conjClosure 315 (genTbls S k) (genInvTbls S k) T 4000)).flatMap
        fun c => c.2.1.toList) = reps.flatMap fun r => (closureEntries S k r).toList := by
    rw [List.flatMap_map, List.flatMap_map]
    rfl
  rw [hUeq] at hdist
  have hUrep : List.Forall₂ (CFSG.Sporadic.Th.Rep 315)
      (reps.flatMap fun r => (closureEntries S k r).toList)
      ((reps.flatMap fun r => (closureEntries S k r).toList).map (tablePerm 315)) := by
    rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun T hT => ?_
    obtain ⟨r, hr, hT⟩ := List.mem_flatMap.1 hT
    exact hentT r hr T hT
  have hnodup := nodup_of_keysDistinct hUrep hdist
  rw [List.map_flatMap, List.nodup_flatMap] at hnodup
  obtain ⟨hnd, hdisj⟩ := hnodup
  have hncard : ∀ r ∈ reps, (conjClass K (permOfArr 315 r)).ncard =
      (closureEntries S k r).size := by
    intro r hr
    have hset : conjClass K (permOfArr 315 r) =
        (((closureEntries S k r).toList.map (tablePerm 315)).toFinset :
          Set (Equiv.Perm (Fin 315))) := by
      ext g
      rw [hclass r hr g, Finset.mem_coe, List.mem_toFinset]
    rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hnd r hr), List.length_map,
      Array.length_toList]
  refine ⟨reps', fun r hr => ?_, fun x hx hx4 => ?_, ?_, ?_⟩
  · obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
    exact ⟨(hrep r₀ hr₀).2.2.1, (hrep r₀ hr₀).2.1⟩
  · obtain ⟨r, hr, c, hc, hxc⟩ := hcov x (by simpa using hx) hx4
    exact ⟨r, hr, c, hc, hxc⟩
  · rw [hreps', List.pairwise_map]
    refine hdisj.imp_of_mem fun {r s} hr hs hrs hmem => ?_
    exact List.disjoint_left.1 hrs ((hclass r hr _).1 hmem) (hzero s hs)
  · rw [← hsz, repSizes, hreps', List.map_map, List.map_map]
    refine List.map_congr_left fun r hr => ?_
    rw [Function.comp_apply, Function.comp_apply]
    exact hncard r hr

end ClassCheck

theorem relIndex_P_R : P.relIndex R = 2 := by
  have h := (P.subgroupOf R).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe P_le_R).toEquiv, card_P, card_R] at h
  change 604800 * P.relIndex R = 1209600 at h
  omega

theorem card_centralizerIn_R_le (x : Equiv.Perm (Fin 315)) :
    Nat.card (centralizerIn R x) ≤ 2 * Nat.card (centralizerIn P x) := by
  set C := centralizerIn R x with hC
  have hCP : C ⊓ P = centralizerIn P x := by
    ext g
    simp only [hC, Subgroup.mem_inf, mem_centralizerIn]
    constructor
    · rintro ⟨⟨-, h⟩, hP⟩
      exact ⟨hP, h⟩
    · rintro ⟨hP, h⟩
      exact ⟨⟨P_le_R hP, h⟩, hP⟩
  have h1 := ((C ⊓ P).subgroupOf C).card_mul_index
  have h2 : Nat.card ((C ⊓ P).subgroupOf C) = Nat.card (C ⊓ P : Subgroup (Equiv.Perm (Fin 315))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 : ((C ⊓ P).subgroupOf C).index ≤ 2 := by
    change (C ⊓ P).relIndex C ≤ 2
    rw [Subgroup.inf_relIndex_left]
    have := Subgroup.relIndex_le_of_le_right (inf_le_left : C ≤ R) (H := P)
      (by rw [relIndex_P_R]; norm_num)
    rwa [relIndex_P_R] at this
  have h4 : Nat.card (C ⊓ P : Subgroup (Equiv.Perm (Fin 315))) =
      Nat.card (centralizerIn P x) := by
    rw [hCP]
  rw [h2] at h1
  calc Nat.card C = Nat.card (C ⊓ P : Subgroup (Equiv.Perm (Fin 315))) *
        ((C ⊓ P).subgroupOf C).index := h1.symm
    _ ≤ Nat.card (C ⊓ P : Subgroup (Equiv.Perm (Fin 315))) * 2 := Nat.mul_le_mul_left _ h3
    _ = 2 * Nat.card (centralizerIn P x) := by rw [h4, mul_comm]

theorem centralizerIn_R_eq {x : Equiv.Perm (Fin 315)} {K : Subgroup (Equiv.Perm (Fin 315))}
    (hK : K ≤ centralizerIn R x) (hcard : Nat.card K = 2 * Nat.card (centralizerIn P x)) :
    centralizerIn R x = K :=
  (Subgroup.eq_of_le_of_card_ge hK (by rw [hcard]; exact card_centralizerIn_R_le x)).symm

theorem chain_facts_of_chainCheck {S : Array (Array ℕ)} {hk : 3 ≤ S.size}
    {base : List (Fin 315)} {hb : base.Nodup} {W : Array (List ℤ)} {sizes : List ℕ}
    {x : Array ℕ} {X : Equiv.Perm (Fin 315)} (hx : Rep 315 x X)
    (h : chainCheck S (base.map Fin.val).toArray W sizes x = true) :
    rawChainOK 315 (S.extract 0 3) S (base.map Fin.val).toArray W 4 = true ∧
      (RawSchreierDatum.ofArrays 315 (by norm_num) S 3 hk base hb W).originalSubgroup ≤
        centralizerIn R X ∧
      Nat.card (RawSchreierDatum.ofArrays 315 (by norm_num) S 3 hk base hb W).originalSubgroup =
        sizes.prod := by
  simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  obtain ⟨hc, hsz, h0, h1, h2, hc0, hc1, hc2⟩ := h
  refine ⟨hc, ?_, by rw [ofArrays_card (by norm_num) hc, hsz]⟩
  rw [ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hrep := rep_permOfArr_of_chainOK hc (lt_of_lt_of_le hi hk)
  rw [SetLike.mem_coe, mem_centralizerIn]
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  · exact ⟨P_le_R ((mem_P_iff hrep).1 h0), eq_of_eqA (rep_compA hrep hx) (rep_compA hx hrep) hc0⟩
  · exact ⟨P_le_R ((mem_P_iff hrep).1 h1), eq_of_eqA (rep_compA hrep hx) (rep_compA hx hrep) hc1⟩
  · exact ⟨(mem_R_iff _).2 (Or.inr ((mem_P_iff (rep_compA hrep rep_permU)).1 h2)),
      eq_of_eqA (rep_compA hrep hx) (rep_compA hx hrep) hc2⟩

@[expose] noncomputable def crAChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) crAStrong 3 (by decide) [0, 3] (by decide) crAWords

@[expose] noncomputable def crTChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) crTStrong 3 (by decide) [0, 1, 2] (by decide)
    crTWords

@[expose] noncomputable def crUChain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by norm_num) crUStrong 3 (by decide) [0, 3] (by decide) crUWords

theorem crABase_eq : (([0, 3] : List (Fin 315)).map Fin.val).toArray = crABase := rfl

theorem crTBase_eq : (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray = crTBase := rfl

theorem crUBase_eq : (([0, 3] : List (Fin 315)).map Fin.val).toArray = crUBase := rfl

theorem cent2BBase_eq : (([0, 3] : List (Fin 315)).map Fin.val).toArray = cent2BBase := rfl

theorem cent2ABase_eq : (([0, 1, 2] : List (Fin 315)).map Fin.val).toArray = cent2ABase := rfl

theorem centralizerIn_P_permA : centralizerIn P permA = cent2BChain.originalSubgroup ∧
    Nat.card (centralizerIn P permA) = 240 ∧ OrderFourClassSizes (centralizerIn P permA) [] := by
  have hc := cent2B_check.1
  have h := cpACheck_eq
  rw [cpACheck, ← cent2BBase_eq] at h
  rw [← cent2BBase_eq] at hc
  have he := inner_classes.2.2.1
  refine ⟨he, by rw [he]; exact cent2B_facts.2.1, ?_⟩
  rw [he]
  exact orderFourClassSizes_of_classCheck hc h

theorem centralizerIn_P_permTwoA : centralizerIn P permTwoA = cent2AChain.originalSubgroup ∧
    Nat.card (centralizerIn P permTwoA) = 1920 ∧
    OrderFourClassSizes (centralizerIn P permTwoA) [20, 120] := by
  have hc := cent2A_check.1
  have h := cpTCheck_eq
  rw [cpTCheck, ← cent2ABase_eq] at h
  rw [← cent2ABase_eq] at hc
  have he := inner_classes.2.2.2.2
  refine ⟨he, by rw [he]; exact cent2A_facts.2.1, ?_⟩
  rw [he]
  exact orderFourClassSizes_of_classCheck hc h

theorem card_centralizerIn_P_permU : Nat.card (centralizerIn P permU) = 336 := by
  rw [outer_classes.2.2]
  exact centOuter_facts.2.1

theorem centralizerIn_R_permA : centralizerIn R permA = crAChain.originalSubgroup ∧
    Nat.card (centralizerIn R permA) = 480 ∧
    OrderFourClassSizes (centralizerIn R permA) [60, 20, 60] := by
  have h := crACheck_eq
  simp only [crACheck, Bool.and_eq_true, ← crABase_eq] at h
  obtain ⟨hch, hcl⟩ := h
  obtain ⟨hc, hle, hcard⟩ := chain_facts_of_chainCheck (hk := by decide) (hb := by decide)
    rep_permA hch
  have hle' : crAChain.originalSubgroup ≤ centralizerIn R permA := hle
  have hcard' : Nat.card crAChain.originalSubgroup = 480 := hcard.trans (by norm_num)
  have he : centralizerIn R permA = crAChain.originalSubgroup :=
    centralizerIn_R_eq hle' (by rw [hcard', centralizerIn_P_permA.2.1])
  refine ⟨he, by rw [he]; exact hcard', ?_⟩
  rw [he]
  exact orderFourClassSizes_of_classCheck hc hcl

theorem centralizerIn_R_permTwoA : centralizerIn R permTwoA = crTChain.originalSubgroup ∧
    Nat.card (centralizerIn R permTwoA) = 3840 ∧
    OrderFourClassSizes (centralizerIn R permTwoA) [20, 120, 480, 40] := by
  have h := crTCheck_eq
  simp only [crTCheck, Bool.and_eq_true, ← crTBase_eq] at h
  obtain ⟨hch, hcl⟩ := h
  obtain ⟨hc, hle, hcard⟩ := chain_facts_of_chainCheck (hk := by decide) (hb := by decide)
    rep_permTwoA hch
  have hle' : crTChain.originalSubgroup ≤ centralizerIn R permTwoA := hle
  have hcard' : Nat.card crTChain.originalSubgroup = 3840 := hcard.trans (by norm_num)
  have he : centralizerIn R permTwoA = crTChain.originalSubgroup :=
    centralizerIn_R_eq hle' (by rw [hcard', centralizerIn_P_permTwoA.2.1])
  refine ⟨he, by rw [he]; exact hcard', ?_⟩
  rw [he]
  exact orderFourClassSizes_of_classCheck hc hcl

theorem centralizerIn_R_permU : centralizerIn R permU = crUChain.originalSubgroup ∧
    Nat.card (centralizerIn R permU) = 672 ∧
    OrderFourClassSizes (centralizerIn R permU) [42, 42] := by
  have h := crUCheck_eq
  simp only [crUCheck, Bool.and_eq_true, ← crUBase_eq] at h
  obtain ⟨hch, hcl⟩ := h
  obtain ⟨hc, hle, hcard⟩ := chain_facts_of_chainCheck (hk := by decide) (hb := by decide)
    rep_permU hch
  have hle' : crUChain.originalSubgroup ≤ centralizerIn R permU := hle
  have hcard' : Nat.card crUChain.originalSubgroup = 672 := hcard.trans (by norm_num)
  have he : centralizerIn R permU = crUChain.originalSubgroup :=
    centralizerIn_R_eq hle' (by rw [hcard', card_centralizerIn_P_permU])
  refine ⟨he, by rw [he]; exact hcard', ?_⟩
  rw [he]
  exact orderFourClassSizes_of_classCheck hc hcl

theorem fourClassesLarge_of_orderFourClassSizes {K : Subgroup (Equiv.Perm (Fin 315))}
    {sizes : List ℕ} (h : OrderFourClassSizes K sizes) (h5 : ∀ s ∈ sizes, 5 ≤ s) :
    FourClassesLarge K := by
  obtain ⟨reps, -, hcov, -, hsz⟩ := h
  intro x hx4 hx2
  have hx4' : (x : Equiv.Perm (Fin 315)) ^ 4 = 1 := by
    rw [← SubgroupClass.coe_pow, hx4, OneMemClass.coe_one]
  have hx2' : (x : Equiv.Perm (Fin 315)) ^ 2 ≠ 1 := fun h => hx2 (Subtype.ext (by
    rw [SubgroupClass.coe_pow, h, OneMemClass.coe_one]))
  obtain ⟨r, hr, c, hc, hxc⟩ := hcov x x.2 (orderOf_eq_four hx4' hx2')
  rw [card_conj_eq_ncard, hxc, conjClass_conj _ hc]
  exact h5 _ (hsz ▸ List.mem_map.2 ⟨r, hr, rfl⟩)

theorem fourClassesLarge_P_permA : FourClassesLarge (centralizerIn P permA) :=
  fourClassesLarge_of_orderFourClassSizes centralizerIn_P_permA.2.2 (by simp)

theorem fourClassesLarge_P_permTwoA : FourClassesLarge (centralizerIn P permTwoA) :=
  fourClassesLarge_of_orderFourClassSizes centralizerIn_P_permTwoA.2.2 (by simp)

theorem fourClassesLarge_R_permA : FourClassesLarge (centralizerIn R permA) :=
  fourClassesLarge_of_orderFourClassSizes centralizerIn_R_permA.2.2 (by simp)

theorem fourClassesLarge_R_permTwoA : FourClassesLarge (centralizerIn R permTwoA) :=
  fourClassesLarge_of_orderFourClassSizes centralizerIn_R_permTwoA.2.2 (by simp)

theorem fourClassesLarge_R_permU : FourClassesLarge (centralizerIn R permU) :=
  fourClassesLarge_of_orderFourClassSizes centralizerIn_R_permU.2.2 (by simp)

theorem fourClassesLarge_P {v : Equiv.Perm (Fin 315)} (hv : v ∈ P) (h2 : orderOf v = 2) :
    FourClassesLarge (centralizerIn P v) := by
  obtain ⟨r, hr, c, hc, rfl⟩ := inner_classes.1 v hv h2
  refine FourClassesLarge.of_mulEquiv (centralizerInConjEquiv P hc r).symm ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact fourClassesLarge_P_permA
  · exact fourClassesLarge_P_permTwoA

theorem fourClassesLarge_R {v : Equiv.Perm (Fin 315)} (hv : v ∈ R) (h2 : orderOf v = 2) :
    FourClassesLarge (centralizerIn R v) := by
  obtain ⟨r, hr, c, hc, rfl⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.2.2.2.2.2.2.2.2.1 v hv h2
  refine FourClassesLarge.of_mulEquiv (centralizerInConjEquiv R (P_le_R hc) r).symm ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact fourClassesLarge_R_permA
  · exact fourClassesLarge_R_permTwoA
  · exact fourClassesLarge_R_permU

end Kernel

open Kernel

theorem conj_injective_P : Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← center_P]
  intro g hg
  rw [Subgroup.mem_center_iff]
  intro h
  have h1 := congrArg (fun α : MulAut P => α h) (MonoidHom.mem_ker.1 hg)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc h * g = g * h * g⁻¹ * g := by rw [h1]
    _ = g * h := by group

@[expose] noncomputable def innerEquivP : P ≃* inner P := MonoidHom.ofInjective conj_injective_P

theorem index_inner_P : (inner P).index = 2 := card_outer_P

theorem eq_inner_or_top_P {J : Subgroup (MulAut P)} (hJ : inner P ≤ J) :
    J = inner P ∨ J = ⊤ := by
  have h := Subgroup.relIndex_mul_index hJ
  rw [index_inner_P] at h
  have hJi : J.index ∣ 2 := Dvd.intro_left _ h
  rcases (Nat.dvd_prime Nat.prime_two).1 hJi with h1 | h1
  · exact Or.inr (Subgroup.index_eq_one.1 h1)
  · left
    rw [h1] at h
    have : (inner P).relIndex J = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.1 this) hJ

theorem centralizer_inner_subgroupOf_P (J : Subgroup (MulAut P)) (hJ : inner P ≤ J) :
    Subgroup.centralizer (((inner P).subgroupOf J : Subgroup J) : Set J) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hfix : ∀ g : P, (x : MulAut P) g = g := by
    intro g
    have h1 := hx ⟨MulAut.conj g, hJ ⟨g, rfl⟩⟩
      (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact ⟨g, rfl⟩)
    have h2 : MulAut.conj g * (x : MulAut P) = (x : MulAut P) * MulAut.conj g :=
      congrArg Subtype.val h1
    have h3 : MulAut.conj ((x : MulAut P) g) = MulAut.conj g := by
      have hc : MulAut.conj ((x : MulAut P) g) =
          (x : MulAut P) * MulAut.conj g * (x : MulAut P)⁻¹ := by
        ext y
        simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, MulAut.apply_inv_self, map_inv]
      rw [hc, ← h2, mul_inv_cancel_right]
    exact conj_injective_P h3
  exact Subgroup.mem_bot.2 (Subtype.ext (MulEquiv.ext hfix))

theorem fourClassesLarge_centralizer_P (J : Subgroup (MulAut P)) (hJ : inner P ≤ J) (v : J)
    (hv : orderOf v = 2) : FourClassesLarge (Subgroup.centralizer ({v} : Set J)) := by
  rcases eq_inner_or_top_P hJ with rfl | rfl
  · refine FourClassesLarge.of_mulEquiv (centralizerEquiv innerEquivP.symm v) ?_
    refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv P (innerEquivP.symm v)) ?_
    apply fourClassesLarge_P (innerEquivP.symm v).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv]
  · refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv ⊤ v) ?_
    rw [centralizerIn_top]
    refine FourClassesLarge.of_mulEquiv (centralizerEquiv rAutEquiv.symm (v : MulAut P)) ?_
    refine FourClassesLarge.of_mulEquiv (centralizerSubgroupEquiv R (rAutEquiv.symm v)) ?_
    apply fourClassesLarge_R (rAutEquiv.symm v).2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hv]

theorem noNormalFour_centralizer_P (J : Subgroup (MulAut P)) (hJ : inner P ≤ J) (v : J)
    (hv : orderOf v = 2) : ∀ N : Subgroup (Subgroup.centralizer ({v} : Set J)), N.Normal →
      IsEmpty (N ≃* Multiplicative (ZMod 4)) ∧
      IsEmpty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4)) := by
  have := finite_mulAut_P
  exact (fourClassesLarge_centralizer_P J hJ v hv).noNormalFour

theorem oddCore_centralizer_P (J : Subgroup (MulAut P)) (hJ : inner P ≤ J) (v : J)
    (hv : orderOf v = 2) : CFSG.oddCore (Subgroup.centralizer ({v} : Set J)) = ⊥ := by
  have := finite_mulAut_P
  exact oddCore_centralizer_eq_bot_of_normal P_inner_oddCore
    (by rw [card_mulAut_P, card_P]) P_outer_oddCore ((inner P).subgroupOf J)
    ((Subgroup.subgroupOfEquivOfLe hJ).trans innerEquivP.symm)
    (centralizer_inner_subgroupOf_P J hJ) v hv

theorem card_centralizer_rConj (r : R) :
    Nat.card (Subgroup.centralizer ({rConj r} : Set (MulAut P))) =
      Nat.card (centralizerIn R (r : Equiv.Perm (Fin 315))) := by
  rw [show rConj r = rAutEquiv r from rfl,
    Nat.card_congr (centralizerEquiv rAutEquiv.symm (rAutEquiv r)).toEquiv,
    MulEquiv.symm_apply_apply, card_centralizer_eq_centralizerIn]

theorem rConj_of_mem_P {g : Equiv.Perm (Fin 315)} (hg : g ∈ P) :
    rConj ⟨g, P_le_R hg⟩ = MulAut.conj (⟨g, hg⟩ : P) := by
  ext x
  rw [rConj_apply, MulAut.conj_apply]
  rfl

theorem ctss_j2_automorphism_involution_centralizers_exclude_small_normal_four_groups :
    (∀ J : Subgroup (MulAut P), inner P ≤ J → J = inner P ∨ J = ⊤) ∧
    (∀ J : Subgroup (MulAut P), inner P ≤ J → ∀ v : J, orderOf v = 2 →
      CFSG.oddCore (Subgroup.centralizer ({v} : Set J)) = ⊥ ∧
      ∀ N : Subgroup (Subgroup.centralizer ({v} : Set J)), N.Normal →
        IsEmpty (N ≃* Multiplicative (ZMod 4)) ∧
        IsEmpty (N ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 4))) ∧
    (∀ t ∈ R, orderOf t = 2 → ∃ r ∈ [permA, permTwoA, permU], ∃ c ∈ P, t = c * r * c⁻¹) ∧
    Nat.card (centralizerIn P permA) = 240 ∧
      OrderFourClassSizes (centralizerIn P permA) [] ∧
    Nat.card (centralizerIn R permA) = 480 ∧
      OrderFourClassSizes (centralizerIn R permA) [60, 20, 60] ∧
    Nat.card (centralizerIn P permTwoA) = 1920 ∧
      OrderFourClassSizes (centralizerIn P permTwoA) [20, 120] ∧
    Nat.card (centralizerIn R permTwoA) = 3840 ∧
      OrderFourClassSizes (centralizerIn R permTwoA) [20, 120, 480, 40] ∧
    Nat.card (centralizerIn R permU) = 672 ∧
      OrderFourClassSizes (centralizerIn R permU) [42, 42] ∧
    Nat.card (Subgroup.centralizer ({MulAut.conj pa} : Set (MulAut P))) = 480 ∧
    Nat.card (Subgroup.centralizer
      ({MulAut.conj (⟨permTwoA, permTwoA_mem⟩ : P)} : Set (MulAut P))) = 3840 ∧
    rConj ⟨permU, permU_mem_R⟩ ∉ inner P ∧
    Nat.card (Subgroup.centralizer ({rConj ⟨permU, permU_mem_R⟩} : Set (MulAut P))) = 672 := by
  refine ⟨fun _ hJ => eq_inner_or_top_P hJ, fun J hJ v hv => ⟨oddCore_centralizer_P J hJ v hv,
      noNormalFour_centralizer_P J hJ v hv⟩,
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.2.2.2.2.2.2.2.2.1,
    centralizerIn_P_permA.2.1, centralizerIn_P_permA.2.2, centralizerIn_R_permA.2.1,
    centralizerIn_R_permA.2.2, centralizerIn_P_permTwoA.2.1, centralizerIn_P_permTwoA.2.2,
    centralizerIn_R_permTwoA.2.1, centralizerIn_R_permTwoA.2.2, centralizerIn_R_permU.2.1,
    centralizerIn_R_permU.2.2, ?_, ?_, ?_, ?_⟩
  · rw [show pa = ⟨permA, permA_mem⟩ from rfl, ← rConj_of_mem_P permA_mem,
      card_centralizer_rConj]
    exact centralizerIn_R_permA.2.1
  · rw [← rConj_of_mem_P permTwoA_mem, card_centralizer_rConj]
    exact centralizerIn_R_permTwoA.2.1
  · rintro ⟨g, hg⟩
    rw [← rConj_of_mem_P g.2] at hg
    have h1 := rConj_injective hg
    exact permU_not_mem (by
      have := congrArg Subtype.val h1
      simp only at this
      rw [← this]
      exact g.2)
  · rw [card_centralizer_rConj]
    exact centralizerIn_R_permU.2.1

end CFSG.ComponentClassification.J2Cover

module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Perm.ChainSpec
public import Certificates.Data.CFSGNative.SectionRank.TitsChain
public meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
import all CFSG.LieType.Simplicity.TitsBits
public import Certificates.Certificate8033
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.SectionRank.TitsOrder

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.Ree CFSG.LieType.Simplicity CFSG.LieType.Simplicity.TitsBits
  CFSG.SectionRank.TitsGen CFSG.SectionRank.Native.Tits CFSG.Sporadic.Th CFSG.Perm
  CFSG.Perm.Native
open CFSG.Sporadic.Th.Native (ap invT invOK idT Table allIn wordT)

theorem tits_chain_check : titsChainCheck = true :=
  Certificates.certificate8033

theorem titsChainCheck_parts :
    orbitOK nPts orbitPts genCols genTables = true ∧ genCols.size = 4 ∧
      (∀ s < 4, invOK nPts genTables[s]! (invT nPts genTables[s]!) = true) ∧
      chainBase.size = 4 ∧
      chainOK nPts chainLetters chainBase checkPts checkBase chainTreesT 3 = true ∧
      orbitSizes chainTreesT = [1755, 1024, 5, 4] ∧
      spanOK checkVecs (spanMasks checkVecs) = true ∧
      ∀ s : ℕ, s < 4 → chainWords[s]! = [(s : ℤ) + 1] := by
  have h := tits_chain_check
  simp only [titsChainCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, fun s hs => (allIn_eq_true.1 h3) s (Nat.zero_le _) hs, h4, h5, h6, h7,
    fun s hs => ?_⟩
  have := (allIn_eq_true.1 h8) s (Nat.zero_le _) hs
  simpa using this

theorem orbitOK_parts : orbitPts.size = nPts ∧ genTables.size = 4 ∧
    (∀ i < nPts, orbitPts[i]! < 2 ^ 52) ∧ (∀ i, i + 1 < nPts → orbitPts[i]! < orbitPts[i + 1]!) ∧
    ∀ s < 4, ∀ i < nPts, ap genTables[s]! i < nPts ∧
      orbitPts[ap genTables[s]! i]! = mv genCols[s]! orbitPts[i]! := by
  obtain ⟨h, hc, -⟩ := titsChainCheck_parts
  simp only [orbitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2.trans hc, fun i hi => ?_, fun i hi => ?_, fun s hs i hi => ?_⟩
  · simpa using (allIn_eq_true.1 h3) i (Nat.zero_le _) hi
  · simpa using (allIn_eq_true.1 h4) i (Nat.zero_le _) (by omega)
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h5) s (Nat.zero_le _) (by rw [hc]; exact hs)))
      i (Nat.zero_le _) hi
    simpa using this

section Bits

variable {K : Type} [Field K]

theorem bitK_true : bitK K true = 1 := by
  simp [bitK]

theorem bitK_false : bitK K false = 0 := by
  simp [bitK]

theorem bitVec_xorSel [CharP K 2] (f : ℕ → ℕ) (m : ℕ) :
    ∀ k, bitVec K (xorSel f m k) =
      ∑ i ∈ Finset.range k, bitK K (m.testBit i) • bitVec K (f i)
  | 0 => by rw [xorSel, Finset.sum_range_zero, bitVec_zero]
  | k + 1 => by
    rw [Finset.sum_range_succ, ← bitVec_xorSel f m k, xorSel]
    cases h : m.testBit k
    · rw [bitK_false, zero_smul, add_zero]
      rfl
    · rw [bitK_true, one_smul, ← bitVec_xor]
      rfl

theorem bitVec_eq_sum (m : ℕ) :
    bitVec K m = ∑ p ∈ Finset.range 52, bitK K (m.testBit p) • posVec ReeTag.F4.tag K p := by
  rw [bitVec]

theorem toEnd_pack_bitVec
    [CharP K 2] (L : List ℕ) (m : ℕ) :
    toEnd K (pack L) (bitVec K m) = bitVec K (mv L m) := by
  rw [mv, bitVec_xorSel, bitVec_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [map_smul, toEnd_pack_posVec K L (Finset.mem_range.1 hp)]

theorem posCoord_bitVec
    {p : ℕ} (hp : p < 52) (m : ℕ) :
    posCoord ReeTag.F4.tag K p (bitVec K m) = bitK K (m.testBit p) := by
  rw [bitVec_eq_sum, posCoord_sum_smul_posVec hp]

theorem bitVec_injective
    {a b : ℕ} (ha : a < 2 ^ 52) (hb : b < 2 ^ 52)
    (h : bitVec K a = bitVec K b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < 52
  · have := congrArg (posCoord ReeTag.F4.tag K p) h
    rw [posCoord_bitVec hp, posCoord_bitVec hp] at this
    exact bitK_injective this
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num)
      (by omega))), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right
      (by norm_num) (by omega)))]

end Bits

section Gens

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

@[expose] noncomputable def genG
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] :
    ℕ → reeFixed ReeTag.F4 K 0
  | 0 => g0 K
  | 1 => g1 K
  | 2 => z1 K
  | _ => z2 K

@[expose] noncomputable def letterG
    (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (l : ℤ) : reeFixed ReeTag.F4 K 0 :=
  if 0 < l ∧ l ≤ 4 then genG K (l.toNat - 1)
  else if l < 0 ∧ -l ≤ 4 then (genG K ((-l).toNat - 1))⁻¹ else 1

@[expose] def genWord : ℕ → List Letter
  | 0 => titsG0Word
  | 1 => titsG1Word
  | 2 => titsZ1Word
  | _ => titsZ2Word

theorem genG_eq_evalG
    (s : ℕ) : (genG K s : adjointGroup ReeTag.F4.tag K) = evalG K (genWord s) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  match s with
  | 0 => exact titsG0_eq_evalG
  | 1 => exact titsG1_eq_evalG
  | 2 => exact titsZ1_eq_evalG
  | _ + 3 => exact titsZ2_eq_evalG

theorem evalB_genWord : ∀ s < 4, evalB (genWord s) % 2 ^ 2704 = pack genCols[s]! % 2 ^ 2704 := by
  decide +kernel

theorem hasBits_genG
    {s : ℕ} (hs : s < 4) :
    HasBits K (genG K s : adjointGroup ReeTag.F4.tag K) (pack genCols[s]!) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [HasBits, genG_eq_evalG, hasBits_evalG (K := K) (genWord s),
    (toEnd_eq_toEnd_iff _ _).2 (evalB_genWord s hs)]

theorem smul_def
    (g : reeFixed ReeTag.F4 K 0) (v : RootModule ReeTag.F4.tag K) :
    g • v = (((g : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :
      Module.End K (RootModule ReeTag.F4.tag K)) v :=
  rfl

theorem genG_smul_bitVec
    {s : ℕ} (hs : s < 4) (m : ℕ) :
    genG K s • bitVec K m = bitVec K (mv genCols[s]! m) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  rw [smul_def, hasBits_genG hs, toEnd_pack_bitVec]

end Gens

section Orbit

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
noncomputable abbrev P (i : ℕ) : RootModule ReeTag.F4.tag K := bitVec K orbitPts[i]!

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem pts_lt_of_lt
    {i j : ℕ} (hij : i < j) (hj : j < nPts) : orbitPts[i]! < orbitPts[j]! := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hstep := orbitOK_parts.2.2.2.1 j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hlt | rfl
    · exact lt_trans (ih hlt (by omega)) hstep
    · exact hstep

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem P_injective
    {i j : ℕ} (hi : i < nPts) (hj : j < nPts) (h : P K i = P K j) : i = j := by
  have e := bitVec_injective (orbitOK_parts.2.2.1 i hi) (orbitOK_parts.2.2.1 j hj) h
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd e (ne_of_lt (pts_lt_of_lt hlt hj))
  · exact heq
  · exact absurd e (ne_of_gt (pts_lt_of_lt hgt hi))

theorem genG_smul_P
    {s : ℕ} (hs : s < 4) {i : ℕ} (hi : i < nPts) :
    ap genTables[s]! i < nPts ∧ genG K s • P K i = P K (ap genTables[s]! i) := by
  obtain ⟨hlt, he⟩ := orbitOK_parts.2.2.2.2 s hs i hi
  exact ⟨hlt, by rw [P, genG_smul_bitVec hs, ← he]⟩

variable (K) in
noncomputable abbrev ptSet : Set (RootModule ReeTag.F4.tag K) := P K '' Set.Iio nPts

theorem inv_smul_mem_of_finite {G Y : Type*} [Group G] [MulAction G Y] {g : G} {S : Set Y}
    (hS : S.Finite) (h : ∀ y ∈ S, g • y ∈ S) : ∀ y ∈ S, g⁻¹ • y ∈ S := by
  have hsub : (fun y => g • y) '' S ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  have himg : (fun y => g • y) '' S = S := by
    apply Set.eq_of_subset_of_ncard_le hsub _ hS
    rw [Set.ncard_image_of_injective _ (MulAction.injective g)]
  intro y hy
  rw [← himg] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  simpa using hz

theorem genG_smul_mem
    {s : ℕ} (hs : s < 4) : ∀ v ∈ ptSet K, genG K s • v ∈ ptSet K := by
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨hlt, he⟩ := genG_smul_P (K := K) hs (Set.mem_Iio.1 hi)
  exact ⟨_, hlt, he.symm⟩

theorem smul_mem_ptSet
    (hK : Nat.card K = 2) (g : reeFixed ReeTag.F4 K 0) :
    ∀ v ∈ ptSet K, g • v ∈ ptSet K := by
  have hg : g ∈ Subgroup.closure (gens K) := by
    rw [closure_titsGens_eq_top hK]; exact Subgroup.mem_top g
  have hfin : (ptSet K).Finite := (Set.finite_Iio nPts).image _
  induction hg using Subgroup.closure_induction with
  | mem z hz =>
    rcases hz with rfl | rfl | rfl | rfl
    · exact genG_smul_mem (s := 0) (by norm_num)
    · exact genG_smul_mem (s := 1) (by norm_num)
    · exact genG_smul_mem (s := 2) (by norm_num)
    · exact genG_smul_mem (s := 3) (by norm_num)
  | one => intro v hv; simpa using hv
  | mul z w _ _ hz hw =>
    intro v hv
    rw [mul_smul]
    exact hz _ (hw v hv)
  | inv z _ hz => exact inv_smul_mem_of_finite hfin hz

theorem exists_smul_P
    (hK : Nat.card K = 2) (g : reeFixed ReeTag.F4 K 0) (i : Fin nPts) :
    ∃ j : Fin nPts, P K j = g • P K i := by
  obtain ⟨j, hj, e⟩ := smul_mem_ptSet hK g _ ⟨i.val, i.isLt, rfl⟩
  exact ⟨⟨j, hj⟩, e⟩

variable (K) in
@[expose, instance_reducible] noncomputable def idxAction
    [hK : Fact (Nat.card K = 2)] :
    MulAction (reeFixed ReeTag.F4 K 0) (Fin nPts) where
  smul g i := Classical.choose (exists_smul_P hK.out g i)
  one_smul i := by
    apply Fin.ext
    apply P_injective (K := K) (Classical.choose (exists_smul_P hK.out 1 i)).isLt i.isLt
    rw [Classical.choose_spec (exists_smul_P hK.out 1 i), one_smul]
  mul_smul g h i := by
    apply Fin.ext
    apply P_injective (K := K) (Classical.choose (exists_smul_P hK.out (g * h) i)).isLt
      (Classical.choose (exists_smul_P hK.out g
        (Classical.choose (exists_smul_P hK.out h i)))).isLt
    rw [Classical.choose_spec (exists_smul_P hK.out (g * h) i),
      Classical.choose_spec (exists_smul_P hK.out g _),
      Classical.choose_spec (exists_smul_P hK.out h i), mul_smul]

attribute [local instance] idxAction

section Action

variable [hK : Fact (Nat.card K = 2)]

theorem P_smul
    (g : reeFixed ReeTag.F4 K 0) (i : Fin nPts) : P K (g • i).val = g • P K i.val :=
  Classical.choose_spec (exists_smul_P hK.out g i)

theorem idx_eq_iff
    {g : reeFixed ReeTag.F4 K 0} {i j : ℕ} (hi : i < nPts) (hj : j < nPts) :
    idx nPts g i = j ↔ g • P K i = P K j := by
  rw [idx_of_lt g hi]
  constructor
  · intro h
    rw [← P_smul g ⟨i, hi⟩, h]
  · intro h
    apply P_injective (K := K) (g • (⟨i, hi⟩ : Fin nPts)).isLt hj
    rw [P_smul g ⟨i, hi⟩]
    exact h

theorem rep_genG
    {s : ℕ} (hs : s < 4) : Rep nPts genTables[s]! (genG K s) := by
  intro i hi
  obtain ⟨hlt, he⟩ := genG_smul_P (K := K) hs hi
  exact ((idx_eq_iff hi hlt).2 he).symm

theorem rep_letterG
    (l : ℤ) : Rep nPts (letterT nPts genTables l) (letterG K l) := by
  have hsz : genTables.size = 4 := orbitOK_parts.2.1
  unfold letterT letterG
  rw [hsz]
  push_cast
  split_ifs with h1 h2
  · exact rep_genG (by omega)
  · refine Rep.inv_of_invOK (rep_genG (by omega)) ?_
    exact titsChainCheck_parts.2.2.1 _ (by omega)
  · exact Rep.idT (by norm_num [nPts])

end Action

end Orbit

attribute [local instance] idxAction

section Chain

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
@[expose] noncomputable def gs
    (j : ℕ) : reeFixed ReeTag.F4 K 0 := wordG (letterG K) chainWords[j]!

theorem chainLetters_size : chainLetters.size = 2 * chainWords.size := by
  simp [chainLetters, buildLetters]

theorem chainLetters_even {j : ℕ} (hj : j < chainWords.size) :
    chainLetters[2 * j]! = wordT nPts (letterT nPts genTables) chainWords[j]! := by
  have hlt : 2 * j < chainLetters.size := by rw [chainLetters_size]; omega
  rw [getElem!_pos chainLetters (2 * j) hlt]
  simp only [chainLetters, buildLetters, Array.getElem_ofFn]
  rw [ite_eq_left (by omega)]
  congr 2
  omega

theorem rep_chainLetters
    [Fact (Nat.card K = 2)] :
    ∀ j < chainLetters.size / 2, Rep nPts chainLetters[2 * j]! (gs K j) := by
  intro j hj
  rw [chainLetters_size] at hj
  rw [chainLetters_even (by omega)]
  exact Rep.wordT (by norm_num [nPts]) _ fun l _ => rep_letterG l

theorem sep
    [Fact (Nat.card K = 2)] (g : reeFixed ReeTag.F4 K 0)
    (hg : ∀ t < checkPts.size, idx nPts g checkPts[t]! = checkPts[t]!) : g = 1 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨-, -, -, -, hch, -, hspan, -⟩ := titsChainCheck_parts
  have hQ := (chainOK_parts hch).2.2.2.2.1
  have hfix : ∀ t < checkVecs.size, g • bitVec K checkVecs[t]! = bitVec K checkVecs[t]! := by
    intro t ht
    have ht' : t < checkPts.size := by simpa [checkVecs] using ht
    have hlt := hQ t ht'
    have e : checkVecs[t]! = orbitPts[checkPts[t]!]! := by
      rw [checkVecs, getElem!_pos (checkPts.map fun i => orbitPts[i]!) t (by simpa using ht'),
        Array.getElem_map, getElem!_pos checkPts t ht']
    rw [e]
    exact (idx_eq_iff hlt hlt).1 (hg t ht')
  have hsum : ∀ (m k : ℕ), k ≤ checkVecs.size →
      g • bitVec K (xorSel (fun t => checkVecs[t]!) m k) =
        bitVec K (xorSel (fun t => checkVecs[t]!) m k) := by
    intro m k hk
    rw [bitVec_xorSel, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [smul_comm, hfix t (by have := Finset.mem_range.1 ht; omega)]
  have hbasis : ∀ c < 52, g • posVec ReeTag.F4.tag K c = posVec ReeTag.F4.tag K c := by
    intro c hc
    have h1 : xorSel (fun t => checkVecs[t]!) (spanMasks checkVecs)[c]! checkVecs.size = 2 ^ c := by
      have := (allIn_eq_true.1 hspan) c (Nat.zero_le _) hc
      simpa using this
    have := hsum (spanMasks checkVecs)[c]! checkVecs.size le_rfl
    rwa [h1, bitVec_two_pow hc] at this
  have hend : (((g : adjointGroup ReeTag.F4.tag K) : ModGL ReeTag.F4.tag K) :
      Module.End K (RootModule ReeTag.F4.tag K)) = 1 := by
    refine ext_posVec fun p hp => ?_
    rw [Module.End.one_apply]
    exact hbasis p (by rwa [dim_F4] at hp)
  exact Subtype.ext (Subtype.ext (Units.ext hend))

theorem levelGroup_zero
    (hK : Nat.card K = 2) :
    levelGroup chainLetters chainBase (pairG (gs K)) 0 = ⊤ := by
  rw [eq_top_iff, ← closure_titsGens_eq_top hK, Subgroup.closure_le]
  have hw := titsChainCheck_parts.2.2.2.2.2.2.2
  have hsz : 8 ≤ chainLetters.size := by
    rw [chainLetters_size]
    have : 4 ≤ chainWords.size := by
      by_contra h
      have := hw 3 (by norm_num)
      rw [getElem!_neg chainWords 3 (by omega)] at this
      simp at this
    omega
  have key : ∀ s < 4, genG K s ∈ levelGroup chainLetters chainBase (pairG (gs K)) 0 := by
    intro s hs
    have h : pairG (gs K) (2 * s) = genG K s := by
      rw [pairG, ite_eq_left (by omega), show 2 * s / 2 = s by omega, gs, hw s hs]
      simp only [wordG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      unfold letterG
      rw [ite_eq_left (by omega)]
      congr 1
    rw [← h]
    exact lG_mem (mem_levelLetters_zero.2 (by omega))
  rintro _ (rfl | rfl | rfl | rfl)
  · exact key 0 (by norm_num)
  · exact key 1 (by norm_num)
  · exact key 2 (by norm_num)
  · exact key 3 (by norm_num)

theorem prod_orbit_lengths :
    ∏ l ∈ Finset.Ico 0 chainBase.size, chainTreesT[l]!.pts.size = 35942400 := by
  obtain ⟨-, -, -, hb, -, ho, -⟩ := titsChainCheck_parts
  have hlen : chainTreesT.size = 4 := by
    have := congrArg List.length ho
    simpa [orbitSizes] using this
  have hval : ∀ l < 4, chainTreesT[l]!.pts.size = [1755, 1024, 5, 4][l]! := by
    intro l hl
    rw [← ho, orbitSizes, getElem!_pos chainTreesT l (by omega)]
    rw [getElem!_pos _ l (by simp [hlen]; omega)]
    simp
  have hs : ∀ l ∈ Finset.Ico 0 chainBase.size,
      chainTreesT[l]!.pts.size = [1755, 1024, 5, 4][l]! := fun l hl =>
    hval l (hb ▸ (Finset.mem_Ico.1 hl).2)
  rw [Finset.prod_congr rfl hs, hb]
  decide

end Chain

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem Tits_card
    (hK : Nat.card K = 2) : Nat.card (reeFixed ReeTag.F4 K 0) = 35942400 := by
  have : Fact (Nat.card K = 2) := ⟨hK⟩
  obtain ⟨-, -, -, -, hch, -⟩ := titsChainCheck_parts
  have h := (chain_facts (rep_chainLetters (K := K)) sep hch).2.2 0 (Nat.zero_le _)
  rw [levelGroup_zero hK, Subgroup.card_top, prod_orbit_lengths] at h
  exact h

theorem Tits_commutator_card_dvd
    (hK : Nat.card K = 2) :
    Nat.card (commutator (reeFixed ReeTag.F4 K 0)) ∣ 35942400 :=
  Tits_card hK ▸ Subgroup.card_subgroup_dvd_card _

end CFSG.SectionRank.TitsOrder

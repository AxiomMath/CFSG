module

public import CFSG.ClassicalInvolution.SmallCases.Sporadic.Assembly
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.J3Check
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.Sporadic.J3
import all CFSG.Blueprint.NativeSporadic
import CFSG.Certificates.Kernel.Spor.RawTreeDefs
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.ChainTools
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutTables
public import CFSG.Sporadic.Schreier.RuEnum
public import Certificates.Data.CFSGNative.Co3Schreier.Orbit

public section

namespace CFSG.ClassicalInvolution

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier.Co3.Native CFSG.ClassicalInvolution.J3Data
  CFSG.ComponentClassification.J2Cover
open CFSG.Sporadic.Schreier (centralizerIn mem_centralizerIn)
open scoped Pointwise

namespace J3Proof

@[expose] noncomputable def pa : Equiv.Perm (Fin 20520) := J3Groups.pa

@[expose] noncomputable def pb : Equiv.Perm (Fin 20520) := J3Groups.pb

@[expose] noncomputable def P3 : Subgroup (Equiv.Perm (Fin 20520)) := J3Groups.P

theorem rep_pa : Rep 20520 abArr[0]! pa := (rep_permOfArr (ab_check 0 (by norm_num))).1

theorem rep_pb : Rep 20520 abArr[1]! pb := (rep_permOfArr (ab_check 1 (by norm_num))).1

theorem pa_mem : pa ∈ P3 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem pb_mem : pb ∈ P3 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem abArr_size : abArr.size = 2 := rfl

theorem abArr_rep : ∀ h < 2, Rep 20520 abArr[h]! (permOfArr 20520 abArr[h]!) := fun h hh =>
  (rep_permOfArr (ab_check h hh)).1

theorem abInv_rep : ∀ h < 2, Rep 20520 abInv[h]! (permOfArr 20520 abArr[h]!)⁻¹ := fun h hh =>
  (rep_permOfArr (ab_check h hh)).2

theorem ab_mem : ∀ h < 2, permOfArr 20520 abArr[h]! ∈ P3 := by
  intro h hh
  interval_cases h
  · exact pa_mem
  · exact pb_mem

theorem mem_of_lt {α : Type*} [Inhabited α] (l : List α) {i : ℕ} (hi : i < l.length) :
    l[i]! ∈ l := by
  rw [getElem!_pos l i hi]
  exact List.getElem_mem hi

theorem getElem!_map_toArray {α β : Type} [Inhabited α] [Inhabited β] (f : α → β) (l : List α)
    {i : ℕ} (hi : i < l.length) : (l.map f).toArray[i]! = f l[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), getElem!_pos l i hi]
  simp

theorem permOfArr_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin 20520)} (ht : Rep 20520 t g) :
    permOfArr 20520 t = g := by
  have hc : (∀ i < 20520, t[i]! < 20520) ∧ ∀ i < 20520, ∀ j < 20520, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => ht.lt hi, fun i hi j hj hij => ?_⟩
    rw [ht.apply hi, ht.apply hj] at hij
    exact congrArg Fin.val (g.injective (Fin.ext hij))
  refine Equiv.ext fun x => Fin.ext ?_
  rw [permOfArr, dite_eq_left hc]
  exact ht x

theorem rep_word_mem {S Sinv : Array (Array ℕ)} {gs : ℕ → Equiv.Perm (Fin 20520)} {j : ℕ}
    {H : Subgroup (Equiv.Perm (Fin 20520))} (hS : ∀ h < j, Rep 20520 S[h]! (gs h))
    (hSinv : ∀ h < j, Rep 20520 Sinv[h]! (gs h)⁻¹) (hH : ∀ h < j, gs h ∈ H) {w : List ℤ}
    (hw : lettersOK j w = true) :
    Rep 20520 (wordA 20520 S Sinv w) (permOfArr 20520 (wordA 20520 S Sinv w)) ∧
      permOfArr 20520 (wordA 20520 S Sinv w) ∈ H := by
  obtain ⟨g, hg, hrep⟩ := exists_rep_wordA hS hSinv hH w hw
  rw [permOfArr_eq_of_rep hrep]
  exact ⟨hrep, hg⟩

theorem kWordsAB_length : kWordsAB.length = 2 := rfl

theorem kStrong_size : kStrong.size = 2 := by
  unfold kStrong
  simp [kWordsAB_length]

theorem kStrong_get (i : ℕ) (hi : i < 2) : kStrong[i]! = wordA 20520 abArr abInv kWordsAB[i]! :=
  getElem!_map_toArray _ _ (by rw [kWordsAB_length]; exact hi)

theorem kWords_ok (i : ℕ) (hi : i < 2) : lettersOK 2 kWordsAB[i]! = true := by
  interval_cases i <;> decide +kernel

@[expose] noncomputable def kChain : RawSchreierDatum 20520 :=
  RawSchreierDatum.ofArrays 20520 (by norm_num) kStrong 2 (le_of_eq kStrong_size.symm)
    [0, 1, 2] (by decide) kDeriv

theorem kChain_eq : kChain.originalSubgroup = J3Groups.K := by
  rw [kChain, ofArrays_originalSubgroup]
  rfl

theorem card_kChain : Nat.card kChain.originalSubgroup = 1920 := by
  rw [kChain_eq]
  exact cent_check.1

theorem kGen_rep (i : ℕ) (hi : i < 2) :
    Rep 20520 kStrong[i]! (permOfArr 20520 kStrong[i]!) := by
  rw [kStrong_get i hi]
  exact (rep_word_mem (gs := fun h => permOfArr 20520 abArr[h]!) (H := P3) abArr_rep abInv_rep
    ab_mem (kWords_ok i hi)).1

theorem kInv_rep (i : ℕ) (hi : i < 2) :
    Rep 20520 kInv[i]! (permOfArr 20520 kStrong[i]!)⁻¹ := by
  have e : kInv[i]! = invCand 20520 kStrong[i]! := by
    unfold kInv
    rw [getElem!_pos _ i (by simp [kStrong_size, hi]),
      getElem!_pos kStrong i (by rw [kStrong_size]; exact hi), Array.getElem_map]
  rw [e]
  exact CFSG.KS.Raw.rep_invCand (kGen_rep i hi)

theorem kGen_mem_P3 (i : ℕ) (hi : i < 2) : permOfArr 20520 kStrong[i]! ∈ P3 := by
  rw [kStrong_get i hi]
  exact (rep_word_mem (gs := fun h => permOfArr 20520 abArr[h]!) abArr_rep abInv_rep ab_mem
    (kWords_ok i hi)).2

theorem kGen_mem_K : ∀ h < 2, permOfArr 20520 kStrong[h]! ∈ kChain.originalSubgroup := by
  intro h hh
  rw [kChain, ofArrays_originalSubgroup]
  exact Subgroup.subset_closure ⟨h, hh, rfl⟩

theorem kChain_le_cent : kChain.originalSubgroup ≤ centralizerIn P3 pa := by
  intro g hg
  have hgK : g ∈ J3Groups.K := by rwa [← kChain_eq]
  rw [mem_centralizerIn]
  refine ⟨?_, cent_check.2.1 g hgK⟩
  rw [kChain, ofArrays_originalSubgroup] at hg
  refine (Subgroup.closure_le P3).2 ?_ hg
  rintro _ ⟨i, hi, rfl⟩
  exact kGen_mem_P3 i hi

theorem kChain_le_P3 : kChain.originalSubgroup ≤ P3 := fun _ hx =>
  (mem_centralizerIn.1 (kChain_le_cent hx)).1

theorem centralizerIn_P3 (_hP : Nat.card P3 = 50232960) :
    centralizerIn P3 pa = kChain.originalSubgroup := by
  refine le_antisymm (fun g hg => ?_) kChain_le_cent
  rw [mem_centralizerIn] at hg
  rw [kChain_eq]
  exact cent_check.2.2 g hg.1 hg.2

theorem uWordsK_length : uWordsK.length = 4 := rfl

theorem uStrong_get (i : ℕ) (hi : i < 4) : uStrong[i]! = wordA 20520 kStrong kInv uWordsK[i]! :=
  getElem!_map_toArray _ _ (by rw [uWordsK_length]; exact hi)

theorem uWords_ok (i : ℕ) (hi : i < 4) : lettersOK 2 uWordsK[i]! = true := by
  interval_cases i <;> decide +kernel

theorem uGen_mem_K (i : ℕ) (hi : i < 4) :
    permOfArr 20520 uStrong[i]! ∈ kChain.originalSubgroup := by
  rw [uStrong_get i hi]
  exact (rep_word_mem (gs := fun h => permOfArr 20520 kStrong[h]!) kGen_rep kInv_rep kGen_mem_K
    (uWords_ok i hi)).2

theorem U_structure :
    ∃ U : Subgroup (Equiv.Perm (Fin 20520)), U ≤ kChain.originalSubgroup ∧
      kChain.originalSubgroup ≤ Subgroup.normalizer (U : Set (Equiv.Perm (Fin 20520))) ∧
      IsPGroup 2 U ∧
      kChain.originalSubgroup ⊓ Subgroup.centralizer (U : Set (Equiv.Perm (Fin 20520))) ≤ U := by
  obtain ⟨hnorm, hcard, hcent⟩ := u_check
  refine ⟨J3Groups.U, ?_, ?_, IsPGroup.of_card (n := 5) (by rw [hcard]; norm_num), ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, rfl⟩
    exact uGen_mem_K i hi
  · rw [kChain_eq]
    exact hnorm
  · rintro g ⟨hgK, hgC⟩
    rw [kChain_eq] at hgK
    exact hcent g hgK fun u hu => (Subgroup.mem_centralizer_iff.1 hgC u hu).symm

theorem sWordsK_length : sWordsK.length = 4 := rfl

theorem sStrong_size : sStrong.size = 4 := by
  unfold sStrong
  simp [sWordsK_length]

theorem sStrong_get (i : ℕ) (hi : i < 4) : sStrong[i]! = wordA 20520 kStrong kInv sWordsK[i]! :=
  getElem!_map_toArray _ _ (by rw [sWordsK_length]; exact hi)

theorem sWords_ok (i : ℕ) (hi : i < 4) : lettersOK 2 sWordsK[i]! = true := by
  interval_cases i <;> decide +kernel

@[expose] noncomputable def sChain : RawSchreierDatum 20520 :=
  RawSchreierDatum.ofArrays 20520 (by norm_num) sStrong 4 (le_of_eq sStrong_size.symm)
    [0, 1, 2] (by decide) sDeriv

theorem sChain_ok : rawChainOK 20520 (sStrong.extract 0 4) sStrong
    (([0, 1, 2] : List (Fin 20520)).map Fin.val).toArray sDeriv 4 = true := sChain_check.1

theorem card_sChain : Nat.card sChain.originalSubgroup = 128 := by
  rw [sChain, ofArrays_card (by norm_num) sChain_ok]
  exact (congrArg List.prod sChain_check.2).trans (by norm_num)

theorem sGen_rep (i : ℕ) (hi : i < 4) :
    Rep 20520 sStrong[i]! (permOfArr 20520 sStrong[i]!) :=
  rep_permOfArr_of_chainOK sChain_ok (by rw [sStrong_size]; exact hi)

theorem sGen_mem_K (i : ℕ) (hi : i < 4) :
    permOfArr 20520 sStrong[i]! ∈ kChain.originalSubgroup := by
  rw [sStrong_get i hi]
  exact (rep_word_mem (gs := fun h => permOfArr 20520 kStrong[h]!) kGen_rep kInv_rep kGen_mem_K
    (sWords_ok i hi)).2

theorem sChain_le_P3 : sChain.originalSubgroup ≤ P3 := by
  rw [sChain, ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact kChain_le_P3 (sGen_mem_K i hi)

theorem cover_S : ∀ s ∈ sChain.originalSubgroup, orderOf s = 2 →
    ∃ c ∈ P3, s = c * pa * c⁻¹ := by
  intro s hs ho
  rw [sChain, ofArrays_originalSubgroup] at hs
  exact cover_check s hs ho

theorem noNonsolvableClassical_P3 (hP : Nat.card P3 = 50232960) : NoNonsolvableClassical P3 := by
  have hS2 : IsPGroup 2 sChain.originalSubgroup :=
    IsPGroup.of_card (n := 7) (by rw [card_sChain]; norm_num)
  have hidx : ¬ 2 ∣ (sChain.originalSubgroup.subgroupOf P3).index := by
    have h := (sChain.originalSubgroup.subgroupOf P3).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe sChain_le_P3).toEquiv, card_sChain, hP]
      at h
    omega
  refine noNonsolvableClassical_of_sylow_cover P3 sChain.originalSubgroup hS2 hidx pa_mem
    cover_S ?_
  unfold CentralizerGood
  rw [centralizerIn_P3 hP]
  exact Or.inl U_structure

section Model

open CFSG.Sporadic.J3 CFSG.Blueprint

@[expose] noncomputable def actionHom3 : J Native.j3Data →* Equiv.Perm (Fin 20520) :=
  MulAction.toPermHom (J Native.j3Data) (Fin Native.j3Data.n)

theorem actionHom3_apply (g : J Native.j3Data) (x : Fin 20520) :
    ((actionHom3 g x : Fin 20520) : ℕ) = CFSG.Sporadic.Th.idx Native.j3Data.n g x.val := by
  rw [CFSG.Sporadic.Th.idx_of_lt g (show x.val < Native.j3Data.n from x.isLt)]
  rfl

theorem actionHom3_a : actionHom3 (a Native.j3Data) = pa := by
  ext x
  have h1 := rep_pa x
  have h2 := rep_a j3Facts.orbitFacts x.val x.isLt
  have h3 : (abArr[0]!)[x.val]! = CFSG.Sporadic.Th.Native.ap Native.j3Data.tA x.val :=
    CFSG.Sporadic.SmallOddCore.natArr_getElem! _ _
  rw [actionHom3_apply, ← h1, h3, h2]

theorem actionHom3_b : actionHom3 (b Native.j3Data) = pb := by
  ext x
  have h1 := rep_pb x
  have h2 := rep_b j3Facts.orbitFacts x.val x.isLt
  have h3 : (abArr[1]!)[x.val]! = CFSG.Sporadic.Th.Native.ap Native.j3Data.tB x.val :=
    CFSG.Sporadic.SmallOddCore.natArr_getElem! _ _
  rw [actionHom3_apply, ← h1, h3, h2]

theorem actionHom3_injective : Function.Injective actionHom3 := by
  have := faithful j3Facts
  exact MulAction.toPerm_injective

theorem actionHom3_range : actionHom3.range = P3 := by
  rw [MonoidHom.range_eq_map, ← closure_ab Native.j3Data, MonoidHom.map_closure, Set.image_pair,
    actionHom3_a, actionHom3_b]
  rfl

@[expose] noncomputable def jEquivP3 : J Native.j3Data ≃* P3 :=
  (MonoidHom.ofInjective actionHom3_injective).trans
    (MulEquiv.subgroupCongr actionHom3_range)

private theorem seedA_eq' : Native.j3Data.seedA = NativeSporadic.J3Seed1 := rfl

private theorem seedB_eq' : Native.j3Data.seedB = NativeSporadic.J3Seed2 := rfl

noncomputable def nativeEquivJ3 : NativeSporadic.J3 ≃* J Native.j3Data := by
  have e := seedEquiv (D := Native.j3Data) j3Facts.powA j3Facts.powB
  rw [seedA_eq', seedB_eq'] at e
  exact e

noncomputable def nativeEquivP3 : NativeSporadic.J3 ≃* P3 :=
  nativeEquivJ3.trans jEquivP3

theorem card_P3 : Nat.card P3 = 50232960 := by
  rw [← Nat.card_congr nativeEquivP3.toEquiv]
  exact card_J3

theorem noNonsolvableClassical_J3 : NoNonsolvableClassical NativeSporadic.J3 :=
  NoNonsolvableClassical.of_mulEquiv nativeEquivP3 (noNonsolvableClassical_P3 card_P3)

end Model

end J3Proof

theorem noNonsolvableClassical_J3 : NoNonsolvableClassical CFSG.Blueprint.NativeSporadic.J3 :=
  J3Proof.noNonsolvableClassical_J3

end CFSG.ClassicalInvolution

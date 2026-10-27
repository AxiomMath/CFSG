module

public import Certificates.Certificate17323
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzDefs
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J3A6
public import CFSG.RankThree.PartOne.KS.PKitLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SimpleLeaf
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.SplitShape

public section

namespace CFSG.HardMathSupport.Dickson.I271

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu CFSG.RankThree.PartTwo.KFacts.K426
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
  CFSG.AGLEmbeddingD2.Wilson.Census228Spor CFSG.CosetTable
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.Sporadic.SuzOddCore (suzM)
open scoped commutatorElement

section Transport

variable {G : Type} [Group G]

theorem a6Split3_comap_subtype (P L : Subgroup G) (hLP : L ≤ P)
    (eL : ↥L ≃* alternatingGroup (Fin 6)) {T e₁ e₂ : G} (hT : T ∈ P) (h₁ : e₁ ∈ P)
    (h₂ : e₂ ∈ P) (E₃ : Subgroup G) {a b c d : ℕ} (hTn : ∀ g : G, g ∈ L ↔ T * g * T⁻¹ ∈ L)
    (hEL : E₃ ≤ L) (hE : Nat.card ↥E₃ = 9) (he₁ : e₁ ∈ E₃) (he₂ : e₂ ∈ E₃)
    (hcomm : e₁ * e₂ = e₂ * e₁) (hgen : ∀ g ∈ E₃, ∃ i j : ℕ, g = e₁ ^ i * e₂ ^ j)
    (h1 : T * e₁ * T⁻¹ = e₁ ^ a * e₂ ^ b) (h2 : T * e₂ * T⁻¹ = e₁ ^ c * e₂ ^ d)
    (hdet : a * d ≡ b * c + 2 [MOD 3]) : A6Split3 (L.comap P.subtype) := by
  have hEP : E₃ ≤ P := hEL.trans hLP
  refine ⟨⟨(Subgroup.subgroupOfEquivOfLe hLP).trans eL⟩, ⟨T, hT⟩, ⟨e₁, h₁⟩, ⟨e₂, h₂⟩,
    E₃.comap P.subtype, a, b, c, d, ?_, Subgroup.comap_mono hEL, ?_, he₁, he₂, ?_, ?_, ?_, ?_,
    hdet⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    exact hTn (g : G)
  · exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv).trans hE
  · exact Subtype.ext hcomm
  · intro g hg
    obtain ⟨i, j, hij⟩ := hgen (g : G) hg
    exact ⟨i, j, Subtype.ext (by simpa using hij)⟩
  · exact Subtype.ext (by simpa using h1)
  · exact Subtype.ext (by simpa using h2)

variable (P : Subgroup G) [Finite P]

theorem splitShapeAt_of_subgroup_data (x : ↥P) (L : Subgroup G)
    (hLC : L ≤ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P)
    (hLn : ∀ g ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (eL : ↥L ≃* alternatingGroup (Fin 6)) {k : ℕ}
    (hk : Nat.card ↥(Subgroup.centralizer ({(x : G)} : Set G) ⊓ P) = Nat.card ↥L * 3 ^ k)
    (hsplit : A6Split3 (L.comap P.subtype)) : SplitShapeAt 3 x := by
  have hLP : L ≤ P := fun l hl => (hLC hl).2
  haveI : Finite ↥L :=
    Finite.of_injective (Subgroup.inclusion hLP) (Subgroup.inclusion_injective hLP)
  let C' : Subgroup ↥P := Subgroup.centralizer ({x} : Set ↥P)
  let L' : Subgroup ↥P := L.comap P.subtype
  have hmapC : C'.map P.subtype = Subgroup.centralizer ({(x : G)} : Set G) ⊓ P :=
    map_centralizer_subtype' P x
  have hL'C : L' ≤ C' := by
    intro l hl
    have hl1 : (l : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := hLC hl
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hl1).1
    exact Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hc)
  let E : Subgroup ↥C' := L'.subgroupOf C'
  have hEn : E.Normal := by
    refine ⟨fun e he g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at he ⊢
    have hgC : ((g : ↥P) : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ P := by
      rw [← hmapC]
      exact ⟨g, g.2, rfl⟩
    exact hLn _ hgC _ he
  haveI := hEn
  have hEmap : E.map C'.subtype = L' := Subgroup.map_subgroupOf_eq_of_le hL'C
  have eL' : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLP
  have eE : ↥E ≃* alternatingGroup (Fin 6) :=
    (E.equivMapOfInjective C'.subtype C'.subtype_injective).trans
      (((MulEquiv.subgroupCongr hEmap).trans eL').trans eL)
  have hq : IsPGroup 3 (↥C' ⧸ E) := by
    have hcardC : Nat.card ↥C' = Nat.card ↥L * 3 ^ k := by
      rw [← hk, ← hmapC, Subgroup.card_map_of_injective P.subtype_injective]
    have hcardE : Nat.card ↥E = Nat.card ↥L := by
      rw [← Subgroup.card_map_of_injective C'.subtype_injective, hEmap]
      exact Nat.card_congr eL'.toEquiv
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine IsPGroup.of_card (n := k) ?_
    have hpos : 0 < Nat.card ↥L := Nat.card_pos
    rw [hcardC, hcardE] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_comm (Nat.card ↥L) _, ← h1])
  right
  exact splitShape_alt6_of_normal E eE hq (hEmap ▸ hsplit)

end Transport

namespace TabSuzC

@[expose] noncomputable def aPerm (i : Fin 2) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (aGens (levels ()))[i.val]!

@[expose] noncomputable def ePerm (i : Fin 2) : Equiv.Perm (Fin 1782) :=
  permOfArr 1782 (sGens (levels ()))[i.val]!

@[expose] noncomputable def tPerm : Equiv.Perm (Fin 1782) := permOfArr 1782 (tArr (levels ()))

@[expose] noncomputable def Esub : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (permsA 1782 (aGens (levels ())))

@[expose] noncomputable def Ssub : Subgroup (Equiv.Perm (Fin 1782)) :=
  Subgroup.closure (permsA 1782 (sGens (levels ())))

theorem aGens_size : (aGens (levels ())).size = 2 := by simp [aGens, aTuples]

theorem sGens_size : (sGens (levels ())).size = 2 := by simp [sGens, sTuples]

theorem range_aPerm : Set.range aPerm = permsA 1782 (aGens (levels ())) := by
  ext σ
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by rw [aGens_size]; exact i.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := by rw [aGens_size] at hk; exact hk
    exact ⟨⟨k, hk2⟩, rfl⟩

structure Parts : Prop where
  derived : derivedLeOK 1782 (cGens (levels ())) (aGens (levels ())) cKeys (aCert (levels ()))
    360 = true
  inC : allLt (aGens (levels ())).size (fun l => inP (levels ()) (aGens (levels ()))[l]! &&
    commA 1782 (aGens (levels ()))[l]! (yArr (levels ()))) = true
  rels : wordsOneOK 1782 (aGens (levels ())) j3tLiftRels = true
  sEnum : enumOK 1782 (sGens (levels ())) cKeys (sCert (levels ())) = true
  sCard : (sCert (levels ())).pts.size = 9
  sInE : allLt (sGens (levels ())).size (fun l =>
    (aCert (levels ())).pts.toList.any (eqA 1782 (sGens (levels ()))[l]!)) = true
  sComm : commA 1782 (sGens (levels ()))[0]! (sGens (levels ()))[1]! = true
  sCube : allLt (sGens (levels ())).size (fun l =>
    eqA 1782 (powArr 1782 (sGens (levels ()))[l]! 3) (idA 1782)) = true
  tValid : validA 1782 (tArr (levels ())) = true
  tInP : inP (levels ()) (tArr (levels ())) = true
  tNorm : allLt (aGens (levels ())).size (fun l =>
    (aCert (levels ())).pts.toList.any (eqA 1782 (conjA 1782 (tArr (levels ()))
      (aGens (levels ()))[l]!)) &&
    (aCert (levels ())).pts.toList.any (eqA 1782 (conjInvA 1782 (tArr (levels ()))
      (aGens (levels ()))[l]!))) = true
  tFix : eqA 1782 (conjA 1782 (tArr (levels ())) (sGens (levels ()))[0]!)
    (sGens (levels ()))[0]! = true
  tInv : eqA 1782 (conjA 1782 (tArr (levels ())) (sGens (levels ()))[1]!)
    (powArr 1782 (sGens (levels ()))[1]! 2) = true

theorem parts : Parts := by
  have h := Certificates.certificate17323
  simp only [tabSuzCCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

section Facts


theorem aEnum : enumOK 1782 (aGens (levels ())) cKeys (aCert (levels ())) = true := by
  have h := parts.derived
  simp only [derivedLeOK, Bool.and_eq_true] at h
  exact h.1.1.1

theorem aGens_valid :
    ∀ k < (aGens (levels ())).size, validA 1782 (aGens (levels ()))[k]! = true :=
  fun _ hk => enumOK_gens_valid aEnum hk

theorem sGens_valid :
    ∀ k < (sGens (levels ())).size, validA 1782 (sGens (levels ()))[k]! = true :=
  fun _ hk => enumOK_gens_valid parts.sEnum hk

theorem rep_ePerm (i : Fin 2) : Rep 1782 (sGens (levels ()))[i.val]! (ePerm i) :=
  rep_of_validA (sGens_valid i.val (by rw [sGens_size]; exact i.2))

theorem rep_tPerm : Rep 1782 (tArr (levels ())) tPerm := rep_of_validA parts.tValid

theorem Esub_derived :
    ⁅closure (permsA 1782 (cGens (levels ()))), closure (permsA 1782 (cGens (levels ())))⁆ ≤
      Esub ∧ Nat.card Esub = 360 :=
  commutator_le_of_derivedLeOK cKeys_lt (fun _ hk => enumOK_gens_valid cEnum hk) parts.derived

theorem Esub_le_C : Esub ≤ Subgroup.centralizer {yPerm} ⊓ suzM := by
  rw [Esub, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have hk' : k < (aGens (levels ())).size := hk
  have hrep := rep_of_validA (aGens_valid k hk')
  have h2 := allLt_spec parts.inC hk'
  rw [Bool.and_eq_true] at h2
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2
    ((commA_iff hrep rep_y).1 h2.2), mem_suzM_of_inP hrep h2.1⟩

theorem Esub_le_P : Esub ≤ suzM := fun _ hl => (Esub_le_C hl).2

theorem tPerm_mem : tPerm ∈ suzM := mem_suzM_of_inP rep_tPerm parts.tInP

theorem tPerm_normalizes (g : Equiv.Perm (Fin 1782)) :
    g ∈ Esub ↔ tPerm * g * tPerm⁻¹ ∈ Esub := by
  have hfwd : ∀ r ∈ Esub, tPerm * r * tPerm⁻¹ ∈ Esub := by
    refine conj_mem_closure_of_gens (T := permsA 1782 (aGens (levels ()))) (g := tPerm) ?_
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < (aGens (levels ())).size := hl
    have h := allLt_spec parts.tNorm hl'
    rw [Bool.and_eq_true] at h
    exact enumOK_mem_of_any cKeys_lt aEnum
      (rep_conjA parts.tValid (rep_of_validA (aGens_valid l hl'))) h.1
  have hbwd : ∀ r ∈ Esub, tPerm⁻¹ * r * tPerm⁻¹⁻¹ ∈ Esub := by
    refine conj_mem_closure_of_gens (T := permsA 1782 (aGens (levels ()))) (g := tPerm⁻¹) ?_
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < (aGens (levels ())).size := hl
    have h := allLt_spec parts.tNorm hl'
    rw [Bool.and_eq_true] at h
    rw [inv_inv]
    exact enumOK_mem_of_any cKeys_lt aEnum
      (rep_conjInvA parts.tValid (rep_of_validA (aGens_valid l hl'))) h.2
  refine ⟨hfwd g, fun hg => ?_⟩
  have := hbwd _ hg
  have e : tPerm⁻¹ * (tPerm * g * tPerm⁻¹) * tPerm⁻¹⁻¹ = g := by group
  rwa [e] at this

theorem Ssub_card : Nat.card Ssub = 9 :=
  (enumOK_spec cKeys_lt parts.sEnum).2.1.trans parts.sCard

theorem Ssub_le_Esub : Ssub ≤ Esub := le_of_gens_mem cKeys_lt aEnum parts.sEnum parts.sInE

theorem ePerm_mem_Ssub (i : Fin 2) : ePerm i ∈ Ssub :=
  Subgroup.subset_closure (mem_permsA (by rw [sGens_size]; exact i.2))

theorem ePerm_comm : ePerm 0 * ePerm 1 = ePerm 1 * ePerm 0 :=
  (commA_iff (rep_ePerm 0) (rep_ePerm 1)).1 parts.sComm

theorem ePerm_cube (i : Fin 2) : ePerm i ^ 3 = 1 := by
  have h := allLt_spec parts.sCube (show i.val < (sGens (levels ())).size by
    rw [sGens_size]; exact i.2)
  exact (eqA_iff (rep_powArr (rep_ePerm i) 3) rep_idA).1 h

theorem tPerm_ePerm_zero : tPerm * ePerm 0 * tPerm⁻¹ = ePerm 0 :=
  (eqA_iff (rep_conjA parts.tValid (rep_ePerm 0)) (rep_ePerm 0)).1 parts.tFix

theorem tPerm_ePerm_one : tPerm * ePerm 1 * tPerm⁻¹ = ePerm 1 ^ 2 :=
  (eqA_iff (rep_conjA parts.tValid (rep_ePerm 1)) (rep_powArr (rep_ePerm 1) 2)).1 parts.tInv

theorem Ssub_gen : ∀ g ∈ Ssub, ∃ i j : ℕ, g = ePerm 0 ^ i * ePerm 1 ^ j := by
  have hc : Commute (ePerm 0) (ePerm 1) := ePerm_comm
  have h30 := ePerm_cube 0
  have h31 := ePerm_cube 1
  have hinv : ∀ e : Equiv.Perm (Fin 1782), e ^ 3 = 1 → ∀ i : ℕ, (e ^ i)⁻¹ = e ^ (2 * i) := by
    intro e he i
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, he, one_pow]
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    obtain ⟨k, hk, rfl⟩ := hs
    have hk2 : k < 2 := by rw [sGens_size] at hk; exact hk
    interval_cases k
    · exact ⟨1, 0, by simp [ePerm]⟩
    · exact ⟨0, 1, by simp [ePerm]⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨i, j, rfl⟩ := ha
    obtain ⟨i', j', rfl⟩ := hb
    refine ⟨i + i', j + j', ?_⟩
    rw [pow_add, pow_add]
    exact (hc.symm.pow_pow j i').mul_mul_mul_comm _ _
  | inv a _ ha =>
    obtain ⟨i, j, rfl⟩ := ha
    refine ⟨2 * i, 2 * j, ?_⟩
    rw [mul_inv_rev, hinv _ h30 i, hinv _ h31 j]
    exact (hc.symm.pow_pow (2 * j) (2 * i)).eq

theorem nonempty_mulEquiv_Esub_alt6 :
    Nonempty (↥Esub ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨hfin, hcard⟩ := card_le_of_cyclicCheckC j3tLiftRels [2] (by norm_num) j3t_lift_check
  have hA : Nat.card (closure (Set.range a6gen)) = 360 := by
    rw [closure_a6gen, ← card_A6]
    exact Nat.card_congr (Subgroup.topEquiv (G := alternatingGroup (Fin 6))).toEquiv
  have hrels : ∀ w ∈ j3tLiftRels, evalW aPerm w = 1 := by
    have h3 := parts.rels
    simp only [wordsOneOK, Bool.and_eq_true, List.all_eq_true] at h3
    intro w hw
    have hv := rep_evalWA (m := 2) (gs := aGens (levels ())) aGens_valid
      (by rw [aGens_size]) w
    exact (eqA_iff hv rep_idA).1 (h3.2 w hw)
  have hE : Nat.card (closure (Set.range aPerm)) = 360 := by
    rw [range_aPerm]
    exact Esub_derived.2
  obtain ⟨e⟩ := nonempty_mulEquiv_of_presented aPerm a6gen j3tLiftRels hrels a6_rels hfin 360
    (by omega) hE.ge hA.ge
  rw [range_aPerm] at e
  exact ⟨e.trans ((MulEquiv.subgroupCongr closure_a6gen).trans Subgroup.topEquiv)⟩

end Facts

end TabSuzC

open TabSuzC in
theorem splitShapeAt_y :
    SplitShapeAt 3 (⟨yPerm, yPerm_mem⟩ : ↥suzM) := by
  obtain ⟨hCeq, hCcard⟩ := Cy_eq
  obtain ⟨hder, hEcard⟩ := Esub_derived
  obtain ⟨eE⟩ := nonempty_mulEquiv_Esub_alt6
  have hEC : Esub ≤ closure (permsA 1782 (cGens (levels ()))) := hCeq ▸ Esub_le_C
  refine splitShapeAt_of_subgroup_data suzM ⟨yPerm, yPerm_mem⟩ Esub Esub_le_C ?_ eE (k := 2) ?_ ?_
  · intro g hg l hl
    rw [← hCeq] at hg
    have h1 : ⁅g, l⁆ ∈ ⁅closure (permsA 1782 (cGens (levels ()))),
        closure (permsA 1782 (cGens (levels ())))⁆ :=
      Subgroup.commutator_mem_commutator hg (hEC hl)
    have h3 : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact Esub.mul_mem (hder h1) hl
  · show Nat.card ↥(Subgroup.centralizer {yPerm} ⊓ suzM) = Nat.card ↥Esub * 3 ^ 2
    rw [← hCeq, hCcard, hEcard]
    norm_num
  · refine a6Split3_comap_subtype suzM Esub Esub_le_P eE tPerm_mem
      (Esub_le_P (Ssub_le_Esub (ePerm_mem_Ssub 0))) (Esub_le_P (Ssub_le_Esub (ePerm_mem_Ssub 1)))
      Ssub (a := 1) (b := 0) (c := 0) (d := 2) tPerm_normalizes Ssub_le_Esub Ssub_card
      (ePerm_mem_Ssub 0) (ePerm_mem_Ssub 1) ePerm_comm Ssub_gen ?_ ?_ (by decide)
    · rw [pow_one, pow_zero, mul_one]
      exact tPerm_ePerm_zero
    · rw [pow_zero, one_mul]
      exact tPerm_ePerm_one

end CFSG.HardMathSupport.Dickson.I271

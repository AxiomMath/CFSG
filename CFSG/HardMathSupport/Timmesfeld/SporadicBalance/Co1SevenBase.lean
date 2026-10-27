module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenLeaf
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1SevenKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1FiveKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Reduction
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public import Certificates.Certificate2043
public import Certificates.Certificate3024

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

open CFSG.Open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative
  Timmesfeld.Co1Seven Matrix
open Timmesfeld.Co1Five (Plan planOK planOKv tupImgs candList stages stagesAux stageStep
  colsToRows slotCols phiRows orbImg xsOf slotVal)

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1F (μG μG_apply μG_injective rows_eq_of_mrep
  validRows_pow validRows_one validRows_mul' orderOf_conj_eq)

local notation "Rows" => CFSG.Sporadic.Co1Schreier.Native.Rows

@[expose] noncomputable def gElts : List GL24 := dagG [A₁, A₂] (dagWords.map Native.decWord)

theorem base_mem : ∀ g ∈ ([A₁, A₂] : List GL24), g ∈ GA := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h
  · rw [h]; exact A₁_mem
  · rw [h]; exact A₂_mem

theorem gElts_mem : ∀ g ∈ gElts, g ∈ GA := by
  unfold gElts
  exact dagG_mem base_mem _

@[expose] noncomputable def gE (k : ℕ) : ↥GA := ⟨gElts.getD k 1, getD_mem_of_forall gElts_mem k⟩

abbrev gRows : List Rows := (gDag Native.aR Native.bR).1

section Rep

theorem rep_gE (hflag : (gDag Native.aR Native.bR).2.2 = true) (k : ℕ) :
    MRep (rowAt gRows k) ((gE k : ↥GA) : GL24) := by
  have hb : List.Forall₂ MRep [Native.aR, Native.bR] [A₁, A₂] :=
    List.Forall₂.cons rep_A₁ (List.Forall₂.cons rep_A₂ List.Forall₂.nil)
  have h := dag_rep hb (dagWords.map Native.decWord) hflag
  exact getD_rep h MRep.one k

end Rep

section Sylow

@[expose] noncomputable def sE : ↥GA := gE iS

@[expose] noncomputable def tE : ↥GA := gE iT

@[expose] noncomputable def xE (k : ℕ) : ↥GA :=
  if k = 0 then sE else if k = 1 then tE else tE * sE ^ (k - 1)

@[expose] noncomputable def tgtE (k : ℕ) : ↥GA := if fusTgt.getD k 0 = 0 then sE else tE

@[expose] noncomputable def cE (k : ℕ) : ↥GA := gE (fusG.getD k 0)

theorem sylowOK_parts {aR bR : Rows} (h : sylowOK aR bR = true) :
    (gDag aR bR).2.2 = true ∧ validRows (rowAt (gDag aR bR).1 iS) = true ∧
    validRows (rowAt (gDag aR bR).1 iT) = true ∧
    rowAt (gDag aR bR).1 iS ≠ Native.one () ∧ rowAt (gDag aR bR).1 iT ≠ Native.one () ∧
    Native.mul (rowAt (gDag aR bR).1 iS) (rowAt (gDag aR bR).1 iT) =
      Native.mul (rowAt (gDag aR bR).1 iT) (rowAt (gDag aR bR).1 iS) ∧
    Native.pow (rowAt (gDag aR bR).1 iS) 7 = Native.one () ∧
    Native.pow (rowAt (gDag aR bR).1 iT) 7 = Native.one () ∧
    gtOK #[rowAt (gDag aR bR).1 iS, rowAt (gDag aR bR).1 iT]
      (treeOf [rowAt (gDag aR bR).1 iS, rowAt (gDag aR bR).1 iT]) = true ∧
    (treeOf [rowAt (gDag aR bR).1 iS, rowAt (gDag aR bR).1 iT]).pts.size = 49 ∧
    (∀ p ∈ (treeOf [rowAt (gDag aR bR).1 iS, rowAt (gDag aR bR).1 iT]).pts.toList,
      p = Native.one () ∨ ∃ k < 8, ∃ b < 6, p = Native.pow (xGen (gDag aR bR).1 k) (b + 1)) ∧
    (∀ k < 8, validRows (rowAt (gDag aR bR).1 (fusG.getD k 0)) = true ∧
      Native.mul (rowAt (gDag aR bR).1 (fusG.getD k 0)) (xGen (gDag aR bR).1 k) =
        Native.mul (tgtRow (gDag aR bR).1 k) (rowAt (gDag aR bR).1 (fusG.getD k 0))) := by
  unfold sylowOK at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, Array.all_eq_true', List.any_eq_true, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_, ?_⟩
  · intro p hp
    have := h11 p (Array.mem_def.2 hp)
    rcases this with h | ⟨k, hk, hk2⟩
    · left; exact h
    · right
      obtain ⟨b, hb, hb2⟩ := hk2
      exact ⟨k, hk, b, hb, hb2⟩
  · intro k hk
    exact h12 k hk

theorem rep_sE (hS : sylowOK Native.aR Native.bR = true) :
    MRep (rowAt gRows iS) ((sE : ↥GA) : GL24) :=
  rep_gE (sylowOK_parts hS).1 iS

theorem rep_tE (hS : sylowOK Native.aR Native.bR = true) :
    MRep (rowAt gRows iT) ((tE : ↥GA) : GL24) :=
  rep_gE (sylowOK_parts hS).1 iT

theorem sE_ne (hS : sylowOK Native.aR Native.bR = true) : sE ≠ 1 := by
  intro h
  have hr := rep_sE hS
  rw [h, Subgroup.coe_one] at hr
  exact (sylowOK_parts hS).2.2.2.1
    (rows_eq_of_mrep (sylowOK_parts hS).2.1 validRows_one hr MRep.one)

theorem tE_ne (hS : sylowOK Native.aR Native.bR = true) : tE ≠ 1 := by
  intro h
  have hr := rep_tE hS
  rw [h, Subgroup.coe_one] at hr
  exact (sylowOK_parts hS).2.2.2.2.1
    (rows_eq_of_mrep (sylowOK_parts hS).2.2.1 validRows_one hr MRep.one)

theorem sE_pow (hS : sylowOK Native.aR Native.bR = true) : sE ^ 7 = 1 := by
  have h := (rep_sE hS).pow 7
  rw [(sylowOK_parts hS).2.2.2.2.2.2.1] at h
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h.eq MRep.one

theorem tE_pow (hS : sylowOK Native.aR Native.bR = true) : tE ^ 7 = 1 := by
  have h := (rep_tE hS).pow 7
  rw [(sylowOK_parts hS).2.2.2.2.2.2.2.1] at h
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h.eq MRep.one

theorem sE_comm (hS : sylowOK Native.aR Native.bR = true) : sE * tE = tE * sE := by
  have r1 := (rep_sE hS).mul (rep_tE hS)
  have r2 := (rep_tE hS).mul (rep_sE hS)
  rw [(sylowOK_parts hS).2.2.2.2.2.1] at r1
  exact Subtype.ext (r1.eq r2)

theorem orderOf_sE (hS : sylowOK Native.aR Native.bR = true) : orderOf sE = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (sE_pow hS) (sE_ne hS)

theorem orderOf_tE (hS : sylowOK Native.aR Native.bR = true) : orderOf tE = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (tE_pow hS) (tE_ne hS)

theorem rep_xE (hS : sylowOK Native.aR Native.bR = true) (k : ℕ) :
    MRep (xGen gRows k) ((xE k : ↥GA) : GL24) := by
  unfold xGen xE
  by_cases h0 : k = 0
  · simp only [h0, ite_true]; exact rep_sE hS
  · by_cases h1 : k = 1
    · simp only [h1, ite_true]; exact rep_tE hS
    · simp only [h0, h1, ite_false]
      rw [Subgroup.coe_mul, Subgroup.coe_pow]
      exact (rep_tE hS).mul ((rep_sE hS).pow _)

theorem rep_tgtE (hS : sylowOK Native.aR Native.bR = true) (k : ℕ) :
    MRep (tgtRow gRows k) ((tgtE k : ↥GA) : GL24) := by
  unfold tgtRow tgtE
  by_cases h0 : fusTgt.getD k 0 = 0
  · simp only [h0, ite_true]; exact rep_sE hS
  · simp only [h0, ite_false]; exact rep_tE hS

theorem conj_to_target (hS : sylowOK Native.aR Native.bR = true) {k : ℕ} (hk : k < 8) :
    cE k * xE k = tgtE k * cE k := by
  have hc : MRep (rowAt gRows (fusG.getD k 0)) ((cE k : ↥GA) : GL24) :=
    rep_gE (sylowOK_parts hS).1 _
  have r1 := hc.mul (rep_xE hS k)
  have r2 := (rep_tgtE hS k).mul hc
  rw [((sylowOK_parts hS).2.2.2.2.2.2.2.2.2.2.2 k hk).2] at r1
  exact Subtype.ext (r1.eq r2)

@[expose] noncomputable def P0 : Subgroup ↥GA := Subgroup.closure ({sE, tE} : Set ↥GA)

@[expose] noncomputable def gg2 (l : ℕ) : ↥GA := if l = 0 then sE else tE

theorem gg2_image : gg2 '' {l | l < (#[rowAt gRows iS, rowAt gRows iT] : Array Rows).size} =
    ({sE, tE} : Set ↥GA) := by
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨l, hl, rfl⟩
    have : l < 2 := hl
    interval_cases l
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by simp, rfl⟩
    · exact ⟨1, by simp, rfl⟩

theorem hgg2 (hS : sylowOK Native.aR Native.bR = true) :
    ∀ l < (#[rowAt gRows iS, rowAt gRows iT] : Array Rows).size,
      μG (gg2 l) = rowsMatrix 24 (#[rowAt gRows iS, rowAt gRows iT] : Array Rows)[l]! := by
  intro l hl
  have : l < 2 := hl
  interval_cases l
  · rw [μG_apply]; exact (rep_sE hS).symm
  · rw [μG_apply]; exact (rep_tE hS).symm

theorem card_P0 (hS : sylowOK Native.aR Native.bR = true) : Nat.card P0 = 49 := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have h := CFSG.Sporadic.Co1Block.prodTree_card μG μG_injective
    (sylowOK_parts hS).2.2.2.2.2.2.2.2.1 gg2 (hgg2 hS)
  rw [gg2_image] at h
  rw [P0, h]
  exact (sylowOK_parts hS).2.2.2.2.2.2.2.2.2.1

theorem mem_P0 (hS : sylowOK Native.aR Native.bR = true) {y : ↥GA} (hy : y ∈ P0) :
    y = 1 ∨ ∃ k < 8, ∃ b < 6, y = xE k ^ (b + 1) := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  obtain ⟨f, hf, -, heq⟩ := CFSG.Sporadic.Co1Block.prodTree_closure_eq μG μG_injective
    (sylowOK_parts hS).2.2.2.2.2.2.2.2.1 gg2 (hgg2 hS)
  rw [gg2_image] at heq
  have hy' : y ∈ (Subgroup.closure ({sE, tE} : Set ↥GA) : Set ↥GA) := hy
  rw [heq] at hy'
  obtain ⟨i, hi, rfl⟩ := hy'
  have hi' : i < (treeOf [rowAt (gDag Native.aR Native.bR).1 iS,
      rowAt (gDag Native.aR Native.bR).1 iT]).pts.size := hi
  have hrep : MRep (treeOf [rowAt gRows iS, rowAt gRows iT]).pts[i]! ((f i : ↥GA) : GL24) := by
    unfold MRep
    rw [← μG_apply, hf i hi']
  have hpt : (treeOf [rowAt gRows iS, rowAt gRows iT]).pts[i]! ∈
      (treeOf [rowAt gRows iS, rowAt gRows iT]).pts.toList := by
    rw [getElem!_pos _ i hi']
    exact Array.getElem_mem_toList hi'
  rcases (sylowOK_parts hS).2.2.2.2.2.2.2.2.2.2.1 _ hpt with h | ⟨k, hk, b, hb, hpe⟩
  · left
    rw [h] at hrep
    exact Subtype.ext (hrep.eq MRep.one)
  · right
    refine ⟨k, hk, b, hb, ?_⟩
    rw [hpe] at hrep
    have := (rep_xE hS k).pow (b + 1)
    rw [← Subgroup.coe_pow] at this
    exact Subtype.ext (hrep.eq this)

end Sylow

section Final

theorem factorization_card_GA_seven : (Nat.card ↥GA).factorization 7 = 2 := by
  rw [card_GA_eq, show (4157776806543360000 : ℕ) = 7 ^ 2 * 84852587888640000 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem qs_A (q : ℕ) (hq : q.Prime) (hd : q ∣ 17640) (h7 : q ≠ 7) : q ∈ qsList := by
  have h : q ∈ Nat.primeFactors 17640 := Nat.mem_primeFactors.2 ⟨hq, hd, by norm_num⟩
  have e : Nat.primeFactors 17640 = {2, 3, 5, 7} := by
    rw [show (17640 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 ^ 2 by norm_num]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide +revert
  rw [e] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold qsList
  rcases h with rfl | rfl | rfl | rfl <;> simp_all

theorem qs_B (q : ℕ) (hq : q.Prime) (hd : q ∣ 1176) (h7 : q ≠ 7) : q ∈ qsList := by
  have h : q ∈ Nat.primeFactors 1176 := Nat.mem_primeFactors.2 ⟨hq, hd, by norm_num⟩
  have e : Nat.primeFactors 1176 = {2, 3, 7} := by
    rw [show (1176 : ℕ) = 2 ^ 3 * 3 * 7 ^ 2 by norm_num]
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.primeFactors_pow _ (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    decide +revert
  rw [e] at h
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  unfold qsList
  rcases h with rfl | rfl | rfl <;> simp_all

theorem orderOf_tgtE (hS : sylowOK Native.aR Native.bR = true) (k : ℕ) : orderOf (tgtE k) = 7 := by
  unfold tgtE
  split_ifs
  · exact orderOf_sE hS
  · exact orderOf_tE hS

theorem bot_tgtE (hA : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sE} : Set ↥GA)) = ⊥)
    (hB : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tE} : Set ↥GA)) = ⊥) (k : ℕ) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tgtE k} : Set ↥GA)) = ⊥ := by
  unfold tgtE
  split_ifs
  · exact hA
  · exact hB

theorem bot_of_mem_P0 (hS : sylowOK Native.aR Native.bR = true)
    (hA : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sE} : Set ↥GA)) = ⊥)
    (hB : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tE} : Set ↥GA)) = ⊥) {y : ↥GA} (hy : y ∈ P0)
    (hyo : orderOf y = 7) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({y} : Set ↥GA)) = ⊥ := by
  rcases mem_P0 hS hy with h1 | ⟨k, hk, b, hb, hyk⟩
  · rw [h1, orderOf_one] at hyo
    exact absurd hyo (by norm_num)
  · have hconj := conj_to_target hS hk
    have hc : cE k * y * (cE k)⁻¹ = tgtE k ^ (b + 1) := by
      rw [hyk]
      exact @conj_pow_of_conj ↥GA (Subgroup.toGroup GA) _ _ _ hconj _
    have hC : Subgroup.centralizer ({tgtE k ^ (b + 1)} : Set ↥GA) =
        Subgroup.centralizer ({tgtE k} : Set ↥GA) :=
      @centralizer_pow_eq_of_not_dvd 7 ↥GA (Subgroup.toGroup GA) _ (by norm_num)
        (orderOf_tgtE hS k) _ (by omega)
    refine (@gLAPPrimeCoreOf_centralizer_conj 7 ↥GA (Subgroup.toGroup GA) (cE k) y).1 ?_
    rw [hc, hC]
    exact bot_tgtE hA hB k

theorem oPrimeCoreTrivialAt_GA (hS : sylowOK Native.aR Native.bR = true)
    (hA : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sE} : Set ↥GA)) = ⊥)
    (hB : GLAPPrimeCoreOf 7 (Subgroup.centralizer ({tE} : Set ↥GA)) = ⊥) :
    OPrimeCoreTrivialAt 7 ↥GA := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro s hs
  have hQ : Nat.card P0 = 7 ^ (Nat.card (⊤ : Subgroup ↥GA)).factorization 7 := by
    rw [card_P0 hS, Subgroup.card_top, factorization_card_GA_seven]
    norm_num
  obtain ⟨g, -, hg⟩ := Co3T.exists_conj_mem_of_full (le_top : P0 ≤ ⊤) hQ (Subgroup.mem_top s) hs
  have hy : orderOf (g⁻¹ * s * g) = 7 := by
    have := orderOf_conj_eq g⁻¹ s
    rw [inv_inv] at this
    rw [this, hs]
  have h := bot_of_mem_P0 hS hA hB hg hy
  refine (@gLAPPrimeCoreOf_centralizer_conj 7 ↥GA (Subgroup.toGroup GA) g⁻¹ s).1 ?_
  rw [inv_inv]
  exact h

theorem isPGroup_centralizer_GA (hS : sylowOK Native.aR Native.bR = true)
    (hA : ∀ c ∈ Subgroup.centralizer ({sE} : Set ↥GA), c * tE = tE * c → c ^ 7 = 1)
    (P : Subgroup ↥GA) (hP : Nat.card P = 49) :
    IsPGroup 7 ↥(Subgroup.centralizer (P : Set ↥GA)) := by
  have : Finite ↥GA := Nat.finite_of_card_ne_zero (by rw [card_GA_eq]; norm_num)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h0 : Nat.card P0 = 7 ^ (Nat.card ↥GA).factorization 7 := by
    rw [card_P0 hS, factorization_card_GA_seven]; norm_num
  have h1 : Nat.card P = 7 ^ (Nat.card ↥GA).factorization 7 := by
    rw [hP, factorization_card_GA_seven]; norm_num
  obtain ⟨g, hg⟩ := @exists_conj_sylow 7 ↥GA (Subgroup.toGroup GA) _ _ P0 P h0 h1
  intro c
  refine ⟨1, ?_⟩
  have hcP : ∀ x ∈ P, x * (c : ↥GA) = (c : ↥GA) * x := fun x hx =>
    Subgroup.mem_centralizer_iff.1 c.2 x hx
  have hsm : sE ∈ P0 := Subgroup.subset_closure (by simp)
  have htm : tE ∈ P0 := Subgroup.subset_closure (by simp)
  have hs : (g⁻¹ * (c : ↥GA) * g) * sE = sE * (g⁻¹ * (c : ↥GA) * g) :=
    @comm_of_conj_comm ↥GA (Subgroup.toGroup GA) g c sE (hcP _ (hg _ hsm))
  have ht : (g⁻¹ * (c : ↥GA) * g) * tE = tE * (g⁻¹ * (c : ↥GA) * g) :=
    @comm_of_conj_comm ↥GA (Subgroup.toGroup GA) g c tE (hcP _ (hg _ htm))
  have h7 := hA _ (mem_Cen.2 hs) ht
  have h8 := @pow_eq_one_of_conj ↥GA (Subgroup.toGroup GA) g c 7 h7
  apply Subtype.ext
  simpa [Subgroup.coe_pow] using h8

end Final

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1S

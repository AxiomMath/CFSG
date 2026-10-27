module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1AutCheck
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1ModelOrbit
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Link
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeAut

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1.Model

open Subgroup Matrix CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
open CFSG.Certificates.Native CFSG.ComponentClassification.J2Cover
open CFSG.EvenSmallLie.UnitarySix.YamadaPar

variable {ε : Eps}

theorem one_le_aDeg (ε : Eps) : 1 ≤ aDeg ε := by cases ε <;> decide

theorem aK_le (ε : Eps) : aK ε ≤ (aS ε).size := by
  cases ε
  · simp [aK, aS, OmegaEight.autS_size]
  · simp [aK, aS, aSMinus, OmegaEight.size_pushWords, OmegaEightMinus.genArrs_size, aWordsMinus]

@[expose] noncomputable def aQ (ε : Eps) : RawSchreierDatum (aDeg ε) :=
  RawSchreierDatum.ofArrays (aDeg ε) (one_le_aDeg ε) (aS ε) (aK ε) (aK_le ε) (aBase ε)
    (by cases ε <;> decide) (OmegaEight.wordsOf (aK ε) (aWords ε))

@[expose] noncomputable def AT (ε : Eps) : Subgroup (Equiv.Perm (Fin (aDeg ε))) :=
  (aQ ε).originalSubgroup

theorem AT_plus : AT .plus = OmegaEight.autT := by
  rw [AT, aQ, OmegaEight.autT, OmegaEight.autQ, ofArrays_originalSubgroup,
    ofArrays_originalSubgroup]
  congr 1

theorem AT_minus : AT .minus = OmegaEightMinus.autT := by
  rw [AT, aQ, OmegaEightMinus.autT, OmegaEightMinus.autQ, ofArrays_originalSubgroup,
    ofArrays_originalSubgroup]
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    change permOfArr 136 OmegaEightMinus.autS[i]! = permOfArr 136 aSMinus[i]!
    rw [OmegaEightMinus.autS, aSMinus, OmegaEight.pushWords_getElem! _ _ (by
      rw [OmegaEightMinus.genArrs_size]; exact hi), OmegaEight.pushWords_getElem! _ _ (by
      rw [OmegaEightMinus.genArrs_size]; exact hi)]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    change permOfArr 136 aSMinus[i]! = permOfArr 136 OmegaEightMinus.autS[i]!
    rw [OmegaEightMinus.autS, aSMinus, OmegaEight.pushWords_getElem! _ _ (by
      rw [OmegaEightMinus.genArrs_size]; exact hi), OmegaEight.pushWords_getElem! _ _ (by
      rw [OmegaEightMinus.genArrs_size]; exact hi)]

theorem aut_parts (ε : Eps) :
    rawChainOK (aDeg ε) ((aS ε).extract 0 (aK ε)) (aS ε) (((aBase ε).map Fin.val).toArray)
      (OmegaEight.wordsOf (aK ε) (aWords ε)) 4 = true ∧
    (∀ y < 64, isInvA (aDeg ε) (psiTT ε y) (invCand (aDeg ε) (psiTT ε y)) = true ∧
      memA ε (psiTT ε y) = true) ∧
    (∀ y < 64, ∀ y' < 64,
      eqA (aDeg ε) (psiTT ε (y ^^^ y')) (compA (aDeg ε) (psiTT ε y) (psiTT ε y')) = true) ∧
    (∀ b ∈ aBaseA ε, inR ε b = true) ∧
    (∀ z < aDeg ε, inR ε z = true → ∃ y < 64, (psiTT ε y)[0]! = z) := by
  have h := autChecks ε
  simp only [autCheck, Bool.and_eq_true, allLt_iff, beq_iff_eq, Array.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, -⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun y hy => ⟨(h2 y hy).1.1, (h2 y hy).1.2⟩, h3, fun b hb => ?_, fun z hz hR => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hb
    exact h4 i hi
  · rcases h5 z hz with h | ⟨y, hy, e⟩
    · rw [hR] at h
      exact absurd h (by decide)
    · exact ⟨y, hy, e⟩

theorem memA_iff {g : Array ℕ} {G : Equiv.Perm (Fin (aDeg ε))} (hG : Rep (aDeg ε) g G) :
    memA ε g = true ↔ G ∈ AT ε := by
  have := ofArrays_mem_iff (hn := one_le_aDeg ε) (hk := aK_le ε) (hb := by cases ε <;> decide)
    (by norm_num) (aut_parts ε).1 hG
  cases ε <;> exact this

@[expose] noncomputable def psiTM (ε : Eps) (v : V6) : Equiv.Perm (Fin (aDeg ε)) :=
  permOfArr (aDeg ε) (psiTT ε (vecBits v))

theorem rep_psiTM (v : V6) : Rep (aDeg ε) (psiTT ε (vecBits v)) (psiTM ε v) ∧
    Rep (aDeg ε) (invCand (aDeg ε) (psiTT ε (vecBits v))) (psiTM ε v)⁻¹ :=
  rep_permOfArr ((aut_parts ε).2.1 _ (vecBits_lt v)).1

theorem psiTM_add (v w : V6) : psiTM ε (v + w) = psiTM ε v * psiTM ε w := by
  have h := (aut_parts ε).2.2.1 (vecBits v) (vecBits_lt v) (vecBits w) (vecBits_lt w)
  rw [← vecBits_add] at h
  exact eq_of_eqA (rep_psiTM (v + w)).1 (rep_compA (rep_psiTM v).1 (rep_psiTM w).1) h

theorem psiTM_mem_A (v : V6) : psiTM ε v ∈ AT ε :=
  (memA_iff (rep_psiTM v).1).1 ((aut_parts ε).2.1 _ (vecBits_lt v)).2

@[expose] def Rset (ε : Eps) : Set (Fin (aDeg ε)) := {z | ∀ v : V6, v ≠ 0 → psiTM ε v z ≠ z}

theorem inR_iff {z : ℕ} (hz : z < aDeg ε) :
    inR ε z = true ↔ (⟨z, hz⟩ : Fin (aDeg ε)) ∈ Rset ε := by
  rw [inR, allLt_iff]
  constructor
  · intro h v hv e
    have hv' := vecBits_ne_zero hv
    have h1 := h (vecBits v - 1) (by have := vecBits_lt v; omega)
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hv'), (rep_psiTM v).1.apply hz, e] at h1
    simp at h1
  · intro h y hy
    have hy1 : y + 1 < 64 := by omega
    have hv : vecBits (toVec 6 (y + 1)) = y + 1 := vecBits_toVec hy1
    have hv0 : toVec 6 (y + 1) ≠ 0 := fun h0 => by
      rw [h0, vecBits_zero] at hv
      omega
    rw [← hv, (rep_psiTM _).1.apply hz]
    have := h _ hv0
    simp only [bne_iff_ne, ne_eq]
    exact fun e => this (Fin.ext e)

theorem aBase_mem_R {b : Fin (aDeg ε)} (hb : b ∈ aBase ε) : b ∈ Rset ε :=
  (inR_iff b.2).1 ((aut_parts ε).2.2.2.1 b.val (by
    rw [aBaseA, List.mem_toArray, List.mem_map]
    exact ⟨b, hb, rfl⟩))

theorem exists_psiTM_apply {z : Fin (aDeg ε)} (hz : z ∈ Rset ε) :
    ∃ v, psiTM ε v ⟨0, by have := one_le_aDeg ε; omega⟩ = z := by
  obtain ⟨y, hy, e⟩ := (aut_parts ε).2.2.2.2 z.val z.2 ((inR_iff z.2).2 hz)
  refine ⟨toVec 6 y, Fin.ext ?_⟩
  rw [← vecBits_toVec hy, (rep_psiTM _).1.apply (by have := one_le_aDeg ε; omega)] at e
  exact e

theorem zero_mem_aBase : (⟨0, by have := one_le_aDeg ε; omega⟩ : Fin (aDeg ε)) ∈ aBase ε := by
  cases ε <;> decide

theorem eq_one_of_fix_R {y : Equiv.Perm (Fin (aDeg ε))} (hy : y ∈ AT ε)
    (hfix : ∀ z ∈ Rset ε, y z = z) : y = 1 := by
  have hV : ValidSchreier (aQ ε) := ofArrays_valid (by norm_num) (aut_parts ε).1
  have h1 : y ∈ (aQ ε).levelSubgroup (aQ ε).baseCount := by
    rw [RawSchreierDatum.mem_levelSubgroup_iff _ hV _ le_rfl]
    refine ⟨hy, fun b hb => hfix b (aBase_mem_R ?_)⟩
    have : (aQ ε).base.toList = aBase ε := RawSchreierDatum.ofArrays_base_toList
    rw [List.take_of_length_le (by simp), this] at hb
    exact hb
  rw [RawSchreierDatum.levelSubgroup_terminal_eq_bot _ hV, mem_bot] at h1
  exact h1

theorem cent_AT {x : Equiv.Perm (Fin (aDeg ε))} (hxA : x ∈ AT ε)
    (hx : ∀ v, x * psiTM ε v = psiTM ε v * x) : ∃ v, x = psiTM ε v := by
  set z0 : Fin (aDeg ε) := ⟨0, by have := one_le_aDeg ε; omega⟩
  have hz0 : z0 ∈ Rset ε := aBase_mem_R zero_mem_aBase
  have hxR : x z0 ∈ Rset ε := by
    intro v hv e
    apply hz0 v hv
    have h1 : x (psiTM ε v z0) = psiTM ε v (x z0) := by
      have := congrArg (fun g : Equiv.Perm (Fin (aDeg ε)) => g z0) (hx v)
      simpa [Equiv.Perm.mul_apply] using this
    rw [e] at h1
    exact x.injective h1
  obtain ⟨v, hv⟩ := exists_psiTM_apply hxR
  obtain ⟨y, hy⟩ : ∃ y, y = (psiTM ε v)⁻¹ * x := ⟨_, rfl⟩
  have hyA : y ∈ AT ε := hy ▸ mul_mem (inv_mem (psiTM_mem_A v)) hxA
  have hcomm : ∀ w, psiTM ε w * psiTM ε v = psiTM ε v * psiTM ε w := fun w => by
    rw [← psiTM_add, ← psiTM_add, add_comm]
  have hyQ : ∀ w, y * psiTM ε w = psiTM ε w * y := by
    intro w
    rw [hy]
    calc (psiTM ε v)⁻¹ * x * psiTM ε w = (psiTM ε v)⁻¹ * (x * psiTM ε w) := by group
      _ = (psiTM ε v)⁻¹ * (psiTM ε w * x) := by rw [hx w]
      _ = (psiTM ε v)⁻¹ * (psiTM ε w * psiTM ε v) * ((psiTM ε v)⁻¹ * x) := by group
      _ = (psiTM ε v)⁻¹ * (psiTM ε v * psiTM ε w) * ((psiTM ε v)⁻¹ * x) := by rw [hcomm w]
      _ = psiTM ε w * ((psiTM ε v)⁻¹ * x) := by group
  have hy0 : y z0 = z0 := by
    rw [hy, Equiv.Perm.mul_apply, ← hv]
    simp [z0]
  have hfix : ∀ z ∈ Rset ε, y z = z := by
    intro z hz
    obtain ⟨w, rfl⟩ := exists_psiTM_apply hz
    have := congrArg (fun g : Equiv.Perm (Fin (aDeg ε)) => g z0) (hyQ w)
    simp only [Equiv.Perm.mul_apply, hy0] at this
    exact this
  have hy1 := eq_one_of_fix_R hyA hfix
  refine ⟨v, ?_⟩
  have := congrArg (fun g => psiTM ε v * g) (hy.symm.trans hy1)
  simpa using this

theorem aut_match (ε : Eps) {y : ℕ} (hy : y < 64) :
    (match ε with
      | .plus => memOmPlus (psiTT ε y) && eqA 120 (OmegaEight.copy0Arr (psiTT ε y)) (psiArr .plus y)
      | .minus => eqA 136 (psiTT ε y) (psiArr .minus y)) = true := by
  have h := autChecks ε
  simp only [autCheck, Bool.and_eq_true, allLt_iff] at h
  exact (h.1.1.1.2 y hy).2

@[expose] noncomputable def psiMm (v : V6) : Equiv.Perm (Fin 136) := psiM .minus v

@[expose] noncomputable def psiTMm (v : V6) : Equiv.Perm (Fin 136) := psiTM .minus v

@[expose] noncomputable def QMmm : Subgroup (Equiv.Perm (Fin 136)) := QMm .minus

theorem psiTMm_eq (v : V6) : psiTMm v = psiMm v :=
  eq_of_eqA (rep_psiTM (ε := .minus) v).1 (rep_psiM (ε := .minus) v).1
    (aut_match .minus (vecBits_lt v))

theorem aut_cent_minus (α : MulAut OmegaEightMinus.omegaT)
    (hα : ∀ x : OmegaEightMinus.omegaT, (x : Equiv.Perm (Fin 136)) ∈ QMmm → α x = x) :
    ∃ q₀ : Equiv.Perm (Fin 136), q₀ ∈ QMmm ∧ ∀ x : OmegaEightMinus.omegaT,
      (α x : Equiv.Perm (Fin 136)) = q₀ * x * q₀⁻¹ := by
  obtain ⟨a, rfl⟩ := OmegaEightMinus.autEquiv.surjective α
  have haA : (a : Equiv.Perm (Fin 136)) ∈ AT .minus := by
    rw [AT_minus]
    exact a.2
  have hcomm : ∀ v, (a : Equiv.Perm (Fin 136)) * psiTMm v = psiTMm v * a := by
    intro v
    have hmem : psiMm v ∈ OmegaEightMinus.omegaT := psiM_mem_L (ε := .minus) v
    have h1 := hα ⟨psiMm v, hmem⟩ (psiM_mem_Q (ε := .minus) v)
    have h2 := OmegaEightMinus.autEquiv_apply a ⟨psiMm v, hmem⟩
    rw [h1] at h2
    change psiMm v = (a : Equiv.Perm (Fin 136)) * psiMm v * (a : Equiv.Perm (Fin 136))⁻¹ at h2
    rw [psiTMm_eq]
    calc (a : Equiv.Perm (Fin 136)) * psiMm v
        = ((a : Equiv.Perm (Fin 136)) * psiMm v * (a : Equiv.Perm (Fin 136))⁻¹) * a := by group
      _ = psiMm v * a := by rw [← h2]
  obtain ⟨v₀, hv₀⟩ := cent_AT (ε := .minus) haA hcomm
  refine ⟨psiMm v₀, psiM_mem_Q (ε := .minus) v₀, fun x => ?_⟩
  rw [OmegaEightMinus.autEquiv_apply]
  have hv₀' : (a : Equiv.Perm (Fin 136)) = psiMm v₀ := hv₀.trans (psiTMm_eq v₀)
  rw [hv₀']

@[expose] noncomputable def psiMp (v : V6) : Equiv.Perm (Fin 120) := psiM .plus v

@[expose] noncomputable def psiTMp (v : V6) : Equiv.Perm (Fin 360) := psiTM .plus v

@[expose] noncomputable def QMmp : Subgroup (Equiv.Perm (Fin 120)) := QMm .plus

theorem psiTMp_mem_omegaT (v : V6) : psiTMp v ∈ OmegaEight.omegaT := by
  have h := aut_match .plus (vecBits_lt v)
  simp only [Bool.and_eq_true] at h
  exact (ofArrays_mem_iff (by norm_num) OmegaEight.omegaChain_ok.1
    (rep_psiTM (ε := .plus) v).1).1 h.1

theorem psiMp_mem (v : V6) : psiMp v ∈ OmegaEight.omega1T := psiM_mem_L (ε := .plus) v

theorem restrict_psiTMp (v : V6) :
    OmegaEight.omegaRestrictEquiv ⟨psiTMp v, psiTMp_mem_omegaT v⟩ = ⟨psiMp v, psiMp_mem v⟩ := by
  have h := aut_match .plus (vecBits_lt v)
  simp only [Bool.and_eq_true] at h
  apply Subtype.ext
  apply Equiv.ext
  intro j
  apply Fin.ext
  rw [OmegaEight.omegaRestrictEquiv_apply, OmegaEight.omegaRes_apply_val]
  have h1 := (rep_psiTM (ε := .plus) v).1.apply (show (j : ℕ) < 360 by omega)
  have h2 := (rep_psiM (ε := .plus) v).1.apply j.2
  have h3 := allLt_spec h.2 j.2
  rw [beq_iff_eq, OmegaEight.copy0Arr_getElem! _ j.2] at h3
  change ((psiTM .plus v) ⟨j, _⟩ : ℕ) = ((psiM .plus v) j : ℕ)
  rw [← h1, h3, h2]
  rfl

theorem aut_cent_plus (α : MulAut OmegaEight.omega1T)
    (hα : ∀ x : OmegaEight.omega1T, (x : Equiv.Perm (Fin 120)) ∈ QMmp → α x = x) :
    ∃ q₀ : Equiv.Perm (Fin 120), q₀ ∈ QMmp ∧ ∀ x : OmegaEight.omega1T,
      (α x : Equiv.Perm (Fin 120)) = q₀ * x * q₀⁻¹ := by
  set r := OmegaEight.omegaRestrictEquiv
  set α' : MulAut OmegaEight.omegaT := (r.trans α).trans r.symm
  obtain ⟨a, ha⟩ := OmegaEight.autEquiv.surjective α'
  have haA : (a : Equiv.Perm (Fin 360)) ∈ AT .plus := by
    rw [AT_plus]
    exact a.2
  have hfix : ∀ v, α' ⟨psiTMp v, psiTMp_mem_omegaT v⟩ = ⟨psiTMp v, psiTMp_mem_omegaT v⟩ := by
    intro v
    simp only [α', MulEquiv.trans_apply]
    rw [restrict_psiTMp, hα ⟨psiMp v, psiMp_mem v⟩ (psiM_mem_Q (ε := .plus) v),
      ← restrict_psiTMp, MulEquiv.symm_apply_apply]
  have hcomm : ∀ v, (a : Equiv.Perm (Fin 360)) * psiTMp v = psiTMp v * a := by
    intro v
    have h2 := OmegaEight.autEquiv_apply a ⟨psiTMp v, psiTMp_mem_omegaT v⟩
    rw [ha, hfix] at h2
    change psiTMp v = (a : Equiv.Perm (Fin 360)) * psiTMp v * (a : Equiv.Perm (Fin 360))⁻¹ at h2
    calc (a : Equiv.Perm (Fin 360)) * psiTMp v
        = ((a : Equiv.Perm (Fin 360)) * psiTMp v * (a : Equiv.Perm (Fin 360))⁻¹) * a := by group
      _ = psiTMp v * a := by rw [← h2]
  obtain ⟨v₀, hv₀⟩ := cent_AT (ε := .plus) haA hcomm
  refine ⟨psiMp v₀, psiM_mem_Q (ε := .plus) v₀, fun x => ?_⟩
  have e1 : α x = r (α' (r.symm x)) := by simp [α']
  have e2 : α' (r.symm x) = ⟨psiTMp v₀, psiTMp_mem_omegaT v₀⟩ * r.symm x *
      (⟨psiTMp v₀, psiTMp_mem_omegaT v₀⟩ : OmegaEight.omegaT)⁻¹ := by
    apply Subtype.ext
    rw [← ha, OmegaEight.autEquiv_apply]
    rw [show (a : Equiv.Perm (Fin 360)) = psiTMp v₀ from hv₀]
    rfl
  rw [e1, e2, map_mul, map_mul, map_inv, restrict_psiTMp, MulEquiv.apply_symm_apply]
  rfl

theorem autCent (ε : Eps) : AutCent (Lm ε) (QMm ε) := by
  cases ε
  · exact fun α hα => aut_cent_plus α hα
  · exact fun α hα => aut_cent_minus α hα

end CFSG.EvenSmallLie.OmegaEight.Stage1.Model

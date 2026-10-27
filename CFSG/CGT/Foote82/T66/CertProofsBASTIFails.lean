module

public import CFSG.CGT.Foote82.T66.CitedBAS
public import Certificates.Certificate7093
public import Certificates.Certificate919001
public import Certificates.Certificate919003
public import Certificates.Certificate919004
public import Certificates.Certificate919010
import CFSG.CGT.Foote82.T66.CertProofsBASMaximalAlt
import CFSG.CGT.Foote82.T66.CertProofsBASMaximal
import CFSG.CGT.Foote82.T66.CertProofsOmegaSixNormalizer
import CFSG.CGT.Foote82.T66.CertProofsOmegaSixA6Centralizer
import CFSG.CGT.Foote82.T66.CertProofsInvolAutA6
import CFSG.CGT.Foote82.T66.OmegaMinusMatrix
import CFSG.CGT.Foote82.T66.BranchARecog
import CFSG.CGT.Foote82.T66.GLSixCodes
import CFSG.CGT.Foote82.T66.FaithfulBasic
import CFSG.Quasithin.Background.G11Basic
import Mathlib.Tactic.Group
public import CFSG.CGT.Foote82.T66.MC1Steps
public import CFSG.CGT.Foote82.T66.Steps
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUp.BlockOrder
public import CFSG.CGT.PushingUpLit.BHS7.BlockComm
public import CFSG.CGT.PushingUpLit.BHS7.SevenThree
public import CFSG.CGT.PushingUpLit.BHS7.VFacts
public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.Fischer.Classification.Defs
public import CFSG.GroupTheory.ConjugatePairSubnormality
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockInputs
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
import CFSG.CGT.Foote82.T66.BranchAGen
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.BASTI

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem ti_of_comm {L : Subgroup (GLV V)} {d l : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hl : l ∈ L) (hdd : d * d = 1)
    (hc : d * (l * d * l⁻¹) = (l * d * l⁻¹) * d) {w : V} (hw : w ∈ commSpace L ⊤)
    (hnz : d ((l * d * l⁻¹) w - w) - ((l * d * l⁻¹) w - w) ≠ 0) :
    l * d * l⁻¹ ≠ d ∧ d * (l * d * l⁻¹) = (l * d * l⁻¹) * d ∧
      commSpace (Subgroup.zpowers d) (commSpace L ⊤) ⊓
        commSpace (Subgroup.zpowers (l * d * l⁻¹)) (commSpace L ⊤) ≠ ⊥ := by
  set e := l * d * l⁻¹ with he
  have heN : e ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.le_normalizer hl) hd)
      (Subgroup.inv_mem _ (Subgroup.le_normalizer hl))
  have hew : e w ∈ commSpace L ⊤ := OmegaMinusMat.apply_mem_commSpace heN hw
  have hdw : d w ∈ commSpace L ⊤ := OmegaMinusMat.apply_mem_commSpace hd hw
  have hvv : ∀ y : V, y + y = 0 := fun y => by
    nth_rewrite 2 [← ZModModule.neg_eq_self y]
    exact add_neg_cancel y
  refine ⟨fun h => hnz ?_, hc, fun hbot => hnz ?_⟩
  ·
    rw [h]
    have hddw : d (d w) = w := by
      rw [← LinearEquiv.mul_apply, hdd]
      rfl
    rw [map_sub, hddw]
    calc w - d w - (d w - w) = (w - d w) + (w - d w) := by abel
      _ = 0 := hvv _
  · have h1 : d (e w - w) - (e w - w) ∈ commSpace (Subgroup.zpowers d) (commSpace L ⊤) :=
      sub_mem_commSpace (Subgroup.mem_zpowers d) ((commSpace L ⊤).sub_mem hew hw)
    have hde : d (e w) = e (d w) := congrArg (fun g : GLV V => g w) hc
    have hswap : d (e w - w) - (e w - w) = e (d w - w) - (d w - w) := by
      rw [map_sub, map_sub, hde]
      abel
    have h2 : d (e w - w) - (e w - w) ∈ commSpace (Subgroup.zpowers e) (commSpace L ⊤) := by
      rw [hswap]
      exact sub_mem_commSpace (Subgroup.mem_zpowers e) ((commSpace L ⊤).sub_mem hdw hw)
    have h3 : d (e w - w) - (e w - w) ∈ (⊥ : Submodule (ZMod 2) V) := by
      rw [← hbot]
      exact ⟨h1, h2⟩
    exact (Submodule.mem_bot _).mp h3

theorem mul_conj_mem {L : Subgroup (GLV V)} {d l : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hl : l ∈ L) (hdd : d * d = 1) :
    d * (l * d * l⁻¹) ∈ L ∧ (l * d * l⁻¹) * d ∈ L := by
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hc1 : d * l * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hd l).mp hl
  have hc2 : d * l⁻¹ * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hd l⁻¹).mp (L.inv_mem hl)
  refine ⟨?_, ?_⟩
  · have e : d * (l * d * l⁻¹) = (d * l * d⁻¹) * l⁻¹ := by
      rw [hdinv]
      group
    rw [e]
    exact L.mul_mem hc1 (L.inv_mem hl)
  · have e : (l * d * l⁻¹) * d = l * (d * l⁻¹ * d⁻¹) := by
      rw [hdinv]
      group
    rw [e]
    exact L.mul_mem hl hc2

section OmegaSix

open Matrix CFSG.CGT.Foote82.OmegaSix CFSG.ClassicalInvolution.Solomon73.Yamaki
  CFSG.ClassicalInvolution.Sp62Rec.Z6NA

local notation "GL6" => GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)
local notation "Mat6" => Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (ZMod 2)

theorem tiCheck_holds : tiCheck () = true :=
  Certificates.certificate919010

private theorem glCode_get_lt (t : GL6) {k : ℕ} (hk : k < 64) : (glCode t)[k]! < 64 := by
  rw [glCode, marr_get _ hk]
  exact vcode_lt _

theorem exists_ti_conj
    {D : GL6}
    (hDO : D ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1) (hDD : D * D = 1) (hD1 : D ≠ 1)
    (hrk : ((D : Mat6) - 1).rank ≠ 1) :
    ∃ G ∈ omegaMinusTwo 2, D * (G * D * G⁻¹) = (G * D * G⁻¹) * D ∧
      ∃ v, ((D : Mat6) - 1) *ᵥ ((((G * D * G⁻¹ : GL6) : Mat6) - 1) *ᵥ v) ≠ 0 := by
  obtain ⟨i, hi, hie⟩ := exists_oEnum hDO
  have h := tiCheck_holds
  simp only [tiCheck, allLt_iff] at h
  have hi' := h i hi
  rw [hie] at hi'
  simp only [Bool.or_eq_true] at hi'
  have hsq : compA (glCode D) (glCode D) = idA () := by
    rw [← isArrCode_glCode.mul, hDD, isArrCode_glCode.one]
  rcases hi' with ((h1 | h1) | h1) | h1
  · rw [hsq] at h1
    simp at h1
  · exfalso
    apply hD1
    apply isArrCode_glCode.injective
    rw [isArrCode_glCode.one]
    exact beq_iff_eq.mp h1
  · exact absurd (rank_sub_one_of_rank1 h1) hrk
  rw [CFSG.CGT.Foote82.InvolA6.anyLt_iff] at h1
  obtain ⟨j, hj, hj'⟩ := h1
  generalize ((omegaEnum ()).lookup (CFSG.CGT.Foote82.InvolA6.invArr (omegaEnum ()).elems[j]!)).getD 0
    = k at hj'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hj'
  obtain ⟨⟨hk, hinv⟩, hwit⟩ := hj'
  obtain ⟨Gx, hGx⟩ := exists_glArr_eq hj
  obtain ⟨Hx, hHx⟩ := exists_glArr_eq hk
  rw [← hGx, ← hHx] at hinv hwit
  have hHG : Hx = Gx⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ((isArrCode_glArr (omegaMinusTwo 2)).injective ?_)
    rw [(isArrCode_glArr (omegaMinusTwo 2)).mul, hinv, (isArrCode_glArr (omegaMinusTwo 2)).one]
  subst hHG
  set G : GL6 := (Gx : GL6) with hG
  have hgl : ∀ x : ↥(omegaMinusTwo 2), glArr x = glCode (x : GL6) := fun _ => rfl
  rw [hgl, hgl, Subgroup.coe_inv] at hwit
  simp only [tiWitness, Bool.and_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
    bne_iff_ne, ne_eq] at hwit
  obtain ⟨hpp, k', hk', hne⟩ := hwit
  have hu : compA (compA (glCode G) (glCode D)) (glCode G⁻¹) = glCode (G * D * G⁻¹) := by
    rw [isArrCode_glCode.mul, isArrCode_glCode.mul]
  rw [hu] at hpp hne
  have hp : compA (glCode D) (glCode (G * D * G⁻¹)) = glCode (D * (G * D * G⁻¹)) :=
    (isArrCode_glCode.mul _ _).symm
  rw [hp] at hpp
  have hpp' : D * (G * D * G⁻¹) * (D * (G * D * G⁻¹)) = 1 := by
    apply isArrCode_glCode.injective
    rw [isArrCode_glCode.mul, hpp, isArrCode_glCode.one]
  refine ⟨G, Gx.2, ?_, cvec k', ?_⟩
  ·
    have hD' : (G * D * G⁻¹) * (G * D * G⁻¹) = 1 := by
      calc (G * D * G⁻¹) * (G * D * G⁻¹) = G * (D * D) * G⁻¹ := by group
        _ = 1 := by rw [hDD, mul_one, mul_inv_cancel]
    have hinvD : D⁻¹ = D := inv_eq_of_mul_eq_one_right hDD
    have hinvD' : (G * D * G⁻¹)⁻¹ = G * D * G⁻¹ := inv_eq_of_mul_eq_one_right hD'
    have h1 := eq_inv_of_mul_eq_one_left hpp'
    rw [_root_.mul_inv_rev, hinvD, hinvD'] at h1
    exact h1
  · have hm := glCode_get_lt (G * D * G⁻¹) hk'
    have hm' : (glCode (G * D * G⁻¹))[k']! ^^^ k' < 64 := Nat.xor_lt_two_pow (n := 6) hm hk'
    rw [sub_one_mulVec_cvec _ hk', sub_one_mulVec_cvec _ hm']
    refine cvec_ne_zero (Nat.xor_lt_two_pow (n := 6) (glCode_get_lt D hm') hm') ?_
    intro h0
    exact hne (Nat.eq_of_xor_eq_zero h0)

theorem basTIFails_omegaSix
    [Finite V]
    {L : Subgroup (GLV V)} (hL : IsOmegaMinusModule L 2) (hf : FaithfulTildeV L) {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hd2 : orderOf d = 2)
    (hrank : Module.finrank (ZMod 2) ↥(tildeVBot L) + 2 ≤
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d)) :
    ∃ l ∈ L, l * d * l⁻¹ ≠ d ∧ d * (l * d * l⁻¹) = (l * d * l⁻¹) * d ∧
      commSpace (Subgroup.zpowers d) (commSpace L ⊤) ⊓
        commSpace (Subgroup.zpowers (l * d * l⁻¹)) (commSpace L ⊤) ≠ ⊥ := by
  obtain ⟨α, hαs, β, hβs, hβker, hrel⟩ := hL
  have hβk : ∀ w, β w = 0 ↔ (w : V) ∈ fixedSpace L := L13Aux.ker_iff_of_eq hβker
  have hrel' : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) w →
      β w' = (((α ℓ : ↥(omegaMinusTwo 2)) : GL6) : Mat6) *ᵥ β w := hrel
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, sq] at h
    exact h
  obtain ⟨D, hDD, hD⟩ := OmegaMinusMat.exists_matrix hβs hβk hd hdd
  have hconj := OmegaMinusMat.conj_eq hβs hrel' hd hdd hDD hD
  have hDO : D ∈ CFSG.PGLModel.orthogonalMinus 2 (ZMod 2) 1 1 := by
    refine omegaMinusSixNormalizer_holds D hDD fun y hy => ?_
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨y, hy⟩
    have hℓ'L : d * (ℓ : GLV V) * d⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hd _).1 ℓ.2
    have h := hconj ℓ ⟨_, hℓ'L⟩ rfl
    rw [hℓ] at h
    have h' : D * y * D⁻¹ = ((α ⟨_, hℓ'L⟩ : ↥(omegaMinusTwo 2)) : GL6) := h
    rw [h']
    exact (α _).2
  have hrk := OmegaMinusMat.finrank_range_add hβs hβk hd hdd hD
  have hrk2 : 2 ≤ ((D : Mat6) - 1).rank := by
    rw [Matrix.rank]
    omega
  have hD1 : D ≠ 1 := by
    intro h
    rw [h, Units.val_one, sub_self, Matrix.rank_zero] at hrk2
    omega
  obtain ⟨G, hG, hcomm, v, hv⟩ := exists_ti_conj hDO hDD hD1 (by omega)
  obtain ⟨ℓ, hℓ⟩ := hαs ⟨G, hG⟩
  have hαi := BASMax.injective_alpha hβk hrel' hf
  have hU : ∀ x ∈ Subgroup.normalizer (L : Set (GLV V)), ∀ w ∈ commSpace L ⊤,
      x w ∈ commSpace L ⊤ := fun x hx w hw => OmegaMinusMat.apply_mem_commSpace hx hw
  have hαℓ : ((α ℓ : ↥(omegaMinusTwo 2)) : GL6) = G := by rw [hℓ]
  have hαℓi : ((α ℓ⁻¹ : ↥(omegaMinusTwo 2)) : GL6) = G⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, hαℓ]
  have hℓN : (ℓ : GLV V) ∈ Subgroup.normalizer (L : Set (GLV V)) := Subgroup.le_normalizer ℓ.2
  have hℓiN : ((ℓ⁻¹ : ↥L) : GLV V) ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.le_normalizer (ℓ⁻¹).2
  have hRℓ : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = (ℓ : GLV V) w →
      β w' = (G : Mat6) *ᵥ β w := fun w w' h => by rw [← hαℓ]; exact hrel' ℓ w w' h
  have hRℓi : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = ((ℓ⁻¹ : ↥L) : GLV V) w →
      β w' = ((G⁻¹ : GL6) : Mat6) *ᵥ β w := fun w w' h => by rw [← hαℓi]; exact hrel' ℓ⁻¹ w w' h
  have hRe0 := OmegaMinusMat.rel_mul (hU _ (Subgroup.mul_mem _ hd hℓiN)) hRℓ
    (OmegaMinusMat.rel_mul (hU _ hℓiN) hD hRℓi)
  have hecoe : (ℓ : GLV V) * (d * ((ℓ⁻¹ : ↥L) : GLV V)) = (ℓ : GLV V) * d * (ℓ : GLV V)⁻¹ := by
    rw [Subgroup.coe_inv, mul_assoc]
  have hRe : ∀ w w' : ↥(commSpace L ⊤), (w' : V) = ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) w →
      β w' = ((G * D * G⁻¹ : GL6) : Mat6) *ᵥ β w := fun w w' h => by
    rw [← hecoe] at h
    rw [mul_assoc G]
    exact hRe0 w w' h
  have heN : (ℓ : GLV V) * d * (ℓ : GLV V)⁻¹ ∈ Subgroup.normalizer (L : Set (GLV V)) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hℓN hd) (Subgroup.inv_mem _ hℓN)
  have hmatL : ∀ (x : ↥L) (X : GL6), (∀ w w' : ↥(commSpace L ⊤), (w' : V) = (x : GLV V) w →
      β w' = (X : Mat6) *ᵥ β w) → ((α x : ↥(omegaMinusTwo 2)) : GL6) = X := by
    intro x X hX
    apply Units.ext
    rw [ext_iff_mulVec]
    intro u
    obtain ⟨w, rfl⟩ := hβs u
    have hxw : (x : GLV V) w ∈ commSpace L ⊤ := hU _ (Subgroup.le_normalizer x.2) w w.2
    rw [← hrel' x w ⟨_, hxw⟩ rfl, ← hX w ⟨_, hxw⟩ rfl]
  obtain ⟨hdeL, hedL⟩ := mul_conj_mem hd ℓ.2 hdd
  have h1 := hmatL ⟨_, hdeL⟩ (D * (G * D * G⁻¹)) (OmegaMinusMat.rel_mul (hU _ heN) hD hRe)
  have h2 := hmatL ⟨_, hedL⟩ ((G * D * G⁻¹) * D) (OmegaMinusMat.rel_mul (hU _ hd) hRe hD)
  have hc : d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) = ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) * d := by
    have h := hαi (Subtype.ext (h1.trans (hcomm.trans h2.symm)))
    exact congrArg Subtype.val h
  obtain ⟨w, hw⟩ := hβs v
  set e := (ℓ : GLV V) * d * (ℓ : GLV V)⁻¹ with he
  have hew : e w ∈ commSpace L ⊤ := hU _ heN w w.2
  set w₂ : ↥(commSpace L ⊤) := ⟨e w, hew⟩ - w with hw₂
  have hβw₂ : β w₂ = (((G * D * G⁻¹ : GL6) : Mat6) - 1) *ᵥ v := by
    rw [hw₂, map_sub, hRe w ⟨e w, hew⟩ rfl, hw, sub_mulVec, one_mulVec]
  have hdw₂ : d w₂ ∈ commSpace L ⊤ := hU _ hd w₂ w₂.2
  have hβy : β (⟨d w₂, hdw₂⟩ - w₂) =
      ((D : Mat6) - 1) *ᵥ ((((G * D * G⁻¹ : GL6) : Mat6) - 1) *ᵥ v) := by
    rw [map_sub, hD w₂ ⟨d w₂, hdw₂⟩ rfl, hβw₂, sub_mulVec (D : Mat6) 1, one_mulVec]
  have hnz : d (e w - w) - (e w - w) ≠ 0 := by
    intro h0
    apply hv
    rw [← hβy]
    have : (⟨d w₂, hdw₂⟩ - w₂ : ↥(commSpace L ⊤)) = 0 := Subtype.ext h0
    rw [this, map_zero]
  exact ⟨ℓ, ℓ.2, ti_of_comm hd ℓ.2 hdd hc w.2 hnz⟩

end OmegaSix

section AltSix

open Equiv Equiv.Perm CFSG.QuasithinUnique BASMaxAlt CFSG.Quasithin.H13

private def cyc3 : Perm (Fin 6) := swap 3 5 * swap 3 4

private def cyc5 : Perm (Fin 6) := swap 1 5 * swap 1 3 * swap 1 4 * swap 1 2

private theorem sign_cyc3 : sign cyc3 = 1 := by
  rw [cyc3, map_mul, sign_swap (by decide), sign_swap (by decide)]
  decide

private theorem sign_cyc5 : sign cyc5 = 1 := by
  rw [cyc5, map_mul, map_mul, map_mul, sign_swap (by decide), sign_swap (by decide),
    sign_swap (by decide), sign_swap (by decide)]
  decide

private theorem inv22_facts :
    (inv22 * (cyc5 * inv22 * cyc5⁻¹)) ^ 4 = 1 ∧ (inv22 * (cyc5 * inv22 * cyc5⁻¹)) ^ 2 ≠ 1 := by
  decide +kernel

private theorem inv222_comm :
    (inv222 * (cyc3 * inv222 * cyc3⁻¹)) * (inv222 * (cyc3 * inv222 * cyc3⁻¹)) = 1 := by
  decide +kernel

private theorem inv222_vec :
    heartAct 6 inv222 (heartAct 6 (cyc3 * inv222 * cyc3⁻¹)
        (QuotientAddGroup.mk (wt2 1 5 (by decide))) - QuotientAddGroup.mk (wt2 1 5 (by decide))) -
      (heartAct 6 (cyc3 * inv222 * cyc3⁻¹) (QuotientAddGroup.mk (wt2 1 5 (by decide))) -
        QuotientAddGroup.mk (wt2 1 5 (by decide))) ≠ 0 := by
  have key : ∀ v : evenWeight 6,
      (¬ ∀ i j : Fin 6, (v : Fin 6 → ZMod 2) i = (v : Fin 6 → ZMod 2) j) →
        (QuotientAddGroup.mk v : CFSG.Quasithin.AltHeart 6) ≠ 0 :=
    fun v hv h => hv ((QuotientAddGroup.eq_zero_iff v).mp h)
  rw [heartAct_mk, ← QuotientAddGroup.mk_sub, heartAct_mk, ← QuotientAddGroup.mk_sub]
  apply key
  decide +kernel

private theorem orderOf_eq_four {G : Type*} [Group G] {z : G} (h4 : z ^ 4 = 1) (h2 : z ^ 2 ≠ 1) :
    orderOf z = 4 := by
  have hd : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hn2 : ¬ orderOf z ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.mp h)
  have hle : orderOf z ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  generalize orderOf z = n at hd hn2 hle ⊢
  interval_cases n <;> omega

private theorem exists_order_four {π : Perm (Fin 6)} (hct : π.cycleType = {2, 2}) :
    ∃ σ : Perm (Fin 6), sign σ = 1 ∧ orderOf (π * (σ * π * σ⁻¹)) = 4 := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv22.trans hct.symm))
  refine ⟨g * cyc5 * g⁻¹, by rw [map_mul, map_mul, sign_cyc5, mul_one, map_inv, mul_inv_cancel],
    ?_⟩
  have e : π * ((g * cyc5 * g⁻¹) * π * (g * cyc5 * g⁻¹)⁻¹) =
      MulAut.conj g (inv22 * (cyc5 * inv22 * cyc5⁻¹)) := by
    rw [← hg, MulAut.conj_apply]
    group
  rw [e, MulEquiv.orderOf_eq]
  exact orderOf_eq_four inv22_facts.1 inv22_facts.2

private theorem exists_ti_model {π : Perm (Fin 6)} (hct : π.cycleType = {2, 2, 2}) :
    ∃ σ : Perm (Fin 6), sign σ = 1 ∧
      (π * (σ * π * σ⁻¹)) * (π * (σ * π * σ⁻¹)) = 1 ∧
      ∃ y : CFSG.Quasithin.AltHeart 6, heartAct 6 π (heartAct 6 (σ * π * σ⁻¹) y - y) -
        (heartAct 6 (σ * π * σ⁻¹) y - y) ≠ 0 := by
  obtain ⟨g, hg⟩ :=
    isConj_iff.mp (isConj_iff_cycleType_eq.mpr (cycleType_inv222.trans hct.symm))
  have hconj : ∀ (x : Perm (Fin 6)) (y : CFSG.Quasithin.AltHeart 6),
      heartAct 6 (g * x * g⁻¹) (heartAct 6 g y) = heartAct 6 g (heartAct 6 x y) := by
    intro x y
    rw [← heartAct_mul, ← heartAct_mul, show g * x * g⁻¹ * g = g * x by group]
  have hσ : (g * cyc3 * g⁻¹) * π * (g * cyc3 * g⁻¹)⁻¹ = g * (cyc3 * inv222 * cyc3⁻¹) * g⁻¹ := by
    rw [← hg]
    group
  refine ⟨g * cyc3 * g⁻¹, by rw [map_mul, map_mul, sign_cyc3, mul_one, map_inv, mul_inv_cancel],
    ?_, heartAct 6 g (QuotientAddGroup.mk (wt2 1 5 (by decide))), ?_⟩
  · rw [hσ, ← hg]
    have e : g * inv222 * g⁻¹ * (g * (cyc3 * inv222 * cyc3⁻¹) * g⁻¹) *
        (g * inv222 * g⁻¹ * (g * (cyc3 * inv222 * cyc3⁻¹) * g⁻¹)) =
        g * ((inv222 * (cyc3 * inv222 * cyc3⁻¹)) * (inv222 * (cyc3 * inv222 * cyc3⁻¹))) * g⁻¹ := by
      group
    rw [e, inv222_comm, mul_one, mul_inv_cancel]
  · rw [hσ, hconj, ← map_sub, ← hg, hconj, ← map_sub]
    intro h0
    exact inv222_vec (heartAct_injective g (by rw [h0, map_zero]))

private theorem heartAct_swap_sub {i j : Fin 6} (hij : i ≠ j) (y : CFSG.Quasithin.AltHeart 6) :
    heartAct 6 (swap i j) y - y = 0 ∨
      heartAct 6 (swap i j) y - y = QuotientAddGroup.mk (wt2 i j hij) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [heartAct_mk, ← QuotientAddGroup.mk_sub]
  have hval : ∀ k, ((CFSG.Quasithin.permWeight 6 (swap i j) x - x : evenWeight 6) :
      Fin 6 → ZMod 2) k = (x : Fin 6 → ZMod 2) (swap i j k) - (x : Fin 6 → ZMod 2) k := by
    intro k
    rw [AddSubgroup.coe_sub, Pi.sub_apply]
    show (x : Fin 6 → ZMod 2) ((swap i j)⁻¹ k) - _ = _
    rw [swap_inv]
  by_cases hx : (x : Fin 6 → ZMod 2) i = (x : Fin 6 → ZMod 2) j
  · left
    have h0 : CFSG.Quasithin.permWeight 6 (swap i j) x - x = 0 := by
      apply Subtype.ext
      funext k
      rw [hval]
      by_cases hki : k = i
      · subst hki
        rw [swap_apply_left, hx, sub_self]
        rfl
      · by_cases hkj : k = j
        · subst hkj
          rw [swap_apply_right, hx, sub_self]
          rfl
        · rw [swap_apply_of_ne_of_ne hki hkj, sub_self]
          rfl
    rw [h0]
    rfl
  · right
    have h1 : ∀ a b : ZMod 2, a ≠ b → b - a = 1 := by decide
    congr 1
    apply Subtype.ext
    funext k
    rw [hval]
    show _ = if k = i ∨ k = j then (1 : ZMod 2) else 0
    by_cases hki : k = i
    · subst hki
      rw [swap_apply_left, if_pos (Or.inl rfl)]
      exact h1 _ _ hx
    · by_cases hkj : k = j
      · subst hkj
        rw [swap_apply_right, if_pos (Or.inr rfl)]
        exact h1 _ _ (Ne.symm hx)
      · rw [swap_apply_of_ne_of_ne hki hkj, sub_self, if_neg (by tauto)]

private theorem eq_one_or_eq_of_mem_zpowers' {G : Type*} [Group G] {e k : G} (he : e * e = 1)
    (hk : k ∈ Subgroup.zpowers e) : k = 1 ∨ k = e := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

theorem basTIFails_altSix [Finite V] {L : Subgroup (GLV V)}
    (hL : IsAltNaturalModule L 6) (hf : FaithfulTildeV L) {d : GLV V}
    (hd : d ∈ Subgroup.normalizer (L : Set (GLV V))) (hd2 : orderOf d = 2)
    (hodd : ∀ l ∈ L, orderOf (d * (l * d * l⁻¹)) ≤ 2 ∨ Odd (orderOf (d * (l * d * l⁻¹))))
    (hrank : Module.finrank (ZMod 2) ↥(tildeVBot L) + 2 ≤
      Module.finrank (ZMod 2) ↥(BAS.tvComm L d)) :
    ∃ l ∈ L, l * d * l⁻¹ ≠ d ∧ d * (l * d * l⁻¹) = (l * d * l⁻¹) * d ∧
      commSpace (Subgroup.zpowers d) (commSpace L ⊤) ⊓
        commSpace (Subgroup.zpowers (l * d * l⁻¹)) (commSpace L ⊤) ≠ ⊥ := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨α, hαs, β, hβs, hβk, hR⟩ := hL
  have hdd : d * d = 1 := by
    have h := pow_orderOf_eq_one d
    rw [hd2, pow_two] at h
    exact h
  have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
  have hker : ∀ w : ↥(commSpace L ⊤), β w = 0 ↔ (w : V) ∈ fixedSpace L := by
    intro w
    rw [← AddMonoidHom.mem_ker, hβk]
    rfl
  have hβℓ : ∀ (ℓ : ↥L) (w : ↥(commSpace L ⊤)) (x : evenWeight 6), β w = ↑x →
      β ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩ =
        ↑(evenWeightPerm (α ℓ : Perm (Fin 6)) x) :=
    fun ℓ w x hx => hR ℓ w _ rfl x hx
  have hαi : Function.Injective α := BranchAAux.injective_of_altNatural hf α β hβk hR
  obtain ⟨π, hπ2, hπψ, hπφ⟩ := exists_perm hαs hαi hβs hker hβℓ hd hdd
  have hπinv : π⁻¹ = π := inv_eq_of_mul_eq_one_right hπ2
  have hℓH : ∀ (ℓ : ↥L) (w : ↥(commSpace L ⊤)),
      heartEquiv (β ⟨(ℓ : GLV V) w, smul_mem_commSpace ℓ.2 w.2⟩) =
        heartAct 6 (α ℓ : Perm (Fin 6)) (heartEquiv (β w)) := by
    intro ℓ w
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β w)
    rw [hβℓ ℓ w x hx.symm, ← hx]
    rfl
  have hdimle : ∀ c : CFSG.Quasithin.AltHeart 6,
      (∀ y, heartAct 6 π y - y = 0 ∨ heartAct 6 π y - y = c) →
        Module.finrank (ZMod 2) ↥(BAS.tvComm L d) ≤
          Module.finrank (ZMod 2) ↥(tildeVBot L) + 1 := by
    intro c hc
    obtain ⟨w₀, hw₀⟩ := hβs (heartEquiv.symm c)
    have hle : BAS.tvComm L d ≤ Submodule.span (ZMod 2) {(w₀ : V)} ⊔ tildeVBot L := by
      refine sup_le ?_ le_sup_right
      refine commSpace_le_iff.2 fun k hk u hu => ?_
      rcases eq_one_or_eq_of_mem_zpowers' hdd hk with rfl | rfl
      · rw [show (1 : GLV V) u = u from rfl, sub_self]
        exact Submodule.zero_mem _
      · have hdu : k u ∈ commSpace L ⊤ := d_mem_commSpace hd hu
        have hβdu : heartEquiv (β (⟨k u, hdu⟩ - ⟨u, hu⟩)) =
            heartAct 6 π (heartEquiv (β ⟨u, hu⟩)) - heartEquiv (β ⟨u, hu⟩) := by
          rw [map_sub, map_sub, ← hπφ ⟨u, hu⟩]
        have hmem : ((⟨k u, hdu⟩ - ⟨u, hu⟩ : ↥(commSpace L ⊤)) : V) = k u - u := rfl
        rcases hc (heartEquiv (β ⟨u, hu⟩)) with h0 | h1
        · have hC := (hker _).mp (heartEquiv.injective (by rw [hβdu, h0, map_zero]))
          rw [hmem] at hC
          exact Submodule.mem_sup_right ⟨hC, (commSpace L ⊤).sub_mem hdu hu⟩
        · have hz : β (⟨k u, hdu⟩ - ⟨u, hu⟩ - w₀) = 0 := by
            apply heartEquiv.injective
            rw [map_sub, map_sub, hβdu, h1, hw₀, AddEquiv.apply_symm_apply, sub_self, map_zero]
          have hC := (hker _).mp hz
          have hmem' : ((⟨k u, hdu⟩ - ⟨u, hu⟩ - w₀ : ↥(commSpace L ⊤)) : V) =
              k u - u - w₀ := rfl
          rw [hmem'] at hC
          rw [show k u - u = (w₀ : V) + (k u - u - w₀) by abel]
          exact Submodule.add_mem_sup (Submodule.mem_span_singleton_self _)
            ⟨hC, (commSpace L ⊤).sub_mem ((commSpace L ⊤).sub_mem hdu hu) w₀.2⟩
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span (ZMod 2) {(w₀ : V)}) (tildeVBot L)
    have h3 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) ({(w₀ : V)} : Set V)) ≤ 1 := by
      by_cases hw : (w₀ : V) = 0
      · rw [hw, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
        exact Nat.zero_le _
      · rw [finrank_span_singleton hw]
    omega
  have hπ1 : π ≠ 1 := by
    intro h
    have := hdimle 0 fun y => Or.inl (by rw [h, heartAct_one, sub_self])
    omega
  have hsw : ¬ π.IsSwap := by
    rintro ⟨i, j, hij, hπij⟩
    have := hdimle _ fun y => by rw [hπij]; exact heartAct_swap_sub hij y
    omega
  have hord : orderOf π = 2 := orderOf_eq_prime (by rw [pow_two, hπ2]) hπ1
  obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two : (orderOf π).Prime)
  rw [hord] at hn
  have hsum := sum_cycleType_le π
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · exact absurd (isSwap_iff_cycleType.mpr hn) hsw
  ·
    exfalso
    obtain ⟨σ, hσs, hσo⟩ := exists_order_four (π := π) (by rw [hn]; rfl)
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨σ, mem_alternatingGroup.mpr hσs⟩
    obtain ⟨hdeL, -⟩ := mul_conj_mem hd ℓ.2 hdd
    have hcdL : d * (ℓ : GLV V) * d⁻¹ ∈ L := conj_mem hd ℓ.2
    have hx : (⟨_, hdeL⟩ : ↥L) = ⟨d * (ℓ : GLV V) * d⁻¹, hcdL⟩ * ℓ⁻¹ := by
      apply Subtype.ext
      show d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) = d * (ℓ : GLV V) * d⁻¹ * (ℓ : GLV V)⁻¹
      rw [hdinv]
      group
    have hαx : ((α ⟨_, hdeL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        π * (σ * π * σ⁻¹) := by
      rw [hx, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπψ ℓ, hℓ, hπinv]
      group
    have hord4 : orderOf (d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹)) = 4 := by
      rw [← Subgroup.orderOf_mk _ hdeL, ← orderOf_injective α hαi, ← Subgroup.orderOf_coe, hαx,
        hσo]
    rcases hodd (ℓ : GLV V) ℓ.2 with h | h
    · omega
    · rw [hord4] at h
      exact absurd h (by decide)
  ·
    obtain ⟨σ, hσs, hsq, y, hy⟩ := exists_ti_model (π := π) (by rw [hn]; rfl)
    obtain ⟨ℓ, hℓ⟩ := hαs ⟨σ, mem_alternatingGroup.mpr hσs⟩
    obtain ⟨hdeL, hedL⟩ := mul_conj_mem hd ℓ.2 hdd
    have hcdL : d * (ℓ : GLV V) * d⁻¹ ∈ L := conj_mem hd ℓ.2
    have hcdL' : d * ((ℓ⁻¹ : ↥L) : GLV V) * d⁻¹ ∈ L := conj_mem hd (ℓ⁻¹).2
    have hx1 : (⟨_, hdeL⟩ : ↥L) = ⟨d * (ℓ : GLV V) * d⁻¹, hcdL⟩ * ℓ⁻¹ := by
      apply Subtype.ext
      show d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) = d * (ℓ : GLV V) * d⁻¹ * (ℓ : GLV V)⁻¹
      rw [hdinv]
      group
    have hx2 : (⟨_, hedL⟩ : ↥L) = ℓ * ⟨d * ((ℓ⁻¹ : ↥L) : GLV V) * d⁻¹, hcdL'⟩ := by
      apply Subtype.ext
      show (ℓ : GLV V) * d * (ℓ : GLV V)⁻¹ * d = (ℓ : GLV V) * (d * (ℓ : GLV V)⁻¹ * d⁻¹)
      rw [hdinv]
      group
    have hcomm : π * (σ * π * σ⁻¹) = (σ * π * σ⁻¹) * π := by
      have hσ2 : (σ * π * σ⁻¹) * (σ * π * σ⁻¹) = 1 := by
        calc (σ * π * σ⁻¹) * (σ * π * σ⁻¹) = σ * (π * π) * σ⁻¹ := by group
          _ = 1 := by rw [hπ2, mul_one, mul_inv_cancel]
      have h1 := eq_inv_of_mul_eq_one_left hsq
      rw [_root_.mul_inv_rev, hπinv, inv_eq_of_mul_eq_one_right hσ2] at h1
      exact h1
    have hc : d * ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) = ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) * d := by
      have h1 : ((α ⟨_, hdeL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          π * (σ * π * σ⁻¹) := by
        rw [hx1, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hπψ ℓ, hℓ, hπinv]
        group
      have h2 : ((α ⟨_, hedL⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          (σ * π * σ⁻¹) * π := by
        rw [hx2, map_mul, Subgroup.coe_mul, hπψ ℓ⁻¹, map_inv, Subgroup.coe_inv, hℓ, hπinv]
        group
      have h := hαi (Subtype.ext (h1.trans (hcomm.trans h2.symm)))
      exact congrArg Subtype.val h
    obtain ⟨w, hw⟩ := hβs (heartEquiv.symm y)
    have hwy : heartEquiv (β w) = y := by rw [hw, AddEquiv.apply_symm_apply]
    set e := (ℓ : GLV V) * d * (ℓ : GLV V)⁻¹ with he
    set w₁ : ↥(commSpace L ⊤) := ⟨((ℓ⁻¹ : ↥L) : GLV V) w, smul_mem_commSpace (ℓ⁻¹).2 w.2⟩
    set w₂ : ↥(commSpace L ⊤) := ⟨d w₁, d_mem_commSpace hd w₁.2⟩
    set w₃ : ↥(commSpace L ⊤) := ⟨(ℓ : GLV V) w₂, smul_mem_commSpace ℓ.2 w₂.2⟩
    have hw₃ : (w₃ : V) = e w := by
      show (ℓ : GLV V) (d (((ℓ⁻¹ : ↥L) : GLV V) w)) = ((ℓ : GLV V) * d * (ℓ : GLV V)⁻¹) w
      rw [Subgroup.coe_inv]
      rfl
    have hβw₃ : heartEquiv (β w₃) = heartAct 6 (σ * π * σ⁻¹) y := by
      rw [hℓH, hπφ, hℓH, hwy, map_inv, Subgroup.coe_inv, hℓ, heartAct_mul, heartAct_mul]
    set v₂ : ↥(commSpace L ⊤) := w₃ - w
    have hβv₂ : heartEquiv (β v₂) = heartAct 6 (σ * π * σ⁻¹) y - y := by
      rw [map_sub, map_sub, hβw₃, hwy]
    set v₃ : ↥(commSpace L ⊤) := ⟨d v₂, d_mem_commSpace hd v₂.2⟩
    have hβv : heartEquiv (β (v₃ - v₂)) = heartAct 6 π (heartAct 6 (σ * π * σ⁻¹) y - y) -
        (heartAct 6 (σ * π * σ⁻¹) y - y) := by
      rw [map_sub, map_sub, hπφ, hβv₂]
    have hnz : d (e w - w) - (e w - w) ≠ 0 := by
      intro h0
      apply hy
      rw [← hβv]
      have : v₃ - v₂ = 0 := by
        apply Subtype.ext
        show d ((w₃ : V) - w) - ((w₃ : V) - w) = 0
        rw [hw₃]
        exact h0
      rw [this, map_zero, map_zero]
    exact ⟨ℓ, ℓ.2, ti_of_comm hd ℓ.2 hdd hc w.2 hnz⟩

end AltSix

end CFSG.CGT.Foote82.BASTI

namespace CFSG.CGT.Foote82

theorem basTIFails_holds :
    BASTIFails := by
  intro V _ _ _ L htype hf _ d hd hd2 hodd hrank
  rcases htype with hA | hO
  · exact BASTI.basTIFails_altSix hA hf hd hd2 hodd hrank
  · exact BASTI.basTIFails_omegaSix hO hf hd hd2 hrank

end CFSG.CGT.Foote82

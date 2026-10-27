module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs
import CFSG.Adapters.TauCetiLieModels
import CFSG.GroupTheory.PLayer.Transport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BAct
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF6
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CLayer
import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
import CFSG.LocalAnalysis.GLTheoremA.PComp
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma103
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherUnitary
import CFSG.LocalAnalysis.StandardType.GGReverseMarking
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClHerm
import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Cfg
public import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsBeta
import CFSG.LieType.Multipliers.U62Sylow
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD42Spec
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
import CFSG.LocalAnalysis.GLTheoremA.S12.Compl123
import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVDefs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.StandardType (markTag markRank markChar markDeg)

private theorem p_exponent_of_card_eight {q : TauCeti.PrimePower} (h : q.card = 8) :
    q.p = 2 ∧ q.exponent = 3 := by
  have hp : q.p = 2 := by
    rw [TauCeti.PrimePower.card_def] at h
    have h1 : q.p ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
      exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.mp q.exponent_pos)
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)
  rw [TauCeti.PrimePower.card_def, hp] at h
  exact ⟨hp, Nat.pow_right_injective le_rfl (h.trans (by norm_num) : 2 ^ q.exponent = 2 ^ 3)⟩

section Main


theorem SG.exists_not_innDiagOn_of_u38 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω}
    {x : Ω} {D K : Subgroup Ω} (h : QSNL 3 S B T x D K)
    (hU : catalogIs (PSimple 3 K) S9.isU3eight) (hB : Nat.card B = 3 ^ 5) :
    ∃ β ∈ B, β ∉ D ∧ ¬ InnDiagOn 3 (Subgroup.zpowers β) K := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hDB, -, hDcard, -, -, -, -⟩ := h.cfg.std
  haveI : Nontrivial (PSimple 3 K) := (isSimple_of_isU3eight hU).toNontrivial
  have hNA := h.nlAct (T123C.dvd_card_of_nontrivial_pSimple Nat.prime_three inferInstance)
  have hBN := hNA.norm
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 K) :=
    isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hNA.comp
  obtain ⟨q, hv, hq8, ⟨e⟩⟩ := CatB.lieIndex_isU3eight hU
  obtain ⟨hp2, hq3⟩ := p_exponent_of_card_eight hq8
  have hLM : CFSG.Blueprint.LieModel (PSimple 3 K) CFSG.Open.StatedLieTag.PSU 3 2 3 := by
    have h1 := CFSG.Models.lieModel_twistedA 2 q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic
        ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 2 :=
      (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hp2
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent
        ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 3 :=
      (TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q).trans hq3
    rw [hc, hf] at h1
    exact CFSG.Models.LieModel.toBlueprint (by decide) h1
  have hall : ∀ b ∈ {b : Ω | b ∈ B ∧ b ∉ D}, CFSG.Assembly.LargeEvenMarking (PQuot 3 K)
      fun _ _ _ I _ θ => ∃ φ ∈ I, CFSG.Assembly.LargeEvenInduces θ (indRel 3 K b) φ :=
    fun b hb => CFSG.StandardType.Canonical.largeEvenMarking_mono
      (fun _ _ _ _ _ _ hh => hh b (Subgroup.mem_zpowers b)) (hcon b hb.1 hb.2).2
  obtain ⟨-, lab, -, hraw⟩ := MI.marking_transport_family (indRel 3 K)
    {b : Ω | b ∈ B ∧ b ∉ D} (Set.toFinite _) hall
    (CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hLM)
  obtain ⟨_, _, _, _, -, -, _, ⟨htag, hrank, hchar, hdeg⟩, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨hlab, hdeg'⟩ := CFSG.StandardType.ClNonsplit.unitaryLabel_of_markTag_PSU htag hchar
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .twA := by
    rcases hlab with h' | ⟨h', h3'⟩
    · exact h'
    · exfalso
      dsimp only at h' h3'
      subst h' h3'
      simp [markRank] at hrank
  obtain rfl : r = 2 := by
    simp only [markRank] at hrank
    omega
  obtain rfl : n = 3 := hdeg'.symm.trans hdeg
  obtain ⟨F, _, _, hF, -, -, θ, -, hθ⟩ := hraw
  have hFd : UnitaryFieldData 2 3 F := ⟨Nat.prime_two, by norm_num, by rw [hF]; norm_num⟩
  let Pr := CFSG.StandardType.InndiagSU.projEquiv hFd (d := 3) (by norm_num)
  haveI := Finite.of_equiv _ θ.toEquiv
  haveI := Finite.of_equiv _ Pr.toEquiv
  let ψ : ↥B →* MulAut (primeFormP hFd ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
    (MulAut.congr Pr).toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp
      ((chevAut 3 K).comp (Subgroup.inclusion hBN)))
  have hψ : ∀ b : ↥B, ψ b = MulAut.congr Pr (MulAut.congr θ (chevAut 3 K ⟨b, hBN b.2⟩)) :=
    fun _ => rfl
  have hψ1 : ∀ b : ↥B, ψ b = 1 ↔ (b : Ω) ∈ D := fun b => by
    rw [hψ, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
    exact hNA.ker b b.2 (hBN b.2)
  have hXD : ψ.range ≤ primeFormD hFd ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rintro _ ⟨b, rfl⟩
    by_cases hbD : (b : Ω) ∈ D
    · rw [(hψ1 b).2 hbD]
      exact Subgroup.one_mem _
    obtain ⟨φ, hφI, hφ⟩ := hθ b ⟨b.2, hbD⟩
    rw [MI.induces_indRel_iff (hBN b.2) θ] at hφ
    have hmem :=
      CFSG.StandardType.InndiagSU.congr_mem_primeFormD hFd (d := 3) (by norm_num) hF hφI
    have hinv : MI.indAut 3 K b (hBN b.2) = (chevAut 3 K ⟨b, hBN b.2⟩)⁻¹ := by
      rw [MI.indAut, ← map_inv]
      rfl
    rw [hφ, hinv, map_inv, map_inv] at hmem
    rw [hψ]
    exact inv_mem_iff.1 hmem
  have hcomm : ∀ a c : ↥B, a * c = c * a := fun a c => h.cfg.elem.1.is_comm.comm a c
  have hX : IsElemAbelian 3 ψ.range := by
    refine ⟨⟨⟨fun a c => ?_⟩⟩, ?_⟩
    · obtain ⟨_, b, rfl⟩ := a
      obtain ⟨_, c, rfl⟩ := c
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm])
    · rintro _ ⟨b, rfl⟩
      have hb : b ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h.cfg.elem.2 _ b.2)
      rw [← map_pow, hb, map_one]
  have hnl : ∀ α ∈ ψ.range, α ≠ 1 → GLAPLayer 3 (fixSubgroup α) = ⊥ := by
    rintro _ ⟨b, rfl⟩ hb1
    have hbD : (b : Ω) ∉ D := fun hbD => hb1 ((hψ1 b).2 hbD)
    rw [hψ, CFSG.glaPLayer_fixSubgroup_congr Nat.prime_three Pr,
      CFSG.glaPLayer_fixSubgroup_congr Nat.prime_three θ, hNA.layer b b.2 hbD (hBN b.2),
      Subgroup.map_bot, Subgroup.map_bot]
  have hker : ψ.ker = D.subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, hψ1, Subgroup.mem_subgroupOf]
  have hkc : Nat.card ψ.ker = 3 ^ 2 := by
    rw [hker, ← hDcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range ψ
  rw [hkc, hB] at hmul
  have hle := SF.card_le_of_nl_primeFormD hFd le_rfl Nat.prime_three (by norm_num) (by norm_num)
    hXD hX hnl
  norm_num at hle hmul
  omega

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265

end

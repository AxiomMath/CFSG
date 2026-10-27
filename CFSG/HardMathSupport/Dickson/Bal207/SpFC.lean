module

public import CFSG.HardMathSupport.Dickson.Bal207.FamSp
public import CFSG.HardMathSupport.Dickson.Bal207.SpFCCases
public import CFSG.Open.GriessAllModelsStatement
import CFSG.Adapters.TauCetiLieModels
import CFSG.GH74.Generic.S3.L3FRankDvd
import CFSG.HardMathSupport.Dickson.Bal207.Center
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Models
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatAlt
import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal207Aux CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier
  CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier in
theorem famSp_coprime_center (hGA : GriessAllModelsStatement) {K : Type} [Group K] [Finite K]
    (hq : CFSG.Open.IsQuasisimple K) (hK : IsLieQuot K (FamSp 3)) :
    Nat.Coprime 3 (Nat.card (Subgroup.center K)) := by
  obtain ⟨⟨dd, hv⟩, ⟨hd, hs⟩, ⟨e⟩⟩ := hK
  cases dd with
  | B r q =>
    obtain ⟨-, h⟩ := hd
    have hp2 : q.p = 2 := by rcases h with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl _) with hL | hL
    · rw [hp2] at hL
      have hg : ¬ 3 ∣ (genericOrders .PSp r 2 q.exponent).1 := by
        simp only [genericOrders]
        exact centerAux_not_three_dvd_gcd (Or.inl rfl)
      exact centerAux_coprime_of_card_le_one Nat.prime_three
        ((center_torsion_le hGA hq e hL Nat.prime_three).trans
          (centerAux_torsBound_eq_one (Or.inl rfl) hg).le)
    · rw [hp2] at hL
      exact absurd hL.1.2.2.2 (by simp)
  | _ => exact hs.elim

theorem isLieQuot_of_isPspQuot {Y : Type} [Group Y] {J : Subgroup Y} (h : IsPspQuot J) :
    IsLieQuot ↥J (fun d => Bal207Index 3 d ∧ ¬ IsG2EightIndex d) := by
  obtain ⟨s, k, E, _, _, hE, hk, hs, hne, ⟨eJ⟩⟩ := h
  have hk0 : 0 < k := by omega
  let q : TauCeti.PrimePower := ⟨2, k, Nat.prime_two, hk0⟩
  have hv : (TauCeti.LieTypeIndex.B s q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨hs, fun h => hne ⟨h.1, ?_⟩⟩, fun h => ?_⟩
    · have h2 : q.card = 2 := h.2
      rw [TauCeti.PrimePower.card_def] at h2
      have h2' : 2 ^ k = 2 ^ 1 := h2
      exact Nat.pow_right_injective le_rfl h2'
    · have h3 : q.card = 3 := h.2
      rw [TauCeti.PrimePower.card_def] at h3
      have h3' : 2 ^ k = 3 := h3
      rcases hk with rfl | rfl <;> norm_num at h3'
  let d : TauCeti.ValidLieTypeIndex := ⟨.B s q, hv⟩
  obtain ⟨eT⟩ : Nonempty (d.Group ≃* StatedProj (StatedSp s ↥d.fixedField)) := by
    rcases (show s = 2 ∨ 3 ≤ s by omega) with rfl | hs3
    · exact ⟨CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv⟩
    · exact ⟨CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj s q hv rfl
        hs3⟩
  haveI : Finite d.fixedField := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype d.fixedField := Fintype.ofFinite _
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card d.fixedField := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      TauCeti.ValidLieTypeIndex.card_fixedField, hE]
    simp only [d, q, TauCeti.ValidLieTypeIndex.fieldOrder, TauCeti.LieTypeIndex.fieldOrder_B,
      TauCeti.PrimePower.card_def]
  let φ : E ≃+* d.fixedField := FiniteField.ringEquivOfCardEq hcard
  let e₁ := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ s)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  refine ⟨d, ⟨⟨rfl, ?_⟩, fun h => h⟩, ⟨eJ.trans (e₁.trans eT.symm)⟩⟩
  rcases hk with rfl | rfl
  · exact Or.inl ⟨⟨rfl, rfl⟩, by omega⟩
  · exact Or.inr ⟨⟨rfl, rfl⟩, hs⟩

theorem two_pow_dvd_card_of_isSpFirstClaimIdx (d : TauCeti.ValidLieTypeIndex)
    (hd : IsSpFirstClaimIdx d.1) : 2 ^ 15 ∣ Nat.card (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    obtain ⟨hq, -, hr5, -⟩ := hd
    have hp : q.p = 2 := by rcases hq with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
      rw [← hp]
      exact TauCeti.LieTypeIndex.characteristic_twistedA r q
    rw [hc] at hL
    have hB := CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
      (by simp [CFSG.Blueprint.classicalTags]) hL
    have hcard := CFSG.SeitzReduction.UnitaryPilot.card_of_lieModel_PSU_two_pow hB
    rw [Nat.add_sub_cancel] at hcard
    have hf0 := TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA r q, hv⟩
    refine dvd_trans ?_ (dvd_trans
      (CFSG.GH74.Generic.S3.L3Ord.pow_dvd_ordTwistedA (by omega)) (dvd_of_eq hcard.symm))
    rw [← pow_mul]
    refine pow_dvd_pow 2 ?_
    have h30 : 30 ≤ r * (r + 1) := Nat.mul_le_mul hr5 (by omega : 6 ≤ r + 1)
    have h15 : 15 ≤ r * (r + 1) / 2 := by
      generalize r * (r + 1) = t at h30 ⊢
      omega
    exact h15.trans (Nat.le_mul_of_pos_left _ hf0)
  | _ => exact hd.elim

theorem bal207SpFirstClaim_of_griess (hGA : GriessAllModelsStatement)
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : Bal207SpFirstClaim G := by
  intro Y _ _ _ K B A ctx hK hIH a haA ha1 J hJ hcomp hBJ hJFC
  obtain ⟨F, _, _, f, r, hF, hf, hr, hne, ⟨e⟩⟩ := exists_psp_of_famSp hK
  have hKq : CFSG.Open.IsQuasisimple ↥K := ctx.comp.2.2
  have hZ := famSp_coprime_center hGA hKq hK
  have haB : a ∈ B := ctx.le haA
  have hBK : B ≤ Subgroup.normalizer (K : Set Y) := ctx.norm
  have hβ3 : uniAut e ⟨a, hBK haB⟩ ^ 3 = 1 := by
    have h3 : (⟨a, hBK haB⟩ : ↥(Subgroup.normalizer (K : Set Y))) ^ 3 = 1 :=
      Subtype.ext (ctx.scp.2.1.2 a haB)
    rw [← map_pow, h3, map_one]
  have hβ1 : uniAut e ⟨a, hBK haB⟩ ≠ 1 := fun h1 =>
    not_mem_centralizer_of_inf_eq_bot ctx.disj haA ha1
      (mem_centralizer_of_uniAut_eq_one e hKq.1 (hBK haB) h1)
  have hlay := (compShape_psp hF hf hr hne _ hβ3 hβ1).layer
  obtain ⟨-, hJc, -⟩ := uni_component e Nat.prime_three hKq hZ (hBK haB) hlay hJ
  have hJK : J ≤ K := hJ.1.trans inf_le_left
  rcases spComp_cases ctx.scp hBK hF hf hr hne e haB hβ1 hJK hcomp.2.2 hJc with h1 | h2 | h3
  · exact Glue.stronglyLocallyOneBalanced_of_ih ctx hIH haA ha1 hJ hcomp.2.2 hBJ
      (Glue.bal207PlusHyp_of_isLieQuot
        (Glue.isLieQuot_subgroupOf (hJ.1.trans inf_le_right) (isLieQuot_of_isPspQuot h1)))
  · exfalso
    obtain ⟨d, hd, ⟨eJ⟩⟩ := hJFC
    have h15 := two_pow_dvd_card_of_isSpFirstClaimIdx d hd
    rw [← Nat.card_congr eJ.toEquiv] at h15
    have h16 := h15.trans h2
    norm_num at h16
  · exact isStronglyLocallyOneBalanced_of_blockFrame ctx.scp hBK hZ e hcomp.2.2 hJK hBJ h3

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end

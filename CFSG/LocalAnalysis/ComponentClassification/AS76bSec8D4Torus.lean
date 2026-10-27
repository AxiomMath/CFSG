module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Cell
public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.LieType.Chevalley.TrialityAllCharTorusCoordinates
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.GraphFixedRankOneImage
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
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
public import Certificates.Certificate117

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoExceptional.D4

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard (rankTwoQuot)
open scoped commutatorElement Matrix

section CharTwoWeyl

variable {K : Type} [Field K] [CharP K 2]

theorem weylElt_mul_canonicalRep_d4
    (i : Fin TwistTag.D4.tag.rank)
    (w : WeylGroup TwistTag.D4.tag) :
    weylElt TwistTag.D4.tag K i 1 * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K
        ((coxeterSystem TwistTag.D4.tag).simple i * w) := by
  rw [weylElt_mul_canonicalRep]
  split_ifs
  · rfl
  · rw [show (-1 : Kˣ) = 1 from Units.ext (CharTwo.neg_eq (1 : K)), torusElt_one, one_mul]

theorem canonicalRep_wordProd_mul_d4
    (ω : List (Fin TwistTag.D4.tag.rank)) (v : WeylGroup TwistTag.D4.tag) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K ((coxeterSystem TwistTag.D4.tag).wordProd ω *
        v) =
      (ω.map fun i => weylElt TwistTag.D4.tag K i 1).prod *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K v := by
  induction ω with
  | nil => rw [CoxeterSystem.wordProd_nil, one_mul, List.map_nil, List.prod_nil, one_mul]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_assoc, ← weylElt_mul_canonicalRep_d4, ih,
      List.map_cons, List.prod_cons, mul_assoc]

theorem canonicalRep_mul_d4
    (w v : WeylGroup TwistTag.D4.tag) :
    canonicalRep (coxeterSystem TwistTag.D4.tag) K (w * v) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K v := by
  obtain ⟨ω, -, rfl⟩ := (coxeterSystem TwistTag.D4.tag).exists_isReduced w
  have h := canonicalRep_wordProd_mul_d4 (K := K) ω 1
  rw [mul_one, canonicalRep_one, mul_one] at h
  rw [canonicalRep_wordProd_mul_d4, h]

end CharTwoWeyl

section TorusCent

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem exists_bruhat_of_commute_torus_d4
    {s g : ModGL TwistTag.D4.tag K}
    (hs : s ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) (hg : g ∈ d4C K σ)
    (hsg : s * g = g * s) :
    ∃ w ∈ relWeylTwist TwistTag.D4, ∃ h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom,
      ∃ u₀ ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
        ∃ u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom,
          g = h * u₀ * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u ∧
            s * u₀ = u₀ * s ∧ s * u = u * s ∧
              s * canonicalRep (coxeterSystem TwistTag.D4.tag) K w =
                canonicalRep (coxeterSystem TwistTag.D4.tag) K w * s := by
  obtain ⟨hB1, -, huniq, -, -, hUN, -, hHc, -, hcov, -, hcell, -, -⟩ :=
    fixed_root_Bruhat_decomposition TwistTag.D4 K σ
  have hg' : g ∈ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K)) := hg
  rw [hcov, Set.mem_iUnion] at hg'
  obtain ⟨⟨w, hw⟩, hgw⟩ := hg'
  obtain ⟨hbij, -⟩ := hcell w hw
  obtain ⟨⟨b, u⟩, ⟨hb, hu⟩, hbu⟩ := hbij.2.2 hgw
  change b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u = g at hbu
  set n := canonicalRep (coxeterSystem TwistTag.D4.tag) K w with hn
  have hsT : s ∈ torusGroup TwistTag.D4.tag K := (mem_inf.1 (mem_inf.1 hs).1).1
  have hsΓ : s ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom := (mem_inf.1 (mem_inf.1 hs).1).2
  have hsC : s ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom := (mem_inf.1 hs).2
  have hnC : n ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    canonicalRep_mem_graphFixedRootGroup (σ := σ.toRingHom) hw
  have hnΓ : n ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hnC
  have hnN := canonicalRep_mem_normalizer (R := K) (τ := TwistTag.D4.tag) w
  set t := n * s⁻¹ * n⁻¹ with ht
  have htT : t ∈ torusGroup TwistTag.D4.tag K := (mem_normalizer_iff.1 hnN s⁻¹).1 (inv_mem hsT)
  have htH : t ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    mem_inf.2 ⟨mem_inf.2 ⟨htT, mul_mem (mul_mem hnΓ (inv_mem hsΓ)) (inv_mem hnΓ)⟩,
      mul_mem (mul_mem hnC (inv_mem hsC)) (inv_mem hnC)⟩
  have hHB := graphFixedRootTorus_le_graphFixedRootBorel (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom)
  have hbB : s * b * t ∈ graphFixedRootBorel TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem (hHB hs) hb) (hHB htH)
  have huU : s * u * s⁻¹ ∈ graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom w :=
    mem_inf.2 ⟨(mem_normalizer_iff.1 (torusGroup_le_normalizer_rootSpan (fun _ hα => hα.1) hsT)
      u).1 (mem_inf.1 hu).1, mul_mem (mul_mem hsΓ (mem_inf.1 hu).2) (inv_mem hsΓ)⟩
  have heq : s * b * t * n * (s * u * s⁻¹) = b * n * u := by
    have h1 : s * (b * n * u) * s⁻¹ = b * n * u := by
      rw [hbu, hsg, mul_inv_cancel_right]
    calc s * b * t * n * (s * u * s⁻¹) = s * (b * n * u) * s⁻¹ := by rw [ht]; group
      _ = b * n * u := h1
  have hpair := hbij.2.1 (Set.mk_mem_prod hbB huU) (Set.mk_mem_prod hb hu) heq
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨hb', hu'⟩ := hpair
  have hbmem : b ∈ (graphFixedRootBorel TwistTag.D4 K σ.toRingHom :
      Set (ModGL TwistTag.D4.tag K)) := hb
  rw [hB1] at hbmem
  obtain ⟨h, hh, u₀, hu₀, rfl⟩ := Set.mem_mul.1 hbmem
  have hu₀' : t⁻¹ * u₀ * t ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    have hUB := graphFixedPosUnipotent_le_graphFixedRootBorel (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom)
    have h1 := hUN.conj_mem ⟨u₀, hUB hu₀⟩ (mem_subgroupOf.2 hu₀) ⟨t⁻¹, inv_mem (hHB htH)⟩
    have h2 := mem_subgroupOf.1 h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h2
    exact h2
  have hshtH : s * h * t ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom :=
    mul_mem (mul_mem hs hh) htH
  have hfac : s * h * t * (t⁻¹ * u₀ * t) = h * u₀ := by
    calc s * h * t * (t⁻¹ * u₀ * t) = s * (h * u₀) * t := by group
      _ = h * u₀ := hb'
  obtain ⟨hht, hut⟩ := huniq _ hshtH _ hh _ hu₀' _ hu₀ hfac
  have hst : t = s⁻¹ := by
    have h1 : h * (s * t) = h * 1 := by
      rw [mul_one, ← mul_assoc, hHc h hh s hs, hht]
    rw [eq_inv_iff_mul_eq_one]
    have := mul_left_cancel h1
    calc t * s = s * t := (hHc t htH s hs)
      _ = 1 := this
  refine ⟨w, hw, h, hh, u₀, hu₀, u, graphFixedInversionUnipotent_le_graphFixedPosUnipotent
    (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) w hu, by rw [← hbu], ?_, ?_, ?_⟩
  · rw [hst, inv_inv] at hut
    calc s * u₀ = s * u₀ * s⁻¹ * s := by group
      _ = u₀ * s := by rw [hut]
  · calc s * u = s * u * s⁻¹ * s := by group
      _ = u * s := by rw [hu']
  · have h1 : n * s⁻¹ * n⁻¹ = s⁻¹ := hst
    have h2 : n * s * n⁻¹ = s := by
      have := congrArg (·⁻¹) h1
      simpa [mul_assoc] using this
    calc s * n = n * s * n⁻¹ * n := by rw [h2]
      _ = n * s := by group

theorem eq_zero_of_mul_eq_self_d4 {F : Type} [Field F] {x a : F} (hx : x ≠ 1) (h : x * a = a) :
    a = 0 := by
  have h1 : (x - 1) * a = 0 := by rw [sub_mul, h, one_mul, sub_self]
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (sub_eq_zero.1 h2) hx
  · exact h2

end TorusCent

section Torus

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem trialityTorusHom_apply_d4
    (a : Kˣ) (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ (a, b) = trialityOuterTorus K σ a * trialityMiddleTorus K σ b :=
  rfl

theorem hm_one_d4 :
    trialityMiddleTorus K σ 1 = 1 := by
  rw [trialityMiddleTorus, map_one, torusElt_one]

theorem ho_eq_d4 (a : Kˣ) :
    trialityOuterTorus K σ a = trialityTorusHom σ (a, 1) := by
  rw [trialityTorusHom_apply_d4, hm_one_d4, mul_one]

theorem ho_one_d4 :
    trialityOuterTorus K σ 1 = 1 := by
  rw [ho_eq_d4, show ((1 : Kˣ), (1 : (trialityFixedField K σ.toRingHom)ˣ)) = 1 from rfl, map_one]

theorem hm_eq_d4
    (b : (trialityFixedField K σ.toRingHom)ˣ) :
    trialityMiddleTorus K σ b = trialityTorusHom σ (1, b) := by
  rw [trialityTorusHom_apply_d4, ho_one_d4, one_mul]

end Torus

section Bridges

variable {K : Type} [Field K] (σ : K ≃+* K)

theorem coe_orbitY_zero_d4
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩) :
    (orbitY TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      d4y₁ K σ (c : K) := by
  rw [coe_orbitY, d4y₁, coe_trialityOrbitProd]
  have hc : (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 := by decide
  have hm : TwistTag.D4.orbitMin ⟨0, by decide⟩ = ⟨0, by decide⟩ := by decide
  have e0 : -trialityRoot 0 = -Pi.single ⟨0, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  have e1 : permLattice TwistTag.D4.perm (-trialityRoot 0) = -Pi.single ⟨1, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  have e2 : permLattice (TwistTag.D4.perm ^ 2) (-trialityRoot 0) =
      -Pi.single ⟨3, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  rw [hc, e1, e2, e0, pinnedX_neg_single, pinnedX_neg_single, pinnedX_neg_single]
  simp only [List.range_succ, List.range_zero, List.nil_append, hm, mul_assoc]
  rfl

theorem coe_orbitX_one_d4
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitX TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      d4x₂ K (c : K) := by
  rw [coe_orbitX, d4x₂]
  have hc : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have hm : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have e : trialityRoot 1 = Pi.single ⟨2, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  rw [hc, e, pinnedX_single]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_zero, hm]
  rfl

theorem coe_orbitY_one_d4
    (c : orbitField TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩) :
    (orbitY TwistTag.D4 K σ.toRingHom ⟨1, by decide⟩ c : ModGL TwistTag.D4.tag K) =
      d4y₂ K (c : K) := by
  rw [coe_orbitY, d4y₂]
  have hc : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have hm : TwistTag.D4.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ := by decide
  have e : -trialityRoot 1 = -Pi.single ⟨2, by decide⟩ 1 := by
    funext i; fin_cases i <;> rfl
  rw [hc, e, pinnedX_neg_single]
  simp only [List.range_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one, pow_zero, hm]
  rfl

theorem trialityTorusHom_mem_d4H
    (hσ : σ ^ 3 = 1)
    (p : Kˣ × (trialityFixedField K σ.toRingHom)ˣ) :
    trialityTorusHom σ p ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  rw [show trialityTorusHom σ p = (e (p.1, p.2) : ModGL TwistTag.D4.tag K) from (he p.1 p.2).symm]
  exact (e _).2

theorem exists_trialityTorusHom_eq_d4
    (hσ : σ ^ 3 = 1) {h : ModGL TwistTag.D4.tag K}
    (hh : h ∈ graphFixedRootTorus TwistTag.D4 K σ.toRingHom) :
    ∃ p, trialityTorusHom σ p = h := by
  obtain ⟨-, ⟨e, he⟩, -⟩ := triality_all_characteristic_faithful_torus_coordinates K σ hσ
  obtain ⟨p, hp⟩ := e.surjective ⟨h, hh⟩
  refine ⟨p, ?_⟩
  rw [show trialityTorusHom σ p = (e (p.1, p.2) : ModGL TwistTag.D4.tag K) from (he p.1 p.2).symm]
  exact congrArg Subtype.val hp

theorem canonicalRep_orbitReflection_inv_d4
    [CharP K 2] (a : Fin TwistTag.D4.foldedTag.rank) :
    (canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a))⁻¹ =
      canonicalRep (coxeterSystem TwistTag.D4.tag) K (TwistTag.D4.orbitReflection a) := by
  rw [inv_eq_iff_mul_eq_one, ← canonicalRep_mul_d4, TwistTag.orbitReflection_mul_self,
    canonicalRep_one]

end Bridges

section SL2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Field F] [CharP F 2] in
theorem exists_finset_card_four_d4 (h4 : 4 ≤ Nat.card F) : ∃ s : Finset F, s.card = 4 := by
  have := Fintype.ofFinite F
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  exact ⟨t, ht⟩

omit [CharP F 2] in
theorem sl2_commutator_d4 (h4 : 4 ≤ Nat.card F) : commutator (SL2 F) = ⊤ :=
  (CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four_d4 h4))).commutator_eq_top

theorem sl2_isSimpleGroup_d4 (h4 : 4 ≤ Nat.card F) : IsSimpleGroup (SL2 F) := by
  obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 2) le_rfl
    (Or.inr (exists_finset_card_four_d4 h4))
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm.isSimpleGroup

theorem sl2_facts_d4 {L : Type} [Group L] (e : L ≃* SL2 F) (h4 : 4 ≤ Nat.card F) :
    commutator L = ⊤ ∧ IsSimpleGroup L ∧ center L = ⊥ ∧ CFSG.Open.IsQuasisimple L ∧
      Nonempty (L ⧸ center L ≃* StatedProj (StatedSL 2 F)) := by
  have := sl2_isSimpleGroup_d4 h4
  have hs : IsSimpleGroup L := e.isSimpleGroup
  have hcomm : commutator L = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ commutator (SL2 F) := by rw [sl2_commutator_d4 h4]; exact mem_top _
    have h1 : (commutator (SL2 F)).map e.symm.toMonoidHom = commutator L := by
      rw [commutator_def, commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.2 e.symm.surjective]
    rw [← h1]
    exact ⟨e x, hx, by simp⟩
  have hc : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ center (SL2 F) := mem_center_iff.2 fun y => by
      rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, mem_center_iff.1 hz]
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, mem_bot] at hz'
    rw [mem_bot, ← e.symm_apply_apply z, hz', map_one]
  have e₁ : L ⧸ center L ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  refine ⟨hcomm, hs, hc, ⟨hcomm, e₁.isSimpleGroup⟩, ⟨e₁.trans ((e.trans
    (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := F)).symm).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F))⟩⟩

end SL2


end CFSG.ComponentClassification.RankTwoExceptional.D4

module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLTypeFactsSmall
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.RankThree.Literature.FSmithOrthogonal
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin

section Abstract

theorem mcltf_commutator_subgroupOf_self {G : Type*} [Group G] (H : Subgroup G) :
    ⁅H, H⁆.subgroupOf H = commutator H := by
  rw [← Subgroup.map_subtype_commutator]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mcltf_finite_linearEquiv [Finite V] : Finite (V ≃ₗ[ZMod 2] V) :=
  Finite.of_injective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem mcltf_facts_orthogonalGroup [Finite V] (Q : QuadraticForm (ZMod 2) V)
    (hs : IsSimpleGroup ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hna : ∃ a b : ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, a * b ≠ b * a)
    (hidx : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆.relIndex
        (TauCeti.QuadraticMap.orthogonalGroup Q) = 2) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  have : Finite (V ≃ₗ[ZMod 2] V) := mcltf_finite_linearEquiv
  have hle : ⁅O, O⁆ ≤ O := Subgroup.commutator_le_self O
  let e : ↥(⁅O, O⁆.subgroupOf O) ≃* ↥⁅O, O⁆ := Subgroup.subgroupOfEquivOfLe hle
  refine mcltf_facts_of_derived_index_two (⁅O, O⁆.subgroupOf O) 1 ?_ e.isSimpleGroup ?_ hidx
  · rw [derivedSeries_one, mcltf_commutator_subgroupOf_self]
  · obtain ⟨a, b, hab⟩ := hna
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem mcltf_scalars_subgroupOf_eq_bot [Nontrivial V] (H : Subgroup (V ≃ₗ[ZMod 2] V)) :
    (scalars (ZMod 2) V).subgroupOf H = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨c, hc⟩ := mem_scalars.mp (Subgroup.mem_subgroupOf.mp hg)
  rw [Subgroup.mem_bot]
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h01 c with rfl | rfl
  · obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h1 := hc ((g : V ≃ₗ[ZMod 2] V).symm v)
    rw [LinearEquiv.apply_symm_apply, zero_smul] at h1
    exact absurd h1 hv
  · exact Subtype.ext (LinearEquiv.ext fun v => by rw [hc v, one_smul]; rfl)

theorem mcltf_facts_orthogonalGroup_of_elementary [FiniteDimensional (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V) (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hs : IsSimpleGroup (ProjElementary Q)) (hperf : commutator (elementaryGroup Q) = ⊤) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup Q) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have hsE : IsSimpleGroup ↥(elementaryGroup Q) :=
    ((QuotientGroup.quotientMulEquivOfEq (mcltf_scalars_subgroupOf_eq_bot _)).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  refine mcltf_facts_orthogonalGroup Q (by rw [hE]; exact hsE) ?_ ?_
  · rw [hE]
    exact mcltf_exists_ne_of_perfect hperf
  · rw [CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6]
    exact CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup Q hQ

end Abstract

section Models

theorem mcltf_irr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by
  decide

theorem mcltf_facts_orthogonalGroup_quadPlus {n : ℕ} (hn : 3 ≤ n) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus n (ZMod 2))) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadPlus (K := ZMod 2) hn
  refine mcltf_facts_orthogonalGroup_of_elementary _ hQ ?_ (commutator_orthogonalGroup_quadPlus hn)
    (isSimpleGroup_projElementary_quadPlus hn)
    (commutator_elementaryGroup_eq_top' hQ hT.ge hTQ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  omega

theorem mcltf_facts_orthogonalGroup_quadMinus_large {m : ℕ} (hm : 4 ≤ m) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus m (ZMod 2) 1 1)) := by
  obtain ⟨hQ, T, hT, hTQ⟩ := regular_quadMinus (K := ZMod 2) hm mcltf_irr
  refine mcltf_facts_orthogonalGroup_of_elementary _ hQ ?_
    (commutator_orthogonalGroup_quadMinus hm mcltf_irr)
    (isSimpleGroup_projElementary_quadMinus hm mcltf_irr)
    (commutator_elementaryGroup_eq_top' hQ hT.ge hTQ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem mcltf_finrank_quadMinus {m : ℕ} (hm : 1 ≤ m) :
    finrank (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) = 2 * m := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_fin]
  omega

theorem mcltf_facts_orthogonalGroup_quadMinus_small {m : ℕ} (hm : m = 2 ∨ m = 3) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus m (ZMod 2) 1 1)) := by
  have hm1 : 1 ≤ m := by omega
  have hQ := nondegenerate_polarBilin_quadMinus_of_finite m (ZMod 2) mcltf_irr
  have hdim := mcltf_finrank_quadMinus hm1
  have hts : ∀ U : Submodule (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2),
      finrank (ZMod 2) U = finrank (ZMod 2) (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → ZMod 2) / 2 →
        ∃ u ∈ U, quadMinus m (ZMod 2) 1 1 u ≠ 0 := by
    intro U hU
    by_contra h
    push Not at h
    exact CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus hm1 mcltf_irr
      ⟨U, by rw [hU, hdim]; omega, h⟩
  obtain ⟨hs, -, hna, hidx, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus m (ZMod 2) 1 1) hQ (by rw [hdim]; omega) hts
  refine mcltf_facts_orthogonalGroup _ hs ?_ hidx
  push Not at hna
  exact hna

theorem mcltf_facts_orthogonalGroup_quadMinus {m : ℕ} (hm : 2 ≤ m) :
    mcltf_Facts ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus m (ZMod 2) 1 1)) := by
  rcases Nat.lt_or_ge m 4 with h | h
  · exact mcltf_facts_orthogonalGroup_quadMinus_small (by omega)
  · exact mcltf_facts_orthogonalGroup_quadMinus_large h

end Models

section GLA

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem mcltf_glaOrthGroup_eq_comap {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    CFSG.Open.GLAOrthGroup Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom :=
  closure_isometries_eq_comap hQ

@[expose] noncomputable def mcltf_glaOrthEquiv {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    ↥(CFSG.Open.GLAOrthGroup Q₀) ≃* ↥(TauCeti.QuadraticMap.orthogonalGroup Q) :=
  ((toLinEquiv ι K).subgroupMap (CFSG.Open.GLAOrthGroup Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [mcltf_glaOrthGroup_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

theorem mcltf_coe_quadPlus (n : ℕ) : ⇑(quadPlus n K) = CFSG.Open.GLAQPlus K n :=
  funext fun v => quadPlus_apply n K v

theorem mcltf_facts_glaPlus {n : ℕ} (hn : 2 ≤ n) :
    mcltf_Facts ↥(CFSG.Open.GLAOrthGroup (CFSG.Open.GLAQPlus (ZMod 2) n)) := by
  refine mcltf_facts_of_mulEquiv (mcltf_glaOrthEquiv (mcltf_coe_quadPlus n)) ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · obtain rfl : n = 2 := by omega
    exact mcltf_facts_orthogonalGroup_quadPlus_two
  · exact mcltf_facts_orthogonalGroup_quadPlus h

@[expose] def mcltf_minusIdx (n : ℕ) :
    Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 ≃ CFSG.Open.GLAMinusIdx n :=
  (Equiv.sumAssoc (Fin n) (Fin n) (Fin 2)).symm

@[expose] noncomputable def mcltf_minusLin (n : ℕ) :
    (CFSG.Open.GLAMinusIdx n → K) ≃ₗ[K] (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2 → K) :=
  LinearEquiv.funCongrLeft K K (mcltf_minusIdx n)

@[expose] noncomputable def mcltf_quadMinusGLA (n : ℕ) (b c : K) :
    QuadraticForm K (CFSG.Open.GLAMinusIdx n → K) :=
  (quadMinus (n + 1) K b c).comp (mcltf_minusLin n).toLinearMap

theorem mcltf_coe_quadMinusGLA (n : ℕ) (b c : K) :
    ⇑(mcltf_quadMinusGLA n b c) = CFSG.Open.GLAQMinus n b c := by
  funext v
  simp only [mcltf_quadMinusGLA, QuadraticMap.comp_apply, LinearEquiv.coe_coe, quadMinus_apply,
    mcltf_minusLin, LinearEquiv.funCongrLeft_apply, mcltf_minusIdx, CFSG.Open.GLAQMinus]
  rfl

@[expose] noncomputable def mcltf_minusIsometry (n : ℕ) (b c : K) :
    (mcltf_quadMinusGLA n b c).IsometryEquiv (quadMinus (n + 1) K b c) :=
  { mcltf_minusLin n with map_app' := fun _ => rfl }

theorem mcltf_facts_glaMinus {n : ℕ} (hn : 1 ≤ n) :
    mcltf_Facts ↥(CFSG.Open.GLAOrthGroup (CFSG.Open.GLAQMinus n (1 : ZMod 2) 1)) :=
  mcltf_facts_of_mulEquiv ((mcltf_glaOrthEquiv (mcltf_coe_quadMinusGLA n 1 1)).trans
    (TauCeti.QuadraticMap.orthogonalGroupCongr (mcltf_minusIsometry n 1 1)))
    (mcltf_facts_orthogonalGroup_quadMinus (by omega))

end GLA

end CFSG.HardMathSupport.Solomon.Coordinator

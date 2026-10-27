module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma512c
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5Elim
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsLit
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bSection
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceAssemblyCentralizers

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem V_le_centralizer_B : h.V ≤ centralizer (h.B : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := LBalance.lBalancePLayer_normalizer_le_centralizer (p := 2) h.B h.isPGroup_B
  rw [LBalance.Asm.lBalancePLayer_eq_map, LBalance.Asm.lBalancePLayer_eq_map] at h1
  exact h1.trans (map_subtype_le _)

theorem K_le_layer_W : h.K ≤ h.V := by
  show h.K ≤ layerIn (normalizer (h.B : Set H))
  rw [← h.layer_eq_K]
  exact le_sup_left

theorem isPComponent_K_centralizer : h.K ≤ centralizer (h.B : Set H) ∧
    IsPComponent 2 (h.K.subgroupOf (centralizer (h.B : Set H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : h.K ≤ centralizer (h.B : Set H) := h.K_le_layer_W.trans h.V_le_centralizer_B
  exact ⟨hKC, CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hKC
    (centralizer_le_normalizer _) h.isPComponent_K.2⟩

theorem card_T_quot_eq_two (hle : h.T ≤ zpowers h.a ⊔ h.B) :
    Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haT : h.a ∈ h.T := mem_inf.mpr ⟨mem_inf.mpr ⟨h.a_mem_S, h.a_mem_normalizer⟩, h.a_mem_P⟩
  obtain ⟨a', ha'⟩ : ∃ a' : ↥h.T, (a' : H) = h.a := ⟨⟨h.a, haT⟩, rfl⟩
  set ab : ↥h.T ⧸ h.B.subgroupOf h.T := QuotientGroup.mk a' with hab
  have hab1 : ab ≠ 1 := by
    intro h1
    rw [hab, QuotientGroup.eq_one_iff, mem_subgroupOf, ha'] at h1
    exact h.a_not_mem_B h1
  have hab2 : orderOf ab = 2 := by
    apply orderOf_eq_prime _ hab1
    have ha2 : a' ^ 2 = 1 := by
      apply Subtype.ext
      rw [SubgroupClass.coe_pow, ha', ← h.orderOf_a, pow_orderOf_eq_one, OneMemClass.coe_one]
    rw [hab, ← QuotientGroup.mk_pow, ha2, QuotientGroup.mk_one]
  have htop : zpowers ab = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    have hN : zpowers h.a ≤ normalizer (h.B : Set H) := zpowers_le.mpr h.a_mem_normalizer
    have hm : (t : H) ∈ (zpowers h.a : Set H) * (h.B : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN]
      exact hle t.2
    obtain ⟨u, hu, v, hv, huv⟩ := Set.mem_mul.mp hm
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    refine ⟨k, ?_⟩
    show (QuotientGroup.mk a' : ↥h.T ⧸ h.B.subgroupOf h.T) ^ k = QuotientGroup.mk t
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf]
    have : (((a' ^ k)⁻¹ * t : ↥h.T) : H) = v := by
      rw [coe_mul, coe_inv, SubgroupClass.coe_zpow, ha', ← huv]
      group
    rw [this]
    exact hv
  rw [← Subgroup.card_top (G := ↥h.T ⧸ h.B.subgroupOf h.T), ← htop, Nat.card_zpowers, hab2]

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem genFitting_A9_or_He (hB5 : GenFittingSimpleStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hHS : HarrisSolomonA7Input)
    (hKP : Assembly.KProper Blueprint.Catalog H)
    (hT : Nat.card (↥h.T ⧸ h.B.subgroupOf h.T) = 2) (hKa : conjugate h.K h.a = h.K)
    (hK : Nonempty (OddBar h.K ≃* alternatingGroup (Fin 7))) :
    Nonempty (↥(generalizedFitting H) ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (↥(generalizedFitting H) ≃* Blueprint.NativeSporadic.He) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hBb, hb, -, -, -⟩ := h.index_two_structure hB7 hT
  have hWC : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    ext y
    rw [hBb, mem_centralizer_singleton_iff]
    exact ⟨comm_of_mem_normalizer_zpowers hb, mem_normalizer_zpowers_of_comm⟩
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  rw [hWC] at hKW hKpc
  have hcyc : ∀ R : Sylow 2 ↥(coreActionKernel h.K),
      IsCyclic (R : Subgroup ↥(coreActionKernel h.K)) := by
    have h6 := hB6 H h.toHyp52
    rw [h.toHyp52.V_eq_K hKa] at h6
    obtain ⟨hBC, R₀, hR₀⟩ := h6
    have hcB : IsCyclic ↥h.B := by rw [hBb]; infer_instance
    have hc0 : IsCyclic ↥(R₀ : Subgroup ↥(coreActionKernel h.K)) := by
      rw [hR₀]
      exact isCyclic_of_surjective (subgroupOfEquivOfLe hBC).symm (MulEquiv.surjective _)
    intro R
    exact isCyclic_of_surjective (Sylow.equiv R₀ R) (MulEquiv.surjective _)
  exact hHS H hKP (hB5 H h) b hb h.K hKW hKpc hK hcyc

end Hyp59

namespace Hyp52

variable {X : Type} [Group X] [Finite X] (h : Hyp52 X)

theorem elim513 [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hKP : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCFi : CFProp23IndexElim) (hB5 : GenFittingSimpleStatement) (hB6 : SylowKernelStatement)
    (hB7 : EmbedsTQuotStatement) (hSol : SolomonTwoSubgroupAltInput)
    (hHS : HarrisSolomonA7Input) (hHe : CFHeNoA5) (hsec : h.SectionData) : h.Elim513 := by
  intro hKa hK
  obtain ⟨hKC, hKpc⟩ := h.isPComponent_K_centralizer
  have hsol := hSol X hnonab hKP hz hU h.B h.K h.isPGroup_B hKC hKpc
  rcases hK with hK7 | hK9 | hK11
  ·
    obtain ⟨e7⟩ := hK7
    have hJ5 := h.oddBar_J_A5_of_oddBar_K_A7 hB1 hCF23 hKa ⟨e7⟩
    have hT := h.card_T_quot_eq_two (hCFi X h (Or.inl ⟨5, by norm_num, hJ5, hKa, ⟨e7⟩⟩))
    obtain ⟨H', _, _, h', ⟨eT⟩, -, -, hK', hJ', hKa', -, hlink, hKP'⟩ := hsec
    have hT' := Nat.card_congr eT.toEquiv
    have hZK : center (OddBar h.K) = ⊥ :=
      center_eq_bot_of_mulEquiv e7.symm (alternatingGroup.center_eq_bot (by simp))
    obtain ⟨eK⟩ := hK' hZK
    obtain ⟨e5⟩ := hJ5
    have hZJ : center (OddBar h.J) = ⊥ :=
      center_eq_bot_of_mulEquiv e5.symm (alternatingGroup.center_eq_bot (by simp))
    obtain ⟨eJ⟩ := hJ' hZJ
    rcases h'.genFitting_A9_or_He hB5 hB6 hB7 hHS (hKP' hKP) (hT'.trans hT) (hKa'.mpr hKa)
        ⟨eK.trans e7⟩ with hA9 | hHe'
    · obtain ⟨B₁, M, hB₁, hMC, hMpc, hM⟩ := hlink hA9
      exact hSol X hnonab hKP hz hU B₁ M hB₁ hMC hMpc (Or.inl hM)
    · exact hHe H' hHe' h'.a h'.orderOf_a h'.J h'.J_le h'.isPComponent_J ⟨eJ.trans e5⟩
  ·
    obtain ⟨e9⟩ := hK9
    have hZK : center (OddBar h.K) = ⊥ :=
      center_eq_bot_of_mulEquiv e9.symm (alternatingGroup.center_eq_bot (by simp))
    exact hsol (Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq
      (fusionZStar_eq_of_center_eq_bot hZK)).trans e9⟩)
  · exact hsol (Or.inr hK11)

end Hyp52

end CFSG.ComponentClassification.GSThmB

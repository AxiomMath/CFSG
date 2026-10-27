module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Local.CommonPrimeFixedNormalSylow
import CFSG.FeitThompson.Local.CommonFixedActionNilpotentHallQuotient
import CFSG.FeitThompson.Local.PrimeFixedSylowNotNarrow
import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.FittingSharpTISetNormalizer
import CFSG.FeitThompson.Local.CommonFixedOddActionFittingBound
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.SigmaComplementPrimeData

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson
open Subgroup Pointwise

universe u

variable {G : Type*} [Group G]

theorem sup_subgroupOf_eq_top_of_sup_eq {M A B : Subgroup G} (hAM : A ≤ M) (hBM : B ≤ M)
    (h : A ⊔ B = M) : A.subgroupOf M ⊔ B.subgroupOf M = ⊤ := by
  refine Subgroup.map_injective M.subtype_injective ?_
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAM,
    Subgroup.map_subgroupOf_eq_of_le hBM, h, ← MonoidHom.range_eq_map, M.range_subtype]

theorem map_subgroupOfEquivOfLe_subgroupOf {L A B : Subgroup G} (hAL : A ≤ L) :
    ((B.subgroupOf L).subgroupOf (A.subgroupOf L)).map
        (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom = B.subgroupOf A := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  refine ⟨?_, fun hx => ⟨⟨⟨x, hAL x.2⟩, x.2⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact hy

theorem map_subtype_centralizer (M : Subgroup G) (N : Subgroup ↥M) :
    (centralizer ((N : Subgroup ↥M) : Set ↥M)).map M.subtype
      = M ⊓ centralizer ((N.map M.subtype : Subgroup G) : Set G) := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro g ⟨n, hn, rfl⟩
    exact congrArg Subtype.val (hy n hn)
  · rintro ⟨hxM, hx⟩
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    intro n hn
    exact Subtype.ext (hx (n : G) ⟨n, hn, rfl⟩)

theorem isCommonPrimeFixedSetup_subgroupOf [Finite G] {M K Z : Subgroup G} {q : ℕ}
    (hodd : Odd (Nat.card G)) (hMsolv : Group.IsSolvable ↥M)
    (hK : K ≠ ⊥) (hsd : FreeCore.IsInternalSemidirectProduct M (sigmaCore M) K)
    (hSnotnil : ¬ Group.IsNilpotent ↥(sigmaCore M))
    (hq : q.Prime) (hZ : Z = sigmaCore M ⊓ centralizer (K : Set G))
    (hZcard : Nat.card ↥Z = q)
    (hcent : ∀ k ∈ K, k ≠ 1 → sigmaCore M ⊓ centralizer ({k} : Set G) = Z)
    (hHall : IsHallPiSubgroup (sigmaPrimes M) ((sigmaCore M).subgroupOf M))
    (hSle : sigmaCore M ≤ (⁅M, M⁆ : Subgroup G)) :
    IsCommonPrimeFixedSetup ↥M q ((sigmaCore M).subgroupOf M) (K.subgroupOf M)
      (Z.subgroupOf M) := by
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have hKM : K ≤ M := hsd.right_le
  have hZM : Z ≤ M := hZ ▸ (inf_le_left.trans hSM)
  have hcardS : Nat.card ↥((sigmaCore M).subgroupOf M) = Nat.card ↥(sigmaCore M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hcardZ : Nat.card ↥(Z.subgroupOf M) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
  have hSnormal : ((sigmaCore M).subgroupOf M).Normal := sigmaCore_normal_subgroupOf M
  have hdisj : (sigmaCore M).subgroupOf M ⊓ K.subgroupOf M = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hsd.inf_eq_bot]
    simp
  refine
    { prime := hq
      odd_natCard := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
      isSolvable := hMsolv
      normal_S := hSnormal
      isComplement := Subgroup.isComplement'_of_card_mul_and_disjoint ?_ (disjoint_iff.2 hdisj)
      coprime := ?_
      K_ne_bot := subgroupOf_ne_bot hKM hK
      not_isNilpotent_S := ?_
      commutator_eq := ?_
      Z_eq := by rw [hZ, subgroupOf_inf_centralizer hKM]
      natCard_Z := by rw [hcardZ, hZcard]
      inf_centralizer_S := ?_ }
  · rw [hcardS, hcardK, ← hsd.natCard_eq_mul, Nat.card_eq_of_bijective _ (Equiv.refl _).bijective]
  ·
    rw [hcardK]
    exact index_subgroupOf_left_eq hsd ▸ hHall.coprime_natCard_index
  · intro hnil
    exact hSnotnil (Group.nilpotent_of_mulEquiv (_h := hnil) (Subgroup.subgroupOfEquivOfLe hSM))
  ·
    have hsolvS : Group.IsSolvable ↥((sigmaCore M).subgroupOf M) := by
      have := hMsolv; infer_instance
    refine (eq_commutator_of_isSolvable_of_le_commutator _ _
      (sup_subgroupOf_eq_top_of_sup_eq hSM hKM hsd.sup_eq) hdisj ?_).symm
    rw [commutator_eq_subgroupOf_commutator]
    exact Subgroup.comap_mono hSle
  · intro k hk hk1
    rw [← subgroupOf_inf_centralizer_singleton (sigmaCore M) k,
      hcent (k : G) (Subgroup.mem_subgroupOf.1 hk) (fun hc => hk1 (Subtype.ext hc))]

theorem mem_betaPrimes_of_isCommonPrimeFixedSetup [Finite G] {M K Z : Subgroup G} {q : ℕ}
    (h : IsCommonPrimeFixedSetup ↥M q ((sigmaCore M).subgroupOf M) (K.subgroupOf M)
      (Z.subgroupOf M)) :
    q ∈ betaPrimes ↥M ∧ ∃ Q : Sylow q ↥M, (Q : Subgroup ↥M).Normal := by
  have := Fact.mk h.prime
  obtain ⟨D, hDS, hDhall, hDK⟩ := exists_hall_qCompl_normalized_by h
  obtain ⟨hDne, -, -, hcompl, hDnorm, -, hcop, hCD, hCQ, -, -⟩ :=
    common_prime_fixed_complement_layout h hDS hDhall hDK
  have hZQ : Z.subgroupOf M = _root_.CFSG.FeitThompson.pCoreIn q
      ((sigmaCore M).subgroupOf M) ⊓ centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    refine le_antisymm (le_inf h.Z_le_pCoreIn (h.Z_eq ▸ inf_le_right)) ?_
    rw [h.Z_eq]
    exact inf_le_inf_right _
      (_root_.CFSG.FeitThompson.pCoreIn_le q ((sigmaCore M).subgroupOf M))
  have hnarrow : ¬ IsPNarrow q
      ↥(_root_.CFSG.FeitThompson.pCoreIn q ((sigmaCore M).subgroupOf M)) := by
    have := h.isSolvable
    exact not_isPNarrow_of_centralizer_lt h.prime h.odd_natCard h.normal_pCoreIn hcompl
      hDnorm (h.inf_D_K_eq_bot hDS) h.isPGroup_pCoreIn hcop
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hDS) h.coprime)
      hDne h.K_ne_bot hCD hCQ hZQ h.natCard_Z rfl (h.inf_centralizer_lt_pCoreIn hDS hDhall)
  refine ⟨(mem_betaPrimes_iff_exists h.prime).2
      ⟨h.natCard_Z ▸ Subgroup.card_subgroup_dvd_card (Z.subgroupOf M), h.sylow,
        by rwa [h.coe_sylow]⟩, h.sylow, ?_⟩
  rw [h.coe_sylow]; exact h.normal_pCoreIn

theorem FBG_prime_fixed_exceptional_hall_core
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FBG_prime_fixed_exceptional_hall_core.{u} := by
  intro G _ _ hG M hM K hK hKM hsd hSnotnil q hq Z hZ hZcard hcent H hH
  have hfin : Finite G := Finite.of_fintype G
  obtain ⟨⟨-, hHallOf⟩, -, hSle⟩ := h₁ G hG M hM
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hSM : sigmaCore M ≤ M := sigmaCore_le M
  have h := isCommonPrimeFixedSetup_subgroupOf hG.odd_natCard hMsolv hK hsd hSnotnil hq hZ
    hZcard hcent hHallOf hSle
  have := Fact.mk hq
  obtain ⟨D, hDS, hDhall, hDK⟩ := exists_hall_qCompl_normalized_by h
  obtain ⟨hHbot, hHS, hnilq, hcomm, hFeq, -⟩ :=
    common_prime_fixed_hall_core_quotient h hDS hDhall hDK
  have hsec := h.isPrimeFixedSectionSetup hDS hDhall hDK
  have hQ0 := h.inf_centralizer_lt_pCoreIn hDS hDhall
  have hFlt : fittingRaw ↥M < (sigmaCore M).subgroupOf M := by
    have hlt := hsec.chiefActionKer_lt_sup_Q_D hQ0
    rw [← hsec.fittingRaw_eq_chiefActionKer hQ0 (h.isNilpotent_of_isHallSubgroup hDS hDhall)] at hlt
    rwa [h.sup_pCoreIn_eq' hDS hDhall] at hlt
  have hcardK : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hKprime : (Nat.card ↥K).Prime := hcardK ▸ hsec.prime_natCard_K hQ0
  have hKcomm : ⁅K.subgroupOf M, K.subgroupOf M⁆ = (⊥ : Subgroup ↥M) := by
    have := Fact.mk (hcardK ▸ hKprime : (Nat.card ↥(K.subgroupOf M)).Prime)
    have : IsCyclic ↥(K.subgroupOf M) :=
      isCyclic_of_prime_card (p := Nat.card ↥(K.subgroupOf M)) rfl
    rw [← Subgroup.map_subtype_commutator, commutator_eq_bot, Subgroup.map_bot]
  have hSeq : sigmaCore M = (⁅M, M⁆ : Subgroup G) := by
    refine le_antisymm hSle ?_
    have hle := commutator_le_sup_commutator (K := (sigmaCore M).subgroupOf M)
      (L := K.subgroupOf M) h.normal_S h.isComplement.sup_eq_top
    rw [hKcomm, sup_bot_eq] at hle
    have h2 := Subgroup.map_mono (f := M.subtype) hle
    rwa [Subgroup.map_subtype_commutator, Subgroup.map_subgroupOf_eq_of_le hSM] at h2
  have hHcoe : H = (hallCore ↥M).map M.subtype := hH
  have hMnorm : M ≤ normalizer ((H : Subgroup G) : Set G) := by
    rw [hHcoe]; exact le_normalizer_map_subtype_of_normal hallCore_normal
  have hHSle : H ≤ sigmaCore M := by
    have := Subgroup.map_mono (f := M.subtype) hHS
    rwa [Subgroup.map_subgroupOf_eq_of_le hSM, ← hHcoe] at this
  have hFcoe : _root_.CFSG.FeitThompson.fittingIn M
      = (fittingRaw ↥M).map M.subtype := rfl
  have hFSle : _root_.CFSG.FeitThompson.fittingIn M ≤ sigmaCore M := by
    have := Subgroup.map_mono (f := M.subtype) hFlt.le
    rwa [Subgroup.map_subgroupOf_eq_of_le hSM, ← hFcoe] at this
  obtain ⟨hbeta, -⟩ := mem_betaPrimes_of_isCommonPrimeFixedSetup h
  have hQnormal : ((h.sylow : Sylow q ↥M) : Subgroup ↥M).Normal := by
    rw [h.coe_sylow]; exact h.normal_pCoreIn
  have hGamb : IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  obtain ⟨hnorm, hTI⟩ := FBG_normal_beta_sylow_fitting_ti G hGamb M hM q hbeta hq h.sylow
    hQnormal (by rwa [mixedFitting_eq])
  have hsharp : fittingRawSharp M = sharp (mixedFitting M) := by
    rw [fittingRawSharp_eq, mixedFitting_eq]; rfl
  refine ⟨hKprime, ?_, hHSle, hSeq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hHcoe, Ne, Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective]
    exact hHbot.ne'
  ·
    rw [← hSeq]
    have hnormal : (H.subgroupOf (sigmaCore M)).Normal :=
      normal_subgroupOf_of_le_normalizer hHSle (hSM.trans hMnorm)
    refine ⟨hnormal, ?_⟩
    have := hnilq
    have h0 : hallCore ↥M = H.subgroupOf M := by
      rw [hHcoe]
      exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective _).symm
    have hmapeq : ((hallCore ↥M).subgroupOf ((sigmaCore M).subgroupOf M)).map
        (Subgroup.subgroupOfEquivOfLe hSM).toMonoidHom = H.subgroupOf (sigmaCore M) := by
      rw [h0]; exact map_subgroupOfEquivOfLe_subgroupOf hSM
    have hnormal' : ((hallCore ↥M).subgroupOf ((sigmaCore M).subgroupOf M)).Normal :=
      Subgroup.normal_subgroupOf
    exact Group.nilpotent_of_mulEquiv (QuotientGroup.congr _ _
      (Subgroup.subgroupOfEquivOfLe hSM) hmapeq)
  ·
    rw [← hSeq]
    have := Subgroup.map_mono (f := M.subtype) hcomm
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hSM, ← hFcoe] at this
  ·
    have hmap : _root_.CFSG.FeitThompson.fittingIn M
        = H ⊔ (M ⊓ centralizer ((H : Subgroup G) : Set G)) := by
      rw [hFcoe, hFeq, Subgroup.map_sup, map_subtype_centralizer, ← hHcoe]
    rw [hmap]
    exact Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hMnorm)
  ·
    rw [← hSeq]
    have := (Subgroup.map_lt_map_iff_of_injective M.subtype_injective).2 hFlt
    rwa [Subgroup.map_subgroupOf_eq_of_le hSM, ← hFcoe] at this
  · rw [hsharp]; exact hnorm
  · intro g hg
    rw [hsharp]; exact hTI g hg

end

end CFSG.FeitThompson.Proofs

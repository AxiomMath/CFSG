module

public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.NormalPSubgroupPComplCoreTransfer
import CFSG.FeitThompson.Local.PrimeCentralizerComplementNoncentral
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.FittingOfComplementaryPrimeCore
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.OddOrder.CoprimeNilpotentSubgroupsCommute

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem mixedFitting_map_subtype (H : Subgroup G) (K : Subgroup ↥H) :
    mixedFitting (K.map H.subtype) = ((fittingRaw ↥K).map K.subtype).map H.subtype := by
  have he : fittingRaw ↥(K.map H.subtype)
      = (fittingRaw ↥K).map (equivMapOfInjective K H.subtype H.subtype_injective :
          ↥K →* ↥(K.map H.subtype)) :=
    (map_fittingRaw_of_mulEquiv (equivMapOfInjective K H.subtype H.subtype_injective)).symm
  have hcomp : (K.map H.subtype).subtype.comp
      (equivMapOfInjective K H.subtype H.subtype_injective : ↥K →* ↥(K.map H.subtype))
      = H.subtype.comp K.subtype := by ext x; rfl
  rw [mixedFitting_eq, he, Subgroup.map_map, hcomp, ← Subgroup.map_map]

theorem mixedFitting_pComplCoreIn (p : ℕ) (H : Subgroup G) :
    mixedFitting (pComplCoreIn p H) = mixedFitting H ⊓ pComplCoreIn p H := by
  rw [pComplCoreIn_eq, mixedFitting_map_subtype, map_subtype_fittingRaw_pComplCore,
    Subgroup.map_inf _ _ _ H.subtype_injective, ← mixedFitting_eq, ← pComplCoreIn_eq]

theorem le_pComplCoreIn {p : ℕ} {X N : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set G)) (hpN : ¬ p ∣ Nat.card ↥N) : N ≤ pComplCoreIn p X := by
  rw [pComplCoreIn_eq, pComplCore_eq_piCore]
  refine le_map_piCore_of_le_of_le_normalizer hNX hnorm (isPiSubgroup_iff.2 fun s hs => ?_)
  exact ⟨Nat.prime_of_mem_primeFactors hs, fun h => hpN (h ▸ Nat.dvd_of_mem_primeFactors hs)⟩

theorem le_normalizer_pComplCoreIn_of_le_normalizer (p : ℕ) {X L : Subgroup G}
    (hL : L ≤ normalizer (X : Set G)) :
    L ≤ normalizer ((pComplCoreIn p X : Subgroup G) : Set G) := by
  rw [pComplCoreIn_eq]
  exact le_normalizer_map_subtype_of_characteristic _ hL

theorem mixedFitting_pComplCoreIn_eq_pComplCoreIn_mixedFitting {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) :
    mixedFitting (pComplCoreIn p H) = pComplCoreIn p (mixedFitting H) := by
  rw [mixedFitting_pComplCoreIn]
  refine le_antisymm (le_pComplCoreIn inf_le_left ?_ ?_) (le_inf (pComplCoreIn_le p _) ?_)
  · exact le_normalizer_inf Subgroup.le_normalizer
      ((mixedFitting_le H).trans (le_normalizer_pComplCoreIn p H))
  · exact fun hdvd => not_dvd_natCard_pComplCoreIn hp H
      (hdvd.trans (Subgroup.card_dvd_of_le inf_le_right))
  · exact le_pComplCoreIn ((pComplCoreIn_le p _).trans (mixedFitting_le H))
      (le_normalizer_pComplCoreIn_of_le_normalizer p (le_normalizer_mixedFitting H))
      (not_dvd_natCard_pComplCoreIn hp (mixedFitting H))

theorem coprime_natCard_of_isPGroup_of_not_dvd {p : ℕ} (hp : p.Prime) {A N : Subgroup G}
    (hA : IsPGroup p ↥A) (hN : ¬ p ∣ Nat.card ↥N) :
    (Nat.card ↥A).Coprime (Nat.card ↥N) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  rw [hn]
  exact (hp.coprime_iff_not_dvd.2 hN).pow_left n

omit [Finite G] in
theorem le_centralizer_of_coprime_natCard_of_isNilpotent (X : Subgroup G) {A B : Subgroup G}
    (hnil : Group.IsNilpotent ↥X) (hAX : A ≤ X) (hBX : B ≤ X)
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥B)) : A ≤ centralizer (B : Set G) := by
  have := hnil
  have hcardA : Nat.card ↥(A.subgroupOf X) = Nat.card ↥A :=
    Nat.card_congr (subgroupOfEquivOfLe hAX).toEquiv
  have hcardB : Nat.card ↥(B.subgroupOf X) = Nat.card ↥B :=
    Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv
  intro a ha
  refine mem_centralizer_iff.2 fun b hb => ?_
  have hc := commute_of_coprime_natCard (R := A.subgroupOf X) (S := B.subgroupOf X)
    (by rwa [hcardA, hcardB]) (r := ⟨a, hAX ha⟩) (s := ⟨b, hBX hb⟩)
    (mem_subgroupOf.2 ha) (mem_subgroupOf.2 hb)
  exact congrArg Subtype.val hc.symm

omit [Finite G] in
theorem isSolvable_of_le_of_isSolvable {A B : Subgroup G} (hAB : A ≤ B)
    (hB : Group.IsSolvable ↥B) : Group.IsSolvable ↥A := by
  have := hB
  have : Group.IsSolvable ↥(A.subgroupOf B) := inferInstance
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hAB).symm.toMonoidHom) (MulEquiv.injective _)

omit [Finite G] in
theorem normalizer_eq_of_isCoatom [IsSimpleGroup G] {X R : Subgroup G} (hX : IsCoatom X)
    (hR : R ≠ ⊥) (hRX : R ≤ X) (hnorm : X ≤ normalizer (R : Set G)) :
    normalizer (R : Set G) = X := by
  have hlt : normalizer (R : Set G) < ⊤ :=
    normalizer_lt_top_of_isSimpleGroup (bot_lt_iff_ne_bot.2 hR)
      (lt_of_le_of_lt hRX (lt_top_iff_ne_top.2 hX.1))
  rcases eq_or_lt_of_le hnorm with heq | hlt2
  · exact heq.symm
  · exact absurd (hX.2 _ hlt2) hlt.ne

variable {p : ℕ} {M E H : Subgroup G}

namespace IsMixedFittingSetup

variable (h : IsMixedFittingSetup p M E)

include h

theorem pComplCoreIn_mixedFitting_le_pComplCoreIn_mixedFittingCentralizer :
    pComplCoreIn p (mixedFitting M) ≤ pComplCoreIn p (mixedFittingCentralizer M E) := by
  have hEp : IsPGroup p ↥E := h.isElementaryAbelian.isPGroup
  have hcop : (Nat.card ↥E).Coprime (Nat.card ↥(pComplCoreIn p (mixedFitting M))) :=
    coprime_natCard_of_isPGroup_of_not_dvd h.prime hEp
      (not_dvd_natCard_pComplCoreIn h.prime (mixedFitting M))
  have hle : pComplCoreIn p (mixedFitting M) ≤ mixedFittingCentralizer M E := by
    rw [mixedFittingCentralizer_eq]
    refine le_inf (pComplCoreIn_le p (mixedFitting M)) ?_
    exact le_centralizer_of_coprime_natCard_of_isNilpotent (mixedFitting M)
      (isNilpotent_mixedFitting M) (pComplCoreIn_le p _) h.le hcop.symm
  exact le_pComplCoreIn hle
    ((mixedFittingCentralizer_le M E).trans (le_normalizer_pComplCoreIn p (mixedFitting M)))
    (not_dvd_natCard_pComplCoreIn h.prime (mixedFitting M))

theorem pComplCoreIn_ne_bot : pComplCoreIn p M ≠ ⊥ := by
  obtain ⟨q, hq, hqp⟩ := h.exists_mem_primeFactors_ne
  have hqprime := Nat.prime_of_mem_primeFactors hq
  have hne : pCoreIn q (mixedFitting M) ≠ ⊥ :=
    pCoreIn_ne_bot_of_dvd_natCard hqprime (isNilpotent_mixedFitting M)
      (Nat.dvd_of_mem_primeFactors hq)
  have hle : pCoreIn q (mixedFitting M) ≤ pComplCoreIn p M := by
    rw [pComplCoreIn_eq]
    exact le_map_pComplCore_of_isPGroup hqprime (Ne.symm hqp)
      ((pCoreIn_le q _).trans (mixedFitting_le M))
      (le_normalizer_pCoreIn q (le_normalizer_mixedFitting M)) (isPGroup_pCoreIn hqprime _)
  exact fun hbot => hne (le_bot_iff.1 (hbot ▸ hle))

theorem pCoreIn_mixedFitting_competing_ne_bot [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    pCoreIn p (mixedFitting H) ≠ ⊥ := by
  refine pCoreIn_ne_bot_of_dvd_natCard h.prime (isNilpotent_mixedFitting H)
    (Nat.dvd_of_mem_primeFactors ?_)
  rw [h.primeFactors_mixedFitting_competing hna hodd hsolv hH hTH]
  exact h.mem_primeFactors_mixedFitting

theorem pComplCoreIn_mixedFitting_competing_le_centralizer_pCoreIn [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    pComplCoreIn p (mixedFitting H)
      ≤ centralizer ((pCoreIn p (mixedFittingCentralizer M E) : Subgroup G) : Set G) := by
  refine pComplCoreIn_le_of_forall_pCoreIn_le (isNilpotent_mixedFitting H) fun r hr hrp => ?_
  by_cases hrπ : r ∈ (Nat.card ↥(mixedFitting M)).primeFactors
  · have hTr : pCoreIn p (mixedFittingCentralizer M E) ≤ pComplCoreIn r H := by
      rw [pComplCoreIn_eq]
      exact h.pCoreIn_le_map_pComplCore hna hodd hsolv hrπ h.mem_primeFactors_mixedFitting hrp
        hH.1 hTH
    have hcent : pCoreIn r (mixedFitting H)
        ≤ centralizer ((pComplCoreIn r H : Subgroup G) : Set G) :=
      le_centralizer_pComplCoreIn hr ((pCoreIn_le r _).trans (mixedFitting_le H))
        (le_normalizer_pCoreIn r (le_normalizer_mixedFitting H)) (isPGroup_pCoreIn hr _)
    exact hcent.trans (Subgroup.centralizer_le fun x hx => hTr hx)
  · rw [pCoreIn_eq_bot_of_notMem_primeFactors hr
      (by rwa [h.primeFactors_mixedFitting_competing hna hodd hsolv hH hTH])]
    exact bot_le

theorem pComplCoreIn_competing_le [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    pComplCoreIn p H ≤ M := by
  set N := pComplCoreIn p H with hN
  set A := pCoreIn p (mixedFittingCentralizer M E) with hA
  have hNH : N ≤ H := pComplCoreIn_le p H
  have hNne : N ≠ ⊤ := fun hcon => hH.1 (top_le_iff.1 (hcon ▸ hNH))
  have hsolvN : Group.IsSolvable ↥N := hsolv N hNne
  have hAH : A ≤ H := (pCoreIn_le p _).trans hTH
  have hAnorm : A ≤ normalizer (N : Set G) :=
    hAH.trans (le_normalizer_pComplCoreIn_of_le_normalizer p Subgroup.le_normalizer)
  have hcop : (Nat.card ↥A).Coprime (Nat.card ↥N) :=
    coprime_natCard_of_isPGroup_of_not_dvd h.prime (isPGroup_pCoreIn h.prime _)
      (not_dvd_natCard_pComplCoreIn h.prime H)
  have hfit : ⁅(fittingRaw ↥N).map N.subtype, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← mixedFitting_eq,
      mixedFitting_pComplCoreIn_eq_pComplCoreIn_mixedFitting h.prime]
    exact h.pComplCoreIn_mixedFitting_competing_le_centralizer_pCoreIn hna hodd hsolv hH hTH
  have hNA : ⁅N, A⁆ = ⊥ :=
    commutator_eq_bot_of_commutator_map_fittingRaw_eq_bot hAnorm hcop hfit
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hNA).trans
    (h.centralizer_pCoreIn_le h.prime h.mem_primeFactors_mixedFitting)

theorem pComplCoreIn_le_competing [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    pComplCoreIn p M ≤ H := by
  set N := pComplCoreIn p M with hN
  set A := pCoreIn p (mixedFitting H) with hA
  have hAM : A ≤ M :=
    (pCoreIn_le p _).trans (h.mixedFitting_competing_le hna hodd hsolv hH hTH)
  have hAH : A ≤ H := (pCoreIn_le p _).trans (mixedFitting_le H)
  have hNM : N ≤ M := pComplCoreIn_le p M
  have hsolvN : Group.IsSolvable ↥N := isSolvable_of_le_of_isSolvable hNM h.isSolvable
  have hAnorm : A ≤ normalizer (N : Set G) :=
    hAM.trans (le_normalizer_pComplCoreIn_of_le_normalizer p Subgroup.le_normalizer)
  have hcop : (Nat.card ↥A).Coprime (Nat.card ↥N) :=
    coprime_natCard_of_isPGroup_of_not_dvd h.prime (isPGroup_pCoreIn h.prime _)
      (not_dvd_natCard_pComplCoreIn h.prime M)
  have hfit : ⁅(fittingRaw ↥N).map N.subtype, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← mixedFitting_eq,
      mixedFitting_pComplCoreIn_eq_pComplCoreIn_mixedFitting h.prime]
    refine h.pComplCoreIn_mixedFitting_le_pComplCoreIn_mixedFittingCentralizer.trans ?_
    exact le_centralizer_of_le_centralizer
      (h.pCoreIn_competing_le_centralizer_pComplCoreIn hna hodd hsolv hH hTH
        h.mem_primeFactors_mixedFitting)
  have hNA : ⁅N, A⁆ = ⊥ :=
    commutator_eq_bot_of_commutator_map_fittingRaw_eq_bot hAnorm hcop hfit
  refine (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hNA).trans ?_
  refine (Subgroup.centralizer_le_normalizer _).trans (le_of_eq ?_)
  exact normalizer_eq_of_isCoatom hH
    (h.pCoreIn_mixedFitting_competing_ne_bot hna hodd hsolv hH hTH) hAH
    (le_normalizer_pCoreIn p (le_normalizer_mixedFitting H))

theorem pComplCoreIn_competing_eq [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) :
    pComplCoreIn p H = pComplCoreIn p M := by
  refine le_antisymm ?_ ?_
  ·
    have hDp : pCoreIn p (mixedFitting H) ≤ M :=
      (pCoreIn_le p _).trans (h.mixedFitting_competing_le hna hodd hsolv hH hTH)
    have htrans := inf_map_pComplCore_le_map_pComplCore_of_normal_pSubgroup hna hodd hsolv
      h.prime (M := H) (D := pCoreIn p (mixedFitting H)) (X := M) hH
      ((pCoreIn_le p _).trans (mixedFitting_le H))
      (normal_subgroupOf_of_le_normalizer ((pCoreIn_le p _).trans (mixedFitting_le H))
        (le_normalizer_pCoreIn p (le_normalizer_mixedFitting H)))
      (isPGroup_pCoreIn h.prime _)
      (h.pCoreIn_mixedFitting_competing_ne_bot hna hodd hsolv hH hTH) h.ne_top hDp
    rw [← pComplCoreIn_eq, ← pComplCoreIn_eq] at htrans
    exact fun x hx => htrans ⟨hx, h.pComplCoreIn_competing_le hna hodd hsolv hH hTH hx⟩
  ·
    have hZM : pCoreIn p (centreIn (mixedFitting M)) ≤ M :=
      (pCoreIn_le p _).trans ((centreIn_le _).trans (mixedFitting_le M))
    have hZH : pCoreIn p (centreIn (mixedFitting M)) ≤ H :=
      (h.pCoreIn_centreIn_le_mixedFittingCentralizer p).trans hTH
    have htrans := inf_map_pComplCore_le_map_pComplCore_of_normal_pSubgroup hna hodd hsolv
      h.prime (M := M) (D := pCoreIn p (centreIn (mixedFitting M))) (X := H) h.isCoatom hZM
      (normal_subgroupOf_of_le_normalizer hZM
        (le_normalizer_pCoreIn_centreIn_mixedFitting p M))
      (isPGroup_pCoreIn h.prime _)
      (h.pCoreIn_centreIn_ne_bot h.prime h.mem_primeFactors_mixedFitting) hH.1 hZH
    rw [← pComplCoreIn_eq, ← pComplCoreIn_eq] at htrans
    exact fun x hx => htrans ⟨hx, h.pComplCoreIn_le_competing hna hodd hsolv hH hTH hx⟩

theorem eq_of_le_mixedFittingCentralizer [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable K)
    (hH : IsCoatom H) (hTH : mixedFittingCentralizer M E ≤ H) : H = M := by
  have heq := h.pComplCoreIn_competing_eq hna hodd hsolv hH hTH
  have hRne : pComplCoreIn p M ≠ ⊥ := h.pComplCoreIn_ne_bot
  have hRM : normalizer ((pComplCoreIn p M : Subgroup G) : Set G) = M :=
    normalizer_eq_of_isCoatom h.isCoatom hRne (pComplCoreIn_le p M)
      (le_normalizer_pComplCoreIn_of_le_normalizer p Subgroup.le_normalizer)
  have hRH : normalizer ((pComplCoreIn p H : Subgroup G) : Set G) = H :=
    normalizer_eq_of_isCoatom hH (heq ▸ hRne) (pComplCoreIn_le p H)
      (le_normalizer_pComplCoreIn_of_le_normalizer p Subgroup.le_normalizer)
  rw [← hRH, heq, hRM]

end IsMixedFittingSetup

end

end CFSG.FeitThompson

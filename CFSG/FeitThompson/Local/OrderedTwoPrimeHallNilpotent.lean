module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.BetaPrimeDerivedNilpotent
import CFSG.FeitThompson.Local.BetaCoreHallQuotient
import CFSG.FeitThompson.Local.BetaPrimeQuotientLargestPrime
import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Local.SigmaSylowAlphaProductNormal
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

section General

variable {H : Type*} [Group H]

theorem isPGroup_of_forall_prime_eq [Finite H] {r : ℕ}
    (h : ∀ d : ℕ, d.Prime → d ∣ Nat.card H → d = r) : IsPGroup r H :=
  IsPGroup.of_card
    (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdvd => h _ hd hdvd)

theorem not_dvd_natCard_of_isPGroup [Finite H] {r s : ℕ} (hr : r.Prime) (hs : s.Prime)
    (hrs : r ≠ s) (h : IsPGroup s H) : ¬ r ∣ Nat.card H := by
  have := Fact.mk hs
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h
  rw [hk]
  exact fun hdvd => hrs ((Nat.prime_dvd_prime_iff_eq hr hs).1 (hr.dvd_of_dvd_pow hdvd))

theorem natCard_eq_pow_factorization_of_sylow_le [Finite H] {r : ℕ} [Fact r.Prime]
    {A : Subgroup H} (hA : IsPGroup r ↥A) (h : ∀ S : Sylow r H, (↑S : Subgroup H) ≤ A) :
    Nat.card ↥A = r ^ (Nat.card H).factorization r := by
  obtain ⟨S, hle⟩ := hA.exists_le_sylow
  rw [le_antisymm hle (h S)]
  exact S.card_eq_multiplicity

theorem isNilpotent_of_normal_sylow_pair [Finite H] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hprimes : ∀ r ∈ (Nat.card H).primeFactors, r = p ∨ r = q)
    {P Q : Subgroup H} [P.Normal] [Q.Normal] (hP : IsPGroup p ↥P) (hQ : IsPGroup q ↥Q)
    (hPcard : Nat.card ↥P = p ^ (Nat.card H).factorization p)
    (hQcard : Nat.card ↥Q = q ^ (Nat.card H).factorization q) :
    Group.IsNilpotent H := by
  refine ((Group.isNilpotent_of_finite_tfae (G := H)).out 4 1).1 ?_
  intro r hrf S
  by_cases hrp : r = p
  · subst hrp
    rw [← Subgroup.eq_of_le_of_card_ge (hP.le_sylow_of_normal S)
      (by rw [hPcard, S.card_eq_multiplicity])]
    infer_instance
  by_cases hrq : r = q
  · subst hrq
    rw [← Subgroup.eq_of_le_of_card_ge (hQ.le_sylow_of_normal S)
      (by rw [hQcard, S.card_eq_multiplicity])]
    infer_instance
  · have hnd : ¬ r ∣ Nat.card H := fun hdvd => by
      rcases hprimes r (Nat.mem_primeFactors.2 ⟨hrf.out, hdvd, Nat.card_pos.ne'⟩) with h | h
      · exact hrp h
      · exact hrq h
    have hone : Nat.card ↥(↑S : Subgroup H) = 1 := by
      rw [S.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hnd, pow_zero]
    rw [Subgroup.card_eq_one.1 hone]
    infer_instance

theorem exists_normal_sylow_of_isNilpotent_normal [Finite H] {r : ℕ} [Fact r.Prime]
    {J : Subgroup H} [J.Normal] (hJnil : Group.IsNilpotent ↥J) (hidx : ¬ r ∣ J.index) :
    ∃ P : Subgroup H, P.Normal ∧ IsPGroup r ↥P ∧
      Nat.card ↥P = r ^ (Nat.card H).factorization r := by
  obtain ⟨S⟩ : Nonempty (Sylow r ↥J) := inferInstance
  have hSchar : (↑S : Subgroup ↥J).Characteristic := S.characteristic_of_normal inferInstance
  refine ⟨Subgroup.map J.subtype (↑S : Subgroup ↥J), ConjAct.normal_of_characteristic_of_normal,
    S.isPGroup'.map _, ?_⟩
  rw [Subgroup.card_subtype, S.card_eq_multiplicity,
    factorization_natCard_eq_of_not_dvd_index hidx]

end General

section Ambient

variable {G : Type u} [Group G]

theorem isPGroup_quotient_subgroupOf_of_le {q : ℕ} {N W Y : Subgroup G} (hWY : W ≤ Y)
    (hWN : W ≤ normalizer (N : Set G)) [(N.subgroupOf Y).Normal]
    (hq : IsPGroup q (↥Y ⧸ N.subgroupOf Y)) :
    letI := normal_subgroupOf_of_le_normalizer hWN
    IsPGroup q (↥W ⧸ N.subgroupOf W) := by
  have hNW := normal_subgroupOf_of_le_normalizer hWN
  set f : ↥W →* (↥Y ⧸ N.subgroupOf Y) :=
    (QuotientGroup.mk' (N.subgroupOf Y)).comp (Subgroup.inclusion hWY) with hf
  have hker : f.ker = N.subgroupOf W := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.subgroupOf,
      Subgroup.subgroupOf, Subgroup.comap_comap, Subgroup.subtype_comp_inclusion]
  have hrange : IsPGroup q ↥f.range := hq.to_subgroup f.range
  have h1 : IsPGroup q (↥W ⧸ f.ker) :=
    hrange.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  exact h1.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)

variable [Finite G]

theorem le_map_pComplCore_of_isPGroup_of_lt {p q : ℕ} (hq : q.Prime) (hpq : p < q)
    {M : Subgroup G} [(pComplCore p ↥M).Normal]
    (hbound : ∀ r ∈ (Nat.card (↥M ⧸ pComplCore p ↥M)).primeFactors, r ≤ p)
    {T : Subgroup G} (hTM : T ≤ M) (hT : IsPGroup q ↥T) :
    T ≤ Subgroup.map M.subtype (pComplCore p ↥M) := by
  have hnd : ¬ q ∣ Nat.card (↥M ⧸ pComplCore p ↥M) := fun hdvd => by
    have := hbound q (Nat.mem_primeFactors.2 ⟨hq, hdvd, Nat.card_pos.ne'⟩)
    omega
  have hTsub : IsPGroup q ↥(T.subgroupOf M) := hT.of_equiv (subgroupOfEquivOfLe hTM).symm
  have hker : T.subgroupOf M ≤ (QuotientGroup.mk' (pComplCore p ↥M)).ker := by
    refine (Subgroup.map_eq_bot_iff _).1 ?_
    have := Fact.mk hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hTsub.map (QuotientGroup.mk' (pComplCore p ↥M)))
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, pow_zero] at hk
      exact Subgroup.card_eq_one.1 hk
    · exact absurd ((dvd_pow_self q hpos.ne').trans
        (hk ▸ Subgroup.card_subgroup_dvd_card _)) hnd
  rw [QuotientGroup.ker_mk'] at hker
  calc T = Subgroup.map M.subtype (T.subgroupOf M) :=
        (Subgroup.map_subgroupOf_eq_of_le hTM).symm
    _ ≤ _ := Subgroup.map_mono hker

end Ambient

theorem FTS_ordered_two_prime_hall_nilpotent
    (h₁ : CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FTS_ordered_two_prime_hall_nilpotent.{u} := by
  intro G _ _ hG M X Y W p q hM hp hq hpodd hqodd hpq hpbeta hqbeta hXM hXq hY hXW hWY hHall
  have : Fintype G := Fintype.ofFinite G
  have hpf := Fact.mk hp
  have hqf := Fact.mk hq
  have hG6 : CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hXY : X ≤ Y := hY ▸ le_sup_left
  have hMMY : (⁅M, M⁆ : Subgroup G) ≤ Y := hY ▸ le_sup_right
  have hYM : Y ≤ M := hY ▸ sup_le hXM (Subgroup.commutator_le_self M)
  have hWM : W ≤ M := hWY.trans hYM
  have hWprimes : ∀ r ∈ (Nat.card ↥W).primeFactors, r = p ∨ r = q := by
    intro r hr
    have hcard : Nat.card ↥(W.subgroupOf Y) = Nat.card ↥W :=
      Nat.card_congr (subgroupOfEquivOfLe hWY).toEquiv
    simpa using (isHallPiSubgroup_iff.1 hHall.2).1 r (by rwa [hcard])
  obtain ⟨hNinst, hbound⟩ :=
    FTS_beta_prime_quotient_largest_prime G hG6 M hM p hp hpodd hpbeta
  have := hNinst
  set K : Subgroup G := Subgroup.map M.subtype (pComplCore p ↥M) with hKdef
  have hKnorm : M ≤ normalizer (K : Set G) :=
    le_normalizer_map_subtype_of_normal (N := pComplCore p ↥M) hNinst
  have hKp : ¬ p ∣ Nat.card ↥K := by
    rw [hKdef, Subgroup.card_subtype]
    exact not_dvd_natCard_pComplCore hp ↥M
  have hQnormal : (K.subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer (hWM.trans hKnorm)
  have := hQnormal
  have hcardQ : Nat.card ↥(K.subgroupOf W) = Nat.card ↥(W ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_left K W]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hQq : IsPGroup q ↥(K.subgroupOf W) := by
    refine isPGroup_of_forall_prime_eq fun d hd hdvd => ?_
    rw [hcardQ] at hdvd
    have hdW : d ∣ Nat.card ↥W := hdvd.trans (Subgroup.card_dvd_of_le inf_le_left)
    have hdK : d ∣ Nat.card ↥K := hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)
    rcases hWprimes d (Nat.mem_primeFactors.2 ⟨hd, hdW, Nat.card_pos.ne'⟩) with rfl | rfl
    · exact absurd hdK hKp
    · rfl
  have hQsylow : ∀ S : Sylow q ↥W, (↑S : Subgroup ↥W) ≤ K.subgroupOf W := by
    intro S
    have hTle : Subgroup.map W.subtype (↑S : Subgroup ↥W) ≤ M :=
      (Subgroup.map_subtype_le _).trans hWM
    have hTq : IsPGroup q ↥(Subgroup.map W.subtype (↑S : Subgroup ↥W)) := S.isPGroup'.map _
    have hTK := le_map_pComplCore_of_isPGroup_of_lt hq hpq hbound hTle hTq
    have hS : (↑S : Subgroup ↥W) =
        (Subgroup.map W.subtype (↑S : Subgroup ↥W)).subgroupOf W := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective W.subtype_injective]
    rw [hS]
    exact Subgroup.comap_mono hTK
  have hQcard : Nat.card ↥(K.subgroupOf W) = q ^ (Nat.card ↥W).factorization q :=
    natCard_eq_pow_factorization_of_sylow_le hQq hQsylow
  have hMMnorm : M ≤ normalizer ((⁅M, M⁆ : Subgroup G) : Set G) := le_normalizer_commutator_self M
  have hJnormalY : ((⁅M, M⁆ : Subgroup G).subgroupOf Y).Normal :=
    normal_subgroupOf_of_le_normalizer (hYM.trans hMMnorm)
  have := hJnormalY
  have hJnormalW : ((⁅M, M⁆ : Subgroup G).subgroupOf W).Normal :=
    normal_subgroupOf_of_le_normalizer (hWM.trans hMMnorm)
  have := hJnormalW
  have hYquot : IsPGroup q (↥Y ⧸ (⁅M, M⁆ : Subgroup G).subgroupOf Y) := by
    have htop : (⊤ : Subgroup (↥Y ⧸ (⁅M, M⁆ : Subgroup G).subgroupOf Y)) =
        Subgroup.map (QuotientGroup.mk' ((⁅M, M⁆ : Subgroup G).subgroupOf Y))
          (X.subgroupOf Y) := by
      have h1 : (X ⊔ ⁅M, M⁆ : Subgroup G).subgroupOf Y =
          X.subgroupOf Y ⊔ (⁅M, M⁆ : Subgroup G).subgroupOf Y := Subgroup.subgroupOf_sup hXY hMMY
      have h2 : (X ⊔ ⁅M, M⁆ : Subgroup G).subgroupOf Y = ⊤ := by
        rw [← hY, Subgroup.subgroupOf_self]
      rw [← Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective ((⁅M, M⁆ : Subgroup G).subgroupOf Y)), ← h2, h1,
        Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
    have h1 : IsPGroup q ↥(X.subgroupOf Y) := hXq.of_equiv (subgroupOfEquivOfLe hXY).symm
    have h2 := h1.map (QuotientGroup.mk' ((⁅M, M⁆ : Subgroup G).subgroupOf Y))
    rw [← htop] at h2
    exact h2.of_equiv Subgroup.topEquiv
  have hWquot : IsPGroup q (↥W ⧸ (⁅M, M⁆ : Subgroup G).subgroupOf W) :=
    isPGroup_quotient_subgroupOf_of_le hWY (hWM.trans hMMnorm) hYquot
  have hidx : ¬ p ∣ ((⁅M, M⁆ : Subgroup G).subgroupOf W).index := by
    rw [Subgroup.index_eq_card]
    exact not_dvd_natCard_of_isPGroup hp hq hpq.ne hWquot
  have hJnil : Group.IsNilpotent ↥((⁅M, M⁆ : Subgroup G).subgroupOf W) := by
    have hnil : Group.IsNilpotent ↥(W ⊓ ⁅M, M⁆ : Subgroup G) := by
      refine FTS_beta_prime_derived_nilpotent h₁ h₂ G hG6 M hM (W ⊓ ⁅M, M⁆) inf_le_right ?_
      intro r hr
      have hdW : r ∣ Nat.card ↥W :=
        (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le inf_le_left)
      rcases hWprimes r (Nat.mem_primeFactors.2
        ⟨Nat.prime_of_mem_primeFactors hr, hdW, Nat.card_pos.ne'⟩) with rfl | rfl
      · exact hpbeta
      · exact hqbeta
    have heq : ((⁅M, M⁆ : Subgroup G).subgroupOf W)
        = (W ⊓ ⁅M, M⁆ : Subgroup G).subgroupOf W := by
      rw [Subgroup.inf_subgroupOf_left]
    rw [heq]
    have := hnil
    exact Group.nilpotent_of_mulEquiv
      (subgroupOfEquivOfLe (inf_le_left : (W ⊓ ⁅M, M⁆ : Subgroup G) ≤ W)).symm
  obtain ⟨P, hPnormal, hPp, hPcard⟩ :=
    exists_normal_sylow_of_isNilpotent_normal (r := p) hJnil hidx
  have := hPnormal
  exact isNilpotent_of_normal_sylow_pair hWprimes hPp hQq hPcard hQcard

end

end CFSG.FeitThompson.Proofs

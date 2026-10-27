module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.KappaResidualCoreStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.MixedElementsKappaCandidateTorus
import CFSG.FeitThompson.Local.KappaCandidateMixedSetTi
import CFSG.FeitThompson.Local.MixedKappaElementsAvoidPackets
import CFSG.FeitThompson.Local.SignalizerPacketCardinality
import CFSG.FeitThompson.Local.DisjointDSetsNonconjugateMaximals
import CFSG.FeitThompson.Local.PacketConjugationDescription
import CFSG.FeitThompson.Local.TwoCoreMixedSaturationMeasure
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.KappaPairMixedDensity

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup Pointwise
open _root_.CFSG.FeitThompson

variable {G : Type*} [Group G]

theorem conjSub03_eq_conjSubgroup (Y : Subgroup G) (g : G) :
    Prep03.conjSub Y g = Prep08.conjSubgroup Y g := by
  rw [Prep03.conjSub, Prep08.conjSubgroup, conj_smul_eq_map_conj]

theorem sigR_eq_sigmaCoreSignalizer [Finite G] (a : G) :
    Prep03.sigR a = Prep08.sigmaCoreSignalizer G a := (rfl)

theorem sigmaDelta_eq_sigmaPacketSupport [Finite G] (T : Subgroup G) :
    Prep03.sigmaDelta T = Prep08.sigmaPacketSupport G T := by
  ext y
  simp only [Prep03.sigmaDelta, Prep03.sat, Prep03.conjSet, Prep08.sigmaPacketSupport,
    Prep08.sigmaPacket, Prep08.conjSet, sigR_eq_sigmaCoreSignalizer, Set.mem_iUnion,
    Set.mem_image, Set.singleton_mul, Set.mem_smul_set, smul_eq_mul, exists_prop]
  tauto

theorem natCard_of_isDirect [Finite G] {X Y W : Subgroup G} (h : Prep03.IsDirect X Y W) :
    Nat.card X = Nat.card Y * Nat.card W := by
  obtain ⟨-, -, hsup, hinf, hcomm⟩ := h
  have hc : ∀ x ∈ Y, ∀ y ∈ W, Commute x y := by
    intro x hx y hy
    exact ((mem_centralizer_iff.1
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hx)) y hy).symm
  exact natCard_of_coe_eq_mul (by rw [← hsup]; exact coe_sup_eq_mul_of_commute hc) hinf

theorem isTIWithNormalizer_mixedTorusSet [Finite G] {Z : Subgroup G} {I : Set (Subgroup G)}
    {KT : Subgroup G → Subgroup G} (hne : (Prep03.mixedTorusSet Z I KT).Nonempty)
    (hnorm : normalizer (Prep03.mixedTorusSet Z I KT) = Z)
    (hti : ∀ g : G, g ∉ Z →
      Prep03.mixedTorusSet Z I KT ∩ Prep03.conjSet (Prep03.mixedTorusSet Z I KT) g = ∅) :
    IsTIWithNormalizer (Prep03.mixedTorusSet Z I KT) Z where
  nonempty := hne
  one_notMem := fun h => h.1.2 rfl
  normalizer_eq := hnorm
  disjoint_conj_image := by
    intro g hg
    have hg' : g⁻¹ ∉ Z := fun hc => hg (by simpa using inv_mem hc)
    rw [Set.disjoint_iff_inter_eq_empty]
    refine Eq.trans (congrArg _ ?_) (hti g⁻¹ hg')
    exact (Set.image_congr' fun x => by simp only [MulAut.conj_apply, inv_inv]).symm

theorem finsum_natCast_int_rat {α : Type*} {I : Set α} (hI : I.Finite) (f : α → ℕ) :
    ((∑ᶠ V ∈ I, (f V : ℤ) : ℤ) : ℚ) = ∑ᶠ V ∈ I, (f V : ℚ) := by
  classical
  rw [finsum_mem_eq_finite_toFinset_sum _ hI, finsum_mem_eq_finite_toFinset_sum _ hI]
  push_cast
  rfl

theorem measure_formula [Finite G] {I : Set (Subgroup G)} {KT AT : Subgroup G → Subgroup G}
    {Z : Subgroup G} {n : ℕ}
    (hfac : ∀ V ∈ I, Nat.card Z = Nat.card (KT V) * Nat.card (AT V))
    (hcount : (n : ℤ)
      = (Nat.card Z : ℤ) + (I.ncard : ℤ) - 1 - ∑ᶠ V ∈ I, (Nat.card (AT V) : ℤ)) :
    (Z.index : ℚ) * (n : ℚ)
      = (Nat.card G : ℚ) * (1 + ((I.ncard : ℚ) - 1) / (Nat.card Z : ℚ)
          - ∑ᶠ V ∈ I, (1 : ℚ) / (Nat.card (KT V) : ℚ)) := by
  classical
  have hI : I.Finite := Set.toFinite I
  have hz0 : ((Nat.card Z : ℚ)) ≠ 0 := by
    have : (0 : ℚ) < (Nat.card Z : ℚ) := by exact_mod_cast Nat.card_pos (α := Z)
    exact this.ne'
  have hsum : ∑ᶠ V ∈ I, (1 : ℚ) / (Nat.card (KT V) : ℚ)
      = (∑ᶠ V ∈ I, (Nat.card (AT V) : ℚ)) / (Nat.card Z : ℚ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hI, finsum_mem_eq_finite_toFinset_sum _ hI,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun V hV => ?_
    have hV' : V ∈ I := hI.mem_toFinset.1 hV
    have hK : (0 : ℚ) < (Nat.card (KT V) : ℚ) := by exact_mod_cast Nat.card_pos (α := KT V)
    have hA : (0 : ℚ) < (Nat.card (AT V) : ℚ) := by exact_mod_cast Nat.card_pos (α := AT V)
    rw [show (Nat.card Z : ℚ) = (Nat.card (KT V) : ℚ) * (Nat.card (AT V) : ℚ) from by
      rw [← Nat.cast_mul, hfac V hV']]
    field_simp
  have hGz : (Nat.card G : ℚ) = (Z.index : ℚ) * (Nat.card Z : ℚ) := by
    rw [← Nat.cast_mul, Subgroup.index_mul_card]
  have hcountQ : (n : ℚ)
      = (Nat.card Z : ℚ) + (I.ncard : ℚ) - 1 - ∑ᶠ V ∈ I, (Nat.card (AT V) : ℚ) := by
    have := congrArg (fun m : ℤ => (m : ℚ)) hcount
    simpa [finsum_natCast_int_rat hI (fun V => Nat.card (AT V))] using this
  rw [hsum, hGz, hcountQ]
  field_simp
  ring

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup Pointwise CFSG.FeitThompson
  CFSG.FeitThompson
  CFSG.FeitThompson.Prep03

universe u

theorem FNI_kappa_candidate_mixed_support_cardinality
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_candidate_family_common_factors.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FTS_canonical_signalizer_structure.{u})
    (h₆ : Statements.FTS_sigma_prime_separation.{u})
    (h₇ : Statements.FTS_signalizer_unique_supporting_maximum.{u})
    (h₈ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FNI_kappa_candidate_mixed_support_cardinality.{u} := by
  intro G _ _ M K A Z I KT hs
  have hamb : Prep03.IsAmbient G := hs.base.ambient
  have hmin08 : Prep08.IsMinimalSimpleOddOrder G :=
    ⟨hamb.isSimpleGroup, hamb.not_isMulCommutative, hamb.odd_natCard, hamb.forall_isSolvable⟩
  obtain ⟨-, -, hmain, -⟩ := h₂ G M K A Z I hs.base hs.I_eq
  obtain ⟨hknonempty, hb, hcpair⟩ := hmain KT hs.KT_self hs.KT_hall
  have hcoatom : ∀ V ∈ I, IsCoatom V := by
    intro V hV
    rw [hs.I_eq] at hV
    rcases hV with h | h
    · rw [h]; exact hs.base.isCoatom
    · exact h.1
  have hhall : ∀ V ∈ I, IsHallPiOf (kappaPrimes V) (KT V) V := by
    intro V hV
    by_cases hVM : V = M
    · subst hVM; rw [hs.KT_self]; exact hs.base.isHall_K
    · exact (hs.KT_hall V hV hVM).1
  obtain ⟨hdesc, hne, hT0card⟩ := FNI_kappa_candidate_mixed_set_description h₂ G M K A Z I KT hs
  obtain ⟨hnorm, hti⟩ := FNI_kappa_candidate_mixed_set_ti h₁ h₂ h₃ h₄ h₈ G M K A Z I KT hs
  have havoid := FNI_kappa_mixed_elements_avoid_packets h₁ h₄ h₅ h₆ h₇ h₈ G hamb
  have hTI : IsTIWithNormalizer (mixedTorusSet Z I KT) Z :=
    isTIWithNormalizer_mixedTorusSet hne hnorm hti
  have hsatcard : (Prep03.sat (mixedTorusSet Z I KT)).ncard
      = Z.index * (mixedTorusSet Z I KT).ncard := by
    rw [sat_eq_conjugatesOfSet]
    exact ncard_conjugatesOfSet_eq_index_mul_ncard hTI
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hsatcard]
    push_cast
    exact measure_formula (fun V hV => natCard_of_isDirect (hb V hV).2.1) hT0card
  ·
    obtain ⟨t, ht⟩ := hne
    exact ⟨t, by rw [sat_eq_conjugatesOfSet]; exact Group.subset_conjugatesOfSet ht⟩
  ·
    intro V hV
    rw [sigmaDelta_eq_sigmaPacketSupport]
    exact (FTS_packet_cardinality h₁ h₅ h₆ G hmin08 V (hcoatom V hV)).2
  ·
    intro V hV
    rw [Set.disjoint_left]
    intro x hx hxD
    rw [sat_eq_conjugatesOfSet, Group.mem_conjugatesOfSet_iff] at hx
    obtain ⟨t, ht, hconj⟩ := hx
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have hinv :=
      (FTS_packet_conjugation_description h₅ h₆ G hmin08 V (hcoatom V hV) _ rfl).2.2.2.1
    rw [sigmaDelta_eq_sigmaPacketSupport] at hxD
    have htD : t ∈ Prep08.sigmaPacketSupport G V := by
      have hmem : t ∈ Prep08.conjSet (Prep08.sigmaPacketSupport G V) c :=
        ⟨x, hxD, by rw [← hc]; group⟩
      rwa [hinv c] at hmem
    rw [hdesc] at ht
    obtain ⟨W, hW, a, ha, ha1, b, hbK, hb1, htab⟩ := Set.mem_iUnion₂.1 ht
    refine havoid W (KT W) (hcoatom W hW) (hknonempty W hW) (hhall W hW) a ha ha1 b hbK hb1 V
      (hcoatom V hV) ?_
    rw [sigmaDelta_eq_sigmaPacketSupport, ← htab]
    exact htD
  ·
    intro V hV V' hV' hVV'
    have hnc : ∀ g : G, V' ≠ Prep08.conjSubgroup V g := fun g hg =>
      (hcpair V hV V' hV' hVV').2.2 ⟨g, by rw [conjSub03_eq_conjSubgroup, ← hg]⟩
    have hd := FTS_nonconjugate_packets_disjoint h₅ h₆ G hmin08 V V' (hcoatom V hV)
      (hcoatom V' hV') hnc
    rw [sigmaDelta_eq_sigmaPacketSupport, sigmaDelta_eq_sigmaPacketSupport,
      Set.disjoint_iff_inter_eq_empty]
    exact hd
  ·
    rw [sat_eq_conjugatesOfSet]
    intro h
    obtain ⟨t, ht, hc⟩ := Group.mem_conjugatesOfSet_iff.1 h
    exact hTI.one_notMem (by rwa [isConj_one_left.1 hc] at ht)
  ·
    intro V hV
    rw [sigmaDelta_eq_sigmaPacketSupport]
    exact (FTS_packet_conjugation_description h₅ h₆ G hmin08 V (hcoatom V hV) _ rfl).2.2.2.2

end

end CFSG.FeitThompson.Proofs

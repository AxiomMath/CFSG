module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
import CFSG.FeitThompson.Local.SigmaTauThreePrimesDerivedContainment
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowEnvelope
import CFSG.FeitThompson.Local.AlphaSigmaPrimeSeparation
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.PComplementControlSylowNormalizer
import CFSG.FeitThompson.Foundations.NormalCommuteModIntersection

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
  Pointwise

universe u

variable {G : Type u} [Group G]

theorem conjSubgroup_inv_eq_conj_smul (M : Subgroup G) (g : G) :
    conjSubgroup M g⁻¹ = MulAut.conj g • M := by
  rw [conjSubgroup_eq, inv_inv, conj_smul_eq_map_conj]

theorem le_normalizer_inf {X Y K : Subgroup G} (hX : K ≤ normalizer (X : Set G))
    (hY : K ≤ normalizer (Y : Set G)) : K ≤ normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.1 (hX hg)) h,
    (Subgroup.mem_normalizer_iff.1 (hY hg)) h]

theorem mul_comm_of_normal_subgroupOf_of_coprime [Finite G] {J A B : Subgroup G}
    (hAJ : A ≤ J) (hBJ : B ≤ J) (hA : (A.subgroupOf J).Normal) (hB : (B.subgroupOf J).Normal)
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥B)) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b = b * a := by
  have := hA
  have := hB
  have hcop' : (Nat.card ↥(A.subgroupOf J)).Coprime (Nat.card ↥(B.subgroupOf J)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAJ).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBJ).toEquiv]
  exact congrArg Subtype.val (mul_comm_of_normal_of_coprime_natCard (A.subgroupOf J)
    (B.subgroupOf J) hcop' (a := ⟨a, hAJ ha⟩) (b := ⟨b, hBJ hb⟩) ha hb)

theorem le_centralizer_of_coprime_of_normal_subgroupOf [Finite G] {J A B : Subgroup G}
    (hAJ : A ≤ J) (hBJ : B ≤ J) (hA : (A.subgroupOf J).Normal) (hB : (B.subgroupOf J).Normal)
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥B)) : B ≤ centralizer (A : Set G) := fun _ hx =>
  Subgroup.mem_centralizer_iff.2 fun _ hy =>
    mul_comm_of_normal_subgroupOf_of_coprime hAJ hBJ hA hB hcop hy hx

theorem FBG_nonconjugate_derived_prime_intersection_centralization
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u}) :
    Statements.FBG_nonconjugate_derived_prime_intersection_centralization.{u} := by
  intro G _ _ hG M L E p hsetup hpL P hPJ hPp
  obtain ⟨hM, hL, hnonconj, hEM, hsd, hp, hpE, hpLdvd⟩ := hsetup
  have hsimple := hG.isSimpleGroup
  have := Fact.mk hp
  have hoddG := hG.odd_natCard
  have hsolv := hG.isSolvable
  have hna := hG.not_isMulCommutative
  have hpnotσM : p ∉ sigmaPrimes M := by
    let _ : Fintype G := Fintype.ofFinite G
    obtain ⟨hHallOf, -, -⟩ := h₁ G ⟨hoddG, hsimple, hna, hsolv⟩ M hM
    have hidx := hHallOf.2.notMem_of_mem_primeFactors_index
    rw [index_subgroupOf_left_eq hsd] at hidx
    exact hidx p (Nat.mem_primeFactors.2 ⟨hp, hpE, Nat.card_pos.ne'⟩)
  have hnc : ∀ g : G, MulAut.conj g • M ≠ L := fun g hg =>
    hnonconj g⁻¹ ((conjSubgroup_inv_eq_conj_smul M g).trans hg).symm
  have hdisj : Disjoint (sigmaPrimes M) (alphaPrimes ↥L) :=
    disjoint_sigmaPrimes_alphaPrimes_of_not_conj hna hoddG hsolv hM hL hnc
  have hDnorm := alphaCore_normal ↥L
  have hD_le : alphaCore ↥L ≤ _root_.commutator ↥L :=
    alphaCore_le_commutator hna hoddG hsolv hL
  have hnilQ : Group.IsNilpotent
      (↥(_root_.commutator ↥L) ⧸ (alphaCore ↥L).subgroupOf (_root_.commutator ↥L)) := by
    rw [isNilpotent_commutator_quotient_iff _ hD_le]
    exact isNilpotent_of_le_fittingRaw
      (commutator_quotient_alphaCore_le_fittingRaw_subgroup hoddG hsolv hL)
  obtain ⟨S⟩ := (Sylow.nonempty : Nonempty (Sylow p ↥L))
  have hSle : (S : Subgroup ↥L) ≤ _root_.commutator ↥L := by
    have hmap : ((S : Subgroup ↥L).map L.subtype) ≤ ⁅L, L⁆ :=
      FNI_sigma_third_primes_derived_containment h₁ G ⟨hoddG, hsimple, hna, hsolv⟩ p L hL hp hpL
        _ (Subgroup.map_subtype_le _)
        ⟨_, by rw [Subgroup.card_subtype]; exact S.card_eq_multiplicity⟩
    rw [← Subgroup.map_subtype_commutator] at hmap
    exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).1 hmap
  set Hin : Subgroup G := (alphaCore ↥L ⊔ (S : Subgroup ↥L)).map L.subtype with hHin
  have hHprime : ∀ r ∈ (Nat.card ↥Hin).primeFactors, r ∉ sigmaPrimes M := by
    intro r hr
    rw [hHin, Subgroup.card_subtype] at hr
    obtain ⟨hrp, hrdvd, -⟩ := Nat.mem_primeFactors.1 hr
    rcases prime_dvd_natCard_sup_sylow (alphaCore ↥L) S hrp hrdvd with h | h
    · intro hrσ
      exact Set.disjoint_left.1 hdisj hrσ (isPiSubgroup_iff.1 (isPiSubgroup_alphaCore ↥L) r
        (Nat.mem_primeFactors.2 ⟨hrp, h, Nat.card_pos.ne'⟩))
    · exact h ▸ hpnotσM
  have hcop0 : (Nat.card ↥(sigmaCore M)).Coprime (Nat.card ↥Hin) :=
    coprime_natCard_of_isPiSubgroup disjoint_compl_right (isPiSubgroup_sigmaCore M)
      (isPiSubgroup_iff.2 hHprime)
  have hcop : (Nat.card ↥(sigmaCore M ⊓ L : Subgroup G)).Coprime
      (Nat.card ↥(Hin ⊓ M : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hcop0)
  have hHinL : Hin ≤ L := Subgroup.map_subtype_le _
  have hAJ : (sigmaCore M ⊓ L : Subgroup G) ≤ M ⊓ L := inf_le_inf_right _ (sigmaCore_le M)
  have hBJ : (Hin ⊓ M : Subgroup G) ≤ M ⊓ L := le_inf inf_le_right (inf_le_left.trans hHinL)
  have hAnorm : ((sigmaCore M ⊓ L : Subgroup G).subgroupOf (M ⊓ L)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (le_normalizer_inf (inf_le_left.trans (le_normalizer_sigmaCore M))
        (inf_le_right.trans L.le_normalizer))
  have hBnorm : ((Hin ⊓ M : Subgroup G).subgroupOf (M ⊓ L)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (le_normalizer_inf (inf_le_right.trans (le_normalizer_map_subtype_of_normal
        (normal_sup_sylow (alphaCore ↥L) hD_le hnilQ S hSle)))
        (inf_le_left.trans M.le_normalizer))
  have hPHin : P ≤ Hin ⊓ M := by
    refine le_inf ?_ (hPJ.trans inf_le_left)
    have hPL : P ≤ L := hPJ.trans inf_le_right
    have hsub : IsPGroup p ↥(P.subgroupOf L) :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
    have h2 := Subgroup.map_mono (f := L.subtype)
      (le_sup_sylow_of_isPGroup (alphaCore ↥L) hD_le hnilQ S hSle hsub)
    rwa [Subgroup.map_subgroupOf_eq_of_le hPL] at h2
  exact hPHin.trans (le_centralizer_of_coprime_of_normal_subgroupOf hAJ hBJ hAnorm hBnorm hcop)

end

end CFSG.FeitThompson.Proofs

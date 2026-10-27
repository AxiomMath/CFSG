module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.KappaFixedPrimeCentralizerSylowUnique
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {π : Set ℕ} {A Q W : Subgroup G}

theorem isPiSubgroup_subgroupOf (hQW : Q ≤ W) (hQ : IsPiSubgroup π Q) :
    IsPiSubgroup π (Q.subgroupOf W) := by
  refine isPiSubgroup_iff.2 fun r hr => isPiSubgroup_iff.1 hQ r ?_
  rwa [← Subgroup.card_subtype W (Q.subgroupOf W), Subgroup.map_subgroupOf_eq_of_le hQW] at hr

theorem le_of_isHallPiSubgroup_subgroupOf [Finite G]
    (hAW : A ≤ W) (hW : W ≤ normalizer (A : Set G))
    (hHall : IsHallPiSubgroup π (A.subgroupOf W)) (hQW : Q ≤ W) (hQ : IsPiSubgroup π Q) :
    Q ≤ A := by
  have : (A.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hW
  have h := hHall.le_of_isPiSubgroup (isPiSubgroup_subgroupOf hQW hQ)
  have h3 := Subgroup.map_mono (f := W.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hQW, Subgroup.map_subgroupOf_eq_of_le hAW] at h3

theorem isHallPiOf_map_subtype [Finite G] (M : Subgroup G) {K : Subgroup ↥M}
    (h : IsHallSubgroup π K) :
    CFSG.FeitThompson.Prep03.IsHallPiOf π (K.map M.subtype) M := by
  have hsub : (K.map M.subtype).subgroupOf M = K :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
  refine ⟨Subgroup.map_subtype_le _, fun r hr => ?_, fun r hr => ?_⟩
  · rw [Subgroup.card_subtype] at hr
    exact isPiNumber_iff.1 h.natCard r hr
  · rw [Subgroup.relIndex, hsub] at hr
    exact isPiNumber_iff.1 h.index r hr

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson CFSG.FeitThompson

universe u

theorem FBG_sigma_hall_centralizer_excludes_kappa
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₃ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FBG_sigma_hall_centralizer_excludes_kappa.{u} := by
  intro G _ _ hmin M hM π H hHbot hHallH r hr hrκ
  have hamb : Prep03.IsAmbient G :=
    ⟨hmin.odd_natCard, hmin.isSimpleGroup, hmin.not_isMulCommutative, hmin.isSolvable_of_ne_top⟩
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  obtain ⟨x, hxC, hxo⟩ := exists_mem_orderOf_eq_of_dvd hrp (Nat.dvd_of_mem_primeFactors hr)
  obtain ⟨hxM, hxcent⟩ := Subgroup.mem_inf.1 hxC
  have hXcard : Nat.card ↥(zpowers x) = r := by rw [Nat.card_zpowers, hxo]
  have hXM : zpowers x ≤ M := zpowers_le.2 hxM
  have hXπ : IsPiSubgroup (kappaPrimes M) (zpowers x) := by
    refine isPiSubgroup_iff.2 fun s hs => ?_
    rw [hXcard, hrp.primeFactors, Finset.mem_singleton] at hs
    exact hs ▸ hrκ
  have hMsolv : Group.IsSolvable ↥M := hmin.isSolvable_of_ne_top M hM.1
  obtain ⟨K₀, hK₀Hall, hXK₀⟩ :=
    exists_isHallSubgroup_ge_of_isPiSubgroup (π := kappaPrimes M)
      (isPiSubgroup_subgroupOf hXM hXπ)
  set K : Subgroup G := K₀.map M.subtype with hKdef
  have hKHall : Prep03.IsHallPiOf (kappaPrimes M) K M := isHallPiOf_map_subtype M hK₀Hall
  have hXK : zpowers x ≤ K := by
    have := Subgroup.map_mono (f := M.subtype) hXK₀
    rwa [Subgroup.map_subgroupOf_eq_of_le hXM] at this
  set A : Subgroup G := Prep03.cent (sigmaCore M) (K : Set G) with hAdef
  have hsetup : Prep03.IsKappaSetup G M K A (K ⊔ A) :=
    ⟨hamb, hM, ⟨r, hrκ⟩, hKHall, rfl, rfl⟩
  obtain ⟨hdir, -, hnorm⟩ := h₂ G M K A (K ⊔ A) hsetup
  obtain ⟨-, hZeq, -⟩ := hnorm (zpowers x) hXK (by rw [hXcard]; exact hrp)
  obtain ⟨hHallOf, hHallG, -⟩ := h₁ G hmin M hM
  obtain ⟨q, hq⟩ : (Nat.card ↥H).primeFactors.Nonempty := by
    refine Nat.nonempty_primeFactors.2 (lt_of_le_of_ne Nat.card_pos (Ne.symm ?_))
    exact fun h => hHbot (Subgroup.card_eq_one.1 h)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqπ : q ∈ π := isPiSubgroup_iff.1 hHallH.isPiSubgroup q hq
  have hHS : H ≤ sigmaCore M := hHallH.le
  have hqσ : q ∈ sigmaPrimes M :=
    isPiSubgroup_iff.1 (isPiSubgroup_sigmaCore M) q
      (Nat.mem_primeFactors.2 ⟨hqp,
        (Nat.dvd_of_mem_primeFactors hq).trans (Subgroup.card_dvd_of_le hHS),
        Nat.card_pos.ne'⟩)
  have hfq : Fact q.Prime := ⟨hqp⟩
  obtain ⟨SQ⟩ : Nonempty (Sylow q ↥H) := inferInstance
  set Q : Subgroup G := (SQ : Subgroup ↥H).map H.subtype with hQdef
  have hfacHS : (Nat.card ↥(sigmaCore M)).factorization q = (Nat.card ↥H).factorization q :=
    factorization_eq_of_isHallPiSubgroup_subgroupOf hqp hHS hHallH.2 hqπ
  have hfacMS : (Nat.card ↥M).factorization q = (Nat.card ↥(sigmaCore M)).factorization q :=
    factorization_eq_of_isHallPiSubgroup_subgroupOf hqp (sigmaCore_le M) hHallOf.2 hqσ
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
    rw [hQdef, Subgroup.card_subtype, SQ.card_eq_multiplicity, hfacMS, hfacHS]
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hQM : Q ≤ M := hQH.trans (hHS.trans (sigmaCore_le M))
  have hHcentX : H ≤ centralizer ((zpowers x : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    intro h hh
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ((Subgroup.mem_centralizer_iff.1 hxcent) h hh).symm
  have hQZ : Q ≤ normalizer (K : Set G) ⊓ M := by
    rw [← hZeq]
    exact le_inf ((hQH.trans hHcentX).trans (centralizer_le_normalizer _)) hQM
  have hAZ : A ≤ normalizer (K : Set G) ⊓ M := hdir.2.1
  have hKcentA : K ≤ centralizer (A : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hdir.2.2.2.2
  have hZnorm : normalizer (K : Set G) ⊓ M ≤ normalizer (A : Set G) := by
    rw [← hdir.2.2.1]
    exact sup_le (hKcentA.trans (centralizer_le_normalizer _)) Subgroup.le_normalizer
  have hsd : FreeCore.IsInternalSemidirectProduct (normalizer (K : Set G) ⊓ M) A K :=
    ⟨by rw [sup_comm]; exact hdir.2.2.1, hZnorm,
      disjoint_iff.2 (by rw [inf_comm]; exact hdir.2.2.2.1)⟩
  have hAsub : Nat.card ↥(A.subgroupOf (normalizer (K : Set G) ⊓ M)) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv
  have hindex : (A.subgroupOf (normalizer (K : Set G) ⊓ M)).index = Nat.card ↥K := by
    have h := Subgroup.card_mul_index (A.subgroupOf (normalizer (K : Set G) ⊓ M))
    rw [hAsub, hsd.natCard_eq_mul] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  have hAHall : IsHallPiSubgroup (sigmaPrimes M)
      (A.subgroupOf (normalizer (K : Set G) ⊓ M)) := by
    refine isHallPiSubgroup_iff.2 ⟨fun s hs => ?_, fun s hs => ?_⟩
    · rw [hAsub] at hs
      exact isPiSubgroup_iff.1 ((isPiSubgroup_sigmaCore M).of_le (hAdef ▸ inf_le_left)) s hs
    · rw [hindex] at hs
      exact fun hsσ => (disjoint_kappaPrimes_sigmaPrimes M).ne_of_mem (hKHall.2.1 s hs) hsσ rfl
  have hQσ : IsPiSubgroup (sigmaPrimes M) Q := isPiSubgroup_of_natCard_eq_pow hqp hQcard hqσ
  have hQA : Q ≤ A := le_of_isHallPiSubgroup_subgroupOf hAZ hZnorm hAHall hQZ hQσ
  have hqQ : q ∣ Nat.card ↥Q := by
    rw [hQcard, hfacMS, hfacHS]
    exact dvd_pow_self q (Nat.Prime.factorization_pos_of_dvd hqp Nat.card_pos.ne'
      (Nat.dvd_of_mem_primeFactors hq)).ne'
  have hqA : q ∣ Nat.card ↥A := hqQ.trans (Subgroup.card_dvd_of_le hQA)
  exact ((FNI_kappa_fixed_prime_centralizer_and_sylow_uniqueness h₁ h₃ h₄
    G M K A (K ⊔ A) hsetup).2.2 q Q hqp hqA ⟨hQM, hQcard⟩).2 hQA

end

end CFSG.FeitThompson.Proofs

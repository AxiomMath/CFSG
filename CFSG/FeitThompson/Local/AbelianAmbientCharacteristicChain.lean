module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.AbelianAmbientTauTwoFitting
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.ControlledPlaneCentralizersPrimeCore
import CFSG.FeitThompson.Local.SplitKernelRemovalExponentAbelianSylow
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Foundations.SylowNormalizerSelfNormalizing
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isCyclic_of_isHallSubgroup {X : Type*} [Group X] [Finite X] [Group.IsSolvable X]
    {π : Set ℕ} {H K : Subgroup X} (hH : IsHallSubgroup π H) (hK : IsHallSubgroup π K)
    (hcyc : IsCyclic ↥H) : IsCyclic ↥K := by
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isHallSubgroup hH hK
  have e := H.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  rw [show (MulAut.conj g).toMonoidHom = ((MulAut.conj g : X ≃* X) : X →* X) from rfl, hg] at e
  exact (MulEquiv.isCyclic e).1 hcyc

theorem isHallSubgroup_subgroupOf_of_le {X : Type*} [Group X] [Finite X] {π : Set ℕ}
    {H K L : Subgroup X} (hHK : H ≤ K) (hKL : K ≤ L)
    (h : IsHallSubgroup π (H.subgroupOf L)) : IsHallSubgroup π (H.subgroupOf K) where
  natCard := by
    rw [natCard_subgroupOf hHK, ← natCard_subgroupOf (hHK.trans hKL)]
    exact h.natCard
  index := by
    refine h.index.of_dvd ?_ Subgroup.index_ne_zero_of_finite
    change H.relIndex K ∣ H.relIndex L
    exact ⟨K.relIndex L, (Subgroup.relIndex_mul_relIndex H K L hHK hKL).symm⟩

theorem isMulCommutative_sup {X : Type*} [Group X] {H K : Subgroup X}
    (hH : IsMulCommutative ↥H) (hK : IsMulCommutative ↥K)
    (hcomm : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) : IsMulCommutative ↥(H ⊔ K) := by
  have := hH
  have := hK
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer H)
      fun y hy => mem_centralizer_iff.2 fun x hx => hcomm x hx y hy
  · rw [Subgroup.le_centralizer_iff]
    exact sup_le (fun x hx => mem_centralizer_iff.2 fun y hy => (hcomm x hx y hy).symm)
      (Subgroup.le_centralizer K)

theorem mul_comm_of_isHallSubgroup_of_isNilpotent [Finite G] {π : Set ℕ} {F Y : Subgroup G}
    (hnil : Group.IsNilpotent ↥F) (hYF : Y ≤ F) (hY : IsHallSubgroup π (Y.subgroupOf F))
    (hYab : IsMulCommutative ↥Y) : ∀ x ∈ F, ∀ y ∈ Y, x * y = y * x := by
  have := hnil
  have : IsMulCommutative ↥(Y.subgroupOf F) :=
    isMulCommutative_subgroupOf_of_isMulCommutative hYab
  have heq : Y.subgroupOf F = sylowPiPart π ↥F := hY.eq_sylowPiPart
  have hcent : centralizer ((Y.subgroupOf F : Subgroup ↥F) : Set ↥F) = ⊤ := by
    refine top_le_iff.1 ?_
    rw [← sylowPiPart_sup_compl π ↥F]
    refine sup_le ?_ ?_
    · rw [← heq]; exact Subgroup.le_centralizer _
    · rw [heq]
      exact Subgroup.le_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (commutator_sylowPiPart_compl π ↥F))
  intro x hx y hy
  have hxc : (⟨x, hx⟩ : ↥F) ∈ centralizer ((Y.subgroupOf F : Subgroup ↥F) : Set ↥F) := by
    rw [hcent]; exact mem_top _
  exact (congrArg Subtype.val
    (mem_centralizer_iff.1 hxc ⟨y, hYF hy⟩ (by simpa [mem_subgroupOf] using hy))).symm

theorem characteristic_subgroupOf_of_eq_pTorsion {p : ℕ} {A Q : Subgroup G}
    (hA : (A : Set G) = {x ∈ (Q : Set G) | x ^ p = 1}) : (A.subgroupOf Q).Characteristic := by
  have hmem : ∀ x : ↥Q, x ∈ A.subgroupOf Q ↔ x ^ p = 1 := by
    intro x
    rw [mem_subgroupOf, ← SetLike.mem_coe, hA]
    refine ⟨fun h => Subtype.ext (by simpa using h.2), fun h => ⟨x.2, ?_⟩⟩
    have := congrArg (Subtype.val (p := fun z => z ∈ Q)) h
    simpa using this
  refine Subgroup.characteristic_iff_map_le.2 fun φ => ?_
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, hmem] at hx
  rw [hmem, ← map_pow, hx, map_one]

theorem isHallSubgroup_singleton_subgroupOf {X Q : Subgroup G} [Finite G] {p : ℕ} [Fact p.Prime]
    (hQX : Q ≤ X) (hQ : Nat.card ↥Q = p ^ (Nat.card G).factorization p) :
    IsHallSubgroup ({p} : Set ℕ) (Q.subgroupOf X) := by
  have hc : Nat.card ↥(Q.subgroupOf X) = p ^ (Nat.card ↥X).factorization p :=
    natCard_subgroupOf_eq_pow_factorization hQ hQX
  have h := isHallSubgroup_sylow (Sylow.ofCard (Q.subgroupOf X) hc)
  rwa [Sylow.coe_ofCard] at h

theorem notMem_tau3Primes_of_mem_tauTwoPrimes {M : Subgroup G} {q : ℕ}
    (h : q ∈ tauTwoPrimes M) : q ∉ tau3Primes M := by
  intro h3
  have h2 := (mem_tauTwoPrimes_iff.1 h).2.2
  have := (mem_tau3Primes_iff.1 h3).2.2.2.1
  omega

theorem le_of_isHallPiSubgroup_normal_subgroupOf [Finite G] {π : Set ℕ} {E Y Q : Subgroup G}
    (hn : (Y.subgroupOf E).Normal) (hY : IsHallPiSubgroup π (Y.subgroupOf E))
    (hQE : Q ≤ E) (hQ : IsPiSubgroup π Q) : Q ≤ Y := by
  have := hn
  have hQ' : IsPiSubgroup π (Q.subgroupOf E) := by
    rw [isPiSubgroup_iff, natCard_subgroupOf hQE]
    exact isPiSubgroup_iff.1 hQ
  have hle := hY.le_of_isPiSubgroup hQ'
  intro x hx
  have hmem : (⟨x, hQE hx⟩ : ↥E) ∈ Q.subgroupOf E := by simpa [mem_subgroupOf] using hx
  simpa [mem_subgroupOf] using hle hmem

theorem FBG_abelian_ambient_characteristic_chain
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_tau_two_full_central_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_global_sylow_normalizer_derived.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_abelian_ambient_characteristic_chain.{u} := by
  intro G _ _ hG M p A E P E₁ E₂ E₃ K hsetup hdec
  have hodd := hG.odd_natCard
  have hsimple := hG.isSimpleGroup
  have hna := hG.not_isMulCommutative
  have hsolv := hG.isSolvable
  have hGosm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G := ⟨hodd, hsimple, hna, hsolv⟩
  obtain ⟨hMc, hp, hpσ, hAM, hplane, hEM, hsd, hAE, hPab, ⟨S, hS⟩, hAP⟩ := id hsetup
  have hfp : Fact p.Prime := ⟨hp⟩
  have hosp : _root_.CFSG.FeitThompson.IsOutsideSigmaPlane p M A := ⟨hMc, hp, hpσ, hAM, hplane⟩
  have hsc : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hMc, hsd⟩
  have hPcardG : Nat.card ↥P = p ^ (Nat.card G).factorization p := by
    rw [← hS]; exact S.card_eq_multiplicity
  have hallab : ∀ R : Sylow p G, IsMulCommutative ↥(R : Subgroup G) := fun R =>
    isMulCommutative_of_natCard_eq_pow_factorization hPab hPcardG R.card_eq_multiplicity
  obtain ⟨hrank, -, hsylP4, -⟩ := h₄ G hGosm p M A hosp
  have hpτ₂ : p ∈ tauTwoPrimes M := mem_tauTwoPrimes_iff.2 ⟨hp, hpσ, hrank⟩
  have hEne : E ≠ ⊤ := fun h => hMc.1 (top_le_iff.1 (h ▸ hEM))
  have hEsolv : Group.IsSolvable ↥E := hsolv E hEne
  obtain ⟨-, -, -, -, -, hPZF⟩ :=
    FBG_abelian_ambient_tau_two_fitting h₁ h₃ h₄ h₅ G hG M p A E P hsetup
  have hPF : P ≤ mixedFitting E := hPZF.trans (centreIn_le _)
  have hPE : P ≤ E := hPF.trans (mixedFitting_le E)
  obtain ⟨-, hE₂ab, hn₂, -⟩ := by
    letI : Fintype G := Fintype.ofFinite G
    exact h₂ G ⟨hodd, hsimple, hna, hsolv⟩ M hMc E hsd p hpτ₂ hallab E₂
      ⟨hdec.le_E_E₂, hdec.hall_E₂⟩
  have hn₃ : (E₃.subgroupOf E).Normal := hdec.semidirect_outer.normal_subgroupOf
  obtain ⟨F₁, F₂, F₃, hsplit, -⟩ := FNI_sigma_complement_three_factors h₁ G hGosm M E hsc
  have hcyc₁ : IsCyclic ↥E₁ := by
    refine (MulEquiv.isCyclic (subgroupOfEquivOfLe hdec.le_E_E₁)).1 ?_
    refine isCyclic_of_isHallSubgroup (isHallSubgroup_iff_isHallPiSubgroup.2 hsplit.isHall_E₁)
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₁) ?_
    exact (MulEquiv.isCyclic (subgroupOfEquivOfLe hsplit.le_E₁)).2 hsplit.isCyclic_E₁
  have hcyc₃ : IsCyclic ↥E₃ := by
    refine (MulEquiv.isCyclic (subgroupOfEquivOfLe hdec.le_E_E₃)).1 ?_
    refine isCyclic_of_isHallSubgroup (isHallSubgroup_iff_isHallPiSubgroup.2 hsplit.isHall_E₃)
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₃) ?_
    exact (MulEquiv.isCyclic (subgroupOfEquivOfLe hsplit.le_E₃)).2 hsplit.isCyclic_E₃
  have hE₃ab : IsMulCommutative ↥E₃ := hcyc₃.isMulCommutative
  have hcop : ∀ q ∈ tauTwoPrimes M, q ∉ tau3Primes M :=
    fun _ hq => notMem_tau3Primes_of_mem_tauTwoPrimes hq
  have hcomm₂₃ : ∀ x ∈ E₂, ∀ y ∈ E₃, x * y = y * x := by
    have hc := (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₂).coprime_natCard
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₃) hcop
    have hcm := Subgroup.commute_of_normal_of_disjoint _ _ hn₂ hn₃
      (Subgroup.disjoint_of_coprime_natCard hc)
    intro x hx y hy
    exact congrArg Subtype.val (hcm ⟨x, hdec.le_E_E₂ hx⟩ ⟨y, hdec.le_E_E₃ hy⟩
      (by simpa [mem_subgroupOf] using hx) (by simpa [mem_subgroupOf] using hy))
  have hKab : IsMulCommutative ↥K := by
    rw [hdec.K_eq]; exact isMulCommutative_sup hE₂ab hE₃ab hcomm₂₃
  have hKE : K ≤ E := by rw [hdec.K_eq]; exact sup_le hdec.le_E_E₂ hdec.le_E_E₃
  have hKsub : K.subgroupOf E = E₂.subgroupOf E ⊔ E₃.subgroupOf E := by
    rw [hdec.K_eq, Subgroup.subgroupOf_sup hdec.le_E_E₂ hdec.le_E_E₃]
  have hnK : (K.subgroupOf E).Normal := by
    rw [hKsub]; exact Subgroup.sup_normal _ _
  have hKhall : IsHallSubgroup (tauTwoPrimes M ∪ tau3Primes M) (K.subgroupOf E) := by
    rw [hKsub]
    exact (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₂).sup
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₃) hcop
  have hKnil : Group.IsNilpotent ↥K := by
    have := hKab; exact isNilpotent_of_isMulCommutative ↥K
  have hKF : K ≤ mixedFitting E := by
    rw [mixedFitting_eq]; exact le_map_fittingRaw_subtype hKE hnK hKnil
  have hFnil : Group.IsNilpotent ↥(mixedFitting E) := isNilpotent_mixedFitting E
  have hKhallF : IsHallSubgroup (tauTwoPrimes M ∪ tau3Primes M) (K.subgroupOf (mixedFitting E)) :=
    isHallSubgroup_subgroupOf_of_le hKF (mixedFitting_le E) hKhall
  have hcommF := mul_comm_of_isHallSubgroup_of_isNilpotent hFnil hKF hKhallF hKab
  have hKZ : K ≤ centreIn (mixedFitting E) := by
    rw [centreIn_eq]
    refine le_inf hKF fun y hy => ?_
    rw [mem_centralizer_iff]
    exact fun x hx => hcommF x hx y hy
  have hPpi : IsPiSubgroup (tauTwoPrimes M) P :=
    ((isPiSubgroup_singleton_iff hp P).2 (IsPGroup.of_card hPcardG)).mono
      (Set.singleton_subset_iff.2 hpτ₂)
  have hPE₂ : P ≤ E₂ :=
    le_of_isHallPiSubgroup_normal_subgroupOf hn₂ hdec.hall_E₂ hPE hPpi
  have hPM : P ≤ M := hPE.trans hEM
  have hAchar : (A.subgroupOf P).Characteristic := by
    have hPsylM : _root_.CFSG.FeitThompson.IsSylowIn p M P :=
      (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hPM).2
        (natCard_eq_pow_factorization_of_le hp hPM hPcardG)
    exact characteristic_subgroupOf_of_eq_pTorsion ((hsylP4 P hPsylM).2 hAP).1
  have hPchar : (P.subgroupOf E₂).Characteristic := by
    have := hE₂ab
    have : Group.IsNilpotent ↥E₂ := isNilpotent_of_isMulCommutative ↥E₂
    exact (isHallSubgroup_singleton_subgroupOf hPE₂ hPcardG).characteristic
  have hE₂char : (E₂.subgroupOf K).Characteristic := by
    have := hKnil
    refine IsHallSubgroup.characteristic (π := tauTwoPrimes M) ?_
    exact isHallSubgroup_subgroupOf_of_le (hdec.K_eq ▸ le_sup_left) hKE
      (isHallSubgroup_iff_isHallPiSubgroup.2 hdec.hall_E₂)
  have hKchar : (K.subgroupOf (mixedFitting E)).Characteristic := by
    have := hFnil
    exact hKhallF.characteristic
  exact ⟨hcyc₁, hcyc₃, hKab, hnK, hKZ, hAP, hPE₂, hdec.K_eq ▸ le_sup_left, hKF, hAchar, hPchar,
    hE₂char, hKchar⟩

end

end CFSG.FeitThompson.Proofs

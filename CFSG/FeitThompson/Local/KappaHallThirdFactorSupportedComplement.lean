module

public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.KappaPrimeLineFixedEquivalence
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.KappaPositiveMultipleCoreTrivialResidual

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type*} [Group G]

theorem cent_eq_centralizerIn (X Y : Subgroup G) :
    Prep03.cent X (Y : Set G) = Prep05.centralizerIn X Y := (rfl)

theorem isHallPiSubgroup_subgroupOf_of_isHallPiOf {π : Set ℕ} {Y X : Subgroup G}
    (h : Prep03.IsHallPiOf π Y X) : IsHallPiSubgroup π (Y.subgroupOf X) := by
  refine ⟨isPiSubgroup_iff.2 fun r hr => h.2.1 r ?_, fun r hr => h.2.2 r ?_⟩
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv] at hr
  · rwa [show (Y.subgroupOf X).index = Y.relIndex X from rfl] at hr

theorem le_of_isHallPiOf_of_le_normalizer [Finite G] {π : Set ℕ} {X H Y : Subgroup G}
    (hH : Prep03.IsHallPiOf π H X) (hnorm : X ≤ normalizer (H : Set G)) (hYX : Y ≤ X)
    (hY : ∀ r ∈ (Nat.card ↥Y).primeFactors, r ∈ π) : Y ≤ H := by
  have hnormal : (H.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH.1).2 hnorm
  have hpi : IsPiSubgroup π (Y.subgroupOf X) := by
    refine isPiSubgroup_iff.2 fun r hr => hY r ?_
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv] at hr
  have hle := (isHallPiSubgroup_subgroupOf_of_isHallPiOf hH).le_of_isPiSubgroup hpi
  have := Subgroup.map_mono (f := X.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le hYX, Subgroup.map_subgroupOf_eq_of_le hH.1] at this

theorem isTauFactorization_of_isThreeHallSetup [Fintype G] {M E E₁ E₂ E₃ : Subgroup G}
    (h : Prep03.IsThreeHallSetup G M E E₁ E₂ E₃) : Prep05.IsTauFactorization M E E₁ E₂ E₃ where
  isSigmaComplement := ⟨h.isCoatom, isInternalSemidirectProduct_of_isSemidirect h.decomp⟩
  le_E₁ := h.isHall_E₁.1
  le_E₂ := h.isHall_E₂.1
  le_E₃ := h.isHall_E₃.1
  hall_E₁ := isHallPiSubgroup_subgroupOf_of_isHallPiOf h.isHall_E₁
  hall_E₂ := isHallPiSubgroup_subgroupOf_of_isHallPiOf h.isHall_E₂
  hall_E₃ := isHallPiSubgroup_subgroupOf_of_isHallPiOf h.isHall_E₃
  semidirect_E := isInternalSemidirectProduct_of_isSemidirect h.decomp_outer
  semidirect_E₂₁ := isInternalSemidirectProduct_of_isSemidirect h.decomp_inner
  isCyclic_E₁ := h.isCyclic_E₁
  isCyclic_E₃ := h.isCyclic_E₃
  le_commutator_E₃ := h.le_derived_E₃
  normalizes_E₂E₃ := h.normal_E₂E₃
  centralizer_E₃ := h.cent_E₃

theorem exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one [Finite G] {q : ℕ}
    (M : Subgroup G) (hq : q.Prime) (hodd : Odd q) (hr : elementaryAbelianPRank q ↥M ≤ 1) :
    ∃ S : Sylow q ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨S⟩ : Nonempty (Sylow q ↥M) := inferInstance
  exact ⟨S, (isCyclic_map_subtype_iff _).2 ((forall_isCyclic_sylow_iff hq hodd).2 hr S)⟩

theorem FNI_kappa_third_supported_complement_action
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FNI_tau13_nonfree_third_factor_structure.{u}) :
    Statements.FNI_kappa_third_supported_complement_action.{u} := by
  intro G _ _ M E E₁ E₂ E₃ K hsetup hK hKE hp
  obtain ⟨p, ⟨hpκ, hpτ₃⟩, hpdvd⟩ := hp
  have hpp : p.Prime := prime_of_mem_kappaPrimes hpκ
  have hKM : K ≤ M := hK.1
  have hEM : E ≤ M := hsetup.decomp.2.1
  have hMG : Nat.card ↥M ∣ Nat.card G := Subgroup.card_subgroup_dvd_card M
  have hoddG : Odd (Nat.card G) := hsetup.ambient.odd_natCard
  obtain ⟨x, hxK, hxo⟩ := exists_mem_orderOf_eq_of_dvd hpp hpdvd
  have hPcard : Nat.card ↥(zpowers x) = p := by rw [Nat.card_zpowers, hxo]
  have hPK : zpowers x ≤ K := zpowers_le.2 hxK
  have hPM : zpowers x ≤ M := hPK.trans hKM
  have hcycp : ∃ S : Sylow p ↥M, IsCyclic ((S : Subgroup ↥M).map M.subtype : Subgroup G) := by
    obtain ⟨-, -, -, S, hS, -⟩ := mem_kappaPrimes_iff.1 hpκ
    exact ⟨S, hS⟩
  have hPne : sigmaCore M ⊓ centralizer ((zpowers x : Subgroup G) : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_mem_kappaPrimes hpp hcycp hpκ hPM hPcard
  have hPE₃ : zpowers x ≤ E₃ := by
    refine le_of_isHallPiOf_of_le_normalizer hsetup.isHall_E₃
      hsetup.decomp_outer.2.2.1 (hPK.trans hKE) ?_
    intro r hr
    rw [hPcard, hpp.primeFactors, Finset.mem_singleton] at hr
    exact hr ▸ hpτ₃
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    exact hpp.one_lt.ne hxo
  have hPbot : (zpowers x : Subgroup G) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.1 (h ▸ mem_zpowers x))
  have hamb : Prep05.IsMinimalSimpleOdd G :=
    ⟨hsetup.ambient.odd_natCard, hsetup.ambient.isSimpleGroup,
      hsetup.ambient.not_isMulCommutative, hsetup.ambient.forall_isSolvable⟩
  obtain ⟨hE₂, hE₁, -, hnormal, hcent⟩ :=
    h₂ G hamb M E E₁ E₂ E₃ (isTauFactorization_of_isThreeHallSetup hsetup)
      ⟨x, hPE₃ (mem_zpowers x), hx1, hPne⟩
  have hCE : Prep05.centralizerIn (sigmaCore M) E ≠ ⊥ := by
    rw [← hcent _ (hPE₃.trans hsetup.isHall_E₃.1) hPbot]
    exact hPne
  obtain ⟨hπE, hrank, -⟩ := FNI_sigma_complement_prime_data h₁ G
    ⟨hsetup.ambient.odd_natCard, hsetup.ambient.isSimpleGroup,
      hsetup.ambient.not_isMulCommutative, hsetup.ambient.forall_isSolvable⟩
    M E ⟨hsetup.isCoatom, isInternalSemidirectProduct_of_isSemidirect hsetup.decomp⟩
  have hnotτ₂ : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∉ tauTwoPrimes M := by
    intro r hr
    refine hsetup.isHall_E₂.2.2 r ?_
    rwa [hE₂, Subgroup.relIndex_bot_left]
  have hEκ : ∀ r ∈ (Nat.card ↥E).primeFactors, r ∈ kappaPrimes M := by
    intro r hr
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hrE : r ∣ Nat.card ↥E := Nat.dvd_of_mem_primeFactors hr
    have hmem : r ∈ CFSG.FeitThompson.primeDivisorsOf ↥E := ⟨hrp, hrE⟩
    have hmem' := hπE ▸ hmem
    have hrM : r ∣ Nat.card ↥M := hmem'.1.2
    have hrσ : r ∉ sigmaPrimes M := hmem'.2
    obtain ⟨-, hr2⟩ := hrank r hmem
    have hr1 : elementaryAbelianPRank r ↥M ≤ 1 := by
      rcases Nat.lt_or_ge (elementaryAbelianPRank r ↥M) 2 with h | h
      · omega
      · exact absurd (mem_tauTwoPrimes_iff.2 ⟨hrp, hrσ, by omega⟩) (hnotτ₂ r hr)
    have hodd : Odd r := Odd.of_dvd_nat hoddG (hrM.trans hMG)
    have hcyc := exists_isCyclic_sylow_of_elementaryAbelianPRank_le_one M hrp hodd hr1
    obtain ⟨y, hyE, hyo⟩ := exists_mem_orderOf_eq_of_dvd hrp hrE
    have hQcard : Nat.card ↥(zpowers y) = r := by rw [Nat.card_zpowers, hyo]
    have hy1 : y ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hyo
      exact hrp.one_lt.ne hyo
    have hQbot : (zpowers y : Subgroup G) ≠ ⊥ := fun h =>
      hy1 (Subgroup.mem_bot.1 (h ▸ mem_zpowers y))
    have hQE : (zpowers y : Subgroup G) ≤ E := zpowers_le.2 hyE
    refine mem_kappaPrimes_of_inf_centralizer_ne_bot hrp hrσ hcyc (hQE.trans hEM) hQcard ?_
    rw [show sigmaCore M ⊓ centralizer ((zpowers y : Subgroup G) : Set G)
        = Prep05.centralizerIn (sigmaCore M) (zpowers y) from rfl, hcent _ hQE hQbot]
    exact hCE
  have hKE' : K = E := by
    have hone : K.relIndex E = 1 := by
      by_contra hne
      have hne0 : K.relIndex E ≠ 0 :=
        show (K.subgroupOf E).index ≠ 0 from Subgroup.index_ne_zero_of_finite
      obtain ⟨r, hr⟩ := Nat.nonempty_primeFactors.2 (by omega : 1 < K.relIndex E)
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrd : r ∣ K.relIndex E := Nat.dvd_of_mem_primeFactors hr
      have hrE : r ∣ Nat.card ↥E := hrd.trans (Subgroup.relIndex_dvd_card _ _)
      have hrM : r ∣ K.relIndex M := by
        rw [← Subgroup.relIndex_mul_relIndex K E M hKE hEM]
        exact hrd.mul_right _
      refine hK.2.2 r (Nat.mem_primeFactors.2 ⟨hrp, hrM, ?_⟩)
        (hEκ r (Nat.mem_primeFactors.2 ⟨hrp, hrE, Nat.card_pos.ne'⟩))
      exact show (K.subgroupOf M).index ≠ 0 from Subgroup.index_ne_zero_of_finite
    exact le_antisymm hKE (Subgroup.relIndex_eq_one.1 hone)
  subst hKE'
  refine ⟨rfl, hE₂, hE₁, fun X hXK hX => hnormal X hXK hX, ?_, fun X hXK hX => ?_⟩
  · rw [cent_eq_centralizerIn]
    exact hCE
  · rw [cent_eq_centralizerIn, cent_eq_centralizerIn, hcent X hXK hX]

end

end CFSG.FeitThompson.Proofs

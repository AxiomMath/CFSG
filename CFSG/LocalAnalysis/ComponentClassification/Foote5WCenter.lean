module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76RankOneClassSurvive
public import CFSG.LocalAnalysis.ComponentClassification.Foote5SolForward

public section

namespace CFSG.ComponentClassification.Foote5.SolMax

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76

variable {G : Type} [Group G] [Finite G]

theorem exists_involution_mem_coreActionKernel_of_center_ne_bot {R : Subgroup G}
    (hZ : center (↥R ⧸ pPrimeCore 2 ↥R) ≠ ⊥) :
    ∃ u ∈ R, orderOf u = 2 ∧ u ∈ coreActionKernel R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := center (↥R ⧸ pPrimeCore 2 ↥R) with hZdef
  have h2 : 2 ∣ Nat.card Z := by
    rcases (isPGroup_center_quotient_pPrimeCore ↥R).card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hZ
    · exact h
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hq' : orderOf (q : ↥R ⧸ pPrimeCore 2 ↥R) = 2 := (Subgroup.orderOf_coe q).trans hq
  have hq2 : (q : ↥R ⧸ pPrimeCore 2 ↥R) ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (q : ↥R ⧸ pPrimeCore 2 ↥R)
    rwa [hq'] at h
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (q : ↥R ⧸ pPrimeCore 2 ↥R)
  have hr2 : r ^ 2 ∈ pPrimeCore 2 ↥R := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hr, hq2]
  set m := orderOf (r ^ 2) with hm
  have hmodd : Odd m := by
    have h1 : orderOf (⟨r ^ 2, hr2⟩ : ↥(pPrimeCore 2 ↥R)) ∣ Nat.card ↥(pPrimeCore 2 ↥R) :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).of_dvd_nat h1
  set u := r ^ m with hu
  have hu2 : u ^ 2 = 1 := by
    rw [hu, ← pow_mul, mul_comm, pow_mul, hm, pow_orderOf_eq_one]
  have humk : (QuotientGroup.mk u : ↥R ⧸ pPrimeCore 2 ↥R) = q := by
    obtain ⟨j, hj⟩ := hmodd
    rw [hu, QuotientGroup.mk_pow, hr, hj, pow_succ, pow_mul, hq2, one_pow, one_mul]
  have hu1 : u ≠ 1 := by
    intro h
    have h1 : (q : ↥R ⧸ pPrimeCore 2 ↥R) = 1 := by rw [← humk, h, QuotientGroup.mk_one]
    rw [h1, orderOf_one] at hq'
    exact absurd hq' (by norm_num)
  have huo : orderOf u = 2 := orderOf_eq_prime hu2 hu1
  refine ⟨u, u.2, by rw [Subgroup.orderOf_coe]; exact huo, ?_⟩
  have huZ : (QuotientGroup.mk u : ↥R ⧸ pPrimeCore 2 ↥R) ∈ Z := by rw [humk]; exact q.2
  refine mem_coreActionKernel.mpr ⟨le_normalizer u.2, fun j hj => ?_⟩
  have h1 := (FooteLit.mk_mem_center_iff _ u).mp huZ ⟨j, hj⟩
  have h2 := (mem_pPrimeCore_iff_mem_oddCoreIn _).mp (inv_mem h1)
  have e : (((((⟨j, hj⟩ : ↥R) * u)⁻¹ * (u * ⟨j, hj⟩))⁻¹ : ↥R) : G) =
      j⁻¹ * (u : G)⁻¹ * j * (u : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h2
  exact h2

theorem center_eq_bot_of_mirrorGood {J K : Subgroup G} (hML : GSMirrorMaximal J)
    (hK : MirrorGood J K)
    (hZ : ∀ (w : G) (V : Subgroup G), orderOf w = 2 →
      IsTwoComponentIn V (centralizer ({w} : Set G)) → GSMirrorReach J V →
      center (↥V ⧸ pPrimeCore 2 ↥V) = ⊥) :
    center (↥K ⧸ pPrimeCore 2 ↥K) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKq, ⟨eK⟩, w, hw, hwK, hstar, hcls⟩ := hK
  have hKZ : Nat.card (↥K ⧸ Open.fusionZStar ↥K) = Nat.card (↥J ⧸ Open.fusionZStar ↥J) :=
    Nat.card_congr eK.toEquiv
  by_contra hZK
  set R := twoLayerIn (K ⊓ centralizer ({w} : Set G)) with hR
  obtain ⟨-, hRr, -, ⟨eR⟩⟩ := cover_facts hKq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq (isPGroup_zpowers_of_orderOf hw) (zpowers_le.mpr hwK))
  rw [centralizer_zpowers'] at hRr eR
  have hRq : IsQuasisimple (↥R ⧸ pPrimeCore 2 ↥R) := by
    rw [hR, hRr]
    exact LocalCores.isQuasisimple_of_mulEquiv eR.symm hKq
  have eRK : ↥R ⧸ pPrimeCore 2 ↥R ≃* ↥K ⧸ pPrimeCore 2 ↥K := by
    rw [hR, hRr]
    exact eR
  have hZR : center (↥R ⧸ pPrimeCore 2 ↥R) ≠ ⊥ := by
    intro hbot
    apply hZK
    rw [eq_bot_iff]
    intro x hx
    have h1 : eRK.symm x ∈ center (↥R ⧸ pPrimeCore 2 ↥R) := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      have h := congrArg eRK.symm (Subgroup.mem_center_iff.mp hx (eRK g))
      rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h
    rw [hbot, mem_bot] at h1
    rw [mem_bot]
    have h2 := congrArg eRK h1
    rwa [MulEquiv.apply_symm_apply, map_one] at h2
  obtain ⟨u, huR, hu, huC⟩ := exists_involution_mem_coreActionKernel_of_center_ne_bot hZR
  obtain ⟨hJc, -, -, ⟨eJ⟩⟩ := cover_facts hRq inf_le_left
    (inf_centralizer_sup_oddCoreIn_eq (isPGroup_zpowers_of_orderOf hu) (zpowers_le.mpr huC))
  rw [centralizer_zpowers'] at hJc eJ
  set J₀ := oddResidualIn (R ⊓ centralizer ({u} : Set G)) with hJ₀
  have hJ₀R : J₀ ≤ R := hJc.1.trans inf_le_left
  have hJ₀u : ∀ j ∈ J₀, j * u = u * j := fun j hj =>
    mem_centralizer_singleton_iff.mp (mem_inf.mp (hJc.1 hj)).2
  have huJ₀ : u ∈ J₀ := by
    rw [hJ₀]
    exact Subgroup.mem_closure_of_mem (show u ∈ {g : G | g ∈ R ⊓ centralizer ({u} : Set G) ∧
      ∃ k : ℕ, orderOf g = 2 ^ k} from
      ⟨mem_inf.mpr ⟨huR, mem_centralizer_singleton_iff.mpr rfl⟩, 1, by rw [pow_one]; exact hu⟩)
  have hJ₀res : oddResidualIn J₀ = J₀ := by
    rw [hJ₀]
    exact le_antisymm ((closure_le _).mpr fun _ hx => hx.1)
      ((closure_le _).mpr fun _ hx => subset_closure ⟨subset_closure hx, hx.2⟩)
  have hJ₀perf : ⁅J₀, J₀⁆ = J₀ := UnbalancedCorr.commutator_eq_of_isPComponent hJc.1 hJc.2
  have hJ₀q : IsQuasisimple (↥J₀ ⧸ pPrimeCore 2 ↥J₀) :=
    LocalCores.isQuasisimple_of_mulEquiv eJ.symm hRq
  have hJ₀card : Nat.card (↥J₀ ⧸ Open.fusionZStar ↥J₀) = Nat.card (↥K ⧸ Open.fusionZStar ↥K) :=
    Nat.card_congr (Sol78.fusionZStarQuotOfCore (eJ.trans eRK)).toEquiv
  have hmv : ∀ X : Subgroup G, ¬ J₀ ≤ coreActionKernel X → ¬ R ≤ coreActionKernel X :=
    fun X h hc => h (hJ₀R.trans hc)
  obtain ⟨X, hX, hXmv, hXZ⟩ := RankOneClass.exists_center_ne_bot_of_moves (hJ₀R.trans hstar)
    hJ₀perf hJ₀res hJ₀q huJ₀ hu hJ₀u fun X hX hXmv => le_of_eq (by
      rw [hJ₀card, hKZ, card_eq_of_reach hML (hcls X hX (hmv X hXmv))])
  exact hXZ (hZ w X hw hX (hcls X hX (hmv X hXmv)))

end CFSG.ComponentClassification.Foote5.SolMax

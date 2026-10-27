module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSocleCore
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.LyFive

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.LocalAnalysis.RankThreeUC.AGL81C (oPPrimeHull)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12 (oPrimeModPrimeComplement modPrimeComplement)
open CFSG.RankThreeEvenClassification.Helpers (primeComplementCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

private lemma card_oPrimeModPrimeComplement_G2_five
    {X : Type} [Group X] {X₁ : Subgroup X}
    (hT : CFSG.Blueprint.ChevalleyExceptionalModel
      (oPrimeModPrimeComplement 31 X₁) .G2 5 1) :
    Nat.card (oPrimeModPrimeComplement 31 X₁) = 5859000000 := by
  have hG2 : CFSG.Blueprint.UntwistedChevalleyModel
      (oPrimeModPrimeComplement 31 X₁) .G2 (5 ^ 1) := by
    simpa only [CFSG.Blueprint.ChevalleyExceptionalModel] using hT.2
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 hG2]
  unfold CFSG.Open.ordG2
  norm_num

theorem primeComplementCore_eq_bot_of_ly
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 5 31) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Ly)
    (hDK : D ≤ K)
    (hT : CFSG.Blueprint.ChevalleyExceptionalModel (oPrimeModPrimeComplement 31 X₁) .G2 5 1) :
    primeComplementCore (↥X₁) 31 = ⊥ := by
  classical
  obtain ⟨φ⟩ := hs
  have hcardK : Nat.card ↥K = 51765179004000000 :=
    (Nat.card_congr φ.toEquiv).trans CFSG.Sporadic.Ly.card_Ly
  have hsK : IsSimpleGroup ↥K :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Ly.fam_ly_simplicity.2.2 φ
  have hZ : Subgroup.center ↥K = ⊥ :=
    @SporCent.center_eq_bot_of_not_prime ↥K _ _ hsK (by rw [hcardK]; norm_num)
  have hO : Nat.card (Outer ↥K) ∣ 2 :=
    (CFSG.Sporadic.LySchreier.outer_order_divides_two ⟨φ⟩).1
  have hout5 : ¬ 5 ∣ Nat.card (Outer ↥K) := by
    intro h5
    have h1 : 5 ≤ Nat.card (Outer ↥K) := Nat.le_of_dvd Nat.card_pos h5
    have h2 : Nat.card (Outer ↥K) ≤ 2 := Nat.le_of_dvd (by norm_num) hO
    omega
  have hX₁K : X₁ ≤ K := h.lt.le.trans (sup_le le_rfl hDK)
  have hNnormal : (primeComplementCore (↥X₁) 31).Normal := inferInstance
  obtain ⟨Ebar, ⟨hcomm, hexp⟩, hEc, hC, -⟩ := h.exists_barE hZ hout5
  have hQcard : Nat.card (oPrimeModPrimeComplement 31 X₁) = 5859000000 :=
    card_oPrimeModPrimeComplement_G2_five hT
  have hQdvd : Nat.card (oPrimeModPrimeComplement 31 X₁) ∣
      Nat.card (↥X₁ ⧸ primeComplementCore (↥X₁) 31) :=
    Subgroup.card_subgroup_dvd_card
      (oPPrimeHull 31 (⊤ : Subgroup (modPrimeComplement 31 X₁)))
  have hX1card : Nat.card ↥X₁ =
      Nat.card (↥X₁ ⧸ primeComplementCore (↥X₁) 31) *
        Nat.card (primeComplementCore (↥X₁) 31) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (primeComplementCore (↥X₁) 31)
  have hmul : 5859000000 * Nat.card (primeComplementCore (↥X₁) 31) ∣ Nat.card ↥X₁ := by
    rw [hQcard] at hQdvd
    rw [hX1card]
    exact Nat.mul_dvd_mul_right hQdvd _
  have hkey : 5859000000 * Nat.card (primeComplementCore (↥X₁) 31) ∣
      51765179004000000 := by
    rw [← hcardK]
    exact hmul.trans (Subgroup.card_dvd_of_le hX₁K)
  have hNdvd : Nat.card (primeComplementCore (↥X₁) 31) ∣ 8835156 := by
    have h' : 5859000000 * Nat.card (primeComplementCore (↥X₁) 31) ∣
        5859000000 * 8835156 := by
      rw [show 5859000000 * 8835156 = 51765179004000000 by norm_num]
      exact hkey
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5859000000) h'
  have hN5 : ¬ 5 ∣ Nat.card (primeComplementCore (↥X₁) 31) := by
    intro h5
    exact absurd (h5.trans hNdvd) (by norm_num)
  let ι : ↥X₁ →* ↥K := Subgroup.inclusion hX₁K
  have hιinj : Function.Injective ι := Subgroup.inclusion_injective hX₁K
  let NK : Subgroup ↥K := (primeComplementCore (↥X₁) 31).map ι
  have hNKcard : Nat.card NK = Nat.card (primeComplementCore (↥X₁) 31) :=
    Subgroup.card_map_of_injective hιinj
  have hNK5 : ¬ 5 ∣ Nat.card NK := by
    rw [hNKcard]
    exact hN5
  have hsubconj : ∀ g ∈ X₁.subgroupOf K, ∀ y ∈ NK, g * y * g⁻¹ ∈ NK := by
    intro g hg y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    let x : ↥X₁ := ⟨g, Subgroup.mem_subgroupOf.mp hg⟩
    have hxg : ι x = g := rfl
    refine Subgroup.mem_map.mpr ⟨x * n * x⁻¹, hNnormal.conj_mem n hn x, ?_⟩
    rw [map_mul, map_mul, map_inv, hxg]
  have hEX : ∀ e ∈ Ebar, e ∈ X₁.subgroupOf K := by
    intro e he
    rcases eq_or_ne e 1 with h1 | h1
    · rw [h1]
      exact (X₁.subgroupOf K).one_mem
    · exact hC e he h1 (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hEN : Ebar ≤ Subgroup.normalizer (NK : Set ↥K) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hsubconj e (hEX e he) y
    · intro hy
      have h1 := hsubconj e⁻¹ ((X₁.subgroupOf K).inv_mem (hEX e he)) (e * y * e⁻¹) hy
      rwa [show e⁻¹ * (e * y * e⁻¹) * (e⁻¹)⁻¹ = y by group] at h1
  have hcen : ∀ e ∈ Ebar, e ≠ 1 →
      NK ⊓ Subgroup.centralizer ({e} : Set ↥K) = ⊥ := by
    intro e he he1
    set C : Subgroup ↥K := Subgroup.centralizer ({e} : Set ↥K)
    have heord : orderOf e = 5 :=
      @orderOf_eq_prime ↥K _ e 5 ⟨Nat.prime_five⟩ (hexp e he) he1
    have hcoreTriv : CFSG.Open.GLAPPrimeCoreOf 5 C = ⊥ :=
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_Ly_five
        ↥K ⟨φ⟩ e heord
    have hinle : NK ⊓ C ≤ CFSG.Open.GLAPPrimeCoreOf 5 C := by
      refine CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal
        inf_le_right ?_ ?_
      · intro g hg x hx
        exact ⟨hsubconj g (hC e he he1 hg) x hx.1,
          C.mul_mem (C.mul_mem hg hx.2) (C.inv_mem hg)⟩
      · refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 ?_
        intro h5
        exact hNK5 (h5.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hle : NK ⊓ C ≤ ⊥ := by
      rwa [hcoreTriv] at hinle
    exact le_bot_iff.mp hle
  have hNKbot : NK = ⊥ :=
    CFSG.Walter.eq_bot_of_forall_inf_centralizer_eq_bot_of_elementary
      Nat.prime_five hcomm hexp (le_of_eq hEc.symm) hEN hNK5 hcen
  have hmapbot : (primeComplementCore (↥X₁) 31).map ι = ⊥ := hNKbot
  exact (Subgroup.map_eq_bot_iff_of_injective (primeComplementCore (↥X₁) 31) hιinj).mp
    hmapbot

theorem socle_of_ly
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X}
    (h : ThreeNineHyp K E D X₁ 5 31) (hs : CFSG.Blueprint.NativeSporadic.IsSporadic ↥K .Ly)
    (hDK : D ≤ K)
    (hT : CFSG.Blueprint.ChevalleyExceptionalModel (oPrimeModPrimeComplement 31 X₁) .G2 5 1) :
    IsSimpleGroup ↥(oPPrimeHull 31 X₁) ∧
      Subgroup.centralizer (oPPrimeHull 31 X₁ : Set X) ⊓ K = ⊥ := by
  have hcore := primeComplementCore_eq_bot_of_ly h hs hDK hT
  have hsQ : IsSimpleGroup (oPrimeModPrimeComplement 31 X₁) :=
    (CFSG.LieType.Simplicity.fam_g2_simplicity _ 5 1 hT).2
  have hp : ¬ (Nat.card (oPrimeModPrimeComplement 31 X₁)).Prime := by
    rw [card_oPrimeModPrimeComplement_G2_five hT]
    norm_num
  exact h.socle_of_primeComplementCore_eq_bot hDK hcore hsQ hp

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

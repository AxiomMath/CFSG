module

public import CFSG.Goldschmidt.Steps.G37CoreTypeII
public import CFSG.Adapters.GeneralizedFitting

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter
open CFSG.Open (goldschmidtOddCore goldschmidtLayer)
open scoped commutatorElement

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

section Core

variable {M : Type} [Group M] [Finite M]

theorem oddFit_le_centralizer_of_le_centralizer {a : M} {X : Subgroup M}
    (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
    {L : Subgroup M} (hL : IsComponentOf L ⊤) (hLa : L ≤ Subgroup.centralizer ({a} : Set M)) :
    oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set M) := by
  have hLY : L ≤ Subgroup.normalizer (oddCoreOf (CFSG.fittingSubgroupOf X) : Set M) :=
    hLa.trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  rcases le_or_commutator_eq_bot_of_le_normalizer hL
      (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top).ge) hLY with h | h
  · exfalso
    have h2 : 2 ∣ Nat.card L := CFSG.Walter.IsQuasisimple.two_dvd_card hL.2.2
    have h3 := Subgroup.card_dvd_of_le h
    exact (Nat.not_even_iff_odd.mpr (odd_card_oddFit X)) (even_iff_two_dvd.mpr (h2.trans h3))
  · rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem le_centralizer_of_not_le_normalClosureIn {A : Subgroup M} {a : M} (haA : a ∈ A)
    {L : Subgroup M} (hL : IsComponentOf L ⊤) (hLK : ¬ L ≤ normalClosureIn ⊤ A) :
    L ≤ Subgroup.centralizer ({a} : Set M) := by
  rcases CFSG.Walter.isComponentOf_le_or_commutator_eq_bot hL le_top
      (Subgroup.normalizer_eq_top_iff.mpr (normalClosureIn_top_normal A)).ge with h | h
  · exact absurd h hLK
  · intro x hx
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp h1 a (le_normalClosureIn_top A haA)).symm

omit [Finite M] in
theorem le_centralizer_of_mem {H A : Subgroup M} (hS : IsSStarIn H A) {a : M} (haA : a ∈ A) :
    A ≤ Subgroup.centralizer ({a} : Set M) := by
  intro b hb
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hS.2.1.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩)

theorem mem_fstar_of_mem (h31 : S_G31) (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {a : M} (haA : a ∈ A) :
    a ∈ generalizedFittingSubgroupOf (⊤ : Subgroup M) :=
  normalClosureIn_le_fstar h31 hO hS (le_normalClosureIn_top A haA)

theorem eq_bot_of_le_centralizer_fstar (hO : goldschmidtOddCore M = ⊥) {Z : Subgroup M}
    (hZ : Odd (Nat.card Z))
    (hZC : Z ≤ Subgroup.centralizer (generalizedFittingSubgroupOf (⊤ : Subgroup M) : Set M)) :
    Z = ⊥ := by
  have hZF : Z ≤ CFSG.fittingSubgroupOf (⊤ : Subgroup M) :=
    (le_inf hZC (hZC.trans CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le)).trans
      centralizer_generalizedFitting_intersection_le_fittingSubgroupOf
  have h := inf_eq_bot_of_odd_of_isPGroup hZ (isPGroup_fitting hO)
  rwa [inf_eq_left.mpr hZF] at h

variable (h31 : S_G31) (h32Q : S_G32Q) (h33 : S_G33) (h34 : S_G34) (h35 : S_G35)
  (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
  (hE : CFSG.Open.IsElemAbelian 2 A) {a : M} (haA : a ∈ A) {X : Subgroup M}
  (hXa : Subgroup.centralizer ({a} : Set M) ≤ Subgroup.normalizer (X : Set M))
  (hXE : X = componentLayerOf X ⊔ oddCoreOf (CFSG.fittingSubgroupOf X))

include h31 h32Q h33 h35 hO hS hE haA hXa hXE

theorem component_of_not_le_centralizer {L : Subgroup M} (hL : IsComponentOf L ⊤)
    (hYL : ¬ oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set M)) :
    L ≤ normalClosureIn ⊤ A ∧ ¬ L ≤ Subgroup.centralizer ({a} : Set M) ∧ IsGoldTypeII L ∧
      IsGoldL2 L := by
  have hLa : ¬ L ≤ Subgroup.centralizer ({a} : Set M) := fun h =>
    hYL (oddFit_le_centralizer_of_le_centralizer hXa hL h)
  have hLK : L ≤ normalClosureIn ⊤ A := by
    by_contra h
    exact hLa (le_centralizer_of_not_le_normalClosureIn haA hL h)
  rcases isGoldType h31 hO hS hL hLK with hI | hII
  · exact absurd (typeI_oddFit h31 h32Q h33 hO hS haA hXa hXE hL hLK hI hLa) hYL
  · rcases hII.2 with hL2 | hJR
    · exact ⟨hLK, hLa, hII, hL2⟩
    · exact absurd (typeII_JR_oddFit h31 h35 hO hS hE haA hXa hXE hL hLK hII hLa hJR) hYL

include h34 in
theorem core_oddFit_component {L : Subgroup M} (hL : IsComponentOf L ⊤) {Y₀ : Subgroup M}
    (hY₀ : Y₀ ≤ oddCoreOf (CFSG.fittingSubgroupOf X))
    (hY₀L : ¬ Y₀ ≤ Subgroup.centralizer (L : Set M)) :
    L ≤ normalClosureIn ⊤ A ∧ IsGoldL2 L ∧ Y₀ ≤ L ⊔ Subgroup.centralizer (L : Set M) ∧
      (∃ y ∈ Y₀, Y₀ ≤ Subgroup.zpowers y ⊔ Subgroup.centralizer (L : Set M)) ∧
      ⁅A ⊓ L, Y₀⁆ ≠ ⊥ := by
  have hYL : ¬ oddCoreOf (CFSG.fittingSubgroupOf X) ≤ Subgroup.centralizer (L : Set M) :=
    fun h => hY₀L (hY₀.trans h)
  obtain ⟨hLK, hLa, hII, hL2⟩ :=
    component_of_not_le_centralizer h31 h32Q h33 h35 hO hS hE haA hXa hXE hL hYL
  obtain ⟨-, h2, h3⟩ := typeII_L2 h31 h34 h35 hO hS haA hXa hXE hL hLK hII hLa hL2
  exact ⟨hLK, hL2, hY₀.trans (typeII_oddFit_le_sup h31 h35 hO hS haA hXa hXE hL hLK hII hLa),
    h2 Y₀ hY₀, fun h => hY₀L (h3 Y₀ hY₀ h)⟩

include h34 in
theorem core_commutator_oddFit :
    ⁅oddCoreOf (CFSG.fittingSubgroupOf X), Subgroup.zpowers a⁆ = ⊥ := by
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have haY : a ∈ Subgroup.normalizer (Y : Set M) :=
    hXa.trans (normalizer_le_normalizer_oddFit X) (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hZY : ⁅Y, Subgroup.zpowers a⁆ ≤ Y :=
    CFSG.Walter.commutator_zpowers_le_of_mem_normalizer haY
  have ha2 : a ^ 2 = 1 := hE.2 a haA
  have hXF := le_centralizer_fitting hO (mem_fstar_of_mem h31 hO hS haA) hXa hXE
  have hC : generalizedFittingSubgroupOf (⊤ : Subgroup M) ≤
      Subgroup.centralizer ((⁅Y, Subgroup.zpowers a⁆ : Subgroup M) : Set M) := by
    refine sup_le ?_ (sSup_le fun L hL => ?_)
    · exact Subgroup.le_centralizer_iff.mp ((hZY.trans (oddFit_le X)).trans hXF)
    · apply Subgroup.le_centralizer_iff.mp
      rw [Subgroup.commutator_le]
      intro y hy b hb
      rcases eq_one_or_eq_of_mem_zpowers ha2 hb with rfl | rfl
      · rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
      by_cases hYL : Y ≤ Subgroup.centralizer (L : Set M)
      · rw [commutatorElement_def, show y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) by group]
        exact Subgroup.mul_mem _ (hYL hy)
          (hYL ((Subgroup.mem_normalizer_iff.mp haY y⁻¹).mp (Y.inv_mem hy)))
      · obtain ⟨hLK, hLa, hII, hL2⟩ :=
          component_of_not_le_centralizer h31 h32Q h33 h35 hO hS hE haA hXa hXE hL hYL
        exact (typeII_L2 h31 h34 h35 hO hS haA hXa hXE hL hLK hII hLa hL2).1 y hy
  exact eq_bot_of_le_centralizer_fstar hO
    ((odd_card_oddFit X).of_dvd_nat (Subgroup.card_dvd_of_le hZY))
    (Subgroup.le_centralizer_iff.mp hC)

include h34 in
theorem core_oddFit_le : oddCoreOf (CFSG.fittingSubgroupOf X) ≤ normalClosureIn ⊤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := oddCoreOf (CFSG.fittingSubgroupOf X) with hY
  have hXF := le_centralizer_fitting hO (mem_fstar_of_mem h31 hO hS haA) hXa hXE
  set Y₁ := Y ⊓ Subgroup.centralizer (A : Set M) with hY₁
  have hC : generalizedFittingSubgroupOf (⊤ : Subgroup M) ≤
      Subgroup.centralizer (Y₁ : Set M) := by
    refine sup_le ?_ (sSup_le fun L hL => ?_)
    · exact Subgroup.le_centralizer_iff.mp ((inf_le_left.trans (oddFit_le X)).trans hXF)
    · apply Subgroup.le_centralizer_iff.mp
      by_contra hY₁L
      apply (core_oddFit_component h31 h32Q h33 h34 h35 hO hS hE haA hXa hXE hL inf_le_left
        hY₁L).2.2.2.2
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_right.trans (Subgroup.centralizer_le inf_le_left))
  have hY₁0 : Y₁ = ⊥ := eq_bot_of_le_centralizer_fstar hO
    ((odd_card_oddFit X).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    (Subgroup.le_centralizer_iff.mp hC)
  have hAY : A ≤ Subgroup.normalizer (Y : Set M) :=
    (le_centralizer_of_mem hS haA).trans (hXa.trans (normalizer_le_normalizer_oddFit X))
  have hYs : Group.IsSolvable Y := by
    have := isNilpotent_oddFit X
    infer_instance
  have hA2 : IsPGroup 2 A := by
    obtain ⟨-, -, T, hT, hAT, -⟩ := hS
    exact hT.2.1.to_le hAT
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Y) := by
    obtain ⟨k, hk⟩ := hA2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr (odd_card_oddFit X))
  have h1 := CFSG.Walter.le_sup_commutator_of_coprime hAY hYs hcop
  rw [← hY₁, hY₁0, bot_sup_eq] at h1
  have hKn := normalClosureIn_top_normal A
  exact h1.trans ((Subgroup.commutator_mono le_rfl (le_normalClosureIn_top A)).trans
    (Subgroup.commutator_le_right Y _))

include h34 in
theorem core_component {K : Subgroup M} (hK : IsComponentOf K X) :
    ∃ L : Subgroup M, IsComponentOf L ⊤ ∧ K ≤ L ∧ (K = L ∨ (IsGoldL2 K ∧
      K ≤ Subgroup.centralizer ({a} : Set M) ∧ IsGoldJR L ∧ L ≤ normalClosureIn ⊤ A)) := by
  have hXF := le_centralizer_fitting hO (mem_fstar_of_mem h31 hO hS haA) hXa hXE
  obtain ⟨L, hL, hKL⟩ : ∃ L : Subgroup M, IsComponentOf L ⊤ ∧
      ¬ K ≤ Subgroup.centralizer (L : Set M) := by
    by_contra hne
    push Not at hne
    apply not_le_centralizer_self hK.2.2
    have hKC : K ≤ Subgroup.centralizer
        (generalizedFittingSubgroupOf (⊤ : Subgroup M) : Set M) := by
      apply Subgroup.le_centralizer_iff.mp
      exact sup_le (Subgroup.le_centralizer_iff.mp (hK.1.trans hXF))
        (sSup_le fun L hL => Subgroup.le_centralizer_iff.mp (hne L hL))
    exact hKC.trans (Subgroup.centralizer_le (hKC.trans CFSG.Adapters.centralizer_generalizedFittingSubgroupOf_top_le))
  have hKLne : ⁅K, L⁆ ≠ ⊥ := fun h => hKL (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  by_cases hLa : L ≤ Subgroup.centralizer ({a} : Set M)
  ·
    rcases le_or_commutator_eq_bot_of_le_normalizer hL
        (le_top.trans (Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_top).ge)
        (hLa.trans hXa) with h | h
    · have hKeq := eq_of_commutator_ne_bot hK (isComponentOf_of_le hL h le_top) hKLne
      exact ⟨L, hL, hKeq.le, Or.inl hKeq⟩
    · exact absurd (le_bot_iff.mp ((Subgroup.commutator_mono hK.1 le_rfl).trans
        ((Subgroup.commutator_comm X L).trans h).le)) hKLne
  have hLK : L ≤ normalClosureIn ⊤ A := by
    by_contra h
    exact hLa (le_centralizer_of_not_le_normalClosureIn haA hL h)
  rcases isGoldType h31 hO hS hL hLK with hI | hII
  · rcases typeI_component h31 h32Q h33 hO hS haA hXa hXE hL hLK hI hLa hK with h | h
    · exact ⟨L, hL, h.le, Or.inl h⟩
    · exact absurd h hKLne
  · by_cases hKL' : K ≤ L
    · rcases typeII_component_le h31 h34 hO hS hE haA hXa hXE hL hLK hII hLa hK hKL' with
        h | ⟨h1, h2, h3⟩
      · exact ⟨L, hL, hKL', Or.inl h⟩
      · exact ⟨L, hL, hKL', Or.inr ⟨h2, h1, h3, hLK⟩⟩
    · exact absurd (typeII_component_not_le h31 h35 hO hS haA hXa hXE hL hLK hII hLa hK hKL')
        hKLne

end Core

end CFSG.Goldschmidt.G37

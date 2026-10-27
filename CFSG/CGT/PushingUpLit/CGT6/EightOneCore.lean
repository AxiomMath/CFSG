module

public import CFSG.CGT.PushingUpLit.CGT6.SixThreeCore
public import CFSG.CGT.PushingUpLit.RouteB
public import CFSG.RankThree.PartOne.S12.Sec15Final
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.CGT.PushingUpLit.ThreeFromEightOne
public import CFSG.CGT.PushingUpLit.EightOneFinal
import CFSG.Foundations.KCoreClosure
public import CFSG.CGT.PushingUp.BenderBridge
public import CFSG.CGT.PushingUpLit.EightOneBlocks
public import CFSG.CGT.PushingUpLit.EightOneFinalSylow

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneFinal CFSG.CGT.PushingUpLit.ThreeFromEight
open CFSG.GroupTheory (conjugate_conjugate isSubnormal_subgroupOf_conjugate)
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open scoped commutatorElement

@[expose] def AschbacherEightOneK : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    (∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N) →
    ∀ X : Subgroup G, IsMaximalInClassXG X → ∀ N : Subgroup G,
      N ∈ maximalTwoLocalsContaining (X : Set G) → (X.subgroupOf N).IsSubnormal

section Proof

variable {G : Type} [Group G] [Finite G]

theorem existsBlockAbove_core (h6 : AschbacherSixThreeCore) {X N' : Subgroup G}
    (hK : CFSG.IsKGroup ↥N') (hN : IsCharacteristicP 2 ↥N') (hXN : InClassXGIn N' X)
    (hnot : ¬ (X.subgroupOf N').IsSubnormal) : ∃ L : Subgroup G, BlockAbove X N' L := by
  obtain ⟨L, hXL, hLN, hsub, hcl, harrow⟩ := h6.rel hK hN hXN
  exact ⟨L, hXL, hLN, hsub, hcl, harrow, fun hLX => hnot (hLX ▸ hsub)⟩

theorem isSubnormal_of_normalizer_le_core (h6 : AschbacherSixThreeCore)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hKG : ∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N)
    {X D N L S₀ P : Subgroup G} (hX : InClassX ↥X)
    (hgood : ∀ N' : Subgroup G, AnchoredWitness X D N' → InClassXGIn N' X)
    (hNw : AnchoredWitness X D N) (hLB : BlockAbove X N L)
    (hmax : ∀ N' L' : Subgroup G, AnchoredWitness X D N' → BlockAbove X N' L' →
      Nat.card ↥L' ≤ Nat.card ↥L)
    (hS₀ : IsSylowOf 2 S₀ (Subgroup.normalizer (X : Set G) ⊓ N)) (hDS₀ : D ≤ S₀)
    (hS₀P : S₀ ≤ Subgroup.normalizer (P : Set G)) (hLP : L ≤ Subgroup.normalizer (P : Set G))
    {N' : Subgroup G} (hN' : IsMaximalTwoLocal N') (hPN' : Subgroup.normalizer (P : Set G) ≤ N') :
    (L.subgroupOf N').IsSubnormal := by
  have hLN' : L ≤ N' := hLP.trans hPN'
  have hXN' : X ≤ N' := hLB.le.trans hLN'
  have hS₀N' : S₀ ≤ N' := hS₀P.trans hPN'
  have hDN' : D ≤ N' := hDS₀.trans hS₀N'
  by_cases hXs : (X.subgroupOf N').IsSubnormal
  · exact isSubnormal_of_conjClosure hLN'
      (conjClosure_eq hX hLB.inClassX hLB.le hLB.ne hLB.arrow) hXs
  · have hanch : AnchoredWitness X D N' := by
      refine ⟨⟨hN', fun g hg => (sup_le hXN' hDN') hg⟩, hXs, ?_⟩
      rcases hNw.2.2 with hl | ⟨S, hS, hSN⟩
      · exact Or.inl hl
      · exact Or.inr ⟨S₀, isSylowOf_of_isSylowOf_inf hS hSN hS₀, hS₀N'⟩
    have hN'char : IsCharacteristicP 2 ↥N' := isCharacteristicP_of_isPLocal hchar hN'.1
    obtain ⟨L', hL'⟩ := existsBlockAbove_core h6 (hKG N' hN') hN'char (hgood N' hanch) hXs
    have hLL' : L ≤ L' := le_of_arrow_block hN'char hX hLB.inClassX hLB.le hLN' hLB.ne
      hLB.arrow hL'.isBlockOfInX hL'.le
    have hEq : L = L' := Subgroup.eq_of_le_of_card_ge hLL' (hmax N' L' hanch hL')
    rw [hEq]
    exact hL'.isSubnormal

end Proof

theorem eightOneK_of_core (h : AschbacherSixThreeCore) : AschbacherEightOneK := by
  intro G _ _ _hK hchar hKG X hX N hN
  by_contra hnot
  obtain ⟨D, hD2, -, hDC, hex, hgood⟩ := exists_window hchar hX.1 hN hnot
  have hblocks : ∀ N' : Subgroup G, AnchoredWitness X D N' → ∃ L, BlockAbove X N' L :=
    fun N' hN' => existsBlockAbove_core h (hKG N' hN'.isMaximalTwoLocal)
      (isCharacteristicP_of_isPLocal hchar hN'.isMaximalTwoLocal.1) (hgood N' hN')
      hN'.not_isSubnormal
  obtain ⟨N₁, L, hN₁, hLB, hmax⟩ := exists_maximal_pair hex hblocks
  have hN₁char : IsCharacteristicP 2 ↥N₁ :=
    isCharacteristicP_of_isPLocal hchar hN₁.isMaximalTwoLocal.1
  obtain ⟨S₀, P, hS₀, hDS₀, hP, hS₀P, hP1, hLP⟩ :=
    exists_sylow_data hN₁char hX.1.1 hLB hD2 (le_sup_right.trans hN₁.xd_le) hDC
  have hLG : InClassXG L := inClassXG_of_key hLB.inClassX hP hP1 hLP fun N' hN' hPN' =>
    isSubnormal_of_normalizer_le_core h hchar hKG hX.1.1 hgood hN₁ hLB hmax hS₀ hDS₀ hS₀P hLP hN'
      hPN'
  exact hLB.ne (hX.2 L hLG hLB.arrow).symm

section Simple

variable {G : Type} [Group G] [Finite G]

theorem isKGroup_of_commutative {X : Type} [Group X] [Finite X] (hX : ∀ a b : X, a * b = b * a) :
    CFSG.IsKGroup X :=
  CFSG.KCore.KGroupAllSimple.of_commutative CFSG.Assembly.inCatalog_containsAbelianSimple hX

theorem commutative_of_simple_isPGroup [IsSimpleGroup G] (h : IsPGroup 2 G) :
    ∀ a b : G, a * b = b * a := by
  have hnt : Nontrivial (Subgroup.center G) := h.center_nontrivial
  rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with hc | hc
  · exact absurd hc ((Subgroup.nontrivial_iff_ne_bot _).mp hnt)
  · intro a b
    exact Subgroup.mem_center_iff.mp (hc ▸ Subgroup.mem_top b) a

theorem isKGroup_of_isMaximalTwoLocal [IsSimpleGroup G] (hK : KProper InCatalog G)
    {N : Subgroup G} (hN : IsMaximalTwoLocal N) : CFSG.IsKGroup ↥N := by
  by_cases hNtop : N = ⊤
  · obtain ⟨P, hP1, hP2, hNP⟩ := hN.1
    have hPn : P.Normal := Subgroup.normalizer_eq_top_iff.mp (hNP ▸ hNtop)
    rcases hPn.eq_bot_or_eq_top with h | h
    · exact absurd h hP1
    · have hG2 : IsPGroup 2 G := fun g => by
        obtain ⟨k, hk⟩ := hP2 ⟨g, by rw [h]; exact Subgroup.mem_top g⟩
        exact ⟨k, by simpa using congrArg Subtype.val hk⟩
      have hcomm := commutative_of_simple_isPGroup hG2
      exact isKGroup_of_commutative fun a b => Subtype.ext (hcomm a b)
  · exact CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_isKGroup hK N hNtop

theorem factorizationThree_of_eightOneK (h : AschbacherEightOneK) (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hKG : ∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N)
    {X : Subgroup G} (hX : IsMaximalInClassXG X) :
    ∃ M : Subgroup G, maximalTwoLocalsContaining (X : Set G) = {M} ∧
      (X.subgroupOf M).IsSubnormal := by
  have hXcl : InClassX ↥X := hX.1.1
  refine exists_unique_maximalTwoLocal (fun H hH => isCharacteristicP_of_isPLocal hchar hH)
    {Z | ∃ g : G, Z = conjugate X g} ?_ ?_ ?_ (X := X) ⟨1, (conjugate_one X).symm⟩
  · rintro Z ⟨a, rfl⟩ g
    exact ⟨a * g, conjugate_conjugate X a g⟩
  · rintro Z ⟨a, rfl⟩
    exact InClassX.of_mulEquiv ((MulAut.conj a⁻¹).subgroupMap X) hXcl
  · rintro Z ⟨a, rfl⟩ N ⟨hNmax, hZN⟩
    have hN'max : IsMaximalTwoLocal (conjugate N a⁻¹) := by
      have h1 := isMaximalTwoLocal_map_conj hNmax a
      rwa [← conjugate_inv_eq_map] at h1
    have hXN' : (X : Set G) ⊆ conjugate N a⁻¹ := by
      intro x hx
      have h1 : a⁻¹ * x * a⁻¹⁻¹ ∈ conjugate X a := by
        rw [mem_conjugate_iff]
        simpa [mul_assoc] using hx
      exact mem_conjugate_iff.2 (hZN h1)
    have hsub := h G hK hchar hKG X hX (conjugate N a⁻¹) ⟨hN'max, hXN'⟩
    have h2 := isSubnormal_subgroupOf_conjugate a hsub
    rwa [conjugate_conjugate, inv_mul_cancel, conjugate_one] at h2

theorem corollary_omega_of_core (hCore : AschbacherSixThreeCore)
    (h2 : AschbacherFactorizationTwo) (hTwo : AschbacherTheoremTwoK)
    (hSol : SolomonAlternatingBlockK) [IsSimpleGroup G] (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G) (T : Sylow 2 G) {N : Subgroup G} (hN : N ≠ ⊤)
    (hT₁ : ∀ T₁ : Subgroup G, T₁ ≠ ⊥ → T₁ ≤ pushingUpS (T : Subgroup G) →
      (T₁.subgroupOf (pushingUpS (T : Subgroup G))).Characteristic →
      Subgroup.normalizer (T₁ : Set G) ≤ N)
    (hΩ : Subgroup.centralizer (omegaOneCenterIn (T : Subgroup G) : Set G) ≤ N) :
    ThreeTwoConclusion G := by
  by_cases hT : (T : Subgroup G) = ⊥
  · exfalso
    have hbot : omegaOneCenterIn (T : Subgroup G) = ⊥ :=
      le_bot_iff.mp (hT ▸ omegaOneCenterIn_le (T : Subgroup G))
    rw [hbot, Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)] at hΩ
    exact hN (top_le_iff.mp hΩ)
  · have hcore : characteristicCoreStar (T : Subgroup G) ≤ N := by
      refine sup_le hΩ ?_
      exact iSup_le fun B => iSup_le fun hB => hT₁ B hB.1 hB.2.1 hB.2.2
    have hne : characteristicCoreStar (T : Subgroup G) ≠ ⊤ := fun h =>
      hN (top_le_iff.mp (h ▸ hcore))
    rcases h2 G hK hchar T hne with hSE | ⟨X, hX⟩
    · have hB := CFSG.BenderSuzuki.bender_suzuki _ hSE
      rcases benderModelsBridge G hB with ⟨n, hn, h | h⟩ | h
      · exact Or.inl ⟨n, hn, Or.inl h⟩
      · exact Or.inl ⟨n, hn, Or.inr (Or.inl h)⟩
      · exact Or.inr (Or.inl h)
    · obtain ⟨X', hX'⟩ := exists_isMaximalInClassXG hX
      obtain ⟨M, hM, hsub⟩ := factorizationThree_of_eightOneK (eightOneK_of_core hCore) hK hchar
        (fun N' hN' => isKGroup_of_isMaximalTwoLocal hK hN') hX'
      have hmem : M ∈ maximalTwoLocalsContaining (X' : Set G) := by
        rw [hM]
        exact Set.mem_singleton M
      exact threeTwo_of_block hK hTwo hSol hchar hX'.1.1 hmem.1 (fun x hx => hmem.2 hx) hsub hM

end Simple

theorem pushingUpCorollaryΩ_of_core (hCore : AschbacherSixThreeCore)
    (hN : AschbacherNineContent) (hTwo : AschbacherTheoremTwoK)
    (hSol : SolomonAlternatingBlockK) : PushingUpCorollaryΩ :=
  fun _ _ _ _ hK hchar T _ hN' hT₁ hΩ =>
    corollary_omega_of_core hCore (factorizationTwo_of_nineContent hN) hTwo hSol hK hchar T hN'
      hT₁ hΩ

end CFSG.CGT.PushingUpLit.CGT6

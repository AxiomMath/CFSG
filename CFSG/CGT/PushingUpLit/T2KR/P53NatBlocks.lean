module

public import CFSG.CGT.PushingUpLit.CGT6.SixThreeNat
public import CFSG.CGT.PushingUpLit.EightOneBlocks
public import CFSG.CGT.PushingUpLit.EightOneFinal
public import CFSG.CGT.PushingUpLit.EightOneFinalSylow
public import CFSG.CGT.PushingUpLit.ThreeFromEightOne

public section

namespace CFSG.CGT.PushingUpLit.T2KR.P53

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneFinal CFSG.CGT.PushingUpLit.ThreeFromEight
open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.GroupTheory (conjugate_conjugate isSubnormal_subgroupOf_conjugate)
open CFSG.Assembly (KProper InCatalog)
open scoped commutatorElement

section Proof

variable {G : Type} [Group G] [Finite G]

@[expose] def BlockAboveNat (X N' L : Subgroup G) : Prop :=
  BlockAbove X N' L ∧ ArrowNat X L

namespace BlockAboveNat

variable {X N' L : Subgroup G}

theorem le (h : BlockAboveNat X N' L) : X ≤ L := h.1.le

theorem isSubnormal (h : BlockAboveNat X N' L) : (L.subgroupOf N').IsSubnormal :=
  h.1.isSubnormal

theorem inClassX (h : BlockAboveNat X N' L) : InClassX ↥L := h.1.inClassX

theorem arrow (h : BlockAboveNat X N' L) : Arrow X L := h.1.arrow

theorem ne (h : BlockAboveNat X N' L) : X ≠ L := h.1.ne

theorem isBlockOfInX (h : BlockAboveNat X N' L) : IsBlockOfInX N' L := h.1.isBlockOfInX

end BlockAboveNat

theorem existsBlockAbove_coreNat (h6 : AschbacherSixThreeCoreNat) {X N' : Subgroup G}
    (hK : CFSG.IsKGroup ↥N') (hN : IsCharacteristicP 2 ↥N') (hXN : InClassXGIn N' X)
    (hnot : ¬ (X.subgroupOf N').IsSubnormal) : ∃ L : Subgroup G, BlockAboveNat X N' L := by
  obtain ⟨L, hXL, hLN, hsub, hcl, harrow⟩ := h6.rel hK hN hXN
  exact ⟨L, ⟨hXL, hLN, hsub, hcl, harrow.arrow, fun hLX => hnot (hLX ▸ hsub)⟩, harrow⟩

theorem exists_maximal_pairNat {X D : Subgroup G} (hex : ∃ N', AnchoredWitness X D N')
    (hL : ∀ N', AnchoredWitness X D N' → ∃ L, BlockAboveNat X N' L) :
    ∃ N L : Subgroup G, AnchoredWitness X D N ∧ BlockAboveNat X N L ∧
      ∀ N' L' : Subgroup G, AnchoredWitness X D N' → BlockAboveNat X N' L' →
        Nat.card ↥L' ≤ Nat.card ↥L := by
  obtain ⟨N₁, hN₁⟩ := hex
  obtain ⟨L₁, hL₁⟩ := hL N₁ hN₁
  obtain ⟨⟨N, L⟩, ⟨hN, hLB⟩, hmax⟩ := Set.exists_max_image
    {p : Subgroup G × Subgroup G | AnchoredWitness X D p.1 ∧ BlockAboveNat X p.1 p.2}
    (fun p => Nat.card ↥p.2) (Set.toFinite _) ⟨(N₁, L₁), hN₁, hL₁⟩
  exact ⟨N, L, hN, hLB, fun N' L' hN' hL' => hmax (N', L') ⟨hN', hL'⟩⟩

theorem isSubnormal_of_normalizer_le_coreNat (h6 : AschbacherSixThreeCoreNat)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hKG : ∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N)
    {X D N L S₀ P : Subgroup G} (hX : InClassX ↥X)
    (hgood : ∀ N' : Subgroup G, AnchoredWitness X D N' → InClassXGIn N' X)
    (hNw : AnchoredWitness X D N) (hLB : BlockAboveNat X N L)
    (hmax : ∀ N' L' : Subgroup G, AnchoredWitness X D N' → BlockAboveNat X N' L' →
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
    obtain ⟨L', hL'⟩ := existsBlockAbove_coreNat h6 (hKG N' hN') hN'char (hgood N' hanch) hXs
    have hLL' : L ≤ L' := le_of_arrow_block hN'char hX hLB.inClassX hLB.le hLN' hLB.ne
      hLB.arrow hL'.isBlockOfInX hL'.le
    have hEq : L = L' := Subgroup.eq_of_le_of_card_ge hLL' (hmax N' L' hanch hL')
    rw [hEq]
    exact hL'.isSubnormal

end Proof

@[expose] def AschbacherEightOneKNat : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → CFSG.Assembly.IsCharTwoType G →
    (∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N) →
    ∀ X : Subgroup G, IsMaximalInClassXGNat X → ∀ N : Subgroup G,
      N ∈ maximalTwoLocalsContaining (X : Set G) → (X.subgroupOf N).IsSubnormal

theorem eightOneK_of_coreNat (h : AschbacherSixThreeCoreNat) : AschbacherEightOneKNat := by
  intro G _ _ _hK hchar hKG X hX N hN
  by_contra hnot
  obtain ⟨D, hD2, -, hDC, hex, hgood⟩ := exists_window hchar hX.1 hN hnot
  have hblocks : ∀ N' : Subgroup G, AnchoredWitness X D N' → ∃ L, BlockAboveNat X N' L :=
    fun N' hN' => existsBlockAbove_coreNat h (hKG N' hN'.isMaximalTwoLocal)
      (isCharacteristicP_of_isPLocal hchar hN'.isMaximalTwoLocal.1) (hgood N' hN')
      hN'.not_isSubnormal
  obtain ⟨N₁, L, hN₁, hLB, hmax⟩ := exists_maximal_pairNat hex hblocks
  have hN₁char : IsCharacteristicP 2 ↥N₁ :=
    isCharacteristicP_of_isPLocal hchar hN₁.isMaximalTwoLocal.1
  obtain ⟨S₀, P, hS₀, hDS₀, hP, hS₀P, hP1, hLP⟩ :=
    exists_sylow_data hN₁char hX.1.1 hLB.1 hD2 (le_sup_right.trans hN₁.xd_le) hDC
  have hLG : InClassXG L := inClassXG_of_key hLB.inClassX hP hP1 hLP fun N' hN' hPN' =>
    isSubnormal_of_normalizer_le_coreNat h hchar hKG hX.1.1 hgood hN₁ hLB hmax hS₀ hDS₀ hS₀P hLP
      hN' hPN'
  exact hLB.ne (hX.2 L hLG hLB.2).symm

theorem factorizationThree_of_eightOneKNat {G : Type} [Group G] [Finite G]
    (h : AschbacherEightOneKNat) (hK : KProper InCatalog G)
    (hchar : CFSG.Assembly.IsCharTwoType G)
    (hKG : ∀ N : Subgroup G, IsMaximalTwoLocal N → CFSG.IsKGroup ↥N)
    {X : Subgroup G} (hX : IsMaximalInClassXGNat X) :
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

end CFSG.CGT.PushingUpLit.T2KR.P53

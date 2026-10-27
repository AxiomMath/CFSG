module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.NonunitaryLinearDegree
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.SolvableLinearCosetNormalizerClass

public section

namespace CFSG.ProperTwoGeneratedCore.HighRankPair

open CFSG.Open CFSG.ShultStronglyClosedTI CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ProperTwoGeneratedCore.LocalCriterionArbitraryCentralizerHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open CFSG.ProperTwoGeneratedCore.CosetNormalizer
open CFSG.BenderSuzuki.PFAppendixIII
open scoped Pointwise MatrixGroups

universe u

variable {G : Type u} [Group G] [Finite G]

@[expose] def LinearSuzukiPointKernelRootProduct (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G) (z : G), MinimalInvolutionPointLocalFailure H z →
    ∀ beta : rightCosetSpace H, beta ≠ rightCosetMk H 1 →
      ∀ t ∈ rightPairFlipFiber H z beta, twoRank (pairPointStabilizer H beta) = 1 →
        ∀ w ∈ pairPointStabilizer H beta, orderOf w = 2 → Commute w z → Commute w t →
          ∀ i : ℕ, (i = 1 ∨ i = 2) →
            Nat.card (elementFixedSet H w) =
                Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i + 1 →
              (∀ R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H),
                Nat.card R = Nat.card ({1} ∪ distinguishedRoots H z w : Set G) ^ i) ∧
              Subgroup.centralizer ({w} : Set G) ⊓
                  Subgroup.centralizer (localInvolutionPointHull z w : Set G) =
                Subgroup.zpowers w ∧
              ∀ (R : Sylow 2 ↥(localInvolutionPointHull z w ⊓ H))
                (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({w} : Set G))),
                (∃ ε : Subgroup.zpowers w ×
                    ↥((R : Subgroup ↥(localInvolutionPointHull z w ⊓ H)).map
                      (localInvolutionPointHull z w ⊓ H).subtype) ≃*
                    ↥(Subgroup.centralizer (rootCoset H z w)),
                  ∀ a b, (ε (a, b) : G) = a * b) ∧
                (Subgroup.centralizer (rootCoset H z w) : Set G) =
                  ((T₁ : Subgroup ↥(H ⊓ Subgroup.centralizer ({w} : Set G))).map
                      (H ⊓ Subgroup.centralizer ({w} : Set G)).subtype : Set G) ∩
                    ((localInvolutionPointHull z w : Set G) *
                      (Subgroup.centralizer (localInvolutionPointHull z w : Set G) : Set G))

omit [Finite G] in
theorem one_union_distinguishedRoots_eq (H : Subgroup G) (z u : G) :
    ({1} ∪ distinguishedRoots H z u : Set G) = {1} ∪ (involutionPointClass z ∩
      (Subgroup.centralizer ({u} : Set G) : Set G) ∩ (H : Set G)) := by
  rw [distinguishedRoots, Set.inter_right_comm]

theorem solvable_linear_root_data
    (hPK : LinearSuzukiPointKernelRootProduct G)
    (hOC : LinearSuzukiHullOddCoreTrivial G) {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z) {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hrank : twoRank (pairPointStabilizer H beta) = 1) {u : G}
    (huD : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) (huz : Commute u z)
    (hut : Commute u t)
    (hdeg : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) + 1) :
    let M := Subgroup.centralizer ({u} : Set G)
    let L := localInvolutionPointHull z u
    let q := Nat.card ({1} ∪ distinguishedRoots H z u : Set G)
    (IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a) ∧ ¬ IsConj u z ∧
    (∃ f : ℕ, 2 ≤ f ∧ q = 2 ^ f) ∧
    ∃ U : Subgroup G, (U : Set G) = {1} ∪ distinguishedRoots H z u ∧ IsElementaryAbelian 2 U ∧
      Nat.card U = q ∧ (∀ x ∈ U, x ≠ 1 → IsConj z x) ∧ (∀ b ∈ U, IsConj u (u * b)) ∧
      U ≤ L ∧ u ∉ L ∧ (L.subgroupOf M).Normal ∧
      (∀ X : Subgroup G, X ≤ L ⊓ H → IsPGroup 2 X → X ≤ U) ∧
      (∃ f : ℕ, 1 ≤ f ∧ Nat.card (BinaryGaloisField f) = 2 ^ f ∧
        Nonempty (L ≃* SL(2, BinaryGaloisField f))) ∧
      M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.zpowers u ⊔ U ∧
      M ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.zpowers u ∧
      (∀ c : G, c * u * c⁻¹ ∈ H → ∃ m ∈ M, c * m ∈ H) ∧
      (∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y → IsConj z (x * y)) := by
  intro M L q
  classical
  have hcomm := properStrongEmbeddingCommutingImages_holds G
  have hR1 := smallerR1Full G
  have htH : t ∉ H := not_mem_of_mem_rightPairFlipFiber hbeta ht
  have hesc : ¬ M ≤ H := fun hle =>
    htH (hle (Subgroup.mem_centralizer_singleton_iff.mpr hut.eq.symm))
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huD
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥(L ⊓ H)) := inferInstance
  obtain ⟨T₁⟩ : Nonempty (Sylow 2 ↥(H ⊓ M)) := inferInstance
  obtain ⟨⟨hsimple, hnonab⟩, -, -, -, -, U, hUset0, hUel, hU4, hRU, hzU, hmodels, h2trans,
      ⟨S, hS⟩, huL, -, -, hUu, -, -, -, -, -, hUclass, -, -, hinterA, -, -, -, hneq, -, -⟩ :=
    RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
      beta hbeta hrank huD hu huz hesc R T₁
  have hUset : (U : Set G) = {1} ∪ distinguishedRoots H z u := by
    rw [hUset0, one_union_distinguishedRoots_eq]
  have hqU : Nat.card U = q := by
    change Nat.card (U : Set G) = _
    rw [hUset]
  have h4 : 4 ≤ q := hqU ▸ hU4
  have hdeg' : Nat.card (elementFixedSet H u) =
      Nat.card ({1} ∪ distinguishedRoots H z u : Set G) ^ 1 + 1 := by
    rw [pow_one]; exact hdeg
  obtain ⟨f, hf, hqf, hFcard, E⟩ : ∃ f : ℕ, 2 ≤ f ∧ Nat.card U = 2 ^ f ∧
      Nat.card (BinaryGaloisField f) = Nat.card U ∧
      Nonempty (localInvolutionPointHull z u ⧸ CFSG.oddCore (localInvolutionPointHull z u) ≃*
        CFSG.BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup f) := by
    rcases hmodels with ⟨-, f, hf, hq, hF, E, -⟩ | ⟨hΓ, -⟩ | ⟨hΓ, -⟩
    · exact ⟨f, hf, hq, hF, ⟨E⟩⟩
    · exfalso
      rw [hdeg, hqU] at hΓ
      have hsq : q ^ 2 = q := by omega
      nlinarith
    · exfalso
      rw [hdeg, hqU] at hΓ
      have hcube : q ^ 3 = q := by omega
      have h16 : 16 ≤ q * q := by nlinarith
      have hq3 : q ^ 3 = q * q * q := by ring
      nlinarith
  obtain ⟨E⟩ := E
  have hnconj : ¬ IsConj u z := by
    intro huz'
    apply hneq
    ext x
    rw [mem_involutionPointClass_iff, mem_involutionPointClass_iff]
    exact ⟨fun hx => huz'.symm.trans hx, fun hx => huz'.trans hx⟩
  have hUz : ∀ x ∈ U, x ≠ 1 → IsConj z x := fun x hx hx1 =>
    mem_involutionPointClass_iff.mp (hUclass ⟨hx, hx1⟩)
  have hΔu : ∀ b ∈ U, IsConj u (u * b) := fun b hb => by
    have hmem : u * b ∈ (fun x : G => u * x) '' (U : Set G) := ⟨b, hb, rfl⟩
    rw [← hinterA] at hmem
    exact mem_involutionPointClass_iff.mp hmem.1
  obtain ⟨-, hLn, -⟩ :=
    minimalLocalFailure_arbitrary_involution_centralizer_hull h hcomm hR1 huH hu huz hesc
  obtain ⟨hRcard, hKu, hB⟩ := hPK H z h beta hbeta t ht hrank u huD hu huz hut 1 (Or.inl rfl) hdeg'
  have hsylU : ∀ R' : Sylow 2 ↥(L ⊓ H), (R' : Subgroup ↥(L ⊓ H)).map (L ⊓ H).subtype = U := by
    intro R'
    obtain ⟨-, -, -, -, -, U', hU'set, -, -, hRU', -⟩ :=
      RankOnePair.rank_one_pair_centralizer_model_and_two_global_involution_classes h hcomm hR1
        beta hbeta hrank huD hu huz hesc R' T₁
    have hUU' : U' = U := SetLike.coe_injective (hU'set.trans hUset0.symm)
    have hle : U ≤ (R' : Subgroup ↥(L ⊓ H)).map (L ⊓ H).subtype := by
      rw [← hUU', ← hRU']
      rintro _ ⟨y, -, rfl⟩
      exact ⟨y, y.2, rfl⟩
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [Subgroup.card_map_of_injective (L ⊓ H).subtype_injective, hRcard R', pow_one, hqU]
  have hUL : U ≤ L := by
    intro x hx
    rw [← hsylU R] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2.1
  have hXU : ∀ X : Subgroup G, X ≤ L ⊓ H → IsPGroup 2 X → X ≤ U := by
    intro X hX hXp
    obtain ⟨R', hR'⟩ :=
      (hXp.comap_of_injective (L ⊓ H).subtype (L ⊓ H).subtype_injective).exists_le_sylow
    intro x hx
    rw [← hsylU R']
    exact ⟨⟨x, hX hx⟩, hR' (show (⟨x, hX hx⟩ : ↥(L ⊓ H)) ∈ X.comap (L ⊓ H).subtype from hx), rfl⟩
  have hodd : CFSG.oddCore L = ⊥ :=
    hOC H z h beta hbeta t ht hrank u huD hu huz hut 1 (Or.inl rfl) hdeg'
  have hFcard' : Nat.card (BinaryGaloisField f) = 2 ^ f := hFcard.trans hqf
  have eL : L ≃* SL(2, BinaryGaloisField f) :=
    (((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm.trans
      E).trans sl2EquivPSL2.symm
  obtain ⟨T1'⟩ : Nonempty (Sylow 2 ↥(H ⊓ M)) := inferInstance
  obtain ⟨⟨ε, hε⟩, -⟩ := hB R T1'
  have hΔ : rootCoset H z u = (fun v : G => u * v) '' (U : Set G) := by rw [hUset]; rfl
  have hBle : M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.zpowers u ⊔ U := by
    intro x hx
    have hxB : x ∈ Subgroup.centralizer (rootCoset H z u) := by
      rw [hΔ, unit_translate_entire_centralizer]
      exact hx
    obtain ⟨⟨a, b⟩, hab⟩ := ε.surjective ⟨x, hxB⟩
    have hx' : x = a * b := by
      rw [← hε, hab]
    have hb : (b : G) ∈ U := hsylU R ▸ b.2
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right hb)
  have hconjH : ∀ c : G, c * u * c⁻¹ ∈ H → ∃ m ∈ M, c * m ∈ H := by
    intro c hc
    have hγ : pointRightCosetMul H (rightCosetMk H 1) c ∈ elementFixedSet H u := by
      change pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) c) u =
        pointRightCosetMul H (rightCosetMk H 1) c
      have hcu : c * u = (c * u * c⁻¹) * c := by group
      rw [pointRightCosetMul_mul, hcu, ← pointRightCosetMul_mul,
        (point_right_base_fixed_iff H _).mpr hc]
    have hα : rightCosetMk H 1 ∈ elementFixedSet H u := (point_right_base_fixed_iff H u).mpr huH
    by_cases hγα : pointRightCosetMul H (rightCosetMk H 1) c = rightCosetMk H 1
    · exact ⟨1, M.one_mem, by rw [mul_one]; exact (point_right_base_fixed_iff H c).mp hγα⟩
    · let := LocalCriterionNumerator.originalCentralizerFixedSetAction H u
      have hne1 : (⟨_, hγ⟩ : elementFixedSet H u) ≠ ⟨_, hα⟩ := fun h' =>
        hγα (congrArg Subtype.val h')
      have hne2 : (⟨_, hα⟩ : elementFixedSet H u) ≠ ⟨_, hγ⟩ := fun h' =>
        hγα (congrArg Subtype.val h').symm
      obtain ⟨g, hg1, -⟩ := (MulAction.is_two_pretransitive_iff.mp h2trans) hne1 hne2
      refine ⟨(g : G)⁻¹, M.inv_mem g.2, ?_⟩
      have h1 : pointRightCosetMul H (pointRightCosetMul H (rightCosetMk H 1) c) (g : G)⁻¹ =
          rightCosetMk H 1 := congrArg Subtype.val hg1
      rw [← point_right_base_fixed_iff, ← pointRightCosetMul_mul]
      exact h1
  have hprod : ∀ x y : G, IsConj u x → IsConj u y → x ≠ y → Commute x y →
      IsConj z (x * y) := by
    intro x y hx hy hxy hcxy
    refine isConj_mul_of_commute_of_sylow hu S U ?_ hUz hx hy hxy hcxy
    intro w hw hwu
    rw [hS] at hw
    have hw' : w ∈ involutionPointClass u ∩
        ((Subgroup.map (H ⊓ M).subtype (T₁ : Subgroup ↥(H ⊓ M)) : Subgroup G) : Set G) :=
      ⟨mem_involutionPointClass_iff.mpr hwu, hw⟩
    rw [hinterA] at hw'
    obtain ⟨b, hb, rfl⟩ := hw'
    exact ⟨b, hb, rfl⟩
  exact ⟨⟨hsimple, hnonab⟩, hnconj, ⟨f, hf, hqU.symm.trans hqf⟩, U, hUset, hUel, hqU, hUz, hΔu,
    hUL, huL, hLn, hXU, ⟨f, by omega, hFcard', ⟨eL⟩⟩, hBle, hKu.le, hconjH, hprod⟩

end CFSG.ProperTwoGeneratedCore.HighRankPair

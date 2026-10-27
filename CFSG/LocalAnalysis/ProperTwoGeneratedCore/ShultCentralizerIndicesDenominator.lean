module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionPairGeneratedHull
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorSuzukiOrderTransport
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairLinearOrder
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDistinguishedPairNontrivial

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
open CFSG.ProperTwoGeneratedCore.LocalCriterionDistinguishedPair
open scoped LinearAlgebra.Projectivization

variable {G : Type*} [Group G]

theorem rightInvolutionCommutatorSubgroup_eq_distinguishedCommutator (t : G)
    (J : Subgroup G) :
    rightInvolutionCommutatorSubgroup t J = distinguishedCommutator t J := by
  unfold rightInvolutionCommutatorSubgroup distinguishedCommutator
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.property, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, rfl⟩

variable [Finite G]

theorem distinguished_second_index_eq_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta)
    {u : G} (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ pairPointStabilizer H beta) (huz : Commute u z)
    (hunoncentral : u ∉ Subgroup.center G)
    (hthree : DistinguishedThreePointCentralization H (pairPointStabilizer H beta) t)
    (hgen : pairGeneratedHull H z beta t = ⊤)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L) (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    (hCtwo : ∀ s : L, orderOf s = 2 → IsPGroup 2 (Subgroup.centralizer ({s} : Set L)))
    (hSylow : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p L, IsCyclic P) :
    let D := pairPointStabilizer H beta
    let W := L ⊓ D
    W ≠ ⊥ ∧ Odd (Nat.card W) ∧
      (D ⊓ Subgroup.centralizer (Subgroup.closure ({u, t} : Set G) : Set G)).relIndex
          (D ⊓ Subgroup.centralizer ({u * t} : Set G)) = Nat.card W ∧
      (∀ x ∈ W, x ≠ 1 → elementFixedSet H x = {rightCosetMk H 1, beta} ∧
        L ⊓ Subgroup.centralizer ({x} : Set G) = W) ∧
      Disjoint (elementFixedSet H (u * t))
        ({rightCosetMk H 1, beta} : Set (pointRightCosetSpace H)) := by
  intro D W
  have hgen' : Subgroup.zpowers z ⊔ Subgroup.zpowers t ⊔
      distinguishedCommutator t
        ((oddCore (show Subgroup G from
          rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta)).map
          (rightCosetStabilizer H (rightCosetMk H 1) ⊓ rightCosetStabilizer H beta).subtype) =
        ⊤ := by
    rw [← rightInvolutionCommutatorSubgroup_eq_distinguishedCommutator]
    exact hgen
  have hWne := distinguished_pair_hull_nontrivial_of_commutator_generation h
    (rightCosetMk H 1) beta hbeta.symm t htclass hflip u hu hut huD huz hunoncentral hgen' L
    hLC hLnormal htL
  obtain ⟨-, hodd, -, -, -, -, hindex, hfull, hdisjoint⟩ :=
    distinguished_denominator_geometric_conclusions h (rightCosetMk H 1) beta hbeta.symm t
      htclass hflip u hu hut huD hthree L hLC hLnormal htL hclass hCtwo hSylow
  exact ⟨hWne, hodd, hindex, hfull, hdisjoint⟩

theorem linear_second_index_of_fixedSet_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta)
    {u : G} (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ pairPointStabilizer H beta) (huz : Commute u z)
    (hunoncentral : u ∉ Subgroup.center G)
    (hthree : DistinguishedThreePointCentralization H (pairPointStabilizer H beta) t)
    (hgen : pairGeneratedHull H z beta t = ⊤)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L) (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    {k : Type} [Field k] [Finite k] (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card k = 2 ^ f)
    (e : L ≃* GLAProj (GLASLGroup (Fin 2) k))
    (hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card k + 1) :
    (pairPointStabilizer H beta ⊓
        Subgroup.centralizer (Subgroup.closure ({u, t} : Set G) : Set G)).relIndex
      (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({u * t} : Set G)) =
      Nat.card k + 1 := by
  obtain ⟨hWne, -, hindex, -, -⟩ := distinguished_second_index_eq_card h beta hbeta htclass
    hflip hu hut huD huz hunoncentral hthree hgen L hLC hLnormal htL hclass
    (linear_model_involution_centralizers_two f hf hcard e)
    (linear_model_oddSylow_cyclic f hf hcard e)
  have hphi : Nonempty (elementFixedSet H (u * t) ≃ ℙ k (Fin 2 → k)) := by
    apply Finite.card_eq.mp
    rw [hdegree, Projectivization.card_of_finrank_two k (Fin 2 → k) (by simp)]
  obtain ⟨x, hxW, hxne⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).mp
    ((Subgroup.nontrivial_iff_ne_bot _).mpr hWne)
  rw [hindex]
  exact distinguished_linear_order_of_nonidentity h (rightCosetMk H 1) beta hbeta.symm t
    htclass hflip u hu hut huD hthree L hLC hLnormal htL hclass f hf hcard e hphi.some x hxW
    hxne

theorem suzuki_second_index_of_fixedSet_card
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : pointRightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (htclass : t ∈ involutionPointClass z)
    (hflip : pointRightCosetMul H (rightCosetMk H 1) t = beta)
    {u : G} (hu : orderOf u = 2) (hut : Commute u t)
    (huD : u ∈ pairPointStabilizer H beta) (huz : Commute u z)
    (hunoncentral : u ∉ Subgroup.center G)
    (hthree : DistinguishedThreePointCentralization H (pairPointStabilizer H beta) t)
    (hgen : pairGeneratedHull H z beta t = ⊤)
    (L : Subgroup G) (hLC : L ≤ Subgroup.centralizer ({u * t} : Set G))
    (hLnormal : (L.subgroupOf (Subgroup.centralizer ({u * t} : Set G))).Normal)
    (htL : t ∈ L) (hclass : ∀ s ∈ L, orderOf s = 2 → s ∈ involutionPointClass z)
    {k : Type} [Field k] [Finite k] (a : ℕ) (ha : 1 ≤ a)
    (hcard : Nat.card k = 2 ^ (2 * a + 1)) (e : L ≃* GLASzGroup a k)
    (hdegree : Nat.card (elementFixedSet H (u * t)) = Nat.card k ^ 2 + 1) :
    let C := pairPointStabilizer H beta ⊓
      Subgroup.centralizer (Subgroup.closure ({u, t} : Set G) : Set G)
    let E := pairPointStabilizer H beta ⊓ Subgroup.centralizer ({u * t} : Set G)
    C.relIndex E = Nat.card k - 2 ^ (a + 1) + 1 ∨
      C.relIndex E = Nat.card k + 2 ^ (a + 1) + 1 := by
  intro C E
  let W := L ⊓ pairPointStabilizer H beta
  obtain ⟨hWne, -, hindex, hfull, hdisjoint⟩ := distinguished_second_index_eq_card h beta
    hbeta htclass hflip hu hut huD huz hunoncentral hthree hgen L hLC hLnormal htL hclass
    (suzuki_model_involution_centralizers_two a ha hcard e)
    (suzuki_model_oddSylow_cyclic a ha hcard e)
  have hWC : W ≤ Subgroup.centralizer ({u * t} : Set G) := inf_le_left.trans hLC
  have hdiv := denominator_card_dvd_entire_fixedSet H W (u * t) hWC (rightCosetMk H 1) beta
    hdisjoint (fun x hx hne => (hfull x hx hne).1)
  rw [hdegree] at hdiv
  let U := W.subgroupOf L
  have hUcard : Nat.card U = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show W ≤ L from inf_le_left)).toEquiv
  have hUne : U ≠ ⊥ := by
    intro hU
    apply hWne
    apply Subgroup.card_eq_one.mp
    rw [← hUcard, hU, Subgroup.card_bot]
  have hUcentralizer : ∀ x ∈ U, x ≠ 1 → Subgroup.centralizer ({x} : Set L) = U := by
    intro x hx hxne
    have hC : L ⊓ Subgroup.centralizer ({(x : G)} : Set G) = W :=
      (hfull (x : G) hx fun h => hxne (Subtype.ext h)).2
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff]
    change y * x = x * y ↔ (y : G) ∈ W
    rw [← hC]
    constructor
    · intro hy
      exact ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val hy)⟩
    · intro hy
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hy.2)
  have horder := suzuki_actual_full_centralizer_card a ha hcard e U hUne
    (hUcard.symm ▸ hdiv) hUcentralizer
  rw [hUcard] at horder
  change C.relIndex E = Nat.card W at hindex
  rwa [hindex]

end CFSG.ProperTwoGeneratedCore.RankOnePair

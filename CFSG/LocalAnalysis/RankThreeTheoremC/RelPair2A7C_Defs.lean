module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.Quasithin.Background.Basic
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.RankThree.PartTwo.KFacts.KP2

@[expose] def a7Five : Subgroup (Perm (Fin 7)) :=
  alternatingGroup (Fin 7) ⊓ MulAction.stabilizer (Perm (Fin 7)) (1 : Fin 7) ⊓
    MulAction.stabilizer (Perm (Fin 7)) (2 : Fin 7)

@[expose] def a7Four : Subgroup (Perm (Fin 7)) :=
  a7Five ⊓ MulAction.stabilizer (Perm (Fin 7)) (0 : Fin 7)

theorem mem_a7Five_iff {σ : Perm (Fin 7)} :
    σ ∈ a7Five ↔ σ ∈ alternatingGroup (Fin 7) ∧ σ 1 = 1 ∧ σ 2 = 2 := by
  simp [a7Five, MulAction.mem_stabilizer_iff, and_assoc]

theorem mem_a7Four_iff {σ : Perm (Fin 7)} :
    σ ∈ a7Four ↔ σ ∈ alternatingGroup (Fin 7) ∧ σ 1 = 1 ∧ σ 2 = 2 ∧ σ 0 = 0 := by
  simp [a7Four, a7Five, MulAction.mem_stabilizer_iff, and_assoc]

theorem a7Four_le_a7Five : a7Four ≤ a7Five := inf_le_left

theorem a7Five_le_alternatingGroup : a7Five ≤ alternatingGroup (Fin 7) :=
  inf_le_left.trans inf_le_left

variable {G : Type} [Group G] [Finite G]

@[expose] def a7K (H : Subgroup G) : Subgroup G :=
  (primeComplementCore (G := H) 3).map H.subtype

@[expose] def a7I (H : Subgroup G) (ι : ↥H →* Perm (Fin 7)) : Subgroup G :=
  (a7Five.comap ι).map H.subtype

@[expose] def a7W (H : Subgroup G) : Subgroup G :=
  CFSG.Quasithin.omegaOneCenterOf (pCoreOf 2 H)

@[expose] def a7J (H Y₁ : Subgroup G) : Subgroup G :=
  ⨆ (h : G) (_ : h ∈ H), Y₁.map (MulAut.conj h).toMonoidHom

omit [Finite G] in
theorem a7K_le (H : Subgroup G) : a7K H ≤ H := Subgroup.map_subtype_le _

omit [Finite G] in
theorem a7I_le (H : Subgroup G) (ι : ↥H →* Perm (Fin 7)) : a7I H ι ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem mem_a7I_iff {H : Subgroup G} {ι : ↥H →* Perm (Fin 7)} {g : G} :
    g ∈ a7I H ι ↔ ∃ h : H, ι h ∈ a7Five ∧ (h : G) = g := by
  simp [a7I, Subgroup.mem_map, Subgroup.mem_comap]

structure A7Frame (D H V : Subgroup G) (ι : ↥H →* Perm (Fin 7)) : Prop where
  D_le : D ≤ H
  V_le : V ≤ H
  S_le : pCoreOf 2 H ≤ V
  V_two : IsPGroup 2 V
  D_norm : D ≤ normalizer (V : Set G)
  D_three : IsPGroup 3 D
  D_card : Nat.card D = 9
  H_norm : normalizer (pCoreOf 2 H : Set G) = H
  charTwo : H ⊓ centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H
  sylow : CFSG.ABGLocalTools.IsSylowOf 2 (pCoreOf 2 H) (a7K H)
  K_coprime : Nat.Coprime 3 (Nat.card (a7K H))
  card_V : Nat.card V = 4 * Nat.card (pCoreOf 2 H)
  ker_eq : ι.ker = primeComplementCore (G := H) 3
  A7_le : alternatingGroup (Fin 7) ≤ ι.range
  D_img : (D.subgroupOf H).map ι = eNine
  V_img : (V.subgroupOf H).map ι = vOne
  kGroup : ∀ X : Subgroup G, X ≤ H → CFSG.Open.IsKGroup ↥X
  noCover : ∀ Y : Subgroup G, Y ≤ V → Y ≠ ⊥ → normalizer (V : Set G) ≤ normalizer (Y : Set G) →
    ¬ alternatingGroup (Fin 7) ≤ ((H ⊓ normalizer (Y : Set G)).subgroupOf H).map ι
  exists_n : ∃ n ∈ H, n ∈ normalizer (D : Set G) ∧
    3 ∣ Nat.card (V ⊔ V.map (MulAut.conj n).toMonoidHom : Subgroup G)

end CFSG.LocalAnalysis.RankThreeTheoremC

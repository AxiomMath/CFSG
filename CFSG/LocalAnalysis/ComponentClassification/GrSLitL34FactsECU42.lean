module

public import CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksU42
public import CFSG.LieType.Chevalley.CLSEvenE6GraphInvolutionFourGroup

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanksTwo

theorem card_le_three_of_isElementaryAbelian {B : Subgroup (StatedSp 2 (ZMod 3))}
    (hB : CFSG.IsElementaryAbelian 2 B)
    (hneg : ∀ b ∈ B, ((b : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ -1) :
    Nat.card B ≤ 3 := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  let f : B → GL (Fin 2 ⊕ Fin 2) (ZMod 3) := fun b => ((b : StatedSp 2 (ZMod 3)) :
    GL (Fin 2 ⊕ Fin 2) (ZMod 3))
  have hf : Function.Injective f := fun b b' h => Subtype.ext (Subtype.ext h)
  have := hB
  have hsq : ∀ b : B, f b * f b = 1 := fun b => by
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := B)
      (b : StatedSp 2 (ZMod 3)) b.2
    have h' := congrArg Subtype.val h
    simpa [f, sq] using h'
  have hcomm : ∀ b b' : B, f b * f b' = f b' * f b := fun b b' => by
    have h := hB.is_comm.comm b b'
    have h' := congrArg (fun x : B => ((x : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3))) h
    simpa [f] using h'
  have hmem : ∀ b : B, f b ∈ StatedSp 2 (ZMod 3) := fun b => (b : StatedSp 2 (ZMod 3)).2
  have hne : ∀ b : B, f b ≠ -1 := fun b => hneg _ b.2
  obtain ⟨a, ha⟩ : ∃ a : GL (Fin 2 ⊕ Fin 2) (ZMod 3),
      ∀ b : B, f b ∈ ({1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))) := by
    by_cases hall : ∀ b : B, f b = 1 ∨ f b = -1
    · refine ⟨1, fun b => ?_⟩
      rcases hall b with h | h
      · simp [h]
      · exact absurd h (hne b)
    · push Not at hall
      obtain ⟨b₀, hb₁, hbm⟩ := hall
      refine ⟨f b₀, fun b => ?_⟩
      rcases CFSG.RankThree.SubgroupLists.eq_of_commute_involution h2 (hmem b₀) (hmem b)
          (hsq b₀) (hsq b) (hcomm b₀ b) hb₁ hbm with h | h | h | h
      · simp [h]
      · exact absurd h (hne b)
      · simp [h]
      · simp [h]
  calc Nat.card B ≤ Nat.card ({1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))) :=
        Nat.card_le_card_of_injective (fun b => ⟨f b, ha b⟩)
          (fun b b' h => hf (Subtype.mk.inj h))
    _ = ({1, a, -a} : Finset (GL (Fin 2 ⊕ Fin 2) (ZMod 3))).card :=
        Nat.card_eq_finsetCard _
    _ ≤ 3 := Finset.card_le_three

theorem false_of_U42_cover
    {G : Type} [Group G] [Finite G] (hq : IsQuasisimple G) (hZ : Nat.card (center G) = 2)
    (hL : Blueprint.LieModel (G ⧸ center G) .PSU 4 2 1) {K : Subgroup G}
    (hKZ : K ⊓ center G = ⊥) [IsSimpleGroup (K ⧸ pPrimeCore 2 K)]
    (hne : ∃ a b : K ⧸ pPrimeCore 2 K, a * b ≠ b * a) : False := by
  obtain ⟨e₁⟩ := CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 hL
  obtain ⟨e₂⟩ :=
    CFSG.LieType.Multipliers.U42.nonempty_mulEquiv_PSp43 blueprint_lieModel_projSU_four_two
  obtain ⟨α⟩ := nonempty_mulEquiv_statedSp_of_double_cover hq.1 hZ (e₁.trans e₂.symm)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 := CFSG.LieType.Chevalley.two_le_pRank_of_isSimpleGroup hne
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 K) := fun h => by
    have := Nat.Coprime.eq_one_of_dvd pPrimeCore_coprime_card h
    omega
  rw [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hodd] at h2
  obtain ⟨A, hA, hcard⟩ := LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  have : CFSG.IsElementaryAbelian 2 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).2 hA
  have : CFSG.IsElementaryAbelian 2 (A.map K.subtype) := CFSG.IsElementaryAbelian.map _
  set B : Subgroup (StatedSp 2 (ZMod 3)) := (A.map K.subtype).map α.symm.toMonoidHom with hBdef
  have hB : CFSG.IsElementaryAbelian 2 B := CFSG.IsElementaryAbelian.map _
  have hcB : Nat.card B = 4 := by
    rw [hBdef, Subgroup.card_map_of_injective α.symm.injective,
      Subgroup.card_map_of_injective K.subtype_injective, hcard]
  have hneg : ∀ b ∈ B, ((b : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)) ≠ -1 := by
    intro b hb hb1
    have hbc : α b ∈ center G := by
      rw [mem_center_iff]
      intro g
      obtain ⟨g', rfl⟩ := α.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hb1, mul_neg_one, neg_one_mul]
    obtain ⟨x, hx, hxb⟩ := Subgroup.mem_map.mp hb
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    have hαb : α b = (y : G) := by
      rw [← hxb]
      simp
    have hmem : α b ∈ K ⊓ center G := ⟨hαb ▸ y.2, hbc⟩
    rw [hKZ, mem_bot, map_eq_one_iff α α.injective] at hmem
    rw [hmem, Subgroup.coe_one] at hb1
    exact absurd hb1 (by decide)
  have := card_le_three_of_isElementaryAbelian hB hneg
  omega

end CFSG.ComponentClassification.GrSLit.L34Facts.EvenCover

module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenChev
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicGenIndex
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts
public import CFSG.Quasithin.Background.C22PfG
public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Iso
public import CFSG.Quasithin.EmptyFaithful.SBc17Ent3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 Subgroup

theorem ncard_radicalRoots_G2 (i : Fin Tag.G2.rank) :
    (parabolicRadicalRoots Tag.G2 ({i} : Set (Fin Tag.G2.rank))).ncard = 5 := by
  rcases fin_two_cases i with rfl | rfl
  · rw [radicalRoots_zero, show ({rR, rU, rV, rB, rC} : Set (Fin Tag.G2.rank → ℤ)) =
      ((({rR, rU, rV, rB, rC} : Finset (Fin Tag.G2.rank → ℤ))) : Set (Fin Tag.G2.rank → ℤ)) by
        simp, Set.ncard_coe_finset]
    decide +kernel
  · rw [radicalRoots_one, show ({rA, rU, rV, rB, rC} : Set (Fin Tag.G2.rank → ℤ)) =
      ((({rA, rU, rV, rB, rC} : Finset (Fin Tag.G2.rank → ℤ))) : Set (Fin Tag.G2.rank → ℤ)) by
        simp, Set.ncard_coe_finset]
    decide +kernel

theorem card_radical_G2_zmod_two
    (i : Fin Tag.G2.rank) :
    Nat.card (parabolicRadical Tag.G2 (ZMod 2) ({i} : Set (Fin Tag.G2.rank))) = 32 := by
  rw [card_parabolicRadical, ncard_radicalRoots_G2, Nat.card_zmod]
  norm_num

theorem hasParGen_of_isPSU_three_three
    {X : Type} [Group X] [Finite X] (hX : IsPSU 3 3 1 X) : HasParGen X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (ZMod 2) = 2 := Nat.card_zmod 2
  obtain ⟨eA⟩ := SmithC27.nonempty_quasithinG2_mulEquiv_adjointGroup_two hF
  have hD : IsPSU 3 3 1 ↥⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ :=
    SmithC27.isPSU_of_equiv_g2Derived hF (MulEquiv.refl _)
  obtain ⟨eD⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hD
  obtain ⟨eX⟩ := SBc17.nonempty_mulEquiv_PSU3_of_isPSU hX
  obtain ⟨eU⟩ := u33Pres_mulEquiv_PSU3
  obtain ⟨Fam, hFQ⟩ := parFam_adjointGroup Tag.G2 (f := 1) one_pos (ZMod 2) (by rw [hF, pow_one])
  set Γ₀ := ↥(adjointGroup Tag.G2 (ZMod 2)) with hΓ₀
  have hcardΓ : Nat.card Γ₀ = 12096 := by
    rw [hΓ₀, ← Nat.card_congr eA.toEquiv,
      SmithC27.card_quasithinG2' (n := 1) (by rw [hF, pow_one]), hF]
    norm_num
  have hcardC : Nat.card (commutator Γ₀) = 6048 := by
    rw [← Nat.card_congr (commutatorEquiv eA).toEquiv,
      ← Nat.card_congr (commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).toEquiv]
    exact SBc11.card_of_isPSU_three_three hD
  have hcardq : Nat.card (Γ₀ ⧸ commutator Γ₀) = 2 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator Γ₀)
    rw [hcardΓ, hcardC] at h
    omega
  have hq : IsPGroup 2 (Γ₀ ⧸ commutator Γ₀) := IsPGroup.of_card (n := 1) (by rw [hcardq, pow_one])
  have hQΔ : ∀ i : Fin Tag.G2.rank, Fam.Q i ⊓ commutator Γ₀ ≠ ⊥ := by
    intro i hbot
    have hQi : Fam.Q i =
        (parabolicRadical Tag.G2 (ZMod 2) {i}).subgroupOf (adjointGroup Tag.G2 (ZMod 2)) :=
      congrFun hFQ i
    have hradA : parabolicRadical Tag.G2 (ZMod 2) {i} ≤ adjointGroup Tag.G2 (ZMod 2) :=
      (parabolic_root_radical_Levi_factors Tag.G2 (ZMod 2) {i}).1.trans
        (parabolicSubgroup_le_adjointGroup Tag.G2 (ZMod 2) _)
    have hinj : Function.Injective
        ((QuotientGroup.mk' (commutator Γ₀)).comp (Fam.Q i).subtype) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      have ha1 : (a : Γ₀) ∈ commutator Γ₀ := (QuotientGroup.eq_one_iff _).mp ha
      have ha2 : (a : Γ₀) ∈ Fam.Q i ⊓ commutator Γ₀ := ⟨a.2, ha1⟩
      rw [hbot, Subgroup.mem_bot] at ha2
      exact Subtype.ext ha2
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [hcardq, hQi, card_subgroupOf_of_le hradA, card_radical_G2_zmod_two] at hle
    omega
  let eΔ : ↥(commutator Γ₀) ≃* CFSG.Open.PSU3 3 1 :=
    ((commutatorEquiv eA).symm.trans (commutatorSubgroupEquiv (quasithinG2 (ZMod 2))).symm).trans
      eD
  have hNU : Subgroup.normalizer ((u33SylowT : Subgroup U33G) : Set U33G) ≤ u33SylowT := by
    rw [coe_u33SylowT, u33Extra.normalizer_T]
  have hSN : ∀ S : Sylow 2 ↥(commutator Γ₀), Subgroup.normalizer (S : Set ↥(commutator Γ₀)) ≤ S :=
    C22Pf.normalizer_le_of_mulEquiv (eΔ.trans eU.symm) u33SylowT hNU
  exact hasParGen_of_mulEquiv (eΔ.trans eX.symm)
    (hasParGen_of_normal_two_quotient Fam hq hQΔ hSN)

end KPGen

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

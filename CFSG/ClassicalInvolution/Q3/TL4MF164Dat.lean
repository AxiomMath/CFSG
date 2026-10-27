module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.ClassicalInvolution.Q3.TL4InductDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MF164

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint

theorem q8_pow_four : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide

theorem pow_four_of_pow_eight {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R}
    (eS : (S : Subgroup R) ≃* QuaternionGroup 2) {r : X} (hr : r ∈ R) (h8 : r ^ 8 = 1) :
    r ^ 4 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r' : R := ⟨r, hr⟩
  have h8' : r' ^ 2 ^ 3 = 1 := Subtype.ext (by simpa using h8)
  have hp : IsPGroup 2 (Subgroup.zpowers r') := IsPGroup.of_card (by
    rw [Nat.card_zpowers]
    exact (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h8') |>.choose_spec.2)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq R S P
  have hmem : r' ∈ ((g • S : Sylow 2 R) : Subgroup R) := hP (Subgroup.mem_zpowers r')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  set t : (S : Subgroup R) := ⟨_, hmem⟩
  have ht : t ^ 4 = 1 := eS.injective (by rw [map_pow, q8_pow_four, map_one])
  have ht' := congrArg (fun x : (S : Subgroup R) => (x : R)) ht
  simp only [t, Subgroup.coe_pow, MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_one] at ht'
  have h4 : r' ^ 4 = 1 := by
    have h1 : (g⁻¹ * r' * g) ^ 4 = g⁻¹ * r' ^ 4 * g := by
      rw [show g⁻¹ * r' * g = g⁻¹ * r' * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
    rw [h1] at ht'
    calc r' ^ 4 = g * (g⁻¹ * r' ^ 4 * g) * g⁻¹ := by group
      _ = 1 := by rw [ht']; group
  simpa using congrArg Subtype.val h4

theorem sq_mem_of_index_le_two {X : Type} [Group X] [Finite X] {N : Subgroup X}
    (h : N.index ≤ 2) (x : X) : x ^ 2 ∈ N := by
  have h0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h2
  · rw [Subgroup.index_eq_one] at h1
    rw [h1]
    trivial
  · rw [sq]
    exact Subgroup.mul_self_mem_of_index_two h2 x

theorem exists_fstar_equiv_psl2 {X : Type} [Group X] (hs : IsSimpleGroup ↥(genFittingFStar X))
    {p f : ℕ} (hL : LieModel (TL4.FStarQuot X) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ^ f ∧
      Nonempty (↥(genFittingFStar X) ≃* GorensteinWalter.PSL2 F) := by
  obtain ⟨F, _, _, hF, ⟨e₀⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
  refine ⟨F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  let e₁ : LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 F ≃* GorensteinWalter.PSL2 F :=
    QuotientGroup.quotientMulEquivOfEq
      (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 2 F)
  have hZ : Subgroup.center ↥(genFittingFStar X) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(genFittingFStar X)) with
      h | h
    · exact h
    · exfalso
      have htop : Subsingleton (↥(genFittingFStar X) ⧸ (⊤ : Subgroup ↥(genFittingFStar X))) :=
        ⟨fun a b => by
          induction a using QuotientGroup.induction_on
          induction b using QuotientGroup.induction_on
          exact QuotientGroup.eq.mpr (Subgroup.mem_top _)⟩
      have hsub : Subsingleton (TL4.FStarQuot X) :=
        (QuotientGroup.quotientMulEquivOfEq h).toEquiv.subsingleton
      have hnt : Nontrivial (GorensteinWalter.PSL2 F) := inferInstance
      exact not_subsingleton _ ((e₀.trans e₁).symm.toEquiv.subsingleton)
  exact (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    (e₀.trans e₁)

end CFSG.ClassicalInvolution.Q3.TL4.MF164

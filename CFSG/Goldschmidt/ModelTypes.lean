module

public import CFSG.Goldschmidt.J1ModelTransport
public import CFSG.Goldschmidt.Basic
import CFSG.Goldschmidt.Steps.GoldType
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
import CFSG.LieType.CurtisTits.Conclusion
import CFSG.GH74.KGroups.PSL2
import CFSG.GH74.Bender.Suzuki

public section

namespace CFSG.Goldschmidt

open CFSG.Open
open scoped MatrixGroups

@[expose] def SimpleModels (L : Type) [Group L] : Prop :=
  (∃ f : ℕ, 3 ≤ f ∧ CFSG.Blueprint.LieModel L .PSL 2 2 f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.LieModel L .twistedB2 0 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ CFSG.Blueprint.LieModel L .PSU 3 2 f) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
    (p ^ f % 8 = 3 ∨ p ^ f % 8 = 5) ∧ CFSG.Blueprint.LieModel L .PSL 2 p f) ∨
  (∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ CFSG.Blueprint.LieModel L .twistedG2 0 3 f) ∨
  CFSG.Blueprint.NativeSporadic.IsSporadic L .J1

theorem simpleModels_of_mulEquiv {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : SimpleModels L') : SimpleModels L := by
  rcases h with ⟨f, hf, hm⟩ | ⟨f, ho, hf, hm⟩ | ⟨f, hf, hm⟩ |
    ⟨p, f, hp, hp2, hf, h5, h8, hm⟩ | ⟨f, ho, hf, hm⟩ | hJ
  · exact Or.inl ⟨f, hf, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩
  · exact Or.inr (Or.inl ⟨f, ho, hf,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h5, h8,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, ho, hf,
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hm⟩))))
  · change Nonempty (L' ≃* CFSG.Blueprint.NativeSporadic.J1) at hJ
    change _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ Nonempty (L ≃* CFSG.Blueprint.NativeSporadic.J1)
    obtain ⟨eJ⟩ := hJ
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans eJ⟩))))

theorem simpleModels_of_goldschmidtJ1 {L : Type} [Group L]
    (h : Nonempty (L ≃* goldschmidtJ1)) : SimpleModels L :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (CFSG.Open.goldschmidtJ1_native_model_of_iso h)))))


theorem simpleModels_of_psl2_even {L : Type} [Group L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSL(2, GaloisField 2 f)) : SimpleModels L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.lt_or_ge f 3 with hf3 | hf3
  · obtain rfl : f = 2 := by omega
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e5⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨5, 1, by norm_num, by norm_num, le_rfl, by norm_num,
        Or.inr (by norm_num), CFSG.Walter.blueprintLieModel_psl_two_of_mulEquiv
          5 1 (by norm_num) (e.trans e5.symm)⟩)))
  · have h4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    exact Or.inl ⟨f, hf3, CFSG.Walter.blueprintLieModel_psl_two_of_mulEquiv 2 f h4 e⟩

theorem simpleModels_of_sz {L : Type} [Group L] {a : ℕ} (ha : 1 ≤ a)
    (e : L ≃* Sz a) : SimpleModels L :=
  Or.inr (Or.inl ⟨2 * a + 1, ⟨a, rfl⟩, by omega,
    Or.inr (Or.inr (Or.inr ⟨rfl, rfl,
      CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz ha e⟩))⟩)

theorem simpleModels_of_psu3 {L : Type} [Group L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* PSU3 2 f) : SimpleModels L := by
  have hc : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  let eC : CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) (GaloisField 2 (2 * f)) (2 ^ f)) ≃*
      CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) (GaloisField 2 (2 * f))) :=
    MulEquiv.refl _
  refine Or.inr (Or.inr (Or.inl ⟨f, hf, Or.inl ⟨by decide, ?_⟩⟩))
  exact ⟨CFSG.ShultStronglyClosedTI.unitaryCover_psu_admissible f hf,
    GaloisField 2 (2 * f), inferInstance, inferInstance, hc,
    ⟨(e.trans (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative f).symm).trans eC⟩⟩

theorem simpleModels_of_walter (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (hS : IsMulCommutative (S : Subgroup G)) : SimpleModels G := by
  rcases CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models G hnab S hS with
    ⟨f, hf, hm⟩ | ⟨p, f, hp, hp2, hf, h5, h8, hm⟩ | ⟨f, ho, hf, hm⟩ | hJ
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel
      (F := GaloisField 2 f) 2 f (by omega) (GaloisField.card 2 f (by omega)) hm
    exact simpleModels_of_psl2_even hf e
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hp2, hf, h5, h8, hm⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨f, ho, hf, hm⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hJ))))

theorem simpleModels_of_old_type_abelian_omega (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (htype : goldschmidtSimpleType G) (hOmega : IsMulCommutative (Omega1 (S : Subgroup G))) :
    SimpleModels G := by
  by_cases hS : IsMulCommutative (S : Subgroup G)
  · exact simpleModels_of_walter G hnab S hS
  · rcases (N11a G htype S hOmega).2 hS with ⟨a, ha, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩
    · exact simpleModels_of_sz ha e
    · exact simpleModels_of_psu3 hf e

end CFSG.Goldschmidt

module

public import CFSG.CGT.PushingUpLit.EightOneBlocksStruct
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open scoped commutatorElement

theorem isSimpleGroup_sl2_gf {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.isSimpleGroup

theorem center_sl2_eq_bot (F : Type) [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h1 : r = 1 := by
    have h2 : (r - 1) ^ 2 = 0 := by
      have h2' : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination hr - r * h2' + h2'
    have := pow_eq_zero_iff (two_ne_zero) |>.mp h2
    exact sub_eq_zero.mp this
  subst h1
  apply Subtype.ext
  rw [← hrA]
  simp

theorem isSimpleGroup_of_quasisimple_of_center_eq_bot {A : Type} [Group A]
    (h2 : IsSimpleGroup (A ⧸ Subgroup.center A)) (hc : Subgroup.center A = ⊥) :
    IsSimpleGroup A := by
  let e : A ≃* A ⧸ Subgroup.center A :=
    (QuotientGroup.quotientBot (G := A)).symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm
  exact e.isSimpleGroup

variable {G : Type} [Group G] [Finite G]

theorem inClassX_isSimpleGroup_top {L : Type} [Group L] [Finite L] (hL : InClassX L) :
    IsSimpleGroup (L ⧸ pCore 2 L) := by
  rcases hL.1.quotient_type with hq | hp
  · rcases hL.2 with ⟨n, hn, φ, -⟩ | ⟨n, hn, φ, -⟩
    · by_cases h2 : 2 ≤ n
      · have : IsSimpleGroup (alternatingGroup (Fin (2 * n + 1))) :=
          alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ 2 * n + 1))
        exact φ.isSimpleGroup
      · have hn1 : n = 1 := by omega
        subst hn1
        have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
          rw [Nat.card_eq_fintype_card, card_alternatingGroup]
          simp [Nat.factorial]
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        have : IsSimpleGroup (alternatingGroup (Fin (2 * 1 + 1))) :=
          isSimpleGroup_of_prime_card hcard
        exact φ.isSimpleGroup
    · by_cases h2 : 2 ≤ n
      · have := isSimpleGroup_sl2_gf h2
        exact φ.isSimpleGroup
      · have hc : Subgroup.center (L ⧸ pCore 2 L) = ⊥ := by
          have h1 : (Subgroup.center (L ⧸ pCore 2 L)).map φ.toMonoidHom =
              Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
            Subgroup.map_center_eq φ
          rw [center_sl2_eq_bot] at h1
          exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h1
        exact isSimpleGroup_of_quasisimple_of_center_eq_bot hq.2.1 hc
  · have : Fact (Nat.Prime (Nat.card (L ⧸ pCore 2 L))) := ⟨hp⟩
    exact isSimpleGroup_of_prime_card rfl

theorem inClassX_eq_of_normal_not_le {X K : Subgroup G} (hX : InClassX ↥X) (hKX : K ≤ X)
    (hn : (K.subgroupOf X).Normal) (hnot : ¬ K ≤ oTwoIn X) : K = X :=
  eq_of_le_normalizer_of_not_le_oTwoIn hX.1 (inClassX_isSimpleGroup_top hX) hKX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hn) hnot

theorem inClassX_not_le_oTwoIn {X : Subgroup G} (hX : InClassX ↥X) : ¬ X ≤ oTwoIn X :=
  fun h => InClassX.not_isPGroup hX ((ThreeFromEight.isPGroup_oTwoIn X).to_le h)

theorem inClassX_commutator_eq_self {X : Subgroup G} (hX : InClassX ↥X)
    (hq : IsQuasisimple (↥X ⧸ pCore 2 ↥X)) : ⁅X, X⁆ = X :=
  commutator_eq_self_of_qs hX.1 hq

end CFSG.CGT.PushingUpLit.CGT6

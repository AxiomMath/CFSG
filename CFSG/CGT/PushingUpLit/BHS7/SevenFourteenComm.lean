module

public import CFSG.CGT.PushingUpLit.Glue.ModuleTrivial
public import CFSG.CGT.PushingUpLit.EightOneBlocksStruct
public import CFSG.CGT.PushingUpLit.BHS6.SixFour
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E F : Subgroup Γ}

theorem isSimpleGroup_sl2_galoisField {n : ℕ} (hn : 2 ≤ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := by
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 2 n (by omega)]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm.isSimpleGroup

omit [Finite Γ] in
theorem isSimpleGroup_top_of_isBTBlock (hE : IsBTBlock G T E) :
    IsSimpleGroup (↥E ⧸ pCore 2 ↥E) := by
  rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm1, hm⟩
  · obtain ⟨φ, -⟩ := hn
    have := isSimpleGroup_sl2_galoisField hn2
    exact φ.isSimpleGroup
  · obtain ⟨φ, -⟩ := hm
    by_cases h2 : 2 ≤ m
    · have : IsSimpleGroup (alternatingGroup (Fin (2 * m + 1))) :=
        alternatingGroup.isSimpleGroup (by simpa using (by omega : 5 ≤ 2 * m + 1))
      exact φ.isSimpleGroup
    · have hm1' : m = 1 := by omega
      subst hm1'
      have hcard : Nat.card (alternatingGroup (Fin (2 * 1 + 1))) = 3 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have : IsSimpleGroup (alternatingGroup (Fin (2 * 1 + 1))) :=
        isSimpleGroup_of_prime_card hcard
      exact φ.isSimpleGroup

theorem commutator_eq_of_not_centralizes (hG : CharTwo G) (hT : IsSylowOf 2 T G)
    (hF : IsBTBlock G T F) {A : Subgroup Γ} (hA : A ≤ baum T) (h : ⁅blockW F, A⁆ ≠ ⊥) :
    ⁅F, A⁆ = F := by
  have hchar : CharTwo F := charTwo_of_isBTBlock hG hT hF
  have hshort : IsShortGroup ↥F := Glue.isShortGroup_of_isBTBlock hF hchar
  have hBN : baum T ≤ Subgroup.normalizer (F : Set Γ) := baum_le_normalizer_of_isBTBlock hF
  have hAN : A ≤ Subgroup.normalizer (F : Set Γ) := hA.trans hBN
  have hN : ⁅F, A⁆ ≤ F := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hAN
  have hnorm : F ≤ Subgroup.normalizer ((⁅F, A⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left F A
  have hnot : ¬ ⁅F, A⁆ ≤ oTwoIn F := by
    intro hle
    apply h
    have hab : ∀ x ∈ oTwoIn F, ∀ y ∈ oTwoIn F, x * y = y * x := by
      rw [oTwoIn_eq_pCoreOf]
      exact hF.elemAbelian.1
    have hperf : ⁅oTwoIn F, F⁆ = oTwoIn F := by
      rw [oTwoIn_eq_pCoreOf]
      exact hF.perfect
    have hI2 : IsPGroup 2 ↥A := (hT : IsSylowTwoOf T G).2.1.to_le (hA.trans inf_le_left)
    have hc : ∀ i ∈ A, ∀ e ∈ F, i * e * i⁻¹ * e⁻¹ ∈ oTwoIn F := by
      intro i hi e he
      apply hle
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hi he
    have hfix := Glue.centralizes_oTwoIn_of_commutator_le hshort hab hperf hI2 hAN hc
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw a ha
    rw [blockW_eq_pCoreOf hF, ← oTwoIn_eq_pCoreOf] at hw
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    have := hfix a ha w hw
    calc w * a = (a * w * a⁻¹) * a := by rw [this]
      _ = a * w := by group
  exact eq_of_le_normalizer_of_not_le_oTwoIn hshort (isSimpleGroup_top_of_isBTBlock hF) hN hnorm
    hnot

theorem commutator_eq_of_le (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    (hF : IsBTBlock G T F) (hFE : F ≤ E) {A : Subgroup Γ} (hA : A ≤ baum T)
    (hFA : ⁅F, A⁆ = F) : ⁅E, A⁆ = E := by
  have hcharE : CharTwo E := charTwo_of_isBTBlock hG hT hE
  have hcharF : CharTwo F := charTwo_of_isBTBlock hG hT hF
  have hshort : IsShortGroup ↥E := Glue.isShortGroup_of_isBTBlock hE hcharE
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hAN : A ≤ Subgroup.normalizer (E : Set Γ) := hA.trans hBN
  have hN : ⁅E, A⁆ ≤ E := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hAN
  have hnorm : E ≤ Subgroup.normalizer ((⁅E, A⁆ : Subgroup Γ) : Set Γ) :=
    Subgroup.normalizer_commutator_ge_left E A
  have hnot : ¬ ⁅E, A⁆ ≤ oTwoIn E := by
    intro hle
    have hFle : F ≤ oTwoIn E := by
      calc F = ⁅F, A⁆ := hFA.symm
        _ ≤ ⁅E, A⁆ := Subgroup.commutator_mono hFE le_rfl
        _ ≤ oTwoIn E := hle
    exact InClassX.not_isPGroup (Glue.inClassX_of_isBTBlock hF hcharF)
      ((isPGroup_oTwoIn E).to_le hFle)
  exact eq_of_le_normalizer_of_not_le_oTwoIn hshort (isSimpleGroup_top_of_isBTBlock hE) hN hnorm
    hnot

end CFSG.CGT.PushingUpLit.BHS7

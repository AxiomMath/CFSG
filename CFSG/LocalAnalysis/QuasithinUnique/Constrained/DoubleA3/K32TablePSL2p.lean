module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TablePSL2Core
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedPSL2
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableTransport
public import CFSG.StronglyEmbedded.Catalog

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.GorensteinWalter
open scoped MatrixGroups

section Cases

variable {F : Type} [Field F] [Finite F]

theorem k32_card_psl2_shape {p b o : ℕ} (hF : Nat.card F = p)
    (hK : IsOddPrimePower (Nat.card F))
    (hshape : (p = 2 * 2 ^ b + 1 ∧ o = 2 ^ b + 1) ∨ (p + 1 = 2 * 2 ^ b ∧ o = 2 ^ b - 1)) :
    Nat.card (PSL2 F) = p * (2 * 2 ^ b) * o := by
  rw [psl2_card_formula F hK, hF]
  apply Nat.div_eq_of_eq_mul_left (by norm_num)
  rcases hshape with ⟨hpF, hoF⟩ | ⟨hpM, hoM⟩
  · have hsq : p ^ 2 - 1 = 4 * 2 ^ b * (2 ^ b + 1) := by
      have : p ^ 2 = 4 * 2 ^ b * (2 ^ b + 1) + 1 := by rw [hpF]; ring
      exact Nat.sub_eq_of_eq_add this
    rw [hsq, hoF]
    ring
  · have hpos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    obtain ⟨s, hs⟩ : ∃ s, 2 ^ b = s + 1 := ⟨2 ^ b - 1, by omega⟩
    have hps : p = 2 * s + 1 := by omega
    have hos : o = s := by omega
    have hsq : p ^ 2 - 1 = 4 * (s + 1) * s := by
      have : p ^ 2 = 4 * (s + 1) * s + 1 := by rw [hps]; ring
      exact Nat.sub_eq_of_eq_add this
    rw [hsq, hos, hs]
    ring

end Cases

theorem k32ExclPSL2p_proved
    : K32ExclPSL2p := by
  intro K _ _ hq p hp hp17 hmodel hK
  obtain ⟨⟨hpp, hf1, h2n, hne22, hne23⟩, F, hFfield, hFfin, hcard, ⟨e⟩⟩ := hmodel
  have : Fact p.Prime := ⟨hpp⟩
  let e' : K ≃* PSL(2, F) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hF : Nat.card F = p := by simpa using hcard
  have hp2 : p ≠ 2 := fun h => hne22 (by rw [h]; norm_num)
  have hp3 : p ≠ 3 := fun h => hne23 (by rw [h]; norm_num)
  by_cases hp7 : p ≤ 7
  · exfalso
    have hp2' : 2 ≤ p := hpp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl
    · exact absurd hpp (by norm_num)
    ·
      have hK5 : IsOddPrimePower (Nat.card F) :=
        ⟨5, 1, by norm_num, by decide, le_rfl, by rw [hF]; norm_num⟩
      have h60 : Nat.card (PSL(2, F)) = 60 := by
        rw [psl2_card_formula F hK5, hF]
        norm_num
      have : IsSimpleGroup PSL(2, F) :=
        Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hF]; norm_num)
      obtain ⟨e5⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h60
      exact hK (Or.inl ⟨e'.trans e5⟩)
    · exact absurd hpp (by norm_num)
    ·
      have : Fintype F := Fintype.ofFinite F
      have hKF : Fintype.card F = 7 := by rw [← Nat.card_eq_fintype_card, hF]
      have : CharP F 7 := charP_of_card_eq_prime hKF
      let φ : ZMod 7 ≃+* F := ZMod.ringEquiv F hKF
      exact hK (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨e'.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ.symm (Fin 2))⟩)))))
  · push Not at hp7
    obtain ⟨b, o, hb3, ho, hpodd, hshape⟩ := CFSG.QuasithinUnique.Vol2Native.L239.fermat_mersenne_shape hp hp7
    have hb4 : 4 ≤ b := by
      by_contra hcon
      have hb : b = 3 := by omega
      subst hb
      rcases hshape with ⟨hpF, -⟩ | ⟨hpM, -⟩
      · exact hp17 (by omega)
      · have : p = 15 := by omega
        subst this
        exact absurd hpp (by norm_num)
    have hK' : IsOddPrimePower (Nat.card F) :=
      Unc25K1.isOddPrimePower_of_card_prime (by omega) hF
    have hcardB := k32_card_psl2_shape hF hK' hshape
    have h32 : 32 ∣ Nat.card (PSL2 F) := by
      rw [hcardB]
      have : 32 ∣ 2 * 2 ^ b := by
        obtain ⟨c, rfl⟩ : ∃ c, b = c + 4 := ⟨b - 4, by omega⟩
        exact ⟨2 ^ c, by ring⟩
      exact (this.mul_left p).mul_right o
    exact k32NoDatum_of_mulEquiv e' (k32_noDatum_psl2 (by omega) hF h32)

end CFSG.QuasithinUnique.DoubleA3

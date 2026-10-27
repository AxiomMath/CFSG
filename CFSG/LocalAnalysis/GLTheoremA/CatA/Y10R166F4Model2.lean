module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166F4Model
public import CFSG.Quasithin.EmptyFaithful.S1565L4
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.StandardType CFSG.StandardType.TableBF4 CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot

section Certs



namespace F4Fam

variable {F : Type} [Field F] [Finite F]

theorem exists_q_zeta {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    ∃ (q : ℕ) (ζ : Fˣ), q.Prime ∧ q ≠ 2 ∧ orderOf ζ = q ∧ q ∣ 2 ^ n - 1 := by
  obtain ⟨q, hq, hq2, hqd⟩ := CFSG.Quasithin.exists_odd_prime_dvd_two_pow_sub_one hn
  haveI : Fact q.Prime := ⟨hq⟩
  have hpq : q ∣ Nat.card F - 1 := by rw [hF]; exact hqd
  obtain ⟨ζ, hζ⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := F) (p := q) hpq
  exact ⟨q, ζ, hq, hq2, hζ, hqd⟩

theorem shape_f4 {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) :
    ∀ lab : GLALabel, HasLabel (adjointGroup .F4 F) (· = lab) →
      JShape lab (3 ∣ Nat.card (Subgroup.center (adjointGroup .F4 F))) ⟨.B, 3, n⟩ := by
  intro lab hlab
  have hev : evenRank (adjointGroup .F4 F) = 4 := evenRank_adjointGroup_F4 hF hn
  have h0 : HasLabel (adjointGroup .F4 F) (· = ⟨.F4, 0, n⟩) :=
    hasLabel_adjointGroup_F4 hF (by omega)
  rcases label_eq_or_BC (K := adjointGroup .F4 F) (by omega) h0 hlab with h | h
  · subst h
    simp [JShape]
  · exact absurd h.1 (by simp)

end F4Fam

end Certs

end CFSG.LocalAnalysis.GLTheoremA.Y10F

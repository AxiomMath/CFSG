module

public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.RankThree.Classical2
open scoped MatrixGroups

theorem e6Four_dvd_sl4_order {p : ℕ} (q : ℕ) (hq : 1 ≤ q) (hpd : p ∣ q ^ 2 + 1) :
    p ∣ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) := by
  have h1 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    have : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq
    zify [this, Nat.one_le_pow _ _ hq, Nat.one_le_pow 4 _ hq]
    ring
  rw [h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hpd _) _) _) _

theorem e6Four_p_dvd_card_of_sl4_family {k : Type} [Field k] [Finite k] {L : Type} [Field L]
    (φ : k →+* L) {p : ℕ} (hpd : p ∣ Nat.card k ^ 2 + 1) {G : Type*} [Group G]
    (ρ : SL(4, L) →* G) (hρ : Function.Injective ρ) (Pt : Subgroup G) [Finite Pt] (H : SL(4, L))
    (hH : ∀ Y : SL(4, k), ρ (H * Matrix.SpecialLinearGroup.map φ Y * H⁻¹) ∈ Pt) :
    p ∣ Nat.card Pt := by
  classical
  let θ : SL(4, k) →* G := ρ.comp ((MulAut.conj H).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map φ))
  have hθinj : Function.Injective θ := fun Y Z h =>
    specialLinearGroup_map_injective φ.injective ((MulAut.conj H).injective (hρ h))
  have hle : θ.range ≤ Pt := by
    rintro _ ⟨Y, rfl⟩
    exact hH Y
  have hcard : Nat.card θ.range = Nat.card SL(4, k) :=
    (Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv).symm
  have hk : 1 ≤ Nat.card k := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
  have hdvd : p ∣ Nat.card SL(4, k) := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 k).toEquiv,
      CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSL_four k]
    exact e6Four_dvd_sl4_order (Nat.card k) hk hpd
  rw [← hcard] at hdvd
  exact hdvd.trans (Subgroup.card_dvd_of_le hle)

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

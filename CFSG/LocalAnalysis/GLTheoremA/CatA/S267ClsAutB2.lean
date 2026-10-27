module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ClsAutFieldSp
import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA

variable {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} [S.Normal]

theorem false_of_sp_two_three (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hZ : Subgroup.center ↥S = ⊥)
    {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (e : PSimple 3 S ≃* StatedProj (StatedSp 2 K)) {B : Subgroup Ω} (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hB81 : Nat.card B ≠ 3 ^ 4) : False := by
  obtain ⟨φ, hφS, hφk, -, θ, hθ, hθel, hθk, hθ1, hsplit⟩ :=
    exists_clsData_sp Nat.prime_three (by norm_num) hcore hZ le_rfl hℓ hf hK hℓ2 e hB
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    have : CharP K ℓ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
    intro h
    have h1 := (CharP.cast_eq_zero_iff K ℓ 3).1 h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h1)
  have hA : Nat.card θ.range ≤ 3 ^ 2 :=
    CFSG.StandardType.SpJoin.card_le_pow_of_isElemAbelian Nat.prime_three (by norm_num) h3K
      θ.range hθel
  have hBC' : Nat.card ↥(B ⊓ (S ⊔ Subgroup.centralizer (S : Set Ω)) ⊓
      Subgroup.centralizer (S : Set Ω)) = 3 := by
    rw [inf_assoc, inf_eq_right.2 (le_sup_right : Subgroup.centralizer (S : Set Ω) ≤
      S ⊔ Subgroup.centralizer (S : Set Ω)), ← inf_centMod_eq_inf_centralizer inferInstance hcore]
    exact hBC
  have hB1 := card_range_mul_card_inf θ hθ1
  rw [hBC'] at hB1
  have hBle := card_le_of_inner_split hB (by norm_num)
    (hsplit.imp_right fun ⟨b, hb, _, hBb, hbinf, _⟩ => ⟨b, hb, hBb, hbinf⟩)
  omega

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end

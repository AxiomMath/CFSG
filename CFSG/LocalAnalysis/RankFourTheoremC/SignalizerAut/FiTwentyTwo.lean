module

public import CFSG.LocalAnalysis.RankFourTheoremC.SignalizerAut.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveOrbit
public import CFSG.Sporadic.Bridge.Fi22Surj
import CFSG.GroupTheory.SmallOrderNotSimple

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.Monster.B.Fischer CFSG.Blueprint Subgroup

theorem eq_bot_of_le_normalizer_sylow_five {G : Type} [Group G] [Finite G] {x y : G} {m : ℕ}
    (hD : PlaneData x y) (hm : Nat.card G = 5 ^ 2 * m) (hm5 : ¬ 5 ∣ m) (hN : NormData x y)
    (hS : Star5Data x y) (T : Sylow 5 G) {U : Subgroup G} (hU : ¬ 5 ∣ Nat.card U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G)) : U = ⊥ := by
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hm hm5 T
  have h1 : g * x * g⁻¹ = MulAut.conj g x := rfl
  have h2 : g * y * g⁻¹ = MulAut.conj g y := rfl
  rw [h1, h2] at hg
  rw [← hg] at hTU
  exact coprime_core (hD.map (MulAut.conj g)) (hN.map (MulAut.conj g)) (hS.map (MulAut.conj g)) U
    hU hTU

theorem exists_planeData_fi22P :
    ∃ x y : fi22P, PlaneData x y ∧ NormData x y ∧ Star5Data x y := by
  obtain ⟨x, y, hx, hy, hD, hN⟩ := orbit_part
  exact ⟨x, y, hD, hN, star5_part hx hy hD⟩

theorem center_eq_bot_of_isSimpleGroup_of_not_prime {X : Type*} [Group X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h' | h'
  · exact h'
  · have hc : IsMulCommutative X := Subgroup.center_eq_top_iff.1 h'
    exact absurd (Group.is_simple_iff_prime_card.1 inferInstance) h

theorem center_eq_bot_of_equiv_fi22 {K : Type*} [Group K]
    (θ : K ≃* NativeSporadic.Fi22) : center K = ⊥ := by
  have hs : IsSimpleGroup K :=
    @MulEquiv.isSimpleGroup K _ NativeSporadic.Fi22 _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 θ
  refine center_eq_bot_of_isSimpleGroup_of_not_prime ?_
  rw [Nat.card_congr θ.toEquiv, CFSG.Sporadic.Fi22.card_Fi22]
  norm_num

theorem signalizerInnAt_fiTwentyTwo :
    SignalizerInnAt 5 (.sporadic .Fi22) := by
  intro K _ _ ⟨e⟩ B Y _ hBc hY hBY
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let φ : K ≃* fi22P := (e.trans β.symm).trans fi22PermEquiv
  obtain ⟨x, y, hD, hN, hS⟩ := exists_planeData_fi22P
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hcard : Nat.card K = 64561751654400 := (Nat.card_congr φ.toEquiv).trans card_fi22P
  have hf : (Nat.card K).factorization 5 = 2 :=
    hcard ▸ CFSG.GroupTheory.factorization_eq_of_pow_dvd Nat.prime_five (by norm_num)
      (by norm_num) (by norm_num)
  let T : Sylow 5 K := Sylow.ofCard B (by rw [hBc, hf])
  have hY1 : Y = ⊥ := eq_bot_of_le_normalizer_sylow_five (hD.map φ.symm)
    (m := 2582470066176) (hcard.trans (by norm_num)) (by norm_num) (hN.map φ.symm)
    (hS.map φ.symm) T ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).1 hY) hBY
  rw [hY1]
  intro b _
  rw [mem_centralizer_iff]
  intro h hh
  rw [SetLike.mem_coe, mem_bot] at hh
  rw [hh, mul_one, one_mul]

theorem signalizerAutAt_fiTwentyTwo
    {p : ℕ} (hp : p = 5) :
    SignalizerAutAt p (.sporadic .Fi22) := by
  subst hp
  refine signalizerAutAt_of_signalizerInnAt Nat.prime_five ?_ ?_ signalizerInnAt_fiTwentyTwo
  · intro K _ _ ⟨e⟩
    obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
    let θ : K ≃* NativeSporadic.Fi22 := e.trans β.symm
    exact center_eq_bot_of_equiv_fi22 θ
  · rintro ⟨d, hd, -⟩
    cases hd

end CFSG.LocalAnalysis.RankFourTheoremC

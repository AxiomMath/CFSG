module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2CoprimeSylowCyclic
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallRee
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

theorem g2b_card_identity (k N G : ℕ) (hN : N = 2 * k * (k + 1) * (2 * k + 1))
    (hG : G = (2 * k + 1) ^ 3 * ((2 * k + 1) ^ 3 + 1) * (2 * k + 1 - 1)) :
    G = N * (2 * (2 * k + 1) ^ 2 * (4 * k ^ 2 + 2 * k + 1)) := by
  subst hN hG
  rw [Nat.add_sub_cancel]
  ring

theorem g2b_psl_card (k N : ℕ) (hN : N = (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) / 2) :
    N = 2 * k * (k + 1) * (2 * k + 1) := by
  have h1 : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := by
    apply Nat.sub_eq_of_eq_add
    ring
  rw [h1] at hN
  rw [hN, show (2 * k + 1) * (4 * k * (k + 1)) = 2 * (2 * k * (k + 1) * (2 * k + 1)) by ring]
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem g2b_not_dvd (k p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 * k + 1 + 1) :
    ¬ p ∣ 2 * (2 * k + 1) ^ 2 * (4 * k ^ 2 + 2 * k + 1) := by
  intro h
  have hk1 : p ∣ k + 1 := by
    have h2 : p ∣ 2 * (k + 1) := by
      have e : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [← e]
      exact hpq
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · exact h3
  rcases (Nat.Prime.dvd_mul hp).1 h with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exfalso
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have h3 : p ∣ 2 * k + 1 := hp.dvd_of_dvd_pow h2
      have h4 : p ∣ 1 := (Nat.dvd_add_right h3).1 hpq
      exact hp.not_dvd_one h4
  · have h5 : p ∣ 4 * k * (k + 1) + 3 := by
      have h6 : p ∣ (4 * k ^ 2 + 2 * k + 1) + 2 * (k + 1) :=
        dvd_add h1 (dvd_mul_of_dvd_right hk1 2)
      have e : 4 * k ^ 2 + 2 * k + 1 + 2 * (k + 1) = 4 * k * (k + 1) + 3 := by ring
      rw [← e]
      exact h6
    have h7 : p ∣ 4 * k * (k + 1) := dvd_mul_of_dvd_right hk1 (4 * k)
    have h8 : p ∣ 3 := (Nat.dvd_add_right h7).1 h5
    exfalso
    have := Nat.le_of_dvd (by norm_num) h8
    omega

section


theorem reeG2_sylow_cyclic_of_dvd_add_one (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (P : Sylow p (ReeTag.G2.reeGamma K a)) :
    IsCyclic (P : Subgroup (ReeTag.G2.reeGamma K a)) := by
  have hpp : p.Prime := Fact.out
  have h27 : 27 ≤ Nat.card K := by
    rw [hK]
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by norm_num)
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at hpq
  have hk1 : 1 ≤ k := by omega
  have hK7 : 7 ≤ Nat.card K := by omega
  have hcop : Nat.Coprime p (Nat.card K) := by
    rw [hK]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes hpp Nat.prime_three).2 (by omega))
  have hodd3 : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) := by
    unfold CFSG.GorensteinWalter.IsOddPrimePower
    exact ⟨3, 2 * a + 1, Nat.prime_three, by norm_num, by omega, hK⟩
  haveI : Finite (ModGL ReeTag.G2.tag K) := CFSG.LieType.Chevalley.finite_modGL
  obtain ⟨w₀, hw₀, -⟩ := CFSG.LieType.Chevalley.weyl_longest_element ReeTag.G2.tag
  obtain ⟨ψ, hψC, -, -, -, -, -, -, e, -⟩ :=
    CFSG.Walter.Ree.Model.small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
  have hle : CFSG.Walter.Ree.Model.smallReeInvCentralizer a K ≤ ReeTag.G2.reeGamma K a :=
    inf_le_left
  have hrange : ψ.range ≤ ReeTag.G2.reeGamma K a := by
    intro x hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hx
    exact hle (hψC g)
  let φ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K →* ↥(ReeTag.G2.reeGamma K a) :=
    (Subgroup.inclusion hrange).comp e.toMonoidHom
  have hφ : Function.Injective φ := (Subgroup.inclusion_injective hrange).comp e.injective
  obtain ⟨Q⟩ : Nonempty (Sylow p (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
    inferInstance
  have hQcyc : IsCyclic (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)) :=
    CFSG.GorensteinWalter.psl2_sylow_isCyclic_of_coprime_field_card (p := 3) (f := 2 * a + 1)
      K hK hK7 p (by omega) hcop Q
  have hTcyc : IsCyclic (((Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map φ :
      Subgroup ↥(ReeTag.G2.reeGamma K a))) :=
    isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
        φ hφ).toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))
        φ hφ).surjective
  have hcardT : Nat.card (((Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map φ :
      Subgroup ↥(ReeTag.G2.reeGamma K a))) =
      p ^ (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).factorization p := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Sylow.card_eq_multiplicity Q
  have hPSL : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) / 2 :=
    CFSG.GorensteinWalter.psl2_card_formula K hodd3
  rw [hk] at hPSL
  have hN := g2b_psl_card k _ hPSL
  have hΓ := CFSG.HardMathSupport.Lang.Coordinator.card_reeGamma_G2_eq (a := a) (K := K) hK
  rw [← hK, hk] at hΓ
  have hid := g2b_card_identity k _ _ hN hΓ
  have hNpos : 0 < 2 * k * (k + 1) * (2 * k + 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hk1) (Nat.succ_pos k)) (by omega)
  have hNne : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) ≠ 0 := by
    rw [hN]
    exact hNpos.ne'
  have hMne : 2 * (2 * k + 1) ^ 2 * (4 * k ^ 2 + 2 * k + 1) ≠ 0 := by positivity
  have hfac : (Nat.card ↥(ReeTag.G2.reeGamma K a)).factorization p =
      (Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).factorization p := by
    rw [hid, Nat.factorization_mul hNne hMne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (g2b_not_dvd k p hpp hp5 hpq), add_zero]
  have hC : (Nat.card ↥(ReeTag.G2.reeGamma K a)).factorization p ≤
      (Nat.card ↥(((Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map φ :
        Subgroup ↥(ReeTag.G2.reeGamma K a)))).factorization p :=
    le_of_eq (by rw [hcardT, Nat.factorization_pow_self hpp, hfac])
  exact CFSG.SectionRank.sylow_isCyclic_of_cyclic_subgroup
    ((Q : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)).map φ) hC P

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

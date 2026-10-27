module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5OmegaReduction
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

open CFSG.Open
open CFSG.EvenSmallLie.CatalogOrders (lieOrd lieExp lieMin pow_lieExp_dvd le_lieExp_add_one
  card_eq_lieOrd_of_classical card_eq_lieOrd_of_exceptional)

private theorem isMulCommutative_sylow_of_statedProjSL2 {K : Type} [Group K] [Finite K]
    {F : Type} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (e : K ≃* StatedProj (StatedSL 2 F)) (S : Sylow p K) (hS : Nat.card S = Nat.card F) :
    IsMulCommutative (S : Subgroup K) := by
  let φ : Multiplicative F →* K := e.symm.toMonoidHom.comp
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).toMonoidHom.comp
      (CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom (K := F)))
  have hφ : Function.Injective φ := by
    simp only [φ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    exact e.symm.injective.comp ((MulEquiv.injective _).comp
      (CFSG.LocalAnalysis.RankThreeTheoremC.pslUnipotentHom_injective (K := F)))
  have hcard : Nat.card φ.range = p ^ (Nat.card K).factorization p := by
    rw [← S.card_eq_multiplicity, hS]
    calc Nat.card φ.range = Nat.card (Multiplicative F) :=
          (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
      _ = Nat.card F := Nat.card_congr Multiplicative.toAdd
  let A : Sylow p K := Sylow.ofCard φ.range hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K A S
  have h2 : ((g • A : Sylow p K) : Subgroup K) = (S : Subgroup K) := congrArg _ hg
  have hA : (A : Subgroup K) = φ.range := Sylow.coe_ofCard _ _
  have hSA : (S : Subgroup K) = φ.range.map (MulAut.conj g).toMonoidHom := by
    rw [← h2, Sylow.coe_subgroup_smul, hA]
    ext x
    simp [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
  rw [hSA]
  infer_instance

private theorem mul_lieExp_le_five {t : StatedLieTag} {n f N : ℕ} (hN : N ≠ 0)
    (hfac : N.factorization 5 = 5) (hn : lieMin t ≤ n) (hcard : N = lieOrd t n (5 ^ f)) :
    f * lieExp t n ≤ 5 := by
  have h1 : 5 ^ (f * lieExp t n) ∣ N := by
    rw [pow_mul, hcard]
    exact pow_lieExp_dvd hn _
  rw [Nat.prime_five.pow_dvd_iff_le_factorization hN, hfac] at h1
  exact h1

private theorem classical_eq_psl_two_five {t : StatedLieTag} {n f N : ℕ} (hN : N ≠ 0)
    (hfac : N.factorization 5 = 5) (hadm : StatedLieAdmissible t n 5 f)
    (hcl : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
      t = .POmegaMinus)
    (hcard : N = lieOrd t n (5 ^ f)) : t = .PSL ∧ n = 2 ∧ f = 5 := by
  have h55 : 5 ^ 5 ∣ lieOrd t n (5 ^ f) := by
    rw [← hcard, Nat.prime_five.pow_dvd_iff_le_factorization hN, hfac]
  obtain ⟨-, hf, hadmt⟩ := hadm
  rcases hcl with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨hn, -, -⟩ := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .PSL) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .PSL n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> try omega
    · have hf5 : f ≤ 5 := by omega
      interval_cases f <;> first | exact ⟨rfl, rfl, rfl⟩ | exact absurd h55 (by decide +kernel)
    · obtain rfl : f = 1 := by omega
      exact absurd h55 (by decide +kernel)
  · obtain ⟨hn, -⟩ := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .PSU) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .PSU n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> try omega
    obtain rfl : f = 1 := by omega
    exact absurd h55 (by decide +kernel)
  · obtain ⟨hn, -⟩ := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .PSp) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .PSp n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> try omega
    obtain rfl : f = 1 := by omega
    exact absurd h55 (by decide +kernel)
  · obtain ⟨hn, -⟩ := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .POmegaOdd) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .POmegaOdd n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> omega
  · have hn : lieMin .POmegaPlus ≤ n := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .POmegaPlus) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .POmegaPlus n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> omega
  · have hn : lieMin .POmegaMinus ≤ n := hadmt
    have hle := mul_lieExp_le_five hN hfac hn hcard
    have hnB := le_lieExp_add_one (t := .POmegaMinus) hn (by simp)
    have hE := (Nat.le_mul_of_pos_left (lieExp .POmegaMinus n) hf).trans hle
    have hn6 : n ≤ 6 := by omega
    interval_cases n <;> simp only [lieExp] at hle <;> omega

theorem defCharCase_holds :
    DefCharCase := by
  intro K _ _ t n f hadm hmodel S hS
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card K).factorization 5 = 5 := by
    have h := S.card_eq_multiplicity
    rw [hS] at h
    exact (Nat.pow_right_injective (by norm_num) h).symm
  rcases hmodel with ⟨htc, hm⟩ | ⟨rfl, ht, hm⟩ | ⟨rfl, ht, -⟩ | ⟨rfl, rfl, hm⟩
  ·
    have hcl : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨
        t = .POmegaMinus := by
      simpa [CFSG.Blueprint.classicalTags] using htc
    obtain ⟨rfl, rfl, rfl⟩ :=
      classical_eq_psl_two_five hK0 hfac hadm hcl (card_eq_lieOrd_of_classical hm)
    obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hm
    exact isMulCommutative_sylow_of_statedProjSL2 e S (hS.trans hF.symm)
  ·
    have hcard := card_eq_lieOrd_of_exceptional hm
    have hf : 1 ≤ f := hadm.2.1
    simp only [CFSG.Blueprint.chevalleyExceptionalTags, Finset.mem_insert,
      Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · have hle := mul_lieExp_le_five hK0 hfac le_rfl hcard
      simp only [lieExp] at hle
      omega
  ·
    simp only [CFSG.Blueprint.reeTitsTags, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> obtain ⟨-, -, -, h, -⟩ := hadm <;> omega
  ·
    exact absurd hm.1 (by norm_num)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.Sylow5Omega

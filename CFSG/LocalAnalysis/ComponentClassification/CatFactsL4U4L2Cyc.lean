module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4CycPGamma
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Cyc

open CFSG Subgroup CFSG.ComponentClassification.GSThmB GorensteinWalter

theorem factorization_card_psl {Q : ℕ} (hQ : Q % 4 = 1) (hQ1 : 1 < Q) :
    (Q * (Q ^ 2 - 1) / 2).factorization 2 = padicValNat 2 (Q - 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, rfl⟩ : ∃ t, Q = 4 * t + 1 := ⟨Q / 4, by omega⟩
  have ht : 0 < t := by omega
  have e : (4 * t + 1) * ((4 * t + 1) ^ 2 - 1) = 2 * ((4 * t + 1) * (4 * t * (2 * t + 1))) := by
    rw [show (4 * t + 1) ^ 2 = 8 * t * (2 * t + 1) + 1 by ring, Nat.add_sub_cancel]
    ring
  rw [e, Nat.mul_div_cancel_left _ (by norm_num), Nat.factorization_def _ Nat.prime_two,
    padicValNat.mul (by omega) (by positivity), padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 4 * t + 1),
    padicValNat.eq_zero_of_not_dvd (by omega : ¬ 2 ∣ 2 * t + 1), Nat.add_sub_cancel]
  ring

end L2Cyc

open CFSG Subgroup CFSG.ComponentClassification.GSThmB GorensteinWalter L2Cyc

theorem cf82L2Cyc : CF82L2Cyc := by
  intro Y _ _ p f hp hp2 hf hL T C E hC hCT hE hEC hCE
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, F, _, _, hF, ⟨e₀⟩⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two hL
  set e₁ : Y ≃* PSL2 F :=
    e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm with he₁
  have hodd := isOddPrimePower_of_card hp hp2 hf hF
  have hQ4 := card_mod_four hp hp2 hF
  have hcard3 : 3 < Nat.card F := by
    rw [hF]
    calc 3 < 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ p ^ (2 * f) := Nat.pow_le_pow_right hp.pos (by omega)
  set Φ : PGammaL2 F ≃* MulAut (PSL2 F) := MulEquiv.ofBijective
    (pGammaL2ToMulAutPSL2 F hodd hcard3)
    ⟨pGammaL2ToMulAutPSL2_injective F hodd hcard3,
      pGammaL2ToMulAutPSL2_surjective F hF hodd hcard3⟩ with hΦ
  set Ψ : MulAut Y ≃* PGammaL2 F := (MulAut.congr e₁).trans Φ.symm with hΨ
  set a := padicValNat 2 (p ^ (2 * f) - 1) with ha
  have hT : Nat.card T = 2 ^ a := by
    rw [Sylow.card_eq_multiplicity, Nat.card_congr e₁.toEquiv, psl2_card_formula F hodd,
      factorization_card_psl hQ4 (by omega), hF]
  by_contra hE2
  push Not at hE2
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hE
  have hm2 : 2 ≤ m := by
    by_contra h
    interval_cases m <;> simp_all
  obtain ⟨E', hE'⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 2)
    (by rw [hm]; exact pow_dvd_pow 2 hm2)
  set E'' : Subgroup (MulAut Y) := E'.map E.subtype with hE''
  have hE''E : E'' ≤ E := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hE''card : Nat.card E'' = 2 ^ 2 := by
    rw [hE'', card_map_of_injective E.subtype_injective, hE']
  have hcomm : ∀ (c : C) (e : E''), Commute (C.subtype c) (E''.subtype e) := fun c e =>
    ((mem_centralizer_iff.mp (hEC (hE''E e.2))) c c.2)
  set φ := C.subtype.noncommCoprod E''.subtype hcomm with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨c, e⟩ hce
    rw [MonoidHom.mem_ker, hφ, MonoidHom.noncommCoprod_apply] at hce
    have hc : (c : MulAut Y) = (e : MulAut Y)⁻¹ := eq_inv_of_mul_eq_one_left hce
    have heE : (e : MulAut Y)⁻¹ ∈ E := E.inv_mem (hE''E e.2)
    have hcE : (c : MulAut Y) ∈ C ⊓ E := ⟨c.2, by rw [hc]; exact heE⟩
    rw [hCE, mem_bot] at hcE
    have hc1 : c = 1 := Subtype.ext hcE
    have he1 : e = 1 := by
      apply Subtype.ext
      change (c : MulAut Y) * (e : MulAut Y) = 1 at hce
      rw [hcE, one_mul] at hce
      exact hce
    rw [mem_bot, hc1, he1]
    rfl
  have hCab : ∀ a b : C, a * b = b * a := fun a b =>
    (IsCyclic.isMulCommutative (α := C)).is_comm.comm a b
  have hEab : ∀ a b : E'', a * b = b * a := fun a b =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq hE''card).is_comm.comm a b
  set B : Subgroup (PGammaL2 F) := φ.range.map Ψ.toMonoidHom with hB
  have hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩ _ ⟨_, ⟨v, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Prod.ext (hCab _ _) (hEab _ _)
  have hBcard : Nat.card B = 2 ^ (a + 1) := by
    rw [hB, card_map_of_injective Ψ.injective,
      ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, Nat.card_prod, hE''card]
    have h2 : 2 ^ (a + 1) = 2 * Nat.card T := by rw [hT, pow_succ, mul_comm]
    rw [h2, ← hCT]
    ring
  have hB2 : IsPGroup 2 B := IsPGroup.of_card hBcard
  have hle : Nat.card B ≤ 2 ^ a := card_le_of_abelian hp hp2 hf hF hB2 hBab
  rw [hBcard] at hle
  exact absurd hle (Nat.not_le.mpr (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self a)))

end CFSG.ComponentClassification.CatFactsL4U4

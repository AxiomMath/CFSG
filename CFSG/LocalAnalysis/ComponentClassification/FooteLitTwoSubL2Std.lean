module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubL2Nm
public import CFSG.CharacterTheory.Wreathed.CentralSL2Abelianization
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Statement
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTwoSubBase

public section

namespace CFSG.ComponentClassification.FooteLit.TwoSub

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.FooteLit.Aut5L2

variable {F : Type} [Field F] [Finite F]

theorem exists_twist_fu_stdGen {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hn : 2 ≤ twoVal F) (σ : F ≃+* F)
    (hσ2 : orderOf σ = 2) : ∃ ε : Bool, twist F ε (fu F σ (stdGen F)) = -stdGen F := by
  obtain ⟨ε, hε⟩ : ∃ ε : Bool, twist F ε (fu F σ (stdGen F ^ 2)) = stdGen F ^ 2 := by
    rcases fix_or_inv_of_order_two hp hp2 hF σ (by rw [pow_one]; exact hσ2) (stdGen F ^ 2)
      (orderOf_stdGen_sq hodd) (by omega) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, by rw [h, twist_true, inv_inv]⟩
  refine ⟨ε, ?_⟩
  have hu : (twist F ε (fu F σ (stdGen F)) * (stdGen F)⁻¹) *
      (twist F ε (fu F σ (stdGen F)) * (stdGen F)⁻¹) = 1 := by
    rw [← pow_two, mul_pow, ← twist_pow', ← map_pow, hε, inv_pow, mul_inv_cancel]
  rcases eq_one_or_neg_one_of_mul_self hu with h | h
  · exfalso
    have h1 : twist F ε (fu F σ (stdGen F)) = stdGen F := mul_inv_eq_one.mp h
    have hfix : fu F σ (stdGen F) = stdGen F ∨ fu F σ (stdGen F) = (stdGen F)⁻¹ := by
      cases ε
      · exact Or.inl h1
      · right
        rw [twist_true] at h1
        exact inv_eq_iff_eq_inv.mp h1
    exact not_two_pow_twoVal_succ_dvd F Finite.one_lt_card
      (two_pow_add_dvd_of_fix_or_inv hp hp2 hF σ le_rfl (by rw [pow_one]; exact hσ2) (stdGen F)
        orderOf_stdGen hfix)
  · rw [mul_inv_eq_iff_eq_mul] at h
    rw [h, neg_one_mul]

theorem isSemidihedral_of {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hn : 3 ≤ twoVal F)
    {Q : Subgroup (PGammaL2 F)} (hTQ : (stdT F).map (incl F) ≤ Q)
    (hQc : Nat.card Q ≤ 2 ^ (twoVal F + 1)) {σ : F ≃+* F} (hσ2 : orderOf σ = 2)
    (hx₀ : nm F (stdGen F) false σ ∈ Q) : AschbacherTheorem3.IsSemidihedralTwoGroup Q := by
  have := finite_pGammaL2 (F := F)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ : ∃ k, twoVal F = k + 3 := ⟨twoVal F - 3, by omega⟩
  obtain ⟨ε, hε⟩ := exists_twist_fu_stdGen hp hp2 hF hodd (by omega) σ hσ2
  have hσσ : σ * σ = 1 := by
    have h1 := pow_orderOf_eq_one σ
    rwa [hσ2, pow_two] at h1
  have hmN : stdGen F ^ 2 ^ (k + 2) = -1 := by
    have h1 := stdGen_pow_half hodd (F := F)
    rwa [hk, show k + 3 - 1 = k + 2 by omega] at h1
  have hneg : (-1 : Fˣ) ≠ 1 := by
    rw [← hmN]
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [orderOf_stdGen, hk]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hm2 : (-1 : Fˣ) * -1 = 1 := by simp
  have ha : nm F (stdGen F) ε σ ∈ Q := by
    have h1 : nm F (stdGen F) ε σ = nm F (stdGen F) false σ * nm F 1 ε 1 := by
      rw [nm_mul]
      simp
    rw [h1]
    exact Q.mul_mem hx₀ (hTQ ((nm_mem_stdT_iff hodd hsq 1 ε).mpr (one_pow _)))
  have haa : nm F (stdGen F) ε σ * nm F (stdGen F) ε σ = nm F (-stdGen F ^ 2) false 1 := by
    rw [nm_mul, hε, Bool.xor_self, hσσ, mul_neg, ← pow_two]
  have hpow : ∀ j : ℕ, nm F (stdGen F) ε σ ^ (2 * j) = nm F ((-stdGen F ^ 2) ^ j) false 1 :=
    fun j => by rw [pow_mul, pow_two, haa, nm_false_pow]
  have hdM : (-stdGen F ^ 2) ^ 2 ^ (k + 1) = -1 := by
    rw [Even.neg_pow (Nat.even_pow.mpr ⟨even_two, by omega⟩), ← pow_mul, ← pow_succ', hmN]
  have horder : orderOf (nm F (stdGen F) ε σ) = 2 ^ (k + 3) := by
    apply orderOf_eq_prime_pow (n := k + 2)
    · rw [show 2 ^ (k + 2) = 2 * 2 ^ (k + 1) by ring, hpow, hdM, ← nm_one, nm_eq_nm_iff]
      exact fun h => hneg h.1
    · rw [show 2 ^ (k + 2 + 1) = 2 * (2 * 2 ^ (k + 1)) by ring, hpow, pow_mul', hdM, pow_two, hm2,
        nm_one]
  have hs : nm F 1 true 1 ∈ Q := hTQ ((nm_mem_stdT_iff hodd hsq 1 true).mpr (one_pow _))
  have hsinv : (nm F 1 true 1)⁻¹ = nm F 1 true 1 := inv_eq_of_mul_eq_one_right (nm_true_mul_self 1)
  have hrel : nm F 1 true 1 * nm F (stdGen F) ε σ * (nm F 1 true 1)⁻¹ =
      nm F (stdGen F) ε σ ^ (2 ^ (k + 2) - 1) := by
    have he : 2 ^ (k + 2) - 1 = 2 * (2 ^ (k + 1) - 1) + 1 := by
      have : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by ring
      have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      omega
    have h1 : (-stdGen F ^ 2) ^ (2 ^ (k + 1) - 1) * stdGen F = (stdGen F)⁻¹ := by
      have h2 : (-stdGen F ^ 2) ^ (2 ^ (k + 1) - 1) * -stdGen F ^ 2 = -1 := by
        rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hdM]
      apply eq_inv_of_mul_eq_one_left
      calc (-stdGen F ^ 2) ^ (2 ^ (k + 1) - 1) * stdGen F * stdGen F
          = (-stdGen F ^ 2) ^ (2 ^ (k + 1) - 1) * stdGen F ^ 2 := by rw [mul_assoc, ← pow_two]
        _ = -((-stdGen F ^ 2) ^ (2 ^ (k + 1) - 1) * -stdGen F ^ 2) := by rw [mul_neg, neg_neg]
        _ = 1 := by rw [h2, neg_neg]
    rw [hsinv, he, pow_succ, hpow, nm_mul, nm_mul, nm_mul]
    simp only [fu_one, twist_true, map_one, twist_one, twist_false, one_mul, mul_one, h1,
      Bool.true_xor, Bool.xor_true, Bool.not_not, Bool.false_xor]
  have hbn : nm F 1 true 1 ∉ zpowers (nm F (stdGen F) ε σ) := by
    intro h
    rw [← mem_powers_iff_mem_zpowers] at h
    obtain ⟨j, hj⟩ := h
    beta_reduce at hj
    have hr : σ ^ j = 1 := by
      have h1 := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut F))
        (nm F (stdGen F) ε σ) j
      rw [hj] at h1
      exact h1.symm
    obtain ⟨i, rfl⟩ : 2 ∣ j := hσ2 ▸ orderOf_dvd_of_pow_eq_one hr
    rw [hpow] at hj
    exact absurd (nm_eq_nm_iff.mp hj).2.1 (by decide)
  refine ⟨k + 4, by omega, nonempty_mulEquiv_semidihedral_of (n := k + 4) (by omega) ?_ ha hs ?_
    (by rw [pow_two]; exact nm_true_mul_self 1) ?_ hbn⟩
  · rw [hk] at hQc
    exact hQc
  · rw [horder, show k + 4 - 1 = k + 3 by omega]
  · rw [show k + 4 - 2 = k + 2 by omega]
    exact hrel

theorem twoSub_std {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F)) (hq4 : Nat.card F % 4 = 1)
    (hn : 3 ≤ twoVal F) {Q : Subgroup (PGammaL2 F)} (hQ : IsPGroup 2 Q)
    (hTQ : (stdT F).map (incl F) ≤ Q) (hnl : ∃ x ∈ Q, x.right ≠ 1) :
    (Nat.card Q ≤ 2 * 2 ^ twoVal F ∧ AschbacherTheorem3.IsSemidihedralTwoGroup Q) ∨
      ∃ β ∈ Q, β * β = 1 ∧ β.right ≠ 1 ∧ ∀ g ∈ (stdT F).map (incl F), β * g = g * β := by
  by_cases hg : ∃ b : Fˣ, b ^ 2 ^ (twoVal F - 1) = 1 ∧
      ∃ ε σ, σ * σ = 1 ∧ σ ≠ 1 ∧ nm F b ε σ ∈ Q
  · obtain ⟨b, hb, ε, σ, hσσ, hσ1, hmem⟩ := hg
    exact Or.inr (exists_central_of_good hp hp2 hF hodd hsq hn hTQ hb hσσ hσ1 hmem)
  left
  have := finite_pGammaL2 (F := F)
  obtain ⟨x₁, hx₁, hσ1⟩ := hnl
  obtain ⟨σ, hσ⟩ : ∃ σ, x₁.right = σ := ⟨_, rfl⟩
  rw [hσ] at hσ1
  have hσσ : σ * σ = 1 := hσ ▸ right_mul_self_of_not_good hodd hsq hq4 hn hQ hTQ hg hx₁
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσσ) hσ1
  have hall : ∀ x ∈ Q, x.right = 1 ∨ x.right = σ := fun x hx => by
    by_cases h : x.right = 1
    · exact Or.inl h
    · exact Or.inr (ringAut_eq_of_sq (right_mul_self_of_not_good hodd hsq hq4 hn hQ hTQ hg hx)
        hσσ h hσ1)
  obtain ⟨b₁, ε₁, hb₁, hx₁b⟩ := exists_nm_of_mem hodd hsq hq4 hn hQ hTQ hx₁
  rw [hσ] at hx₁b
  have hb₁N : b₁ ^ 2 ^ (twoVal F - 1) = -1 := (pow_half_eq_one_or hodd hb₁).resolve_left
    fun h => hg ⟨b₁, h, ε₁, σ, hσσ, hσ1, hx₁b ▸ hx₁⟩
  have hm2 : (-1 : Fˣ) * -1 = 1 := by simp
  have hlin : (linearPart Q).map SemidirectProduct.inl ≤ (stdT F).map (incl F) := by
    rintro _ ⟨g, hg', rfl⟩
    obtain ⟨b, ε, hb, hgb⟩ := exists_nm_of_mem hodd hsq hq4 hn hQ hTQ hg'
    rw [SemidirectProduct.right_inl] at hgb
    rw [hgb, nm_mem_stdT_iff hodd hsq]
    refine (pow_half_eq_one_or hodd hb).resolve_right fun h =>
      hg ⟨b * twist F ε b₁, ?_, xor ε ε₁, σ, hσσ, hσ1, ?_⟩
    · rw [mul_pow, ← twist_pow', h, hb₁N, twist_of_mul_self _ hm2, hm2]
    · have h1 := Q.mul_mem hg' hx₁
      rw [hgb, hx₁b, nm_mul, fu_one, one_mul] at h1
      exact h1
  have h1 : Nat.card (linearPart Q) ≤ 2 ^ twoVal F := by
    rw [← card_map_of_injective (SemidirectProduct.inl_injective (φ := pgl2FieldAut F)),
      ← card_stdT hodd hsq, ← card_map_of_injective (incl_injective F)]
    exact card_le_of_le hlin
  have h2 : Nat.card (Q.map (fieldProj F)) ≤ 2 := by
    have hle : Q.map (fieldProj F) ≤ zpowers σ := by
      rintro _ ⟨x, hx, rfl⟩
      rcases hall x hx with h | h
      · rw [show fieldProj F x = x.right from rfl, h]
        exact one_mem _
      · rw [show fieldProj F x = x.right from rfl, h]
        exact mem_zpowers _
    calc Nat.card (Q.map (fieldProj F)) ≤ Nat.card (zpowers σ) := card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, hσ2]
  have hcard : Nat.card Q ≤ 2 * 2 ^ twoVal F := by
    rw [card_eq_linearPart_mul Q, mul_comm 2]
    exact Nat.mul_le_mul h1 h2
  have hx₀ : nm F (stdGen F) false σ ∈ Q := by
    have hu : (stdGen F * (twist F ε₁ b₁)⁻¹) ^ 2 ^ (twoVal F - 1) = 1 := by
      rw [mul_pow, inv_pow, ← twist_pow', hb₁N, stdGen_pow_half hodd, twist_of_mul_self _ hm2,
        mul_inv_cancel]
    have h3 : nm F (stdGen F) false σ = nm F (stdGen F * (twist F ε₁ b₁)⁻¹) ε₁ 1 * x₁ := by
      rw [hx₁b, nm_mul, fu_one, Bool.xor_self, one_mul, inv_mul_cancel_right]
    rw [h3]
    exact Q.mul_mem (hTQ ((nm_mem_stdT_iff hodd hsq _ ε₁).mpr hu)) hx₁
  exact ⟨hcard, isSemidihedral_of hp hp2 hF hodd hsq hn hTQ (by rw [pow_succ]; omega) hσ2 hx₀⟩

end CFSG.ComponentClassification.FooteLit.TwoSub

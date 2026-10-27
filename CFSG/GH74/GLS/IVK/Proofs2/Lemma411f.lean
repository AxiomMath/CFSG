module

public import CFSG.GH74.GLS.Stage2.Final.ModelOneClass
public import CFSG.GH74.GLS.Stage2.Final.ModelFam

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Stage2.Final

theorem ivk_4_11f :
    ∀ (K : Type) [Group K] [Finite K] (ε : ℤ) (q : ℕ), (ε = 1 ∨ ε = -1) → Odd q → 3 < q →
      ¬ ((q : ℤ) ≡ ε [ZMOD 8]) → IsLnEps 4 K ε q → (q : ℤ) ≡ ε [ZMOD 4] →
        ∀ x y : K, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  intro K _ _ ε q hε hqodd hq3 h8 hK h4 x y hx hy
  rcases hK with ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩ | ⟨rfl, F, iF, fF, hF, ⟨e⟩⟩
  ·
    obtain ⟨p, f, hp, hf, hpf⟩ : ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ Nat.card F = p ^ f := by
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨n, hpp, hn⟩ := FiniteField.card F (ringChar F)
      refine ⟨ringChar F, n, hpp, n.pos, ?_⟩
      rw [Nat.card_eq_fintype_card]
      exact hn
    have hq8 : q % 8 = 5 := by
      have h1 : (q : ℤ) % 4 = 1 % 4 := h4
      have h2 : ¬ ((q : ℤ) % 8 = 1 % 8) := h8
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ Nat.card F := by
        rw [hpf]
        exact dvd_pow_self 2 (by omega)
      obtain ⟨k, hk⟩ := hqodd
      rw [hF] at this
      omega
    have hmodel : LieModel K .PSL 4 p f := by
      have hadm : StatedLieAdmissible .PSL 4 p f :=
        ⟨hp, hf, by norm_num, fun h => by simp at h, fun h => by simp at h⟩
      exact Or.inl ⟨by simp [classicalTags], hadm, F, iF, fF, hpf, ⟨e⟩⟩
    have hqpf : p ^ f = q := by rw [← hpf, hF]
    exact modelOneClass K p f hp hp2 (Or.inl ⟨by rw [hqpf]; exact hq8, hmodel⟩) x y hx hy
  ·
    obtain ⟨p, f, hfp, hcp, hqf⟩ := Stage2.Final.ModelBlock.exists_uni_params hF
    have hp : p.Prime := hfp.out
    have hq8 : q % 8 = 3 := by
      have h1 : (q : ℤ) % 4 = (-1) % 4 := h4
      have h2 : ¬ ((q : ℤ) % 8 = (-1) % 8) := h8
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at hqf
        omega
      · exact hf
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ q := by
        rw [hqf]
        exact dvd_pow_self 2 (by omega)
      obtain ⟨k, hk⟩ := hqodd
      omega
    have hmodel : LieModel K .PSU 4 p f := by
      have hadm : StatedLieAdmissible .PSU 4 p f :=
        ⟨hp, hf, by norm_num, fun h => by simp at h⟩
      rw [hqf] at e
      exact Or.inl ⟨by simp [classicalTags], hadm, F, iF, fF, by rw [hF, hqf], ⟨e⟩⟩
    exact modelOneClass K p f hp hp2 (Or.inr ⟨by rw [← hqf]; exact hq8, hmodel⟩) x y hx hy

end CFSG.GH74.GLS.IVK.Proofs2

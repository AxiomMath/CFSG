module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk412Uni

public section

open Subgroup CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.IVK.Proofs2

theorem prop412_of_isLnEps_lin {K : Type} [Group K] [Finite K] {q : ℕ}
    (h4 : q % 4 = 3) (h5 : 5 ≤ q) (hK : IsLnEps 4 K 1 q) : Prop412 K := by
  rcases hK with ⟨-, F, iF, fF, hF, ⟨e⟩⟩ | ⟨h1, -⟩
  · have e' : K ≃* PG (ModelData.lin F) := e
    have hP := prop412_lin (F := F) (by rw [hF]; exact h5) (by rw [hF]; exact h4)
    exact hP.map e'.symm
  · exact absurd h1 (by norm_num)

theorem prop412_of_isLnEps_uni {K : Type} [Group K] [Finite K] {q : ℕ} (hq : Odd q)
    (h4 : q % 4 = 1) (h5 : 5 ≤ q) (hK : IsLnEps 4 K (-1) q) : Prop412 K := by
  rcases hK with ⟨h1, -⟩ | ⟨-, F, iF, fF, hF, ⟨e⟩⟩
  · exact absurd h1 (by norm_num)
  · obtain ⟨p, f, hfp, hcp, hqf⟩ := exists_uni_params hF
    subst hqf
    have hp2 : p ≠ 2 := by
      rintro rfl
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at h5
      · have : 2 ∣ 2 ^ f := dvd_pow_self 2 hf.ne'
        obtain ⟨k, hk⟩ := hq
        omega
    have e' : K ≃* PG (ModelData.uni hF) := e
    exact (prop412_uni hF hp2 h5 h4).map e'.symm

theorem prop412_of_L4U4 {K : Type} [Group K] [Finite K] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IsLnEps 4 K (-1) q)) : Prop412 K := by
  rcases hK with ⟨h4, hK⟩ | ⟨h4, hK⟩
  · exact prop412_of_isLnEps_lin h4 h5 hK
  · exact prop412_of_isLnEps_uni hq h4 h5 hK

theorem ivk_4_12_nc {K : Type} [Group K] [Finite K] {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q)
    (hK : (q % 4 = 3 ∧ IsLnEps 4 K 1 q) ∨ (q % 4 = 1 ∧ IsLnEps 4 K (-1) q)) {u : K}
    (hu : orderOf u = 2) (hnc : ¬ CFSG.GH74.IsCentralInvolution u)
    (S : Sylow 2 ↥(centralizer ({u} : Set K))) :
    ∃ (D₁ D₂ : Subgroup K) (n : ℕ), 3 ≤ n ∧
      S.map (centralizer ({u} : Set K)).subtype = D₁ ⊔ D₂ ∧
      (∀ a ∈ D₁, ∀ b ∈ D₂, a * b = b * a) ∧ D₁ ⊓ D₂ = ⊥ ∧ IsDihedralTwoGroup ↥D₁ n ∧
      IsDihedralTwoGroup ↥D₂ n ∧
      ((∀ a ∈ D₁, u * a = a * u) ∧ u ∈ D₁ ∨ (∀ a ∈ D₂, u * a = a * u) ∧ u ∈ D₂) ∧
      Nat.card ↥(S.map (centralizer ({u} : Set K)).subtype) = 2 ^ (2 * n) ∧
      ∀ T : Sylow 2 K, Nat.card ↥(T : Subgroup K) = 2 ^ (2 * n + 1) :=
  (prop412_of_L4U4 hq h5 hK).sylow hu hnc S

end CFSG.GH74.GLS.IVK.Proofs2

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.PropA.AutModel

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Equiv Subgroup CFSG.Sporadic.Schreier

theorem exists_pi
    {C : Type*} [Group C] [Finite C] (N : Subgroup C) [N.Normal]
    (θ : ↥N ≃* ↥D24) {t : C}
    (hker : ∀ c : C, (∀ n : ↥N, c * n * c⁻¹ = n) ↔ c ∈ zpowers t)
    (hcard : Nat.card C = 4 * Nat.card ↥N) (ht2 : orderOf t = 2) :
    ∃ (π : C →* Perm (Fin 24)) (g : C), π.ker = zpowers t ∧
      (∀ n : ↥N, π n = (θ n : Perm (Fin 24))) ∧ π g = m12Sigma := by
  obtain ⟨ψ, hψ⟩ := exists_aut_equiv
  let κ : C →* MulAut ↥N := MulAut.conjNormal
  let π₁ : C →* MulAut ↥D24 := (MulAut.congr θ).toMonoidHom.comp κ
  let π : C →* Perm (Fin 24) := AA.subtype.comp (ψ.symm.toMonoidHom.comp π₁)
  have hconjN : ∀ (n x : ↥N), κ n x = n * x * n⁻¹ := by
    intro n x
    apply Subtype.ext
    rfl
  have hπ₁ : ∀ (n : ↥N) (d : ↥D24), (π₁ n) d = θ (n * θ.symm d * n⁻¹) := by
    intro n d
    show (MulAut.congr θ (κ n)) d = θ (n * θ.symm d * n⁻¹)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply]
    rw [hconjN]
  have hpsi_theta : ∀ n : ↥N,
      ψ ⟨(θ n : Perm (Fin 24)), D24_le_AA (θ n).2⟩ = π₁ n := by
    intro n
    apply MulEquiv.ext
    intro d
    apply Subtype.ext
    rw [hψ ⟨(θ n : Perm (Fin 24)), D24_le_AA (θ n).2⟩ d, hπ₁ n d]
    simp only [map_mul, map_inv, θ.apply_symm_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have hpi_n : ∀ n : ↥N, π n = (θ n : Perm (Fin 24)) := by
    intro n
    have h1 : ψ.symm (π₁ n) = ⟨(θ n : Perm (Fin 24)), D24_le_AA (θ n).2⟩ :=
      (MulEquiv.symm_apply_eq ψ).mpr (hpsi_theta n).symm
    exact congrArg (fun x : ↥AA => (x : Perm (Fin 24))) h1
  have hpi_one : ∀ c : C, π c = 1 ↔ ∀ n : ↥N, c * n * c⁻¹ = n := by
    intro c
    have h1 : π c = 1 ↔ ψ.symm (π₁ c) = 1 := by
      show AA.subtype (ψ.symm (π₁ c)) = 1 ↔ ψ.symm (π₁ c) = 1
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; exact map_one AA.subtype⟩
    have h2 : ψ.symm (π₁ c) = 1 ↔ π₁ c = 1 := MulEquiv.map_eq_one_iff ψ.symm
    have h3 : π₁ c = 1 ↔ κ c = 1 := MulEquiv.map_eq_one_iff (MulAut.congr θ)
    have h4 : κ c = 1 ↔ ∀ n : ↥N, c * n * c⁻¹ = n := by
      constructor
      · intro h n
        exact congrArg (fun x : ↥N => (x : C)) (DFunLike.congr_fun h n)
      · intro h
        exact MulEquiv.ext fun n => Subtype.ext (h n)
    exact h1.trans (h2.trans (h3.trans h4))
  have hkerπ : π.ker = zpowers t := by
    ext c
    rw [MonoidHom.mem_ker]
    exact (hpi_one c).trans (hker c)
  have hcardker : Nat.card π.ker = 2 := by
    rw [hkerπ, Nat.card_zpowers, ht2]
  have hC : Nat.card C = 380160 := by
    rw [hcard, Nat.card_congr θ.toEquiv, card_D24]
  have hmul := card_ker_mul_card_range π
  rw [hcardker, hC] at hmul
  have hrange_card : Nat.card π.range = 190080 :=
    Nat.mul_left_cancel (by norm_num : (0 : ℕ) < 2) (by rw [hmul])
  have hle : π.range ≤ AA := by
    rintro y ⟨c, rfl⟩
    exact (ψ.symm (π₁ c)).2
  have hrange : π.range = AA :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hrange_card, card_AA])
  have hsig : m12Sigma ∈ π.range := by
    rw [hrange]
    exact sigma_mem_AA
  obtain ⟨g, hg⟩ := hsig
  exact ⟨π, g, hkerπ, hpi_n, hg⟩

end CFSG.EvenSporadicStandard.M12Std.PropA

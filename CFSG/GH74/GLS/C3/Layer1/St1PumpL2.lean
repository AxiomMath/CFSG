module

public import CFSG.GH74.GLS.IVK.Proofs2.C3Ivk102L
public import CFSG.GH74.GLS.IVK.Lifted.SolvAut

public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpL2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.GH74.GLS.IVK.Proofs2

section Involution

variable {F₀ : Type} [Field F₀] [Finite F₀] {K : Type} [Group K] [Finite K]

private theorem exists_eps_of_l2Field (hF : L2Field F₀) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (Nat.card F₀ : ℤ) ≡ ε [ZMOD 4] := by
  obtain ⟨t, ht⟩ := hF.1
  by_cases h : t % 2 = 0
  · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
  · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩

theorem solvable_fixedSubgroup_of_involution (hF : L2Field F₀) (hfm : IsFM9 (Nat.card F₀))
    (e : K ≃* L2 F₀) (N : L2Notation e) {y : MulAut K} (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1) :
    Group.IsSolvable ↥(CFSG.GH74.GLS.fixedSubgroup K y) := by
  have hinj := conj_injective_of_L2 e
  have hyo : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  obtain ⟨ε, hε1, hε⟩ := exists_eps_of_l2Field hF
  by_cases hyInn : y ∈ innAut K
  ·
    obtain ⟨u, rfl⟩ := hyInn
    have hu2 : u ^ 2 = 1 := by
      apply hinj
      rw [map_pow, hy2, map_one]
    have hu1 : u ≠ 1 := fun h => hy1 (by rw [h, map_one])
    have hu : orderOf u = 2 := orderOf_eq_prime hu2 hu1
    obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F₀ - ε :=
      ⟨(Nat.card F₀ - ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
    have hdih := (ivk_1_3a F₀ hF K e ε hε1 hε d hd u hu).2.1
    rw [Lemma118.fixedSubgroup_conj]
    exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_isDihedralOrder hdih
  · by_cases hyD : y ∈ innDiagSub e
    ·
      obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = Nat.card F₀ + ε :=
        ⟨(Nat.card F₀ + ε).toNat, Int.toNat_of_nonneg (by have := hF.2; omega)⟩
      have hdih := (ivk_1_3b F₀ hF K e ε hε1 hε d hd y hyD hyInn hyo).2.1
      exact CFSG.GH74.GLS.IVK.Lifted.isSolvable_of_isDihedralOrder hdih
    ·
      obtain ⟨-, ⟨ρ⟩⟩ := exists_equiv_perm4_fixedSubgroup hF hfm e N hy2 hyD
      have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
      exact Group.isSolvable_of_isSolvable_injective (f := ρ.toMonoidHom) ρ.injective

end Involution

theorem solvable_of_fixed_fm9 {L : Type} [Group L] [Finite L] (hL : HasL2Model L IsFM9)
    (σ : L ≃* L) (hσ : ∀ l, σ (σ l) = l) (hσ1 : ∃ l, σ l ≠ l)
    (F : Subgroup L) (hF : ∀ l ∈ F, σ l = l) : Group.IsSolvable ↥F := by
  obtain ⟨p, f, hp, hf, hq, hlie⟩ := hL
  have hmodel : HasL2Model L (fun r => r = p ^ f) := ⟨p, f, hp, hf, rfl, hlie⟩
  obtain ⟨F₀, _, _, e0, hF₀, hFq⟩ := exists_l2Field_of_hasL2Model hq hmodel
  have hfm : IsFM9 (Nat.card F₀) := hFq ▸ hq
  obtain ⟨e, N, -⟩ :=
    ivk_1_2a_exists F₀ hF₀ L e0 (inferInstance : Nonempty (Sylow 2 (MulAut L))).some
  let y : MulAut L := σ
  have hy2 : y ^ 2 = 1 := by
    ext l
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    exact hσ l
  have hy1 : y ≠ 1 := by
    intro h
    obtain ⟨l, hl⟩ := hσ1
    apply hl
    have := DFunLike.congr_fun h l
    simpa using this
  have hle : F ≤ CFSG.GH74.GLS.fixedSubgroup L y := fun l hl => hF l hl
  have hsolv := solvable_fixedSubgroup_of_involution hF₀ hfm e N hy2 hy1
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

end CFSG.GH74.GLS.C3.Layer1.PumpL2

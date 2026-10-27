module

public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6FiveDiag
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Open

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem mem_map_conj_iff {G : Type*} [Group G] (D : Subgroup G) (P x : G) :
    x ∈ D.map (MulAut.conj P).toMonoidHom ↔ P⁻¹ * x * P ∈ D := by
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  · intro hx
    exact ⟨P⁻¹ * x * P, hx, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem exists_le_prod_conj_diagP (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1)
    (E : Subgroup (unitarySU ℓ f K 2 × unitarySU ℓ f K 6)) (hE : IsElemAbelian 5 E) :
    ∃ R : unitarySU ℓ f K 2 × unitarySU ℓ f K 6,
      E ≤ ((diagP ℓ f 5 2 K).map (MulAut.conj R.1).toMonoidHom).prod
        ((diagP ℓ f 5 6 K).map (MulAut.conj R.2).toMonoidHom) := by
  obtain ⟨R₁, hR₁⟩ := exists_conj_le_diagP h Nat.prime_five h5
    (E.map (MonoidHom.fst _ _)) (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE _)
  obtain ⟨R₂, hR₂⟩ := exists_conj_le_diagP h Nat.prime_five h5
    (E.map (MonoidHom.snd _ _)) (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE _)
  refine ⟨(R₁, R₂), fun x hx => ⟨hR₁ ⟨x, hx, rfl⟩, hR₂ ⟨x, hx, rfl⟩⟩⟩

theorem exists_conj_le_toral [Finite K] (h : UnitaryFieldData ℓ f K) (h5 : 5 ∣ ℓ ^ f + 1)
    (Ew : Subgroup (unitarySU ℓ f K 2 × unitarySU ℓ f K 6)) (hEw : IsElemAbelian 5 Ew)
    (hc : Nat.card Ew = 5 ^ 6) (E : Subgroup (unitarySU ℓ f K 2 × unitarySU ℓ f K 6))
    (hE : IsElemAbelian 5 E) :
    ∃ c : unitarySU ℓ f K 2 × unitarySU ℓ f K 6, E ≤ Ew.map (MulAut.conj c).toMonoidHom := by
  classical
  obtain ⟨P, hP⟩ := exists_le_prod_conj_diagP h h5 Ew hEw
  obtain ⟨R, hR⟩ := exists_le_prod_conj_diagP h h5 E hE
  set D₂ := diagP ℓ f 5 2 K with hD₂
  set D₆ := diagP ℓ f 5 6 K with hD₆
  set Big : Subgroup (unitarySU ℓ f K 2 × unitarySU ℓ f K 6) :=
    (D₂.map (MulAut.conj P.1).toMonoidHom).prod (D₆.map (MulAut.conj P.2).toMonoidHom) with hBig
  have hcard2 : Nat.card D₂ ≤ 5 := by
    simpa using card_diagP_le (ℓ := ℓ) (f := f) (K := K) (p := 5) (n := 2) (by norm_num)
      (by norm_num)
  have hcard6 : Nat.card D₆ ≤ 5 ^ 5 := by
    simpa using card_diagP_le (ℓ := ℓ) (f := f) (K := K) (p := 5) (n := 6) (by norm_num)
      (by norm_num)
  have hBigcard : Nat.card Big ≤ 5 ^ 6 := by
    rw [hBig, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_map_of_injective (MulAut.conj P.1).injective,
      Subgroup.card_map_of_injective (MulAut.conj P.2).injective]
    calc Nat.card D₂ * Nat.card D₆ ≤ 5 * 5 ^ 5 := Nat.mul_le_mul hcard2 hcard6
      _ = 5 ^ 6 := by norm_num
  have hBigeq : Ew = Big := by
    refine Subgroup.eq_of_le_of_card_ge hP ?_
    rw [hc]
    exact hBigcard
  refine ⟨(R.1 * P.1⁻¹, R.2 * P.2⁻¹), fun x hx => ?_⟩
  rw [mem_map_conj_iff, hBigeq, hBig, Subgroup.mem_prod]
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_prod.1 (hR hx)
  rw [mem_map_conj_iff] at hx1 hx2
  refine ⟨?_, ?_⟩
  · rw [mem_map_conj_iff]
    have e1 : P.1⁻¹ * ((R.1 * P.1⁻¹, R.2 * P.2⁻¹)⁻¹ * x * (R.1 * P.1⁻¹, R.2 * P.2⁻¹)).1 * P.1 =
        R.1⁻¹ * x.1 * R.1 := by
      simp only [Prod.fst_mul, Prod.fst_inv]
      group
    rw [e1]
    exact hx1
  · rw [mem_map_conj_iff]
    have e2 : P.2⁻¹ * ((R.1 * P.1⁻¹, R.2 * P.2⁻¹)⁻¹ * x * (R.1 * P.1⁻¹, R.2 * P.2⁻¹)).2 * P.2 =
        R.2⁻¹ * x.2 * R.2 := by
      simp only [Prod.snd_mul, Prod.snd_inv]
      group
    rw [e2]
    exact hx2

theorem exists_conj_le_of_mulEquiv {H H' : Type*} [Group H] [Group H'] (θ : H ≃* H')
    (Ew E : Subgroup H)
    (hc : ∃ c : H', E.map θ.toMonoidHom ≤ (Ew.map θ.toMonoidHom).map (MulAut.conj c).toMonoidHom) :
    ∃ c : H, E ≤ Ew.map (MulAut.conj c).toMonoidHom := by
  obtain ⟨c, hc⟩ := hc
  refine ⟨θ.symm c, fun x hx => ?_⟩
  obtain ⟨_, ⟨y, hy, rfl⟩, hyx⟩ := hc ⟨x, hx, rfl⟩
  refine ⟨y, hy, θ.injective ?_⟩
  simpa [MulAut.conj_apply] using hyx

theorem exists_conj_le_toral_of_equiv [Finite K] (h : UnitaryFieldData ℓ f K)
    (h5 : 5 ∣ ℓ ^ f + 1) {H : Type*} [Group H]
    (θ : H ≃* unitarySU ℓ f K 2 × unitarySU ℓ f K 6) (Ew : Subgroup H)
    (hEw : IsElemAbelian 5 Ew) (hc : Nat.card Ew = 5 ^ 6) (E : Subgroup H)
    (hE : IsElemAbelian 5 E) : ∃ c : H, E ≤ Ew.map (MulAut.conj c).toMonoidHom := by
  refine exists_conj_le_of_mulEquiv θ Ew E ?_
  refine exists_conj_le_toral h h5 (Ew.map θ.toMonoidHom)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hEw _) ?_ (E.map θ.toMonoidHom)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 5 hE _)
  rw [Subgroup.card_map_of_injective θ.injective, hc]

end CFSG.LieType.SeitzGeneration.ExcHigh.TwFive

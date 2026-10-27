module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19USp4Lin
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder

public section

namespace CFSG.QuasithinUnique.Id2519.USp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

section Sylow

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_projSp_two (hF : Nat.card F = 4) :
    Nat.card (StatedProj (StatedSp 2 F)) = 979200 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ UnitaryHigher.proj_bijective_of_charTwo),
    SymplecticFlag.card_statedSp, hF]
  rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  norm_num

@[expose] noncomputable def torusP (F : Type) [Field F] [CharP F 2] :
    Subgroup (StatedProj (StatedSp 2 F)) :=
  (SymplecticTorusWeyl.torus 2 F).map (proj 2 F)

theorem card_torusP (hF : Nat.card F = 4) : Nat.card (torusP F) = 9 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have h1 : Nat.card (SymplecticTorusWeyl.torus 2 F) = Nat.card (Fin 2 → Fˣ) :=
    (Nat.card_congr (MonoidHom.ofInjective (SymplecticTorusWeyl.torusHom_injective
      (r := 2) (k := F))).toEquiv).symm
  have h2 : Nat.card Fˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF]
  rw [torusP, Subgroup.card_map_of_injective UnitaryHigher.proj_bijective_of_charTwo.1, h1,
    Nat.card_fun, h2]
  simp

theorem pow_three_eq_one_of_commute_torusP (hF : Nat.card F = 4) {s : StatedProj (StatedSp 2 F)}
    (hs : ∀ x ∈ torusP F, s * x = x * s) : s ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := proj_surjective s
  have hg : g ^ 3 = 1 := by
    refine pow_three_eq_one_of_commute_torus hF g fun t => ?_
    have h1 := hs (proj 2 F (SymplecticTorusWeyl.torusHom t))
      ⟨_, ⟨t, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact UnitaryHigher.proj_bijective_of_charTwo.1 h1
  rw [← map_pow, hg, map_one]

theorem not_dvd_index_of_card_nine (hF : Nat.card F = 4) {R : Subgroup (StatedProj (StatedSp 2 F))}
    (hR : Nat.card R = 9) : ¬ 3 ∣ R.index := by
  have h := Subgroup.card_mul_index R
  rw [hR, card_projSp_two hF] at h
  have : R.index = 108800 := by omega
  rw [this]
  norm_num

theorem eq_one_of_centralizes_order_nine (hF : Nat.card F = 4)
    {R : Subgroup (StatedProj (StatedSp 2 F))} (hR : Nat.card R = 9)
    {s : StatedProj (StatedSp 2 F)} (hs : s ^ 2 = 1) (hc : ∀ r ∈ R, s * r = r * s) : s = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n := 2) (by rw [hR]; norm_num)
  have hTcard := card_torusP hF
  have hTp : IsPGroup 3 (torusP F) := IsPGroup.of_card (n := 2) (by rw [hTcard]; norm_num)
  have hTi : ¬ 3 ∣ (torusP F).index := not_dvd_index_of_card_nine hF hTcard
  let QR : Sylow 3 (StatedProj (StatedSp 2 F)) := hRp.toSylow (not_dvd_index_of_card_nine hF hR)
  let QT : Sylow 3 (StatedProj (StatedSp 2 F)) := hTp.toSylow hTi
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (StatedProj (StatedSp 2 F)) QR QT
  have h1 : ((x • QR : Sylow 3 _) : Subgroup _) = (torusP F) := by
    rw [hx]
    rfl
  have hxT : ∀ y ∈ torusP F, x⁻¹ * y * x ∈ R := by
    intro y hy
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hy' : x⁻¹ * y * x ∈ (QR : Subgroup (StatedProj (StatedSp 2 F))) := by
      simpa [MulAut.conj_apply] using hy
    exact hy'
  have hsT : ∀ y ∈ torusP F, (x * s * x⁻¹) * y = y * (x * s * x⁻¹) := by
    intro y hy
    have h2 := hc _ (hxT y hy)
    calc x * s * x⁻¹ * y = x * (s * (x⁻¹ * y * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * y * x) * s) * x⁻¹ := by rw [h2]
      _ = y * (x * s * x⁻¹) := by group
  have h3 : (x * s * x⁻¹) ^ 3 = 1 := pow_three_eq_one_of_commute_torusP hF hsT
  have h4 : s ^ 3 = 1 := by
    have : (x * s * x⁻¹) ^ 3 = x * s ^ 3 * x⁻¹ := by
      simp
    rw [this] at h3
    have := congrArg (fun z => x⁻¹ * z * x) h3
    simpa [mul_assoc] using this
  calc s = s ^ 3 * (s ^ 2)⁻¹ := by group
    _ = 1 := by rw [h4, hs]; simp

theorem eq_one_of_centralizes_of_nine_dvd (hF : Nat.card F = 4)
    {Kb : Subgroup (StatedProj (StatedSp 2 F))} (h9 : 9 ∣ Nat.card Kb)
    {s : StatedProj (StatedSp 2 F)} (hs : s ^ 2 = 1) (hc : ∀ k ∈ Kb, s * k = k * s) : s = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R₀, hR₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := Kb) 3 (n := 2)
    (by simpa using h9)
  refine eq_one_of_centralizes_order_nine hF (R := R₀.map Kb.subtype) ?_ hs ?_
  · rw [Subgroup.card_map_of_injective Kb.subtype_injective, hR₀]
    norm_num
  · rintro _ ⟨r, _, rfl⟩
    exact hc _ r.2

end Sylow

end CFSG.QuasithinUnique.Id2519.USp4

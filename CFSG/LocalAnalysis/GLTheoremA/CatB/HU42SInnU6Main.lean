module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Core
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SInnU6Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE81

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.Open Matrix

theorem rhoG_scalY (hK : Nat.card K4 = 4) (c : K4ˣ) (v : Fin 6 → K4) :
    rhoG (HU42S.scalY hK c) v = (c : K4) • v := by
  rw [rhoG_apply]
  have h : ((HU42S.scalY hK c : ↥(StatedSU 6 (2 ^ 1) K4)) : GL (Fin 6) K4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := rfl
  rw [h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  simp [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]

theorem rankFine_u6_aux : RankFine (StatedProj (StatedSU 6 (2 ^ 1) K4)) 27 := by
  intro E T hE hT hTne hET
  by_contra hgt
  push_neg at hgt
  haveI : Finite ↥(StatedSU 6 (2 ^ 1) K4) := HU42S.finite_SU K4
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g.1 g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hEp
  have hn4 : 4 ≤ n := by
    by_contra h
    push_neg at h
    have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨E₀, hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 4)
    (by rw [hn]; exact pow_dvd_pow 3 hn4)
  set E₁ : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K4)) := E₀.map E.subtype with hE₁def
  have hE₁card : Nat.card E₁ = 81 := by
    rw [hE₁def, Subgroup.card_map_of_injective E.subtype_injective, hE₀]
    norm_num
  have hE₁le : ∀ x ∈ E₁, x ∈ E := by
    intro x hx
    obtain ⟨k, _, rfl⟩ := Subgroup.mem_map.1 hx
    exact k.2
  have hE₁comm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    have := hE.1.is_comm.comm ⟨x, hE₁le x hx⟩ ⟨y, hE₁le y hy⟩
    exact congrArg Subtype.val this
  have hE₁exp : ∀ x ∈ E₁, x ^ 3 = 1 := fun x hx => hE.2 x (hE₁le x hx)
  have hN : ∀ e ∈ E₁, ∀ t ∈ T, e * t * e⁻¹ ∈ T := by
    intro e he t ht
    exact (Subgroup.mem_normalizer_iff.1 (hET (hE₁le e he)) t).1 ht
  have hK : Nat.card K4 = 4 := K4_card
  set π := HU42S.projSU (MulEquiv.refl (StatedProj (StatedSU 6 (2 ^ 1) K4))) with hπdef
  have hk : Nat.card π.ker = 3 := HU42S.card_ker_projSU hK (MulEquiv.refl _)
  have hπs : Function.Surjective π := HU42S.projSU_surjective (MulEquiv.refl _)
  have hc : ∀ z ∈ π.ker, ∀ x : ↥(StatedSU 6 (2 ^ 1) K4), x * z = z * x := fun z hz x =>
    Subgroup.mem_center_iff.1 (HU42S.ker_projSU_le_center hK (MulEquiv.refl _) hz) x
  obtain ⟨T₀, hT₀, hT₀ne, hN'⟩ := exists_two_normal hπs hk hc hT hTne hN
  have hPcard : Nat.card (E₁.comap π) = 243 := by
    rw [card_comap_of_surjective hπs, hk, hE₁card]
  have hZ : ∀ z ∈ π.ker, ∃ c : K4, (∀ v, rhoG z v = c • v) ∧ (c = 1 → z = 1) := by
    intro z hz
    have hz' := hz
    rw [hπdef, HU42S.ker_projSU_eq hK (MulEquiv.refl _)] at hz'
    obtain ⟨c, hcz⟩ := MonoidHom.mem_range.1 hz'
    refine ⟨(c : K4), ?_, ?_⟩
    · intro v
      rw [← hcz, rhoG_scalY hK c v]
    · intro h1
      rw [← hcz]
      have hc1 : c = 1 := Units.ext h1
      rw [hc1, map_one]
  have hcube : ∀ x ∈ E₁.comap π, x ^ 3 ∈ π.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, map_pow]
    exact hE₁exp _ hx
  have hcomm2 : ∀ x ∈ E₁.comap π, ∀ y ∈ E₁.comap π, x * y * x⁻¹ * y⁻¹ ∈ π.ker := by
    intro x hx y hy
    rw [MonoidHom.mem_ker]
    have hcx : π x * π y = π y * π x := hE₁comm _ hx _ hy
    simp only [map_mul, map_inv]
    calc π x * π y * (π x)⁻¹ * (π y)⁻¹ = π y * π x * (π x)⁻¹ * (π y)⁻¹ := by rw [hcx]
      _ = 1 := by group
  exact core_false (E₁.comap π) T₀ π.ker hPcard hZ hcube hcomm2 hT₀ hT₀ne hN'

theorem rankFine_u6 : RankFine (StatedProj (StatedSU 6 2 K4)) 27 := rankFine_u6_aux

end CFSG.LocalAnalysis.GLTheoremA.CatB.InnU6

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.LocalAnalysis.GLTheoremA.CatB CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem u42E81InnU6At_holds : U42E81InnU6At := by
  intro S _ _ hS
  obtain ⟨q, hv, hq2, ⟨e0⟩⟩ := U62RankSound.lieIndex_isU6two hS
  obtain ⟨e1⟩ := nonempty_equiv_timmesfeldPSU 5 q hv hq2 e0
  exact RankFine.of_mulEquiv (e1.trans (CFSG.GF2Type.timmesfeldPSUEquivStatedProj 6))
    InnU6.rankFine_u6

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.InvolutionFusion
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Confinement
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOne

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.TwoRankLowerBound.Helpers

universe u v

variable {G : Type u} [Group G] {Ω : Type v} [MulAction G Ω]

theorem orderOf_mul_mul_inv (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa only [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq x

theorem exists_conj_interchange [FaithfulSMul G Ω] [MulAction.IsMultiplyPretransitive G Ω 2]
    {α β : Ω} (hαβ : α ≠ β) {v : G} (hv : orderOf v = 2) :
    ∃ h : G, (h * v * h⁻¹) • α = β ∧ (h * v * h⁻¹) • β = α := by
  have hv1 : v ≠ 1 := fun h => by simp [h] at hv
  obtain ⟨γ, hγ⟩ : ∃ γ : Ω, v • γ ≠ γ := by
    by_contra hall
    push Not at hall
    exact hv1 (FaithfulSMul.eq_of_smul_eq_smul fun ω => (hall ω).trans (one_smul G ω).symm)
  obtain ⟨h, hhγ, hhδ⟩ :=
    (MulAction.is_two_pretransitive_iff (G := G) (α := Ω)).mp inferInstance hγ.symm hαβ
  have hvv : v * v = 1 := by rw [← pow_two, ← hv, pow_orderOf_eq_one]
  have hhα : h⁻¹ • α = γ := by rw [← hhγ, inv_smul_smul]
  have hhβ : h⁻¹ • β = v • γ := by rw [← hhδ, inv_smul_smul]
  refine ⟨h, ?_, ?_⟩
  · rw [mul_smul, mul_smul, hhα, hhδ]
  · rw [mul_smul, mul_smul, hhβ, ← mul_smul v v, hvv, one_smul, hhγ]

theorem exists_common_fixed_point [Finite Ω] (hodd : Odd (Nat.card Ω)) {x y : G}
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : Commute x y) :
    ∃ ω : Ω, x • ω = ω ∧ y • ω = ω := by
  have hxTwo : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hyTwo : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (hxy.symm.zpow_left n).eq
  obtain ⟨ω, hω⟩ :=
    (hxTwo.to_sup_of_normal_right' hyTwo hxN).nonempty_fixed_point_of_prime_not_dvd_card Ω
      (fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h))
  exact ⟨ω, hω ⟨x, Subgroup.mem_sup_left (Subgroup.mem_zpowers x)⟩,
    hω ⟨y, Subgroup.mem_sup_right (Subgroup.mem_zpowers y)⟩⟩

theorem exists_conj_commute_of_rank_one [Finite G] {B : Subgroup G}
    (hB : CFSG.Open.pRank 2 B ≤ 1) {u : G} (huB : u ∈ B) (hu : orderOf u = 2) {y : G}
    (hy : orderOf y = 2) (hyB : y ∈ Subgroup.normalizer (B : Set G)) :
    ∃ b ∈ B, Commute (b * y * b⁻¹) u := by
  classical
  have hyTwo : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  obtain ⟨P, hP⟩ := CFSG.PreuniquenessRankFour.Helpers.exists_normalized_same_prime_sylow 2
    hyTwo (Subgroup.zpowers_le.mpr hyB)
  let uB : B := ⟨u, huB⟩
  have huBorder : orderOf uB = 2 := (Subgroup.orderOf_coe uB).symm.trans hu
  have hBeven : Even (Nat.card B) := even_iff_two_dvd.mpr (huBorder ▸ orderOf_dvd_natCard uB)
  have hBrank : twoRank B ≤ 1 := by
    rw [twoRank, ← pRank_subgroup_eq_internal_top 2 (by decide)]
    exact hB
  obtain ⟨w, hwP, hw, hwuniq⟩ := exists_unique_involution_of_rank_one_sylow B hBeven hBrank P
  have hyw : y * w = w * y := by
    have hmem : y * (w : G) * y⁻¹ ∈ (P : Subgroup B).map B.subtype :=
      (Subgroup.mem_normalizer_iff.mp (hP (Subgroup.mem_zpowers y)) (w : G)).mp
        (Subgroup.mem_map_of_mem B.subtype hwP)
    obtain ⟨w', hw'P, hw'⟩ := Subgroup.mem_map.mp hmem
    have hw'order : orderOf w' = 2 := by
      rw [← Subgroup.orderOf_coe]
      change orderOf (B.subtype w') = 2
      rw [hw', orderOf_mul_mul_inv, Subgroup.orderOf_coe, hw]
    have hconj : y * (w : G) * y⁻¹ = w := by
      rw [← hw', hwuniq w' hw'P hw'order]
      rfl
    calc y * w = y * w * y⁻¹ * y := by group
      _ = w * y := by rw [hconj]
  obtain ⟨b, -, hb⟩ := involution_conjugate_into_sylow P ⊤ le_top uB trivial huBorder
  have hbw : b⁻¹ * uB * b = w := hwuniq _ hb (by
    simpa only [MulAut.conj_apply, inv_inv, huBorder] using (MulAut.conj b⁻¹).orderOf_eq uB)
  have hu_eq : u = b * w * (b : G)⁻¹ := by
    have h := congrArg Subtype.val hbw
    change (b : G)⁻¹ * u * b = w at h
    rw [← h]
    group
  refine ⟨b, b.property, ?_⟩
  change b * y * (b : G)⁻¹ * u = u * (b * y * (b : G)⁻¹)
  rw [hu_eq]
  calc b * y * (b : G)⁻¹ * (b * w * (b : G)⁻¹) = b * (y * w) * (b : G)⁻¹ := by group
    _ = b * (w * y) * (b : G)⁻¹ := by rw [hyw]
    _ = b * w * (b : G)⁻¹ * (b * y * (b : G)⁻¹) := by group

theorem odd_degree_rank_one_pair_centralizer_meets_involution_classes [Finite G] [Finite Ω]
    [FaithfulSMul G Ω] [MulAction.IsMultiplyPretransitive G Ω 2] (hodd : Odd (Nat.card Ω))
    {α β : Ω} (hαβ : α ≠ β)
    (hrank : CFSG.Open.pRank 2 (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 1)
    {u : G} (huB : u ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β)
    (hu : orderOf u = 2)
    (htransitive : ∀ γ δ : Ω, u • γ = γ → u • δ = δ →
      ∃ c ∈ Subgroup.centralizer ({u} : Set G), c • γ = δ)
    (T : Sylow 2 ↥(Subgroup.centralizer ({u} : Set G) ⊓ MulAction.stabilizer G α))
    (v : G) (hv : orderOf v = 2) :
    ∃ g : G, g⁻¹ * v * g ∈ (T : Subgroup _).map
      (Subgroup.centralizer ({u} : Set G) ⊓ MulAction.stabilizer G α).subtype := by
  classical
  let B := MulAction.stabilizer G α ⊓ MulAction.stabilizer G β
  let D := Subgroup.centralizer ({u} : Set G) ⊓ MulAction.stabilizer G α
  obtain ⟨h, hα, hβ⟩ := exists_conj_interchange hαβ hv
  set y := h * v * h⁻¹ with hy
  have hyorder : orderOf y = 2 := (orderOf_mul_mul_inv h v).trans hv
  have hyy : y * y = 1 := by rw [← pow_two, ← hyorder, pow_orderOf_eq_one]
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyB : y ∈ Subgroup.normalizer (B : Set G) := by
    have key : ∀ x ∈ B, y * x * y⁻¹ ∈ B := by
      intro x hx
      obtain ⟨hxα, hxβ⟩ := Subgroup.mem_inf.mp hx
      rw [MulAction.mem_stabilizer_iff] at hxα hxβ
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩ <;>
        rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hyinv]
      · rw [hα, hxβ, hβ]
      · rw [hβ, hxα, hα]
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨key x, fun hx => ?_⟩
    have hxeq : y * (y * x * y⁻¹) * y⁻¹ = x := by
      rw [hyinv]
      calc y * (y * x * y) * y = (y * y) * x * (y * y) := by group
        _ = x := by rw [hyy, one_mul, mul_one]
    simpa only [hxeq] using key _ hx
  obtain ⟨b, -, hbu⟩ := exists_conj_commute_of_rank_one hrank.le huB hu hyorder hyB
  set y₂ := b * y * b⁻¹ with hy₂
  have hy₂order : orderOf y₂ = 2 := (orderOf_mul_mul_inv b y).trans hyorder
  obtain ⟨γ, huγ, hy₂γ⟩ := exists_common_fixed_point hodd hu hy₂order hbu.symm
  obtain ⟨c, hcC, hcγ⟩ := htransitive γ α huγ (Subgroup.mem_inf.mp huB).1
  set y₃ := c * y₂ * c⁻¹ with hy₃
  have hy₃D : y₃ ∈ D := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have hcu : Commute c u := Subgroup.mem_centralizer_singleton_iff.mp hcC
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((hcu.mul_left hbu).mul_left hcu.inv_left).eq
    · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hcγ, inv_smul_smul, hy₂γ]
  have hy₃order : orderOf (⟨y₃, hy₃D⟩ : D) = 2 :=
    (Subgroup.orderOf_mk y₃ hy₃D).trans ((orderOf_mul_mul_inv c y₂).trans hy₂order)
  obtain ⟨d, -, hd⟩ := involution_conjugate_into_sylow T ⊤ le_top _ trivial hy₃order
  refine ⟨h⁻¹ * b⁻¹ * c⁻¹ * d, ?_⟩
  convert Subgroup.mem_map_of_mem D.subtype hd using 1
  change _ = (d : G)⁻¹ * y₃ * d
  rw [hy₃, hy₂, hy]
  group

end CFSG.ProperTwoGeneratedCore.RankOnePair

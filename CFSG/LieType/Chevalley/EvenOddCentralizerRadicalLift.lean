module

public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalOpposite
public import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing

public noncomputable section

namespace CFSG.LieType.Chevalley.EvenOddRadical

open CFSG.Blueprint.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem exists_level
    {J : Set (Fin τ.rank)} {u : ModGL τ K}
    (hu : u ∈ parabolicRadical τ K J) (hu1 : u ≠ 1) :
    ∃ n : ℕ, u ∈ levelRadical τ K J (n + 1) ∧ u ∉ levelRadical τ K J (n + 1 + 1) := by
  classical
  obtain ⟨D, hD⟩ := exists_levelRoots_eq_empty (τ := τ) J
  have hex : ∃ m : ℕ, u ∉ levelRadical τ K J ((m : ℤ) + 1) := by
    refine ⟨D.toNat, fun h => hu1 ?_⟩
    rw [levelRadical_eq_bot (hD _ (by omega))] at h
    exact Subgroup.mem_bot.1 h
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, Nat.cast_zero, zero_add, levelRadical_one] at this
    exact this hu
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨n, not_not.1 (Nat.find_min hex (by omega)), ?_⟩
  have := Nat.find_spec hex
  rw [hn] at this
  push_cast at this
  exact this

theorem units_inv_apply_apply (g : ModGL τ K) (y : RootModule τ K) :
    (↑g⁻¹ : Module.End K (RootModule τ K)) ((g : Module.End K (RootModule τ K)) y) = y := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem isPGroup_levelRadical
    [Finite K] [CharP K 2] (J : Set (Fin τ.rank)) (d : ℤ) :
    IsPGroup 2 (levelRadical τ K J d) :=
  (isPGroup_posUnipotent 2 τ).to_le (levelRadical_le_posUnipotent J d)

theorem exists_fixed_mem_oppRadical
    [Finite K] [CharP K 2]
    (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {J : Set (Fin τ.rank)}
    {S : Subgroup (ModGL τ K)} (hSM : S ≤ parabolicLevi τ K J) (hodd : Odd (Nat.card S))
    {u : ModGL τ K} (hu : u ∈ parabolicRadical τ K J) (hu1 : u ≠ 1)
    (hfix : ∀ s ∈ S, s * u * s⁻¹ = u) :
    ∃ v ∈ oppRadical τ K J, v ≠ 1 ∧ ∀ s ∈ S, s * v * s⁻¹ = v := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_modGL (τ := τ) (K := K)
  obtain ⟨n, hun, hun'⟩ := exists_level hu hu1
  obtain ⟨x, hx, hx0, hxS⟩ := exists_fixed_vector_of_fixed hτ h2 J n hSM hun hun' hfix
  obtain ⟨y, hy, hy0, hyS⟩ := exists_fixed_neg_of_fixed hτ h2 J n hSM hodd hx hx0 hxS
  obtain ⟨w₀, δ, hinj, hδ, hsq, h₀⟩ := exists_longest τ
  set n₀ := canonicalRep (coxeterSystem τ) K w₀ with hn₀
  set S' := S.map (MulAut.conj n₀).toMonoidHom with hS'
  have hS'M : S' ≤ parabolicLevi τ K (δ '' J) :=
    (Subgroup.map_mono hSM).trans (map_conj_parabolicLevi_le hδ J)
  have hx' : (n₀ : Module.End K (RootModule τ K)) y ∈ parabolicGraded τ K (δ '' J) (n + 1) :=
    longest_mem_parabolicGraded hinj hδ J (n + 1) hy
  have hx'0 : (n₀ : Module.End K (RootModule τ K)) y ≠ 0 := fun h => hy0 (by
    rw [← units_inv_apply_apply n₀ y, h, map_zero])
  have hx'S : ∀ s ∈ S', (s : Module.End K (RootModule τ K))
      ((n₀ : Module.End K (RootModule τ K)) y) = (n₀ : Module.End K (RootModule τ K)) y := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Units.val_mul, Module.End.mul_apply,
      units_inv_apply_apply, hyS s hs]
  obtain ⟨u', hu', hu'', hcos⟩ :=
    exists_invariant_coset_of_fixed_vector hτ h2 (δ '' J) n hS'M hx' hx'0 hx'S
  have hN1 : S' ≤ Subgroup.normalizer (levelRadical τ K (δ '' J) (n + 1) : Set (ModGL τ K)) :=
    hS'M.trans (parabolicLevi_le_normalizer _ (one_le_succ n))
  have hN2 : S' ≤ Subgroup.normalizer
      (levelRadical τ K (δ '' J) (n + 1 + 1) : Set (ModGL τ K)) :=
    hS'M.trans (parabolicLevi_le_normalizer _ (one_le_succ_succ n))
  let _ : MulDistribMulAction S' (levelRadical τ K (δ '' J) (n + 1)) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer S' _ hN1
  have hinv : CFSG.IsInvariant S' (levelRadical τ K (δ '' J) (n + 1))
      ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1))) :=
    CFSG.SolvableHall.isInvariant_of_forall_smul_mem fun a z hz => by
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      exact (Subgroup.mem_normalizer_iff.1 (hN2 a.2) z).1 hz
  have hp : IsPGroup 2 ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) :=
    (isPGroup_levelRadical (δ '' J) (n + 1 + 1)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (levelRadical_succ_le (δ '' J) (n + 1))).symm
  have hsolv : Group.IsSolvable ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
      (levelRadical τ K (δ '' J) (n + 1))) := by
    have := hp.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card S')
      (Nat.card ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf
        (levelRadical τ K (δ '' J) (n + 1)))) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
    rw [hk, hS', Subgroup.card_map_of_injective (MulAut.conj n₀).injective]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  obtain ⟨c, hc, hcu⟩ := CFSG.SolvableHall.exists_fixed_of_coset_fixed
    ((levelRadical τ K (δ '' J) (n + 1 + 1)).subgroupOf (levelRadical τ K (δ '' J) (n + 1)))
    hinv hsolv hcop ⟨u', hu'⟩ fun b => by
      rw [Subgroup.mem_subgroupOf]
      exact hcos b b.2
  have hcN : (c : ModGL τ K) ∉ levelRadical τ K (δ '' J) (n + 1 + 1) := fun h => hu'' (by
    have h' := Subgroup.mem_subgroupOf.1 hcu
    have e : u' = (c : ModGL τ K) * ((c⁻¹ * ⟨u', hu'⟩ : levelRadical τ K (δ '' J) (n + 1)) :
      ModGL τ K) := by simp
    rw [e]
    exact mul_mem h h')
  refine ⟨n₀⁻¹ * c * n₀, ?_, fun h => hcN ?_, fun s hs => ?_⟩
  · have hcQ : (c : ModGL τ K) ∈ parabolicRadical τ K (δ '' J) :=
      levelRadical_le_parabolicRadical _ (one_le_succ n) c.2
    have := map_conj_longest_parabolicRadical_le (K := K) hinj hδ hsq h₀ J
      (Subgroup.mem_map_of_mem _ hcQ)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using this
  · have e : (c : ModGL τ K) = n₀ * (n₀⁻¹ * c * n₀) * n₀⁻¹ := by group
    rw [e, h, mul_one, mul_inv_cancel]
    exact one_mem _
  · have hcs := congrArg Subtype.val (hc ⟨n₀ * s * n₀⁻¹, ⟨s, hs, rfl⟩⟩)
    change n₀ * s * n₀⁻¹ * (c : ModGL τ K) * (n₀ * s * n₀⁻¹)⁻¹ = c at hcs
    calc s * (n₀⁻¹ * c * n₀) * s⁻¹ =
        n₀⁻¹ * (n₀ * s * n₀⁻¹ * (c : ModGL τ K) * (n₀ * s * n₀⁻¹)⁻¹) * n₀ := by group
      _ = n₀⁻¹ * c * n₀ := by rw [hcs]

end CFSG.LieType.Chevalley.EvenOddRadical

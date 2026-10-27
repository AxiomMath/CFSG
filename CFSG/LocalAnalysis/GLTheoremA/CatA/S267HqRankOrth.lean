module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267HqRankLift
public import CFSG.RankThree.PartOne.S11c.OrthogonalCore
public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Solomon.Coordinator

section Abstract

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

private theorem iSupIndep_zpowers_of_two {G : Type*} [Group G] {ι : Type*} (y : ι → G)
    (hy : ∀ i, orderOf (y i) = 2)
    (h : ∀ j, y j ∉ ⨆ (i : ι) (_ : i ≠ j), Subgroup.zpowers (y i)) :
    iSupIndep fun i => Subgroup.zpowers (y i) := by
  rw [iSupIndep_def]
  intro j
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hx, hxs⟩
  rw [mem_bot]
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  have hk : (y j) ^ k = (y j) ^ (k % 2) := by
    rw [← zpow_mod_orderOf, hy j]
    norm_num
  rw [hk] at hxs ⊢
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero]
  · rw [h1, zpow_one] at hxs
    exact absurd hxs (h j)

theorem orth_large_witness [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hV9 : 9 ≤ Module.finrank K V) (hB : (polarBilin Q).Nondegenerate) :
    (∃ E : Subgroup (ProjOrthDerived Q), IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 7) ∧
      ∃ S E : Subgroup (ProjOrthDerived Q), IsPGroup 2 S ∧ S ≠ ⊥ ∧
        E ≤ normalizer (S : Set (ProjOrthDerived Q)) ∧ IsElemAbelian p E ∧
          Nat.card E = p ^ 6 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp2)
  have hKodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have hKodd' : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hKodd
  have : Finite V := Module.finite_of_finite K
  set d := Module.finrank K V with hd
  obtain ⟨vb, hvo, hv1, -⟩ := CFSG.RankThree.Classical.exists_orthogonal_basis_quad_eq hKodd
    hd.symm (by omega) Q hB one_ne_zero
  set v : Fin 8 → V := fun i => vb ⟨i, by omega⟩ with hvdef
  set w₈ : V := vb ⟨8, by omega⟩ with hw₈def
  have hvinj : ∀ i j : Fin 8, (⟨i, by omega⟩ : Fin d) = ⟨j, by omega⟩ → i = j := fun i j h =>
    Fin.ext (by simpa using congrArg Fin.val h)
  have hQv : ∀ i, Q (v i) = 1 := fun i => hv1 _ (by simp; omega)
  have hpvv : ∀ i j, i ≠ j → polar Q (v i) (v j) = 0 := fun i j hij =>
    hvo _ _ fun h => hij (hvinj i j h)
  have hpvw : ∀ i, polar Q (v i) w₈ = 0 := fun i =>
    hvo _ _ fun h => by have := congrArg Fin.val h; simp at this; omega
  have hpol : ∀ i j, polar Q (v i) (v j) = if i = j then 2 else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      rw [polar_self_eq_two_mul, hQv, mul_one]
    · exact hpvv i j hij
  have hv0 : ∀ i, v i ≠ 0 := fun i h0 => by
    have := hQv i
    rw [h0, QuadraticMap.map_zero] at this
    exact zero_ne_one this
  have hw0 : w₈ ≠ 0 := vb.ne_zero _
  set Ω := orthDerived Q with hΩdef
  set Zs := (scalars K V).subgroupOf Ω with hZsdef
  set ρ := QuotientGroup.mk' Zs with hρdef
  have hnotsc : ∀ g : Ω, (g : V ≃ₗ[K] V) w₈ = w₈ → ∀ u, u ≠ 0 → (g : V ≃ₗ[K] V) u = -u →
      ρ g ≠ 1 := by
    intro g hgw u hu hgu hg1
    have hmem := (QuotientGroup.eq_one_iff (N := Zs) g).mp hg1
    rw [hZsdef, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    have hc1 : c = 1 := by
      have h1 := hc w₈
      rw [hgw] at h1
      have h1' : (c - 1) • w₈ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h1' with h1' | h1'
      · exact sub_eq_zero.mp h1'
      · exact absurd h1' hw0
    have h2u := hc u
    rw [hgu, hc1, one_smul] at h2u
    have : (2 : K) • u = 0 := by rw [two_smul]; nth_rewrite 1 [← h2u]; exact neg_add_cancel u
    rcases smul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hu h'
  have hds : ∀ i j : Fin 8, i ≠ j → ∃ g ∈ Ω, g (v i) = -v i ∧ g (v j) = -v j ∧
      ∀ x, polar Q (v i) x = 0 → polar Q (v j) x = 0 → g x = x := fun i j hij =>
    exists_mem_orthDerived_double_sign h2 (hQv i) (hQv j) (hpvv i j hij)
  have hj1 : ∀ j : Fin 7, (0 : Fin 8) ≠ j.succ := fun j h => by
    have := congrArg Fin.val h
    simp at this
  choose ε hεΩ hε0 hεj hεx using fun j : Fin 7 => hds 0 j.succ (hj1 j)
  have hεv : ∀ (j : Fin 7) (k : Fin d), ε j (vb k) = vb k ∨ ε j (vb k) = -vb k := by
    intro j k
    by_cases hk0 : k = ⟨0, by omega⟩
    · subst hk0
      exact Or.inr (hε0 j)
    by_cases hkj : k = ⟨j.succ, by omega⟩
    · subst hkj
      exact Or.inr (hεj j)
    · left
      refine hεx j (vb k) (hvo _ _ fun h => hk0 h.symm) (hvo _ _ fun h => hkj h.symm)
  have hεsq : ∀ j, ε j * ε j = 1 := by
    intro j
    refine LinearEquiv.toLinearMap_injective (vb.ext fun k => ?_)
    change ε j (ε j (vb k)) = vb k
    rcases hεv j k with h | h
    · rw [h, h]
    · rw [h, map_neg, h, neg_neg]
  have hεcomm : ∀ i j, ε i * ε j = ε j * ε i := by
    intro i j
    refine LinearEquiv.toLinearMap_injective (vb.ext fun k => ?_)
    change ε i (ε j (vb k)) = ε j (ε i (vb k))
    rcases hεv i k with hi | hi <;> rcases hεv j k with hj | hj <;>
      simp only [hi, hj, map_neg, neg_neg]
  have hεw : ∀ j, ε j w₈ = w₈ := fun j =>
    hεx j w₈ (hpvw 0) (hpvw _)
  set y : Fin 7 → ProjOrthDerived Q := fun j => ρ ⟨ε j, hεΩ j⟩ with hydef
  have hy2 : ∀ j, y j ^ 2 = 1 := by
    intro j
    rw [hydef, ← map_pow]
    have : (⟨ε j, hεΩ j⟩ : Ω) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact hεsq j)
    rw [this, map_one]
  have hy1 : ∀ j, y j ≠ 1 := fun j =>
    hnotsc ⟨ε j, hεΩ j⟩ (hεw j) _ (hv0 _) (hεj j)
  have hyo : ∀ j, orderOf (y j) = 2 := fun j =>
    orderOf_eq_prime (hy2 j) (hy1 j)
  have hycomm : ∀ i j, y i * y j = y j * y i := by
    intro i j
    rw [hydef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hεcomm i j)
  have hyind : iSupIndep fun j => Subgroup.zpowers (y j) := by
    refine iSupIndep_zpowers_of_two y hyo fun j hj => ?_
    set St : Subgroup Ω := {
      carrier := {g | (g : V ≃ₗ[K] V) (v j.succ) = v j.succ ∧
        (g : V ≃ₗ[K] V) w₈ = w₈}
      one_mem' := ⟨rfl, rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨by
          change (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) _) = _
          rw [hb.1, ha.1], by
          change (a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) _) = _
          rw [hb.2, ha.2]⟩
      inv_mem' := fun {a} ha => ⟨by
          change (a : V ≃ₗ[K] V).symm _ = _
          rw [LinearEquiv.symm_apply_eq, ha.1], by
          change (a : V ≃ₗ[K] V).symm _ = _
          rw [LinearEquiv.symm_apply_eq, ha.2]⟩ } with hSt
    have hle : (⨆ (i : Fin 7) (_ : i ≠ j), Subgroup.zpowers (y i)) ≤ St.map ρ := by
      refine iSup₂_le fun i hij => ?_
      rw [zpowers_le]
      refine ⟨⟨ε i, hεΩ i⟩, ⟨?_, hεw i⟩, rfl⟩
      have hne : (0 : Fin 8) ≠ j.succ := hj1 j
      have hne' : i.succ ≠ j.succ := fun h => hij (by
        have := congrArg Fin.val h
        simp at this
        exact Fin.ext this)
      exact hεx i _ (hpvv _ _ hne) (hpvv _ _ hne')
    obtain ⟨g, hgSt, hgy⟩ := hle hj
    have hmem : g⁻¹ * ⟨ε j, hεΩ j⟩ ∈ Zs := by
      rw [← QuotientGroup.eq]
      exact hgy
    rw [hZsdef, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨c, hc⟩ := mem_scalars.mp hmem
    have hgw : (g : V ≃ₗ[K] V).symm w₈ = w₈ := by
      rw [LinearEquiv.symm_apply_eq, hgSt.2]
    have hc1 : c = 1 := by
      have h1 := hc w₈
      change (g : V ≃ₗ[K] V).symm (ε j w₈) = c • w₈ at h1
      rw [hεw, hgw] at h1
      have h1' : (c - 1) • w₈ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
      rcases smul_eq_zero.mp h1' with h1' | h1'
      · exact sub_eq_zero.mp h1'
      · exact absurd h1' hw0
    have hgv : (g : V ≃ₗ[K] V).symm (v j.succ) = v j.succ := by
      rw [LinearEquiv.symm_apply_eq, hgSt.1]
    have h3 := hc (v j.succ)
    change (g : V ≃ₗ[K] V).symm (ε j _) = c • _ at h3
    rw [hεj, map_neg, hc1, one_smul, hgv] at h3
    have : (2 : K) • v j.succ = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h3]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp this with h' | h'
    · exact h2 h'
    · exact hv0 _ h'
  obtain ⟨hE2, hE2c⟩ := i1020_family y hyo (fun i j _ => hycomm i j) hyind
  refine ⟨⟨_, hE2, by rw [hE2c, Fintype.card_fin]⟩, ?_⟩
  obtain ⟨x, yy, hxy⟩ := CFSG.SectionRank.OddCover.exists_sq_add_sq hKodd' (-1 : K)
  set c : K := 2⁻¹ with hcdef
  have hc : 2 * c = 1 := mul_inv_cancel₀ h2
  set e : V := x • v 0 + yy • v 1 + v 2 with hedef
  set h : V := c • v 2 - c ^ 2 • e with hhdef
  set d₀ : V := yy • v 0 - x • v 1 with hd₀def
  have hQa : Q (x • v 0 + yy • v 1) = x ^ 2 + yy ^ 2 := by
    rw [CFSG.RankThree.Classical.quad_smul_add_smul Q (by rw [hpol]; simp), hQv, hQv]
    ring
  have hpa : ∀ j, polar Q (x • v 0 + yy • v 1) (v j) =
      x * (if (0 : Fin 8) = j then 2 else 0) + yy * (if (1 : Fin 8) = j then 2 else 0) := by
    intro j
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hpol, hpol]
  have hev : ∀ j, polar Q e (v j) =
      x * (if (0 : Fin 8) = j then 2 else 0) + yy * (if (1 : Fin 8) = j then 2 else 0) +
        (if (2 : Fin 8) = j then 2 else 0) := by
    intro j
    rw [hedef, polar_add_left, hpa, hpol]
  have he : Q e = 0 := by
    rw [hedef, QuadraticMap.map_add Q, hQa, hQv, hpa]
    simp only [Fin.reduceEq, ite_false, mul_zero, add_zero]
    linear_combination hxy
  have hee : polar Q e e = 0 := polar_self_eq_zero he
  have hev2 : polar Q e (v 2) = 2 := by
    rw [hev]
    simp
  have hh : Q h = 0 := by
    have hpve : polar Q (v 2) e = 2 := by rw [polar_comm, hev2]
    rw [hhdef, sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q, QuadraticMap.map_smul,
      QuadraticMap.map_smul, hQv, he, polar_smul_left_eq, polar_smul_right_eq, hpve,
      smul_eq_mul, smul_eq_mul]
    linear_combination (-c ^ 2) * hc
  have heh : polar Q e h = 1 := by
    rw [hhdef, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hev2, hee]
    linear_combination hc
  let fD : Fin 6 → V := ![d₀, v 3, v 4, v 5, v 6, v 7]
  have hQd₀ : Q d₀ = -1 := by
    rw [hd₀def, sub_eq_add_neg, ← neg_smul,
      CFSG.RankThree.Classical.quad_smul_add_smul Q (by rw [hpol]; simp), hQv, hQv]
    linear_combination hxy
  have hd₀v : ∀ j : Fin 8, 3 ≤ (j : ℕ) → polar Q d₀ (v j) = 0 := by
    intro j hj
    have h0 : (0 : Fin 8) ≠ j := fun h' => by rw [← h'] at hj; simp at hj
    have h1 : (1 : Fin 8) ≠ j := fun h' => by rw [← h'] at hj; simp at hj
    rw [hd₀def, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hpol, hpol]
    simp [h0, h1]
  have hed₀ : polar Q e d₀ = 0 := by
    rw [hd₀def, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hev, hev]
    simp
    ring
  have hv2d₀ : polar Q (v 2) d₀ = 0 := by
    rw [hd₀def, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hpol, hpol]
    simp
  have hfo : ∀ i j, i ≠ j → polar Q (fD i) (fD j) = 0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij <;>
      simp [fD, hpol, hd₀v, polar_comm Q _ d₀]
  have hfQ : ∀ i, Q (fD i) ≠ 0 := by
    intro i
    fin_cases i <;> simp [fD, hQd₀, hQv]
  obtain ⟨hfli, hDreg⟩ := CFSG.RankThree.Classical.nondegenerate_restrict_span h2 Q hfo hfQ
  set D := Submodule.span K (Set.range fD) with hDdef
  have hDdim : Module.finrank K D = 6 := by
    rw [hDdef, finrank_span_eq_card hfli, Fintype.card_fin]
  have hspan_ker : ∀ a : V, (∀ i, polar Q a (fD i) = 0) → ∀ w ∈ D, polar Q a w = 0 := by
    intro a ha w hw
    have hle : D ≤ LinearMap.ker ((polarBilin Q) a) := by
      rw [hDdef, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, polarBilin_apply_apply]
      exact ha i
    have := hle hw
    rwa [LinearMap.mem_ker, polarBilin_apply_apply] at this
  have hfe : ∀ i, polar Q e (fD i) = 0 := by
    intro i
    fin_cases i
    · exact hed₀
    all_goals
      show polar Q e (v _) = 0
      rw [hev]
      simp
  have hfv2 : ∀ i, polar Q (v 2) (fD i) = 0 := by
    intro i
    fin_cases i
    · exact hv2d₀
    all_goals
      show polar Q (v 2) (v _) = 0
      rw [hpol]
      simp
  have hDe : ∀ w ∈ D, polar Q e w = 0 := hspan_ker e hfe
  have hDh : ∀ w ∈ D, polar Q h w = 0 := by
    intro w hw
    rw [hhdef, polar_sub_left, polar_smul_left_eq, polar_smul_left_eq, hDe w hw,
      hspan_ker (v 2) hfv2 w hw, mul_zero, mul_zero, sub_zero]
  obtain ⟨U₀, hU₀, hU₀Ω, -, hUab, hUcard, -⟩ :=
    CFSG.RankThree.PartOne.orthogonal_isotropic_line_unipotent_core_odd.{0, 0, 0} hp hp2 hK Q he
      hh heh
      hDe hDh hDreg hDdim (by norm_num)
  obtain ⟨ε₀, hε₀Ω, hε₀a, hε₀b, hε₀x⟩ := hds 0 1 (by decide)
  obtain ⟨ε₁, hε₁Ω, hε₁a, hε₁b, hε₁x⟩ := hds 2 3 (by decide)
  obtain ⟨ε₂, hε₂Ω, hε₂a, hε₂b, hε₂x⟩ := hds 4 5 (by decide)
  obtain ⟨ε₃, hε₃Ω, hε₃a, hε₃b, hε₃x⟩ := hds 6 7 (by decide)
  set z₀ : V ≃ₗ[K] V := ε₀ * ε₁ * ε₂ * ε₃ with hz₀def
  have hz₀Ω : z₀ ∈ Ω := mul_mem (mul_mem (mul_mem hε₀Ω hε₁Ω) hε₂Ω) hε₃Ω
  have hzv : ∀ i, z₀ (v i) = -v i := by
    intro i
    rw [hz₀def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    fin_cases i
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 0)))) = -v 0
      rw [hε₃x _ (hpvv 6 0 (by decide)) (hpvv 7 0 (by decide)),
        hε₂x _ (hpvv 4 0 (by decide)) (hpvv 5 0 (by decide)),
        hε₁x _ (hpvv 2 0 (by decide)) (hpvv 3 0 (by decide)), hε₀a]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 1)))) = -v 1
      rw [hε₃x _ (hpvv 6 1 (by decide)) (hpvv 7 1 (by decide)),
        hε₂x _ (hpvv 4 1 (by decide)) (hpvv 5 1 (by decide)),
        hε₁x _ (hpvv 2 1 (by decide)) (hpvv 3 1 (by decide)), hε₀b]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 2)))) = -v 2
      rw [hε₃x _ (hpvv 6 2 (by decide)) (hpvv 7 2 (by decide)),
        hε₂x _ (hpvv 4 2 (by decide)) (hpvv 5 2 (by decide)), hε₁a, map_neg,
        hε₀x _ (hpvv 0 2 (by decide)) (hpvv 1 2 (by decide))]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 3)))) = -v 3
      rw [hε₃x _ (hpvv 6 3 (by decide)) (hpvv 7 3 (by decide)),
        hε₂x _ (hpvv 4 3 (by decide)) (hpvv 5 3 (by decide)), hε₁b, map_neg,
        hε₀x _ (hpvv 0 3 (by decide)) (hpvv 1 3 (by decide))]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 4)))) = -v 4
      rw [hε₃x _ (hpvv 6 4 (by decide)) (hpvv 7 4 (by decide)), hε₂a, map_neg, map_neg,
        hε₁x _ (hpvv 2 4 (by decide)) (hpvv 3 4 (by decide)),
        hε₀x _ (hpvv 0 4 (by decide)) (hpvv 1 4 (by decide))]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 5)))) = -v 5
      rw [hε₃x _ (hpvv 6 5 (by decide)) (hpvv 7 5 (by decide)), hε₂b, map_neg, map_neg,
        hε₁x _ (hpvv 2 5 (by decide)) (hpvv 3 5 (by decide)),
        hε₀x _ (hpvv 0 5 (by decide)) (hpvv 1 5 (by decide))]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 6)))) = -v 6
      rw [hε₃a, map_neg, map_neg, map_neg,
        hε₂x _ (hpvv 4 6 (by decide)) (hpvv 5 6 (by decide)),
        hε₁x _ (hpvv 2 6 (by decide)) (hpvv 3 6 (by decide)),
        hε₀x _ (hpvv 0 6 (by decide)) (hpvv 1 6 (by decide))]
    · change ε₀ (ε₁ (ε₂ (ε₃ (v 7)))) = -v 7
      rw [hε₃b, map_neg, map_neg, map_neg,
        hε₂x _ (hpvv 4 7 (by decide)) (hpvv 5 7 (by decide)),
        hε₁x _ (hpvv 2 7 (by decide)) (hpvv 3 7 (by decide)),
        hε₀x _ (hpvv 0 7 (by decide)) (hpvv 1 7 (by decide))]
  have hzfix : ∀ u, (∀ i, polar Q (v i) u = 0) → z₀ u = u := by
    intro u hu
    rw [hz₀def, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hε₃x u (hu 6) (hu 7), hε₂x u (hu 4) (hu 5), hε₁x u (hu 2) (hu 3), hε₀x u (hu 0) (hu 1)]
  have hzw : z₀ w₈ = w₈ := hzfix w₈ hpvw
  have hze : z₀ e = -e := by
    rw [hedef, map_add, map_add, map_smul, map_smul, hzv, hzv, hzv]
    module
  have hzD : ∀ w ∈ D, z₀ w = -w := by
    have hle : D ≤ LinearMap.ker ((z₀ : V →ₗ[K] V) + LinearMap.id) := by
      rw [hDdef, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe,
        LinearMap.id_apply]
      fin_cases i
      · change z₀ d₀ + d₀ = 0
        rw [hd₀def, map_sub, map_smul, map_smul, hzv, hzv]
        module
      all_goals
        change z₀ (v _) + v _ = 0
        rw [hzv, neg_add_cancel]
    intro w hw
    have := hle hw
    rw [LinearMap.mem_ker, LinearMap.add_apply, LinearEquiv.coe_coe, LinearMap.id_apply] at this
    exact eq_neg_of_add_eq_zero_left this
  have hz₀2 : z₀ * z₀ = 1 := by
    refine LinearEquiv.toLinearMap_injective (vb.ext fun k => ?_)
    change z₀ (z₀ (vb k)) = vb k
    by_cases hk : (k : ℕ) < 8
    · have : vb k = v ⟨k, hk⟩ := rfl
      rw [this, hzv, map_neg, hzv, neg_neg]
    · have hfix : z₀ (vb k) = vb k := hzfix _ fun i =>
        hvo _ _ fun h => by have := congrArg Fin.val h; simp at this; omega
      rw [hfix, hfix]
  set z : ProjOrthDerived Q := ρ ⟨z₀, hz₀Ω⟩ with hzdef
  have hz1 : z ≠ 1 := hnotsc ⟨z₀, hz₀Ω⟩ hzw _ (hv0 0) (hzv 0)
  have hz2 : z ^ 2 = 1 := by
    rw [hzdef, ← map_pow]
    have : (⟨z₀, hz₀Ω⟩ : Ω) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, pow_two]
      exact hz₀2)
    rw [this, map_one]
  have hzo : orderOf z = 2 := orderOf_eq_prime hz2 hz1
  have hzU : ∀ u ∈ (U₀.subgroupOf Ω).map ρ, Commute z u := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' : (g : V ≃ₗ[K] V) ∈ (U₀ : Set (V ≃ₗ[K] V)) := hg
    rw [hU₀] at hg'
    obtain ⟨w, hw, hgw⟩ := hg'
    have hgE : (g : V ≃ₗ[K] V) = eichler Q e w := LinearEquiv.ext fun t => by
      rw [eichler_apply he (hDe w hw)]
      exact LinearMap.congr_fun hgw t
    have hcomm : (⟨z₀, hz₀Ω⟩ : Ω) * g = g * ⟨z₀, hz₀Ω⟩ := by
      apply Subtype.ext
      change z₀ * (g : V ≃ₗ[K] V) = (g : V ≃ₗ[K] V) * z₀
      have hconj := eichler_conj (Q := Q) (g := z₀) (Subgroup.commutator_le.mpr
        (fun g₁ h₁ g₂ h₂ => by
          rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)) hz₀Ω) e w
      rw [hze, hzD w hw, ← neg_one_smul K e, eichler_smul_left, neg_one_smul,
        neg_neg, ← hgE] at hconj
      exact mul_inv_eq_iff_eq_mul.mp hconj
    show z * ρ g = ρ g * z
    rw [hzdef, ← map_mul, ← map_mul, hcomm]
  have hdvd : p ^ 6 ∣ Nat.card ((U₀.subgroupOf Ω).map ρ) := by
    rw [hUcard]
    exact pow_dvd_pow p (by nlinarith)
  obtain ⟨E, hEU, hE, hEc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hUab hdvd
  refine ⟨Subgroup.zpowers z, E, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo,
    pow_one]), ?_, ?_, hE, hEc⟩
  · intro hbot
    have : z ∈ (⊥ : Subgroup (ProjOrthDerived Q)) := hbot ▸ mem_zpowers z
    exact hz1 (mem_bot.mp this)
  · intro u hu
    refine centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro t ht
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ht
    exact (Commute.zpow_left (hzU u (hEU hu)) m).eq

end Abstract

section Models

open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus
  StatedClassicalModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders generic exceptional)

theorem six_le_twoLocalRank_of_projOrth {F : Type} [Group F] [Finite F] [IsSimpleGroup F]
    (hnc : ∃ a b : F, a * b ≠ b * a) {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (Q : QuadraticForm K V) (hV9 : 9 ≤ Module.finrank K V)
    (hB : (polarBilin Q).Nondegenerate) (e : F ≃* ProjOrthDerived Q)
    (hM : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier F)) {X : Type} [Group X] [Finite X]
    (φ : X →* F) (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank p X := by
  obtain ⟨⟨E₂, hE₂, hE₂c⟩, S, E, hS, hSne, hES, hE, hEc⟩ :=
    orth_large_witness hp hp2 hf hK Q hV9 hB
  have hV : IsElemAbelian 2 (E₂.map e.symm.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE₂ _
  have hVc : Nat.card (E₂.map e.symm.toMonoidHom) = 2 ^ (6 + 1) := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hE₂c]
  have hF6 : 6 ≤ GLATwoLocalRank p F := by
    obtain ⟨hS', hSne', hES', hE', hEc'⟩ :=
      i1020_map_witness e.symm.toMonoidHom e.symm.injective hS hES hE hEc
    exact le_twoLocalRank_of_witness hp hS' (hSne' hSne) hES' hE' hEc'
  exact le_twoLocalRank_of_surj hnc hp hp2 hV hVc
    (twoLocalRank_cover_of_multiplier hnc hp hM hF6) φ hφ

private theorem exists_not_comm_of_perfect {G : Type} [Group G] [Nontrivial G]
    (hperf : Group.IsPerfect G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩

private theorem not_dvd_of_dvd_four {q m : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hm : m ∣ 4) :
    ¬ q ∣ m := fun h => by
  have h4 : q ∣ 2 ^ 2 := h.trans (by simpa using hm)
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h4))

theorem six_le_twoLocalRank_B {n : ℕ} (hn : 4 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n Q).Valid) (hq2 : Q.p ≠ 2) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.B n Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  let eB := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n Q hv hq2
    (by omega)
  have hMd : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.B n Q, hv⟩).Group .POmegaOdd n Q.p
      Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, by omega, hq2⟩, _, inferInstance, inferInstance, hcard, ⟨eB⟩⟩
  obtain ⟨-, hnt, hsimp, hperf⟩ :=
    CFSG.LieType.SeitzGeneration.orth_facts_of_model (Or.inl rfl) hMd
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.B n Q, hv⟩).Group := Finite.of_equiv _ eB.symm.toEquiv
  have h2 : (2 : Fx) ≠ 0 := Ring.two_ne_zero (by
    have : CharP Fx Q.p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Q.prime_p Q.exponent_pos hcard
    rw [ringChar.eq Fx Q.p]; exact hq2)
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadOdd n Fx)
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier
      (TauCeti.CFSGIndex.lie ⟨.B n Q, hv⟩).Group) := by
    have hq5 : 5 ≤ Q.p ^ Q.exponent ∨ (Q.p ^ Q.exponent = 3 ∧ 4 ≤ n) := by
      by_cases h3 : Q.p ^ Q.exponent = 3
      · exact Or.inr ⟨h3, hn⟩
      · left
        have hodd : Odd (Q.p ^ Q.exponent) := (Q.prime_p.odd_of_ne_two hq2).pow
        have h1 : 1 < Q.p ^ Q.exponent := Nat.one_lt_pow Q.exponent_pos.ne' Q.prime_p.one_lt
        obtain ⟨k, hk⟩ := hodd
        omega
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaOdd_row hMd hq5
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .POmegaOdd n Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> first | rfl | omega | simp_all
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders]
    exact not_dvd_of_dvd_four Q.prime_p hq2 (by norm_num)
  have hdim : 9 ≤ Module.finrank Fx (Fin n ⊕ Fin n ⊕ Unit → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    omega
  exact six_le_twoLocalRank_of_projOrth (exists_not_comm_of_perfect hperf) Q.prime_p hq2
    Q.exponent_pos hcard _ hdim (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadOdd n Fx h2)
    (eB.trans e₂) hM φ hφ

theorem six_le_twoLocalRank_D
    {n : ℕ} (hn : 5 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D n Q).Valid) (hq2 : Q.p ≠ 2) {X : Type} [Group X] [Finite X]
    (φ : X →* (TauCeti.CFSGIndex.lie ⟨.D n Q, hv⟩).Group) (hφ : Function.Surjective φ) :
    6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  let eD := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n Q hv
  have hMd : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.D n Q, hv⟩).Group .POmegaPlus n Q.p
      Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, by omega⟩, _, inferInstance, inferInstance, hcard, ⟨eD⟩⟩
  obtain ⟨-, hnt, hsimp, hperf⟩ :=
    CFSG.LieType.SeitzGeneration.orth_facts_of_model (Or.inr (Or.inl rfl)) hMd
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.D n Q, hv⟩).Group := Finite.of_equiv _ eD.symm.toEquiv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadPlus n Fx)
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier
      (TauCeti.CFSGIndex.lie ⟨.D n Q, hv⟩).Group) := by
    have hq3 : 3 ≤ Q.p ^ Q.exponent ∨ (Q.p ^ Q.exponent = 2 ∧ 5 ≤ n) := by
      left
      have hodd : Odd (Q.p ^ Q.exponent) := (Q.prime_p.odd_of_ne_two hq2).pow
      have h1 : 1 < Q.p ^ Q.exponent := Nat.one_lt_pow Q.exponent_pos.ne' Q.prime_p.one_lt
      obtain ⟨k, hk⟩ := hodd
      omega
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaPlus_row hMd hq3
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .POmegaPlus n Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    have hodd : ¬ Even (Q.p ^ Q.exponent) :=
      Nat.not_even_iff_odd.2 (Q.prime_p.odd_of_ne_two hq2).pow
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders, hodd, if_false]
    refine not_dvd_of_dvd_four Q.prime_p hq2 ?_
    split
    · norm_num
    · simpa using Nat.gcd_dvd_left 4 _
  have hdim : 9 ≤ Module.finrank Fx (Fin n ⊕ Fin n → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  exact six_le_twoLocalRank_of_projOrth (exists_not_comm_of_perfect hperf) Q.prime_p hq2
    Q.exponent_pos hcard _ hdim (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus n Fx)
    (eD.trans e₂) hM φ hφ

theorem six_le_twoLocalRank_twistedD
    {n : ℕ} (hn : 5 ≤ n) (Q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedD n Q).Valid) (hq2 : Q.p ≠ 2) {X : Type} [Group X]
    [Finite X] (φ : X →* (TauCeti.CFSGIndex.lie ⟨.twistedD n Q, hv⟩).Group)
    (hφ : Function.Surjective φ) : 6 ≤ GLATwoLocalRank Q.p X := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set Fx := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD n Q, hv⟩)
  haveI : Finite Fx := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card Fx = Q.p ^ Q.exponent := by
    rw [CFSG.LieType.SeitzGeneration.card_fixedField_eq]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n Q hv
  have hMd : StatedClassicalModel (TauCeti.CFSGIndex.lie ⟨.twistedD n Q, hv⟩).Group .POmegaMinus
      n Q.p Q.exponent :=
    ⟨⟨Q.prime_p, Q.exponent_pos, by omega⟩, _, inferInstance, inferInstance, hcard, b, c, hirr,
      ⟨eD⟩⟩
  obtain ⟨-, hnt, hsimp, hperf⟩ :=
    CFSG.LieType.SeitzGeneration.orth_facts_of_model (Or.inr (Or.inr rfl)) hMd
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.twistedD n Q, hv⟩).Group :=
    Finite.of_equiv _ eD.symm.toEquiv
  obtain ⟨e₂⟩ := CFSG.RankThree.CentralLift.nonempty_statedProj_mulEquiv_projOrthDerived
    (CFSG.LieType.Universal.Spin.coe_quadMinus n Fx b c)
  have hM : ¬ Q.p ∣ Nat.card (CFSG.Open.griessHopfMultiplier
      (TauCeti.CFSGIndex.lie ⟨.twistedD n Q, hv⟩).Group) := by
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaMinus_row hMd
    rw [Nat.card_congr eM.toEquiv]
    have hex : exceptionalOrders .POmegaMinus n Q.p Q.exponent = (1, 1) := by
      unfold exceptionalOrders
      split <;> simp_all
    simp only [generic, exceptional, hex, Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, genericOrders]
    exact not_dvd_of_dvd_four Q.prime_p hq2 (by simpa using Nat.gcd_dvd_left 4 _)
  have hdim : 9 ≤ Module.finrank Fx (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → Fx) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  exact six_le_twoLocalRank_of_projOrth (exists_not_comm_of_perfect hperf) Q.prime_p hq2
    Q.exponent_pos hcard _ hdim
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite n Fx hirr)
    (eD.trans e₂) hM φ hφ

end Models

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

end

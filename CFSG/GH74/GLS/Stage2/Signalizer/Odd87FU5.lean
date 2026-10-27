module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Cell
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Inner
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Bar
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU5Bad
public import CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.ComponentInitial.OddUnitaryInvolutionSylow CFSG.Assembly.LowTwoRank

section Classification

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem semilinearAutHom_bar_ne_conj (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    (hn : 3 ≤ 2 * r + ε) {A : GL (HypIndex r ε) K} {σ : K ≃+* K} (hσ : ∀ c, σ c = h.bar c)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) K) ∈ semilinearSimilitudes h r ε)
    (s : hypPSU h r ε) : semilinearAutHom h hr hε ⟨_, hx⟩ ≠ MulAut.conj s := by
  intro hs
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε s
  have hy : (⟨(g : GL (HypIndex r ε) K), RingEquiv.refl K⟩ : SemiGL (HypIndex r ε) K) ∈
      semilinearSimilitudes h r ε :=
    ⟨1, one_ne_zero, map_one _, by
      rw [one_smul]
      exact (mem_gramSU.mp g.2).1⟩
  let y : semilinearSimilitudes h r ε := ⟨_, hy⟩
  have hΦy : semilinearAutHom h hr hε y = MulAut.conj (hypProj h r ε g) := by
    ext t
    obtain ⟨g', rfl⟩ := hypProj_surjective h r ε t
    rw [semilinearAutHom_apply, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have h1 : semilinearAutHom h hr hε (⟨_, hx⟩ * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hs, hΦy, mul_inv_cancel]
  obtain ⟨hright, -⟩ := (semilinearAutHom_eq_one_iff h hr hε hn _).mp h1
  have hσ1 : σ = RingEquiv.refl K := by
    have h2 : ((⟨_, hx⟩ * y⁻¹ : semilinearSimilitudes h r ε) : SemiGL (HypIndex r ε) K).right =
        σ * (RingEquiv.refl K)⁻¹ := rfl
    rw [h2, show (RingEquiv.refl K)⁻¹ = 1 from rfl, mul_one] at hright
    exact hright
  obtain ⟨c₀, hc₀⟩ := h.exists_bar_ne
  apply hc₀
  rw [← hσ c₀, hσ1]
  rfl

theorem unitary5_involution_cases (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    (α : MulAut (hypPSU h 2 1)) (hα : α ^ 2 = 1) :
    (∃ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h 2 1,
        Function.Injective ((hypProj h 2 1).comp ψ) ∧
        ∀ s ∈ ((hypProj h 2 1).comp ψ).range, α s = s) ∨
    ((∀ s : hypPSU h 2 1, α ≠ MulAut.conj s) ∧
      ∃ E : Subgroup (hypPSU h 2 1), (∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) ∧
        (∀ e ∈ E, e * e = 1) ∧ 2 ^ 4 ≤ Nat.card ↥E ∧ ∀ e ∈ E, α e = e) := by
  classical
  have := h.finite
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := h.charP
    rwa [ringChar.eq K p]
  have hinj : ∀ ψ : ↥(StatedSU 3 (p ^ f) K) →* hypSU h 2 1,
      (∀ x, hypProj h 2 1 (ψ x) = 1 → x = 1) → Function.Injective ((hypProj h 2 1).comp ψ) :=
    fun ψ hψ => by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact hψ x hx
  by_cases hα1 : α = 1
  · subst hα1
    obtain ⟨ψ, -, hψs⟩ := exists_comm_su3Hom h hp (by norm_num) (one_mem (hypUnitary h 2 1))
      one_ne_zero (by simp) (by simp [UnitaryFieldData.norm])
    exact Or.inl ⟨ψ, hinj ψ hψs, fun s _ => rfl⟩
  have hα2 : orderOf α = 2 := orderOf_eq_prime hα hα1
  obtain ⟨A, σ, hx, hA, hαeq, hσ, hrefl, hbar⟩ :=
    (odd_unitary_automorphism_semilinear_representation h hp (by norm_num : 1 ≤ 2)
      (by norm_num : 1 ≤ 1) (by norm_num : 3 ≤ 2 * 2 + 1)).2.2.2 α hα2
  subst hαeq
  rcases hσ with rfl | hσ
  ·
    have hord := hrefl rfl
    have hsq : (QuotientGroup.mk (⟨A, hA⟩ * ⟨A, hA⟩) : hypUnitaryMod h 2 1) = 1 := by
      rw [QuotientGroup.mk_mul, ← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hord])
    obtain ⟨d, hd, -, hAA⟩ := mem_normOneScalars.mp ((QuotientGroup.eq_one_iff _).mp hsq)
    obtain ⟨l, hl0, hld⟩ := exists_sq_eq_of_norm_eq_one h hp hd
    have hAA' : (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) * A = (l ^ 2) • 1 := by
      have h1 := congrArg (fun g : GL (HypIndex 2 1) K =>
        (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hAA
      simp only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
      rw [h1, hld, scalar_apply, smul_one_eq_diagonal]
    have hN : h.norm l = 1 ∨ h.norm l = -1 := by
      have h1 : h.norm l * h.norm l = 1 := by
        rw [← norm_mul_eq h, ← pow_two, hld, hd]
      exact mul_self_eq_one_iff.mp h1
    rcases hN with hN | hN
    · obtain ⟨ψ, hψ, hψs⟩ := exists_comm_su3Hom h hp (by norm_num) hA hl0 hAA' hN
      exact Or.inl ⟨ψ, hinj ψ hψs, fixed_of_comm h _ _ hx ψ hψ⟩
    · exact (not_paired_of_odd h hp ⟨2, rfl⟩ hA hl0 hAA' hN).elim
  ·
    obtain ⟨c, hc, hAA⟩ := hbar hσ
    obtain ⟨ψ, hψ, hψs⟩ := exists_signs_comm_of_bar h hp (by norm_num) hA hc hAA
    have hθ : Function.Injective ((hypProj h 2 1).comp ψ) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      exact hψs x hx
    obtain ⟨hcomm, hsq, hcard⟩ := elemAbelian_range_of_signs hK2 _ hθ
    exact Or.inr ⟨semilinearAutHom_bar_ne_conj h _ _ (by norm_num) hσ hx, _, hcomm, hsq, hcard,
      fixed_of_comm_bar h _ _ hσ hx ψ hψ⟩

end Classification

theorem exists_unitaryData_equiv {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hL : CFSG.Blueprint.LieModel Y .PSU 5 p f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData p f K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (Y ≃* hypPSU h 2 1) := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (p ^ f) ^ 2 ∧ Nonempty (Y ≃*
        Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSU 5 (p ^ f) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := 2) (ε := 1) h
  exact ⟨K, inferInstance, inferInstance, h, hcard,
    ⟨e₀.trans (hypPSUEquivStatedProj h hR₀ (by omega)).symm⟩⟩

theorem cell87_FU5 : Cell87 FU5 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  obtain ⟨p0, f, hp0, hf, hq4, hL⟩ := hF
  obtain ⟨K, _, _, h, hcard, ⟨e⟩⟩ := exists_unitaryData_equiv hp0 hf hL
  have hp02 : p0 ≠ 2 := by
    rintro rfl
    have : Even (2 ^ f) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have := Nat.even_iff.mp this
    omega
  have : Fact p0.Prime := ⟨hp0⟩
  have : CharP K p0 := h.charP
  obtain ⟨π, α, hπ, hker, hcomm, hαα⟩ :=
    exists_induced (layerAut (zSec z H₀ hz H₁)) (layerAut_layerAut hd.z2) e
  have hα2 : α ^ 2 = 1 := by
    ext s
    rw [sq, MulAut.mul_apply]
    exact hαα s
  rcases unitary5_involution_cases h hp02 α hα2 with
    ⟨ψ, hψi, hfix⟩ | ⟨hnotinn, E, hEc, hE2, hEcard, hEfix⟩
  ·
    have hP3 := isPerfect_statedSU_three_odd (K := K) hcard hp02
    have : Group.IsPerfect ((hypProj h 2 1).comp ψ).range := Group.IsPerfect.range _
    let c : ↥((hypProj h 2 1).comp ψ).range →* StatedProj (StatedSU 3 (p0 ^ f) K) :=
      (QuotientGroup.mk' _).comp (MonoidHom.ofInjective hψi).symm.toMonoidHom
    have hc : Function.Surjective c :=
      (QuotientGroup.mk'_surjective _).comp (MonoidHom.ofInjective hψi).symm.surjective
    have hCS := centSection_of_fixed_perfect hπ hker.le hcomm _ hfix c hc
    have := isSimpleGroup_statedProj_three (K := K) hcard hq4
    have : Group.IsPerfect (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have : Nontrivial (StatedProj (StatedSU 3 (p0 ^ f) K)) := IsSimpleGroup.toNontrivial
    have hns : ¬ Group.IsSolvable (StatedProj (StatedSU 3 (p0 ^ f) K)) :=
      Group.IsPerfect.not_isSolvable _
    have hKF := kindFactor_of_section_sec hctx hsig hns hCS.isSection
    exact not_kindFactor hp02 (involved_qdSL_statedProj_three hcard)
      (not_card_dvd_factorial_statedProj_three hf hcard hq4) hKF
  ·
    have hzK : zSec z H₀ hz H₁ ∉ layer (Sec H₀ H₁) := by
      intro hzb
      apply hnotinn (π ⟨zSec z H₀ hz H₁, hzb⟩)
      ext s
      obtain ⟨x, rfl⟩ := hπ s
      rw [← hcomm, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [coe_layerAut]
      simp
    exact gen4_kill (gen4_sec hctx.std.gen4 H₀ H₁) hd.z2 hzK hπ hker hcomm E hEc hE2 hEcard hEfix

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidual
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.LieType.Universal.SpecialLinear
open scoped commutatorElement

namespace L5Core

section Perm

variable {ι : Type*} [DecidableEq ι]

theorem exists_perm_two {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ π : Equiv.Perm ι, π i = k ∧ π j = l := by
  have hne : Equiv.swap i k j ≠ k := by
    intro h
    apply hij
    have := congrArg (Equiv.swap i k) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    exact this.symm
  refine ⟨Equiv.swap (Equiv.swap i k j) l * Equiv.swap i k, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hne.symm hkl
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

end Perm

section Roots

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

omit [Fintype ι] in
theorem signedPerm_one_eq (π : Equiv.Perm ι) :
    signedPerm π (1 : ι → F) = (π⁻¹).permMatrix F := by
  ext r s
  simp [signedPerm_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Equiv.eq_symm_apply, eq_comm]

theorem det_signedPerm_one [CharP F 2] (π : Equiv.Perm ι) :
    Matrix.det (signedPerm π (1 : ι → F)) = 1 := by
  rw [signedPerm_one_eq, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π⁻¹) with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]

theorem exists_conj_rootSL [CharP F 2] {n : ℕ} {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) F,
      g * rootSL (K := F) i j * g⁻¹ = rootSL (K := F) k l := by
  obtain ⟨π, hπi, hπj⟩ := exists_perm_two hij hkl
  subst hπi hπj
  refine ⟨⟨signedPerm π (1 : Fin n → F), det_signedPerm_one π⟩, ?_⟩
  rw [rootSL_of_ne (K := F) hij, rootSL_of_ne (K := F) (π.injective.ne hij)]
  have := conj_transvection_of_coe_eq_signedPerm
    (g := (⟨signedPerm π (1 : Fin n → F), det_signedPerm_one π⟩ :
      Matrix.SpecialLinearGroup (Fin n) F)) (π := π) (ε := (1 : Fin n → F)) rfl
    (fun s => by simp) hij (1 : F)
  simpa using this

end Roots

end L5Core

theorem examExcludes_l5 : ExamExcludes FamL5 := by
  rintro G _ _ K B B' P R m h hmodel
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have hcp : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hF
  have habs := h.toAbs
  let ψ : (↥K ⧸ Subgroup.center ↥K) ≃* projectiveSL 5 F :=
    e.trans (CFSG.QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 5 F)
  let θ : ↥K →* projectiveSL 5 F := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hθsurj : Function.Surjective θ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hθker : θ.ker = Subgroup.center ↥K := by
    ext x
    rw [MonoidHom.mem_ker]
    change ψ (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff]
  obtain ⟨S, hSU⟩ := exists_sylow_projUnitriangular (K := F) 2 (n := 5) (by norm_num)
  have hU : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 5 F) ⊤ :=
    hSU ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  obtain ⟨R₀, A₀, hR₀U, hnorm, hcardR, -, -, -, -, hstrong⟩ :=
    habs.exists_Rprime θ hθsurj hθker.le (projUnitriangular 5 F) hU
  have hcardU : Nat.card (projUnitriangular 5 F) = 2 ^ 10 := by
    rw [card_projUnitriangular, hF2]
  have hle := Subgroup.card_le_of_le hR₀U
  rw [hcardR, hcardU] at hle
  have hm := h.two_le
  have h4m : 4 * m ≤ 10 := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ 10 < 2 ^ (4 * m) := Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  have hm2 : m = 2 := by omega
  rw [hm2] at hcardR
  have hnormal : (R₀.subgroupOf (projUnitriangular 5 F)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : projectiveSL 5 F) ∈ R₀ := hx
    show ((g : projectiveSL 5 F) * x * (g : projectiveSL 5 F)⁻¹) ∈ R₀
    exact hnorm g (Subgroup.le_normalizer g.2) x hx'
  have hsub : Nat.card (R₀.subgroupOf (projUnitriangular 5 F)) = 2 ^ 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR₀U).toEquiv, hcardR]
  have hquot : Nat.card (↥(projUnitriangular 5 F) ⧸ R₀.subgroupOf (projUnitriangular 5 F)) =
      2 ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (R₀.subgroupOf (projUnitriangular 5 F))
    rw [hcardU, hsub] at h1
    have h2 : Nat.card (↥(projUnitriangular 5 F) ⧸ R₀.subgroupOf (projUnitriangular 5 F)) *
        2 ^ 8 = 2 ^ 2 * 2 ^ 8 := by rw [← h1]; norm_num
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  have hcomm2 : IsMulCommutative
      (↥(projUnitriangular 5 F) ⧸ R₀.subgroupOf (projUnitriangular 5 F)) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
  have hcomm : ∀ u ∈ projUnitriangular 5 F, ∀ v ∈ projUnitriangular 5 F, ⁅u, v⁆ ∈ R₀ := by
    intro u hu v hv
    have h1 : QuotientGroup.mk' (R₀.subgroupOf (projUnitriangular 5 F))
        ⁅(⟨u, hu⟩ : ↥(projUnitriangular 5 F)), ⟨v, hv⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcomm2.is_comm.comm _ _)
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact h2
  set ρ : Fin 5 → Fin 5 → projectiveSL 5 F := fun i j => proj 5 F (rootSL i j) with hρ
  have hρU : ∀ i j : Fin 5, i < j → ρ i j ∈ projUnitriangular 5 F := fun i j hij =>
    Subgroup.mem_map_of_mem _ (rootSL_mem_unitriangular hij)
  have hρsq : ∀ i j : Fin 5, ρ i j * ρ i j = 1 := fun i j => by
    rw [hρ]
    simp only
    rw [← map_mul, rootSL_mul_self, map_one]
  have h02 : ρ 0 2 ∈ R₀ := by
    have h1 := hcomm (ρ 0 1) (hρU 0 1 (by decide)) (ρ 1 2) (hρU 1 2 (by decide))
    have e : ⁅ρ 0 1, ρ 1 2⁆ = ρ 0 2 := by
      rw [hρ]
      simp only
      rw [← map_commutatorElement, commutatorElement_rootSL (by decide) (by decide) (by decide)]
    rwa [e] at h1
  have hroot : ∀ i j : Fin 5, i < j → ρ i j ∈ R₀ := by
    intro i j hij
    obtain ⟨g, hg⟩ := L5Core.exists_conj_rootSL (F := F) (show (0 : Fin 5) ≠ 2 by decide) hij.ne
    have e : proj 5 F g * ρ 0 2 * (proj 5 F g)⁻¹ = ρ i j := by
      rw [hρ]
      simp only
      rw [← map_inv, ← map_mul, ← map_mul, hg]
    have h1 := hstrong (ρ 0 2) h02 (hρsq 0 2) (proj 5 F g) (by rw [e]; exact hρU i j hij)
    rwa [e] at h1
  have hUR : projUnitriangular 5 F ≤ R₀ := by
    show Subgroup.map (proj 5 F) (unitriangular 5 F) ≤ R₀
    refine (Subgroup.map_mono (unitriangular_le_closure_rootSL (K := F) (n := 5) hF2)).trans ?_
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨_, ⟨i, j, hij, rfl⟩, rfl⟩
    exact hroot i j hij
  have := Subgroup.card_le_of_le hUR
  rw [hcardU, hcardR] at this
  norm_num at this

end CFSG.QuasithinUnique.Lin2

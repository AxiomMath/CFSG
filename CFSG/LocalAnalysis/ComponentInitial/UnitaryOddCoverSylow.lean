module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCoverRadical

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

universe u

theorem ker_eq_bot_of_sq_reduction {X : Type*} [Group X]
    (H : ∀ {E' : Type u} [Group E'] [Finite E'] [Group.IsPerfect E'] (θ' : E' →* X),
      Function.Surjective θ' → θ'.ker ≤ Subgroup.center E' → (∀ c, θ' c = 1 → c ^ 2 = 1) →
        θ'.ker = ⊥)
    {E : Type u} [Group E] [Finite E] [Group.IsPerfect E] (θ : E →* X)
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) :
    θ.ker = ⊥ := by
  set D := BinarySymplecticSix.powers hC 2 with hD
  have : D.Normal :=
    Subgroup.normal_of_le_center ((BinarySymplecticSix.powers_le hC 2).trans hC)
  have hDle : D ≤ θ.ker := BinarySymplecticSix.powers_le hC 2
  set θ' := QuotientGroup.lift D θ hDle with hθ'
  have hθ'mk : ∀ y : E, θ' (y : E ⧸ D) = θ y := fun y => QuotientGroup.lift_mk _ _ _
  have hθ'surj : Function.Surjective θ' := by
    intro x
    obtain ⟨y, rfl⟩ := hθ x
    exact ⟨y, hθ'mk y⟩
  have hθ'C : θ'.ker ≤ Subgroup.center (E ⧸ D) := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [MonoidHom.mem_ker, hθ'mk] at hc
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          Subgroup.mem_center_iff.mp (hC hc) g]
  have hsq : ∀ c, θ' c = 1 → c ^ 2 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθ'mk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  have hbot := H θ' hθ'surj hθ'C hsq
  have hsqr : ∀ x ∈ θ.ker, ∃ y ∈ θ.ker, x = y ^ 2 := fun x hx => by
    have hmem : (x : E ⧸ D) ∈ θ'.ker := by
      rw [MonoidHom.mem_ker, hθ'mk]
      exact hx
    rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  have hexp := BinarySymplecticSix.sq_eq_one_of_forall_sq_eq_pow_four hC h2 fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hsqr x hx
    exact ⟨y, hy, by rw [← pow_mul]⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hsqr x hx
  exact Subgroup.mem_bot.mpr (hexp y hy)

variable {p f : ℕ} {K : Type} [Field K] {r : ℕ} {E : Type*} [Group E]

theorem eq_one_of_hypProj_nElt_mul_lHom {h : UnitaryFieldData p f K} (hr : 1 ≤ r)
    {x : Fin r → K}
    {C : Matrix (Fin r) (Fin r) K} (hC : IsRad h x C) {A : GL (Fin r) K}
    (hA : IsUnitriangular (A : Matrix (Fin r) (Fin r) K))
    (h1 : hypProj h r 1 (nElt hC) * hypProj h r 1 (lHom h r A) = 1) : A = 1 := by
  have hU : nElt hC * lHom h r A ∈ hypUnitriangular h r 1 :=
    mul_mem (nElt_mem_hypUnitriangular hC) (lHom_mem_hypUnitriangular hA)
  have hinj := hypProj_injective_on h hr le_rfl
  have he : (⟨nElt hC * lHom h r A, hU⟩ : hypUnitriangular h r 1) = 1 :=
    hinj (Subtype.ext (by
      simp only [MonoidHom.subgroupMap_apply_coe, map_mul, map_one]
      exact h1))
  have he' : nElt hC = lHom h r A⁻¹ := by
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val he)
  exact inv_eq_one.mp (eq_one_of_nElt_eq_lHom he')

theorem ker_eq_bot_of_lifts {h : UnitaryFieldData 2 f K} {θ : E →* hypPSU h r 1} [Finite E]
    [Group.IsPerfect E] (hθ : Function.Surjective θ)
    (hC : θ.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 θ.ker) (hr : 1 ≤ r) (M₀ : Subgroup E)
    (hM₀N : M₀ ≤ preN θ) (hM₀inj : ∀ y ∈ M₀, θ y = 1 → y = 1)
    (hM₀surj : ∀ {x : Fin r → K} {C : Matrix (Fin r) (Fin r) K} (hx : IsRad h x C),
      ∃ y ∈ M₀, θ y = hypProj h r 1 (nElt hx))
    (hM₀norm : ∀ (A : SpecialLinearGroup (Fin r) K) (u : E),
      θ u = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) →
        ∀ y, y ∈ M₀ ↔ u * y * u⁻¹ ∈ M₀)
    (Y : Subgroup E) (hYinj : ∀ y ∈ Y, θ y = 1 → y = 1)
    (hYsurj : ∀ A ∈ LinearFlag.unitriangular r K,
      ∃ y ∈ Y, θ y = hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A))) :
    θ.ker = ⊥ := by
  set ρ : SpecialLinearGroup (Fin r) K →* hypPSU h r 1 :=
    (hypProj h r 1).comp ((lHom h r).comp SpecialLinearGroup.toGL) with hρ
  set Ut := Y ⊓ ((LinearFlag.unitriangular r K).map ρ).comap θ with hUt
  have hUtN : Ut ≤ Subgroup.normalizer (M₀ : Set E) := by
    intro u hu
    obtain ⟨A, -, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    rw [Subgroup.mem_normalizer_iff]
    exact hM₀norm A u hAu.symm
  set P₀ := M₀ ⊔ Ut with hP₀
  have hP₀mul : (P₀ : Set E) = (M₀ : Set E) * (Ut : Set E) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M₀ Ut hUtN
  have hinj : ∀ z ∈ P₀, θ z = 1 → z = 1 := by
    intro z hz hθz
    rw [← SetLike.mem_coe, hP₀mul, Set.mem_mul] at hz
    obtain ⟨m, hm, u, hu, rfl⟩ := hz
    obtain ⟨_, ⟨x, C, hx, rfl⟩, hxm⟩ := hM₀N hm
    obtain ⟨A, hA, hAu⟩ := (Subgroup.mem_inf.mp hu).2
    have hAU : IsUnitriangular ((SpecialLinearGroup.toGL A : GL (Fin r) K) :
        Matrix (Fin r) (Fin r) K) := ⟨fun i j hij => hA.1 i j hij, hA.2⟩
    have h1 : hypProj h r 1 (nElt hx) * hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) =
        1 := by
      rw [hxm]
      change θ m * ρ A = 1
      rw [hAu, ← map_mul, hθz]
    have hA1 := eq_one_of_hypProj_nElt_mul_lHom hr hx hAU h1
    have hθu : θ u = 1 := by
      rw [← hAu]
      change hypProj h r 1 (lHom h r (SpecialLinearGroup.toGL A)) = 1
      rw [hA1, map_one, map_one]
    have hθm : θ m = 1 := by rwa [map_mul, hθu, mul_one] at hθz
    rw [hM₀inj m hm hθm, hYinj u (Subgroup.mem_inf.mp hu).1 hθu, one_mul]
  obtain ⟨-, -, -, -, ⟨S, hS⟩, -, -⟩ := unitary_order_and_Sylow h hr (le_refl 1)
  have hSle : (S : Subgroup (hypPSU h r 1)) ≤ P₀.map θ := by
    intro s hs
    rw [hS] at hs
    obtain ⟨g, hg, rfl⟩ := hs
    obtain ⟨A, hA, x, C, hx, rfl⟩ := exists_lHom_mul_nElt_of_mem hg
    set A' : SpecialLinearGroup (Fin r) K := ⟨A, hA.det_eq_one⟩ with hA'
    have hA'U : A' ∈ LinearFlag.unitriangular r K :=
      ⟨fun i j hij => hA.1 hij, hA.2⟩
    have hA'GL : SpecialLinearGroup.toGL A' = A := Units.ext rfl
    obtain ⟨y, hy, hyA⟩ := hYsurj A' hA'U
    obtain ⟨m, hm, hmx⟩ := hM₀surj hx
    have hyU : y ∈ Ut := ⟨hy, ⟨A', hA'U, hyA.symm⟩⟩
    refine ⟨y * m, mul_mem (Subgroup.mem_sup_right hyU) (Subgroup.mem_sup_left hm), ?_⟩
    rw [map_mul, hyA, hmx, hA'GL, map_mul]
  exact LinearCover.ker_eq_bot_of_sylow_le_map θ hθ hC h2 S P₀ hSle hinj

end CFSG.LocalAnalysis.ComponentInitial.UnitaryOddCover

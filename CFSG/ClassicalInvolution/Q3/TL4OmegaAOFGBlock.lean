module

public import CFSG.ClassicalInvolution.Q3.TL4OmegaAOFGForm
public import CFSG.ClassicalInvolution.Q3.Q3MFODSimE
public import CFSG.ClassicalInvolution.Q3.Q3MFODSim
public import CFSG.ClassicalInvolution.Q3.Q3NMBlocks
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Center
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Split

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Gauss

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Balance

section Block

variable {F : Type} [Field F] [Finite F] [Fact (Nat.card F = 3)] {V : Type} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V] [Module (GaussField F) V]
  [IsScalarTower F (GaussField F) V] {Q : QuadraticForm F V} {a : V ≃ₗ[F] V}

variable (F V) in
theorem finiteDimensional_gauss : FiniteDimensional (GaussField F) V :=
  Module.Finite.of_restrictScalars_finite F (GaussField F) V

omit [Finite F] [Fact (Nat.card F = 3)] [FiniteDimensional F V] in
theorem exists_ne_zero_of_nondegenerate {K W : Type} [Field K] [AddCommGroup W] [Module K W]
    [Nontrivial W] {q : QuadraticForm K W} (hq : (polarBilin q).Nondegenerate) :
    ∃ x, q x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  apply hx
  refine hq.1 x fun y => ?_
  rw [polarBilin_apply_apply, polar, h, h, h, sub_zero, sub_zero]

theorem mul_self_eq_one_of_commute (hF : Nat.card F = 3)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (hQ : (polarBilin Q).Nondegenerate)
    (h3 : 3 ≤ Module.finrank (GaussField F) V) {g : V ≃ₗ[GaussField F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup (gaussQuad Q hω hg))
    (hcomm : ∀ h ∈ elementaryGroup (gaussQuad Q hω hg), g * h = h * g) : g * g = 1 := by
  have := finiteDimensional_gauss F V
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hodd : Odd (Nat.card (GaussField F)) := by rw [card_gaussField_eq_nine hF]; decide
  have hQq := nondegenerate_gaussQuad h2 hω hg hQ
  obtain ⟨c, hc⟩ := Q3MFOD.exists_smul_of_commute_elementary hodd hQq h3 hgO hcomm
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := GaussField F) (by omega)
  obtain ⟨x, hx⟩ := exists_ne_zero_of_nondegenerate hQq
  have hcc : c * c = 1 := by
    have h1 := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO) x
    rw [hc, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h4 : (c * c - 1) * gaussQuad Q hω hg x = 0 := by linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right hx)
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, hc, hc, smul_smul, hcc, one_smul]
  rfl

theorem oddCoreIn_fixed_conjES_of_gauss (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank F V)
    (hE : elementaryGroup Q = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hω : ∀ v, (QuadraticAlgebra.omega : GaussField F) • v = a v)
    (hg : ∀ v, Q (a v) = (-1 : F) * Q v) (h3 : 3 ≤ Module.finrank (GaussField F) V)
    (hq : CFSG.Open.IsQuasisimple ↥(elementaryGroup (gaussQuad Q hω hg))) :
    oddCoreIn (fixedSubgroup (autToCentralQuotient ↥(elementaryGroup Q)
      (Q3MFOD.conjES Q hE (neg_ne_zero.mpr one_ne_zero) hg))) = ⊥ := by
  classical
  have := finiteDimensional_gauss F V
  have h2 : (2 : F) ≠ 0 := Q3MFOD.two_ne_zero_of_card_three hF
  have hμ : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hZ2 := isPGroup_center_elementaryGroup hF hQ hdim
  have : Group.IsPerfect ↥(elementaryGroup (gaussQuad Q hω hg)) := ⟨hq.1⟩
  set φ : ↥(elementaryGroup (gaussQuad Q hω hg)) →* (V ≃ₗ[F] V) :=
    (res F).comp (elementaryGroup (gaussQuad Q hω hg)).subtype with hφ
  have hφapp : ∀ y, φ y = res F (y : V ≃ₗ[GaussField F] V) := fun y => rfl
  have hφinj : Function.Injective φ := res_injective.comp Subtype.val_injective
  have hP : ∀ y, φ y ∈ elementaryGroup Q := by
    intro y
    have hperf : ⁅φ.range, φ.range⁆ = φ.range :=
      Subgroup.isPerfect_iff.mp (Group.IsPerfect.range φ)
    have hle : φ.range ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
      rintro _ ⟨y, rfl⟩
      exact res_mem_orthogonalGroup h2 hω hg
        (elementaryGroup_le_orthogonalGroup (gaussQuad Q hω hg) y.2)
    have h4 : φ.range ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
      calc φ.range = ⁅φ.range, φ.range⁆ := hperf.symm
        _ ≤ _ := Subgroup.commutator_mono hle hle
    rw [hE]
    exact h4 ⟨y, rfl⟩
  let embE : ↥(elementaryGroup (gaussQuad Q hω hg)) →* ↥(elementaryGroup Q) :=
    φ.codRestrict _ hP
  have hembE : ∀ y, ((embE y : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) = φ y := fun y => rfl
  have hZq : IsPGroup 2 (Subgroup.center ↥(elementaryGroup (gaussQuad Q hω hg))) := by
    intro z
    refine ⟨1, ?_⟩
    have hz := Subgroup.mem_center_iff.mp z.2
    have hsq := mul_self_eq_one_of_commute hF hω hg hQ h3
      (elementaryGroup_le_orthogonalGroup (gaussQuad Q hω hg) z.1.2)
      (fun h hh => (congrArg Subtype.val (hz ⟨h, hh⟩)).symm)
    refine Subtype.ext (Subtype.ext ?_)
    rw [pow_one, _root_.sq]
    exact hsq
  have hker : ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp embE).ker ≤
      Subgroup.center ↥(elementaryGroup (gaussQuad Q hω hg)) := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hy
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg Subtype.val (Subgroup.mem_center_iff.mp hy (embE z))
    apply hφinj
    rw [map_mul, map_mul]
    exact h1
  have hno : oddCoreIn (embE.range.map
      (QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
    have h := CFSG.ClassicalInvolution.Q3.oddCoreIn_range_eq_bot_of_isQuasisimple
      ((QuotientGroup.mk' (Subgroup.center ↥(elementaryGroup Q))).comp embE) hq hZq hker
    rwa [MonoidHom.range_comp] at h
  refine oddCoreIn_fixed_eq_bot_of_blocks hZ2 _ (ι := Unit) (fun _ => embE.range) ?_ ?_
    (fun _ => hno) ?_
  · intro _ x hx
    obtain ⟨y, rfl⟩ := hx
    refine (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg _).mpr ?_
    rw [hembE, hφapp]
    exact res_mul_a hω _
  · intro _ b hb x hx
    obtain ⟨y, rfl⟩ := hx
    have hbc := (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg b).mp hb
    obtain ⟨b', hb'O, hb'⟩ :=
      exists_gauss_of_commute hω hg (elementaryGroup_le_orthogonalGroup Q b.2) hbc
    refine ⟨⟨b' * (y : V ≃ₗ[GaussField F] V) * b'⁻¹, conj_mem_elementaryGroup hb'O y.2⟩,
      Subtype.ext ?_⟩
    show res F (b' * (y : V ≃ₗ[GaussField F] V) * b'⁻¹) =
      (b : V ≃ₗ[F] V) * res F (y : V ≃ₗ[GaussField F] V) * (b : V ≃ₗ[F] V)⁻¹
    rw [map_mul, map_mul, map_inv, hb']
  · intro ν hν hcomm
    have hνc := (Q3MFOD.mem_fixedSubgroup_conjES hE hμ hg ν).mp hν
    obtain ⟨ν', hν'O, hν'⟩ :=
      exists_gauss_of_commute hω hg (elementaryGroup_le_orthogonalGroup Q ν.2) hνc
    have hc : ∀ h ∈ elementaryGroup (gaussQuad Q hω hg), ν' * h = h * ν' := by
      intro h hh
      apply res_injective
      have h1 := congrArg Subtype.val (hcomm () (embE ⟨h, hh⟩) ⟨⟨h, hh⟩, rfl⟩)
      rw [map_mul, map_mul, hν']
      exact h1
    have hsq := mul_self_eq_one_of_commute hF hω hg hQ h3 hν'O hc
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, _root_.sq, Subgroup.coe_mul, ← hν', ← map_mul, hsq, map_one]
    rfl

end Block

end CFSG.ClassicalInvolution.Q3.TL4.Gauss

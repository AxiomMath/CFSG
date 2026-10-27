module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightCoverComplement
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalEightCoverLevi

public section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace OrthogonalEightCover

open Matrix OrthogonalSplit MatrixExtension

@[expose] def kerTwoOf {E X : Type*} [Group E] [Group X] (θ : E →* X) : Subgroup E where
  carrier := {c | c ∈ Subgroup.center E ∧ θ c = 1 ∧ c ^ 2 = 1}
  mul_mem' {a b} ha hb := ⟨Subgroup.mul_mem _ ha.1 hb.1, by rw [map_mul, ha.2.1, hb.2.1, mul_one],
    by rw [(show Commute a b from (Subgroup.mem_center_iff.mp ha.1 b).symm).mul_pow, ha.2.2,
      hb.2.2, mul_one]⟩
  one_mem' := ⟨Subgroup.one_mem _, map_one θ, one_pow 2⟩
  inv_mem' {a} ha := ⟨Subgroup.inv_mem _ ha.1, by rw [map_inv, ha.2.1, inv_one],
    by rw [inv_pow, ha.2.2, inv_one]⟩

theorem kernel_sq_eq_one_of_model {X : Type*} [Group X] (ρ : GL (Fin 4) (ZMod 2) →* X)
    (hρ : Function.Injective ρ) (τ : Multiplicative (binaryAltMatrices 4) →* X)
    (hτ : Function.Injective τ)
    (f : GL (Fin 4) (ZMod 2) → binaryAltMatrices 4 → binaryAltMatrices 4)
    (hfval : ∀ g a, ((f g a : binaryAltMatrices 4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (a : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ)
    (hf : ∀ g a, ρ g * τ (Multiplicative.ofAdd a) * (ρ g)⁻¹ = τ (Multiplicative.ofAdd (f g a)))
    (S : Sylow 2 X)
    (hS : ∀ s ∈ (S : Subgroup X),
      ∃ a ∈ (LinearFlag.unitriangular 4 (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL),
        ∃ b ∈ τ.range, s = a * b)
    (hVUR : (LinearFlag.unitriangular 4 (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL) ⊓
      τ.range = ⊥)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {θ : E →* X}
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h4 : ∀ c, θ c = 1 → c ^ 4 = 1) {c : E} (hc : θ c = 1) : c ^ 2 = 1 := by
  have h2 : IsPGroup 2 θ.ker := fun k => ⟨2, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact h4 _ k.2)⟩
  set act := actRad hθ hC ρ hf with hact
  set π := piRad θ hτ with hπ
  have hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      (g : Matrix (Fin 4) (Fin 4) (ZMod 2)) * ((π x).toAdd : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        (g : Matrix (Fin 4) (Fin 4) (ZMod 2))ᵀ := fun g x => by
    rw [hπ, hact, piRad_actRad hθ hC ρ hτ hf g x, hfval]
  obtain ⟨P₀, hP₀inv, hP₀ker, hP₀surj⟩ := binary_alternating_four_extension_complement act π
    (piRad_surjective hθ hτ) hπact (piRad_ker_le_center hC hτ)
    (fun c hc => Subtype.ext (by
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
      exact h4 _ ((piRad_eq_one_iff hτ c).mp hc)))
    (fun g c hc => actRad_apply_of_mem_ker hθ hC ρ hτ hf g hc)
  set V' : Subgroup E := P₀.map (preRad θ τ).subtype with hV'def
  have hmemV' : ∀ x : preRad θ τ, (x : E) ∈ V' ↔ x ∈ P₀ := fun x =>
    ⟨fun hx => by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [Subtype.ext hyx] at hy,
      fun hx => Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hV'le : V' ≤ preRad θ τ := Subgroup.map_subtype_le P₀
  have hV'inv : ∀ (g : GL (Fin 4) (ZMod 2)) (x : preRad θ τ), (x : E) ∈ V' →
      ((actRad hθ hC ρ hf g x : preRad θ τ) : E) ∈ V' := fun g x hx =>
    (hmemV' _).mpr (hP₀inv g x ((hmemV' x).mp hx))
  set ρ' : SpecialLinearGroup (Fin 4) (ZMod 2) →* X := ρ.comp SpecialLinearGroup.toGL with hρ'
  have hρ'inj : Function.Injective ρ' :=
    hρ.comp fun A B h => Subtype.ext (congrArg Units.val h)
  set R := ρ'.range with hR
  have : Group.IsPerfect (SpecialLinearGroup (Fin 4) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set F₀ := leviLift θ R with hF₀
  have : Group.IsPerfect F₀ := isPerfect_leviLift θ R hθ hC
  have hF₀sq : ∀ u ∈ F₀, θ u = 1 → u ^ 2 = 1 := by
    intro u hu hθu
    have h := levi_four_kernel_sq_eq_one (K := ZMod 2) (by rw [Nat.card_zmod]) ρ' hρ'inj
      (leviLiftHom θ R) (leviLiftHom_surjective θ R hθ) (leviLiftHom_ker_le_center θ R hC)
      (isPGroup_leviLiftHom_ker θ R h2) ⟨u, hu⟩ ((leviLiftHom_eq_one_iff θ R _).mpr hθu)
    have := congrArg Subtype.val h
    simpa using this
  set UR := (LinearFlag.unitriangular 4 (ZMod 2)).map ρ' with hUR
  set Ũ := UR.comap θ ⊓ F₀ with hŨ
  have hURR : UR ≤ R := Subgroup.map_le_range ρ' _
  have hŨN : Ũ ≤ Subgroup.normalizer (V' : Set E) := by
    intro u hu
    obtain ⟨A, -, hA⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hu).1
    exact mem_normalizer_of_actRad_mem hθ hC ρ hf hV'le hV'inv (g := SpecialLinearGroup.toGL A)
      hA.symm
  have hker := ker_le_of_lifts hθ hC h2 (kerTwoOf θ) τ.range UR S hS hVUR V' Ũ hŨN
    (fun v hv => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hv
      exact x.2)
    (fun u hu => (Subgroup.mem_inf.mp hu).1)
    (fun b hb => by
      obtain ⟨a, rfl⟩ := hb
      obtain ⟨x, hx, hxa⟩ := hP₀surj a
      exact ⟨x, (hmemV' x).mpr hx, by rw [← tau_piRad hτ x, ← hπ, hxa]⟩)
    (fun a ha => by
      have haR : a ∈ F₀.map θ := by rw [hF₀, map_leviLift θ R hθ]; exact hURR ha
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp haR
      exact ⟨u, Subgroup.mem_inf.mpr ⟨ha, hu⟩, rfl⟩)
    (fun v hv hθv => by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
      have hx1 : π x = 1 := (piRad_eq_one_iff hτ x).mpr hθv
      have hx2 := hP₀ker x hx hx1
      exact ⟨hC hθv, hθv, by
        have := congrArg Subtype.val hx2
        simpa using this⟩)
    (fun u hu hθu => ⟨hC hθu, hθu, hF₀sq u (Subgroup.mem_inf.mp hu).2 hθu⟩)
  exact (hker hc).2.2

end OrthogonalEightCover

end CFSG.LocalAnalysis.ComponentInitial

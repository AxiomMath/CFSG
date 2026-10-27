module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverLift
public import CFSG.LocalAnalysis.ComponentInitial.MatrixExtensionAlternating
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCover
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

open Matrix MatrixExtension LinearFlag

theorem scalars_zmod_two_eq_bot (r : ℕ) : scalars r (ZMod 2) = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, -, hA⟩
  rw [Subgroup.mem_bot]
  have hc : c = 1 := Subsingleton.elim c 1
  apply Subtype.ext
  change (A : Matrix (Fin r) (Fin r) (ZMod 2)) = 1
  rw [hA, hc, Units.val_one, map_one]

theorem ker_eq_bot_of_sq_of_model {r : ℕ} (hr : 5 ≤ r) {X : Type*} [Group X]
    (ρ : GL (Fin r) (ZMod 2) →* X) (hρ : Function.Injective ρ)
    (τ : Multiplicative (binaryAltMatrices r) →* X) (hτ : Function.Injective τ)
    (f : GL (Fin r) (ZMod 2) → binaryAltMatrices r → binaryAltMatrices r)
    (hfval : ∀ g a, ((f g a : binaryAltMatrices r) : Matrix (Fin r) (Fin r) (ZMod 2)) =
      (g : Matrix (Fin r) (Fin r) (ZMod 2)) * (a : Matrix (Fin r) (Fin r) (ZMod 2)) *
        (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ)
    (hf : ∀ g a, ρ g * τ (Multiplicative.ofAdd a) * (ρ g)⁻¹ = τ (Multiplicative.ofAdd (f g a)))
    (S : Sylow 2 X)
    (hS : ∀ s ∈ (S : Subgroup X),
      ∃ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL),
        ∃ b ∈ τ.range, s = a * b)
    (hVUR : (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL) ⊓
      τ.range = ⊥)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {θ : E →* X}
    (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (hsq : ∀ c, θ c = 1 → c ^ 2 = 1) : θ.ker = ⊥ := by
  have h2 : IsPGroup 2 θ.ker := fun k => ⟨1, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact hsq _ k.2)⟩
  set act := actRad hθ hC ρ hf with hact
  set π := piRad θ hτ with hπ
  have hπact : ∀ g x, ((π (act g x)).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) =
      (g : Matrix (Fin r) (Fin r) (ZMod 2)) * ((π x).toAdd : Matrix (Fin r) (Fin r) (ZMod 2)) *
        (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ := fun g x => by
    rw [hπ, hact, piRad_actRad hθ hC ρ hτ hf g x, hfval]
  have hP2 : IsPGroup 2 (preRad θ τ) := fun x => ⟨2, Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have hx2 : θ ((x : E) ^ 2) = 1 := by
      obtain ⟨b, hb⟩ := x.2
      rw [map_pow, ← hb, ← map_pow]
      have hb2 : b ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        rw [toAdd_pow, AddSubgroup.coe_nsmul, two_nsmul]
        exact binary_add_self _
      rw [hb2, map_one]
    rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul]
    exact hsq _ hx2)⟩
  obtain ⟨-, P₀, hP₀inv, hP₀ker, -, hP₀bij⟩ :=
    binary_alternating_matrix_central_extension_splitting hr hP2 act π (piRad_surjective hθ hτ)
      hπact (piRad_ker_le_center hC hτ)
      (fun c hc => Subtype.ext (by
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hsq _ ((piRad_eq_one_iff hτ c).mp hc)))
      (fun g c hc => actRad_apply_of_mem_ker hθ hC ρ hτ hf g hc)
  set V' : Subgroup E := P₀.map (preRad θ τ).subtype with hV'def
  have hmemV' : ∀ x : preRad θ τ, (x : E) ∈ V' ↔ x ∈ P₀ := fun x =>
    ⟨fun hx => by
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rwa [Subtype.ext hyx] at hy,
      fun hx => Subgroup.mem_map.mpr ⟨x, hx, rfl⟩⟩
  have hV'le : V' ≤ preRad θ τ := Subgroup.map_subtype_le P₀
  have hV'inv : ∀ (g : GL (Fin r) (ZMod 2)) (x : preRad θ τ), (x : E) ∈ V' →
      ((actRad hθ hC ρ hf g x : preRad θ τ) : E) ∈ V' := fun g x hx =>
    (hmemV' _).mpr (hP₀inv g x ((hmemV' x).mp hx))
  set ρ' : SpecialLinearGroup (Fin r) (ZMod 2) →* X := ρ.comp SpecialLinearGroup.toGL with hρ'
  have hρ'inj : Function.Injective ρ' :=
    hρ.comp fun A B h => Subtype.ext (congrArg Units.val h)
  set R := ρ'.range with hR
  have : Group.IsPerfect (SpecialLinearGroup (Fin r) (ZMod 2)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by omega)
  have : Group.IsPerfect R := Group.IsPerfect.range _
  set F₀ := leviLift θ R with hF₀
  have : Group.IsPerfect F₀ := isPerfect_leviLift θ R hθ hC
  set η : F₀ →* LinearFlag.projectiveSL r (ZMod 2) := (LinearFlag.proj r (ZMod 2)).comp
    ((MonoidHom.ofInjective hρ'inj).symm.toMonoidHom.comp (leviLiftHom θ R)) with hη
  have hηeq : ∀ u : F₀, η u = 1 ↔ θ u = 1 := by
    intro u
    rw [hη, MonoidHom.comp_apply, LinearFlag.proj_eq_one_iff, scalars_zmod_two_eq_bot,
      Subgroup.mem_bot, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq,
      map_one, ← leviLiftHom_eq_one_iff θ R u]
  have hηsurj : Function.Surjective η :=
    (LinearFlag.proj_surjective r (ZMod 2)).comp
      ((MonoidHom.ofInjective hρ'inj).symm.surjective.comp (leviLiftHom_surjective θ R hθ))
  have hηC : η.ker ≤ Subgroup.center F₀ := fun u hu => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hηeq u).mp hu)) g)
  have hη2 : IsPGroup 2 η.ker := fun k => ⟨1, Subtype.ext (Subtype.ext (by
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_one]
    exact hsq _ ((hηeq k).mp k.2)))⟩
  have hηbot := LinearCover.ker_eq_bot_of_projectiveSL (K := ZMod 2) (by rw [Nat.card_zmod]) hr
    η hηsurj hηC hη2
  have hF₀inj : ∀ u ∈ F₀, θ u = 1 → u = 1 := by
    intro u hu hθu
    have hk : (⟨u, hu⟩ : F₀) ∈ η.ker := (hηeq _).mpr hθu
    rw [hηbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  set UR := (LinearFlag.unitriangular r (ZMod 2)).map ρ' with hUR
  set Ũ := UR.comap θ ⊓ F₀ with hŨ
  have hURR : UR ≤ R := Subgroup.map_le_range ρ' _
  have hŨN : Ũ ≤ Subgroup.normalizer (V' : Set E) := by
    intro u hu
    obtain ⟨A, -, hA⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hu).1
    exact mem_normalizer_of_actRad_mem hθ hC ρ hf hV'le hV'inv (g := SpecialLinearGroup.toGL A)
      hA.symm
  have hker := ker_le_of_lifts hθ hC h2 ⊥ τ.range UR S hS hVUR V' Ũ hŨN
    (fun v hv => by
      obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hv
      exact x.2)
    (fun u hu => (Subgroup.mem_inf.mp hu).1)
    (fun b hb => by
      obtain ⟨a, rfl⟩ := hb
      obtain ⟨⟨x, hx⟩, hxa⟩ := hP₀bij.2 a
      exact ⟨x, (hmemV' x).mpr hx, by rw [← tau_piRad hτ x, ← hπ]; exact congrArg τ hxa⟩)
    (fun a ha => by
      have haR : a ∈ F₀.map θ := by rw [hF₀, map_leviLift θ R hθ]; exact hURR ha
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp haR
      exact ⟨u, Subgroup.mem_inf.mpr ⟨ha, hu⟩, rfl⟩)
    (fun v hv hθv => by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
      have hx1 : x ∈ π.ker := (piRad_eq_one_iff hτ x).mpr hθv
      have hxb : x ∈ π.ker ⊓ P₀ := Subgroup.mem_inf.mpr ⟨hx1, hx⟩
      rw [hP₀ker, Subgroup.mem_bot] at hxb
      rw [Subgroup.mem_bot, hxb]
      rfl)
    (fun u hu hθu => Subgroup.mem_bot.mpr (hF₀inj u (Subgroup.mem_inf.mp hu).2 hθu))
  exact le_bot_iff.mp hker

theorem ker_eq_bot_of_model {r : ℕ} (hr : 5 ≤ r) {X : Type*} [Group X]
    (ρ : GL (Fin r) (ZMod 2) →* X) (hρ : Function.Injective ρ)
    (τ : Multiplicative (binaryAltMatrices r) →* X) (hτ : Function.Injective τ)
    (f : GL (Fin r) (ZMod 2) → binaryAltMatrices r → binaryAltMatrices r)
    (hfval : ∀ g a, ((f g a : binaryAltMatrices r) : Matrix (Fin r) (Fin r) (ZMod 2)) =
      (g : Matrix (Fin r) (Fin r) (ZMod 2)) * (a : Matrix (Fin r) (Fin r) (ZMod 2)) *
        (g : Matrix (Fin r) (Fin r) (ZMod 2))ᵀ)
    (hf : ∀ g a, ρ g * τ (Multiplicative.ofAdd a) * (ρ g)⁻¹ = τ (Multiplicative.ofAdd (f g a)))
    (S : Sylow 2 X)
    (hS : ∀ s ∈ (S : Subgroup X),
      ∃ a ∈ (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL),
        ∃ b ∈ τ.range, s = a * b)
    (hVUR : (LinearFlag.unitriangular r (ZMod 2)).map (ρ.comp SpecialLinearGroup.toGL) ⊓
      τ.range = ⊥)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (θ : E →* X)
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
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hC hc) g]
  have hsq : ∀ c, θ' c = 1 → c ^ 2 = 1 := by
    intro c hc
    induction c using QuotientGroup.induction_on with
    | H y =>
      rw [hθ'mk] at hc
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨y, hc, rfl⟩
  have hbot := ker_eq_bot_of_sq_of_model hr ρ hρ τ hτ f hfval hf S hS hVUR hθ'surj hθ'C hsq
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

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensorNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTransitiveCore

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open TensorProduct Module

universe u v

theorem exists_halving {s : ℕ} (hs : 2 ≤ s) (A : Type u) [Group A] [Finite A]
    [CFSG.IsElementaryAbelian 2 A] (π : A →* Equiv.Perm (Fin s))
    (htr : ∀ i j, ∃ a, π a i = j) :
    ∃ (a₀ : A) (A₁ : Subgroup A) (S : Set (Fin s)), a₀ ∉ A₁ ∧ (∀ a, a ∈ A₁ ∨ a * a₀ ∈ A₁) ∧
      (∀ a ∈ A₁, ∀ i, π a i ∈ S ↔ i ∈ S) ∧ (∀ a, a ∉ A₁ → ∀ i, π a i ∈ S ↔ i ∉ S) ∧
      (⟨0, by omega⟩ : Fin s) ∈ S := by
  classical
  have hcomm : ∀ a b : A, a * b = b * a := fun a b => (IsMulCommutative.is_comm (M := A)).comm a b
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    rwa [pow_two] at this
  let i₀ : Fin s := ⟨0, by omega⟩
  let i₁ : Fin s := ⟨1, by omega⟩
  have hreg : ∀ a i, π a i = i → π a = 1 := by
    intro a i hi
    ext j
    obtain ⟨t, ht⟩ := htr i j
    rw [← ht]
    have : π a (π t i) = π t (π a i) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, hcomm]
    rw [this, hi]
    rfl
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, π a₀ ≠ 1 := by
    obtain ⟨t, ht⟩ := htr i₀ i₁
    refine ⟨t, fun h => ?_⟩
    rw [h] at ht
    have : i₀ = i₁ := ht
    simp [i₀, i₁, Fin.ext_iff] at this
  let 𝒮 : Set (Subgroup A) := {M | π.ker ≤ M ∧ a₀ ∉ M}
  have hne : 𝒮.Nonempty := ⟨π.ker, le_rfl, fun h => ha₀ (MonoidHom.mem_ker.1 h)⟩
  obtain ⟨A₁, ⟨hA₁1, hA₁2⟩, hmax⟩ := Set.Finite.exists_maximalFor id 𝒮 (Set.toFinite _) hne
  have hdich : ∀ a : A, a ∈ A₁ ∨ a * a₀ ∈ A₁ := by
    intro a
    by_contra hcon
    push Not at hcon
    obtain ⟨ha1, ha2⟩ := hcon
    let M : Subgroup A :=
      { carrier := {x | x ∈ A₁ ∨ x * a ∈ A₁}
        mul_mem' := by
          rintro x y (hx | hx) (hy | hy)
          · exact Or.inl (A₁.mul_mem hx hy)
          · refine Or.inr ?_
            rw [mul_assoc]; exact A₁.mul_mem hx hy
          · refine Or.inr ?_
            have : x * y * a = (x * a) * y := by
              rw [mul_assoc, hcomm y a, ← mul_assoc]
            rw [this]; exact A₁.mul_mem hx hy
          · refine Or.inl ?_
            have : x * y = (x * a) * (y * a) := by
              calc x * y = x * y * (a * a) := by rw [hsq, mul_one]
                _ = (x * a) * (y * a) := by
                  rw [mul_assoc x a, ← mul_assoc a y, hcomm a y, mul_assoc y a a, ← mul_assoc x y]
            rw [this]; exact A₁.mul_mem hx hy
        one_mem' := Or.inl A₁.one_mem
        inv_mem' := by
          intro x hx
          rw [inv_eq_of_mul_eq_one_right (hsq x)]
          exact hx }
    have hAM : A₁ ≤ M := fun x hx => Or.inl hx
    by_cases ha₀M : a₀ ∈ M
    · rcases ha₀M with h | h
      · exact hA₁2 h
      · exact ha2 (by rw [hcomm]; exact h)
    · have hM : M ∈ 𝒮 := ⟨le_trans hA₁1 hAM, ha₀M⟩
      have := hmax hM hAM
      exact ha1 (this (Or.inr (by rw [hsq]; exact A₁.one_mem)))
  let S : Set (Fin s) := {i | ∃ a ∈ A₁, π a i₀ = i}
  have hS1 : ∀ a ∈ A₁, ∀ i, π a i ∈ S ↔ i ∈ S := by
    intro a ha i
    constructor
    · rintro ⟨c, hc, hci⟩
      refine ⟨a⁻¹ * c, A₁.mul_mem (A₁.inv_mem ha) hc, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hci, map_inv]
      exact Equiv.symm_apply_apply _ _
    · rintro ⟨c, hc, hci⟩
      refine ⟨a * c, A₁.mul_mem ha hc, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, hci]
  have hS2 : ∀ a, a ∉ A₁ → ∀ i, π a i ∈ S ↔ i ∉ S := by
    intro a ha i
    constructor
    · rintro ⟨c, hc, hci⟩ ⟨c', hc', hci'⟩
      have h1 : π (c⁻¹ * a * c') i₀ = i₀ := by
        rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hci', ← hci, map_inv]
        exact Equiv.symm_apply_apply _ _
      have h2 : c⁻¹ * a * c' ∈ π.ker := MonoidHom.mem_ker.2 (hreg _ _ h1)
      have h3 : c⁻¹ * a * c' ∈ A₁ := hA₁1 h2
      apply ha
      have : a = c * (c⁻¹ * a * c') * c'⁻¹ := by group
      rw [this]
      exact A₁.mul_mem (A₁.mul_mem hc h3) (A₁.inv_mem hc')
    · intro hiS
      obtain ⟨t, ht⟩ := htr i₀ i
      have htA : t ∉ A₁ := fun h => hiS ⟨t, h, ht⟩
      have h1 : a * a₀ ∈ A₁ := (hdich a).resolve_left ha
      have h2 : t * a₀ ∈ A₁ := (hdich t).resolve_left htA
      have h3 : a * t ∈ A₁ := by
        have : a * t = (a * a₀) * (t * a₀) := by
          calc a * t = a * t * (a₀ * a₀) := by rw [hsq, mul_one]
            _ = (a * a₀) * (t * a₀) := by
              rw [mul_assoc a t, mul_assoc a a₀]
              congr 1
              rw [← mul_assoc]
              exact hcomm _ _
        rw [this]; exact A₁.mul_mem h1 h2
      refine ⟨a * t, h3, ?_⟩
      rw [map_mul, Equiv.Perm.mul_apply, ht]
  exact ⟨a₀, A₁, S, hA₁2, hdich, hS1, hS2, ⟨1, A₁.one_mem, by simp [i₀]⟩⟩


theorem exists_perm_of_blocks {κ : Type*} [Finite κ] (μ : Equiv.Perm (κ ⊕ κ))
    (h1 : ∀ l, ∃ l', μ (Sum.inl l) = Sum.inl l') (h2 : ∀ l, ∃ l', μ (Sum.inr l) = Sum.inr l') :
    ∃ ν₁ ν₂ : Equiv.Perm κ, (∀ l, μ (Sum.inl l) = Sum.inl (ν₁ l)) ∧
      (∀ l, μ (Sum.inr l) = Sum.inr (ν₂ l)) := by
  choose f₁ hf₁ using h1
  choose f₂ hf₂ using h2
  have hi1 : Function.Injective f₁ := fun a b h => by
    have := μ.injective ((hf₁ a).trans ((congrArg Sum.inl h).trans (hf₁ b).symm))
    exact Sum.inl_injective this
  have hi2 : Function.Injective f₂ := fun a b h => by
    have := μ.injective ((hf₂ a).trans ((congrArg Sum.inr h).trans (hf₂ b).symm))
    exact Sum.inr_injective this
  exact ⟨Equiv.ofBijective f₁ ⟨hi1, Finite.injective_iff_surjective.1 hi1⟩,
    Equiv.ofBijective f₂ ⟨hi2, Finite.injective_iff_surjective.1 hi2⟩, hf₁, hf₂⟩

theorem exists_regroup {s : ℕ} (S : Set (Fin s)) (τ : Equiv.Perm (Fin s))
    (hτS : ∀ i, τ i ∈ S ↔ i ∉ S) (hτ2 : ∀ i, τ (τ i) = i) :
    ∃ E : Fin s ≃ {i // i ∈ S} ⊕ {i // i ∈ S},
      (∀ l, E (τ.symm (E.symm (Sum.inl l))) = Sum.inr l) ∧
      (∀ l, E (τ.symm (E.symm (Sum.inr l))) = Sum.inl l) ∧
      (∀ π : Equiv.Perm (Fin s), (∀ i, π i ∈ S ↔ i ∈ S) →
        ∃ ν₁ ν₂ : Equiv.Perm {i // i ∈ S},
          (∀ l, E (π.symm (E.symm (Sum.inl l))) = Sum.inl (ν₁.symm l)) ∧
          (∀ l, E (π.symm (E.symm (Sum.inr l))) = Sum.inr (ν₂.symm l))) := by
  classical
  have hτ' : ∀ i, τ.symm i = τ i := fun i => (Equiv.symm_apply_eq τ).2 (hτ2 i).symm
  let ρ' : {i // i ∉ S} ≃ {i // i ∈ S} :=
    { toFun := fun i => ⟨τ i.1, (hτS i.1).2 i.2⟩
      invFun := fun k => ⟨τ k.1, fun h => ((hτS k.1).1 h) k.2⟩
      left_inv := fun i => Subtype.ext (hτ2 i.1)
      right_inv := fun k => Subtype.ext (hτ2 k.1) }
  let E : Fin s ≃ {i // i ∈ S} ⊕ {i // i ∈ S} :=
    (Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumCongr (Equiv.refl _) ρ')
  have hEinl : ∀ l : {i // i ∈ S}, E.symm (Sum.inl l) = l.1 := fun l => by
    simp [E]
  have hEinr : ∀ l : {i // i ∈ S}, E.symm (Sum.inr l) = (ρ'.symm l).1 := fun l => by
    simp [E]
  have hEpos : ∀ i (h : i ∈ S), E i = Sum.inl ⟨i, h⟩ := fun i h => by
    simp [E, Equiv.sumCompl_symm_apply_of_pos h]
  have hEneg : ∀ i (h : i ∉ S), E i = Sum.inr (ρ' ⟨i, h⟩) := fun i h => by
    simp [E, Equiv.sumCompl_symm_apply_of_neg h]
  refine ⟨E, fun l => ?_, fun l => ?_, fun π hπ => ?_⟩
  · rw [hEinl, hτ']
    have h : τ l.1 ∉ S := fun h => (hτS l.1).1 h l.2
    rw [hEneg _ h]
    exact congrArg Sum.inr (Subtype.ext (hτ2 l.1))
  · rw [hEinr, show (ρ'.symm l).1 = τ l.1 from rfl, hτ', hτ2]
    rw [hEpos _ l.2]
  · have hπ' : ∀ i, π.symm i ∈ S ↔ i ∈ S := fun i => by
      have := hπ (π.symm i)
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    obtain ⟨ν₁, ν₂, hν₁, hν₂⟩ := exists_perm_of_blocks
      (E.symm.trans ((π.symm).trans E) : Equiv.Perm ({i // i ∈ S} ⊕ {i // i ∈ S}))
      (fun l => by
        have hl : π.symm l.1 ∈ S := (hπ' l.1).2 l.2
        exact ⟨⟨π.symm l.1, hl⟩, by simp [hEinl, hEpos _ hl]⟩)
      (fun l => by
        have hl : π.symm (ρ'.symm l).1 ∉ S := fun h => (ρ'.symm l).2 ((hπ' _).1 h)
        exact ⟨ρ' ⟨π.symm (ρ'.symm l).1, hl⟩, by simp [hEinr, hEneg _ hl]⟩)
    refine ⟨ν₁.symm, ν₂.symm, fun l => ?_, fun l => ?_⟩
    · simpa [Equiv.trans_apply] using hν₁ l
    · simpa [Equiv.trans_apply] using hν₂ l




section PermStructure

variable {F : Type u} [Field F] {U : Type u} [AddCommGroup U] [Module F U]

theorem factorEnd_comm_of_ne {ι : Type*} [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)] {i j : ι} (hij : i ≠ j)
    (f : Module.End F (V i)) (g : Module.End F (V j)) :
    factorEnd i f * factorEnd j g = factorEnd j g * factorEnd i f := by
  refine LinearMap.ext fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r m =>
    simp only [Module.End.mul_apply, map_smul]
    rw [factorEnd_tprod, factorEnd_tprod, factorEnd_tprod, factorEnd_tprod]
    have e1 : Function.update m j (g (m j)) i = m i := Function.update_of_ne hij _ _
    have e2 : Function.update m i (f (m i)) j = m j := Function.update_of_ne hij.symm _ _
    rw [e1, e2, Function.update_comm hij.symm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_noncomm_end [Module.Finite F U] (hd : 2 ≤ Module.finrank F U) :
    ∃ f g : Module.End F U, f * g ≠ g * f := by
  let b := Module.finBasis F U
  let i₀ : Fin (Module.finrank F U) := ⟨0, by omega⟩
  let i₁ : Fin (Module.finrank F U) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by simp [i₀, i₁, Fin.ext_iff] at h
  refine ⟨(b.coord i₀).smulRight (b i₁), (b.coord i₁).smulRight (b i₀), fun h => ?_⟩
  have := LinearMap.congr_fun h (b i₁)
  simp [Module.End.mul_apply, Basis.coord_apply, h01] at this
  exact b.ne_zero i₁ this


theorem factorAlg_index_injective [Module.Finite F U] (hd : 2 ≤ Module.finrank F U) {s : ℕ} :
    Function.Injective (fun i : Fin s => (factorAlg (F := F) (V := fun _ : Fin s => U) i)) := by
  intro i j hij
  by_contra hne
  have hnt : Nontrivial U := Module.nontrivial_of_finrank_pos (R := F) (M := U) (by omega)
  obtain ⟨f, g, hfg⟩ := exists_noncomm_end (F := F) (U := U) hd
  have hij' : factorAlg (F := F) (V := fun _ : Fin s => U) i =
      factorAlg (F := F) (V := fun _ : Fin s => U) j := hij
  have hmem : factorAlgHom (F := F) (V := fun _ : Fin s => U) i f ∈
      factorAlg (F := F) (V := fun _ : Fin s => U) j := by
    rw [← hij']
    exact AlgHom.mem_range_self _ f
  obtain ⟨h, hh⟩ := hmem
  have hh' : factorEnd j h = factorEnd (V := fun _ : Fin s => U) i f := hh
  apply hfg
  have hinj := factorAlgHom_injective (F := F) (V := fun _ : Fin s => U) i
  apply hinj
  have e1 : factorAlgHom (F := F) (V := fun _ : Fin s => U) i (f * g) =
      factorAlgHom (F := F) (V := fun _ : Fin s => U) i f *
        factorAlgHom (F := F) (V := fun _ : Fin s => U) i g := map_mul _ _ _
  have e2 : factorAlgHom (F := F) (V := fun _ : Fin s => U) i (g * f) =
      factorAlgHom (F := F) (V := fun _ : Fin s => U) i g *
        factorAlgHom (F := F) (V := fun _ : Fin s => U) i f := map_mul _ _ _
  have e3 : factorAlgHom (F := F) (V := fun _ : Fin s => U) j h =
      factorAlgHom (F := F) (V := fun _ : Fin s => U) i f := hh
  have e4 := factorEnd_comm_of_ne (F := F) (V := fun _ : Fin s => U) (Ne.symm hne) h g
  rw [e1, e2, ← e3]
  exact e4

theorem conjAlgHom_mul {W : Type*} [AddCommGroup W] [Module F W] (a b : W ≃ₗ[F] W) :
    ((a * b).conjAlgEquiv F).toAlgHom =
      ((a.conjAlgEquiv F).toAlgHom).comp ((b.conjAlgEquiv F).toAlgHom) := by
  refine AlgHom.ext fun f => ?_
  refine LinearMap.ext fun w => ?_
  simp [LinearEquiv.conjAlgEquiv_apply]
  rfl

theorem conjAlgHom_one {W : Type*} [AddCommGroup W] [Module F W] :
    ((1 : W ≃ₗ[F] W).conjAlgEquiv F).toAlgHom = AlgHom.id F _ := by
  refine AlgHom.ext fun f => ?_
  refine LinearMap.ext fun w => ?_
  simp [LinearEquiv.conjAlgEquiv_apply]
  rfl

theorem exists_perm_hom [Module.Finite F U] (hd : 2 ≤ Module.finrank F U) {s : ℕ}
    (A : Subgroup ((⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U))
    (hperm : ∀ a ∈ A, ∀ i, ∃ j,
      (factorAlg i).map (a.conjAlgEquiv F).toAlgHom = factorAlg j) :
    ∃ π : A →* Equiv.Perm (Fin s), ∀ (a : A) (i : Fin s),
      (factorAlg i).map (a.1.conjAlgEquiv F).toAlgHom = factorAlg (π a i) := by
  choose pi hpi using fun (a : A) i => hperm a.1 a.2 i
  have hinj := factorAlg_index_injective (F := F) (U := U) hd (s := s)
  have hmul : ∀ (a b : A) i, pi (a * b) i = pi a (pi b i) := by
    intro a b i
    apply hinj
    have h1 := hpi (a * b) i
    have h2 := hpi b i
    have h3 := hpi a (pi b i)
    show factorAlg (F := F) (V := fun _ : Fin s => U) (pi (a * b) i) =
      factorAlg (F := F) (V := fun _ : Fin s => U) (pi a (pi b i))
    rw [← h1, ← h3, ← h2, Subalgebra.map_map, ← conjAlgHom_mul]
    rfl
  have hone : ∀ i, pi 1 i = i := by
    intro i
    apply hinj
    have h1 := hpi 1 i
    show factorAlg (F := F) (V := fun _ : Fin s => U) (pi 1 i) =
      factorAlg (F := F) (V := fun _ : Fin s => U) i
    rw [← h1]
    have : ((1 : A).1).conjAlgEquiv F = (1 : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U).conjAlgEquiv F := rfl
    rw [this, conjAlgHom_one, Subalgebra.map_id]
  let πf : A → Equiv.Perm (Fin s) := fun a =>
    ⟨pi a, pi a⁻¹, fun i => by rw [← hmul, inv_mul_cancel, hone],
      fun i => by rw [← hmul, mul_inv_cancel, hone]⟩
  refine ⟨MonoidHom.mk' πf (fun a b => Equiv.ext fun i => hmul a b i), hpi⟩

theorem finrank_piTensor_const [Module.Finite F U] (κ : Type*) [Fintype κ] :
    Module.finrank F (⨂[F] _ : κ, U) = Module.finrank F U ^ Fintype.card κ := by
  classical
  have := Module.finrank_eq_card_basis
    (Basis.piTensorProduct (fun _ : κ => Module.finBasis F U))
  rw [this]
  simp

end PermStructure


section Final

variable {F : Type u} [Field F] {U : Type u} [AddCommGroup U] [Module F U]

theorem transitive_tensor_quadratic_offender_small_exception [Finite F] [CharP F 2]
    [Module.Finite F U] (hd : 2 ≤ Module.finrank F U) {s : ℕ} (hs : 2 ≤ s)
    (A : Subgroup ((⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U)) [CFSG.IsElementaryAbelian 2 A]
    (hperm : ∀ a ∈ A, ∀ i, ∃ j, (factorAlg i).map (a.conjAlgEquiv F).toAlgHom = factorAlg j)
    (htrans : ∀ i j, ∃ a ∈ A, (factorAlg i).map (a.conjAlgEquiv F).toAlgHom = factorAlg j)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w)
    (hoff : Nat.card (⨂[F] _ : Fin s, U) ≤ Nat.card A * Nat.card (fixGL A)) :
    s = 2 ∧ Module.finrank F U = 2 ∧ Nat.card F = 2 := by
  classical
  have hmfW : Module.Finite F (⨂[F] _ : Fin s, U) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : Fin s => Module.finBasis F U))
  have hWfin : Finite (⨂[F] _ : Fin s, U) := Module.finite_of_finite F
  have hAfin : Finite A :=
    Finite.of_injective (fun a : A => ((a : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) :
      (⨂[F] _ : Fin s, U) → ⨂[F] _ : Fin s, U))
      (fun a b h => Subtype.ext (LinearEquiv.ext fun w => congrFun h w))
  obtain ⟨π, hπ⟩ := exists_perm_hom hd A hperm
  have hinj := factorAlg_index_injective (F := F) (U := U) hd (s := s)
  have htr : ∀ i j, ∃ a : A, π a i = j := by
    intro i j
    obtain ⟨a, ha, hmap⟩ := htrans i j
    refine ⟨⟨a, ha⟩, ?_⟩
    apply hinj
    show factorAlg (F := F) (V := fun _ : Fin s => U) (π ⟨a, ha⟩ i) =
      factorAlg (F := F) (V := fun _ : Fin s => U) j
    rw [← hπ ⟨a, ha⟩ i]
    exact hmap
  obtain ⟨a₀, A₁, S, ha₀1, hdich, hS1, hS2, hi₀⟩ := exists_halving hs A π htr
  have hsq : ∀ a : A, a * a = 1 := fun a => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.1
      (CFSG.IsElementaryAbelian.exponent_dvd_p 2 A) a
    rwa [pow_two] at this
  have hcomm : ∀ a b : A, a * b = b * a := fun a b =>
    (IsMulCommutative.is_comm (M := A)).comm a b
  have hτ2 : ∀ i, π a₀ (π a₀ i) = i := by
    intro i
    rw [← Equiv.Perm.mul_apply, ← map_mul, hsq, map_one]
    rfl
  obtain ⟨E, hE1, hE2, hE3⟩ := exists_regroup S (π a₀) (hS2 a₀ ha₀1) hτ2
  have : Fintype {i : Fin s // i ∈ S} := Fintype.ofFinite _
  have hmfP : Module.Finite F (⨂[F] _ : {i : Fin s // i ∈ S}, U) :=
    Module.Finite.of_basis (Basis.piTensorProduct (fun _ : {i : Fin s // i ∈ S} =>
      Module.finBasis F U))
  let Φ : (⨂[F] _ : Fin s, U) ≃ₗ[F] (⨂[F] _ : {i : Fin s // i ∈ S}, U) ⊗[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U) := phiEquiv E
  have hblock : ∀ b ∈ A₁.map A.subtype, ∃ x y : (⨂[F] _ : {i : Fin s // i ∈ S}, U) ≃ₗ[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U), ∀ p q, Φ (b (Φ.symm (p ⊗ₜ[F] q))) = x p ⊗ₜ[F] y q := by
    intro b hb
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.1 hb
    obtain ⟨g, hg⟩ := full_matrix_tensor_factor_normalizer hd hs (π b₀) b₀.1 (hπ b₀)
    obtain ⟨ν₁, ν₂, h1, h2⟩ := hE3 (π b₀) (hS1 b₀ hb₀)
    refine ⟨opT ν₁ (fun l => g (E.symm (Sum.inl l))),
      opT ν₂ (fun l => g (E.symm (Sum.inr l))), fun p q => ?_⟩
    have hg' : (b₀ : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) = opT (π b₀) g := hg
    show Φ (b₀.1 (Φ.symm (p ⊗ₜ[F] q))) = _
    rw [hg', ← TensorProduct.congr_tmul]
    exact phi_conj_block E (π b₀) g ν₁ ν₂ h1 h2 (p ⊗ₜ[F] q)
  have hswap : ∃ α β : (⨂[F] _ : {i : Fin s // i ∈ S}, U) ≃ₗ[F]
      (⨂[F] _ : {i : Fin s // i ∈ S}, U), ∀ p q,
      Φ (a₀.1 (Φ.symm (p ⊗ₜ[F] q))) = α q ⊗ₜ[F] β p := by
    obtain ⟨g, hg⟩ := full_matrix_tensor_factor_normalizer hd hs (π a₀) a₀.1 (hπ a₀)
    refine ⟨PiTensorProduct.congr (fun l => g (E.symm (Sum.inl l))),
      PiTensorProduct.congr (fun l => g (E.symm (Sum.inr l))), fun p q => ?_⟩
    have hg' : (a₀ : (⨂[F] _ : Fin s, U) ≃ₗ[F] ⨂[F] _ : Fin s, U) = opT (π a₀) g := hg
    show Φ (a₀.1 (Φ.symm (p ⊗ₜ[F] q))) = _
    rw [hg', phi_conj_swap E (π a₀) g hE1 hE2, TensorProduct.comm_tmul, TensorProduct.congr_tmul]
  have hcard : 1 ≤ Fintype.card {i : Fin s // i ∈ S} :=
    Fintype.card_pos_iff.2 ⟨⟨_, hi₀⟩⟩
  have hfinrank := finrank_piTensor_const (F := F) (U := U) {i : Fin s // i ∈ S}
  have hD : 2 ≤ Module.finrank F (⨂[F] _ : {i : Fin s // i ∈ S}, U) := by
    rw [hfinrank]
    calc 2 ≤ Module.finrank F U := hd
      _ = Module.finrank F U ^ 1 := (pow_one _).symm
      _ ≤ Module.finrank F U ^ Fintype.card {i : Fin s // i ∈ S} :=
        Nat.pow_le_pow_right (by omega) hcard
  have hA₁le : A₁.map A.subtype ≤ A := Subgroup.map_subtype_le A₁
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => congrArg Subtype.val (hsq ⟨a, ha⟩)
  have ha₀1' : a₀.1 ∉ A₁.map A.subtype := by
    rintro h
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 h
    exact ha₀1 (Subtype.ext hxa ▸ hx)
  have hidx : ∀ a ∈ A, a ∈ A₁.map A.subtype ∨ a * a₀.1 ∈ A₁.map A.subtype := by
    intro a ha
    rcases hdich ⟨a, ha⟩ with h | h
    · exact Or.inl (Subgroup.mem_map.2 ⟨⟨a, ha⟩, h, rfl⟩)
    · exact Or.inr (Subgroup.mem_map.2 ⟨⟨a, ha⟩ * a₀, h, rfl⟩)
  obtain ⟨hD2, hq2⟩ := transitive_two_factor_core hD Φ A (A₁.map A.subtype) hA₁le hAab hA2 a₀.1
    a₀.2 ha₀1' hidx hblock hswap hquad hoff
  rw [hfinrank] at hD2
  have hc1 : Fintype.card {i : Fin s // i ∈ S} = 1 := by
    by_contra hne
    have h2 : 2 ≤ Fintype.card {i : Fin s // i ∈ S} := by omega
    have : Module.finrank F U ^ 2 ≤ Module.finrank F U ^ Fintype.card {i : Fin s // i ∈ S} :=
      Nat.pow_le_pow_right (by omega) h2
    have h4 : 2 * 2 ≤ Module.finrank F U ^ 2 := by
      rw [pow_two]; exact Nat.mul_le_mul hd hd
    omega
  rw [hc1, pow_one] at hD2
  have hsum : s = 2 * Fintype.card {i : Fin s // i ∈ S} := by
    have := Fintype.card_congr E
    rw [Fintype.card_sum, Fintype.card_fin] at this
    omega
  exact ⟨by omega, hD2, hq2⟩

end Final


end CFSG.QuasithinUnique.Setup.Offender

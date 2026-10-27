module

public import CFSG.CharacterTheory.Semidihedral.CentralTransferSplitting

public noncomputable section

namespace CFSG.Semidihedral.CentralPrimeExtensions

universe u v w x

variable {A : Type u} {E₁ : Type v} {E₂ : Type w} {G : Type x}
  [Group A] [Group E₁] [Group E₂] [Group G]

@[expose] def fiberProduct (π₁ : E₁ →* G) (π₂ : E₂ →* G) : Subgroup (E₁ × E₂) :=
  (π₁.comp (MonoidHom.fst E₁ E₂)).eqLocus (π₂.comp (MonoidHom.snd E₁ E₂))

theorem mem_fiberProduct (π₁ : E₁ →* G) (π₂ : E₂ →* G) (z : E₁ × E₂) :
    z ∈ fiberProduct π₁ π₂ ↔ π₁ z.1 = π₂ z.2 := Iff.rfl

@[expose] def firstProjection (π₁ : E₁ →* G) (π₂ : E₂ →* G) :
    fiberProduct π₁ π₂ →* E₁ :=
  (MonoidHom.fst E₁ E₂).comp (fiberProduct π₁ π₂).subtype

@[expose] def secondProjection (π₁ : E₁ →* G) (π₂ : E₂ →* G) :
    fiberProduct π₁ π₂ →* E₂ :=
  (MonoidHom.snd E₁ E₂).comp (fiberProduct π₁ π₂).subtype

@[expose] def fiberQuotient (π₁ : E₁ →* G) (π₂ : E₂ →* G) :
    fiberProduct π₁ π₂ →* G := π₁.comp (firstProjection π₁ π₂)

theorem fiber_quotient_second (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (z : fiberProduct π₁ π₂) :
    fiberQuotient π₁ π₂ z = π₂ (secondProjection π₁ π₂ z) := z.property

theorem fiberQuotient_surjective (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (hπ₁ : Function.Surjective π₁) (hπ₂ : Function.Surjective π₂) :
    Function.Surjective (fiberQuotient π₁ π₂) := by
  intro g
  obtain ⟨a, ha⟩ := hπ₁ g
  obtain ⟨b, hb⟩ := hπ₂ g
  exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩

@[expose] def centralDifference {D H : Type*} [Group D] [Group H]
    (K : Subgroup H) (hK : K ≤ Subgroup.center H) (f g : D →* H)
    (hfg : ∀ d, (f d)⁻¹ * g d ∈ K) : D →* K where
  toFun d := ⟨(f d)⁻¹ * g d, hfg d⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    change (f (a * b))⁻¹ * g (a * b) =
      ((f a)⁻¹ * g a) * ((f b)⁻¹ * g b)
    rw [map_mul, map_mul, mul_inv_rev]
    have hc := Subgroup.mem_center_iff.mp (hK (hfg a)) ((f b)⁻¹)
    calc
      ((f b)⁻¹ * (f a)⁻¹) * (g a * g b) =
          ((f b)⁻¹ * ((f a)⁻¹ * g a)) * g b := by group
      _ = (((f a)⁻¹ * g a) * (f b)⁻¹) * g b := by rw [hc]
      _ = ((f a)⁻¹ * g a) * ((f b)⁻¹ * g b) := by group

theorem centralDifference_apply {D H : Type*} [Group D] [Group H]
    (K : Subgroup H) (hK : K ≤ Subgroup.center H) (f g : D →* H)
    (hfg : ∀ d, (f d)⁻¹ * g d ∈ K) (d : D) :
    (centralDifference K hK f g hfg d : H) = (f d)⁻¹ * g d := rfl

@[expose] def centralCoefficient {D H : Type*} [Group D] [Group H]
    (ι : A →* H) (hι : Function.Injective ι)
    (hc : ι.range ≤ Subgroup.center H) (f g : D →* H)
    (hfg : ∀ d, (f d)⁻¹ * g d ∈ ι.range) : D →* A :=
  (MonoidHom.ofInjective hι).symm.toMonoidHom.comp
    (centralDifference ι.range hc f g hfg)

theorem centralCoefficient_spec {D H : Type*} [Group D] [Group H]
    (ι : A →* H) (hι : Function.Injective ι)
    (hc : ι.range ≤ Subgroup.center H) (f g : D →* H)
    (hfg : ∀ d, (f d)⁻¹ * g d ∈ ι.range) (d : D) :
    ι (centralCoefficient ι hι hc f g hfg d) = (f d)⁻¹ * g d := by
  let e := MonoidHom.ofInjective hι
  have h := congrArg (fun z : ι.range => (z : H))
    (e.apply_symm_apply (centralDifference ι.range hc f g hfg d))
  exact h

@[expose] def localFirst (π₁ : E₁ →* G) (π₂ : E₂ →* G) (P : Subgroup G) :
    P.comap (fiberQuotient π₁ π₂) →* P.comap π₁ :=
  ((firstProjection π₁ π₂).comp
    (P.comap (fiberQuotient π₁ π₂)).subtype).codRestrict (P.comap π₁)
      (fun z => z.property)

@[expose] def transportedFirst (π₁ : E₁ →* G) (π₂ : E₂ →* G) (P : Subgroup G)
    (α : P.comap π₁ ≃* P.comap π₂) :
    P.comap (fiberQuotient π₁ π₂) →* E₂ :=
  (P.comap π₂).subtype.comp (α.toMonoidHom.comp (localFirst π₁ π₂ P))

@[expose] def localSecond (π₁ : E₁ →* G) (π₂ : E₂ →* G) (P : Subgroup G) :
    P.comap (fiberQuotient π₁ π₂) →* E₂ :=
  (secondProjection π₁ π₂).comp (P.comap (fiberQuotient π₁ π₂)).subtype

theorem local_difference_mem_range (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (P : Subgroup G) (α : P.comap π₁ ≃* P.comap π₂)
    (hα : ∀ x : P.comap π₁, π₂ (α x) = π₁ x)
    (ι₂ : A →* E₂) (hker : π₂.ker = ι₂.range)
    (z : P.comap (fiberQuotient π₁ π₂)) :
    (transportedFirst π₁ π₂ P α z)⁻¹ * localSecond π₁ π₂ P z ∈ ι₂.range := by
  rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
  change (π₂ (α (localFirst π₁ π₂ P z)))⁻¹ *
    π₂ (secondProjection π₁ π₂ z.val) = 1
  rw [hα]
  have h := fiber_quotient_second π₁ π₂ z.val
  change π₁ (localFirst π₁ π₂ P z) = π₂ (secondProjection π₁ π₂ z.val) at h
  rw [h, inv_mul_cancel]

@[expose] def sylowDiscrepancy (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (P : Subgroup G) (α : P.comap π₁ ≃* P.comap π₂)
    (hα : ∀ x : P.comap π₁, π₂ (α x) = π₁ x)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂) (hker : π₂.ker = ι₂.range) :
    P.comap (fiberQuotient π₁ π₂) →* A :=
  centralCoefficient ι₂ hι₂ hc₂ (transportedFirst π₁ π₂ P α)
    (localSecond π₁ π₂ P) (local_difference_mem_range π₁ π₂ P α hα ι₂ hker)

theorem sylowDiscrepancy_spec (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (P : Subgroup G) (α : P.comap π₁ ≃* P.comap π₂)
    (hα : ∀ x : P.comap π₁, π₂ (α x) = π₁ x)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂) (hker : π₂.ker = ι₂.range)
    (z : P.comap (fiberQuotient π₁ π₂)) :
    ι₂ (sylowDiscrepancy π₁ π₂ P α hα ι₂ hι₂ hc₂ hker z) =
      (α (localFirst π₁ π₂ P z) : E₂)⁻¹ * (z.val.val).2 :=
  centralCoefficient_spec ι₂ hι₂ hc₂ (transportedFirst π₁ π₂ P α)
    (localSecond π₁ π₂ P) (local_difference_mem_range π₁ π₂ P α hα ι₂ hker) z


abbrev embeddedCommGroup (ι : A →* E₂) (hι : Function.Injective ι)
    (hc : ι.range ≤ Subgroup.center E₂) : CommGroup A where
  __ := (inferInstance : Group A)
  mul_comm a b := hι (by
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (hc ⟨b, rfl⟩) (ι a))

theorem quotient_kernel_embedding (π : E₁ →* G) (ι : A →* E₁)
    (hker : π.ker = ι.range) (a : A) : π (ι a) = 1 :=
  MonoidHom.mem_ker.mp (hker.symm ▸ (show ι a ∈ ι.range from ⟨a, rfl⟩))

@[expose] def kernelInto (π : E₁ →* G) (ι : A →* E₁)
    (hker : π.ker = ι.range) (P : Subgroup G) : A →* P.comap π :=
  ι.codRestrict (P.comap π) (fun a => by
    change π (ι a) ∈ P
    rw [quotient_kernel_embedding π ι hker]
    exact P.one_mem)

@[expose] def leftKernel (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range) :
    A →* fiberProduct π₁ π₂ :=
  (ι₁.prod (1 : A →* E₂)).codRestrict (fiberProduct π₁ π₂) (fun a => by
    change π₁ (ι₁ a) = π₂ 1
    rw [quotient_kernel_embedding π₁ ι₁ hker₁, map_one])

@[expose] def rightKernel (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₂ : A →* E₂) (hker₂ : π₂.ker = ι₂.range) :
    A →* fiberProduct π₁ π₂ :=
  ((1 : A →* E₁).prod ι₂).codRestrict (fiberProduct π₁ π₂) (fun a => by
    change π₁ 1 = π₂ (ι₂ a)
    rw [quotient_kernel_embedding π₂ ι₂ hker₂, map_one])

theorem leftKernel_mem_center (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range)
    (hc₁ : ι₁.range ≤ Subgroup.center E₁) (a : A) :
    leftKernel π₁ π₂ ι₁ hker₁ a ∈ Subgroup.center (fiberProduct π₁ π₂) := by
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact Subgroup.mem_center_iff.mp (hc₁ ⟨a, rfl⟩) z.val.1
  · change z.val.2 * 1 = 1 * z.val.2
    simp

theorem rightKernel_mem_center (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₂ : A →* E₂) (hker₂ : π₂.ker = ι₂.range)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂) (a : A) :
    rightKernel π₁ π₂ ι₂ hker₂ a ∈ Subgroup.center (fiberProduct π₁ π₂) := by
  apply Subgroup.mem_center_iff.mpr
  intro z
  apply Subtype.ext
  apply Prod.ext
  · change z.val.1 * 1 = 1 * z.val.1
    simp
  · exact Subgroup.mem_center_iff.mp (hc₂ ⟨a, rfl⟩) z.val.2

theorem leftKernel_mem_preimage (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range) (P : Subgroup G) (a : A) :
    leftKernel π₁ π₂ ι₁ hker₁ a ∈ P.comap (fiberQuotient π₁ π₂) := by
  change π₁ (ι₁ a) ∈ P
  rw [quotient_kernel_embedding π₁ ι₁ hker₁]
  exact P.one_mem

theorem rightKernel_mem_preimage (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (ι₂ : A →* E₂) (hker₂ : π₂.ker = ι₂.range) (P : Subgroup G) (a : A) :
    rightKernel π₁ π₂ ι₂ hker₂ a ∈ P.comap (fiberQuotient π₁ π₂) := by
  change π₁ 1 ∈ P
  rw [map_one]
  exact P.one_mem

theorem discrepancy_leftKernel (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (P : Subgroup G) (α : P.comap π₁ ≃* P.comap π₂)
    (hα : ∀ x : P.comap π₁, π₂ (α x) = π₁ x)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂) (hker₂ : π₂.ker = ι₂.range)
    (hαι : ∀ a : A, (α (kernelInto π₁ ι₁ hker₁ P a) : E₂) = ι₂ a) (a : A) :
    sylowDiscrepancy π₁ π₂ P α hα ι₂ hι₂ hc₂ hker₂
      ⟨leftKernel π₁ π₂ ι₁ hker₁ a,
        leftKernel_mem_preimage π₁ π₂ ι₁ hker₁ P a⟩ = a⁻¹ := by
  apply hι₂
  rw [sylowDiscrepancy_spec]
  have hx : localFirst π₁ π₂ P
      ⟨leftKernel π₁ π₂ ι₁ hker₁ a,
        leftKernel_mem_preimage π₁ π₂ ι₁ hker₁ P a⟩ =
      kernelInto π₁ ι₁ hker₁ P a := Subtype.ext rfl
  rw [hx, hαι]
  change (ι₂ a)⁻¹ * 1 = ι₂ (a⁻¹)
  rw [mul_one, map_inv]

theorem discrepancy_rightKernel (π₁ : E₁ →* G) (π₂ : E₂ →* G)
    (P : Subgroup G) (α : P.comap π₁ ≃* P.comap π₂)
    (hα : ∀ x : P.comap π₁, π₂ (α x) = π₁ x)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂) (hker₂ : π₂.ker = ι₂.range) (a : A) :
    sylowDiscrepancy π₁ π₂ P α hα ι₂ hι₂ hc₂ hker₂
      ⟨rightKernel π₁ π₂ ι₂ hker₂ a,
        rightKernel_mem_preimage π₁ π₂ ι₂ hker₂ P a⟩ = a := by
  apply hι₂
  rw [sylowDiscrepancy_spec]
  have hx : localFirst π₁ π₂ P
      ⟨rightKernel π₁ π₂ ι₂ hker₂ a,
        rightKernel_mem_preimage π₁ π₂ ι₂ hker₂ P a⟩ = 1 := Subtype.ext rfl
  rw [hx, map_one]
  change (1 : E₂)⁻¹ * ι₂ a = ι₂ a
  simp

theorem exists_discrepancy_transfer [Finite E₁] [Finite E₂] [Finite G]
    (p : ℕ) (hp : p.Prime) (hA : Nat.card A = p)
    (π₁ : E₁ →* G) (hπ₁ : Function.Surjective π₁)
    (π₂ : E₂ →* G) (hπ₂ : Function.Surjective π₂)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range)
    (hc₁ : ι₁.range ≤ Subgroup.center E₁)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hker₂ : π₂.ker = ι₂.range) (hc₂ : ι₂.range ≤ Subgroup.center E₂)
    (P : Sylow p G) (α : (P : Subgroup G).comap π₁ ≃* (P : Subgroup G).comap π₂)
    (hα : ∀ x : (P : Subgroup G).comap π₁, π₂ (α x) = π₁ x)
    (hαι : ∀ a : A, (α (kernelInto π₁ ι₁ hker₁ P a) : E₂) = ι₂ a) :
    ∃ T : fiberProduct π₁ π₂ →* A,
      (∀ a : A, T (leftKernel π₁ π₂ ι₁ hker₁ a) = a⁻¹) ∧
      (∀ a : A, T (rightKernel π₁ π₂ ι₂ hker₂ a) = a) := by
  let : Fact p.Prime := ⟨hp⟩
  let : CommGroup A := embeddedCommGroup ι₂ hι₂ hc₂
  have hpA : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let U := (P : Subgroup G).comap (fiberQuotient π₁ π₂)
  have hindex : p.Coprime U.index := by
    rw [Subgroup.index_comap_of_surjective _ (fiberQuotient_surjective π₁ π₂ hπ₁ hπ₂)]
    exact hp.coprime_iff_not_dvd.mpr P.not_dvd_index
  let φ := sylowDiscrepancy π₁ π₂ P α hα ι₂ hι₂ hc₂ hker₂
  obtain ⟨T, hT⟩ := CentralTransferSplitting.exists_normalized_transfer p U hpA hindex φ
  refine ⟨T, ?_, ?_⟩
  · intro a
    rw [hT _ (leftKernel_mem_preimage π₁ π₂ ι₁ hker₁ P a)
      (leftKernel_mem_center π₁ π₂ ι₁ hker₁ hc₁ a)]
    exact discrepancy_leftKernel π₁ π₂ P α hα ι₁ hker₁ ι₂ hι₂ hc₂ hker₂ hαι a
  · intro a
    rw [hT _ (rightKernel_mem_preimage π₁ π₂ ι₂ hker₂ P a)
      (rightKernel_mem_center π₁ π₂ ι₂ hker₂ hc₂ a)]
    exact discrepancy_rightKernel π₁ π₂ P α hα ι₂ hι₂ hc₂ hker₂ a


theorem fiber_equiv_of_kernel_transfer
    (π₁ : E₁ →* G) (hπ₁ : Function.Surjective π₁)
    (π₂ : E₂ →* G) (hπ₂ : Function.Surjective π₂)
    (ι₁ : A →* E₁) (hker₁ : π₁.ker = ι₁.range)
    (ι₂ : A →* E₂) (hker₂ : π₂.ker = ι₂.range)
    (T : fiberProduct π₁ π₂ →* A)
    (hTL : ∀ a : A, T (leftKernel π₁ π₂ ι₁ hker₁ a) = a⁻¹)
    (hTR : ∀ a : A, T (rightKernel π₁ π₂ ι₂ hker₂ a) = a) :
    ∃ F : E₁ ≃* E₂,
      (∀ x : E₁, π₂ (F x) = π₁ x) ∧ (∀ a : A, F (ι₁ a) = ι₂ a) := by
  let K := T.ker
  let f₁ : K →* E₁ := (firstProjection π₁ π₂).comp K.subtype
  let f₂ : K →* E₂ := (secondProjection π₁ π₂).comp K.subtype
  have hf₁ker : f₁.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro r hr
    have hx : r.val.val.1 = 1 := MonoidHom.mem_ker.mp hr
    have hy : r.val.val.2 ∈ π₂.ker := by
      rw [MonoidHom.mem_ker]
      exact r.val.property.symm.trans (by
        change π₁ (r.val.val.1) = 1
        rw [hx, map_one])
    obtain ⟨a, ha⟩ := hker₂ ▸ hy
    have heq : r.val = rightKernel π₁ π₂ ι₂ hker₂ a := by
      apply Subtype.ext
      exact Prod.ext hx ha.symm
    have hTr : T r.val = 1 := r.property
    rw [heq, hTR] at hTr
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact hx
    · change r.val.val.2 = 1
      rw [← ha, hTr, map_one]
  have hf₂ker : f₂.ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro r hr
    have hy : r.val.val.2 = 1 := MonoidHom.mem_ker.mp hr
    have hx : r.val.val.1 ∈ π₁.ker := by
      rw [MonoidHom.mem_ker]
      exact r.val.property.trans (by
        change π₂ (r.val.val.2) = 1
        rw [hy, map_one])
    obtain ⟨a, ha⟩ := hker₁ ▸ hx
    have heq : r.val = leftKernel π₁ π₂ ι₁ hker₁ a := by
      apply Subtype.ext
      exact Prod.ext ha.symm hy
    have hTr : T r.val = 1 := r.property
    rw [heq, hTL, inv_eq_one] at hTr
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · change r.val.val.1 = 1
      rw [← ha, hTr, map_one]
    · exact hy
  have hf₁surj : Function.Surjective f₁ := by
    intro x
    obtain ⟨y, hy⟩ := hπ₂ (π₁ x)
    let w : fiberProduct π₁ π₂ := ⟨(x, y), hy.symm⟩
    let r : fiberProduct π₁ π₂ := w * (rightKernel π₁ π₂ ι₂ hker₂ (T w))⁻¹
    have hr : r ∈ K := by
      change T r = 1
      dsimp only [r]
      rw [map_mul, map_inv, hTR, mul_inv_cancel]
    refine ⟨⟨r, hr⟩, ?_⟩
    change x * 1⁻¹ = x
    simp
  have hf₂surj : Function.Surjective f₂ := by
    intro y
    obtain ⟨x, hx⟩ := hπ₁ (π₂ y)
    let w : fiberProduct π₁ π₂ := ⟨(x, y), hx⟩
    let r : fiberProduct π₁ π₂ := w * leftKernel π₁ π₂ ι₁ hker₁ (T w)
    have hr : r ∈ K := by
      change T r = 1
      dsimp only [r]
      rw [map_mul, hTL, mul_inv_cancel]
    refine ⟨⟨r, hr⟩, ?_⟩
    change y * 1 = y
    simp
  let e₁ : K ≃* E₁ := MulEquiv.ofBijective f₁
    ⟨(MonoidHom.ker_eq_bot_iff f₁).mp hf₁ker, hf₁surj⟩
  let e₂ : K ≃* E₂ := MulEquiv.ofBijective f₂
    ⟨(MonoidHom.ker_eq_bot_iff f₂).mp hf₂ker, hf₂surj⟩
  refine ⟨e₁.symm.trans e₂, ?_, ?_⟩
  · intro x
    let r := e₁.symm x
    have hr : r.val.val.1 = x := e₁.apply_symm_apply x
    change π₂ (r.val.val.2) = π₁ x
    rw [← hr]
    exact r.val.property.symm
  · intro a
    let d : fiberProduct π₁ π₂ :=
      leftKernel π₁ π₂ ι₁ hker₁ a * rightKernel π₁ π₂ ι₂ hker₂ a
    have hd : d ∈ K := by
      change T d = 1
      dsimp only [d]
      rw [map_mul, hTL, hTR, inv_mul_cancel]
    let r : K := ⟨d, hd⟩
    have hr₁ : e₁ r = ι₁ a := by
      change ι₁ a * 1 = ι₁ a
      simp
    have hr₂ : e₂ r = ι₂ a := by
      change 1 * ι₂ a = ι₂ a
      simp
    change e₂ (e₁.symm (ι₁ a)) = ι₂ a
    rw [← hr₁, e₁.symm_apply_apply, hr₂]

theorem central_prime_extensions_determined_on_sylow
    [Finite E₁] [Finite E₂] [Finite G]
    (p : ℕ) (hp : p.Prime) (hA : Nat.card A = p)
    (ι₁ : A →* E₁) (hι₁ : Function.Injective ι₁)
    (hc₁ : ι₁.range ≤ Subgroup.center E₁)
    (π₁ : E₁ →* G) (hπ₁ : Function.Surjective π₁) (hker₁ : π₁.ker = ι₁.range)
    (ι₂ : A →* E₂) (hι₂ : Function.Injective ι₂)
    (hc₂ : ι₂.range ≤ Subgroup.center E₂)
    (π₂ : E₂ →* G) (hπ₂ : Function.Surjective π₂) (hker₂ : π₂.ker = ι₂.range)
    (P : Sylow p G) (α : (P : Subgroup G).comap π₁ ≃* (P : Subgroup G).comap π₂)
    (hα : ∀ x : (P : Subgroup G).comap π₁, π₂ (α x) = π₁ x)
    (hαι : ∀ a : A, (α (kernelInto π₁ ι₁ hker₁ P a) : E₂) = ι₂ a) :
    ∃ F : E₁ ≃* E₂,
      (∀ x : E₁, π₂ (F x) = π₁ x) ∧ (∀ a : A, F (ι₁ a) = ι₂ a) := by
  let : Finite A := Finite.of_injective ι₁ hι₁
  obtain ⟨T, hTL, hTR⟩ := exists_discrepancy_transfer p hp hA
    π₁ hπ₁ π₂ hπ₂ ι₁ hker₁ hc₁ ι₂ hι₂ hker₂ hc₂ P α hα hαι
  exact fiber_equiv_of_kernel_transfer π₁ hπ₁ π₂ hπ₂ ι₁ hker₁ ι₂ hker₂ T hTL hTR

end CFSG.Semidihedral.CentralPrimeExtensions

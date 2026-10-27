module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutCore
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLargeTorus

public section

namespace CFSG.AGLEmbedding.UnitaryModel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.UnitaryThreeRecognition.Model

section Finite

theorem inv_mem_of_forall_mem {G : Type*} [Group G] [Finite G] (H : Subgroup G) (γ : MulAut G)
    (h : ∀ t ∈ H, γ t ∈ H) : ∀ t ∈ H, γ⁻¹ t ∈ H := by
  have hmap : H.map γ.toMonoidHom = H := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨t, ht, rfl⟩
      exact h t ht
    · rw [Subgroup.card_map_of_injective (f := γ.toMonoidHom) γ.injective]
  intro t ht
  have : t ∈ H.map γ.toMonoidHom := by
    rw [hmap]
    exact ht
  obtain ⟨s, hs, rfl⟩ := this
  simpa using hs

end Finite

section Decomp

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem exists_mem_rootGroup_torus_stable (hq : 2 < p ^ f)
    (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ) :
    ∃ u ∈ rootGroup J hJ, ∀ t ∈ torusGroup J hJ, u⁻¹ * α t * u ∈ torusGroup J hJ := by
  have hBN := normalizer_rootGroup_eq_stabilizer J hJ hK hfix hq
  have hmapR : (rootGroup J hJ).map α.toMonoidHom = rootGroup J hJ := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨r, hr, rfl⟩
      exact hαR r hr
    · rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
  have hN : (Subgroup.normalizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))).map
      α.toMonoidHom = Subgroup.normalizer
        (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
    rw [Subgroup.map_equiv_normalizer_eq, hmapR]
  have hαB : ∀ g, α g • pinf J hJ = pinf J hJ ↔ g • pinf J hJ = pinf J hJ := by
    intro g
    have := mem_map_iff α (Subgroup.normalizer
      (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) g
    rw [hN, hBN] at this
    exact this
  have hw : α (weyl J hJ) • pinf J hJ ≠ pinf J hJ := fun h =>
    weyl_not_mem_stabilizer J hJ ((hαB _).1 h)
  obtain ⟨u, huR, hu⟩ := exists_mem_rootGroup_smul_pzero_eq J hJ _ hw
  have hu_inf : u • pinf J hJ = pinf J hJ := rootGroup_le_stabilizer J hJ huR
  refine ⟨u, huR, fun t ht => ?_⟩
  rw [← stabilizer_pinf_inf_stabilizer_pzero J hJ (p ^ f) hK hfix] at ht ⊢
  obtain ⟨ht_inf, ht_zero⟩ := ht
  refine ⟨?_, ?_⟩
  · show (u⁻¹ * α t * u) • pinf J hJ = pinf J hJ
    rw [mul_smul, mul_smul, hu_inf, (hαB t).2 ht_inf, inv_smul_eq_iff.2 hu_inf.symm]
  · show (u⁻¹ * α t * u) • pzero J hJ = pzero J hJ
    have ht_zero' : t • pzero J hJ = pzero J hJ := ht_zero
    have hs : ((weyl J hJ)⁻¹ * t * weyl J hJ) • pinf J hJ = pinf J hJ := by
      rw [mul_smul, mul_smul, weyl_smul_pinf, ht_zero', weyl_inv, weyl_smul_pzero]
    have hαt : α t • (α (weyl J hJ) • pinf J hJ) = α (weyl J hJ) • pinf J hJ := by
      rw [← mul_smul, ← map_mul]
      have h3 : t * weyl J hJ = weyl J hJ * ((weyl J hJ)⁻¹ * t * weyl J hJ) := by group
      rw [h3, map_mul, mul_smul, (hαB _).2 hs]
    rw [← hu] at hαt
    rw [mul_smul, mul_smul, hαt, inv_smul_smul]

end Decomp

section Induced

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

omit [Finite K] [Fact p.Prime] in
@[expose] noncomputable def fstAdd (r : ↥(rootGroup J hJ)) : K :=
  Multiplicative.toAdd (fstHom J hJ r)

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_mul (r s : ↥(rootGroup J hJ)) :
    fstAdd J hJ (r * s) = fstAdd J hJ r + fstAdd J hJ s := by
  simp [fstAdd]

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_inv (r : ↥(rootGroup J hJ)) : fstAdd J hJ r⁻¹ = - fstAdd J hJ r := by
  simp [fstAdd]

omit [Finite K] [Fact p.Prime] in
theorem fstAdd_conj (k : Kˣ) (y : ↥(rootGroup J hJ))
    (hy : torus J hJ k * (y : ProjectiveSpecialUnitaryMatrixGroup J) * (torus J hJ k)⁻¹ ∈
      rootGroup J hJ) :
    fstAdd J hJ ⟨torus J hJ k * (y : ProjectiveSpecialUnitaryMatrixGroup J) * (torus J hJ k)⁻¹,
      hy⟩ = ((lamUnit J k : Kˣ) : K) * fstAdd J hJ y := by
  have := fstHom_conj J hJ k y hy
  simp only [fstAdd, this, toAdd_ofAdd]

include hK hfix

theorem fstAdd_surjective : Function.Surjective (fstAdd J hJ) := by
  intro a
  obtain ⟨r, hr⟩ := fstHom_surjective J hJ hK hfix (Multiplicative.ofAdd a)
  exact ⟨r, by simp [fstAdd, hr]⟩

theorem fstAdd_eq_zero_iff (r : ↥(rootGroup J hJ)) :
    fstAdd J hJ r = 0 ↔ (r : ProjectiveSpecialUnitaryMatrixGroup J) ∈ rootGroup J hJ ⊓
      Subgroup.centralizer (rootGroup J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  rw [← fstHom_eq_one_iff J hJ hK hfix]
  exact toAdd_eq_zero

theorem fstAdd_zero_of_central (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hβ' : ∀ r ∈ rootGroup J hJ, β⁻¹ r ∈ rootGroup J hJ) (r : ↥(rootGroup J hJ))
    (hr : fstAdd J hJ r = 0) (hr' : β r ∈ rootGroup J hJ) : fstAdd J hJ ⟨β r, hr'⟩ = 0 := by
  rw [fstAdd_eq_zero_iff J hJ hK hfix] at hr ⊢
  refine ⟨hr', Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  have hc := Subgroup.mem_centralizer_iff.1 hr.2 (β⁻¹ s) (hβ' s hs)
  have := congrArg β hc
  simpa [map_mul] using this

theorem exists_addMonoidHom (g : ↥(rootGroup J hJ) →* ↥(rootGroup J hJ))
    (hg : ∀ r, fstAdd J hJ r = 0 → fstAdd J hJ (g r) = 0) :
    ∃ A : K →+ K, ∀ r, A (fstAdd J hJ r) = fstAdd J hJ (g r) := by
  have hsurj := fstAdd_surjective J hJ hK hfix
  set sec : K → ↥(rootGroup J hJ) := Function.surjInv hsurj with hsec
  have hsec' : ∀ x, fstAdd J hJ (sec x) = x := Function.surjInv_eq hsurj
  have key : ∀ r s, fstAdd J hJ r = fstAdd J hJ s → fstAdd J hJ (g r) = fstAdd J hJ (g s) := by
    intro r s h
    have h1 : fstAdd J hJ (s⁻¹ * r) = 0 := by
      rw [fstAdd_mul, fstAdd_inv, h]
      ring
    have h2 := hg _ h1
    rw [map_mul, map_inv, fstAdd_mul, fstAdd_inv] at h2
    linear_combination h2
  refine ⟨AddMonoidHom.mk' (fun x => fstAdd J hJ (g (sec x))) ?_, ?_⟩
  · intro x y
    have h1 : fstAdd J hJ (sec (x + y)) = fstAdd J hJ (sec x * sec y) := by
      rw [fstAdd_mul, hsec', hsec', hsec']
    have h2 := key _ _ h1
    rw [map_mul, fstAdd_mul] at h2
    exact h2
  · intro r
    exact key _ _ (hsec' _)

theorem exists_indAdd (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hαR : ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ)
    (hαR' : ∀ r ∈ rootGroup J hJ, α⁻¹ r ∈ rootGroup J hJ) :
    ∃ A : K ≃+ K, ∀ r : ↥(rootGroup J hJ), A (fstAdd J hJ r) = fstAdd J hJ ⟨α r, hαR r r.2⟩ := by
  let g : ↥(rootGroup J hJ) →* ↥(rootGroup J hJ) :=
    (α.toMonoidHom.comp (rootGroup J hJ).subtype).codRestrict _ (fun r => hαR r r.2)
  let g' : ↥(rootGroup J hJ) →* ↥(rootGroup J hJ) :=
    ((α⁻¹).toMonoidHom.comp (rootGroup J hJ).subtype).codRestrict _ (fun r => hαR' r r.2)
  have hgval : ∀ r : ↥(rootGroup J hJ), ((g r : ↥(rootGroup J hJ)) :
      ProjectiveSpecialUnitaryMatrixGroup J) = α r := fun r => rfl
  have hg'val : ∀ r : ↥(rootGroup J hJ), ((g' r : ↥(rootGroup J hJ)) :
      ProjectiveSpecialUnitaryMatrixGroup J) = α⁻¹ r := fun r => rfl
  obtain ⟨A, hA⟩ := exists_addMonoidHom J hJ hK hfix g fun r hr =>
    fstAdd_zero_of_central J hJ hK hfix α hαR' r hr (hαR r r.2)
  obtain ⟨A', hA'⟩ := exists_addMonoidHom J hJ hK hfix g' fun r hr =>
    fstAdd_zero_of_central J hJ hK hfix α⁻¹ (by simpa using hαR) r hr (hαR' r r.2)
  have hl : ∀ x, A' (A x) = x := by
    intro x
    obtain ⟨r, rfl⟩ := fstAdd_surjective J hJ hK hfix x
    rw [hA, hA']
    congr 1
    apply Subtype.ext
    rw [hg'val, hgval]
    simp
  have hr : ∀ x, A (A' x) = x := by
    intro x
    obtain ⟨r, rfl⟩ := fstAdd_surjective J hJ hK hfix x
    rw [hA', hA]
    congr 1
    apply Subtype.ext
    rw [hgval, hg'val]
    simp
  exact ⟨{ toFun := A, invFun := A', left_inv := hl, right_inv := hr, map_add' := A.map_add }, hA⟩

end Induced

section Semilinear

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem indAdd_lam_mul (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγR : ∀ r ∈ rootGroup J hJ, γ r ∈ rootGroup J hJ) (A : K ≃+ K)
    (hA : ∀ r : ↥(rootGroup J hJ), A (fstAdd J hJ r) = fstAdd J hJ ⟨γ r, hγR r r.2⟩)
    {k k' : Kˣ} (hkk' : γ (torus J hJ k) = torus J hJ k') (x : K) :
    A (((lamUnit J k : Kˣ) : K) * x) = ((lamUnit J k' : Kˣ) : K) * A x := by
  obtain ⟨r, rfl⟩ := fstAdd_surjective J hJ hK hfix x
  have htN : ∀ (m : Kˣ) (y : ProjectiveSpecialUnitaryMatrixGroup J), y ∈ rootGroup J hJ →
      torus J hJ m * y * (torus J hJ m)⁻¹ ∈ rootGroup J hJ := fun m y hy =>
    (Subgroup.mem_normalizer_iff.1
      (torusGroup_le_normalizer_rootGroup J hJ (torus_mem_torusGroup J hJ m)) y).1 hy
  have hy := htN k r r.2
  rw [← fstAdd_conj J hJ k r hy, hA]
  have hy' := htN k' (γ r) (hγR r r.2)
  have h2 : (⟨γ (torus J hJ k * r * (torus J hJ k)⁻¹), hγR _ hy⟩ : ↥(rootGroup J hJ)) =
      ⟨torus J hJ k' * γ r * (torus J hJ k')⁻¹, hy'⟩ := by
    apply Subtype.ext
    simp only [map_mul, map_inv, hkk']
  rw [h2, fstAdd_conj J hJ k' ⟨γ r, hγR r r.2⟩ hy', hA]

theorem exists_semilinear (hq : 2 < p ^ f) (γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hγR : ∀ r ∈ rootGroup J hJ, γ r ∈ rootGroup J hJ)
    (hγR' : ∀ r ∈ rootGroup J hJ, γ⁻¹ r ∈ rootGroup J hJ)
    (hγT : ∀ t ∈ torusGroup J hJ, γ t ∈ torusGroup J hJ) :
    ∃ (c : Kˣ) (σ : K ≃+* K), (∀ r : ↥(rootGroup J hJ),
      fstAdd J hJ ⟨γ r, hγR r r.2⟩ = (c : K) * σ (fstAdd J hJ r)) ∧
      ∀ {k k' : Kˣ}, γ (torus J hJ k) = torus J hJ k' →
        σ ((lamUnit J k : Kˣ) : K) = (lamUnit J k' : Kˣ) := by
  obtain ⟨A, hA⟩ := exists_indAdd J hJ hK hfix γ hγR hγR'
  have hA' : ∀ r : ↥(rootGroup J hJ),
      A.symm (fstAdd J hJ r) = fstAdd J hJ ⟨γ⁻¹ r, hγR' r r.2⟩ := by
    intro r
    rw [AddEquiv.symm_apply_eq, hA]
    congr 1
    apply Subtype.ext
    simp
  have hγT' := inv_mem_of_forall_mem (torusGroup J hJ) γ hγT
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨Fact.out, hf1, by rw [hK, ← pow_mul, mul_comm]⟩
  have key1 : ∀ k : Kˣ, ∃ k' : Kˣ, ∀ x : K,
      A (((lamUnit J k : Kˣ) : K) * x) = ((lamUnit J k' : Kˣ) : K) * A x := by
    intro k
    obtain ⟨k', hk'⟩ := (mem_torusGroup J hJ).1 (hγT _ (torus_mem_torusGroup J hJ k))
    exact ⟨k', indAdd_lam_mul J hJ hK hfix γ hγR A hA hk'.symm⟩
  have key2 : ∀ k : Kˣ, ∃ k' : Kˣ, ∀ x : K,
      A.symm (((lamUnit J k : Kˣ) : K) * x) = ((lamUnit J k' : Kˣ) : K) * A.symm x := by
    intro k
    obtain ⟨k', hk'⟩ := (mem_torusGroup J hJ).1 (hγT' _ (torus_mem_torusGroup J hJ k))
    exact ⟨k', indAdd_lam_mul J hJ hK hfix γ⁻¹ hγR' A.symm hA' hk'.symm⟩
  have hnorm : (A.toEquiv : Equiv.Perm K) ∈ Subgroup.normalizer
      (((lamUnit J).range.map (MulAction.toPermHom Kˣ K) : Subgroup (Equiv.Perm K)) :
        Set (Equiv.Perm K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      obtain ⟨k', hk'⟩ := key1 k
      refine ⟨lamUnit J k', ⟨k', rfl⟩, ?_⟩
      ext y
      show ((lamUnit J k' : Kˣ) : K) * y = A (((lamUnit J k : Kˣ) : K) * A.symm y)
      rw [hk' (A.symm y), AddEquiv.apply_symm_apply]
    · rintro ⟨_, ⟨k, rfl⟩, hk⟩
      obtain ⟨k', hk'⟩ := key2 k
      refine ⟨lamUnit J k', ⟨k', rfl⟩, ?_⟩
      ext y
      have h1 := congrArg (fun e : Equiv.Perm K => e (A y)) hk
      have h2 : ((lamUnit J k : Kˣ) : K) * A y = A (g (A.symm (A y))) := h1
      rw [AddEquiv.symm_apply_apply] at h2
      have h3 := hk' (A y)
      rw [h2, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply] at h3
      show ((lamUnit J k' : Kˣ) : K) * y = g y
      exact h3.symm
  obtain ⟨c, σ, hcσ⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.unitary_large_torus_additive_normalizer h
      (lt_card_range_lamUnit J hK hfix hq) A hnorm
  refine ⟨c, σ, fun r => by rw [← hA r, hcσ], fun {k k'} hkk' => ?_⟩
  have h1 := indAdd_lam_mul J hJ hK hfix γ hγR A hA hkk' 1
  rw [mul_one, hcσ, hcσ, map_one, mul_one] at h1
  exact mul_left_cancel₀ c.ne_zero (h1.trans (mul_comm _ _))

end Semilinear

section Kernel

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

omit [Fact p.Prime] in
theorem torus_eq_one_of_lamUnit_eq_one (k : Kˣ) (hk : lamUnit J k = 1) : torus J hJ k = 1 := by
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hc0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have h1 : (k : K) * (J.conj (k : K))⁻¹ ^ 2 = 1 := by
    have := congrArg Units.val hk
    rwa [coe_lamUnit, Units.val_one] at this
  have h2 : (k : K) = J.conj (k : K) ^ 2 := by
    field_simp at h1
    exact h1
  have h3 : J.conj (k : K) = (k : K) ^ 2 := by
    have := congrArg J.conj h2
    rwa [map_pow, conj_conj] at this
  have h4 : (k : K) ^ 3 = 1 := by
    have h5 : (k : K) * (k : K) ^ 3 = (k : K) * 1 := by
      rw [h3] at h2
      linear_combination -h2
    exact mul_left_cancel₀ hk0 h5
  have h6 : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 := by
    rw [← mul_inv, h3, ← pow_succ, h4, inv_one]
  have hact : ∀ z : Coord J, hermitianTorusAction J k z = z := by
    intro z
    apply coord_ext
    · rw [torusAction_val]
      dsimp only
      have : (k : K) * (J.conj (k : K))⁻¹ ^ 2 = 1 := h1
      rw [mul_assoc, this, mul_one]
    · rw [torusAction_val]
      dsimp only
      rw [mul_assoc, h6, mul_one]
  have hfix_all : ∀ x : IsoPoint J, torus J hJ k • x = x := by
    intro x
    by_cases hx : x = pinf J hJ
    · rw [hx]
      exact torus_smul_pinf J hJ k
    · obtain ⟨z, rfl⟩ := exists_root_smul_pzero_eq J hJ x hx
      rw [torus_smul_root_smul_pzero, hact]
  have := faithfulSMul_isoPoint J hJ (p ^ f) hK hfix
  exact eq_of_smul_eq_smul (fun x => by rw [hfix_all x, one_smul])

omit [Fact p.Prime] in
theorem torus_eq_of_lamUnit_eq (k k' : Kˣ) (h : lamUnit J k = lamUnit J k') :
    torus J hJ k = torus J hJ k' := by
  have h1 : lamUnit J (k * k'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have h2 := torus_eq_one_of_lamUnit_eq_one J hJ hK hfix _ h1
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

omit [Fact p.Prime] in
theorem eq_one_of_conj_fixes_torus (hq : 2 < p ^ f) {r : ProjectiveSpecialUnitaryMatrixGroup J}
    (hr : r ∈ rootGroup J hJ) (h : ∀ t ∈ torusGroup J hJ, r * t * r⁻¹ = t) : r = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨z, rfl⟩ := (mem_rootGroup J hJ).1 hr
  have h1 := h (torus J hJ g) (torus_mem_torusGroup J hJ g)
  have h2 : torus J hJ g * root J hJ z * (torus J hJ g)⁻¹ = root J hJ z := by
    have h3 : root J hJ z * torus J hJ g = torus J hJ g * root J hJ z := by
      calc root J hJ z * torus J hJ g
          = (root J hJ z * torus J hJ g * (root J hJ z)⁻¹) * root J hJ z := by group
        _ = torus J hJ g * root J hJ z := by rw [h1]
    calc torus J hJ g * root J hJ z * (torus J hJ g)⁻¹
        = (root J hJ z * torus J hJ g) * (torus J hJ g)⁻¹ := by rw [h3]
      _ = root J hJ z := by group
  rw [eq_one_of_generator_comm J hJ hK hfix hq hg h2, map_one]

end Kernel

section Interface

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

omit [Finite K] [Fact p.Prime] hK hfix in
theorem fstAdd_mul_mul_inv (u y : ↥(rootGroup J hJ)) :
    fstAdd J hJ (u * y * u⁻¹) = fstAdd J hJ y := by
  rw [fstAdd_mul, fstAdd_mul, fstAdd_inv]
  ring

theorem exists_semilinear_of_mem (hq : 2 < p ^ f)
    (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hS : IsPGroup p S)
    (hSR : ∀ α ∈ S, ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ) (α : S) :
    ∃ (c : Kˣ) (σ : K ≃+* K),
      (∀ r : ↥(rootGroup J hJ),
        fstAdd J hJ ⟨(α : MulAut _) r, hSR α α.2 r r.2⟩ = (c : K) * σ (fstAdd J hJ r)) ∧
      (σ = 1 → ∃ u ∈ rootGroup J hJ, (α : MulAut _) = MulAut.conj u) := by
  have hα1 : ∀ r ∈ rootGroup J hJ, (α : MulAut _) r ∈ rootGroup J hJ := hSR α α.2
  have hα2 : ∀ r ∈ rootGroup J hJ, (α : MulAut _)⁻¹ r ∈ rootGroup J hJ :=
    hSR _ (S.inv_mem α.2)
  obtain ⟨u, huR, huT⟩ := exists_mem_rootGroup_torus_stable J hJ hK hfix hq α hα1
  set γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.conj u⁻¹ * (α : MulAut _)
    with hγdef
  have hγapp : ∀ g, γ g = u⁻¹ * (α : MulAut _) g * u := by
    intro g
    simp [hγdef]
  have hγR : ∀ r ∈ rootGroup J hJ, γ r ∈ rootGroup J hJ := by
    intro r hr
    rw [hγapp]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ huR) (hα1 r hr)) huR
  have hγR' : ∀ r ∈ rootGroup J hJ, γ⁻¹ r ∈ rootGroup J hJ := by
    intro r hr
    have : γ⁻¹ r = (α : MulAut _)⁻¹ (u * r * u⁻¹) := by
      simp [hγdef, MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hα2 _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ huR hr) (Subgroup.inv_mem _ huR))
  have hγT : ∀ t ∈ torusGroup J hJ, γ t ∈ torusGroup J hJ := by
    intro t ht
    rw [hγapp]
    exact huT t ht
  obtain ⟨c, σ, hrel, hlam⟩ := exists_semilinear J hJ hK hfix hq γ hγR hγR' hγT
  have hrelα : ∀ r : ↥(rootGroup J hJ),
      fstAdd J hJ ⟨(α : MulAut _) r, hα1 r r.2⟩ = (c : K) * σ (fstAdd J hJ r) := by
    intro r
    rw [← hrel r]
    have : (⟨γ r, hγR r r.2⟩ : ↥(rootGroup J hJ)) =
        ⟨u, huR⟩ ⁻¹ * ⟨(α : MulAut _) r, hα1 r r.2⟩ * ⟨u, huR⟩ := by
      apply Subtype.ext
      simp [hγapp]
    rw [this]
    have := fstAdd_mul_mul_inv J hJ (⟨u, huR⟩ ⁻¹) ⟨(α : MulAut _) r, hα1 r r.2⟩
    simpa using this.symm
  refine ⟨c, σ, hrelα, fun hσ1 => ?_⟩
  have hγfix : ∀ t ∈ torusGroup J hJ, γ t = t := by
    intro t ht
    obtain ⟨k, rfl⟩ := (mem_torusGroup J hJ).1 ht
    obtain ⟨k', hk'⟩ := (mem_torusGroup J hJ).1 (hγT _ (torus_mem_torusGroup J hJ k))
    have h1 := hlam hk'.symm
    rw [hσ1] at h1
    have h2 : lamUnit J k = lamUnit J k' := Units.ext h1
    rw [← hk', torus_eq_of_lamUnit_eq J hJ hK hfix k k' h2]
  let InnR : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (rootGroup J hJ).map (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut _)
  have hInnp : IsPGroup p InnR := (isPGroup_rootGroup J hJ hK hfix).map _
  have hSN : S ≤ Subgroup.normalizer
      (InnR : Set (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    have hβ1 : ∀ r ∈ rootGroup J hJ, β r ∈ rootGroup J hJ := hSR β hβ
    have hβ2 : ∀ r ∈ rootGroup J hJ, β⁻¹ r ∈ rootGroup J hJ := hSR _ (S.inv_mem hβ)
    intro h
    constructor
    · rintro ⟨r, hr, rfl⟩
      refine ⟨β r, hβ1 r hr, ?_⟩
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply]
    · rintro ⟨r, hr, hrh⟩
      refine ⟨β⁻¹ r, hβ2 r hr, ?_⟩
      have : h = β⁻¹ * MulAut.conj r * β := by
        rw [hrh]
        group
      rw [this]
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply]
  have hAp : IsPGroup p ↥(InnR ⊔ S) := hInnp.to_sup_of_normal_left' hS hSN
  have hγmem : γ ∈ InnR ⊔ S :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨u⁻¹, Subgroup.inv_mem _ huR, rfl⟩)
      (Subgroup.mem_sup_right α.2)
  obtain ⟨m, hm⟩ := hAp ⟨γ, hγmem⟩
  have hγp : γ ^ p ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨r, hr, hγr⟩ := eq_conj_of_pElement J hJ hK hfix hq γ hγp hγR hγfix
  have hr1 : r = 1 := by
    refine eq_one_of_conj_fixes_torus J hJ hK hfix hq hr fun t ht => ?_
    have := hγfix t ht
    rw [hγr, MulAut.conj_apply] at this
    exact this
  refine ⟨u, huR, ?_⟩
  have : (α : MulAut _) = MulAut.conj u * γ := by
    rw [hγdef, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [this, hγr, hr1, map_one, mul_one]

theorem exists_semilinear_hom (hq : 2 < p ^ f)
    (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J))) (hS : IsPGroup p S)
    (hSR : ∀ α ∈ S, ∀ r ∈ rootGroup J hJ, α r ∈ rootGroup J hJ) :
    ∃ (φ : S →* (K ≃+* K)) (c : S → Kˣ),
      (∀ (α : S) (r : ↥(rootGroup J hJ)),
        fstAdd J hJ ⟨(α : MulAut _) r, hSR α α.2 r r.2⟩ = (c α : K) * φ α (fstAdd J hJ r)) ∧
      ∀ α : S, φ α = 1 → ∃ u ∈ rootGroup J hJ, (α : MulAut _) = MulAut.conj u := by
  choose c σ hrel hker using fun α : S => exists_semilinear_of_mem J hJ hK hfix hq S hS hSR α
  have huniq : ∀ (c₁ c₂ : Kˣ) (σ₁ σ₂ : K ≃+* K),
      (∀ x : K, (c₁ : K) * σ₁ x = c₂ * σ₂ x) → c₁ = c₂ ∧ σ₁ = σ₂ := by
    intro c₁ c₂ σ₁ σ₂ h
    have hc : c₁ = c₂ := Units.ext (by simpa using h 1)
    refine ⟨hc, RingEquiv.ext fun x => ?_⟩
    have := h x
    rw [hc] at this
    exact mul_left_cancel₀ c₂.ne_zero this
  have hsurj := fstAdd_surjective J hJ hK hfix
  have hone : c 1 = 1 ∧ σ 1 = 1 := by
    refine huniq (c 1) 1 (σ 1) 1 fun x => ?_
    obtain ⟨r, rfl⟩ := hsurj x
    have h1 := hrel 1 r
    have h2 : (⟨((1 : S) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) r,
        hSR 1 (1 : S).2 r r.2⟩ : ↥(rootGroup J hJ)) = r := Subtype.ext rfl
    rw [h2] at h1
    simpa using h1.symm
  have hmul : ∀ α β : S, σ (α * β) = σ α * σ β := by
    intro α β
    have hne : (c α : K) * σ α (c β) ≠ 0 :=
      mul_ne_zero (c α).ne_zero ((map_ne_zero _).2 (c β).ne_zero)
    refine (huniq (c (α * β)) (Units.mk0 _ hne) (σ (α * β)) (σ α * σ β) fun x => ?_).2
    obtain ⟨r, rfl⟩ := hsurj x
    have h1 := hrel (α * β) r
    have h2 := hrel α ⟨(β : MulAut _) r, hSR β β.2 r r.2⟩
    have h3 := hrel β r
    have h4 : (⟨((α * β : S) : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) r,
        hSR (α * β) (α * β).2 r r.2⟩ : ↥(rootGroup J hJ)) =
        ⟨(α : MulAut _) ((β : MulAut _) r), hSR α α.2 _ (hSR β β.2 r r.2)⟩ := Subtype.ext rfl
    rw [h4, h2, h3, map_mul] at h1
    simp only [Units.val_mk0]
    rw [← h1]
    show _ = (c α : K) * σ α (c β) * σ α (σ β (fstAdd J hJ r))
    ring
  exact ⟨⟨⟨σ, hone.2⟩, hmul⟩, c, hrel, hker⟩

omit [Fact p.Prime] hK hfix in
theorem card_ker_le_card_comap (S : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)))
    (φ : S →* (K ≃+* K))
    (hker : ∀ α : S, φ α = 1 → ∃ u ∈ rootGroup J hJ, (α : MulAut _) = MulAut.conj u) :
    Nat.card φ.ker ≤ Nat.card (S.comap
      ((MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* MulAut _).comp
        (rootGroup J hJ).subtype)) := by
  let Cj : ↥(rootGroup J hJ) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
    (MulAut.conj : ProjectiveSpecialUnitaryMatrixGroup J →* _).comp (rootGroup J hJ).subtype
  let D : Subgroup ↥(rootGroup J hJ) := S.comap Cj
  let gHom : D →* S := (Cj.comp D.subtype).codRestrict S (fun u => u.2)
  have hle : φ.ker ≤ gHom.range := by
    intro α hα
    obtain ⟨u, hu, hαu⟩ := hker α (MonoidHom.mem_ker.1 hα)
    have huD : (⟨u, hu⟩ : ↥(rootGroup J hJ)) ∈ D := by
      show Cj ⟨u, hu⟩ ∈ S
      have : Cj ⟨u, hu⟩ = (α : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) := hαu.symm
      rw [this]
      exact α.2
    exact ⟨⟨⟨u, hu⟩, huD⟩, Subtype.ext hαu.symm⟩
  exact (Subgroup.card_le_of_le hle).trans
    (Nat.card_le_card_of_surjective _ gHom.rangeRestrict_surjective)

end Interface

section Sylow

open scoped Pointwise

theorem exists_sylow_stable {L : Type*} [Group L] [Finite L] (p : ℕ) [Fact p.Prime]
    (E : Subgroup (MulAut L)) (hEp : IsPGroup p E) :
    ∃ U : Sylow p L, ∀ α ∈ E, ∀ r ∈ (U : Subgroup L), α r ∈ (U : Subgroup L) := by
  let _ : MulDistribMulAction E L := inferInstance
  let _ : MulAction E (Sylow p L) := Sylow.pointwiseMulAction
  have hmod := hEp.card_modEq_card_fixedPoints (Sylow p L)
  have hsyl := card_sylow_modEq_one p L
  have hne : Nonempty (MulAction.fixedPoints E (Sylow p L)) := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : Nat.card (MulAction.fixedPoints E (Sylow p L)) = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    have h1 : 1 ≡ 0 [MOD p] := hsyl.symm.trans hmod
    have h2 : p ∣ 1 := (Nat.modEq_zero_iff_dvd).1 h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨⟨U, hU⟩⟩ := hne
  refine ⟨U, fun α hα r hr => ?_⟩
  have h1 : ((⟨α, hα⟩ : E) • U : Sylow p L) = U := MulAction.mem_fixedPoints.1 hU ⟨α, hα⟩
  have h2 : (⟨α, hα⟩ : E) • r ∈ ((⟨α, hα⟩ : E) • (U : Subgroup L)) :=
    Subgroup.smul_mem_pointwise_smul _ _ _ hr
  have h3 : (((⟨α, hα⟩ : E) • U : Sylow p L) : Subgroup L) = (⟨α, hα⟩ : E) • (U : Subgroup L) :=
    Sylow.pointwise_smul_def
  rw [h1] at h3
  exact h3.symm ▸ h2

end Sylow

section Transport

variable {K : Type} [Field K] [Finite K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) {p f : ℕ} [Fact p.Prime]
  (hK : Nat.card K = (p ^ f) ^ 2) (hfix : Nat.card {x : K // J.conj x = x} = p ^ f)

include hK hfix

theorem exists_equiv_stable_rootGroup {L : Type*} [Group L] [Finite L] (hf : 1 ≤ f)
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) (S : Subgroup (MulAut L))
    (hS : IsPGroup p S) :
    ∃ e' : L ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∀ β ∈ S.map (MulAut.congr e').toMonoidHom, ∀ r ∈ rootGroup J hJ, β r ∈ rootGroup J hJ := by
  obtain ⟨U, hU⟩ := exists_sylow_stable p S hS
  obtain ⟨Sy, hSy⟩ := exists_sylow_eq_rootGroup J hJ hK hfix hf
  obtain ⟨e', he'⟩ := exists_equiv_map_eq e U Sy
  have hUR : (U : Subgroup L).map e'.toMonoidHom = rootGroup J hJ := he'.trans hSy
  refine ⟨e', ?_⟩
  rintro _ ⟨α, hα, rfl⟩ r hr
  have hr' : e'.symm r ∈ (U : Subgroup L) := by
    have : r ∈ (U : Subgroup L).map e'.toMonoidHom := by
      rw [hUR]
      exact hr
    exact Subgroup.mem_map_equiv.1 this
  have h1 := hU α hα _ hr'
  have h2 : e' (α (e'.symm r)) ∈ (U : Subgroup L).map e'.toMonoidHom := ⟨_, h1, rfl⟩
  rw [hUR] at h2
  simpa [MulAut.congr_apply] using h2

end Transport

end CFSG.AGLEmbedding.UnitaryModel

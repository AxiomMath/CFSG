module

public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LieType.CentralExt.QuaternionCover
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

public section

namespace CFSG.LieType.CentralExt

open Matrix

section Transvection

variable {k : Type*} [Field k]

theorem transvection_pow {i j : Fin 2} (hij : i ≠ j) (c : k) (m : ℕ) :
    SpecialLinearGroup.transvection hij c ^ m = SpecialLinearGroup.transvection hij (m • c) := by
  induction m with
  | zero => rw [pow_zero, zero_smul, SpecialLinearGroup.transvection_coeff_zero]
  | succ m ih => rw [pow_succ, ih, ← SpecialLinearGroup.transvection_add, succ_nsmul]

theorem toSpecialLinearGroup_pow_ringChar (t : TransvectionStruct (Fin 2) k) :
    t.toSpecialLinearGroup ^ ringChar k = 1 := by
  rw [TransvectionStruct.toSpecialLinearGroup_def, transvection_pow, nsmul_eq_mul,
    ringChar.Nat.cast_ringChar, zero_mul, SpecialLinearGroup.transvection_coeff_zero]

theorem exists_orderOf_toSpecialLinearGroup [Finite k] (t : TransvectionStruct (Fin 2) k) :
    ∃ n : ℕ, orderOf t.toSpecialLinearGroup = ringChar k ^ n := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  exact exists_orderOf_eq_pow_of_pow_eq_one (n := 1)
    (by rw [pow_one, toSpecialLinearGroup_pow_ringChar])

end Transvection

theorem not_dvd_card_of_isPGroup_two {K : Type*} [Group K] [Finite K] (hK : IsPGroup 2 K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬p ∣ Nat.card K := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hK
  rw [hm]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

section Lift

variable {k : Type*} [Field k] [Finite k] {E G : Type*} [Group E] [Group G] [Finite E]
  {π : E →* G}

theorem lift_unique (hk : ringChar k ≠ 2) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) {β₁ β₂ : SpecialLinearGroup (Fin 2) k →* E}
    (h : π.comp β₁ = π.comp β₂) : β₁ = β₂ := by
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hC : ¬ringChar k ∣ Nat.card π.ker := not_dvd_card_of_isPGroup_two h2 hp.out hk
  apply MonoidHom.eq_of_eqOn_dense
    SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rintro _ ⟨t, rfl⟩
  have ht := exists_orderOf_toSpecialLinearGroup t
  exact eq_of_pElement hcen hC (DFunLike.congr_fun h t.toSpecialLinearGroup)
    (exists_orderOf_map_eq_pow β₁ ht) (exists_orderOf_map_eq_pow β₂ ht)

theorem exists_lift (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) :
    ∃ β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α := by
  classical
  have hp : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  set H := SpecialLinearGroup (Fin 2) k
  let R : Subgroup (H × E) := (α.comp (MonoidHom.fst H E)).eqLocus (π.comp (MonoidHom.snd H E))
  have hR : ∀ z : H × E, z ∈ R ↔ α z.1 = π z.2 := fun _ => Iff.rfl
  let ρ : R →* H := (MonoidHom.fst H E).comp R.subtype
  have hρ : Function.Surjective ρ := by
    intro h
    obtain ⟨e, he⟩ := hπ (α h)
    exact ⟨⟨(h, e), (hR (h, e)).2 he.symm⟩, rfl⟩
  have hρker : ∀ z : R, z ∈ ρ.ker → (z : H × E).2 ∈ π.ker := by
    intro z hz
    have h1 : (z : H × E).1 = 1 := hz
    rw [MonoidHom.mem_ker, ← (hR z).1 z.2, h1, map_one]
  have hρcen : ρ.ker ≤ Subgroup.center R := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have h1 : (z : H × E).1 = 1 := hz
    have h2' := Subgroup.mem_center_iff.1 (hcen (hρker z hz)) (w : H × E).2
    apply Subtype.ext
    exact Prod.ext (by simp [h1]) h2'
  have hρ2 : IsPGroup 2 ρ.ker := by
    intro z
    obtain ⟨n, hn⟩ := h2 ⟨_, hρker z z.2⟩
    have h1 : ((z : R) : H × E).1 = 1 := z.2
    refine ⟨n, Subtype.ext (Subtype.ext (Prod.ext ?_ ?_))⟩
    · simp [h1]
    · exact congrArg Subtype.val hn
  have hρC : ¬ringChar k ∣ Nat.card ρ.ker := not_dvd_card_of_isPGroup_two hρ2 hp.out hk
  let gen : TransvectionStruct (Fin 2) k → R := fun t =>
    pLift (ringChar k) ρ t.toSpecialLinearGroup
  have hgen : ∀ t, ρ (gen t) = t.toSpecialLinearGroup ∧
      ∃ n : ℕ, orderOf (gen t) = ringChar k ^ n :=
    fun t => pLift_spec hρ hρC (exists_orderOf_toSpecialLinearGroup t)
  let R₀ : Subgroup R := Subgroup.closure (Set.range gen)
  let η₀ : R₀ →* H := ρ.comp R₀.subtype
  have hη₀ : Function.Surjective η₀ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff,
      ← SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field,
      Subgroup.closure_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨gen t, Subgroup.subset_closure ⟨t, rfl⟩⟩, (hgen t).1⟩
  have hη₀cen : η₀.ker ≤ Subgroup.center R₀ := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hρcen hz) w)
  have hη₀2 : IsPGroup 2 η₀.ker := by
    intro z
    obtain ⟨n, hn⟩ := hρ2 ⟨_, z.2⟩
    have hn' : ((z : R₀) : R) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using hn'))⟩
  have hodd : Subgroup.closure {x : R₀ | Odd (orderOf x)} = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := Set.range gen)]
    apply Subgroup.closure_mono
    rintro x ⟨t, ht⟩
    obtain ⟨n, hn⟩ := (hgen t).2
    show Odd (orderOf x)
    rw [← Subgroup.orderOf_coe, ← ht, hn]
    exact (hp.out.odd_of_ne_two hk).pow
  have hker : η₀.ker = ⊥ :=
    ker_eq_bot_of_mulEquiv_specialLinearGroup hk hodd η₀ hη₀ hη₀cen hη₀2 (MulEquiv.refl _)
  have hbij : Function.Bijective η₀ := ⟨(MonoidHom.ker_eq_bot_iff η₀).1 hker, hη₀⟩
  let σ : H ≃* R₀ := (MulEquiv.ofBijective η₀ hbij).symm
  refine ⟨(MonoidHom.snd H E).comp (R.subtype.comp (R₀.subtype.comp σ.toMonoidHom)), ?_⟩
  ext h
  have h1 : (((σ h : R₀) : R) : H × E).1 = h := MulEquiv.ofBijective_apply_symm_apply η₀ hbij
  have h2' := (hR _).1 ((σ h : R₀) : R).2
  rw [h1] at h2'
  exact h2'.symm

open _root_.Classical in
noncomputable def sl2Lift (π : E →* G) (α : SpecialLinearGroup (Fin 2) k →* G) :
    SpecialLinearGroup (Fin 2) k →* E :=
  if h : ∃ β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α then h.choose else 1

omit [Finite k] [Finite E] in
theorem comp_sl2Lift_of_exists {α : SpecialLinearGroup (Fin 2) k →* G}
    (h : ∃ β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α) : π.comp (sl2Lift π α) = α := by
  classical
  rw [sl2Lift, dite_eq_left h]
  exact h.choose_spec

theorem comp_sl2Lift (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) : π.comp (sl2Lift π α) = α :=
  comp_sl2Lift_of_exists (exists_lift hk hπ hcen h2 α)

theorem map_sl2Lift (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) (h : SpecialLinearGroup (Fin 2) k) :
    π (sl2Lift π α h) = α h :=
  DFunLike.congr_fun (comp_sl2Lift hk hπ hcen h2 α) h

theorem eq_sl2Lift (hk : ringChar k ≠ 2) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) {α : SpecialLinearGroup (Fin 2) k →* G}
    {β : SpecialLinearGroup (Fin 2) k →* E} (hβ : π.comp β = α) : β = sl2Lift π α :=
  lift_unique hk hcen h2 (hβ.trans (comp_sl2Lift_of_exists ⟨β, hβ⟩).symm)

theorem existsUnique_lift (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) :
    ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α :=
  ⟨sl2Lift π α, comp_sl2Lift hk hπ hcen h2 α, fun _ hβ => eq_sl2Lift hk hcen h2 hβ⟩

theorem sl2Lift_injective (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    {α : SpecialLinearGroup (Fin 2) k →* G} (hα : Function.Injective α) :
    Function.Injective (sl2Lift π α) := by
  intro h₁ h₂ h
  apply hα
  rw [← map_sl2Lift hk hπ hcen h2 α, ← map_sl2Lift hk hπ hcen h2 α, h]

theorem sl2Lift_conj (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) (e : E) :
    (MulAut.conj e).toMonoidHom.comp (sl2Lift π α) =
      sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α) := by
  apply eq_sl2Lift hk hcen h2
  ext h
  simp [map_sl2Lift hk hπ hcen h2 α h]

theorem conj_sl2Lift_apply (hk : ringChar k ≠ 2) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) (e : E) (h : SpecialLinearGroup (Fin 2) k) :
    e * sl2Lift π α h * e⁻¹ = sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α) h :=
  DFunLike.congr_fun (sl2Lift_conj hk hπ hcen h2 α e) h

variable {k' : Type*} [Field k'] [Finite k']

theorem sl2Lift_comp (hk : ringChar k ≠ 2) (hk' : ringChar k' ≠ 2)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G)
    (β : SpecialLinearGroup (Fin 2) k' →* SpecialLinearGroup (Fin 2) k) :
    (sl2Lift π α).comp β = sl2Lift π (α.comp β) := by
  apply eq_sl2Lift hk' hcen h2
  rw [← MonoidHom.comp_assoc, comp_sl2Lift hk hπ hcen h2 α]

theorem commute_sl2Lift (hk : ringChar k ≠ 2) (hk' : ringChar k' ≠ 2)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker)
    (α : SpecialLinearGroup (Fin 2) k →* G) (α' : SpecialLinearGroup (Fin 2) k' →* G)
    (hαα' : ∀ h h', Commute (α h) (α' h')) (h : SpecialLinearGroup (Fin 2) k)
    (h' : SpecialLinearGroup (Fin 2) k') : Commute (sl2Lift π α h) (sl2Lift π α' h') := by
  have hconj : (MulAut.conj (π (sl2Lift π α h))).toMonoidHom.comp α' = α' := by
    ext g
    simp [map_sl2Lift hk hπ hcen h2 α h, (hαα' h g).eq]
  have h3 := conj_sl2Lift_apply hk' hπ hcen h2 α' (sl2Lift π α h) h'
  rw [hconj] at h3
  exact (mul_inv_eq_iff_eq_mul.1 h3)

theorem odd_special_linear_two_lifting (hk : ringChar k ≠ 2) (hk' : ringChar k' ≠ 2)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    (∀ α : SpecialLinearGroup (Fin 2) k →* G,
      ∃! β : SpecialLinearGroup (Fin 2) k →* E, π.comp β = α) ∧
    (∀ α : SpecialLinearGroup (Fin 2) k →* G, Function.Injective α →
      Function.Injective (sl2Lift π α)) ∧
    (∀ (α : SpecialLinearGroup (Fin 2) k →* G) (α' : SpecialLinearGroup (Fin 2) k' →* G),
      (∀ h h', Commute (α h) (α' h')) →
        ∀ h h', Commute (sl2Lift π α h) (sl2Lift π α' h')) ∧
    (∀ (α : SpecialLinearGroup (Fin 2) k →* G) (e : E),
      (MulAut.conj e).toMonoidHom.comp (sl2Lift π α) =
        sl2Lift π ((MulAut.conj (π e)).toMonoidHom.comp α)) ∧
    (∀ (α : SpecialLinearGroup (Fin 2) k →* G)
      (β : SpecialLinearGroup (Fin 2) k' →* SpecialLinearGroup (Fin 2) k),
      (sl2Lift π α).comp β = sl2Lift π (α.comp β)) :=
  ⟨existsUnique_lift hk hπ hcen h2, fun _ hα => sl2Lift_injective hk hπ hcen h2 hα,
    fun α α' hαα' => commute_sl2Lift hk hk' hπ hcen h2 α α' hαα',
    sl2Lift_conj hk hπ hcen h2, sl2Lift_comp hk hk' hπ hcen h2⟩

end Lift

end CFSG.LieType.CentralExt

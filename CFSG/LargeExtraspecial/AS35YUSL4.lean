module

public import CFSG.LargeExtraspecial.A2ModCfgSL

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35YU

open Module Matrix QuadraticMap CFSG.RankThree.OrthogonalInvolutions A2Mod

section Collinear

variable {X : Type} [Group X] {D : Set X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V} {ρ : X →* (V ≃ₗ[ZMod 2] V)}

theorem polar_eq_zero_of_collinear (hA : A2Action D Q ρ) {d e : X} (hd : d ∈ D) (he : e ∈ D)
    (hde : d * e ∈ D) {x y : V} (hx : x ∈ commSpace (ρ d)) (hy : y ∈ commSpace (ρ e)) :
    polar Q x y = 0 := by
  have hxy : x + y ∈ commSpace (ρ d) ⊔ commSpace (ρ e) := Submodule.add_mem_sup hx hy
  have h0 : Q (x + y) = 0 := by
    rcases hA.mem_or_mem_or_mem hd he hde hxy with h | h | h
    · exact (hA.isTypeA hd).2.2.2.2 _ h
    · exact (hA.isTypeA he).2.2.2.2 _ h
    · exact (hA.isTypeA hde).2.2.2.2 _ h
  have hx0 := (hA.isTypeA hd).2.2.2.2 _ hx
  have hy0 := (hA.isTypeA he).2.2.2.2 _ hy
  rw [QuadraticMap.polar, h0, hx0, hy0]
  rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_eq_of_polar_commSpace (hQ : Q.polarBilin.Nondegenerate)
    {g : V ≃ₗ[ZMod 2] V} (hg : ∀ v, Q (g v) = Q v) {x : V}
    (hx : ∀ y ∈ commSpace g, polar Q x y = 0) : g x = x := by
  have hpol : ∀ a b, polar Q (g a) (g b) = polar Q a b := fun a b => by
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hg, hg, hg]
  have hrad : g.symm x - x = 0 := by
    refine hQ.1 _ fun u => ?_
    rw [polarBilin_apply_apply, polar_sub_left]
    have h1 := hx _ (mem_commSpace.mpr ⟨u, rfl⟩)
    rw [polar_sub_right, sub_eq_zero] at h1
    rw [← hpol (g.symm x) u, LinearEquiv.apply_symm_apply, h1, sub_self]
  have h2 : g.symm x = x := sub_eq_zero.mp hrad
  calc g x = g (g.symm x) := by rw [h2]
    _ = x := LinearEquiv.apply_symm_apply g x

end Collinear

section SL4

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {ρ : SpecialLinearGroup (Fin 4) (ZMod 2) →* (V ≃ₗ[ZMod 2] V)}

omit [FiniteDimensional (ZMod 2) V] in
theorem polar_self_YU (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul]
  exact CharTwo.add_self_eq_zero _

omit [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] in
theorem add_ne_zero_of_ne_YU {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {x y : W}
    (h : x ≠ y) : x + y ≠ 0 := fun h0 => h (by
  have := congrArg (· + y) h0
  simpa [add_assoc, ZModModule.add_self] using this)

theorem false_of_pointCentreMap_YU (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ)
    {c : (Fin 4 → ZMod 2) → V} (hc : IsPointCentreMap ρ c)
    (hB : finrank (ZMod 2) (commSpaceOf ρ (hyperplaneGroup (Pi.single 0 1))) ≤ 3) : False := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set φ : Fin 4 → ZMod 2 := Pi.single 0 1 with hφ
  have hφ0 : φ ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hinj := hc.injective hA (by norm_num)
  have hperp : ∀ v₁ v₂, polar Q (c v₁) (c v₂) = 0 := by
    intro v₁ v₂
    by_cases h1 : v₁ = 0
    · rw [h1, hc.1, polar_zero_left]
    by_cases h2 : v₂ = 0
    · rw [h2, hc.1, polar_zero_right]
    by_cases h12 : v₁ = v₂
    · rw [h12]
      exact polar_self_YU _
    obtain ⟨ψ, hψ, hψ1, hψ2⟩ := exists_ne_zero_dotProduct_eq_zero_two (by norm_num) v₁ v₂
    have m12 : tv v₁ ψ * tv v₂ ψ ∈ transvectionSet 4 (ZMod 2) := by
      rw [tv_mul_tv_right hψ1 hψ2]
      exact tv_mem_transvectionSet (add_ne_zero_of_ne_YU h12) hψ
        (by rw [dotProduct_add, hψ1, hψ2, add_zero])
    exact polar_eq_zero_of_collinear hA (tv_mem_transvectionSet h1 hψ hψ1)
      (tv_mem_transvectionSet h2 hψ hψ2) m12 ((hc.2 v₁ h1).2 ψ hψ hψ1) ((hc.2 v₂ h2).2 ψ hψ hψ2)
  have hmem : ∀ w : Fin 4 → ZMod 2, φ ⬝ᵥ w = 0 → c w ∈ commSpaceOf ρ (hyperplaneGroup φ) := by
    intro w hw
    by_cases hw0 : w = 0
    · rw [hw0, hc.1]
      exact Submodule.zero_mem _
    · exact commSpace_le_commSpaceOf ρ (tv_mem_hyperplaneGroup w φ) ((hc.2 w hw0).2 φ hφ0 hw)
  let f : {w : Fin 4 → ZMod 2 // φ ⬝ᵥ w = 0} → commSpaceOf ρ (hyperplaneGroup φ) :=
    fun w => ⟨c w, hmem w w.2⟩
  have hf : Function.Injective f := fun w w' h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hK : Nat.card {w : Fin 4 → ZMod 2 // φ ⬝ᵥ w = 0} = 8 := by
    rw [Nat.card_eq_fintype_card, hφ]
    decide
  have hcardB : Nat.card (commSpaceOf ρ (hyperplaneGroup φ)) ≤ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 2 ^ finrank (ZMod 2) (commSpaceOf ρ (hyperplaneGroup φ)) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) hB
      _ = 8 := by norm_num
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, le_antisymm (Nat.card_le_card_of_injective f hf) (by omega)⟩
  have hsurj : ∀ y ∈ commSpaceOf ρ (hyperplaneGroup φ), ∃ w, c w = y := fun y hy => by
    obtain ⟨⟨w, _⟩, h⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨w, congrArg Subtype.val h⟩
  set v : Fin 4 → ZMod 2 := Pi.single 0 1 with hv
  set w : Fin 4 → ZMod 2 := Pi.single 1 1 with hw
  have hφv : φ ⬝ᵥ v = 1 := by
    rw [hφ, hv]
    decide
  have hφw : φ ⬝ᵥ w = 0 := by
    rw [hφ, hw]
    decide
  have hw0 : w ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hfix : ρ (tv w φ) (c v) = c v := by
    refine apply_eq_of_polar_commSpace hA.nondegenerate (hA.map_apply _) fun y hy => ?_
    obtain ⟨w', rfl⟩ := hsurj y (commSpace_le_commSpaceOf ρ (tv_mem_hyperplaneGroup w φ) hy)
    exact hperp v w'
  rw [← hc.map_mulVec hA (by norm_num), tv_mulVec hφw, hφv, one_smul] at hfix
  have h := hinj hfix
  exact hw0 (by simpa using h)

theorem false_of_hyperplaneCentreMap_YU (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ)
    {d : (Fin 4 → ZMod 2) → V} (hd : IsHyperplaneCentreMap ρ d)
    (hA3 : finrank (ZMod 2) (commSpaceOf ρ (pointGroup (Pi.single 0 1))) ≤ 3) : False := by
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set v : Fin 4 → ZMod 2 := Pi.single 0 1 with hv
  have hv0 : v ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hinj := hd.injective hA (by norm_num)
  have hperp : ∀ ψ₁ ψ₂, polar Q (d ψ₁) (d ψ₂) = 0 := by
    intro ψ₁ ψ₂
    by_cases h1 : ψ₁ = 0
    · rw [h1, hd.1, polar_zero_left]
    by_cases h2 : ψ₂ = 0
    · rw [h2, hd.1, polar_zero_right]
    by_cases h12 : ψ₁ = ψ₂
    · rw [h12]
      exact polar_self_YU _
    obtain ⟨w, hw, hw1, hw2⟩ := exists_ne_zero_dotProduct_eq_zero_two (by norm_num) ψ₁ ψ₂
    rw [dotProduct_comm] at hw1 hw2
    have m12 : tv w ψ₁ * tv w ψ₂ ∈ transvectionSet 4 (ZMod 2) := by
      rw [tv_mul_tv_left hw1 hw2]
      exact tv_mem_transvectionSet hw (add_ne_zero_of_ne_YU h12)
        (by rw [add_dotProduct, hw1, hw2, add_zero])
    exact polar_eq_zero_of_collinear hA (tv_mem_transvectionSet hw h1 hw1)
      (tv_mem_transvectionSet hw h2 hw2) m12 ((hd.2 ψ₁ h1).2 w hw hw1) ((hd.2 ψ₂ h2).2 w hw hw2)
  have hmem : ∀ ψ : Fin 4 → ZMod 2, ψ ⬝ᵥ v = 0 → d ψ ∈ commSpaceOf ρ (pointGroup v) := by
    intro ψ hψ
    by_cases hψ0 : ψ = 0
    · rw [hψ0, hd.1]
      exact Submodule.zero_mem _
    · exact commSpace_le_commSpaceOf ρ (tv_mem_pointGroup v ψ) ((hd.2 ψ hψ0).2 v hv0 hψ)
  let f : {ψ : Fin 4 → ZMod 2 // ψ ⬝ᵥ v = 0} → commSpaceOf ρ (pointGroup v) :=
    fun ψ => ⟨d ψ, hmem ψ ψ.2⟩
  have hf : Function.Injective f := fun ψ ψ' h => Subtype.ext (hinj (congrArg Subtype.val h))
  have hK : Nat.card {ψ : Fin 4 → ZMod 2 // ψ ⬝ᵥ v = 0} = 8 := by
    rw [Nat.card_eq_fintype_card, hv]
    decide
  have hcardA : Nat.card (commSpaceOf ρ (pointGroup v)) ≤ 8 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    calc 2 ^ finrank (ZMod 2) (commSpaceOf ρ (pointGroup v)) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) hA3
      _ = 8 := by norm_num
  have hbij := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hf, le_antisymm (Nat.card_le_card_of_injective f hf) (by omega)⟩
  have hsurj : ∀ y ∈ commSpaceOf ρ (pointGroup v), ∃ ψ, d ψ = y := fun y hy => by
    obtain ⟨⟨ψ, _⟩, h⟩ := hbij.2 ⟨y, hy⟩
    exact ⟨ψ, congrArg Subtype.val h⟩
  set ψ'' : Fin 4 → ZMod 2 := Pi.single 0 1 with hψ''
  set ψ₀ : Fin 4 → ZMod 2 := Pi.single 1 1 with hψ₀
  have hψ''v : ψ'' ⬝ᵥ v = 1 := by
    rw [hψ'', hv]
    decide
  have hψ₀v : ψ₀ ⬝ᵥ v = 0 := by
    rw [hψ₀, hv]
    decide
  have hψ₀0 : ψ₀ ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have hfix : ρ (tv v ψ₀) (d ψ'') = d ψ'' := by
    refine apply_eq_of_polar_commSpace hA.nondegenerate (hA.map_apply _) fun y hy => ?_
    obtain ⟨ψ', rfl⟩ := hsurj y (commSpace_le_commSpaceOf ρ (tv_mem_pointGroup v ψ₀) hy)
    exact hperp ψ'' ψ'
  rw [← hd.map_contra hA (by norm_num), contra_tv hψ₀v, hψ''v, one_smul] at hfix
  have h := hinj hfix
  exact hψ₀0 (by simpa using h)

theorem exists_isPointMaps_or_finrank_le_six (hA : A2Action (transvectionSet 4 (ZMod 2)) Q ρ) :
    (∃ P Pd, IsPointMaps ρ Q P Pd) ∨ finrank (ZMod 2) (commSpaceOf ρ ⊤) ≤ 6 := by
  have he : (Pi.single 0 1 : Fin 4 → ZMod 2) ≠ 0 := Pi.single_ne_zero_iff.mpr one_ne_zero
  have h3 := finrank_commSpaceOf_top_le_add (ρ := ρ) (0 : Fin 4)
  rcases hA.common_point_or_finrank_le_three (A := pointGroup (Pi.single 0 1))
      forall_mem_pointGroup_mem_transvectionSet with hcA | hA3
  · obtain ⟨p, hp⟩ := id hcA
    obtain ⟨c, hc⟩ := exists_isPointCentreMap fun v hv =>
      exists_isPointCentre_of_isPointCentre he ((isPointCentre_iff he).mpr hp) hv
    rcases hA.common_point_or_finrank_le_three (A := hyperplaneGroup (Pi.single 0 1))
        forall_mem_hyperplaneGroup_mem_transvectionSet with hcB | hB3
    · obtain ⟨P, Pd, h1, h2, h3', h4, h5, h6, h7, h8, h9⟩ :=
        exists_pointMaps_of_concurrent hA (le_refl 4) he he hcA hcB
      exact .inl ⟨P, Pd, h1, h2, h3', h4, h5, h6, h7, h8, h9⟩
    · exact (false_of_pointCentreMap_YU hA hc hB3).elim
  · rcases hA.common_point_or_finrank_le_three (A := hyperplaneGroup (Pi.single 0 1))
        forall_mem_hyperplaneGroup_mem_transvectionSet with hcB | hB3
    · obtain ⟨p, hp⟩ := hcB
      obtain ⟨d, hd⟩ := exists_isHyperplaneCentreMap fun φ hφ =>
        exists_isHyperplaneCentre_of_isHyperplaneCentre he ((isHyperplaneCentre_iff he).mpr hp)
          hφ
      exact (false_of_hyperplaneCentreMap_YU hA hd hA3).elim
    · exact .inr (by omega)

end SL4

end CFSG.LargeExtraspecial.AS35YU

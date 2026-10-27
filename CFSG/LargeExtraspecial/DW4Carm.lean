module

public import CFSG.LargeExtraspecial.DW4Burn
public import CFSG.LargeExtraspecial.DW4Inv
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW.W4

open Subgroup Module Matrix CFSG.GH74.Exceptional CFSG.ComponentClassification.PresentationLocal

abbrev V₄ : Type := Fin 4 → ZMod 2

@[expose] noncomputable def glToLin : GL (Fin 4) (ZMod 2) ≃* (V₄ ≃ₗ[ZMod 2] V₄) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _)

theorem glToLin_apply (P : GL (Fin 4) (ZMod 2)) (v : V₄) :
    glToLin P v = (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v := rfl

instance finite_glV₄ : Finite (V₄ ≃ₗ[ZMod 2] V₄) :=
  Finite.of_injective (fun f : V₄ ≃ₗ[ZMod 2] V₄ => (f : V₄ → V₄))
    fun _ _ h => LinearEquiv.ext (congrFun h)

theorem card_glV₄ : Nat.card (V₄ ≃ₗ[ZMod 2] V₄) = 20160 := by
  rw [← Nat.card_congr glToLin.toEquiv, card_GL_four_two]

@[expose] noncomputable def carmY (k : CarmichaelIndex 8) : V₄ ≃ₗ[ZMod 2] V₄ :=
  glToLin (l42Gen k)

theorem carmY_pow_three (k : CarmichaelIndex 8) : carmY k ^ 3 = 1 := by
  rw [carmY, ← map_pow, l42Gen_pow_three, map_one]

theorem card_fix_l42Mat_mul : ∀ i j : Fin 6, i ≠ j →
    Fintype.card {v : V₄ // (l42Mat i * l42Mat j) *ᵥ v = v} = 4 := by
  decide

theorem isRank2Inv_carmY_mul {k l : CarmichaelIndex 8} (hkl : k ≠ l) :
    IsRank2Inv (carmY k * carmY l) := by
  refine ⟨?_, ?_⟩
  · rw [carmY, carmY, ← map_mul, ← map_mul, ← pow_two, l42Gen_mul_sq k l hkl, map_one]
  · have hmem : ∀ v : V₄, v ∈ fixSpace (carmY k * carmY l) ↔
        (l42Mat (carmichaelIndexToFin6 k) * l42Mat (carmichaelIndexToFin6 l)) *ᵥ v = v := by
      intro v
      rw [mem_fixSpace, carmY, carmY, ← map_mul, glToLin_apply]
      rfl
    have hcard : Nat.card (fixSpace (carmY k * carmY l)) = 2 ^ 2 := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight hmem), Nat.card_eq_fintype_card,
        card_fix_l42Mat_mul _ _ (carmichaelIndexToFin6_injective.ne hkl)]
      norm_num
    rw [card_fixSpace] at hcard
    exact Nat.pow_right_injective le_rfl hcard

@[expose] def k₀ : CarmichaelIndex 8 := ⟨2, by decide⟩

theorem carmY_k₀_ne_one : carmY k₀ ≠ 1 := by
  intro h
  have h1 : l42Gen k₀ = 1 := glToLin.injective (h.trans (map_one glToLin).symm)
  have : l42Mat 0 = 1 := by
    have := congrArg Units.val h1
    simpa [l42Gen, l42Unit, carmichaelIndexToFin6, k₀] using this
  exact absurd this (by decide)

theorem exists_hom_bijective {J : Type*} [Group J] (η : J →* (V₄ ≃ₗ[ZMod 2] V₄))
    (hη : Function.Surjective η) {z : J} (hηz : η z = 1)
    (hker : ∀ j, η j = 1 → j = 1 ∨ j = z) (hzc : ∀ j, z * j = j * z) (hz2 : z * z = 1)
    (hinv : ∀ j, IsRank2Inv (η j) → j * j = 1) :
    ∃ φ : alternatingGroup (Fin 8) →* J, Function.Bijective (η.comp φ) := by
  have hlift : ∀ k : CarmichaelIndex 8, ∃ x : J, η x = carmY k ∧ x ^ 3 = 1 := by
    intro k
    obtain ⟨y, hy⟩ := hη (carmY k)
    have h3 : η (y ^ 3) = 1 := by rw [map_pow, hy, carmY_pow_three]
    rcases hker _ h3 with h | h
    · exact ⟨y, hy, h⟩
    · refine ⟨y * z, by rw [map_mul, hy, hηz, mul_one], ?_⟩
      have hc : Commute y z := (hzc y).symm
      rw [hc.mul_pow, h]
      simp [pow_three, hz2]
  choose x hxη hx3 using hlift
  have hxx : ∀ k l, k ≠ l → (x k * x l) ^ 2 = 1 := by
    intro k l hkl
    rw [pow_two]
    exact hinv _ (by rw [map_mul, hxη, hxη]; exact isRank2Inv_carmY_mul hkl)
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle (n := 8) (by norm_num) x hx3 hxx
  refine ⟨φ, ?_⟩
  have hinj : Function.Injective (η.comp φ) := by
    have : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (MonoidHom.normal_ker (η.comp φ)).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff _).mp h
    · exfalso
      have hk : carmichaelCycle k₀ ∈ (η.comp φ).ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hφ, hxη] at hk
      exact carmY_k₀_ne_one hk
  have hcard : Nat.card (alternatingGroup (Fin 8)) = Nat.card (V₄ ≃ₗ[ZMod 2] V₄) := by
    rw [card_glV₄, nat_card_alternatingGroup, Nat.card_fin]
    decide
  exact hinj.bijective_of_nat_card_le hcard.ge

namespace Hyp

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {W₁ W₂ : Submodule (ZMod 2) T.Qt}
  (H : Hyp T W₁ W₂)
include H

theorem exists_levi (hsurj : Function.Surjective H.res)
    (hx : ∃ x : T.M, x * x = 1 ∧ IsRank2Inv (H.res x)) {U₀ U₀' : Subgroup X}
    (hU₀ : IsZCompl U₀ (T.clPre W₁) T.z) (hU₀' : IsZCompl U₀' (T.clPre W₂) T.z) :
    ∃ L : Subgroup X, ∃ hLM : L ≤ T.M, L ≤ normalizer (U₀' : Set X) ∧
      (∀ l ∈ L, l ∈ T.QG → l = 1) ∧
      (∀ m : T.M, ∃ l : L, H.res ⟨l, hLM l.2⟩ = H.res m) ∧ Nat.card L = 20160 := by
  set L₂ : Subgroup X := normalizer (U₀ : Set X) ⊓ normalizer (U₀' : Set X) ⊓ T.M with hL₂
  have hL₂M : L₂ ≤ T.M := inf_le_right
  let φ := (Module.finBasisOfFinrankEq (ZMod 2) W₁ H.finrank₁).equivFun
  let η : L₂ →* (V₄ ≃ₗ[ZMod 2] V₄) :=
    (congrGL φ).toMonoidHom.comp (H.res.comp (Subgroup.inclusion hL₂M))
  have hη : ∀ j : L₂, η j = congrGL φ (H.res ⟨j, hL₂M j.2⟩) := fun _ => rfl
  have hzL₂ : T.z ∈ L₂ := by
    have hzn : ∀ U : Subgroup X, U ≤ T.QG → T.z ∈ normalizer (U : Set X) := fun U hU =>
      mem_normalizer_of_conj_mem fun u hu => by
        rw [← T.z_comm_QG (hU hu), mul_inv_cancel_right]
        exact hu
    exact ⟨⟨hzn U₀ fun _ h => hU₀.mem_QG h, hzn U₀' fun _ h => hU₀'.mem_QG h⟩, T.z_mem_M⟩
  have hres1 : ∀ {m : T.M}, (m : X) ∈ T.QG → H.res m = 1 := fun h => H.res_eq_one_of_mem_QG h
  have hsurjη : Function.Surjective η := by
    intro g
    obtain ⟨m, hm⟩ := hsurj ((congrGL φ).symm g)
    obtain ⟨ν, hν, hν₁, hν₂⟩ := H.exists_mul_mem_normalizer hU₀ hU₀' m.2
    refine ⟨⟨ν * m, ⟨hν₁, hν₂⟩, T.M.mul_mem (T.QG_le_M hν) m.2⟩, ?_⟩
    rw [hη]
    have e : (⟨ν * m, hL₂M ⟨⟨hν₁, hν₂⟩, T.M.mul_mem (T.QG_le_M hν) m.2⟩⟩ : T.M) =
        ⟨ν, T.QG_le_M hν⟩ * m := rfl
    rw [e, map_mul, hres1 hν, one_mul, hm, MulEquiv.apply_symm_apply]
  have hker : ∀ j : L₂, η j = 1 → j = 1 ∨ j = ⟨T.z, hzL₂⟩ := by
    intro j hj
    rw [hη, (congrGL φ).map_eq_one_iff] at hj
    have hjQ := H.mem_QG_of_res_eq_one hj
    rcases H.eq_one_or_z_of_mem_normalizer hU₀ hU₀' hjQ j.2.1.1 j.2.1.2 with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hinv : ∀ j : L₂, IsRank2Inv (η j) → j * j = 1 := by
    intro j hj
    rw [hη, isRank2Inv_congrGL_iff] at hj
    obtain ⟨x₀, hx₀, hx₀r⟩ := hx
    obtain ⟨g, hg⟩ := hx₀r.exists_conj_eq H.finrank₁ hj
    obtain ⟨m, rfl⟩ := hsurj g
    set x : T.M := m * x₀ * m⁻¹
    have hxx : (x : X) * x = 1 := by
      have : x * x = 1 := by
        change m * x₀ * m⁻¹ * (m * x₀ * m⁻¹) = 1
        rw [show m * x₀ * m⁻¹ * (m * x₀ * m⁻¹) = m * (x₀ * x₀) * m⁻¹ by group, hx₀, mul_one,
          mul_inv_cancel]
      exact congrArg Subtype.val this
    have hxj : (x : X) * (j : X)⁻¹ ∈ T.QG := by
      have h1 : H.res (x * (⟨j, hL₂M j.2⟩ : T.M)⁻¹) = 1 := by
        rw [map_mul, map_inv, show H.res x = H.res m * H.res x₀ * (H.res m)⁻¹ by
          simp [x, map_mul, map_inv], hg, mul_inv_cancel]
      exact H.mem_QG_of_res_eq_one h1
    have h := H.mul_self_eq_one_of_lift hU₀ hU₀' (hL₂M j.2) j.2.1.1 j.2.1.2 hxx hxj
      fun a ha hfa => by
        obtain ⟨v, hv⟩ := hj.exists_sub_eq H.finrank₁ (w := ⟨a, ha⟩) (Subtype.ext hfa)
        exact ⟨v, v.2, congrArg Subtype.val hv⟩
    exact Subtype.ext h
  obtain ⟨φA, hφA⟩ := exists_hom_bijective η hsurjη (z := ⟨T.z, hzL₂⟩)
    (by rw [hη, hres1 T.z_mem_QG, map_one]) hker
    (fun j => Subtype.ext (T.z_comm (hL₂M j.2)).symm) (Subtype.ext T.z_mul_z) hinv
  have hinjA : Function.Injective φA := fun a b hab => hφA.1 (by
    change η (φA a) = η (φA b)
    rw [hab])
  set L : Subgroup X := (L₂.subtype.comp φA).range with hL
  have hLL₂ : L ≤ L₂ := by
    rintro _ ⟨a, rfl⟩
    exact (φA a).2
  refine ⟨L, hLL₂.trans hL₂M, hLL₂.trans (inf_le_left.trans inf_le_right), ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ hQ
    have h1 : (η.comp φA) a = (η.comp φA) 1 := by
      rw [map_one, MonoidHom.comp_apply, hη, hres1 hQ, map_one]
    rw [hφA.1 h1, map_one]
  · intro m
    obtain ⟨a, ha⟩ := hφA.2 (congrGL φ (H.res m))
    refine ⟨⟨(φA a : X), a, rfl⟩, ?_⟩
    rw [MonoidHom.comp_apply, hη] at ha
    exact (congrGL φ).injective ha
  · have hinj : Function.Injective (L₂.subtype.comp φA) :=
      Subtype.val_injective.comp hinjA
    rw [hL, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, nat_card_alternatingGroup,
      Nat.card_fin]
    decide

end Hyp

end CFSG.LargeExtraspecial.DW.W4

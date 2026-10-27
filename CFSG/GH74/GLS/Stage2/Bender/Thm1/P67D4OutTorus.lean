module

public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Cartan

variable {K : Type} [Field K]

theorem cartanChar_mul' {τ : Tag} (c c' : Fin τ.rank → Kˣ) :
    cartanChar (c * c') = cartanChar c * cartanChar c' := by
  funext l
  simp only [cartanChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem cartanChar_mulSingle {τ : Tag} (i : Fin τ.rank) (s : Kˣ) :
    cartanChar (Pi.mulSingle i s : Fin τ.rank → Kˣ) = fun l => s ^ τ.cartan i l := by
  funext l
  simp only [cartanChar]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.mulSingle_eq_of_ne hj]
  · simp

@[expose] def cartanCharHom (τ : Tag) (K : Type) [Field K] :
    (Fin τ.rank → Kˣ) →* (Fin τ.rank → Kˣ) where
  toFun := cartanChar
  map_one' := by
    funext l
    simp [cartanChar]
  map_mul' := cartanChar_mul'

theorem sq_eq_one_of_cartanChar_D4 (ε : Fin Tag.D4.rank → Kˣ)
    (h : cartanChar ε = 1) (j : Fin Tag.D4.rank) : ε j ^ 2 = 1 := by
  suffices H : ∀ e : Fin 4 → Kˣ, (∀ l : Fin 4, ∏ i : Fin 4,
      e i ^ ((!![2, 0, -1, 0; 0, 2, -1, 0; -1, -1, 2, -1; 0, 0, -1, 2] :
        Matrix (Fin 4) (Fin 4) ℤ) i l) = 1) → ∀ j : Fin 4, e j ^ 2 = 1 from
    H ε (fun l => congrFun h l) j
  intro ε key j
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  simp [Fin.prod_univ_four] at h0 h1 h2 h3
  have hc : (ε 0 : K) ^ 2 = ε 2 := by simpa using congrArg Units.val (mul_inv_eq_one.1 h0)
  have hb : (ε 1 : K) ^ 2 = ε 2 := by simpa using congrArg Units.val (mul_inv_eq_one.1 h1)
  have hd : (ε 3 : K) ^ 2 = ε 2 := by
    simpa using congrArg Units.val (inv_mul_eq_one.1 h3).symm
  have hA : (ε 0 : K) ≠ 0 := (ε 0).ne_zero
  have hB : (ε 1 : K) ≠ 0 := (ε 1).ne_zero
  have hC : (ε 2 : K) ≠ 0 := (ε 2).ne_zero
  have hD : (ε 3 : K) ≠ 0 := (ε 3).ne_zero
  have hc2 : (ε 2 : K) ^ 2 = ε 0 * ε 1 * ε 3 := by
    have := congrArg Units.val h2
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      Units.val_one] at this
    field_simp at this
    linear_combination this
  have e1 : (ε 0 : K) ^ 3 = ε 1 * ε 3 := by
    refine mul_left_cancel₀ hA ?_
    linear_combination ((ε 0 : K) ^ 2 + ε 2) * hc + hc2
  have e2 : (ε 0 : K) ^ 2 = 1 := by
    have h4 : (ε 0 : K) ^ 4 * ((ε 0 : K) ^ 2) = (ε 0 : K) ^ 4 * 1 := by
      linear_combination ((ε 0 : K) ^ 3 + (ε 1 : K) * ε 3) * e1 + (ε 3 : K) ^ 2 * hb +
        (ε 2 : K) * hd - ((ε 0 : K) ^ 2 + ε 2) * hc
    exact mul_left_cancel₀ (pow_ne_zero 4 hA) h4
  have e3 : (ε 2 : K) = 1 := by rw [← hc, e2]
  have toU : ∀ j : Fin 4, (ε j : K) ^ 2 = 1 → ε j ^ 2 = 1 := fun j hj =>
    Units.ext (by simpa using hj)
  fin_cases j
  · exact toU 0 e2
  · exact toU 1 (by rw [hb, e3])
  · exact toU 2 (by rw [e3]; norm_num)
  · exact toU 3 (by rw [hd, e3])

end Cartan

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Torus

variable {K : Type} [Field K]

theorem torusGroup_eq_map_cartanChar (τ : Tag) :
    torusGroup τ K = ((cartanCharHom τ K).range).map (rootDiagUnitHom τ K) := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    refine ⟨cartanChar (Pi.mulSingle i s), ⟨Pi.mulSingle i s, rfl⟩, ?_⟩
    show rootDiagUnit τ (cartanChar (Pi.mulSingle i s)) = torusElt τ K i s
    rw [torusElt_eq_rootDiagUnit, cartanChar_mulSingle]
  · rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    change rootDiagUnit τ (cartanChar c) ∈ torusGroup τ K
    rw [← list_prod_torusElt_eq_rootDiagUnit]
    exact list_prod_torusElt_mem_torusGroup c

theorem mem_torusGroup_iff_cartanChar {τ : Tag} {h : ModGL τ K} :
    h ∈ torusGroup τ K ↔ ∃ c : Fin τ.rank → Kˣ, h = rootDiagUnit τ (cartanChar c) := by
  rw [torusGroup_eq_map_cartanChar]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨c, rfl⟩, rfl⟩

end Torus

end CFSG.GH74.GLS.Stage2.Bender.Thm1


namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section FixedTorus

variable {K : Type} [Field K]

theorem fixed_torusGroup_D4_eq_map_of_cube (σ : K ≃+* K) (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    torusGroup TwistTag.D4.tag K ⊓
        (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) =
      (torusGroup TwistTag.D4.tag (fixSubfield σ)).map
        (baseChangeGL (fixSubfield σ).subtype) := by
  set k := fixSubfield σ
  set ι := k.subtype
  refine le_antisymm ?_ ?_
  · rintro h ⟨hh, hfix⟩
    obtain ⟨c, rfl⟩ := mem_torusGroup_iff_cartanChar.1 hh
    set σU : Kˣ →* Kˣ := Units.map σ.toRingHom.toMonoidHom with hσU
    have hσa : ∀ l, σU (cartanChar c l) = cartanChar c l := by
      have hF : Units.map (entrywiseHom σ.toRingHom)
          (rootDiagUnit TwistTag.D4.tag (cartanChar c)) =
            rootDiagUnit TwistTag.D4.tag (cartanChar c) := hfix
      have h0 : Units.map (entrywiseHom σ.toRingHom)
          (rootDiagUnit TwistTag.D4.tag (cartanChar c)) =
          rootDiagUnit TwistTag.D4.tag (fun i => σU (cartanChar c i)) :=
        Units.ext (entrywise_rootDiag σ.toRingHom _)
      exact fun l => congrFun (rootDiagUnit_injective (h0.symm.trans hF)) l
    set ε : Fin TwistTag.D4.tag.rank → Kˣ := fun j => σU (c j) * (c j)⁻¹ with hε
    have hσc : cartanChar (fun j => σU (c j)) = fun l => σU (cartanChar c l) := by
      funext l
      simp only [cartanChar, map_prod, map_zpow]
    have hεk : cartanChar ε = 1 := by
      have : ε = (fun j => σU (c j)) * c⁻¹ := rfl
      rw [this, cartanChar_mul']
      have h1 : cartanChar c⁻¹ = (cartanChar c)⁻¹ := map_inv (cartanCharHom _ K) c
      rw [h1, hσc]
      funext l
      simp [hσa l]
    have hε2 := sq_eq_one_of_cartanChar_D4 ε hεk
    have hcfix : ∀ j, σ (c j : K) = c j := by
      intro j
      have h2 := hε2 j
      have h3 : (σ (c j : K)) ^ 2 = (c j : K) ^ 2 := by
        have := congrArg Units.val h2
        have hne : (c j : K) ≠ 0 := (c j).ne_zero
        simp only [hε, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val,
          Units.val_one] at this
        have e : ((σU (c j) : Kˣ) : K) = σ (c j : K) := rfl
        rw [e] at this
        field_simp at this
        exact this
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h4 | h4
      · exact h4
      · have h5 : σ (σ (c j : K)) = (c j : K) := by rw [h4, map_neg, h4, neg_neg]
        have h6 := hσ3 (c j : K)
        rw [h5, h4] at h6
        have : (c j : K) = - (c j : K) := h6.symm
        rw [h4]
        exact this.symm
    set c' : Fin TwistTag.D4.tag.rank → kˣ := fun j =>
      Units.mk0 ⟨c j, hcfix j⟩ fun h0 => (c j).ne_zero (congrArg Subtype.val h0) with hc'
    have hc'ι : ∀ j, Units.map ι.toMonoidHom (c' j) = c j := fun j => Units.ext rfl
    refine ⟨((List.finRange TwistTag.D4.tag.rank).map fun j => torusElt TwistTag.D4.tag k j
      (c' j)).prod, list_prod_torusElt_mem_torusGroup _, ?_⟩
    rw [map_list_prod, List.map_map, ← list_prod_torusElt_eq_rootDiagUnit]
    refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
    rw [Function.comp_apply, baseChangeGL_torusElt, hc'ι]
  · have hle : torusGroup TwistTag.D4.tag k ≤
        (torusGroup TwistTag.D4.tag K).comap (baseChangeGL ι) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨⟨i, s⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_torusGroup i _
    rintro _ ⟨g, hg, rfl⟩
    refine ⟨hle hg, ?_⟩
    change baseChangeGL σ.toRingHom (baseChangeGL ι g) = baseChangeGL ι g
    rw [baseChangeGL_baseChangeGL,
      show σ.toRingHom.comp ι = ι from RingHom.ext fun c => (mem_fixSubfield σ).1 c.2]

end FixedTorus

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section FixedGroup

variable {K : Type} [Field K] [Finite K]

theorem entrywiseFixedGroup_D4_eq_fixedFieldImage_of_cube (σ : K ≃+* K)
    (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    entrywiseFixedGroup TwistTag.D4.tag σ = fixedFieldImage TwistTag.D4.tag σ := by
  obtain ⟨-, -, -, hJΓ, hΓ, -⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup TwistTag.D4.tag K σ
  refine le_antisymm (fun g hg => ?_) hJΓ
  have hg' : g ∈ (entrywiseFixedGroup TwistTag.D4.tag σ : Set (ModGL TwistTag.D4.tag K)) := hg
  rw [hΓ] at hg'
  obtain ⟨h, hh, j, hj, rfl⟩ := Set.mem_mul.1 hg'
  refine mul_mem ?_ hj
  have hh' : h ∈ torusGroup TwistTag.D4.tag K ⊓
      (Units.map (entrywiseHom σ.toRingHom)).eqLocus (MonoidHom.id _) := ⟨hh.1, hh.2.2⟩
  rw [fixed_torusGroup_D4_eq_map_of_cube σ hσ3] at hh'
  obtain ⟨t, ht, rfl⟩ := hh'
  have hle : torusGroup TwistTag.D4.tag (fixSubfield σ) ≤
      adjointGroup TwistTag.D4.tag (fixSubfield σ) :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact ⟨t, hle ht, rfl⟩

end FixedGroup

end CFSG.GH74.GLS.Stage2.Bender.Thm1

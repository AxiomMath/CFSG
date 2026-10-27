module

public import CFSG.GH74.GLS.IVK.L2.Borel

public section

namespace CFSG.GH74.GLS.SP.Local

open CFSG.PSL2Table CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups

section PSL2

variable {F : Type} [Field F]

theorem psl2_weyl_relation : unip (1 : F) * (weyl * unip 1 * weyl⁻¹) * unip 1 = -weyl := by
  apply SL_ext <;> simp [mul_apply_SL, neg_apply_SL]

theorem psl2_weyl_inv : (weyl : SL(2, F))⁻¹ = -weyl := by
  apply SL_ext <;> simp [neg_apply_SL]

theorem psl2_bruhat_matrix_cases (m : SL(2, F))
    (h : unip (1 : F) * (m * unip 1 * m⁻¹) * unip 1 = m) :
    m = unip 3 ∨ ∃ a : F, m = unip (-a) * weyl⁻¹ * unip a := by
  have hdet := det_entries m
  have e00 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 0) h
  have e01 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 0 1) h
  have e10 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h
  have e11 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 1) h
  simp only [mul_apply_SL, coe_inv_SL, coe_unip] at e00 e01 e10 e11
  simp at e00 e01 e10 e11
  set a := (m : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b := (m : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c := (m : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d := (m : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hcc : c * (c + 1) = 0 := by linear_combination -e10
  rcases mul_eq_zero.1 hcc with h0 | h1
  · left
    have ha1 : a = 1 := by
      rw [h0] at e00 hdet
      linear_combination hdet - e00
    have hd1 : d = 1 := by
      rw [h0] at hdet
      linear_combination hdet - d * ha1
    have hb3 : b = 3 := by
      rw [h0, ha1, hd1] at e01
      linear_combination -e01
    apply SL_ext
    · simpa using ha1
    · simpa using hb3
    · simpa using h0
    · simpa using hd1
  · right
    have hc1 : c = -1 := by linear_combination h1
    refine ⟨a, ?_⟩
    rw [hc1] at e11 e01 hdet
    have hd' : d = -a := by
      linear_combination hdet - e11
    have hb' : b = a * a + 1 := by
      linear_combination e01 - 2 * a * hd'
    apply SL_ext
    · simpa [mul_apply_SL] using ha.symm
    · simpa [mul_apply_SL] using hb'
    · simpa [mul_apply_SL] using hc1
    · simpa [mul_apply_SL] using hd'

theorem psl2_bruhat_class_cases (m : SL(2, F))
    (h : mk m = mk (unip (1 : F) * (m * unip 1 * m⁻¹) * unip 1)) :
    mk m = mk (unip 3) ∨ ∃ a : F, mk m = mk (unip (-a) * weyl⁻¹ * unip a) := by
  rw [mk_eq_mk_iff] at h
  rcases h with h | h
  · rcases psl2_bruhat_matrix_cases m h with h' | ⟨a, h'⟩
    · exact Or.inl (by rw [h'])
    · exact Or.inr ⟨a, by rw [h']⟩
  · have hconj : (-m) * unip (1 : F) * (-m)⁻¹ = m * unip 1 * m⁻¹ := by
      apply SL_ext <;> simp [mul_apply_SL]
    have hneg : unip (1 : F) * ((-m) * unip 1 * (-m)⁻¹) * unip 1 = -m := by
      rw [hconj]; exact h
    rcases psl2_bruhat_matrix_cases (-m) hneg with h' | ⟨a, h'⟩
    · left; rw [← mk_neg m, h']
    · right; exact ⟨a, by rw [← mk_neg m, h']⟩

theorem psl2_hom_eq_id_of_fixes_unip_weyl {β : PSL(2, F) →* PSL(2, F)}
    (hU : ∀ s : F, β (mk (unip s)) = mk (unip s)) (hw : β (mk weyl) = mk weyl) :
    ∀ g : PSL(2, F), β g = g := by
  have hx : (mk weyl : PSL(2, F)) ∉ borel F := by
    rw [mk_mem_borel_iff, mem_borelSL_iff]
    simp
  have hle : Subgroup.closure ((unipotent F : Set PSL(2, F)) ∪ {mk weyl}) ≤
      MonoidHom.eqLocus β (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists x).1 hx
      exact hU t
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hw
  rw [closure_unipotent_insert_eq_top hx] at hle
  intro g
  exact hle (Subgroup.mem_top g)

theorem psl2_aut_fixing_U (α : PSL(2, F) ≃* PSL(2, F))
    (hα : ∀ s : F, α (mk (unip s)) = mk (unip s)) :
    ∃ x : F, ∀ g : PSL(2, F), α g = mk (unip x) * g * (mk (unip x))⁻¹ := by
  obtain ⟨m, hm⟩ := mk_surjective (α (mk weyl))
  have hrel : mk (weyl : SL(2, F)) = mk (unip 1 * (weyl * unip 1 * weyl⁻¹) * unip 1) := by
    rw [mk_eq_mk_iff]
    right
    exact psl2_weyl_relation
  have hrel' : mk (weyl : SL(2, F)) =
      mk (unip 1) * (mk weyl * mk (unip 1) * (mk weyl)⁻¹) * mk (unip 1) := by
    simpa only [map_mul, map_inv] using hrel
  have h1 : mk m = mk (unip 1 * (m * unip 1 * m⁻¹) * unip 1) := by
    have h := congrArg α hrel'
    simp only [map_mul, map_inv, hα] at h
    rw [← hm] at h
    simpa only [map_mul, map_inv] using h
  rcases psl2_bruhat_class_cases m h1 with h3 | ⟨a, h3⟩
  · exfalso
    have h4 : α (mk weyl) = α (mk (unip 3)) := by rw [← hm, h3, hα]
    have h5 := α.injective h4
    rw [mk_eq_mk_iff] at h5
    rcases h5 with h5 | h5
    · have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h5
      simp at this
    · have := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F) 1 0) h5
      simp [neg_apply_SL] at this
  · refine ⟨-a, ?_⟩
    let β : PSL(2, F) →* PSL(2, F) :=
      (MulAut.conj (mk (unip a))).toMonoidHom.comp α.toMonoidHom
    have hβapp : ∀ y, β y = mk (unip a) * α y * (mk (unip a))⁻¹ := fun y => rfl
    have hβU : ∀ s : F, β (mk (unip s)) = mk (unip s) := by
      intro s
      rw [hβapp, hα, ← map_inv, ← map_mul, ← map_mul, unip_neg, ← unip_add, ← unip_add]
      have : a + s + -a = s := by ring
      rw [this]
    have hβw : β (mk weyl) = mk weyl := by
      rw [hβapp, ← hm, h3, ← map_inv, ← map_mul, ← map_mul]
      have key : unip a * (unip (-a) * weyl⁻¹ * unip a) * (unip a)⁻¹ = weyl⁻¹ := by
        rw [← unip_neg a]
        group
      rw [key, psl2_weyl_inv, mk_neg]
    have hid := psl2_hom_eq_id_of_fixes_unip_weyl hβU hβw
    intro g
    have hneg : mk (unip (-a) : SL(2, F)) = (mk (unip a))⁻¹ := by rw [← map_inv, unip_neg]
    rw [hneg, inv_inv]
    have h := hid g
    rw [hβapp] at h
    calc α g = (mk (unip a))⁻¹ * (mk (unip a) * α g * (mk (unip a))⁻¹) * mk (unip a) := by group
      _ = _ := by rw [h]

end PSL2

section SylowStep

theorem aut_fixing_sylow_inner {F : Type} [Field F] [Finite F] (p k : ℕ) (hp : p.Prime)
    (hodd : p ≠ 2) (hq : Nat.card F = p ^ k) (hk : 1 ≤ k) {K : Type} [Group K]
    (e : K ≃* IVK.L2 F) (W : Subgroup K) (hWp : IsPGroup p ↥W) (hWc : Nat.card ↥W = Nat.card F)
    (α : K ≃* K) (hα : ∀ w ∈ W, α w = w) :
    ∃ w₀ ∈ W, ∀ k' : K, α k' = w₀ * k' * w₀⁻¹ := by
  have _ := hk
  have hF2 : (2 : F) ≠ 0 := by
    apply two_ne_zero_of_odd_card
    rw [hq]
    exact (hp.eq_two_or_odd'.resolve_left hodd).pow
  have : Fintype F := Fintype.ofFinite F
  have : Finite K := Finite.of_equiv _ (toPSL e).symm.toEquiv
  obtain ⟨Q, hWQ⟩ := hWp.exists_le_sylow
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hq Q
  set ψ := psiEquiv e c with hψ
  have hQcard : Nat.card (Q : Subgroup K) = Nat.card F := by
    rw [hc, Subgroup.card_map_of_injective ψ.injective, card_unipotent hF2,
      Nat.card_eq_fintype_card]
  have hWQ' : W = (Q : Subgroup K) := Subgroup.eq_of_le_of_card_ge hWQ (by rw [hQcard, hWc])
  have hmem : ∀ s : F, ψ (mk (unip s)) ∈ W := by
    intro s
    rw [hWQ', hc]
    exact ⟨_, mk_unip_mem_unipotent s, rfl⟩
  let α' : PSL(2, F) ≃* PSL(2, F) := ψ.trans (α.trans ψ.symm)
  have hα' : ∀ s : F, α' (mk (unip s)) = mk (unip s) := by
    intro s
    show ψ.symm (α (ψ (mk (unip s)))) = mk (unip s)
    rw [hα _ (hmem s), ψ.symm_apply_apply]
  obtain ⟨x, hx⟩ := psl2_aut_fixing_U α' hα'
  refine ⟨ψ (mk (unip x)), hmem x, fun k' => ?_⟩
  have h := hx (ψ.symm k')
  have h2 : α k' = ψ (α' (ψ.symm k')) := by
    show α k' = ψ (ψ.symm (α (ψ (ψ.symm k'))))
    simp
  rw [h2, h, map_mul, map_mul, map_inv, ψ.apply_symm_apply]

end SylowStep

end CFSG.GH74.GLS.SP.Local

module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec8TC
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Local

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup DihedralGroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame} {T₁ : Subgroup X}

theorem mem_yB_or (F : S.Frame) {a : X} (ha : a ∈ S.data.T) (ha2 : a ^ 2 = 1) (haB : a ∉ S.B) :
    F.yF⁻¹ * a ∈ S.B ∨ (F.xF * F.yF)⁻¹ * a ∈ S.B := by
  obtain ⟨i, hi⟩ := coords_refl (isRefl_yF F)
  have hx := coords_xF F
  have hsq : S.coords ⟨a, ha⟩ * S.coords ⟨a, ha⟩ = 1 := by
    rw [← map_mul, ← map_one S.coords]
    congr 1
    exact Subtype.ext (by simpa [pow_two] using ha2)
  have hnB : ¬ ((S.coords ⟨a, ha⟩).1 = 1 ∨ (S.coords ⟨a, ha⟩).1 = r 2) := fun h =>
    haB (mem_B_of_coords_fst ha h)
  have key : ∀ (c cx : DihedralGroup 4 × DihedralGroup 2) (j : ZMod 4),
      (cx = (r 1, 1) ∨ cx = (r 3, 1)) → c * c = 1 → ¬ (c.1 = 1 ∨ c.1 = r 2) →
      (((sr j, 1)⁻¹ * c).1 = 1 ∨ ((sr j, 1)⁻¹ * c).1 = r 2) ∨
        (((cx * (sr j, 1))⁻¹ * c).1 = 1 ∨ ((cx * (sr j, 1))⁻¹ * c).1 = r 2) := by
    decide
  rcases key _ _ i hx hsq hnB with h | h
  · left
    refine mem_B_of_coords_fst (mul_mem (inv_mem (yF_mem_T F)) ha) ?_
    rwa [coords_mul (inv_mem (yF_mem_T F)) ha, coords_inv (yF_mem_T F), hi]
  · right
    have hxy := mul_mem (xF_mem_T F) (yF_mem_T F)
    refine mem_B_of_coords_fst (mul_mem (inv_mem hxy) ha) ?_
    rwa [coords_mul (inv_mem hxy) ha, coords_inv hxy, coords_mul (xF_mem_T F) (yF_mem_T F), hi]

omit [Finite X] in
theorem sup_zpowers_eq {B : Subgroup X} {a b : X} (h : b⁻¹ * a ∈ B) :
    B ⊔ zpowers a = B ⊔ zpowers b := by
  apply le_antisymm
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have : a = b * (b⁻¹ * a) := by group
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers b)) (mem_sup_left h)
  · refine sup_le le_sup_left (zpowers_le.mpr ?_)
    have : b = a * (b⁻¹ * a)⁻¹ := by group
    rw [this]
    exact mul_mem (mem_sup_right (mem_zpowers a)) (mem_sup_left (inv_mem h))

theorem eq_E_of_elem_le_T (F : S.Frame) {A : Subgroup X} (hA : ElemAbelianTwo A)
    (hAT : A ≤ S.data.T) (hcard : Nat.card A = 16) :
    A = S.E F.yF ∨ A = S.E (F.xF * F.yF) := by
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ S.B := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show A ≤ S.B from hall)
    rw [hcard, S.card_B] at this
    omega
  have ha2 := hA.sq_eq_one a haA
  have haT := hAT haA
  have hcomm : ∀ b ∈ S.B, a * b = b * a := fun _ hb => (S.central_of_mem_B hb haT).symm
  have hle : A ≤ S.B ⊔ zpowers a := by
    intro g hg
    rcases mem_B_or_of_comm haT ha2 haB (hAT hg) (hA.comm g hg a haA) with h | h
    · exact mem_sup_left h
    · have : g = g * a * a⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers a)))
  have heq : A = S.B ⊔ zpowers a := Subgroup.eq_of_le_of_card_ge hle (by
    rw [card_sup_of_not_mem elemAbelianTwo_B ha2 haB hcomm, S.card_B, hcard])
  rcases mem_yB_or F haT ha2 haB with h | h
  · left; rw [heq, E_eq, sup_zpowers_eq h]
  · right; rw [heq, E_eq, sup_zpowers_eq h]

theorem mem_E0_of_not_conjTo {yi ki ui : X} (D : S.Sec6 T₁ yi ki ui) (h : IsRefl F yi)
    (hk : IsK (S := S) ki) {e : X} (he : e ∈ S.E yi) (hne : ¬ ConjTo S.t e) :
    e ∈ S.E0 yi ki := by
  rcases h.mem_E0_or hk he with h0 | h0
  · exact h0
  · exfalso
    apply hne
    have h1 := conjTo_t_mul_any D h hk h0
    rwa [← mul_assoc, ← S.data.commute_t (h.E_le_T he), mul_assoc, ← pow_two, S.t_sq,
      mul_one] at h1

theorem not_conjTo_conj {a g : X} (h : ¬ ConjTo S.t a) : ¬ ConjTo S.t (g * a * g⁻¹) := by
  rintro ⟨c, hc⟩
  refine h ⟨g⁻¹ * c, ?_⟩
  calc g⁻¹ * c * S.t * (g⁻¹ * c)⁻¹ = g⁻¹ * (c * S.t * c⁻¹) * g := by group
    _ = a := by rw [hc]; group

theorem not_conjTo_of_gens (D₁ : S.Sec6 T₁ F.yF F.kF (F.xF * F.yF))
    (D₂ : S.Sec6 T₁ (F.xF * F.yF) (S.z * F.kF) (S.z * F.yF)) {A : Subgroup X}
    (hA : ElemAbelianTwo A) (hcard : Nat.card A = 16) {s : Set X} (hsA : s ⊆ A)
    (hs : A ≤ closure s) (hns : ∀ x ∈ s, ¬ ConjTo S.t x) {a : X} (ha : a ∈ A) :
    ¬ ConjTo S.t a := by
  rintro ⟨c, hc⟩
  set A' := A.map (MulAut.conj c⁻¹).toMonoidHom with hA'
  have htA' : S.t ∈ A' := ⟨a, ha, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hc]; group⟩
  have hA'el : ElemAbelianTwo A' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hA.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA.sq_eq_one x hx, map_one]
  have hA't : A' ≤ centralizer ({S.t} : Set X) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hA'el.comm _ hx _ htA')
  obtain ⟨h, hh, hT⟩ := S.data.exists_conj_le_T (isPGroup_of_elemAbelianTwo hA'el) hA't
  set A'' := A'.map (MulAut.conj h).toMonoidHom with hA''
  have hA''el : ElemAbelianTwo A'' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hA'el.comm x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hA'el.sq_eq_one x hx, map_one]
  have hcard'' : Nat.card A'' = 16 := by
    rw [hA'', card_map_of_injective (MulAut.conj h).injective, hA',
      card_map_of_injective (MulAut.conj c⁻¹).injective, hcard]
  have htA'' : S.t ∈ A'' := ⟨S.t, htA', by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [mem_centralizer_singleton_iff.mp hh, mul_inv_cancel_right]⟩
  have hmem : ∀ x ∈ A, h * c⁻¹ * x * (h * c⁻¹)⁻¹ ∈ A'' := fun x hx =>
    ⟨c⁻¹ * x * c⁻¹⁻¹, ⟨x, hx, rfl⟩, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hcase : ∀ {yi ki ui : X} (D : S.Sec6 T₁ yi ki ui), IsRefl F yi → IsK (S := S) ki →
      A'' = S.E yi → False := by
    intro yi ki ui D hyi hki hE
    have hs0 : ∀ x ∈ s, h * c⁻¹ * x * (h * c⁻¹)⁻¹ ∈ S.E0 yi ki := fun x hx =>
      mem_E0_of_not_conjTo D hyi hki (hE ▸ hmem x (hsA hx)) (not_conjTo_conj (hns x hx))
    have hle : A'' ≤ S.E0 yi ki := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have hx' := hs hx
      have hcl : (closure s).map (MulAut.conj (h * c⁻¹)).toMonoidHom ≤ S.E0 yi ki := by
        rw [MonoidHom.map_closure, closure_le]
        rintro _ ⟨y, hy, rfl⟩
        exact hs0 y hy
      have := hcl ⟨x, hx', rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rwa [show h * (c⁻¹ * x * c⁻¹⁻¹) * h⁻¹ = h * c⁻¹ * x * (h * c⁻¹)⁻¹ by group]
    exact hyi.t_not_mem_E0 hki (hle htA'')
  rcases eq_E_of_elem_le_T F hA''el ((map_mono (le_refl A')).trans hT) hcard'' with hE | hE
  · exact hcase D₁ (isRefl_yF F) (isK_kF F) hE
  · exact hcase D₂ (isRefl_xyF F) (isK_zkF F) hE

end Sec8

end CFSG.ComponentClassification.HSFLit

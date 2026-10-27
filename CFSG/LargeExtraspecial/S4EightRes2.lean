module

public import CFSG.LargeExtraspecial.S4SpFour

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem beta_spRho_apply_self (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2) (x : V) :
    β x (spRho hβ hcd l x) = l * β x c := by
  rw [spRho_apply, map_add, map_add, map_smul, map_smul, hβ.self_eq_zero, smul_eq_mul,
    smul_eq_mul]
  rcases zmod2_eq_zero_or_eq_one (β x c) with h | h <;>
    rcases zmod2_eq_zero_or_eq_one (β x d) with h' | h' <;>
    rcases zmod2_eq_zero_or_eq_one l with rfl | rfl <;>
    simp only [h, h'] <;> decide

theorem apply_eq_of_commute_spRho_one (hβ : β.IsAlt) (hnd : β.Nondegenerate) {c d : V}
    (hcd : β c d = 0) {f : V ≃ₗ[ZMod 2] V} (hf : f ∈ TauCeti.BilinForm.isometryGroup β)
    (hcomm : f * spRho hβ hcd 1 = spRho hβ hcd 1 * f) : f c = c := by
  have hf' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hf
  have key : ∀ v, β (f v) c = β (f v) (f c) := by
    intro v
    have h3 : spRho hβ hcd 1 (f v) = f (spRho hβ hcd 1 v) := by
      have := congrArg (fun u : V ≃ₗ[ZMod 2] V => u v) hcomm
      simpa only [LinearEquiv.mul_apply] using this.symm
    have h1 := beta_spRho_apply_self hβ hcd 1 (f v)
    rw [h3, hf', beta_spRho_apply_self hβ hcd 1 v, one_mul, one_mul] at h1
    rw [hf', ← h1]
  have key' : ∀ w, β (f c - c) w = 0 := by
    intro w
    have := key (f.symm w)
    rw [f.apply_symm_apply] at this
    rw [isAlt_symm hβ, map_sub, ← this, sub_self]
  exact sub_eq_zero.mp (hnd.1 _ key')

theorem beta_eq_zero_of_spRho_apply_eq (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (hc : c ≠ 0)
    (hd : d ∉ (ZMod 2) ∙ c) {l : ZMod 2} {v : V} (hv : spRho hβ hcd l v = v) :
    β v c = 0 ∧ β v d = 0 := by
  rw [spRho_apply, add_assoc, add_eq_left] at hv
  rcases zmod2_eq_zero_or_eq_one (β v c) with h1 | h1
  · rw [h1, zero_smul, zero_add, mul_zero, add_zero] at hv
    refine ⟨h1, ?_⟩
    rcases zmod2_eq_zero_or_eq_one (β v d) with h2 | h2
    · exact h2
    · rw [h2, one_smul] at hv
      exact absurd hv hc
  · exfalso
    rw [h1, one_smul] at hv
    apply hd
    rw [eq_neg_of_add_eq_zero_left hv]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c))

theorem spRho_eq_of_mem_span (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) (l : ZMod 2)
    (hd : d ∈ (ZMod 2) ∙ c) : spRho hβ hcd l = spRho hβ (map_zero (β c)) l := by
  rcases mem_span_singleton_iff.mp hd with h | h
  · exact spRho_congr hβ hcd _ rfl h rfl
  · have h' : β c (0 + c) = 0 := by
      rw [zero_add]
      rw [h] at hcd
      exact hcd
    rw [spRho_congr hβ hcd h' rfl (by rw [zero_add, h]) rfl]
    exact spRho_add_self hβ _ l h'

theorem not_mem_span_of_spRho_mem (hβ : β.IsAlt) {c d : V} (hcd : β c d = 0) {l : ZMod 2}
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hτ : spTransvection β hβ c ∉ E)
    (hE : spRho hβ hcd l ∈ E) (h1 : spRho hβ hcd l ≠ 1) : d ∉ (ZMod 2) ∙ c := by
  intro hdP
  rw [spRho_eq_of_mem_span hβ hcd l hdP] at hE h1
  rcases zmod2_eq_zero_or_eq_one l with rfl | rfl
  · exact h1 (spRho_zero_zero hβ c _)
  · rw [spRho_zero_one] at hE
    exact hτ hE

variable [FiniteDimensional (ZMod 2) V]

theorem mem_span_pair_of_perp (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {c d : V} (hc : c ≠ 0) (hd : d ∉ (ZMod 2) ∙ c)
    (hcd : β c d = 0) {v : V} (hvc : β c v = 0) (hvd : β d v = 0) :
    v ∈ Submodule.span (ZMod 2) {c, d} := by
  set N := Submodule.span (ZMod 2) ({c, d} : Set V) with hN
  have hdc : β d c = 0 := by rw [isAlt_symm hβ, hcd]
  have hcN : (ZMod 2) ∙ c ≤ N := Submodule.span_mono (by simp)
  have hdN : d ∈ N := Submodule.subset_span (by simp)
  have h2 : 2 ≤ finrank (ZMod 2) N := by
    have hlt : (ZMod 2) ∙ c < N := lt_of_le_of_ne hcN fun h => hd (h ▸ hdN)
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_span_singleton hc] at this
    omega
  have hNN : N ≤ LinearMap.BilinForm.orthogonal β N := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨r', s', rfl⟩ := Submodule.mem_span_pair.mp hy
    show β _ _ = 0
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hβ.self_eq_zero,
      hcd, hdc, smul_zero, add_zero]
  have hdim := LinearMap.BilinForm.finrank_orthogonal hnd N
  have hmono := Submodule.finrank_mono hNN
  have heq : N = LinearMap.BilinForm.orthogonal β N :=
    Submodule.eq_of_le_of_finrank_eq hNN (by omega)
  rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hn
  show β _ _ = 0
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hvc, hvd,
    smul_zero, add_zero]

theorem beta_eq_one_of_not_mem_span (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {c d d' : V} (hc : c ≠ 0) (hd : d ∉ (ZMod 2) ∙ c)
    (hd' : d' ∉ (ZMod 2) ∙ c) (hdd' : d + d' ∉ (ZMod 2) ∙ c) (hcd : β c d = 0)
    (hcd' : β c d' = 0) : β d d' = 1 := by
  by_contra h
  have h0 : β d d' = 0 := (zmod2_eq_zero_or_eq_one _).resolve_right h
  obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp
    (mem_span_pair_of_perp hβ hnd h4 hc hd hcd hcd' h0)
  rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
  · apply hd'
    rw [← hrs, zero_smul, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)
  · apply hdd'
    rw [← hrs, one_smul, add_comm d, add_assoc, vec_add_self, add_zero]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)

theorem perp_cases (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : finrank (ZMod 2) V = 4)
    {a x y : V} (ha : a ≠ 0) (hx : β a x = 0) (hy : β a y = 0) (hxn : x ∉ (ZMod 2) ∙ a)
    (hyn : y ∉ (ZMod 2) ∙ a) (hxy : x + y ∉ (ZMod 2) ∙ a) {v : V} (hv : β a v = 0) :
    v ∈ (ZMod 2) ∙ a ∨ v + x ∈ (ZMod 2) ∙ a ∨ v + y ∈ (ZMod 2) ∙ a ∨
      v + x + y ∈ (ZMod 2) ∙ a := by
  have hβxy := beta_eq_one_of_not_mem_span hβ hnd h4 ha hxn hyn hxy hx hy
  have hmem : ∀ w, β a w = 0 → β x w = 0 → w ∈ (ZMod 2) ∙ a ∨ w + x ∈ (ZMod 2) ∙ a := by
    intro w hw hxw
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp
      (mem_span_pair_of_perp hβ hnd h4 ha hxn hx hw hxw)
    have hra : r • a ∈ (ZMod 2) ∙ a := Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)
    rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
    · left
      rw [← hrs, zero_smul, add_zero]
      exact hra
    · right
      rw [← hrs, one_smul, add_assoc, vec_add_self, add_zero]
      exact hra
  rcases zmod2_eq_zero_or_eq_one (β x v) with h | h
  · rcases hmem v hv h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have hw : β a (v + y) = 0 := by rw [map_add, hv, hy, add_zero]
    have hxw : β x (v + y) = 0 := by rw [map_add, h, hβxy, zmod2_add_self]
    rcases hmem (v + y) hw hxw with h' | h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · right; right; right
      rwa [add_assoc, add_comm y x, ← add_assoc] at h'

theorem card_centralizer_le_three (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h4 : finrank (ZMod 2) V = 4) {a d : V} (ha : a ≠ 0) (hd : β a d = 0)
    (hdn : d ∉ (ZMod 2) ∙ a) (l : ZMod 2) {P : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hreg : ∀ f ∈ P, f a = a → f = 1) :
    Nat.card (P ⊓ centralizer {spRho hβ hd l} : Subgroup (V ≃ₗ[ZMod 2] V)) ≤ 3 := by
  classical
  set T : Finset V := {a, d, a + d}
  have hea : spRho hβ hd l a = a := (spRho_mem_spPointRadical hβ hd l).2.1
  have hmem : ∀ u ∈ (P ⊓ centralizer {spRho hβ hd l} : Subgroup (V ≃ₗ[ZMod 2] V)), u a ∈ T := by
    intro u hu
    obtain ⟨huP, huC⟩ := mem_inf.mp hu
    have hc := mem_centralizer_singleton_iff.mp huC
    have hfix : spRho hβ hd l (u a) = u a := by
      have := congrArg (fun w : V ≃ₗ[ZMod 2] V => w a) hc
      simp only [LinearEquiv.mul_apply, hea] at this
      exact this.symm
    obtain ⟨h1, h2⟩ := beta_eq_zero_of_spRho_apply_eq hβ hd ha hdn hfix
    rw [isAlt_symm hβ] at h1 h2
    obtain ⟨r, s, hrs⟩ := Submodule.mem_span_pair.mp
      (mem_span_pair_of_perp hβ hnd h4 ha hdn hd h1 h2)
    have hne : u a ≠ 0 := fun h0 => ha (u.map_eq_zero_iff.mp h0)
    simp only [T, Finset.mem_insert, Finset.mem_singleton]
    rcases zmod2_eq_zero_or_eq_one r with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one s with rfl | rfl
    · exact absurd (by rw [← hrs, zero_smul, zero_smul, add_zero]) hne
    · right; left; rw [← hrs, zero_smul, one_smul, zero_add]
    · left; rw [← hrs, one_smul, zero_smul, add_zero]
    · right; right; rw [← hrs, one_smul, one_smul]
  let φ : (P ⊓ centralizer {spRho hβ hd l} : Subgroup (V ≃ₗ[ZMod 2] V)) → T :=
    fun u => ⟨(u : V ≃ₗ[ZMod 2] V) a, hmem u u.2⟩
  have hφ : Function.Injective φ := by
    intro u u' h
    have h' : (u : V ≃ₗ[ZMod 2] V) a = (u' : V ≃ₗ[ZMod 2] V) a := congrArg Subtype.val h
    have hP : (u' : V ≃ₗ[ZMod 2] V)⁻¹ * u ∈ P :=
      mul_mem (inv_mem (mem_inf.mp u'.2).1) (mem_inf.mp u.2).1
    have h1 := hreg _ hP (by
      rw [LinearEquiv.mul_apply, h']
      exact (u' : V ≃ₗ[ZMod 2] V).symm_apply_apply a)
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_eq_finsetCard] at this
  exact this.trans Finset.card_le_three

end CFSG.LargeExtraspecial.S4

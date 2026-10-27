module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Subgroup CFSG.EvenSporadicStandard.HNRecog.Section3

private lemma trans_conj_apply {G : Type*} [Group G] (e : G ≃* G) (g x : G) :
    (e.trans (MulAut.conj g)) x = g * e x * g⁻¹ := by
  rw [MulEquiv.trans_apply, MulAut.conj_apply]

theorem xAutInner_of_data {X : Type*} [Group X] {A c₁ c₂ : X} (hAc : ∀ x : X, x * A = A * x)
    (hc₁ : c₁ ∈ commutator X) (hc₂ : c₂ ∈ commutator X)
    (hgen : commutator X ≤ closure ({c₁, c₂} : Set X))
    (h5 : c₁ ^ 5 = 1) (h1 : c₁ ≠ 1) (h3 : c₂ ^ 3 = 1) (hrel : relA c₁ c₂ = A)
    (hF1 : ∀ y ∈ commutator X, y ^ 5 = 1 → y ≠ 1 → ∃ h : X, h * c₁ * h⁻¹ = y)
    (hF2 : ∀ v ∈ commutator X, v ^ 3 = 1 → relA c₁ v = A →
      ∃ d : X, d * c₁ = c₁ * d ∧ d * c₂ * d⁻¹ = v) :
    XAutInner X A := by
  intro σ hσ
  have hσc₁mem : σ c₁ ∈ commutator X := mulEquiv_mem_commutator σ hc₁
  have hσc₁5 : (σ c₁) ^ 5 = 1 := by rw [← map_pow, h5, map_one]
  have hσc₁ne : σ c₁ ≠ 1 := σ.map_ne_one_iff.mpr h1
  obtain ⟨h, hh⟩ := hF1 (σ c₁) hσc₁mem hσc₁5 hσc₁ne
  let σ₁ : X ≃* X := σ.trans (MulAut.conj h⁻¹)
  have hσ₁c₁ : σ₁ c₁ = c₁ := by
    change (σ.trans (MulAut.conj h⁻¹)) c₁ = c₁
    rw [trans_conj_apply, ← hh]
    group
  have hσ₁A : σ₁ A = A := by
    change (σ.trans (MulAut.conj h⁻¹)) A = A
    rw [trans_conj_apply, hσ, hAc h⁻¹]
    group
  let v : X := σ₁ c₂
  have hv : v ∈ commutator X := mulEquiv_mem_commutator σ₁ hc₂
  have hv3 : v ^ 3 = 1 := by
    change (σ₁ c₂) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have hvrel : relA c₁ v = A := by
    have h := map_relA σ₁ c₁ c₂
    rw [hrel, hσ₁A] at h
    change relA c₁ (σ₁ c₂) = A
    rw [h, hσ₁c₁]
  obtain ⟨d, hd1, hd2⟩ := hF2 v hv hv3 hvrel
  let σ₂ : X ≃* X := σ₁.trans (MulAut.conj d⁻¹)
  have hd1' : Commute d⁻¹ c₁ := (show Commute d c₁ from hd1).inv_left
  have hσ₂c₁ : σ₂ c₁ = c₁ := by
    change (σ₁.trans (MulAut.conj d⁻¹)) c₁ = c₁
    rw [trans_conj_apply, hσ₁c₁, hd1']
    group
  have hσ₂c₂ : σ₂ c₂ = c₂ := by
    change (σ₁.trans (MulAut.conj d⁻¹)) c₂ = c₂
    rw [trans_conj_apply]
    change d⁻¹ * v * (d⁻¹)⁻¹ = c₂
    rw [← hd2]
    group
  have hfixc : Set.EqOn σ₂.toMonoidHom (MonoidHom.id X) ({c₁, c₂} : Set X) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hσ₂c₁
    · exact hσ₂c₂
  have hfix : ∀ x ∈ commutator X, σ₂ x = x := by
    intro x hx
    simpa using MonoidHom.eqOn_closure hfixc (hgen hx)
  refine ⟨h * d, fun x hx => ?_⟩
  have hfixx : σ₂ x = x := hfix x hx
  have hσ₂x : d⁻¹ * σ₁ x * d = x := by
    change (σ₁.trans (MulAut.conj d⁻¹)) x = x at hfixx
    rw [trans_conj_apply] at hfixx
    simpa using hfixx
  have hσ₁x : σ₁ x = d * x * d⁻¹ := by
    have h := congrArg (fun t => d * t * d⁻¹) hσ₂x
    rw [← h]
    group
  have hσ₁x' : σ₁ x = h⁻¹ * σ x * h := by
    rw [trans_conj_apply]
    simp
  calc σ x = h * (h⁻¹ * σ x * h) * h⁻¹ := by group
    _ = h * σ₁ x * h⁻¹ := by rw [← hσ₁x']
    _ = h * (d * x * d⁻¹) * h⁻¹ := by rw [hσ₁x]
    _ = (h * d) * x * (h * d)⁻¹ := by group

theorem xAutInner_of_ambient {Γ : Type} [Group Γ] (X : Subgroup Γ) {A c₁ c₂ : Γ} (hA : A ∈ X)
    (hAc : ∀ x ∈ X, x * A = A * x) (hc₁ : c₁ ∈ derivedOf X) (hc₂ : c₂ ∈ derivedOf X)
    (hgen : derivedOf X ≤ closure ({c₁, c₂} : Set Γ))
    (h5 : c₁ ^ 5 = 1) (h1 : c₁ ≠ 1) (h3 : c₂ ^ 3 = 1) (hrel : relA c₁ c₂ = A)
    (hF1 : ∀ y ∈ derivedOf X, y ^ 5 = 1 → y ≠ 1 → ∃ h ∈ X, h * c₁ * h⁻¹ = y)
    (hF2 : ∀ v ∈ derivedOf X, v ^ 3 = 1 → relA c₁ v = A →
      ∃ d ∈ X, d * c₁ = c₁ * d ∧ d * c₂ * d⁻¹ = v) :
    XAutInner ↥X ⟨A, hA⟩ := by
  obtain ⟨hc₁X, hc₁c⟩ := mem_derivedOf_iff.mp hc₁
  obtain ⟨hc₂X, hc₂c⟩ := mem_derivedOf_iff.mp hc₂
  set c₁' : ↥X := ⟨c₁, hc₁X⟩ with hc₁'_def
  set c₂' : ↥X := ⟨c₂, hc₂X⟩ with hc₂'_def
  set A' : ↥X := ⟨A, hA⟩ with hA'_def
  have hAc' : ∀ x : ↥X, x * A' = A' * x := by
    intro x
    apply Subtype.ext
    simpa [hA'_def] using hAc (x : Γ) x.2
  have hc₁' : c₁' ∈ commutator ↥X := hc₁c
  have hc₂' : c₂' ∈ commutator ↥X := hc₂c
  have himg : X.subtype '' ({c₁', c₂'} : Set ↥X) = ({c₁, c₂} : Set Γ) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw ⊢
      rcases hw with rfl | rfl <;> simp [hc₁'_def, hc₂'_def]
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨c₁', by simp, rfl⟩
      · exact ⟨c₂', by simp, rfl⟩
  have hmap : (closure ({c₁', c₂'} : Set ↥X)).map X.subtype = closure ({c₁, c₂} : Set Γ) := by
    rw [MonoidHom.map_closure, himg]
  have hgen' : commutator ↥X ≤ closure ({c₁', c₂'} : Set ↥X) := by
    rw [← Subgroup.map_le_map_iff_of_injective X.subtype_injective, hmap]
    exact hgen
  have h5' : c₁' ^ 5 = 1 := by
    rw [hc₁'_def]
    apply Subtype.ext
    simp [h5]
  have h1' : c₁' ≠ 1 := by
    rw [hc₁'_def]
    intro hh
    exact h1 (by simpa using congrArg Subtype.val hh)
  have h3' : c₂' ^ 3 = 1 := by
    rw [hc₂'_def]
    apply Subtype.ext
    simp [h3]
  have hrel' : relA c₁' c₂' = A' := by
    rw [hc₁'_def, hc₂'_def, hA'_def]
    apply Subtype.ext
    simp only [relA, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hrel
  have hF1' : ∀ y ∈ commutator ↥X, y ^ 5 = 1 → y ≠ 1 →
      ∃ k : ↥X, k * c₁' * k⁻¹ = y := by
    intro y hy hy5 hy1
    have hyder : (y : Γ) ∈ derivedOf X := mem_derivedOf_iff.mpr ⟨y.2, hy⟩
    have hy5' : (y : Γ) ^ 5 = 1 := by
      simpa using congrArg Subtype.val hy5
    have hy1' : (y : Γ) ≠ 1 := by
      intro hh
      exact hy1 (Subtype.ext (by simpa using hh))
    obtain ⟨k, hkX, hkk⟩ := hF1 (y : Γ) hyder hy5' hy1'
    exact ⟨⟨k, hkX⟩, by apply Subtype.ext; simpa [hc₁'_def] using hkk⟩
  have hF2' : ∀ v ∈ commutator ↥X, v ^ 3 = 1 → relA c₁' v = A' →
      ∃ e : ↥X, e * c₁' = c₁' * e ∧ e * c₂' * e⁻¹ = v := by
    intro v hv hv3 hvrel
    have hvder : (v : Γ) ∈ derivedOf X := mem_derivedOf_iff.mpr ⟨v.2, hv⟩
    have hv3' : (v : Γ) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hv3
    have hvrel' : relA c₁ (v : Γ) = A := by
      have h := congrArg Subtype.val hvrel
      simp only [relA, Subgroup.coe_mul, Subgroup.coe_inv, hc₁'_def, hA'_def] at h
      exact h
    obtain ⟨e, heX, he1, he2⟩ := hF2 (v : Γ) hvder hv3' hvrel'
    refine ⟨⟨e, heX⟩, ?_, ?_⟩
    · apply Subtype.ext
      simpa [hc₁'_def] using he1
    · apply Subtype.ext
      simpa [hc₂'_def] using he2
  have hmain := xAutInner_of_data hAc' hc₁' hc₂' hgen' h5' h1' h3' hrel' hF1' hF2'
  rwa [hA'_def] at hmain

end CFSG.EvenSporadicStandard.HNRecog.Section4

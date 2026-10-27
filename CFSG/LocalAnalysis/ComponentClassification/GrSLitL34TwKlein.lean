module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRADefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsElem

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.GrSLit.L34Facts

theorem mk_mul_mk (a b c d : Equiv.Perm (Fin 42)) :
    (⟨a, b, false⟩ : WrE) * ⟨c, d, false⟩ = ⟨a * c, b * d, false⟩ := rfl

theorem mk_sq (a b : Equiv.Perm (Fin 42)) (ha : a * a = 1) (hb : b * b = 1) :
    (⟨a, b, false⟩ : WrE) * ⟨a, b, false⟩ = 1 := by
  rw [mk_mul_mk, ha, hb]
  rfl

theorem mk_comm (a b c d : Equiv.Perm (Fin 42)) (h₁ : a * c = c * a) (h₂ : b * d = d * b) :
    (⟨a, b, false⟩ : WrE) * ⟨c, d, false⟩ = ⟨c, d, false⟩ * ⟨a, b, false⟩ := by
  rw [mk_mul_mk, mk_mul_mk, h₁, h₂]

theorem mul_e (x y : WrE) : (x * y).e = xor x.e y.e := by
  rw [WrE.mul_def]
  split <;> rfl

private def noSwapB (L : Subgroup (Equiv.Perm (Fin 42))) : Subgroup WrE where
  carrier := {x | x.e = false ∧ x.b ∈ L}
  one_mem' := ⟨rfl, L.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    rw [Set.mem_setOf_eq, WrE.mul_def, hy.1]
    simp only [Bool.false_eq_true, ↓reduceIte, hx.1, Bool.xor_false, true_and]
    exact L.mul_mem hx.2 hy.2
  inv_mem' := by
    intro x hx
    rw [Set.mem_setOf_eq, WrE.inv_def, hx.1]
    simp only [Bool.false_eq_true, ↓reduceIte, true_and]
    exact L.inv_mem hx.2

theorem klein_violation {X : Subgroup WrE} (hN : N0w ≤ X) {g : WrE}
    {s s' e₁ e₂ f₁ f₂ : Equiv.Perm (Fin 42)} (hg : g * g = ⟨s, s', false⟩)
    (he₁ : e₁ ∈ L34Facts.T0) (he₂ : e₂ ∈ L34Facts.T0) (hf₁ : f₁ ∈ L34Facts.T0)
    (hf₂ : f₂ ∈ L34Facts.T0) (he₁2 : e₁ * e₁ = 1) (he₂2 : e₂ * e₂ = 1) (hf₁2 : f₁ * f₁ = 1)
    (hf₂2 : f₂ * f₂ = 1) (he₁1 : e₁ ≠ 1) (he₂1 : e₂ ≠ 1) (he₁₂ : e₁ ≠ e₂) (hf₁1 : f₁ ≠ 1)
    (hf₂1 : f₂ ≠ 1) (hf₁₂ : f₂ ≠ f₁) (hee : e₁ * e₂ = e₂ * e₁) (hff : f₁ * f₂ = f₂ * f₁)
    (hes₁ : e₁ * s = s * e₁) (hes₂ : e₂ * s = s * e₂) (hfs₁ : f₁ * s' = s' * f₁)
    (hfs₂ : f₂ * s' = s' * f₂) :
    ∃ F ≤ X ⊓ centralizer ({g * g} : Set WrE), IsEightGroup F ∧
      ∃ w ∈ X ⊓ centralizer ({g * g} : Set WrE), w * w = 1 ∧ (∀ e ∈ F, w * e = e * w) ∧
        w ∉ F := by
  have T1 : (1 : Equiv.Perm (Fin 42)) ∈ L34Facts.T0 := L34Facts.T0.one_mem
  have hm1 : ∀ a : Equiv.Perm (Fin 42), a * 1 = 1 * a := fun a => by rw [mul_one, one_mul]
  obtain ⟨A, hA⟩ : ∃ A : WrE, A = ⟨e₁, 1, false⟩ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : WrE, B = ⟨e₂, 1, false⟩ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : WrE, C = ⟨1, f₁, false⟩ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : WrE, D = ⟨1, f₂, false⟩ := ⟨_, rfl⟩
  have hAX : A ∈ X := hA ▸ hN ⟨rfl, he₁, T1⟩
  have hBX : B ∈ X := hB ▸ hN ⟨rfl, he₂, T1⟩
  have hCX : C ∈ X := hC ▸ hN ⟨rfl, T1, hf₁⟩
  have hDX : D ∈ X := hD ▸ hN ⟨rfl, T1, hf₂⟩
  have hgcomm : ∀ x : WrE, x * ⟨s, s', false⟩ = ⟨s, s', false⟩ * x →
      x ∈ centralizer ({g * g} : Set WrE) := fun x hx => by
    rw [mem_centralizer_singleton_iff, hg]
    exact hx
  have hAg : A ∈ centralizer ({g * g} : Set WrE) :=
    hgcomm _ (by rw [hA]; exact mk_comm _ _ _ _ hes₁ (hm1 s'))
  have hBg : B ∈ centralizer ({g * g} : Set WrE) :=
    hgcomm _ (by rw [hB]; exact mk_comm _ _ _ _ hes₂ (hm1 s'))
  have hCg : C ∈ centralizer ({g * g} : Set WrE) :=
    hgcomm _ (by rw [hC]; exact mk_comm _ _ _ _ (hm1 s) hfs₁)
  have hDg : D ∈ centralizer ({g * g} : Set WrE) :=
    hgcomm _ (by rw [hD]; exact mk_comm _ _ _ _ (hm1 s) hfs₂)
  have hA2 : A * A = 1 := by rw [hA]; exact mk_sq _ _ he₁2 (mul_one 1)
  have hB2 : B * B = 1 := by rw [hB]; exact mk_sq _ _ he₂2 (mul_one 1)
  have hC2 : C * C = 1 := by rw [hC]; exact mk_sq _ _ (mul_one 1) hf₁2
  have hD2 : D * D = 1 := by rw [hD]; exact mk_sq _ _ (mul_one 1) hf₂2
  have hAB : A * B = B * A := by rw [hA, hB]; exact mk_comm _ _ _ _ hee (hm1 1)
  have hAC : A * C = C * A := by rw [hA, hC]; exact mk_comm _ _ _ _ (hm1 e₁) (hm1 f₁)
  have hBC : B * C = C * B := by rw [hB, hC]; exact mk_comm _ _ _ _ (hm1 e₂) (hm1 f₁)
  have hAD : A * D = D * A := by rw [hA, hD]; exact mk_comm _ _ _ _ (hm1 e₁) (hm1 f₂)
  have hBD : B * D = D * B := by rw [hB, hD]; exact mk_comm _ _ _ _ (hm1 e₂) (hm1 f₂)
  have hCD : C * D = D * C := by rw [hC, hD]; exact mk_comm _ _ _ _ (hm1 1) hff
  have hA1 : A ≠ 1 := fun h => he₁1 (by rw [hA] at h; exact congrArg WrE.a h)
  have hBA : B ∉ zpowers A := fun h => by
    rcases eq_one_or_eq_of_mem_zpowers hA2 h with h | h
    · exact he₂1 (by rw [hB] at h; exact congrArg WrE.a h)
    · exact he₁₂ (by rw [hA, hB] at h; exact (congrArg WrE.a h).symm)
  have hQ : zpowers B ⊔ zpowers A ≤ noSwapB ⊥ :=
    sup_le (zpowers_le.2 (by rw [hB]; exact ⟨rfl, Subgroup.one_mem _⟩))
      (zpowers_le.2 (by rw [hA]; exact ⟨rfl, Subgroup.one_mem _⟩))
  have hCQ : C ∉ zpowers B ⊔ zpowers A := fun h => by
    have := (hQ h).2
    rw [hC, Subgroup.mem_bot] at this
    exact hf₁1 this
  have hE8 := isEightGroup_of_three hA2 hB2 hC2 hAB hAC hBC hA1 hBA hCQ
  have hF : zpowers C ⊔ (zpowers B ⊔ zpowers A) ≤ noSwapB (zpowers f₁) :=
    sup_le (zpowers_le.2 (by rw [hC]; exact ⟨rfl, mem_zpowers f₁⟩))
      (sup_le (zpowers_le.2 (by rw [hB]; exact ⟨rfl, Subgroup.one_mem _⟩))
        (zpowers_le.2 (by rw [hA]; exact ⟨rfl, Subgroup.one_mem _⟩)))
  have hDF : D ∉ zpowers C ⊔ (zpowers B ⊔ zpowers A) := fun h => by
    have := (hF h).2
    rw [hD] at this
    rcases eq_one_or_eq_of_mem_zpowers hf₁2 this with h | h
    · exact hf₂1 h
    · exact hf₁₂ h
  refine ⟨zpowers C ⊔ (zpowers B ⊔ zpowers A), ?_, hE8, D, mem_inf.2 ⟨hDX, hDg⟩, hD2, ?_, hDF⟩
  · exact sup_le (zpowers_le.2 (mem_inf.2 ⟨hCX, hCg⟩))
      (sup_le (zpowers_le.2 (mem_inf.2 ⟨hBX, hBg⟩)) (zpowers_le.2 (mem_inf.2 ⟨hAX, hAg⟩)))
  · have hle : zpowers C ⊔ (zpowers B ⊔ zpowers A) ≤ centralizer ({D} : Set WrE) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hCD))
        (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hBD))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 hAD)))
    intro e he
    exact (mem_centralizer_singleton_iff.1 (hle he)).symm

end CFSG.ComponentClassification.GrSLit.L34Tw

module

public import CFSG.FeitThompson.Representations.DisjointCoherentWeightedFamiliesOrthogonal
public import CFSG.FeitThompson.Representations.UnitInnerProductSignedPair

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CoherentJoin

open CoherentAntirealBlock DisjointCoherentBlocks

section Direct
variable {R' M : Type*} [Ring R'] [AddCommGroup M] [Module R' M]

noncomputable def prodEquivSupOfDisjoint (p q : Submodule R' M) (hd : Disjoint p q) :
    (p × q) ≃ₗ[R'] (p ⊔ q : Submodule R' M) :=
  (LinearEquiv.ofInjective (p.subtype.coprod q.subtype) (by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_coprod_of_disjoint_range]
    · simp
    · simpa using hd)).trans (LinearEquiv.ofEq _ _ (Submodule.sup_eq_range p q).symm)

@[simp] theorem coe_prodEquivSupOfDisjoint {p q : Submodule R' M} (hd : Disjoint p q) (z : p × q) :
    ((prodEquivSupOfDisjoint p q hd z : (p ⊔ q : Submodule R' M)) : M) = (z.1 : M) + (z.2 : M) :=
  (rfl)

theorem prodEquivSupOfDisjoint_symm_apply {p q : Submodule R' M} (hd : Disjoint p q)
    (z : p × q) (w : (p ⊔ q : Submodule R' M)) (hw : (w : M) = (z.1 : M) + (z.2 : M)) :
    (prodEquivSupOfDisjoint p q hd).symm w = z := by
  apply (prodEquivSupOfDisjoint p q hd).injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext (by rw [hw, coe_prodEquivSupOfDisjoint])

end Direct

section Join
variable {L G : Type*} [Fintype L] [Group G] {T₁ T₂ : Finset (L → ℂ)}

theorem span_union_eq_sup (T₁ T₂ : Finset (L → ℂ)) :
    Submodule.span ℤ ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ))
      = Submodule.span ℤ (T₁ : Set (L → ℂ)) ⊔ Submodule.span ℤ (T₂ : Set (L → ℂ)) := by
  rw [Finset.coe_union, Submodule.span_union]

noncomputable def joinHom
    (hd : Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))))
    (ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G)
    (ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G) :
    Submodule.span ℤ ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ)) →+ virtualChars G :=
  (ν₁.coprod ν₂).comp
    ((prodEquivSupOfDisjoint _ _ hd).symm.toLinearMap.toAddMonoidHom.comp
      (LinearEquiv.ofEq _ _ (span_union_eq_sup T₁ T₂)).toLinearMap.toAddMonoidHom)

theorem joinHom_apply
    (hd : Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))))
    (ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G)
    (ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G)
    (f : Submodule.span ℤ ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ)))
    (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
    (hf : (f : L → ℂ) = (f₁ : L → ℂ) + (f₂ : L → ℂ)) :
    joinHom hd ν₁ ν₂ f = ν₁ f₁ + ν₂ f₂ := by
  have h := prodEquivSupOfDisjoint_symm_apply hd (f₁, f₂)
    ((LinearEquiv.ofEq _ _ (span_union_eq_sup T₁ T₂)) f) hf
  simp only [joinHom, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_coe, h, AddMonoidHom.coprod_apply]

theorem exists_decomp
    (hd : Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))))
    (ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G)
    (ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G)
    (f : Submodule.span ℤ ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ))) :
    ∃ (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ))),
      (f : L → ℂ) = (f₁ : L → ℂ) + (f₂ : L → ℂ) ∧ joinHom hd ν₁ ν₂ f = ν₁ f₁ + ν₂ f₂ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 ((span_union_eq_sup T₁ T₂).le f.2)
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy.symm, joinHom_apply hd ν₁ ν₂ f ⟨x, hx⟩ ⟨y, hy⟩ hxy.symm⟩

theorem joinHom_apply_left
    (hd : Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))))
    (ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G)
    (ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G)
    (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) :
    joinHom hd ν₁ ν₂ ⟨(f₁ : L → ℂ), (span_union_eq_sup T₁ T₂).ge (Submodule.mem_sup_left f₁.2)⟩
      = ν₁ f₁ := by
  rw [joinHom_apply hd ν₁ ν₂ _ f₁ 0 (by simp), map_zero, add_zero]

theorem joinHom_apply_right
    (hd : Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))))
    (ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G)
    (ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G)
    (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ))) :
    joinHom hd ν₁ ν₂ ⟨(f₂ : L → ℂ), (span_union_eq_sup T₁ T₂).ge (Submodule.mem_sup_right f₂.2)⟩
      = ν₂ f₂ := by
  rw [joinHom_apply hd ν₁ ν₂ _ 0 f₂ (by simp), map_zero, zero_add]

end Join

section Node
variable {L G : Type*} [Group L] [Fintype L] [Group G] [Fintype G]
  {S T T₁ T₂ : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  {τT : charSpanZero (T : Set (L → ℂ)) →+ virtualChars G}
  {ν : Submodule.span ℤ (T : Set (L → ℂ)) →+ virtualChars G}

theorem coe_apply_eq_tau (hν : IsCoherentWith (T : Set (L → ℂ)) τT ν)
    (hτT : ∀ f : charSpanZero (T : Set (L → ℂ)), (τT f : G → ℂ) = tau (f : L → ℂ))
    (g : Submodule.span ℤ (T : Set (L → ℂ))) (hg : (g : L → ℂ) 1 = 0) :
    (ν g : G → ℂ) = tau (g : L → ℂ) := by
  have hmem : (g : L → ℂ) ∈ charSpanZero (T : Set (L → ℂ)) := mem_charSpanZero.2 ⟨g.2, hg⟩
  have h := hν.eq_on_zero ⟨(g : L → ℂ), hmem⟩
  have he : Submodule.inclusion (charSpanZero_le _) (⟨(g : L → ℂ), hmem⟩ :
      charSpanZero (T : Set (L → ℂ))) = g := Subtype.ext rfl
  rw [he] at h
  rw [h, hτT]

theorem exists_int_apply_one (hc : IsSubcoherent S tau R) (hTS : T ⊆ S) {f : L → ℂ}
    (hf : f ∈ Submodule.span ℤ (T : Set (L → ℂ))) : ∃ a : ℤ, f 1 = (a : ℂ) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨d, hd⟩ := (hc.isCharacter x (hTS (Finset.mem_coe.1 hx))).exists_nat_apply_one
      exact ⟨(d : ℤ), by simpa using hd⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      exact ⟨a + b, by push_cast [Pi.add_apply, ha, hb]; ring⟩
  | smul n x _ ih =>
      obtain ⟨a, ha⟩ := ih
      exact ⟨n * a, by push_cast [Pi.smul_apply, zsmul_eq_mul, ha]; ring⟩

variable {τ₁ : charSpanZero (T₁ : Set (L → ℂ)) →+ virtualChars G}
  {ν₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) →+ virtualChars G}
  {τ₂ : charSpanZero (T₂ : Set (L → ℂ)) →+ virtualChars G}
  {ν₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) →+ virtualChars G}

omit [Group L] [Fintype G] in
theorem cfInner_eq_zero_of_mem_span_of_mem_span {A B : Set (L → ℂ)}
    (h : ∀ χ ∈ A, ∀ ψ ∈ B, cfInner χ ψ = 0) {f g : L → ℂ}
    (hf : f ∈ Submodule.span ℤ A) (hg : g ∈ Submodule.span ℤ B) : cfInner f g = 0 := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    induction hf using Submodule.span_induction with
    | mem x hx => exact h x hx y hy
    | zero => rw [cfInner_zero_left]
    | add x₁ x₂ _ _ ih₁ ih₂ => rw [cfInner_add_left, ih₁, ih₂, add_zero]
    | smul a x _ ih =>
      rw [show (a • x : L → ℂ) = (a : ℂ) • x from (Int.cast_smul_eq_zsmul ℂ a x).symm,
        cfInner_smul_left, ih, mul_zero]
  | zero => rw [cfInner_zero_right]
  | add y₁ y₂ _ _ ih₁ ih₂ => rw [cfInner_add_right, ih₁, ih₂, add_zero]
  | smul a y _ ih =>
    rw [show (a • y : L → ℂ) = (a : ℂ) • y from (Int.cast_smul_eq_zsmul ℂ a y).symm,
      cfInner_smul_right, ih, mul_zero]

theorem cfInner_eq_zero_of_mem_span (hc : IsSubcoherent S tau R) (hT₁S : T₁ ⊆ S) (hT₂S : T₂ ⊆ S)
    (hdisj : Disjoint T₁ T₂) {f g : L → ℂ} (hf : f ∈ Submodule.span ℤ (T₁ : Set (L → ℂ)))
    (hg : g ∈ Submodule.span ℤ (T₂ : Set (L → ℂ))) : cfInner f g = 0 := by
  refine cfInner_eq_zero_of_mem_span_of_mem_span (fun χ hχ ψ hψ => ?_) hf hg
  have hne : χ ≠ ψ := fun h =>
    (Finset.disjoint_left.1 hdisj (Finset.mem_coe.1 hχ)) (h ▸ Finset.mem_coe.1 hψ)
  rw [← charInner_eq_cfInner]
  exact hc.charInner_eq_zero χ (hT₁S (Finset.mem_coe.1 hχ)) ψ (hT₂S (Finset.mem_coe.1 hψ)) hne

theorem disjoint_span (hc : IsSubcoherent S tau R) (hT₁S : T₁ ⊆ S) (hT₂S : T₂ ⊆ S)
    (hdisj : Disjoint T₁ T₂) :
    Disjoint (Submodule.span ℤ (T₁ : Set (L → ℂ))) (Submodule.span ℤ (T₂ : Set (L → ℂ))) := by
  rw [Submodule.disjoint_def]
  intro f hf₁ hf₂
  exact cfInner_self_eq_zero.1 (cfInner_eq_zero_of_mem_span hc hT₁S hT₂S hdisj hf₁ hf₂)

theorem cfInner_add_add (hc : IsSubcoherent S tau R)
    (hT₁S : T₁ ⊆ S) (hT₁star : ∀ ψ ∈ T₁, star ψ ∈ T₁)
    (hν₁ : IsCoherentWith (T₁ : Set (L → ℂ)) τ₁ ν₁)
    (hτ₁ : ∀ f : charSpanZero (T₁ : Set (L → ℂ)), (τ₁ f : G → ℂ) = tau (f : L → ℂ))
    (hT₂S : T₂ ⊆ S) (hT₂star : ∀ ψ ∈ T₂, star ψ ∈ T₂)
    (hν₂ : IsCoherentWith (T₂ : Set (L → ℂ)) τ₂ ν₂)
    (hτ₂ : ∀ f : charSpanZero (T₂ : Set (L → ℂ)), (τ₂ f : G → ℂ) = tau (f : L → ℂ))
    (hdisj : Disjoint T₁ T₂)
    (f₁ g₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)))
    (f₂ g₂ : Submodule.span ℤ (T₂ : Set (L → ℂ))) :
    cfInner ((ν₁ f₁ : G → ℂ) + (ν₂ f₂ : G → ℂ)) ((ν₁ g₁ : G → ℂ) + (ν₂ g₂ : G → ℂ))
      = cfInner ((f₁ : L → ℂ) + (f₂ : L → ℂ)) ((g₁ : L → ℂ) + (g₂ : L → ℂ)) := by
  have hcr₁ : cfInner (ν₁ f₁ : G → ℂ) (ν₂ g₂ : G → ℂ) = 0 :=
    cfInner_eq_zero_of_disjoint hc hT₁S hT₁star hν₁ hτ₁ hT₂S hT₂star hν₂ hτ₂ hdisj f₁ g₂
  have hcr₂ : cfInner (ν₂ f₂ : G → ℂ) (ν₁ g₁ : G → ℂ) = 0 := by
    rw [← conj_cfInner,
      cfInner_eq_zero_of_disjoint hc hT₁S hT₁star hν₁ hτ₁ hT₂S hT₂star hν₂ hτ₂ hdisj g₁ f₂,
      map_zero]
  have hl₁ : cfInner (f₁ : L → ℂ) (g₂ : L → ℂ) = 0 :=
    cfInner_eq_zero_of_mem_span hc hT₁S hT₂S hdisj f₁.2 g₂.2
  have hl₂ : cfInner (f₂ : L → ℂ) (g₁ : L → ℂ) = 0 :=
    cfInner_eq_zero_of_mem_span hc hT₂S hT₁S hdisj.symm f₂.2 g₁.2
  rw [cfInner_add_left, cfInner_add_right, cfInner_add_right, hcr₁, hcr₂,
    cfInner_add_left, cfInner_add_right, cfInner_add_right, hl₁, hl₂,
    hν₁.inner_eq, hν₂.inner_eq]

theorem add_eq_tau_of_apply_one_add_eq_zero (hc : IsSubcoherent S tau R)
    (hT₁S : T₁ ⊆ S) (hν₁ : IsCoherentWith (T₁ : Set (L → ℂ)) τ₁ ν₁)
    (hτ₁ : ∀ f : charSpanZero (T₁ : Set (L → ℂ)), (τ₁ f : G → ℂ) = tau (f : L → ℂ))
    (hT₂S : T₂ ⊆ S) (hν₂ : IsCoherentWith (T₂ : Set (L → ℂ)) τ₂ ν₂)
    (hτ₂ : ∀ f : charSpanZero (T₂ : Set (L → ℂ)), (τ₂ f : G → ℂ) = tau (f : L → ℂ))
    {χ : L → ℂ} (hχ : χ ∈ T₁) (φ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
    (hdeg : χ 1 = (φ : L → ℂ) 1)
    (hbridge : tau (χ - (φ : L → ℂ))
      = (ν₁ ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) - (ν₂ φ : G → ℂ))
    (f₁ : Submodule.span ℤ (T₁ : Set (L → ℂ))) (f₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
    (hf1 : (f₁ : L → ℂ) 1 + (f₂ : L → ℂ) 1 = 0) :
    (ν₁ f₁ : G → ℂ) + (ν₂ f₂ : G → ℂ) = tau ((f₁ : L → ℂ) + (f₂ : L → ℂ)) := by
  obtain ⟨dn, hdn, hdeq⟩ :=
    (hc.isCharacter χ (hT₁S hχ)).exists_pos_nat_apply_one (hc.ne_zero χ (hT₁S hχ))
  obtain ⟨a, ha⟩ := exists_int_apply_one hc hT₁S f₁.2
  have hf₂1 : (f₂ : L → ℂ) 1 = -(a : ℂ) := by rw [ha] at hf1; linear_combination hf1
  have hφ1 : (φ : L → ℂ) 1 = (dn : ℂ) := by rw [← hdeg, hdeq]
  set d : ℤ := (dn : ℤ) with hd_def
  have hdne : d ≠ 0 := by simp only [hd_def, ne_eq, Nat.cast_eq_zero]; omega
  have hle₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) ≤ Submodule.span ℤ (S : Set (L → ℂ)) :=
    Submodule.span_mono (Finset.coe_subset.2 hT₁S)
  have hle₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) ≤ Submodule.span ℤ (S : Set (L → ℂ)) :=
    Submodule.span_mono (Finset.coe_subset.2 hT₂S)
  set g₁ : Submodule.span ℤ (T₁ : Set (L → ℂ)) :=
    d • f₁ - a • (⟨χ, mem_span_of_mem hχ⟩ : Submodule.span ℤ (T₁ : Set (L → ℂ))) with hg₁
  set g₂ : Submodule.span ℤ (T₂ : Set (L → ℂ)) := d • f₂ + a • φ with hg₂
  have hg₁c : (g₁ : L → ℂ) = d • (f₁ : L → ℂ) - a • χ := by simp [hg₁]
  have hg₂c : (g₂ : L → ℂ) = d • (f₂ : L → ℂ) + a • (φ : L → ℂ) := by simp [hg₂]
  have hg₁1 : (g₁ : L → ℂ) 1 = 0 := by
    rw [hg₁c, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, ha, hdeq]
    simp only [zsmul_eq_mul, hd_def]
    push_cast
    ring
  have hg₂1 : (g₂ : L → ℂ) 1 = 0 := by
    rw [hg₂c, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hf₂1, hφ1]
    simp only [zsmul_eq_mul, hd_def]
    push_cast
    ring
  have hm₁ : (g₁ : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne.2 ⟨hle₁ g₁.2, hg₁1⟩
  have hm₂ : (g₂ : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne.2 ⟨hle₂ g₂.2, hg₂1⟩
  have hbr : χ - (φ : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne.2 ⟨Submodule.sub_mem _ (hle₁ (mem_span_of_mem hχ)) (hle₂ φ.2), by
      simp [Pi.sub_apply, hdeg]⟩
  have hbra : a • (χ - (φ : L → ℂ)) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    Submodule.smul_mem _ a hbr
  have hsum : (f₁ : L → ℂ) + (f₂ : L → ℂ) ∈ intSpanZeroAtOne (S : Set (L → ℂ)) :=
    mem_intSpanZeroAtOne.2 ⟨Submodule.add_mem _ (hle₁ f₁.2) (hle₂ f₂.2), by
      simpa [Pi.add_apply] using hf1⟩
  have hkey : d • ((f₁ : L → ℂ) + (f₂ : L → ℂ))
      = (g₁ : L → ℂ) + (g₂ : L → ℂ) + a • (χ - (φ : L → ℂ)) := by
    rw [hg₁c, hg₂c]; module
  have htau : tau (d • ((f₁ : L → ℂ) + (f₂ : L → ℂ)))
      = tau (g₁ : L → ℂ) + tau (g₂ : L → ℂ) + tau (a • (χ - (φ : L → ℂ))) := by
    rw [hkey, hc.map_add _ (Submodule.add_mem _ hm₁ hm₂) _ hbra, hc.map_add _ hm₁ _ hm₂]
  rw [hc.map_zsmul d hsum, hc.map_zsmul a hbr, hbridge,
    ← coe_apply_eq_tau hν₁ hτ₁ g₁ hg₁1, ← coe_apply_eq_tau hν₂ hτ₂ g₂ hg₂1] at htau
  have he₁ : (ν₁ g₁ : G → ℂ)
      = d • (ν₁ f₁ : G → ℂ) - a • (ν₁ ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) := by
    rw [hg₁, map_sub, map_zsmul, map_zsmul]; simp
  have he₂ : (ν₂ g₂ : G → ℂ) = d • (ν₂ f₂ : G → ℂ) + a • (ν₂ φ : G → ℂ) := by
    rw [hg₂, map_add, map_zsmul, map_zsmul]; simp
  rw [he₁, he₂] at htau
  have hfin : d • tau ((f₁ : L → ℂ) + (f₂ : L → ℂ))
      = d • ((ν₁ f₁ : G → ℂ) + (ν₂ f₂ : G → ℂ)) := by
    rw [htau]; module
  exact (smul_right_injective (G → ℂ) hdne hfin).symm

variable {τU : charSpanZero ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ)) →+ virtualChars G}

theorem isCoherentWith_joinHom (hc : IsSubcoherent S tau R)
    (hT₁S : T₁ ⊆ S) (hT₁star : ∀ ψ ∈ T₁, star ψ ∈ T₁) (_hT₁ne : T₁.Nonempty)
    (hν₁ : IsCoherentWith (T₁ : Set (L → ℂ)) τ₁ ν₁)
    (hτ₁ : ∀ f : charSpanZero (T₁ : Set (L → ℂ)), (τ₁ f : G → ℂ) = tau (f : L → ℂ))
    (hT₂S : T₂ ⊆ S) (hT₂star : ∀ ψ ∈ T₂, star ψ ∈ T₂) (_hT₂ne : T₂.Nonempty)
    (hν₂ : IsCoherentWith (T₂ : Set (L → ℂ)) τ₂ ν₂)
    (hτ₂ : ∀ f : charSpanZero (T₂ : Set (L → ℂ)), (τ₂ f : G → ℂ) = tau (f : L → ℂ))
    (hdisj : Disjoint T₁ T₂)
    (hτU : ∀ f : charSpanZero ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ)),
      (τU f : G → ℂ) = tau (f : L → ℂ))
    {χ : L → ℂ} (hχ : χ ∈ T₁) (φ : Submodule.span ℤ (T₂ : Set (L → ℂ)))
    (hdeg : χ 1 = (φ : L → ℂ) 1)
    (hbridge : tau (χ - (φ : L → ℂ))
      = (ν₁ ⟨χ, mem_span_of_mem hχ⟩ : G → ℂ) - (ν₂ φ : G → ℂ)) :
    IsCoherentWith ((T₁ ∪ T₂ : Finset (L → ℂ)) : Set (L → ℂ)) τU
      (joinHom (disjoint_span hc hT₁S hT₂S hdisj) ν₁ ν₂) := by
  set hd := disjoint_span hc hT₁S hT₂S hdisj with hd_def
  constructor
  · intro f g
    obtain ⟨f₁, f₂, hfsum, hfj⟩ := exists_decomp hd ν₁ ν₂ f
    obtain ⟨g₁, g₂, hgsum, hgj⟩ := exists_decomp hd ν₁ ν₂ g
    rw [hfj, hgj, hfsum, hgsum, Submodule.coe_add, Submodule.coe_add]
    exact cfInner_add_add hc hT₁S hT₁star hν₁ hτ₁ hT₂S hT₂star hν₂ hτ₂ hdisj f₁ g₁ f₂ g₂
  · intro f
    obtain ⟨f₁, f₂, hfsum, hfj⟩ :=
      exists_decomp hd ν₁ ν₂ (Submodule.inclusion (charSpanZero_le _) f)
    refine Subtype.ext ?_
    have hf1 : (f₁ : L → ℂ) 1 + (f₂ : L → ℂ) 1 = 0 := by
      have hz := charSpanZero_apply_one f
      rw [show (f : L → ℂ) = (f₁ : L → ℂ) + (f₂ : L → ℂ) from hfsum] at hz
      simpa [Pi.add_apply] using hz
    rw [hfj, hτU, Submodule.coe_add,
      add_eq_tau_of_apply_one_add_eq_zero hc hT₁S hν₁ hτ₁ hT₂S hν₂ hτ₂ hχ φ hdeg hbridge
        f₁ f₂ hf1, ← hfsum]
    rfl

end Node

end CoherentJoin

end CFSG.FeitThompson

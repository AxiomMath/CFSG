module

public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W₁ : Subgroup G}

omit [Finite G] in
theorem closure_frame_eq_top' {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    Subgroup.closure ({T7D.imgQ F.ρ, T7D.imgQ F.ρ', T7D.imgQ F.ρ₃} :
      Set ↥(muGroup Ω W₁)) = ⊤ := by
  have hmemS : ∀ ρ : Thompson.Rep Ω W₁, e (T7D.imgQ ρ) ∈ S4.swaps4 := fun ρ =>
    S4.mem_swaps4_of_isSwap ((he _).mp (T7D.imgQ_mem ρ))
  set a := e (T7D.imgQ F.ρ)
  set b := e (T7D.imgQ F.ρ')
  set c := e (T7D.imgQ F.ρ₃)
  have hab' : a ≠ b := fun h => hab (e.injective h)
  have hcomm' : a * b = b * a := by
    simp only [a, b, ← map_mul, hcomm]
  have hac' : a * c ≠ c * a := by
    intro h
    apply hac
    apply e.injective
    simpa only [a, c, map_mul] using h
  have htop : Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) = ⊤ := by
    rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
    intro t ht
    have ht' := S4.mem_swaps4_of_isSwap ht
    have hmem : ∀ x ∈ ({a, b, c} : Set (Equiv.Perm (Fin 4))),
        x ∈ Subgroup.closure ({a, b, c} : Set (Equiv.Perm (Fin 4))) :=
      fun x hx => Subgroup.subset_closure hx
    have ha := hmem a (by simp)
    have hb := hmem b (by simp)
    have hc := hmem c (by simp)
    rcases S4.swap_word a (hmemS _) b (hmemS _) c (hmemS _) hab' hcomm' hac' t ht' with
        h | h | h | h | h | h <;> rw [h]
    · exact ha
    · exact hb
    · exact hc
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hc) ha
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hc) hb
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ ha hb) hc) hb) ha
  have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) htop
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
  rw [← hmap]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨a, Or.inl rfl, by simp [a]⟩
    · exact ⟨b, Or.inr (Or.inl rfl), by simp [b]⟩
    · exact ⟨c, Or.inr (Or.inr rfl), by simp [c]⟩
  · rintro ⟨y, hy | hy | hy, rfl⟩ <;> subst hy <;> simp [a, b, c]

theorem exists_conj_of_frame (c : Thompson.Ctx p f Ω W₁)
    {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {H₀ : Subgroup G}
    (hr : F.ρ.r ∈ H₀) (hr' : F.ρ'.r ∈ H₀) (hs : F.ρ₃.r ∈ H₀) (σ : Thompson.Rep Ω W₁) :
    ∃ h ∈ H₀, conjSub h F.ρ.K = σ.K := by
  let Y : Subgroup ↥(muGroup Ω W₁) :=
    { carrier := {y | ∃ h ∈ H₀ ⊓ Subgroup.normalizer (W₁ : Set G),
        (y : NQuot (W₁ ⊔ OCW W₁)) = Thompson.piG W₁ h}
      one_mem' := ⟨1, ⟨H₀.one_mem, Subgroup.one_mem _⟩,
        (Thompson.piG_of_mem_sup (Subgroup.one_mem _)).symm⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁, hh₁, e₁⟩ ⟨h₂, hh₂, e₂⟩
        refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
        rw [Subgroup.coe_mul, e₁, e₂, Thompson.piG_mul hh₁.2 hh₂.2]
      inv_mem' := by
        rintro y ⟨h, hh, e₁⟩
        refine ⟨h⁻¹, Subgroup.inv_mem _ hh, ?_⟩
        rw [Subgroup.coe_inv, e₁, Thompson.piG_inv hh.2] }
  have hgen : ∀ ρ : Thompson.Rep Ω W₁, ρ.r ∈ H₀ → T7D.imgQ ρ ∈ Y := fun ρ hρ =>
    ⟨ρ.r, ⟨hρ, ρ.r_mem_normalizer⟩, rfl⟩
  have hle : Subgroup.closure ({T7D.imgQ F.ρ, T7D.imgQ F.ρ', T7D.imgQ F.ρ₃} :
      Set ↥(muGroup Ω W₁)) ≤ Y := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with h | h | h <;> rw [h]
    exacts [hgen _ hr, hgen _ hr', hgen _ hs]
  obtain ⟨y, hy⟩ := S4.exists_conj_of_mem he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem σ)
  have hyY : y ∈ Y :=
    hle (by rw [closure_frame_eq_top' he F hab hcomm hac]; exact Subgroup.mem_top y)
  obtain ⟨h, hh, hyh⟩ := hyY
  have himg : Thompson.piG W₁ h * F.ρ.img * (Thompson.piG W₁ h)⁻¹ = σ.img := by
    rw [← hyh]
    exact congrArg Subtype.val hy
  exact ⟨h, hh.1, c.K_eq_of_img_eq (T7D.conjRep c.hΩ hh.2 F.ρ) σ (by rw [T7D.conjRep_img, himg])⟩

end S24B

end CFSG.ClassicalInvolution.Asc77

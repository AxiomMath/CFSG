module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.GroupTheory.ABGDGroups.LinearStructure

public section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.GorensteinWalter

theorem fourgroup_inf_pslRange_ne_bot {F : Type} [Field F] [Finite F] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    {E : Subgroup (PGammaL2 F)} (hE4 : Nat.card E = 4) (hE2 : ∀ x ∈ E, x * x = 1) :
    E ⊓ pGammaL2PSLRange F ≠ ⊥ := by
  classical
  intro hbot
  have hodd := AutL2Facts.isOddPrimePower_of hp hp2 hf hF
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hE2 _ (mul_mem ha hb))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hE2 b hb), inv_eq_of_mul_eq_one_right (hE2 a ha)]
  have hone : ∀ a ∈ E, a ∈ pGammaL2PSLRange F → a = 1 := fun a ha hPSL => by
    have h1 : a ∈ E ⊓ pGammaL2PSLRange F := mem_inf.mpr ⟨ha, hPSL⟩
    rwa [hbot, mem_bot] at h1
  have hinl : ∀ a : PGammaL2 F, a.right = 1 → a = SemidirectProduct.inl a.left := fun a ha => by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right a]
    rw [ha, map_one, mul_one]
  by_cases hright : ∃ b ∈ E, b.right ≠ 1
  · obtain ⟨b, hb, hbr⟩ := hright
    set π : PGammaL2 F →* (F ≃+* F) := SemidirectProduct.rightHom with hπ
    have hπE : Nat.card (E.map π) ≤ 2 := by
      have : IsCyclic (F ≃+* F) := AutL2Facts.isCyclic_ringAut F
      have hexp : Monoid.exponent (E.map π) ∣ 2 := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
        obtain ⟨x, hx, hxσ⟩ := mem_map.mp σ.2
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, ← hxσ, ← map_pow, sq, hE2 x hx, map_one, OneMemClass.coe_one]
      rw [← IsCyclic.exponent_eq_card]
      exact Nat.le_of_dvd two_pos hexp
    set φ : ↥E →* (F ≃+* F) := π.comp E.subtype with hφ
    have h1 := Subgroup.card_ker_mul_card_range φ
    have hrange : φ.range = E.map π := by rw [hφ, MonoidHom.range_comp, range_subtype]
    rw [hrange, hE4] at h1
    have hker : φ.ker ≠ ⊥ := by
      intro h2
      rw [h2, card_bot, one_mul] at h1
      omega
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hker
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxr : ((x : E) : PGammaL2 F).right = 1 := by
      have h3 := MonoidHom.mem_ker.mp hx
      rwa [hφ, MonoidHom.comp_apply, hπ, SemidirectProduct.rightHom_eq_right] at h3
    have hxe := hinl _ hxr
    have hmem := AutL2Facts.mem_pslRange_of_commute_fieldInv hp hp2 hF b (hE2 b hb) hbr
      ((x : E) : PGammaL2 F).left (by rw [← hxe]; exact hcomm b hb _ (x : E).2)
    rw [← hxe] at hmem
    exact hx1' (Subtype.ext (hone _ (x : E).2 hmem))
  ·
    push Not at hright
    have hdet : ∀ a ∈ E, a ≠ 1 → ABGDGroups.pGammaL2DetClass F hodd a ≠ 1 := by
      intro a ha ha1 hd
      apply ha1
      refine hone a ha ?_
      rw [ABGDGroups.pGammaL2PSLRange_eq_inf_ker hodd, mem_inf, MonoidHom.mem_ker]
      refine ⟨?_, hd⟩
      rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_eq_right, hright a ha]
    obtain ⟨a₀, ha₀, ha₀1⟩ : ∃ a ∈ E, a ≠ 1 := by
      by_contra h
      push Not at h
      have h2 : E = ⊥ := eq_bot_iff.mpr fun a ha => mem_bot.mpr (h a ha)
      rw [h2, card_bot] at hE4
      omega
    have hsub : ∀ a ∈ E, a ∈ ({1, a₀} : Finset (PGammaL2 F)) := by
      intro a ha
      by_cases ha1 : a = 1
      · rw [ha1]
        exact Finset.mem_insert_self _ _
      · have h3 := ABGDGroups.squareClass_eq_of_ne_one hodd (hdet a ha ha1) (hdet a₀ ha₀ ha₀1)
        have h4 : a * a₀⁻¹ = 1 := by
          by_contra h5
          apply hdet _ (mul_mem ha (inv_mem ha₀)) h5
          rw [map_mul, map_inv, h3, mul_inv_cancel]
        rw [mul_inv_eq_one.mp h4]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have h5 := SmallLocal.card_le_of_forall_mem_finset _ hsub
    have h6 : ({1, a₀} : Finset (PGammaL2 F)).card ≤ 2 := Finset.card_le_two
    omega

theorem fourgroup_inf_innAut_ne_bot_alt7 {𝕊 : Type} [Group 𝕊]
    (e : 𝕊 ≃* alternatingGroup (Fin 7)) {V : Subgroup (MulAut 𝕊)} (hV4 : Nat.card V = 4) :
    V ⊓ innAut5 𝕊 ≠ ⊥ := by
  classical
  intro hbot
  set c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7)) with hc
  have hcb : Function.Bijective c :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num)
      (by norm_num)
  set θ : Equiv.Perm (Fin 7) →* MulAut 𝕊 := (MulAut.congr e.symm).toMonoidHom.comp c with hθ
  have hθb : Function.Bijective θ := (MulAut.congr e.symm).bijective.comp hcb
  set W := V.comap θ with hW
  have hWcard : Nat.card W = 4 := by
    rw [← hV4]
    exact Nat.card_congr ((Equiv.ofBijective θ hθb).subtypeEquiv fun σ => Iff.rfl)
  have heven : ∀ σ ∈ W, Equiv.Perm.sign σ = 1 → σ = 1 := by
    intro σ hσW hσ
    have hσA : σ ∈ alternatingGroup (Fin 7) := Equiv.Perm.mem_alternatingGroup.mpr hσ
    have hθσ : θ σ = MulAut.conj (e.symm ⟨σ, hσA⟩) := by
      ext y
      rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulAut.conj_apply]
      simp only [MulEquiv.trans_apply, MulEquiv.symm_symm]
      apply e.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [hc, MulAut.conjNormal_apply]
      simp
    have h1 : θ σ ∈ V ⊓ innAut5 𝕊 := mem_inf.mpr ⟨hσW, by rw [hθσ]; exact ⟨_, rfl⟩⟩
    rw [hbot, mem_bot] at h1
    exact hθb.1 (by rw [h1, map_one])
  obtain ⟨σ₀, hσ₀, hσ₀1⟩ : ∃ σ ∈ W, σ ≠ 1 := by
    by_contra h
    push Not at h
    have h2 : W = ⊥ := eq_bot_iff.mpr fun σ hσ => mem_bot.mpr (h σ hσ)
    rw [h2, card_bot] at hWcard
    omega
  have hneg : ∀ σ ∈ W, σ ≠ 1 → Equiv.Perm.sign σ = -1 := fun σ hσ hσ1 =>
    (Int.units_eq_one_or _).resolve_left fun h1 => hσ1 (heven σ hσ h1)
  have hsub : ∀ σ ∈ W, σ ∈ ({1, σ₀} : Finset (Equiv.Perm (Fin 7))) := by
    intro σ hσ
    by_cases hσ1 : σ = 1
    · rw [hσ1]
      exact Finset.mem_insert_self _ _
    · have h3 : σ * σ₀⁻¹ = 1 := heven _ (mul_mem hσ (inv_mem hσ₀)) (by
        rw [map_mul, map_inv, hneg σ hσ hσ1, hneg σ₀ hσ₀ hσ₀1]
        decide)
      rw [mul_inv_eq_one.mp h3]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have h5 := SmallLocal.card_le_of_forall_mem_finset _ hsub
  have h6 : ({1, σ₀} : Finset (Equiv.Perm (Fin 7))).card ≤ 2 := Finset.card_le_two
  omega

theorem fourgroup_inf_innAut_ne_bot {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (h𝕊 : FooteSimpleType 𝕊)
    {V : Subgroup (MulAut 𝕊)} (hV4 : Nat.card V = 4) (hV2 : ∀ α ∈ V, α * α = 1) :
    V ⊓ innAut5 𝕊 ≠ ⊥ := by
  rcases h𝕊 with ⟨⟨e⟩⟩ | ⟨p, f, hp, hp2, hf, -, hL⟩
  · exact fourgroup_inf_innAut_ne_bot_alt7 e hV4
  · obtain ⟨-, -, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hL
    intro hbot
    set ψ := AutL2Facts.autEquiv e with hψ
    set E := V.map ψ.toMonoidHom with hE
    have hE4 : Nat.card E = 4 := by
      rw [hE, card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, hV4]
    have hE2 : ∀ x ∈ E, x * x = 1 := by
      rintro _ ⟨α, hα, rfl⟩
      rw [← map_mul, hV2 α hα, map_one]
    apply fourgroup_inf_pslRange_ne_bot hp hp2 hf hF hE4 hE2
    rw [hE, ← AutL2Facts.map_autEquiv_innAut e, ← hψ,
      ← map_inf_eq _ _ ψ.toMonoidHom ψ.injective, hbot, Subgroup.map_bot]

end CFSG.ComponentClassification.Foote5

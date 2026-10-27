module

import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81RankOneCentAltTen
import CFSG.Quasithin.Background.A312SporAlt5
import CFSG.LocalAnalysis.EvenBN.Common.Diagonal
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

open CFSG.Open Subgroup Equiv

theorem nonempty_mulEquiv_alt5_of_two_perm {J : Type*} [Group J] [Nontrivial J]
    (hJ : commutator J = ⊤) (ρ₁ ρ₂ : J →* Perm (Fin 5)) (hker : ρ₁.ker ⊓ ρ₂.ker = ⊥)
    (hirr : ∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) :
    Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have himg : ∀ ρ : J →* Perm (Fin 5), ρ.range = ⊥ ∨ ρ.range = alternatingGroup (Fin 5) := by
    intro ρ
    by_cases h : ρ.range = ⊥
    · exact Or.inl h
    · refine Or.inr (CFSG.Quasithin.A312S.eq_alt5_of_perfect ?_ h)
      rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def, hJ]
  have hinj : ∀ ρ : J →* Perm (Fin 5), ρ.ker = ⊥ → Nonempty (J ≃* alternatingGroup (Fin 5)) := by
    intro ρ hρ
    have hi : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hρ
    rcases himg ρ with h | h
    · exfalso
      obtain ⟨x, hx⟩ := exists_ne (1 : J)
      apply hx
      apply hi
      have : ρ x ∈ ρ.range := ⟨x, rfl⟩
      rw [h, mem_bot] at this
      rw [this, map_one]
    · exact ⟨(MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr h)⟩
  have key : ∀ ρ σ : J →* Perm (Fin 5), ρ.ker ⊓ σ.ker = ⊥ →
      ρ.range = alternatingGroup (Fin 5) → ρ.ker = ⊥ ∨ σ.ker = ⊥ := by
    intro ρ σ hρσ hρ
    by_cases hk : ρ.ker = ⊥
    · exact Or.inl hk
    right
    set ρ' : J →* alternatingGroup (Fin 5) :=
      ρ.codRestrict _ (fun x => hρ ▸ ⟨x, rfl⟩) with hρ'
    have hρ's : Function.Surjective ρ' := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (show y ∈ ρ.range from hρ ▸ hy)
      exact ⟨x, Subtype.ext hx⟩
    have hker' : ρ'.ker = ρ.ker := by
      ext x
      simp [hρ', MonoidHom.mem_ker, ← Subtype.val_inj]
    haveI : (σ.ker.map ρ').Normal := σ.normal_ker.map ρ' hρ's
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (σ.ker.map ρ') with h | h
    ·
      have hle : σ.ker ≤ ρ.ker := by
        rw [← hker']
        exact (Subgroup.map_eq_bot_iff _).mp h
      exact (inf_eq_right.mpr hle).symm.trans hρσ
    ·
      exfalso
      have hsup : σ.ker ⊔ ρ.ker = ⊤ := by
        rw [eq_top_iff]
        intro x _
        obtain ⟨k, hk, hkx⟩ := (show ρ' x ∈ σ.ker.map ρ' from h ▸ mem_top _)
        have hm : k⁻¹ * x ∈ ρ.ker := by
          rw [← hker', MonoidHom.mem_ker, map_mul, map_inv, hkx, inv_mul_cancel]
        have := mul_mem_sup hk hm
        rwa [mul_inv_cancel_left] at this
      rcases hirr σ.ker ρ.ker σ.normal_ker ρ.normal_ker hsup with h1 | h1
      · apply hk
        rw [← inf_top_eq ρ.ker, ← h1, hρσ]
      · have : ρ.range = ⊥ := by
          rw [MonoidHom.range_eq_map, eq_bot_iff]
          rintro _ ⟨x, -, rfl⟩
          exact (MonoidHom.mem_ker).mp (h1 ▸ mem_top x)
        rw [this] at hρ
        obtain ⟨a, b, hab⟩ := exists_pair_ne (alternatingGroup (Fin 5))
        have ha : (a : Perm (Fin 5)) ∈ (⊥ : Subgroup (Perm (Fin 5))) := by
          rw [hρ]; exact a.2
        have hb : (b : Perm (Fin 5)) ∈ (⊥ : Subgroup (Perm (Fin 5))) := by
          rw [hρ]; exact b.2
        exact hab (Subtype.ext ((mem_bot.mp ha).trans (mem_bot.mp hb).symm))
  rcases himg ρ₁ with h1 | h1
  ·
    have hk1 : ρ₁.ker = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have : ρ₁ x ∈ ρ₁.range := ⟨x, rfl⟩
      rw [h1, mem_bot] at this
      exact this
    exact hinj ρ₂ (by rw [← top_inf_eq ρ₂.ker, ← hk1, hker])
  · rcases key ρ₁ ρ₂ hker h1 with h | h
    · exact hinj ρ₁ h
    · exact hinj ρ₂ h

section AltTen

variable {B : Finset (Fin 10)}

private theorem pres_or_swap (hB : B.card = 5) {σ : Perm (Fin 10)}
    (h : (∀ i ∈ B, σ i ∈ B) ∨ (∀ i ∈ B, σ i ∉ B)) :
    (∀ x, σ x ∈ B ↔ x ∈ B) ∨ (∀ x, σ x ∈ B ↔ x ∉ B) := by
  rcases h with h | h
  · left
    have himg : B.image σ = B := Finset.eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact h x hx)
      (by rw [Finset.card_image_of_injective _ σ.injective])
    intro x
    refine ⟨fun hx => ?_, h x⟩
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp (himg.symm ▸ hx : σ x ∈ B.image σ)
    exact σ.injective hyx ▸ hy
  · right
    have hc : Bᶜ.card = 5 := by rw [Finset.card_compl, hB]; rfl
    have himg : B.image σ = Bᶜ := Finset.eq_of_subset_of_card_le
      (fun y hy => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_compl.mpr (h x hx))
      (by rw [Finset.card_image_of_injective _ σ.injective, hc, hB])
    intro x
    refine ⟨fun hx hxB => h x hxB hx, fun hxB => ?_⟩
    by_contra hσx
    obtain ⟨y, hy, hyx⟩ :=
      Finset.mem_image.mp (himg.symm ▸ Finset.mem_compl.mpr hσx : σ x ∈ B.image σ)
    exact hxB (σ.injective hyx ▸ hy)

private theorem inv_pres {σ : Perm (Fin 10)} (h : ∀ x, σ x ∈ B ↔ x ∈ B) :
    ∀ x, σ⁻¹ x ∈ B ↔ x ∈ B := by
  intro x
  have := h (σ⁻¹ x)
  rw [show σ (σ⁻¹ x) = x by simp] at this
  exact this.symm

private theorem inv_swap {σ : Perm (Fin 10)} (h : ∀ x, σ x ∈ B ↔ x ∉ B) :
    ∀ x, σ⁻¹ x ∈ B ↔ x ∉ B := by
  intro x
  have := h (σ⁻¹ x)
  rw [show σ (σ⁻¹ x) = x by simp] at this
  tauto

private theorem comm_pres {σ τ : Perm (Fin 10)}
    (hσ : (∀ x, σ x ∈ B ↔ x ∈ B) ∨ (∀ x, σ x ∈ B ↔ x ∉ B))
    (hτ : (∀ x, τ x ∈ B ↔ x ∈ B) ∨ (∀ x, τ x ∈ B ↔ x ∉ B)) :
    ∀ x, (σ * τ * σ⁻¹ * τ⁻¹) x ∈ B ↔ x ∈ B := by
  intro x
  rcases hσ with h1 | h1 <;> rcases hτ with h2 | h2
  · simp only [Perm.mul_apply, h1, h2, inv_pres h1, inv_pres h2]
  · simp only [Perm.mul_apply, h1, h2, inv_pres h1, inv_swap h2, not_not]
  · simp only [Perm.mul_apply, h1, h2, inv_swap h1, inv_pres h2, not_not]
  · simp only [Perm.mul_apply, h1, h2, inv_swap h1, inv_swap h2, not_not]

private def restrictHom {J : Type*} [Group J] (ρ : J →* Perm (Fin 10)) (C : Finset (Fin 10))
    (h : ∀ j : J, ∀ x, ρ j x ∈ C ↔ x ∈ C) : J →* Perm C where
  toFun j := (ρ j).subtypePerm (h j)
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp only [map_mul]
    rfl

private theorem restrictHom_apply {J : Type*} [Group J] (ρ : J →* Perm (Fin 10))
    (C : Finset (Fin 10)) (h : ∀ j : J, ∀ x, ρ j x ∈ C ↔ x ∈ C) (j : J) (x : C) :
    ((restrictHom ρ C h j x : C) : Fin 10) = ρ j x :=
  rfl

theorem nonempty_mulEquiv_alt5_of_altTen {K : Type} [Group K] [Finite K]
    (e : K ≃* alternatingGroup (Fin 10)) (T : Sylow 5 K) {K₁ J : Subgroup K}
    (hNT : normalizer ((T : Subgroup K) : Set K) ≤ K₁) (hK₁ : K₁ ≠ ⊤) (hJK : J ≤ K₁)
    (hJp : ⁅J, J⁆ = J) (hJ1 : J ≠ ⊥)
    (hirr : ∀ N₁ N₂ : Subgroup J, N₁.Normal → N₂.Normal → N₁ ⊔ N₂ = ⊤ → N₁ = ⊤ ∨ N₂ = ⊤) :
    Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hes : Function.Surjective e.toMonoidHom := by
    rw [MulEquiv.coe_toMonoidHom]
    exact e.surjective
  set S : Sylow 5 (alternatingGroup (Fin 10)) := T.mapSurjective hes with hS
  obtain ⟨B, hB, -, -, hY⟩ := RankOneCent.kFactAltTenOvergroup_holds S
  set Y := K₁.map e.toMonoidHom with hYdef
  have hNY : normalizer ((S : Subgroup (alternatingGroup (Fin 10))) : Set _) ≤ Y := by
    rw [show (S : Subgroup (alternatingGroup (Fin 10))) = (T : Subgroup K).map e.toMonoidHom
      from rfl, ← map_equiv_normalizer_eq]
    exact map_mono hNT
  have hYt : Y ≠ ⊤ := fun h => hK₁ (by
    have := congrArg (Subgroup.comap e.toMonoidHom) h
    rwa [hYdef, comap_map_eq_self_of_injective e.injective, comap_top] at this)
  have hK₁B : ∀ k ∈ K₁, (∀ x, (e k : Perm (Fin 10)) x ∈ B ↔ x ∈ B) ∨
      (∀ x, (e k : Perm (Fin 10)) x ∈ B ↔ x ∉ B) := fun k hk =>
    pres_or_swap hB (hY Y hNY hYt (e k) ⟨k, hk, rfl⟩)
  set St : Subgroup K :=
    { carrier := {k | ∀ x, (e k : Perm (Fin 10)) x ∈ B ↔ x ∈ B}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb x => by
        simp only [Set.mem_setOf_eq, map_mul, Subgroup.coe_mul, Perm.mul_apply] at ha hb ⊢
        rw [ha, hb]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, map_inv, Subgroup.coe_inv] at ha ⊢
        exact inv_pres ha } with hSt
  have hJSt : J ≤ St := by
    rw [← hJp, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    intro x
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact comm_pres (hK₁B a (hJK ha)) (hK₁B b (hJK hb)) x
  set ρ : J →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp
    (e.toMonoidHom.comp J.subtype) with hρ
  have hρB : ∀ j : J, ∀ x, ρ j x ∈ B ↔ x ∈ B := fun j => hJSt j.2
  have hρBc : ∀ j : J, ∀ x, ρ j x ∈ Bᶜ ↔ x ∈ Bᶜ := fun j x => by
    simp only [Finset.mem_compl]
    exact not_congr (hρB j x)
  have hcB : Fintype.card B = 5 := by rw [Fintype.card_coe, hB]
  have hcBc : Fintype.card (Bᶜ : Finset (Fin 10)) = 5 := by
    rw [Fintype.card_coe, Finset.card_compl, hB]; rfl
  set ρ₁ : J →* Perm (Fin 5) := ((Fintype.equivFinOfCardEq hcB).permCongrHom).toMonoidHom.comp
    (restrictHom ρ B hρB) with hρ₁
  set ρ₂ : J →* Perm (Fin 5) := ((Fintype.equivFinOfCardEq hcBc).permCongrHom).toMonoidHom.comp
    (restrictHom ρ Bᶜ hρBc) with hρ₂
  have hker : ρ₁.ker ⊓ ρ₂.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro j ⟨h1, h2⟩
    have h1' : restrictHom ρ B hρB j = 1 := by
      apply (Fintype.equivFinOfCardEq hcB).permCongrHom.injective
      rw [map_one]
      exact h1
    have h2' : restrictHom ρ Bᶜ hρBc j = 1 := by
      apply (Fintype.equivFinOfCardEq hcBc).permCongrHom.injective
      rw [map_one]
      exact h2
    have hρ1 : ρ j = 1 := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x ∈ B
      · have := congrArg Subtype.val (DFunLike.congr_fun h1' ⟨x, hx⟩)
        rw [restrictHom_apply] at this
        simpa using this
      · have := congrArg Subtype.val
          (DFunLike.congr_fun h2' ⟨x, Finset.mem_compl.mpr hx⟩)
        rw [restrictHom_apply] at this
        simpa using this
    rw [mem_bot]
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    simpa [hρ] using hρ1
  haveI : Group.IsPerfect J :=
    (CFSG.LocalAnalysis.EvenBN.Common.isPerfect_subgroup_iff_commutator_eq J).mpr hJp
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hJ1
  exact nonempty_mulEquiv_alt5_of_two_perm
    (inferInstance : Group.IsPerfect J).commutator_eq_top ρ₁ ρ₂ hker hirr

end AltTen

end CFSG.LocalAnalysis.RankThreeTheoremC.TenFourteenTwo

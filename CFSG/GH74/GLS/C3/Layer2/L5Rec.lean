module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Subgroup

section Aut

variable {E : Type*} [Group E]

theorem closure_eq_top [Finite E] (hE : Nat.card E = 8) (hsq : ∀ e : E, e * e = 1) (v e₁ e₂ : E)
    (hv : v ≠ 1) (he₁ : e₁ ≠ 1 ∧ e₁ ≠ v) (he₂ : e₂ ≠ 1 ∧ e₂ ≠ v ∧ e₂ ≠ e₁ ∧ e₂ ≠ e₁ * v) :
    Subgroup.closure ({v, e₁, e₂} : Set E) = ⊤ := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hinv : ∀ e : E, e⁻¹ = e := fun e => inv_eq_of_mul_eq_one_right (hsq e)
  set H := Subgroup.closure ({v, e₁, e₂} : Set E) with hH
  have hv' : v ∈ H := Subgroup.subset_closure (by simp)
  have he₁' : e₁ ∈ H := Subgroup.subset_closure (by simp)
  have he₂' : e₂ ∈ H := Subgroup.subset_closure (by simp)
  have hne1v : e₁ * v ≠ 1 := fun h => he₁.2 (by
    have := eq_inv_of_mul_eq_one_left h
    rwa [hinv] at this)
  have hnev : e₁ * v ≠ v := fun h => he₁.1 (by simpa using h)
  have hne1 : e₁ * v ≠ e₁ := fun h => hv (by simpa using h)
  have h1 : (1 : E) ∉ ({v, e₁, e₁ * v, e₂} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hv.symm, he₁.1.symm, hne1v.symm, he₂.1.symm⟩
  have h2 : v ∉ ({e₁, e₁ * v, e₂} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨he₁.2.symm, hnev.symm, he₂.2.1.symm⟩
  have h3 : e₁ ∉ ({e₁ * v, e₂} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne1.symm, he₂.2.2.1.symm⟩
  have h4 : e₁ * v ∉ ({e₂} : Finset E) := by
    simp only [Finset.mem_singleton]
    exact he₂.2.2.2.symm
  have hc5 : ({1, v, e₁, e₁ * v, e₂} : Finset E).card = 5 := by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_insert_of_notMem h4, Finset.card_singleton]
  have hsub : ({1, v, e₁, e₁ * v, e₂} : Finset E) ⊆ (H : Set E).toFinset := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · simp [one_mem]
    · simpa using hv'
    · simpa using he₁'
    · simpa using H.mul_mem he₁' hv'
    · simpa using he₂'
  have hle : 5 ≤ Nat.card H := by
    have := Finset.card_le_card hsub
    rw [hc5] at this
    rw [Nat.card_eq_fintype_card]
    simpa [Set.toFinset_card] using this
  have hdvd : Nat.card H ∣ 8 := hE ▸ Subgroup.card_subgroup_dvd_card H
  have h8 : Nat.card H = 8 := by
    have : Nat.card H ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hh : Nat.card H <;> simp_all
  exact Subgroup.eq_top_of_card_eq H (h8.trans hE.symm)

theorem card_four [DecidableEq E] (hsq : ∀ e : E, e * e = 1) (v a : E) (hv : v ≠ 1) (ha1 : a ≠ 1)
    (hav : a ≠ v) : ({1, v, a, a * v} : Finset E).card = 4 := by
  have hinv : ∀ e : E, e⁻¹ = e := fun e => inv_eq_of_mul_eq_one_right (hsq e)
  have hne1v : a * v ≠ 1 := fun h => hav (by
    have := eq_inv_of_mul_eq_one_left h
    rwa [hinv] at this)
  have hnev : a * v ≠ v := fun h => ha1 (by simpa using h)
  have hne1 : a * v ≠ a := fun h => hv (by simpa using h)
  have h1 : (1 : E) ∉ ({v, a, a * v} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hv.symm, ha1.symm, hne1v.symm⟩
  have h2 : v ∉ ({a, a * v} : Finset E) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hav.symm, hnev.symm⟩
  have h3 : a ∉ ({a * v} : Finset E) := by
    simp only [Finset.mem_singleton]
    exact hne1.symm
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
    Finset.card_insert_of_notMem h3, Finset.card_singleton]

theorem card_stab_le [Finite E] (hE : Nat.card E = 8) (hsq : ∀ e : E, e * e = 1)
    (v : E) (hv : v ≠ 1) :
    Nat.card ↥(MulAction.stabilizer (MulAut E) v) ≤ 24 := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 8 := by rw [← Nat.card_eq_fintype_card]; exact hE
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : E, e₁ ≠ 1 ∧ e₁ ≠ v := by
    by_contra hcon
    have hall : ∀ e : E, e = 1 ∨ e = v := fun e => by
      by_cases h1 : e = 1
      · exact Or.inl h1
      · by_cases h2 : e = v
        · exact Or.inr h2
        · exact absurd ⟨e, h1, h2⟩ hcon
    have : (Finset.univ : Finset E) ⊆ {1, v} := fun e _ => by
      rcases hall e with h | h <;> simp [h]
    have h3 := Finset.card_le_card this
    have h2 : ({1, v} : Finset E).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, hcardE] at h3
    omega
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : E, e₂ ≠ 1 ∧ e₂ ≠ v ∧ e₂ ≠ e₁ ∧ e₂ ≠ e₁ * v := by
    by_contra hcon
    have hall : ∀ e : E, e = 1 ∨ e = v ∨ e = e₁ ∨ e = e₁ * v := fun e => by
      by_cases h1 : e = 1
      · exact Or.inl h1
      · by_cases h2 : e = v
        · exact Or.inr (Or.inl h2)
        · by_cases h3 : e = e₁
          · exact Or.inr (Or.inr (Or.inl h3))
          · by_cases h4 : e = e₁ * v
            · exact Or.inr (Or.inr (Or.inr h4))
            · exact absurd ⟨e, h1, h2, h3, h4⟩ hcon
    have : (Finset.univ : Finset E) ⊆ {1, v, e₁, e₁ * v} := fun e _ => by
      rcases hall e with h | h | h | h <;> simp [h]
    have h3 := Finset.card_le_card this
    have h4 := card_four hsq v e₁ hv he₁.1 he₁.2
    rw [Finset.card_univ, hcardE] at h3
    omega
  have hgen := closure_eq_top hE hsq v e₁ e₂ hv he₁ he₂
  let P : Finset (E × E) := Finset.univ.filter fun p =>
    p.1 ≠ 1 ∧ p.1 ≠ v ∧ p.2 ≠ 1 ∧ p.2 ≠ v ∧ p.2 ≠ p.1 ∧ p.2 ≠ p.1 * v
  have hinj : Function.Injective (fun γ : ↥(MulAction.stabilizer (MulAut E) v) =>
      ((γ : MulAut E) e₁, (γ : MulAut E) e₂)) := by
    intro γ γ' h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hγ : (γ : MulAut E) v = v := MulAction.mem_stabilizer_iff.1 γ.2
    have hγ' : (γ' : MulAut E) v = v := MulAction.mem_stabilizer_iff.1 γ'.2
    apply Subtype.ext
    apply MulEquiv.ext
    have hEq := MonoidHom.eqOn_closure (f := ((γ : MulAut E) : E →* E))
      (g := ((γ' : MulAut E) : E →* E)) (s := ({v, e₁, e₂} : Set E)) (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl
        · exact hγ.trans hγ'.symm
        · exact h1
        · exact h2)
    intro y
    have : y ∈ Subgroup.closure ({v, e₁, e₂} : Set E) := by rw [hgen]; exact mem_top y
    exact hEq this
  have hmap : ∀ γ : ↥(MulAction.stabilizer (MulAut E) v),
      ((γ : MulAut E) e₁, (γ : MulAut E) e₂) ∈ P := by
    intro γ
    have hγ : (γ : MulAut E) v = v := MulAction.mem_stabilizer_iff.1 γ.2
    have hγ1 : (γ : MulAut E) 1 = 1 := map_one _
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
    have hi := (γ : MulAut E).injective
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; exact he₁.1 (hi (h.trans hγ1.symm))
    · intro h; exact he₁.2 (hi (h.trans hγ.symm))
    · intro h; exact he₂.1 (hi (h.trans hγ1.symm))
    · intro h; exact he₂.2.1 (hi (h.trans hγ.symm))
    · intro h; exact he₂.2.2.1 (hi h)
    · intro h; apply he₂.2.2.2; apply hi; rw [h, map_mul, hγ]
  have hcardP : P.card ≤ 24 := by
    set A' : Finset E := Finset.univ.filter fun a => a ≠ 1 ∧ a ≠ v with hA'
    have hA'card : A'.card ≤ 6 := by
      have hsub : A' ⊆ Finset.univ \ {1, v} := by
        intro a ha
        simp only [hA', Finset.mem_filter, Finset.mem_univ, true_and] at ha
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and, not_or]
        exact ha
      have h2 : ({1, v} : Finset E).card = 2 := Finset.card_pair hv.symm
      have h3 := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcardE, h2] at h3
      exact h3
    have hfib : ∀ a ∈ A', (P.filter fun p => p.1 = a).card ≤ 4 := by
      intro a ha
      have hae : a ≠ 1 ∧ a ≠ v := by simpa [hA'] using ha
      have hsub : P.filter (fun p => p.1 = a) ⊆
          (Finset.univ \ {1, v, a, a * v}).image (fun b => (a, b)) := by
        intro p hp
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        obtain ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩ := hp
        simp only [Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
          Finset.mem_singleton, true_and, not_or]
        refine ⟨p.2, ⟨h3, h4, ?_, ?_⟩, ?_⟩
        · rw [← h7]; exact h5
        · rw [← h7]; exact h6
        · exact Prod.ext h7.symm rfl
      have h4 := card_four hsq v a hv hae.1 hae.2
      have h5 := Finset.card_le_card hsub
      have h6 : ((Finset.univ \ {1, v, a, a * v}).image fun b => (a, b)).card ≤
          (Finset.univ \ {1, v, a, a * v}).card := Finset.card_image_le
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcardE, h4] at h6
      exact h5.trans h6
    have hfunc : ∀ p ∈ P, p.1 ∈ A' := by
      intro p hp
      simp only [P, hA', Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    rw [Finset.card_eq_sum_card_fiberwise hfunc]
    calc ∑ a ∈ A', (P.filter fun p => p.1 = a).card ≤ ∑ a ∈ A', 4 := Finset.sum_le_sum hfib
      _ = A'.card * 4 := by simp
      _ ≤ 24 := by omega
  have : Fintype ↥(MulAction.stabilizer (MulAut E) v) := Fintype.ofFinite _
  calc Nat.card ↥(MulAction.stabilizer (MulAut E) v) ≤ P.card := by
        have := Finset.card_le_card_of_injOn
          (s := (Finset.univ : Finset ↥(MulAction.stabilizer (MulAut E) v)))
          (t := P) (fun γ => ((γ : MulAut E) e₁, (γ : MulAut E) e₂)) (fun γ _ => hmap γ)
          (fun a _ b _ h => hinj h)
        rwa [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    _ ≤ 24 := hcardP

end Aut

section Rec

variable {C : Type*} [Group C]

@[expose] def actHom (E D : Subgroup C) [E.Normal] : ↥D →* MulAut ↥E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion (E.normalizer_eq_top ▸ le_top))

theorem actHom_apply (E D : Subgroup C) [E.Normal] (d : ↥D) (e : ↥E) :
    ((actHom E D d e : ↥E) : C) = d * e * (d : C)⁻¹ := rfl

theorem action_facts {E D : Subgroup C} [E.Normal]
    (h : E.IsComplement' D) (v : C) (hv : v ∈ E) (hvc : ∀ c, c * v = v * c)
    (hcent : ∀ c : C, (∀ e ∈ E, c * e = e * c) → c ∈ E) :
    Function.Injective (actHom E D) ∧ ∀ d : ↥D, actHom E D d ⟨v, hv⟩ = ⟨v, hv⟩ := by
  refine ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro d hd
    rw [MonoidHom.mem_ker] at hd
    have hd' : (d : C) ∈ E := by
      apply hcent
      intro e he
      have h1 := congrArg (fun f : MulAut ↥E => ((f ⟨e, he⟩ : ↥E) : C)) hd
      simp only [MulAut.one_apply] at h1
      rw [actHom_apply] at h1
      calc (d : C) * e = (d : C) * e * (d : C)⁻¹ * d := by group
        _ = e * d := by rw [h1]
    have hdis := h.disjoint
    rw [Subgroup.disjoint_def] at hdis
    exact Subgroup.mem_bot.2 (Subtype.ext (hdis hd' d.2))
  · intro d
    apply Subtype.ext
    rw [actHom_apply]
    show (d : C) * v * (d : C)⁻¹ = v
    rw [hvc d]; group

theorem exists_mulEquiv_of_E8 {C₂ : Type*} [Group C₂] [Finite C] [Finite C₂]
    {E₁ D₁ : Subgroup C} {E₂ D₂ : Subgroup C₂} [E₁.Normal] [E₂.Normal]
    (h₁ : E₁.IsComplement' D₁) (h₂ : E₂.IsComplement' D₂)
    (hc₁ : Nat.card C = 192) (hc₂ : Nat.card C₂ = 192)
    (hE₁ : Nat.card E₁ = 8) (hE₂ : Nat.card E₂ = 8)
    (hsq₂ : ∀ e ∈ E₂, e * e = 1)
    (v₁ : C) (v₂ : C₂) (hv₁ : v₁ ∈ E₁) (hv₂ : v₂ ∈ E₂) (hv₂1 : v₂ ≠ 1)
    (hvc₁ : ∀ c, c * v₁ = v₁ * c) (hvc₂ : ∀ c, c * v₂ = v₂ * c)
    (hcent₁ : ∀ c : C, (∀ e ∈ E₁, c * e = e * c) → c ∈ E₁)
    (hcent₂ : ∀ c : C₂, (∀ e ∈ E₂, c * e = e * c) → c ∈ E₂)
    (lam : ↥E₁ ≃* ↥E₂) (hlam : lam ⟨v₁, hv₁⟩ = ⟨v₂, hv₂⟩) :
    Nonempty (C ≃* C₂) := by
  classical
  obtain ⟨hinj₁, hfix₁⟩ := action_facts h₁ v₁ hv₁ hvc₁ hcent₁
  obtain ⟨hinj₂, hfix₂⟩ := action_facts h₂ v₂ hv₂ hvc₂ hcent₂
  have hD₁ : Nat.card D₁ = 24 := by
    have := h₁.card_mul_card
    rw [hc₁, hE₁] at this
    omega
  have hD₂ : Nat.card D₂ = 24 := by
    have := h₂.card_mul_card
    rw [hc₂, hE₂] at this
    omega
  let ψ₁ : ↥D₁ →* MulAut ↥E₂ := (MulAut.congr lam).toMonoidHom.comp (actHom E₁ D₁)
  have hψ₁inj : Function.Injective ψ₁ :=
    (MulAut.congr lam).injective.comp hinj₁
  let Sg : Subgroup (MulAut ↥E₂) := MulAction.stabilizer (MulAut ↥E₂) (⟨v₂, hv₂⟩ : ↥E₂)
  have hSg : Nat.card Sg ≤ 24 :=
    card_stab_le (by rw [← hE₂]) (fun e => Subtype.ext (hsq₂ _ e.2))
      ⟨v₂, hv₂⟩ (fun h => hv₂1 (congrArg Subtype.val h))
  have hψ₁fix : ∀ d, ψ₁ d ∈ Sg := by
    intro d
    show ψ₁ d ⟨v₂, hv₂⟩ = ⟨v₂, hv₂⟩
    have h1 : (MulAut.congr lam) (actHom E₁ D₁ d) ⟨v₂, hv₂⟩ =
        lam ((actHom E₁ D₁ d) (lam.symm ⟨v₂, hv₂⟩)) := rfl
    have h2 : lam.symm ⟨v₂, hv₂⟩ = ⟨v₁, hv₁⟩ := by rw [← hlam]; simp
    show (MulAut.congr lam) (actHom E₁ D₁ d) ⟨v₂, hv₂⟩ = ⟨v₂, hv₂⟩
    rw [h1, h2, hfix₁, hlam]
  have hρ₂fix : ∀ d, actHom E₂ D₂ d ∈ Sg := fun d => hfix₂ d
  have hrange₁ : ψ₁.range = Sg := by
    have hle : ψ₁.range ≤ Sg := by rintro _ ⟨d, rfl⟩; exact hψ₁fix d
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ₁inj).toEquiv, hD₁]
    exact hSg
  have hrange₂ : (actHom E₂ D₂).range = Sg := by
    have hle : (actHom E₂ D₂).range ≤ Sg := by rintro _ ⟨d, rfl⟩; exact hρ₂fix d
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj₂).toEquiv, hD₂]
    exact hSg
  let fg : ↥D₁ ≃* ↥D₂ := (MonoidHom.ofInjective hψ₁inj).trans
    ((MulEquiv.subgroupCongr (hrange₁.trans hrange₂.symm)).trans
      (MonoidHom.ofInjective hinj₂).symm)
  have hfg : ∀ d, actHom E₂ D₂ (fg d) = ψ₁ d := by
    intro d
    have h1 : ((MonoidHom.ofInjective hinj₂) (fg d) : MulAut ↥E₂) = ψ₁ d := by
      show ((MonoidHom.ofInjective hinj₂) ((MonoidHom.ofInjective hinj₂).symm
        ((MulEquiv.subgroupCongr (hrange₁.trans hrange₂.symm)) ((MonoidHom.ofInjective hψ₁inj) d)))
        : MulAut ↥E₂) = ψ₁ d
      rw [MulEquiv.apply_symm_apply]
      rfl
    exact h1
  let Φ : E₁ ⋊[actHom E₁ D₁] D₁ ≃* E₂ ⋊[actHom E₂ D₂] D₂ :=
    SemidirectProduct.congr lam fg (by
      intro d
      refine MulEquiv.ext fun e => ?_
      show lam ((actHom E₁ D₁ d) e) = (actHom E₂ D₂ (fg d)) (lam e)
      rw [hfg]
      show lam ((actHom E₁ D₁ d) e) = ((MulAut.congr lam) (actHom E₁ D₁ d)) (lam e)
      simp [MulAut.congr_apply])
  exact ⟨(SemidirectProduct.mulEquivSubgroup h₁).symm.trans
    (Φ.trans (SemidirectProduct.mulEquivSubgroup h₂))⟩

end Rec

end CFSG.GH74.GLS.C3.Layer2.L5

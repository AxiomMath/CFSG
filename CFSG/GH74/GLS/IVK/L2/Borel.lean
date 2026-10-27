module

public import CFSG.GH74.GLS.IVK.Statements.Sec1
public import CFSG.GH74.GLS.IVK.L2.Transport
public import CFSG.GH74.GLS.IVK.L2.BorelMatrices
public import CFSG.GH74.GLS.IVK.L2.BorelSylow
public import CFSG.CharacterTheory.PSL2Table.Classes

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG.PSL2Table
open scoped MatrixGroups

namespace L2Borel

section Normal

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F)

theorem two_ne_zero_of_odd_card (h : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro hc
  have h1 := FiniteField.even_card_iff_char_two.1 hc
  rw [Nat.card_eq_fintype_card] at h
  have := Nat.odd_iff.1 h
  omega

noncomputable def psiEquiv (c : PSL(2, F)) : PSL(2, F) ≃* K :=
  (MulAut.conj c).trans (toPSL e).symm

omit [Finite F] in
theorem toPSL_psiEquiv (c y : PSL(2, F)) : toPSL e (psiEquiv e c y) = c * y * c⁻¹ := by
  simp [psiEquiv, MulAut.conj_apply]

omit [Finite F] in
theorem psiEquiv_symm_apply (c : PSL(2, F)) (k : K) :
    (psiEquiv e c).symm k = c⁻¹ * toPSL e k * c := by
  simp [psiEquiv]

theorem exists_psiEquiv_eq {p n : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ n) [Finite K]
    (W : Sylow p K) :
    ∃ c : PSL(2, F), (W : Subgroup K) = (unipotent F).map (psiEquiv e c).toMonoidHom := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hF
    (Sylow.mapSurjective (f := (toPSL e).toMonoidHom) (toPSL e).surjective W)
  refine ⟨c, ?_⟩
  have hc' : W.map (toPSL e).toMonoidHom = (unipotent F).map (MulAut.conj c).toMonoidHom := hc
  ext k
  have h1 := congrArg (fun S : Subgroup (PSL(2, F)) => toPSL e k ∈ S) hc'
  simp only [Subgroup.mem_map_equiv] at h1 ⊢
  simpa [psiEquiv] using h1

omit [Finite F] in
theorem innDiagHom_toPGL_toPSL [Finite F] (k : K) :
    innDiagHom e (Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e k)) = MulAut.conj k := by
  ext x
  apply (toPSL e).injective
  apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  rw [toPGL_toPSL_innDiagHom]
  simp [MulAut.conj_apply]

end Normal

end L2Borel

open L2Borel

theorem ivk_1_5c : IVK_1_5c := by
  intro F _ _ hF K _ _ e p n hp hcard W x hx
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF.1
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hcard W
  set ψ := psiEquiv e c with hψ
  have hN : normalizer ((W : Subgroup K) : Set K) = (borel F).map ψ.toMonoidHom := by
    rw [hc, normalizer_map_equiv, normalizer_unipotent_eq h2]
  have hx' : ψ.symm x ∉ borel F := by
    intro h
    apply hx
    rw [hN]
    exact ⟨ψ.symm x, h, by simp⟩
  have hset : ((W : Subgroup K) : Set K) = ψ '' (unipotent F : Set (PSL(2, F))) := by
    rw [hc]
    rfl
  have key : Subgroup.closure (((W : Subgroup K) : Set K) ∪ {x}) =
      (Subgroup.closure ((unipotent F : Set (PSL(2, F))) ∪ {ψ.symm x})).map ψ.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_union, Set.image_singleton, hset]
    simp
  rw [key, closure_unipotent_insert_eq_top hx', Subgroup.map_top_of_surjective _ ψ.surjective]

theorem ivk_1_5d : IVK_1_5d := by
  intro F _ _ hF K _ _ e p n hp hcard W M hWM hModd x hxM
  by_contra hx
  have h := ivk_1_5c F hF K e p n hp hcard W x hx
  have hM : M = ⊤ := by
    rw [eq_top_iff, ← h]
    exact (Subgroup.closure_le M).2 (Set.union_subset hWM (Set.singleton_subset_iff.2 hxM))
  rw [hM, Subgroup.card_top] at hModd
  obtain ⟨k, hk⟩ := hF.1
  have hsq : Nat.card F ^ 2 - 1 = 4 * (k * (k + 1)) := by
    apply Nat.sub_eq_of_eq_add
    rw [hk]
    ring
  have hKeven : Even (Nat.card K) := by
    rw [card_eq_of_L2Field e hF, hsq, hk]
    have : (2 * k + 1) * (4 * (k * (k + 1))) / 2 = (2 * k + 1) * (2 * (k * (k + 1))) := by
      rw [show (2 * k + 1) * (4 * (k * (k + 1))) = 2 * ((2 * k + 1) * (2 * (k * (k + 1)))) by ring]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    rw [this]
    exact ⟨(2 * k + 1) * (k * (k + 1)), by ring⟩
  exact (Nat.not_even_iff_odd.2 hModd) hKeven

theorem ivk_1_4g : IVK_1_4g := by
  intro F _ _ hF K _ _ e p n hp hcard W W₀ hW₀W hW₀
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hF.1
  obtain ⟨c, hc⟩ := exists_psiEquiv_eq e hp hcard W
  set ψ := psiEquiv e c with hψ
  refine ⟨?_, ?_⟩
  · ext α
    constructor
    · rintro ⟨hα, ⟨g, rfl⟩⟩
      obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hW₀
      have hw1' : w ≠ 1 := fun h => hw1 (Subtype.ext h)
      have hfix : innDiagHom e g w = w := by
        have hcomm : MulAut.conj w * innDiagHom e g = innDiagHom e g * MulAut.conj w :=
          (Subgroup.mem_centralizer_iff.1 hα) (MulAut.conj w) ⟨w, hw, rfl⟩
        have hinj := conj_injective_of_L2 e
        apply hinj
        ext y
        have h1 := congrArg (fun γ : MulAut K => γ ((innDiagHom e g)⁻¹ y)) hcomm
        simp [MulAut.conj_apply] at h1 ⊢
        exact h1.symm
      have hcommg : g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e w) =
          Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e w) * g := by
        have h := toPGL_toPSL_innDiagHom e g w
        rw [hfix] at h
        calc g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e w)
            = (g * Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e w) * g⁻¹) * g := by group
          _ = Matrix.ProjectiveSpecialLinearGroup.toPGL (toPSL e w) * g := by rw [← h]
      have hwW : w ∈ (W : Subgroup K) := hW₀W hw
      rw [hc] at hwW
      obtain ⟨y₁, hy₁, hy₁w⟩ := hwW
      obtain ⟨t, rfl⟩ := (mem_unipotent_iff_exists y₁).1 hy₁
      have ht : t ≠ 0 := by
        rintro rfl
        apply hw1'
        rw [← hy₁w]
        simp [unip_zero]
      have hψw : toPSL e w = c * mk (unip t) * c⁻¹ := by
        rw [← hy₁w]
        exact toPSL_psiEquiv e c _
      set C := Matrix.ProjectiveSpecialLinearGroup.toPGL c with hC
      set Y := Matrix.ProjectiveSpecialLinearGroup.toPGL (mk (unip t)) with hY
      have hcommg' : g * (C * Y * C⁻¹) = (C * Y * C⁻¹) * g := by
        have := hcommg
        rw [hψw, map_mul, map_mul, map_inv] at this
        exact this
      have hcomm2 : (C⁻¹ * g * C) * Y = Y * (C⁻¹ * g * C) := by
        calc C⁻¹ * g * C * Y = C⁻¹ * (g * (C * Y * C⁻¹)) * C := by group
          _ = C⁻¹ * ((C * Y * C⁻¹) * g) * C := by rw [hcommg']
          _ = Y * (C⁻¹ * g * C) := by group
      obtain ⟨s, hs⟩ := exists_eq_toPGL_of_commute ht hcomm2
      have hg : g = Matrix.ProjectiveSpecialLinearGroup.toPGL
          (c * mk (unip s) * c⁻¹) := by
        rw [map_mul, map_mul, map_inv, ← hC, ← hs]
        group
      have hkW : ψ (mk (unip s)) ∈ (W : Subgroup K) := by
        rw [hc]
        exact ⟨_, mk_unip_mem_unipotent s, rfl⟩
      refine ⟨ψ (mk (unip s)), hkW, ?_⟩
      have : toPSL e (ψ (mk (unip s))) = c * mk (unip s) * c⁻¹ := toPSL_psiEquiv e c _
      rw [hg, ← this, innDiagHom_toPGL_toPSL]
    · rintro ⟨k, hk, rfl⟩
      refine Subgroup.mem_inf.2 ⟨?_, innAut_le_innDiagSub e ⟨k, rfl⟩⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      have hwW := hW₀W hw
      rw [hc] at hwW hk
      obtain ⟨y₁, hy₁, rfl⟩ := hwW
      obtain ⟨y₂, hy₂, rfl⟩ := hk
      rw [← map_mul, ← map_mul, unipotent_mul_comm hy₁ hy₂]
  · refine ⟨(splitTorus F).map ψ.toMonoidHom, ?_, ?_, ?_⟩
    · have : IsCyclic (splitTorus F) := splitTorus_isCyclic
      exact ((splitTorus F).equivMapOfInjective ψ.toMonoidHom ψ.injective).isCyclic.1 this
    · rw [Subgroup.card_map_of_injective ψ.injective, card_splitTorus_eq h2]
    · rw [hc, normalizer_map_equiv, normalizer_unipotent_eq h2]
      exact IsFrobeniusSplit.map_equiv ψ (isFrobeniusSplit_unipotent h2)

end CFSG.GH74.GLS.IVK

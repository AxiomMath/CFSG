module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelMinusThreeN
public import CFSG.RankThree.GF2n.Smith81.OrthRootInvol

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K : Type*} [Field K] [CharP K 2] {N : Type*} [AddCommGroup N] [Module K N]
  {Q : QuadraticForm K N}

theorem MinusThreeFrame.natCard_le_of_forall_singular [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) (W : AddSubgroup N)
    (hWe : ∀ w ∈ W, polar Q e w = 0) (hWf : ∀ w ∈ W, polar Q f w = 0)
    (hW : ∀ w ∈ W, Q w = 0) : Nat.card W ≤ Nat.card K := by
  by_cases hbot : ∃ w₀ ∈ W, w₀ ≠ 0
  · obtain ⟨w₀, hw₀, hw₀0⟩ := hbot
    have hcol : ∀ w ∈ W, ∃ c : K, w = c • w₀ := by
      intro w hw
      have hpol : polar Q w₀ w = 0 := by
        have h1 := hW _ (W.add_mem hw₀ hw)
        rw [QuadraticMap.map_add Q, hW w₀ hw₀, hW w hw] at h1
        simpa using h1
      exact hF.eq_smul_of_polar_eq_zero (by rw [polar_comm]; exact hWe w₀ hw₀)
        (by rw [polar_comm]; exact hWf w₀ hw₀) (by rw [polar_comm]; exact hWe w hw)
        (by rw [polar_comm]; exact hWf w hw) (hW w₀ hw₀) (hW w hw) hw₀0 hpol
    choose! c hc using hcol
    refine Nat.card_le_card_of_injective (fun w : W => c w) fun w₁ w₂ h => ?_
    refine Subtype.ext ?_
    rw [hc w₁ w₁.2, hc w₂ w₂.2]
    simp only at h
    rw [h]
  · have hbot' : ∀ w ∈ W, w = 0 := fun w hw => by_contra fun hne => hbot ⟨w, hw, hne⟩
    have : Subsingleton W := ⟨fun a b => Subtype.ext ((hbot' a a.2).trans (hbot' b b.2).symm)⟩
    exact (Nat.card_of_subsingleton (0 : W)).le.trans (Nat.succ_le_of_lt Nat.card_pos)

omit [CharP K 2] in
private theorem MinusThreeFrame.finite_space [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) : Finite N := by
  have htop : Submodule.span K {e, f, p, p', u, v} = ⊤ := eq_top_iff.mpr fun x _ => hF.span x
  have : Module.Finite K N :=
    Module.finite_def.2 (htop ▸ Submodule.fg_span (Set.toFinite _))
  exact Module.finite_of_finite K

omit [CharP K 2] in
private theorem MinusThreeFrame.exists_addSubgroup_of_le_rootGroup [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) {Y : Subgroup (N ≃ₗ[K] N)} (hY : Y ≤ rootGroup Q e) :
    ∃ W : AddSubgroup N,
      (∀ w, w ∈ W ↔ polar Q e w = 0 ∧ polar Q f w = 0 ∧ eichler Q e w ∈ Y) ∧
        Nat.card Y ≤ Nat.card W := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hF.ef
  let W : AddSubgroup N :=
    { carrier := {w | polar Q e w = 0 ∧ polar Q f w = 0 ∧ eichler Q e w ∈ Y}
      zero_mem' := ⟨polar_zero_right Q e, polar_zero_right Q f,
        by rw [eichler_zero_right]; exact Y.one_mem⟩
      add_mem' := by
        rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
        refine ⟨by rw [polar_add_right, ha1, hb1, add_zero],
          by rw [polar_add_right, ha2, hb2, add_zero], ?_⟩
        rw [← eichler_mul ha1 hb1]
        exact Y.mul_mem ha3 hb3
      neg_mem' := by
        rintro a ⟨ha1, ha2, ha3⟩
        refine ⟨by rw [polar_neg_right, ha1, neg_zero], by rw [polar_neg_right, ha2, neg_zero],
          ?_⟩
        rw [← eichler_inv ha1]
        exact Y.inv_mem ha3 }
  have hex : ∀ g : Y, ∃ w : N, polar Q e w = 0 ∧ polar Q f w = 0 ∧ eichler Q e w = g := by
    rintro ⟨g, hg⟩
    obtain ⟨x, hx, rfl⟩ := mem_rootGroup.mp (hY hg)
    refine ⟨x + (-polar Q x f) • e, ?_, ?_, eichler_add_smul_self hF.e_sing x _⟩
    · rw [polar_add_right, hx, polar_smul_right_eq, polar_self_eq_zero hF.e_sing]
      simp
    · rw [polar_add_right, polar_smul_right_eq, hfe, polar_comm Q f x]
      ring
  choose φ hφ1 hφ2 hφ3 using hex
  have := hF.finite_space
  refine ⟨W, fun w => Iff.rfl, ?_⟩
  refine Nat.card_le_card_of_injective
    (fun g : Y => (⟨φ g, hφ1 g, hφ2 g, by rw [hφ3 g]; exact g.2⟩ : W)) fun g₁ g₂ h => ?_
  have h' : φ g₁ = φ g₂ := congrArg Subtype.val h
  exact Subtype.ext (by rw [← hφ3 g₁, ← hφ3 g₂, h'])

theorem MinusThreeFrame.exists_eichler_mem_of_lt_natCard [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) {Y : Subgroup (N ≃ₗ[K] N)} (hY : Y ≤ rootGroup Q e)
    (hcard : Nat.card K < Nat.card Y) :
    ∃ w : N, polar Q e w = 0 ∧ polar Q f w = 0 ∧ Q w ≠ 0 ∧ eichler Q e w ∈ Y := by
  by_contra hcon
  obtain ⟨W, hW, hWcard⟩ := hF.exists_addSubgroup_of_le_rootGroup hY
  have := hF.natCard_le_of_forall_singular W (fun w hw => ((hW w).1 hw).1)
    (fun w hw => ((hW w).1 hw).2.1) fun w hw => by
      obtain ⟨h1, h2, h3⟩ := (hW w).1 hw
      by_contra hq
      exact hcon ⟨w, h1, h2, hq, h3⟩
  omega

theorem MinusThreeFrame.exists_eichler_mem_of_lt_natCard_of_point [Finite K] {e f p p' u v : N}
    (hF : MinusThreeFrame Q e f p p' u v) (hnd : (polarBilin Q).Nondegenerate) {a : N}
    (ha : Q a = 0) (ha0 : a ≠ 0) {Y : Subgroup (N ≃ₗ[K] N)} (hY : Y ≤ rootGroup Q a)
    (hcard : Nat.card K < Nat.card Y) :
    ∃ w : N, polar Q a w = 0 ∧ Q w ≠ 0 ∧ eichler Q a w ∈ Y := by
  let P₁ : HypPair Q := ⟨e, f, hF.e_sing, hF.f_sing, hF.ef⟩
  let P₂ : HypPair Q := ⟨p, p', hF.p_sing, hF.p'_sing, hF.pp'⟩
  have horth : P₁.Orth P₂ := ⟨hF.ep, hF.ep', hF.fp, hF.fp'⟩
  obtain ⟨g, hg, hge⟩ := exists_mem_elementaryGroup_apply_eq hnd horth P₁.e_ne_zero ha0
    (hF.e_sing.trans ha.symm)
  replace hge : g e = a := hge
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q hg
  have hga : g⁻¹ a = e := by rw [← hge]; exact LinearEquiv.inv_apply_apply' g e
  have hY' : Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ rootGroup Q e := by
    rintro _ ⟨y, hy, rfl⟩
    have := conj_mem_rootGroup (inv_mem hgO) (hY hy)
    rwa [hga, inv_inv] at this
  have hcard' : Nat.card K < Nat.card (Y.map (MulAut.conj g⁻¹).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
  obtain ⟨w, hwe, -, hQw, y, hy, hyw⟩ := hF.exists_eichler_mem_of_lt_natCard hY' hcard'
  refine ⟨g w, ?_, ?_, ?_⟩
  · rw [← hge, polar_map_of_mem hgO]
    exact hwe
  · rw [map_of_mem hgO]
    exact hQw
  · have hyg : y = g * eichler Q e w * g⁻¹ := by
      rw [← hyw]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [← hge, ← eichler_conj hgO, ← hyg]
    exact hy

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

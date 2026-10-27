module

public import CFSG.RankThree.PartOne.S11d.OrthRational

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_mem_elementaryGroup_hypPair (hQ : (polarBilin Q).Nondegenerate)
    {P₁ P₂ : HypPair Q} (h : P₁.Orth P₂) (P P' : HypPair Q) :
    ∃ g ∈ elementaryGroup Q, g P.e = P'.e ∧ g P.f = P'.f := by
  have hPe : P.e ≠ 0 := fun h0 => by
    have := P.polar_ef
    rw [h0, polar_zero_left] at this
    exact zero_ne_one this
  have hP'e : P'.e ≠ 0 := fun h0 => by
    have := P'.polar_ef
    rw [h0, polar_zero_left] at this
    exact zero_ne_one this
  obtain ⟨g₁, hg₁, hg₁e⟩ := exists_mem_elementaryGroup_apply_eq hQ h hPe hP'e
    (by rw [P.Q_e, P'.Q_e])
  have hg₁o := elementaryGroup_le_orthogonalGroup Q hg₁
  set f₁ := g₁ P.f with hf₁
  have hQf₁ : Q f₁ = 0 := by rw [hf₁, map_of_mem hg₁o]; exact P.Q_f
  have hpf₁ : polar Q P'.e f₁ = 1 := by
    rw [← hg₁e, hf₁, polar_map_of_mem hg₁o]
    exact P.polar_ef
  have hw : polar Q P'.e (P'.f - f₁) = 0 := by
    rw [polar_sub_right, P'.polar_ef, hpf₁, sub_self]
  refine ⟨eichler Q P'.e (P'.f - f₁) * g₁,
    mul_mem (eichler_mem_elementaryGroup Q _ _) hg₁, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₁e]
    exact eichler_apply_self _ _
  · have hpf₁' : polar Q f₁ P'.e = 1 := by rw [polar_comm]; exact hpf₁
    have hQ' : Q (P'.f - f₁) = - polar Q P'.f f₁ := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, P'.Q_f, QuadraticMap.map_neg, hQf₁,
        polar_neg_right]
      ring
    have h1 : polar Q f₁ (P'.f - f₁) + Q (P'.f - f₁) * 1 = 0 := by
      rw [polar_sub_right, hQ', polar_self_eq_zero hQf₁, polar_comm Q P'.f f₁]
      ring
    rw [LinearEquiv.mul_apply, ← hf₁, eichler_apply P'.Q_e hw, hpf₁', h1]
    simp

section Perp

variable (T : HypPair Q)

theorem polar_comp_subtype' (W : Submodule K V) (u w : W) :
    polar (Q.comp W.subtype) u w = polar Q (u : V) (w : V) := by
  simp only [polar, QuadraticMap.comp_apply, Submodule.subtype_apply, Submodule.coe_add]

@[expose] def hypPairToSub (W : Submodule K V) (P : HypPair Q) (he : P.e ∈ W) (hf : P.f ∈ W) :
    HypPair (Q.comp W.subtype) where
  e := ⟨P.e, he⟩
  f := ⟨P.f, hf⟩
  Q_e := by simpa using P.Q_e
  Q_f := by simpa using P.Q_f
  polar_ef := by rw [polar_comp_subtype']; exact P.polar_ef

theorem orth_hypPairToSub {W : Submodule K V} {P P' : HypPair Q} (h : P.Orth P')
    (he : P.e ∈ W) (hf : P.f ∈ W) (he' : P'.e ∈ W) (hf' : P'.f ∈ W) :
    (hypPairToSub W P he hf).Orth (hypPairToSub W P' he' hf') :=
  ⟨by simpa [hypPairToSub, polar_comp_subtype'] using h.ee,
   by simpa [hypPairToSub, polar_comp_subtype'] using h.ef,
   by simpa [hypPairToSub, polar_comp_subtype'] using h.fe,
   by simpa [hypPairToSub, polar_comp_subtype'] using h.ff⟩

theorem exists_extension {g' : T.perp ≃ₗ[K] T.perp}
    (hg' : g' ∈ elementaryGroup (Q.comp T.perp.subtype)) :
    ∃ g ∈ elementaryGroup Q, (∀ v : T.perp, g (v : V) = (g' v : V)) ∧ g T.e = T.e ∧
      g T.f = T.f := by
  induction hg' using Subgroup.closure_induction with
  | mem g' hg' =>
    obtain ⟨u, w, hu, hw, rfl⟩ := hg'
    have hu' : Q (u : V) = 0 := by simpa using hu
    have hw' : polar Q (u : V) (w : V) = 0 := by rwa [polar_comp_subtype'] at hw
    refine ⟨eichler Q (u : V) (w : V), eichler_mem_elementaryGroup Q _ _, fun v => ?_, ?_, ?_⟩
    · rw [eichler_apply hu' hw', eichler_apply hu hw]
      simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul, polar_comp_subtype',
        QuadraticMap.comp_apply, Submodule.subtype_apply]
    · exact eichler_apply_of_polar_eq_zero (HypPair.mem_perp.1 u.2).1 (HypPair.mem_perp.1 w.2).1
    · exact eichler_apply_of_polar_eq_zero (HypPair.mem_perp.1 u.2).2 (HypPair.mem_perp.1 w.2).2
  | one => exact ⟨1, one_mem _, fun v => rfl, rfl, rfl⟩
  | mul a b _ _ ha hb =>
    obtain ⟨ga, hga, hga1, hga2, hga3⟩ := ha
    obtain ⟨gb, hgb, hgb1, hgb2, hgb3⟩ := hb
    refine ⟨ga * gb, mul_mem hga hgb, fun v => ?_, ?_, ?_⟩
    · rw [LinearEquiv.mul_apply, hgb1, hga1]; rfl
    · rw [LinearEquiv.mul_apply, hgb2, hga2]
    · rw [LinearEquiv.mul_apply, hgb3, hga3]
  | inv a _ ha =>
    obtain ⟨ga, hga, hga1, hga2, hga3⟩ := ha
    refine ⟨ga⁻¹, inv_mem hga, fun v => ?_, ?_, ?_⟩
    · have h1 : ga ((a⁻¹ v : T.perp) : V) = (v : V) := by rw [hga1]; simp
      rw [← h1]; simp
    · exact (LinearEquiv.symm_apply_eq _).2 hga2.symm
    · exact (LinearEquiv.symm_apply_eq _).2 hga3.symm

end Perp

@[expose] def hypPairMap {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (P : HypPair Q) : HypPair Q where
  e := g P.e
  f := g P.f
  Q_e := by rw [map_of_mem hg]; exact P.Q_e
  Q_f := by rw [map_of_mem hg]; exact P.Q_f
  polar_ef := by rw [polar_map_of_mem hg]; exact P.polar_ef

theorem orth_hypPairMap {g : V ≃ₗ[K] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {P P' : HypPair Q} (h : P.Orth P') : (hypPairMap hg P).Orth (hypPairMap hg P') :=
  ⟨by simpa [hypPairMap, polar_map_of_mem hg] using h.ee,
   by simpa [hypPairMap, polar_map_of_mem hg] using h.ef,
   by simpa [hypPairMap, polar_map_of_mem hg] using h.fe,
   by simpa [hypPairMap, polar_map_of_mem hg] using h.ff⟩

theorem exists_mem_elementaryGroup_two (hQ : (polarBilin Q).Nondegenerate)
    {S₁ S₂ S₃ : HypPair Q} (h12 : S₁.Orth S₂) (h13 : S₁.Orth S₃) (h23 : S₂.Orth S₃)
    {T₁ T₂ : HypPair Q} (hT : T₁.Orth T₂) :
    ∃ g ∈ elementaryGroup Q, g S₁.e = T₁.e ∧ g S₁.f = T₁.f ∧ g S₂.e = T₂.e ∧ g S₂.f = T₂.f := by
  obtain ⟨g₁, hg₁, hg₁e, hg₁f⟩ := exists_mem_elementaryGroup_hypPair hQ h23 S₁ T₁
  have hg₁o := elementaryGroup_le_orthogonalGroup Q hg₁
  set R₂ := hypPairMap hg₁o S₂ with hR₂
  set R₃ := hypPairMap hg₁o S₃ with hR₃
  have hR23 : R₂.Orth R₃ := orth_hypPairMap hg₁o h23
  have hT1R : ∀ R : HypPair Q, (R.e ∈ T₁.perp ∧ R.f ∈ T₁.perp) ↔
      (polar Q T₁.e R.e = 0 ∧ polar Q T₁.f R.e = 0 ∧ polar Q T₁.e R.f = 0 ∧
        polar Q T₁.f R.f = 0) := fun R => by
    simp only [HypPair.mem_perp]
    tauto
  have hR2 : R₂.e ∈ T₁.perp ∧ R₂.f ∈ T₁.perp := by
    rw [hT1R]
    have := orth_hypPairMap hg₁o h12
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := this.ee; simpa [hR₂, hypPairMap, ← hg₁e] using this
    · have := this.fe; simpa [hR₂, hypPairMap, ← hg₁f] using this
    · have := this.ef; simpa [hR₂, hypPairMap, ← hg₁e] using this
    · have := this.ff; simpa [hR₂, hypPairMap, ← hg₁f] using this
  have hR3 : R₃.e ∈ T₁.perp ∧ R₃.f ∈ T₁.perp := by
    rw [hT1R]
    have := orth_hypPairMap hg₁o h13
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := this.ee; simpa [hR₃, hypPairMap, ← hg₁e] using this
    · have := this.fe; simpa [hR₃, hypPairMap, ← hg₁f] using this
    · have := this.ef; simpa [hR₃, hypPairMap, ← hg₁e] using this
    · have := this.ff; simpa [hR₃, hypPairMap, ← hg₁f] using this
  have hT2 : T₂.e ∈ T₁.perp ∧ T₂.f ∈ T₁.perp := by
    rw [hT1R]
    exact ⟨hT.ee, hT.fe, hT.ef, hT.ff⟩
  have hQ' : (polarBilin (Q.comp T₁.perp.subtype)).Nondegenerate :=
    CFSG.RankThree.PartOne.nondegenerate_comp_of_polarNondegOn
      (HypPair.polarNondegOn_perp hQ T₁)
  set R₂' := hypPairToSub T₁.perp R₂ hR2.1 hR2.2 with hR₂'
  set R₃' := hypPairToSub T₁.perp R₃ hR3.1 hR3.2 with hR₃'
  set T₂' := hypPairToSub T₁.perp T₂ hT2.1 hT2.2 with hT₂'
  have hR23' : R₂'.Orth R₃' := orth_hypPairToSub hR23 hR2.1 hR2.2 hR3.1 hR3.2
  obtain ⟨g', hg', hg'e, hg'f⟩ := exists_mem_elementaryGroup_hypPair hQ' hR23' R₂' T₂'
  obtain ⟨g₂, hg₂, hg₂v, hg₂e, hg₂f⟩ := exists_extension T₁ hg'
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_, ?_, ?_, ?_⟩
  · rw [LinearEquiv.mul_apply, hg₁e, hg₂e]
  · rw [LinearEquiv.mul_apply, hg₁f, hg₂f]
  · have h1 := hg₂v R₂'.e
    have h2 := congrArg Subtype.val hg'e
    rw [LinearEquiv.mul_apply]
    exact h1.trans h2
  · have h1 := hg₂v R₂'.f
    have h2 := congrArg Subtype.val hg'f
    rw [LinearEquiv.mul_apply]
    exact h1.trans h2

end CFSG.HardMathSupport.Dickson.Sec6.I1431.OrthL2

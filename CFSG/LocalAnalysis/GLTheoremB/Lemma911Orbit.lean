module

public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.LocalAnalysis.GLTheoremB.AltInvariant
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Tools
public import CFSG.RankThree.PartOne.FIVES.Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Action

variable {Q : Type*} [Group Q] {Γ : Type*} [Group Γ]

theorem map_mul_act (ρ : Γ →* MulAut Q) (γ δ : Γ) (K : Subgroup Q) :
    K.map (ρ (γ * δ)).toMonoidHom = (K.map (ρ δ).toMonoidHom).map (ρ γ).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp

theorem map_one_act (ρ : Γ →* MulAut Q) (K : Subgroup Q) : K.map (ρ 1).toMonoidHom = K := by
  have : (ρ 1).toMonoidHom = MonoidHom.id Q := by
    ext x
    simp
  rw [this, Subgroup.map_id]

@[expose] def stabSub (ρ : Γ →* MulAut Q) (K : Subgroup Q) : Subgroup Γ where
  carrier := {γ | K.map (ρ γ).toMonoidHom = K}
  mul_mem' := fun {a b} ha hb => by
    show K.map (ρ (a * b)).toMonoidHom = K
    rw [map_mul_act]
    have ha' : K.map (ρ a).toMonoidHom = K := ha
    have hb' : K.map (ρ b).toMonoidHom = K := hb
    rw [hb', ha']
  one_mem' := map_one_act ρ K
  inv_mem' := fun {a} ha => by
    show K.map (ρ a⁻¹).toMonoidHom = K
    have ha' : K.map (ρ a).toMonoidHom = K := ha
    calc K.map (ρ a⁻¹).toMonoidHom = (K.map (ρ a).toMonoidHom).map (ρ a⁻¹).toMonoidHom := by
          rw [ha']
      _ = K := by rw [← map_mul_act, inv_mul_cancel, map_one_act]

theorem mem_stabSub {ρ : Γ →* MulAut Q} {K : Subgroup Q} {γ : Γ} :
    γ ∈ stabSub ρ K ↔ K.map (ρ γ).toMonoidHom = K := Iff.rfl

@[expose] noncomputable def restr (ρ : Γ →* MulAut Q) (K : Subgroup Q) (γ : stabSub ρ K) :
    MulAut ↥K :=
  ((ρ γ).subgroupMap K).trans (MulEquiv.subgroupCongr γ.2)

@[expose] noncomputable def restrHom (ρ : Γ →* MulAut Q) (K : Subgroup Q) :
    stabSub ρ K →* MulAut ↥K where
  toFun := restr ρ K
  map_one' := by
    ext x
    show ρ ((1 : stabSub ρ K) : Γ) x = x
    simp
  map_mul' a b := by
    ext x
    show ρ ((a * b : stabSub ρ K) : Γ) x = ρ a (ρ b x)
    rw [Subgroup.coe_mul, map_mul]
    rfl

end Action

section Closure

variable {Q : Type*} [Group Q]

theorem le_iSup_conj_of_not_central {J W : Subgroup Q} (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hWJ : W ≤ J) (hnc : ∃ w ∈ W, ∃ hw : w ∈ J, (⟨w, hw⟩ : ↥J) ∉ Subgroup.center ↥J) :
    J ≤ ⨆ y ∈ J, W.map (MulAut.conj y).toMonoidHom := by
  set Ncl : Subgroup Q := ⨆ y ∈ J, W.map (MulAut.conj y).toMonoidHom with hNcl
  have hNJ : Ncl ≤ J := by
    refine iSup₂_le fun y hy => ?_
    rintro _ ⟨w, hw, rfl⟩
    exact J.mul_mem (J.mul_mem hy (hWJ hw)) (J.inv_mem hy)
  have hkey : ∀ g ∈ J, ∀ z ∈ Ncl, g * z * g⁻¹ ∈ Ncl := by
    intro g hg z hz
    have hmap : Ncl.map (MulAut.conj g).toMonoidHom ≤ Ncl := by
      rw [hNcl, Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hy => ?_
      rw [Subgroup.map_map]
      refine le_trans ?_ (le_iSup₂_of_le (g * y) (J.mul_mem hg hy) le_rfl)
      refine le_of_eq ?_
      congr 1
      ext x
      simp [mul_assoc]
    exact hmap ⟨z, hz, rfl⟩
  have hJN : J ≤ Subgroup.normalizer (Ncl : Set Q) := by
    intro g hg
    refine Subgroup.mem_normalizer_iff.2 fun z => ⟨hkey g hg z, fun hz => ?_⟩
    have := hkey g⁻¹ (J.inv_mem hg) _ hz
    simpa [mul_assoc] using this
  have hnorm : (Ncl.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).2 hJN
  rcases normal_le_center_or_eq_top' hJq (Ncl.subgroupOf J) with hc | htop
  · exfalso
    obtain ⟨w, hwW, hwJ, hwc⟩ := hnc
    apply hwc
    apply hc
    refine (Subgroup.mem_subgroupOf).2 ?_
    have hle1 : W.map (MulAut.conj (1 : Q)).toMonoidHom ≤ Ncl :=
      le_iSup₂_of_le (1 : Q) J.one_mem le_rfl
    exact hle1 ⟨w, hwW, by simp⟩
  · intro z hz
    have : (⟨z, hz⟩ : ↥J) ∈ Ncl.subgroupOf J := htop ▸ Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf).1 this

end Closure

section Lift

variable {Q : Type} [Group Q] [Finite Q] {Γ : Type} [Group Γ]

theorem exists_two_subgroup_of_stab (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut Q) {J : Subgroup Q}
    (hJ : IsComponentOf J ⊤) (hA7 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥S7.Alt7)) :
    ∃ W : Subgroup Q, W ≤ J ∧ IsPGroup 2 ↥W ∧
      (∀ γ ∈ stabSub ρ J, W.map (ρ γ).toMonoidHom = W) ∧
      J ≤ ⨆ y ∈ J, W.map (MulAut.conj y).toMonoidHom := by
  obtain ⟨e⟩ := hA7
  have hΓs : IsPGroup 3 ↥(stabSub ρ J) := hΓ.to_subgroup _
  set Ψ : stabSub ρ J →* MulAut (↥J ⧸ Subgroup.center ↥J) :=
    quotAutHom (Subgroup.center ↥J) (restrHom ρ J)
      (fun γ => Subgroup.map_center_eq (restrHom ρ J γ)) with hΨ
  have hΨmk : ∀ (γ : stabSub ρ J) (z : ↥J), Ψ γ (QuotientGroup.mk z) =
      QuotientGroup.mk (restrHom ρ J γ z) := fun γ z => quotAutHom_mk _ _ _ γ z
  have hR : IsPGroup 3 ↥Ψ.range := hΓs.of_surjective Ψ.rangeRestrict Ψ.rangeRestrict_surjective
  obtain ⟨Wq, hWb, hW2, hWinv⟩ := S7.exists_invariant_two_subgroup e Ψ.range hR
  set π : ↥J →* ↥J ⧸ Subgroup.center ↥J := QuotientGroup.mk' (Subgroup.center ↥J) with hπ
  have hcomap : ∀ γ : stabSub ρ J, (Wq.comap π).map (restrHom ρ J γ).toMonoidHom = Wq.comap π := by
    intro γ
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_comap, Subgroup.mem_comap]
    have h1 : (restrHom ρ J γ).symm = restrHom ρ J γ⁻¹ := by
      rw [map_inv]
      rfl
    rw [h1]
    constructor
    · intro hx
      have h2 : π (restrHom ρ J γ⁻¹ x) ∈ Wq := hx
      have h3 : Ψ γ (π (restrHom ρ J γ⁻¹ x)) ∈ Wq := hWinv (Ψ γ) ⟨γ, rfl⟩ ⟨_, h2, rfl⟩
      have h4 : Ψ γ (π (restrHom ρ J γ⁻¹ x)) = π x := by
        show Ψ γ (QuotientGroup.mk (restrHom ρ J γ⁻¹ x)) = QuotientGroup.mk x
        rw [hΨmk, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h4] at h3
      exact h3
    · intro hx
      have h3 : Ψ γ⁻¹ (π x) ∈ Wq := hWinv (Ψ γ⁻¹) ⟨γ⁻¹, rfl⟩ ⟨_, hx, rfl⟩
      have h4 : Ψ γ⁻¹ (π x) = π (restrHom ρ J γ⁻¹ x) := by
        show Ψ γ⁻¹ (QuotientGroup.mk x) = QuotientGroup.mk (restrHom ρ J γ⁻¹ x)
        rw [hΨmk]
      rw [h4] at h3
      exact h3
  obtain ⟨U, hU2, hUW, hUinv⟩ :=
    CFSG.RankThree.PartOne.FIVES.exists_lift_two_subgroup Wq hW2
  refine ⟨U.map J.subtype, Subgroup.map_subtype_le U, hU2.map _, ?_, ?_⟩
  · intro γ hγ
    have h1 := hUinv (restrHom ρ J ⟨γ, hγ⟩) (hcomap ⟨γ, hγ⟩)
    have hcomp : (ρ γ).toMonoidHom.comp J.subtype =
        J.subtype.comp (restrHom ρ J ⟨γ, hγ⟩).toMonoidHom := by
      ext x
      rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, h1]
  · refine le_iSup_conj_of_not_central hJ.2.2 (Subgroup.map_subtype_le U) ?_
    have : ∃ u ∈ U, π u ≠ 1 := by
      by_contra hno
      push Not at hno
      apply hWb
      rw [← hUW]
      refine eq_bot_iff.2 ?_
      rintro _ ⟨u, hu, rfl⟩
      exact (Subgroup.mem_bot).2 (hno u hu)
    obtain ⟨u, huU, hu1⟩ := this
    refine ⟨(u : Q), ⟨u, huU, rfl⟩, u.2, ?_⟩
    intro hc
    apply hu1
    exact (QuotientGroup.eq_one_iff u).2 hc

end Lift

section Main

variable {Q : Type} [Group Q] [Finite Q] {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_invariant_two_subgroup_generating (hΓ : IsPGroup 3 Γ) (ρ : Γ →* MulAut Q)
    {J : Subgroup Q} (hJ : IsComponentOf J ⊤)
    (hA7 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* ↥S7.Alt7)) :
    ∃ S : Subgroup Q, IsPGroup 2 ↥S ∧ S ≤ ⨆ γ : Γ, J.map (ρ γ).toMonoidHom ∧
      (∀ γ : Γ, S.map (ρ γ).toMonoidHom ≤ S) ∧
      (⨆ γ : Γ, J.map (ρ γ).toMonoidHom) ≤
        ⨆ y ∈ (⨆ γ : Γ, J.map (ρ γ).toMonoidHom), S.map (MulAut.conj y).toMonoidHom := by
  obtain ⟨W, hWJ, hW2, hWinv, hWcl⟩ := exists_two_subgroup_of_stab hΓ ρ hJ hA7
  have hcomp : ∀ γ : Γ, IsComponentOf (J.map (ρ γ).toMonoidHom) ⊤ := fun γ =>
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (ρ γ) J).2 hJ
  set Wg : Γ → Subgroup Q := fun γ => W.map (ρ γ).toMonoidHom with hWg
  have hWgJ : ∀ γ, Wg γ ≤ J.map (ρ γ).toMonoidHom := fun γ => Subgroup.map_mono hWJ
  have hW2g : ∀ γ, IsPGroup 2 ↥(Wg γ) := fun γ => hW2.map _
  have hpair : ∀ γ δ, Wg γ = Wg δ ∨ ⁅Wg γ, Wg δ⁆ = ⊥ := by
    intro γ δ
    by_cases hJeq : J.map (ρ γ).toMonoidHom = J.map (ρ δ).toMonoidHom
    · left
      have hstab : δ⁻¹ * γ ∈ stabSub ρ J := by
        rw [mem_stabSub, map_mul_act, hJeq, ← map_mul_act, inv_mul_cancel, map_one_act]
      have h1 := hWinv _ hstab
      show W.map (ρ γ).toMonoidHom = W.map (ρ δ).toMonoidHom
      calc W.map (ρ γ).toMonoidHom = W.map (ρ (δ * (δ⁻¹ * γ))).toMonoidHom := by
            rw [mul_inv_cancel_left]
        _ = (W.map (ρ (δ⁻¹ * γ)).toMonoidHom).map (ρ δ).toMonoidHom := map_mul_act ρ δ _ W
        _ = W.map (ρ δ).toMonoidHom := by rw [h1]
    · right
      exact eq_bot_iff.2 ((Subgroup.commutator_mono (hWgJ γ) (hWgJ δ)).trans
        (le_of_eq (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hcomp γ)
          (hcomp δ) hJeq)))
  set S : Subgroup Q := ⨆ γ : Γ, Wg γ with hS
  refine ⟨S, isPGroup_iSup_of_pairwise Wg hW2g hpair, iSup_mono fun γ => hWgJ γ, ?_, ?_⟩
  · intro γ
    rw [hS, Subgroup.map_iSup]
    refine iSup_le fun δ => ?_
    have h1 : (Wg δ).map (ρ γ).toMonoidHom = Wg (γ * δ) := (map_mul_act ρ γ δ W).symm
    rw [h1]
    exact le_iSup Wg (γ * δ)
  · refine iSup_le fun γ => ?_
    have h1 : J.map (ρ γ).toMonoidHom ≤
        ⨆ y ∈ J.map (ρ γ).toMonoidHom, (Wg γ).map (MulAut.conj y).toMonoidHom := by
      refine (Subgroup.map_mono (f := (ρ γ).toMonoidHom) hWcl).trans ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hy => ?_
      refine le_trans ?_ (le_iSup₂_of_le (ρ γ y) ⟨y, hy, rfl⟩ le_rfl)
      refine le_of_eq ?_
      rw [Subgroup.map_map, hWg]
      show W.map ((ρ γ).toMonoidHom.comp (MulAut.conj y).toMonoidHom) =
        (W.map (ρ γ).toMonoidHom).map (MulAut.conj (ρ γ y)).toMonoidHom
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp
    refine h1.trans ?_
    refine iSup₂_le fun y hy => ?_
    refine le_iSup₂_of_le y
      (le_iSup (fun γ => J.map (ρ γ).toMonoidHom) γ hy) ?_
    exact Subgroup.map_mono (le_iSup Wg γ)

end Main

end CFSG.LocalAnalysis.GLTheoremB

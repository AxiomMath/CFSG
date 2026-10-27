module

public import CFSG.Quasithin.Background.SmithCurtisBasic

public section

namespace CFSG.LieType.SpecialLinear

open CFSG.Quasithin.SmithCurtis

variable {k G W : Type*} [Field k] [Group G] [AddCommGroup W] [Module k W]
  {ρ : Representation k G W} {U : Subgroup G}

theorem exists_ne_zero_mem_fixSub (hfix : Module.finrank k (fixSub ρ U) = 1) :
    ∃ v : W, v ∈ fixSub ρ U ∧ v ≠ 0 := by
  have hnt : Nontrivial (fixSub ρ U) := Module.nontrivial_of_finrank_eq_succ hfix
  obtain ⟨v, hv⟩ := @exists_ne (fixSub ρ U) hnt 0
  exact ⟨v.1, v.2, fun h => hv (Subtype.ext h)⟩

theorem eq_smul_id_of_intertwines (hρ : IsSimpleRep ρ)
    (hfix : Module.finrank k (fixSub ρ U) = 1) (X : W →ₗ[k] W)
    (hX : ∀ g : G, X.comp (ρ g) = (ρ g).comp X) :
    ∃ c : k, X = c • LinearMap.id := by
  classical
  obtain ⟨v, hvfix, hvne⟩ := exists_ne_zero_mem_fixSub (ρ := ρ) (U := U) hfix
  have hXmem : ∀ w : W, w ∈ fixSub ρ U → X w ∈ fixSub ρ U := by
    intro w hw
    rw [mem_fixSub] at hw ⊢
    intro g hg
    have h := LinearMap.congr_fun (hX g) w
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hw g hg] at h
    exact h.symm
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hfix
    (x := ⟨v, hvfix⟩) (fun h => hvne (congrArg Subtype.val h)) ⟨X v, hXmem v hvfix⟩
  have hc' : X v = c • v := (congrArg Subtype.val hc).symm
  have hker : LinearMap.ker (X - c • LinearMap.id) ≠ ⊥ := by
    intro hbot
    have hmem : v ∈ LinearMap.ker (X - c • LinearMap.id) := by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hc',
        sub_self]
    rw [hbot] at hmem
    exact hvne (by simpa using hmem)
  have hstable : ∀ g : G, ∀ w ∈ LinearMap.ker (X - c • LinearMap.id),
      ρ g w ∈ LinearMap.ker (X - c • LinearMap.id) := by
    intro g w hw
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hw ⊢
    have h1 : X w = c • w := sub_eq_zero.mp hw
    have h2 : X (ρ g w) = ρ g (X w) := LinearMap.congr_fun (hX g) w
    rw [h2, h1, map_smul]
    exact sub_self _
  rcases hρ.2 (LinearMap.ker (X - c • LinearMap.id)) hstable with hbot | htop
  · exact absurd hbot hker
  · refine ⟨c, ?_⟩
    ext w
    have hw : w ∈ LinearMap.ker (X - c • LinearMap.id) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at hw
    rw [hw, LinearMap.smul_apply, LinearMap.id_apply]

theorem exists_smul_eq_of_intertwines_mulAut (hρ : IsSimpleRep ρ)
    (hfix : Module.finrank k (fixSub ρ U) = 1) {α : MulAut G} {X Y : W ≃ₗ[k] W}
    (hX : ∀ (g : G) (w : W), X (ρ g w) = ρ (α g) (X w))
    (hY : ∀ (g : G) (w : W), Y (ρ g w) = ρ (α g) (Y w)) :
    ∃ c : k, ∀ w : W, X w = c • Y w := by
  classical
  have hYinv : ∀ (g : G) (z : W), Y.symm (ρ (α g) z) = ρ g (Y.symm z) := by
    intro g z
    have h1 : Y (ρ g (Y.symm z)) = ρ (α g) z := by
      simpa using hY g (Y.symm z)
    calc Y.symm (ρ (α g) z) = Y.symm (Y (ρ g (Y.symm z))) := by rw [h1]
      _ = ρ g (Y.symm z) := Y.symm_apply_apply _
  have hcomm : ∀ g : G,
      (Y.symm.toLinearMap.comp X.toLinearMap).comp (ρ g) =
        (ρ g).comp (Y.symm.toLinearMap.comp X.toLinearMap) := by
    intro g
    ext w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hX g w, hYinv]
  obtain ⟨c, hc⟩ := eq_smul_id_of_intertwines hρ hfix
    (Y.symm.toLinearMap.comp X.toLinearMap) hcomm
  refine ⟨c, fun w => ?_⟩
  have h : Y.symm (X w) = c • w := by
    simpa using LinearMap.congr_fun hc w
  calc X w = Y (Y.symm (X w)) := (Y.apply_symm_apply (X w)).symm
    _ = Y (c • w) := by rw [h]
    _ = c • Y w := map_smul Y c w

theorem eq_of_mul_self_eq_one [CharP k 2] (hρ : IsSimpleRep ρ)
    (hfix : Module.finrank k (fixSub ρ U) = 1) {α : MulAut G} {X Y : W ≃ₗ[k] W}
    (hX : ∀ (g : G) (w : W), X (ρ g w) = ρ (α g) (X w))
    (hY : ∀ (g : G) (w : W), Y (ρ g w) = ρ (α g) (Y w))
    (hX2 : X * X = 1) (hY2 : Y * Y = 1) : X = Y := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_intertwines_mulAut hρ hfix hX hY
  obtain ⟨v, -, hvne⟩ := exists_ne_zero_mem_fixSub (ρ := ρ) (U := U) hfix
  have hXY : ∀ w : W, X w = c • Y w := hc
  have hsq : (c * c) • v = v := by
    have h1 : X (X v) = v := by
      rw [← LinearEquiv.mul_apply, hX2]; rfl
    have h2 : X (X v) = (c * c) • ((Y * Y) v) := by
      calc X (X v) = X (c • Y v) := by rw [hXY v]
        _ = c • X (Y v) := by rw [map_smul]
        _ = c • (c • Y (Y v)) := by rw [hXY (Y v)]
        _ = (c * c) • Y (Y v) := by rw [smul_smul]
        _ = (c * c) • ((Y * Y) v) := rfl
    have h3 : (Y * Y) v = v := by rw [hY2]; rfl
    rw [h1, h3] at h2
    exact h2.symm
  have hc1 : c * c = 1 := by
    have h : ((c * c) - 1) • v = 0 := by
      rw [sub_smul, one_smul, hsq, sub_self]
    rcases smul_eq_zero.1 h with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hvne
  have hc_eq : c = 1 := by
    rcases mul_self_eq_one_iff.mp hc1 with h | h
    · exact h
    · rw [CharTwo.neg_eq] at h
      exact h
  apply LinearEquiv.ext
  intro w
  rw [hXY w, hc_eq, one_smul]

end CFSG.LieType.SpecialLinear

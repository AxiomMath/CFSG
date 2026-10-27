module

public import CFSG.ClassicalGroups.Orthogonal.OmegaSiegelRoot

public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open QuadraticMap

variable {K : Type*} [Field K] [CharP K 2] {N : Type*} [AddCommGroup N] [Module K N]
  {Q : QuadraticForm K N}

omit [CharP K 2] in
private theorem exists_eichler_apply_eq_smul {a b x : N} (ha : Q a = 0) (hb : Q b = 0)
    (hab : polar Q a b = 1) (hx : Q x = 0) (hxa : polar Q x a ≠ 0) :
    ∃ (w : N) (μ : K), polar Q a w = 0 ∧ μ ≠ 0 ∧ eichler Q a w b = μ • x := by
  have hy : polar Q a ((polar Q x a)⁻¹ • x) = 1 := by
    rw [polar_smul_right_eq, polar_comm Q a x, inv_mul_cancel₀ hxa]
  have hQy : Q ((polar Q x a)⁻¹ • x) = Q b := by
    rw [map_smul_eq_sq, hx, hb, mul_zero]
  have key := eichler_apply_eq_of_polar_eq ha hQy.symm hab hy one_ne_zero
  refine ⟨_, _, ?_, inv_ne_zero hxa, key⟩
  rw [polar_smul_right_eq, polar_sub_right, hy, hab, sub_self, mul_zero]

private theorem eichler_apply_swap {e f h : N} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (heh : polar Q e h = 0) (hfh : polar Q f h = 0) (hh : Q h = 1) :
    eichler Q e h f = eichler Q f h e := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  rw [eichler_apply he heh, eichler_apply hf hfh, hfe, hef, hh, heh, hfh]
  simp only [one_smul, zero_add, mul_one]
  have h2 : (f + h - e) - (e + h - f) = (2 : K) • (f - e) := by module
  rw [CharTwo.two_eq_zero, zero_smul] at h2
  exact sub_eq_zero.mp h2

private theorem exists_mem_sup_apply_eq {e f h : N} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (heh : polar Q e h = 0) (hfh : polar Q f h = 0) (hh : Q h = 1) :
    ∃ g ∈ rootGroup Q e ⊔ rootGroup Q f, g f = e :=
  ⟨(eichler Q f h)⁻¹ * eichler Q e h,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (eichler_mem_rootGroup hfh)))
      (Subgroup.mem_sup_left (eichler_mem_rootGroup heh)),
    by rw [LinearEquiv.mul_apply, eichler_apply_swap he hf hef heh hfh hh,
      LinearEquiv.inv_apply_apply']⟩

private theorem orbit_of_polar_f {e f h x : N} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (heh : polar Q e h = 0) (hfh : polar Q f h = 0) (hh : Q h = 1)
    (hx : Q x = 0) (hxf : polar Q x f ≠ 0) :
    ∃ g ∈ rootGroup Q e ⊔ rootGroup Q f, ∃ μ : K, μ ≠ 0 ∧ g f = μ • x := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  obtain ⟨w, μ, hw, hμ, hwx⟩ := exists_eichler_apply_eq_smul hf he hfe hx hxf
  obtain ⟨g₀, hg₀, hg₀f⟩ := exists_mem_sup_apply_eq he hf hef heh hfh hh
  exact ⟨eichler Q f w * g₀, Subgroup.mul_mem _ (Subgroup.mem_sup_right
    (eichler_mem_rootGroup hw)) hg₀, μ, hμ, by rw [LinearEquiv.mul_apply, hg₀f, hwx]⟩

private theorem orbit_of_perp (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0)
    {e f h x : N} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (heh : polar Q e h = 0) (hfh : polar Q f h = 0) (hh : Q h = 1)
    (hx : Q x = 0) (hx0 : x ≠ 0) (hxe : polar Q x e = 0) (hxf : polar Q x f = 0) :
    ∃ g ∈ rootGroup Q e ⊔ rootGroup Q f, ∃ μ : K, μ ≠ 0 ∧ g f = μ • x := by
  have hfe : polar Q f e = 1 := by rw [polar_comm]; exact hef
  obtain ⟨y, hy⟩ : ∃ y, polar Q x y ≠ 0 := by
    by_contra! hy
    exact hx0 (hnd x hy)
  obtain ⟨w, hw⟩ : ∃ w, w = y - polar Q y f • e - polar Q y e • f := ⟨_, rfl⟩
  have hew : polar Q e w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero he, hef, polar_comm Q e y]
    ring
  have hfw : polar Q f w = 0 := by
    rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq,
      polar_self_eq_zero hf, hfe, polar_comm Q f y]
    ring
  have hxw : polar Q x w = polar Q x y := by
    rw [hw, polar_sub_right, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hxe, hxf]
    ring
  have hx₁ : eichler Q e w x = x - polar Q x y • e := by
    rw [eichler_apply he hew, hxe, hxw]
    simp
  have hQx₁ : Q (eichler Q e w x) = 0 := by
    rw [map_of_mem (eichler_mem_orthogonalGroup Q e w), hx]
  have hx₁f : polar Q (eichler Q e w x) f ≠ 0 := by
    rw [hx₁, polar_sub_left, polar_smul_left_eq, hxf, hef]
    simpa using hy
  obtain ⟨g, hg, μ, hμ, hgf⟩ := orbit_of_polar_f he hf hef heh hfh hh hQx₁ hx₁f
  refine ⟨(eichler Q e w)⁻¹ * g, Subgroup.mul_mem _ (Subgroup.inv_mem _
    (Subgroup.mem_sup_left (eichler_mem_rootGroup hew))) hg, μ, hμ, ?_⟩
  rw [LinearEquiv.mul_apply, hgf, map_smul, LinearEquiv.inv_apply_apply']

private theorem exists_mem_sup_apply_eq_smul (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0)
    {e f h x : N} (he : Q e = 0) (hf : Q f = 0)
    (hef : polar Q e f = 1) (heh : polar Q e h = 0) (hfh : polar Q f h = 0) (hh : Q h = 1)
    (hx : Q x = 0) (hx0 : x ≠ 0) :
    ∃ g ∈ rootGroup Q e ⊔ rootGroup Q f, ∃ μ : K, μ ≠ 0 ∧ g f = μ • x := by
  by_cases hxe : polar Q x e = 0
  · by_cases hxf : polar Q x f = 0
    · exact orbit_of_perp hnd he hf hef heh hfh hh hx hx0 hxe hxf
    · exact orbit_of_polar_f he hf hef heh hfh hh hx hxf
  · obtain ⟨w, μ, hw, hμ, hwf⟩ := exists_eichler_apply_eq_smul he hf hef hx hxe
    exact ⟨eichler Q e w, Subgroup.mem_sup_left (eichler_mem_rootGroup hw), μ, hμ, hwf⟩

omit [CharP K 2] in
private theorem eichler_mem_of_orbit {f : N} {H : Subgroup (N ≃ₗ[K] N)}
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hRf : rootGroup Q f ≤ H)
    (horb : ∀ x : N, Q x = 0 → x ≠ 0 → ∃ g ∈ H, ∃ μ : K, μ ≠ 0 ∧ g f = μ • x)
    {u w : N} (hu : Q u = 0) (hw : polar Q u w = 0) : eichler Q u w ∈ H := by
  by_cases hu0 : u = 0
  · rw [hu0, eichler_zero_left]
    exact H.one_mem
  obtain ⟨g, hg, μ, hμ, hgf⟩ := horb u hu hu0
  have hgO := hH hg
  have hgz : g (g⁻¹ (μ⁻¹ • w)) = μ⁻¹ • w := LinearEquiv.apply_inv_apply' g _
  have hfz : polar Q f (g⁻¹ (μ⁻¹ • w)) = 0 := by
    rw [← polar_map_of_mem hgO, hgf, hgz, polar_smul_left_eq, polar_smul_right_eq, hw]
    ring
  have hconj : eichler Q u w = g * eichler Q f (g⁻¹ (μ⁻¹ • w)) * g⁻¹ := by
    rw [eichler_conj hgO, hgf, hgz, eichler_smul_left, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  rw [hconj]
  exact H.mul_mem (H.mul_mem hg (hRf (eichler_mem_rootGroup hfz))) (H.inv_mem hg)

theorem elementaryGroup_le_rootGroup_sup (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0)
    {e f h : N} (he : Q e = 0) (hf : Q f = 0) (hef : polar Q e f = 1) (heh : polar Q e h = 0)
    (hfh : polar Q f h = 0) (hh : Q h = 1) :
    elementaryGroup Q ≤ rootGroup Q e ⊔ rootGroup Q f := by
  have hle : rootGroup Q e ⊔ rootGroup Q f ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sup_le ((rootGroup_le_elementaryGroup Q e).trans (elementaryGroup_le_orthogonalGroup Q))
      ((rootGroup_le_elementaryGroup Q f).trans (elementaryGroup_le_orthogonalGroup Q))
  refine elementaryGroup_le_of_eichler_mem fun u w hu hw => ?_
  exact eichler_mem_of_orbit hle le_sup_right
    (fun x hx hx0 => exists_mem_sup_apply_eq_smul hnd he hf hef heh hfh hh hx hx0) hu hw

omit [CharP K 2] in
private theorem polar_zero_symm {x y : N} (h : polar Q x y = 0) : polar Q y x = 0 :=
  (polar_comm Q y x).trans h

omit [CharP K 2] in
private def framePerp (Q : QuadraticForm K N) (e f p p' : N) : Submodule K N where
  carrier := {w | polar Q e w = 0 ∧ polar Q f w = 0 ∧ polar Q p w = 0 ∧ polar Q p' w = 0}
  add_mem' := by
    rintro a b ⟨h1, h2, h3, h4⟩ ⟨h1', h2', h3', h4'⟩
    exact ⟨by rw [polar_add_right, h1, h1', add_zero], by rw [polar_add_right, h2, h2', add_zero],
      by rw [polar_add_right, h3, h3', add_zero], by rw [polar_add_right, h4, h4', add_zero]⟩
  zero_mem' := ⟨polar_zero_right Q e, polar_zero_right Q f, polar_zero_right Q p,
    polar_zero_right Q p'⟩
  smul_mem' := by
    rintro c a ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [polar_smul_right_eq, h1, mul_zero], by rw [polar_smul_right_eq, h2, mul_zero],
      by rw [polar_smul_right_eq, h3, mul_zero], by rw [polar_smul_right_eq, h4, mul_zero]⟩

private theorem frame_commutator_step {a e f d : N} {Y : Subgroup (N ≃ₗ[K] N)}
    (ha : Q a = 0) (he : Q e = 0) (hf : Q f = 0) (hd : Q d = 0) (hef : polar Q e f = 1)
    (hae : polar Q a e = 0) (haf : polar Q a f = 0) (had : polar Q a d = 0)
    (hed : polar Q e d = 0) (hfd : polar Q f d = 0)
    (hYe : ∀ c : K, eichler Q a (c • e) ∈ Y) (hYd : eichler Q f d ∈ Y) (c : K) :
    eichler Q a (c • d) ∈ Y := by
  have hce : Q (c • e) = 0 := by rw [map_smul_eq_sq, he, mul_zero]
  have key := commutatorElement_eichler ha hce hf hd
    (by rw [polar_smul_right_eq, hae, mul_zero]) hfd haf had
    (by rw [polar_smul_left_eq, hed, mul_zero])
  rw [polar_smul_left_eq, hef, mul_one] at key
  rw [← key, commutatorElement_def]
  exact Y.mul_mem (Y.mul_mem (Y.mul_mem (hYe c) hYd) (Y.inv_mem (hYe c))) (Y.inv_mem hYd)

omit [CharP K 2] in
private theorem frame_decomp {u v p p' x : N} (hu : Q u = 0) (hp : Q p = 0) (hp' : Q p' = 0)
    (huv : polar Q u v = 1) (hpp' : polar Q p p' = 1) (hup : polar Q u p = 0)
    (hup' : polar Q u p' = 0) (hvp : polar Q v p = 0) (hvp' : polar Q v p' = 0)
    (hux : polar Q u x = 0) :
    ∃ (a b b' : K) (w : N), polar Q u w = 0 ∧ polar Q v w = 0 ∧ polar Q p w = 0 ∧
      polar Q p' w = 0 ∧ x = w + b • p + b' • p' + a • u := by
  have hvu : polar Q v u = 1 := (polar_comm Q v u).trans huv
  have hp'p : polar Q p' p = 1 := (polar_comm Q p' p).trans hpp'
  have hpu := polar_zero_symm hup
  have hp'u := polar_zero_symm hup'
  refine ⟨polar Q x v, polar Q x p', polar Q x p,
    x - polar Q x v • u - polar Q x p' • p - polar Q x p • p', ?_, ?_, ?_, ?_, by abel⟩
  · simp only [polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hu, hup, hup', hux]
    ring
  · simp only [polar_sub_right, polar_smul_right_eq, hvu, hvp, hvp', polar_comm Q v x]
    ring
  · simp only [polar_sub_right, polar_smul_right_eq, hpu, polar_self_eq_zero hp, hpp',
      polar_comm Q p x]
    ring
  · simp only [polar_sub_right, polar_smul_right_eq, hp'u, hp'p, polar_self_eq_zero hp',
      polar_comm Q p' x]
    ring

omit [CharP K 2] in
private theorem frame_rootGroup_le {u v p p' : N} {Y : Subgroup (N ≃ₗ[K] N)} (hu : Q u = 0)
    (hp : Q p = 0) (hp' : Q p' = 0) (huv : polar Q u v = 1) (hpp' : polar Q p p' = 1)
    (hup : polar Q u p = 0) (hup' : polar Q u p' = 0) (hvp : polar Q v p = 0)
    (hvp' : polar Q v p' = 0)
    (hYw : ∀ w, polar Q u w = 0 → polar Q v w = 0 → polar Q p w = 0 → polar Q p' w = 0 →
      eichler Q u w ∈ Y)
    (hYp : ∀ c : K, eichler Q u (c • p) ∈ Y) (hYp' : ∀ c : K, eichler Q u (c • p') ∈ Y) :
    rootGroup Q u ≤ Y := by
  intro g hg
  obtain ⟨x, hx, rfl⟩ := mem_rootGroup.mp hg
  obtain ⟨a, b, b', w, h1, h2, h3, h4, rfl⟩ :=
    frame_decomp hu hp hp' huv hpp' hup hup' hvp hvp' hx
  have hbp : polar Q u (b • p) = 0 := by rw [polar_smul_right_eq, hup, mul_zero]
  have hbp' : polar Q u (b' • p') = 0 := by rw [polar_smul_right_eq, hup', mul_zero]
  have hwb : polar Q u (w + b • p) = 0 := by rw [polar_add_right, h1, hbp, add_zero]
  rw [eichler_add_smul_self hu, ← eichler_mul hwb hbp', ← eichler_mul h1 hbp]
  exact Y.mul_mem (Y.mul_mem (hYw w h1 h2 h3 h4) (hYp b)) (hYp' b')

theorem elementaryGroup_le_of_frame (hnd : ∀ x : N, (∀ y, polar Q x y = 0) → x = 0)
    {e f p p' e₂ f₂ : N} (he : Q e = 0) (hf : Q f = 0) (hp : Q p = 0) (hp' : Q p' = 0)
    (he₂ : Q e₂ = 0) (hf₂ : Q f₂ = 0) (hef : polar Q e f = 1) (hpp' : polar Q p p' = 1)
    (he₂f₂ : polar Q e₂ f₂ = 1) (hep : polar Q e p = 0) (hep' : polar Q e p' = 0)
    (hfp : polar Q f p = 0) (hfp' : polar Q f p' = 0) (hee₂ : polar Q e e₂ = 0)
    (hfe₂ : polar Q f e₂ = 0) (hpe₂ : polar Q p e₂ = 0) (hp'e₂ : polar Q p' e₂ = 0)
    (hef₂ : polar Q e f₂ = 0) (hff₂ : polar Q f f₂ = 0) (hpf₂ : polar Q p f₂ = 0)
    (hp'f₂ : polar Q p' f₂ = 0) {Y : Subgroup (N ≃ₗ[K] N)}
    (hYe : ∀ w, polar Q e w = 0 → polar Q f w = 0 → polar Q p w = 0 → polar Q p' w = 0 →
      eichler Q e w ∈ Y)
    (hYp : ∀ c : K, eichler Q f (c • p) ∈ Y) (hYp' : ∀ c : K, eichler Q f (c • p') ∈ Y) :
    elementaryGroup Q ≤ Y := by
  have hfe : polar Q f e = 1 := (polar_comm Q f e).trans hef
  have step1 : ∀ w, Q w = 0 → polar Q e w = 0 → polar Q f w = 0 → polar Q p w = 0 →
      polar Q p' w = 0 → ∀ c : K, eichler Q w (c • p) ∈ Y ∧ eichler Q w (c • p') ∈ Y := by
    intro w hw hew hfw hpw hp'w c
    have hYew : ∀ c : K, eichler Q w (c • e) ∈ Y := fun c => by
      have hce : Q (c • e) = 0 := by rw [map_smul_eq_sq, he, mul_zero]
      rw [eichler_comm_of_singular hw hce (by rw [polar_smul_right_eq, polar_zero_symm hew,
        mul_zero]), eichler_smul_left]
      exact hYe (c • w) (by rw [polar_smul_right_eq, hew, mul_zero])
        (by rw [polar_smul_right_eq, hfw, mul_zero]) (by rw [polar_smul_right_eq, hpw, mul_zero])
        (by rw [polar_smul_right_eq, hp'w, mul_zero])
    exact ⟨frame_commutator_step hw he hf hp hef (polar_zero_symm hew) (polar_zero_symm hfw)
      (polar_zero_symm hpw) hep hfp hYew (by simpa using hYp 1) c,
      frame_commutator_step hw he hf hp' hef (polar_zero_symm hew) (polar_zero_symm hfw)
      (polar_zero_symm hp'w) hep' hfp' hYew (by simpa using hYp' 1) c⟩
  have hYe₂ : ∀ c : K, eichler Q e (c • e₂) ∈ Y := fun c => hYe (c • e₂)
    (by rw [polar_smul_right_eq, hee₂, mul_zero]) (by rw [polar_smul_right_eq, hfe₂, mul_zero])
    (by rw [polar_smul_right_eq, hpe₂, mul_zero]) (by rw [polar_smul_right_eq, hp'e₂, mul_zero])
  have hf₂1 := step1 f₂ hf₂ hef₂ hff₂ hpf₂ hp'f₂ 1
  rw [one_smul, one_smul] at hf₂1
  have hRe : rootGroup Q e ≤ Y := frame_rootGroup_le he hp hp' hef hpp' hep hep' hfp hfp' hYe
    (fun c => frame_commutator_step he he₂ hf₂ hp he₂f₂ hee₂ hef₂ hep (polar_zero_symm hpe₂)
      (polar_zero_symm hpf₂) hYe₂ hf₂1.1 c)
    (fun c => frame_commutator_step he he₂ hf₂ hp' he₂f₂ hee₂ hef₂ hep' (polar_zero_symm hp'e₂)
      (polar_zero_symm hp'f₂) hYe₂ hf₂1.2 c)
  have hYf : ∀ w, polar Q e w = 0 → polar Q f w = 0 → polar Q p w = 0 → polar Q p' w = 0 →
      eichler Q f w ∈ Y := by
    intro w h1 h2 h3 h4
    refine eichler_mem_of_forall_singular (H := framePerp Q e f p p') (e₂ := e₂) (f₂ := f₂)
      ⟨hee₂, hfe₂, hpe₂, hp'e₂⟩ ⟨hef₂, hff₂, hpf₂, hp'f₂⟩ he₂ hf₂ he₂f₂ (fun w hw => hw.2.1)
      (fun w hw hw0 => ?_) (show w ∈ framePerp Q e f p p' from ⟨h1, h2, h3, h4⟩)
    obtain ⟨h1, h2, h3, h4⟩ := hw
    have hYd : eichler Q p' w ∈ Y := by
      rw [eichler_comm_of_singular hp' hw0 h4]
      simpa using (step1 w hw0 h1 h2 h3 h4 1).2
    simpa using frame_commutator_step hf hp hp' hw0 hpp' hfp hfp' h2 h3 h4 hYp hYd 1
  have hRf : rootGroup Q f ≤ Y := frame_rootGroup_le hf hp hp' hfe hpp' hfp hfp' hep hep'
    (fun w h1 h2 h3 h4 => hYf w h2 h1 h3 h4) hYp hYp'
  have hh : Q (p + p') = 1 := by
    rw [QuadraticMap.map_add Q p p', hp, hp', hpp', zero_add, zero_add]
  exact (elementaryGroup_le_rootGroup_sup hnd he hf hef (by rw [polar_add_right, hep, hep',
    add_zero]) (by rw [polar_add_right, hfp, hfp', add_zero]) hh).trans (sup_le hRe hRf)

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

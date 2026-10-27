module

public import CFSG.ClassicalGroups.Alternating.I4SpPlaneConj

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

section Fix

variable [CharP K 2] [FiniteDimensional K N]

theorem app_eq_of_commute_planeGroup (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    {π : Submodule K N} (hπ : IsPlane BN π) {g : Gsp BN}
    (hg : ∀ h ∈ planeGroup hBN π, g * h = h * g) : ∀ x ∈ π, g.app x = x := by
  have hline : ∀ ℓ : Submodule K N, IsLine BN ℓ → ℓ ≤ π → ℓ.map g.lin = ℓ := by
    intro ℓ hℓ hℓπ
    have hmap : (planeGroup hBN ℓ).map (MulAut.conj g).toMonoidHom = planeGroup hBN ℓ := by
      ext h
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hkπ : k ∈ planeGroup hBN π := planeGroup_mono hBN hℓπ hk
        have hk' : g * k * g⁻¹ = k := by
          rw [hg k hkπ]
          group
        simpa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hk'] using hk
      · intro hh
        refine ⟨h, hh, ?_⟩
        have hhπ : h ∈ planeGroup hBN π := planeGroup_mono hBN hℓπ hh
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [hg h hhπ]
        group
    rw [map_planeGroup_conj hBN g ℓ] at hmap
    exact eq_of_planeGroup_eq hBN hBNnd (Or.inl (hℓ.map g)) (Or.inl hℓ) hmap
  have heig : ∀ x ∈ π, ∃ μ : K, g.app x = μ • x := by
    intro x hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0, ← Gsp.lin_apply]⟩
    obtain ⟨y, hyπ, hxy⟩ := exists_mem_linearIndependent_pair (σ := π) (by rw [hπ.2]; norm_num)
      hx hx0
    have hxyo : BN x y = 0 := hπ.1 x hx y hyπ
    have hfr : finrank K (Submodule.span K {x, y}) = 2 := by
      rw [← Matrix.range_cons_cons_empty x y ![], finrank_span_eq_card hxy, Fintype.card_fin]
    have hspan : ¬ π ≤ Submodule.span K {x, y} := by
      intro hle
      have h3 := Submodule.finrank_mono hle
      rw [hπ.2, hfr] at h3
      omega
    obtain ⟨w, hwπ, hw⟩ := SetLike.not_le_iff_exists.mp hspan
    have hxw : LinearIndependent K ![x, w] := by
      rw [LinearIndependent.pair_iff' hx0]
      intro a ha
      apply hw
      rw [← ha]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hxwo : BN x w = 0 := hπ.1 x hx w hwπ
    have hℓ₁ : IsLine BN (Submodule.span K {x, y}) := ⟨isotropic_span_pair hBN hxyo, hfr⟩
    have hℓ₂ : IsLine BN (Submodule.span K {x, w}) :=
      ⟨isotropic_span_pair hBN hxwo, by
        rw [← Matrix.range_cons_cons_empty x w ![], finrank_span_eq_card hxw, Fintype.card_fin]⟩
    have hle₁ : Submodule.span K {x, y} ≤ π := by
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hx
      · exact hyπ
    have hle₂ : Submodule.span K {x, w} ≤ π := by
      rw [Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact hx
      · exact hwπ
    have hx₁ : g.app x ∈ Submodule.span K {x, y} := by
      have := hline _ hℓ₁ hle₁
      rw [← this]
      exact ⟨x, Submodule.subset_span (by simp), rfl⟩
    have hx₂ : g.app x ∈ Submodule.span K {x, w} := by
      have := hline _ hℓ₂ hle₂
      rw [← this]
      exact ⟨x, Submodule.subset_span (by simp), rfl⟩
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hx₁
    obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp hx₂
    have hδ : δ = 0 := by
      by_contra hδ0
      apply hw
      have h1 : δ • w = (α - γ) • x + β • y := by
        rw [sub_smul]
        have := hαβ.trans hγδ.symm
        linear_combination (norm := module) -this
      have h2 : w = δ⁻¹ • ((α - γ) • x + β • y) := by
        rw [← h1, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))) (Submodule.smul_mem _ _
        (Submodule.subset_span (by simp))))
    refine ⟨γ, ?_⟩
    rw [← hγδ, hδ, zero_smul, add_zero]
  have hπmap : ∀ x ∈ π, g.lin x ∈ π := by
    intro x hx
    obtain ⟨μ, hμ⟩ := heig x hx
    rw [Gsp.lin_apply, hμ]
    exact π.smul_mem μ hx
  obtain ⟨a, ha⟩ : ∃ a : K, ∀ x ∈ π, g.app x = a • x := by
    obtain ⟨a, ha⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := g.lin.restrict hπmap) (fun v hv => by
        obtain ⟨μ, hμ⟩ := heig v v.2
        have hfv : g.lin.restrict hπmap v = μ • v := Subtype.ext hμ
        rw [LinearIndependent.pair_iff] at hv
        have := hv μ (-1) (by rw [hfv]; module)
        exact one_ne_zero (neg_eq_zero.mp this.2))
    refine ⟨a, fun x hx => ?_⟩
    have := congrArg (fun f : π →ₗ[K] π => (f ⟨x, hx⟩ : N)) ha
    simpa [Gsp.lin_apply] using this
  by_cases hπ0 : π = ⊥
  · have h3 := hπ.2
    rw [hπ0, finrank_bot] at h3
    omega
  obtain ⟨x, hxπ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ0
  obtain ⟨y, hyπ, hxy⟩ := exists_mem_linearIndependent_pair (σ := π) (by rw [hπ.2]; norm_num)
    hxπ hx0
  have hxyo : BN x y = 0 := hπ.1 x hxπ y hyπ
  have hcomm := hg _ (lineElt_mem_planeGroup hBN hxπ hyπ)
  have hconj : g * lineElt hBN x y * g⁻¹ = lineElt hBN x y := by
    rw [hcomm]
    group
  rw [conj_lineElt hBN, ha x hxπ, ha y hyπ] at hconj
  have hxay : BN x (a • y) = 0 := by rw [map_smul, hxyo, smul_zero]
  rw [lineElt_smul_left hBN hxay a] at hconj
  have hinj := lineHom_injective hBN hBNnd hxyo hxy
  have hsq : a * a = 1 := by
    have h1 : lineHom hBN hxyo (Multiplicative.ofAdd (a * a)) =
        lineHom hBN hxyo (Multiplicative.ofAdd 1) := by
      show lineElt hBN x ((a * a) • y) = lineElt hBN x ((1 : K) • y)
      rw [one_smul, mul_smul]
      exact hconj
    exact Multiplicative.ofAdd.injective (hinj h1)
  have ha1 : a = 1 := by
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact h
    · rw [h, CharTwo.neg_eq]
  intro z hz
  rw [ha z hz, ha1, one_smul]

end Fix

section Plane

variable [FiniteDimensional K N]

theorem exists_mem_orthogonal_notMem (hBNnd : BN.Nondegenerate) (h6 : 6 ≤ finrank K N)
    {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) : ∃ w, (∀ p ∈ ℓ, BN p w = 0) ∧ w ∉ ℓ := by
  by_contra hcon
  push Not at hcon
  have hle : BN.orthogonal ℓ ≤ ℓ := fun w hw => hcon w hw
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hBNnd, hℓ.2] at h1
  omega

theorem exists_isPlane_of_orthogonal (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h6 : 6 ≤ finrank K N) {ℓ : Submodule K N} (hℓ : IsLine BN ℓ) {z : N}
    (hz : ∀ p ∈ ℓ, BN p z = 0) :
    ∃ π : Submodule K N, IsPlane BN π ∧ ℓ ≤ π ∧ z ∈ π := by
  obtain ⟨w, hwperp, hwℓ, hzw⟩ : ∃ w, (∀ p ∈ ℓ, BN p w = 0) ∧ w ∉ ℓ ∧
      z ∈ ℓ ⊔ Submodule.span K {w} := by
    by_cases hzℓ : z ∈ ℓ
    · obtain ⟨w, hw, hwℓ⟩ := exists_mem_orthogonal_notMem hBNnd h6 hℓ
      exact ⟨w, hw, hwℓ, Submodule.mem_sup_left hzℓ⟩
    · exact ⟨z, hz, hzℓ, Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)⟩
  have hw0 : w ≠ 0 := fun h => hwℓ (h ▸ ℓ.zero_mem)
  refine ⟨ℓ ⊔ Submodule.span K {w}, ⟨?_, ?_⟩, le_sup_left, hzw⟩
  · intro x hx y hy
    obtain ⟨p, hp, s, hs, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', s', hs', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hs
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hs'
    have h1 : BN p p' = 0 := hℓ.1 p hp p' hp'
    have h2 : BN p w = 0 := hwperp p hp
    have h3 : BN w p' = 0 := by rw [← hBN.neg_eq p' w, hwperp p' hp', neg_zero]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1, h2,
      h3, hBN.self_eq_zero, mul_zero, add_zero]
  · have hinf : ℓ ⊓ Submodule.span K {w} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro v ⟨hvℓ, hvw⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvw
      by_cases hc : c = 0
      · rw [hc, zero_smul]
      · exfalso
        apply hwℓ
        have := ℓ.smul_mem c⁻¹ hvℓ
        rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    have h := Submodule.finrank_sup_add_finrank_inf_eq ℓ (Submodule.span K {w})
    rw [hinf, finrank_bot, hℓ.2, finrank_span_singleton hw0] at h
    omega

end Plane

section Combined

variable [CharP K 2] [FiniteDimensional K N]

theorem mem_lineGroup_of_commute_planeGroup (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
    (h6 : 6 ≤ finrank K N) {a c a' c' : N} (hac : BN a c = 0) (hind : LinearIndependent K ![a, c])
    (hac' : BN a' c' = 0) (hind' : LinearIndependent K ![a', c'])
    (hg : ∀ π : Submodule K N, IsPlane BN π → Submodule.span K {a, c} ≤ π →
      ∀ h ∈ planeGroup hBN π, lineElt hBN a' c' * h = h * lineElt hBN a' c') :
    lineElt hBN a' c' ∈ lineGroup hBN a c := by
  have hfr : finrank K (Submodule.span K {a, c}) = 2 := by
    rw [← Matrix.range_cons_cons_empty a c ![], finrank_span_eq_card hind, Fintype.card_fin]
  have hℓ : IsLine BN (Submodule.span K {a, c}) := ⟨isotropic_span_pair hBN hac, hfr⟩
  have hfix : ∀ z, (∀ p ∈ Submodule.span K {a, c}, BN p z = 0) →
      (lineElt hBN a' c').app z = z := by
    intro z hz
    obtain ⟨π, hπ, hℓπ, hzπ⟩ := exists_isPlane_of_orthogonal hBN hBNnd h6 hℓ hz
    exact app_eq_of_commute_planeGroup hBN hBNnd hπ (hg π hπ hℓπ) z hzπ
  have horth : ∀ z, (∀ p ∈ Submodule.span K {a, c}, BN p z = 0) →
      BN z a' = 0 ∧ BN z c' = 0 := by
    intro z hz
    have h1 := hfix z hz
    rw [lineElt_app hBN hac'] at h1
    have h2 : BN z a' • c' + BN z c' • a' = 0 := by
      have := congrArg (fun v => v - z) h1
      simpa [add_assoc] using this
    have h3 := hind'.eq_zero_of_pair (s := BN z c') (t := BN z a') (by
      rw [add_comm]
      exact h2)
    exact ⟨h3.2, h3.1⟩
  have hmem : ∀ v : N, (∀ z, (∀ p ∈ Submodule.span K {a, c}, BN p z = 0) → BN z v = 0) →
      v ∈ Submodule.span K {a, c} := by
    intro v hv
    have : v ∈ BN.orthogonal (BN.orthogonal (Submodule.span K {a, c})) := fun z hz => hv z hz
    rwa [LinearMap.BilinForm.orthogonal_orthogonal hBNnd hBN.isRefl] at this
  have ha' : a' ∈ Submodule.span K {a, c} := hmem a' fun z hz => (horth z hz).1
  have hc' : c' ∈ Submodule.span K {a, c} := hmem c' fun z hz => (horth z hz).2
  have hle : Submodule.span K {a', c'} ≤ Submodule.span K {a, c} := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ha'
    · exact hc'
  have hfr' : finrank K (Submodule.span K {a', c'}) = 2 := by
    rw [← Matrix.range_cons_cons_empty a' c' ![], finrank_span_eq_card hind', Fintype.card_fin]
  have hspan : Submodule.span K {a', c'} = Submodule.span K {a, c} :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hfr, hfr'])
  rw [← lineGroup_eq_of_span_eq hBN hac' hac hspan]
  exact (mem_lineGroup_iff hBN hac').mpr ⟨1, by rw [one_smul]⟩

end Combined

end CFSG.ClassicalGroups.Alternating

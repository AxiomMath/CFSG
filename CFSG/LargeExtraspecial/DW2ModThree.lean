module

public import CFSG.LargeExtraspecial.DW2ModOne
public import CFSG.LargeExtraspecial.S12Good
public import CFSG.LargeExtraspecial.OrthoF2Fixed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem map_iterComm_le {X : Subgroup (V ≃ₗ[ZMod 2] V)} {γ : V →ₗ[ZMod 2] V}
    (hγ : ∀ x ∈ X, ∀ v, γ (x v) = x (γ v)) (W : Submodule (ZMod 2) V) (k : ℕ) :
    (iterComm X W k).map γ ≤ iterComm X (W.map γ) k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [iterComm_succ', iterComm_succ', map_le_iff_le_comap]
    refine commSub_le_iff.mpr fun x hx w hw => ?_
    rw [mem_comap, map_sub, hγ x hx]
    exact sub_mem_commSub hx (ih (mem_map_of_mem hw))

theorem fixed_mod_or_commSpace_le [FiniteDimensional (ZMod 2) V] {d : V ≃ₗ[ZMod 2] V}
    {U R : Submodule (ZMod 2) V} (hdU : ∀ u ∈ U, d u ∈ U)
    (hd2 : finrank (ZMod 2) ↥(commSpace d) = 2) (hnt : ∃ u ∈ U, d u - u ∉ R) :
    (∀ c : V ≃ₗ[ZMod 2] V, c * d = d * c → (∀ u ∈ U, c u ∈ U) → (∀ r ∈ R, c⁻¹ r ∈ R) →
        ∃ u₀ ∈ U, u₀ ∉ R ∧ c u₀ - u₀ ∈ R) ∨
      (commSpace d ≤ U ∧ commSpace d ⊓ R = ⊥) := by
  set γ : V →ₗ[ZMod 2] V := (d : V →ₗ[ZMod 2] V) - 1 with hγ
  have hγa : ∀ v, γ v = d v - v := fun v => by simp [hγ]
  set M := U.map γ with hM
  have hMd : M ≤ commSpace d := LinearMap.map_le_range
  have hMU : M ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hγa]
    exact sub_mem (hdU u hu) hu
  obtain ⟨u₁, hu₁, hu₁R⟩ := hnt
  have hu₀M : d u₁ - u₁ ∈ M := ⟨u₁, hu₁, hγa u₁⟩
  by_cases h1 : finrank (ZMod 2) ↥(M ⊔ R) = finrank (ZMod 2) R + 1
  · left
    intro c hcd hcU hcR
    have hspan : R ⊔ span (ZMod 2) {d u₁ - u₁} = M ⊔ R := by
      apply Submodule.eq_of_le_of_finrank_eq
      · exact sup_le le_sup_right
          (span_le.mpr (Set.singleton_subset_iff.mpr (mem_sup_left hu₀M)))
      · rw [h1, Submodule.finrank_sup_span_singleton hu₁R]
    have hcM : c (d u₁ - u₁) ∈ M := by
      refine ⟨c u₁, hcU u₁ hu₁, ?_⟩
      rw [hγa, map_sub, ← LinearEquiv.mul_apply, ← hcd, LinearEquiv.mul_apply]
    have hmem : c (d u₁ - u₁) ∈ R ⊔ span (ZMod 2) {d u₁ - u₁} := hspan ▸ mem_sup_left hcM
    obtain ⟨r, hr, w, hw, hrw⟩ := mem_sup.mp hmem
    obtain ⟨a, rfl⟩ := mem_span_singleton.mp hw
    refine ⟨d u₁ - u₁, hMU hu₀M, hu₁R, ?_⟩
    rcases zmod2_cases a with rfl | rfl
    · exfalso
      rw [zero_smul, add_zero] at hrw
      apply hu₁R
      have h := hcR r hr
      rw [hrw] at h
      simpa using h
    · rw [one_smul] at hrw
      rw [← hrw, add_sub_cancel_right]
      exact hr
  · right
    have hlt : R < M ⊔ R := lt_of_le_of_ne le_sup_right fun h => hu₁R (h ▸ mem_sup_left hu₀M)
    have h2 := Submodule.finrank_lt_finrank_of_lt hlt
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq M R
    have h4 := Submodule.finrank_mono hMd
    rw [hd2] at h4
    have h5 : finrank (ZMod 2) ↥(M ⊓ R) = 0 := by omega
    have hMeq : M = commSpace d := Submodule.eq_of_le_of_finrank_eq hMd (by omega)
    rw [← hMeq]
    exact ⟨hMU, Submodule.finrank_eq_zero.mp h5⟩

variable [FiniteDimensional (ZMod 2) V] {Y X : Subgroup (V ≃ₗ[ZMod 2] V)}
  {f : LinearMap.BilinForm (ZMod 2) V}

theorem exists_regular_of_oneFactor (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) (hO2 : S12NoNormalTwo Y)
    (hfix : ∀ v, (∀ y ∈ Y, y v = v) → v = 0) (hXY : X ≤ Y)
    (hXn : Y ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : ∀ y ∈ Y, ∃ k : ℕ, ∃ x ∈ X, ∃ c ∈ Y, (∀ x' ∈ X, c * x' = x' * c) ∧ y ^ 2 ^ k = x * c)
    {d e : V ≃ₗ[ZMod 2] V} (hd : d ∈ X) (he : e ∈ X) (hd2 : finrank (ZMod 2) ↥(commSpace d) = 2)
    (he2 : finrank (ZMod 2) ↥(commSpace e) = 2)
    (hde : finrank (ZMod 2) ↥(commSpace d ⊓ commSpace e) = 1) (h1 : OneFactor X)
    (hprop : commSub X ⊤ ≠ ⊤) :
    ∃ W : Submodule (ZMod 2) V, IsInv Y W ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧ rad f W = ⊥ ∧ stab X ⊤ ≤ W := by
  classical
  have := finite_linearEquiv (V := V)
  have hXle : X ≤ TauCeti.BilinForm.isometryGroup f := hXY.trans hY
  have hconj : ∀ y ∈ Y, ∀ x ∈ X, y * x * y⁻¹ ∈ X := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hXn hy) x).mp hx
  set U := stab X ⊤ with hUdef
  have hUY : IsInv Y U := fun y hy => apply_mem_iterComm (hconj y hy) (fun _ _ => mem_top) _
  have hUX : IsInv X U := isInv_stab isInv_top
  have hRY : IsInv Y (rad f U) := hUY.inf (isInv_orth hY hUY)
  have hRX : IsInv X (rad f U) := hUX.inf (isInv_orth hXle hUX)
  have hRu : IsUnip X ⊥ (rad f U) := isUnip_rad_stab hf hr hXle h1
  have hF : IsNontrivFactor X (rad f U) U := isNontrivFactor_rad_stab hf hr hXle h1
  have hnu : ¬ IsUnip X ⊥ U := not_isUnip_stab h1.not_isUnip
  have hU0 : U ≠ ⊥ := fun h => hnu (by rw [h]; exact isUnip_self ⊥)
  have hX2 : S12NoNormalTwo X := hO2.of_normal hXY hXn
  have hfaith : ∀ x ∈ X, (∀ u ∈ U, x u - u ∈ rad f U) → x = 1 := by
    intro x hx hxU
    set K := X ⊓ secCent (rad f U) U with hK
    have hKu : IsUnip K ⊥ ⊤ :=
      ((hRu.mono_left inf_le_left).trans
        (isUnip_of_commSub_le (commSub_le_of_le_secCent inf_le_right))).trans
        ((isUnip_stab ⊤).mono_left inf_le_left)
    have hKn : X ≤ Subgroup.normalizer (K : Set (V ≃ₗ[ZMod 2] V)) := by
      intro x' hx'
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · rintro ⟨hkX, hkS⟩
        exact ⟨X.mul_mem (X.mul_mem hx' hkX) (X.inv_mem hx'), conj_mem_secCent hRX hUX hx' hkS⟩
      · rintro ⟨hkX, hkS⟩
        have hk : k = x'⁻¹ * (x' * k * x'⁻¹) * x'⁻¹⁻¹ := by group
        rw [hk]
        exact ⟨X.mul_mem (X.mul_mem (X.inv_mem hx') hkX) (X.inv_mem (X.inv_mem hx')),
          conj_mem_secCent hRX hUX (X.inv_mem hx') hkS⟩
    have hK1 := hX2 K inf_le_left (isPGroup_of_isUnip hKu) hKn
    have hxK : x ∈ K := ⟨hx, mem_secCent_of_isInv hUX hx hxU⟩
    rw [hK1, Subgroup.mem_bot] at hxK
    exact hxK
  have hnt : ∀ t ∈ X, finrank (ZMod 2) ↥(commSpace t) = 2 → ∃ u ∈ U, t u - u ∉ rad f U := by
    intro t ht ht2
    by_contra hcon
    push Not at hcon
    have h1t := hfaith t ht hcon
    subst h1t
    have hc1 : commSpace (1 : V ≃ₗ[ZMod 2] V) = ⊥ := by
      refine eq_bot_iff.mpr fun v hv => ?_
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
      simp
    rw [hc1, finrank_bot] at ht2
    omega
  have hCU : ∀ c ∈ Y, (∀ x ∈ X, c * x = x * c) → ∀ u ∈ U, c u - u ∈ rad f U := by
    intro c hcY hcX
    have hcU : ∀ u ∈ U, c u ∈ U := hUY c hcY
    have hcR : ∀ r ∈ rad f U, c⁻¹ r ∈ rad f U := fun r hr => hRY.inv_apply_mem hcY hr
    have hu₀ : ∃ u₀ ∈ U, u₀ ∉ rad f U ∧ c u₀ - u₀ ∈ rad f U := by
      rcases fixed_mod_or_commSpace_le (hUX d hd) hd2 (hnt d hd hd2) with hA | ⟨hdU, hdR⟩
      · exact hA c (hcX d hd) hcU hcR
      rcases fixed_mod_or_commSpace_le (hUX e he) he2 (hnt e he he2) with hA | -
      · exact hA c (hcX e he) hcU hcR
      obtain ⟨l, hl, hl0, hlu⟩ := exists_unique_ne_zero_of_finrank_eq_one hde
      have hcl : c l = l := by
        refine hlu _ ⟨apply_mem_commSpace_of_commute (hcX d hd) hl.1,
          apply_mem_commSpace_of_commute (hcX e he) hl.2⟩ ?_
        intro h
        exact hl0 (c.injective (h.trans (map_zero c).symm))
      refine ⟨l, hdU hl.1, fun hlR => hl0 ?_, by rw [hcl, sub_self]; exact zero_mem _⟩
      have hmem : l ∈ commSpace d ⊓ rad f U := ⟨hl.1, hlR⟩
      rw [hdR, mem_bot] at hmem
      exact hmem
    obtain ⟨u₀, hu₀U, hu₀R, hcu₀⟩ := hu₀
    set Fc : Submodule (ZMod 2) V := U ⊓ (rad f U).comap ((c : V →ₗ[ZMod 2] V) - 1) with hFc
    have hmemFc : ∀ v, v ∈ Fc ↔ v ∈ U ∧ c v - v ∈ rad f U := fun v => by simp [hFc]
    have hFcX : IsInv X Fc := by
      intro x hx v hv
      rw [hmemFc] at hv ⊢
      refine ⟨hUX x hx v hv.1, ?_⟩
      have h : c (x v) - x v = x (c v - v) := by
        rw [map_sub, ← LinearEquiv.mul_apply, hcX x hx, LinearEquiv.mul_apply]
      rw [h]
      exact hRX x hx _ hv.2
    have hRFc : rad f U ≤ Fc := fun r hr =>
      (hmemFc r).mpr ⟨hF.2.2.1 hr, sub_mem (hRY c hcY r hr) hr⟩
    rcases hF.2.2.2.2 Fc hFcX hRFc inf_le_left with h | h
    · exact absurd (h ▸ (hmemFc u₀).mpr ⟨hu₀U, hcu₀⟩) hu₀R
    · intro u hu
      exact ((hmemFc u).mp (h ▸ hu)).2
  obtain ⟨kR, hkR⟩ := id hRu
  have hCU' : ∀ c ∈ Y, (∀ x ∈ X, c * x = x * c) → ∀ u ∈ U, c u = u := by
    intro c hcY hcX u hu
    set γ : V →ₗ[ZMod 2] V := (c : V →ₗ[ZMod 2] V) - 1 with hγdef
    have hγa : ∀ v, γ v = c v - v := fun v => by simp [hγdef]
    have hγ : ∀ x ∈ X, ∀ v, γ (x v) = x (γ v) := by
      intro x hx v
      rw [hγa, hγa, map_sub, ← LinearEquiv.mul_apply, hcX x hx, LinearEquiv.mul_apply]
    have hmap : U.map γ ≤ rad f U := map_le_iff_le_comap.mpr fun u hu => by
      rw [mem_comap, hγa]
      exact hCU c hcY hcX u hu
    have h0 : U.map γ ≤ ⊥ :=
      calc U.map γ = (iterComm X U kR).map γ := by rw [iterComm_stab isInv_top]
        _ ≤ iterComm X (U.map γ) kR := map_iterComm_le hγ U kR
        _ ≤ iterComm X (rad f U) kR := iterComm_mono hmap kR
        _ ≤ ⊥ := hkR
    have h3 := h0 (mem_map_of_mem hu)
    rw [mem_bot, hγa, sub_eq_zero] at h3
    exact h3
  have hpow : ∀ S : Submodule (ZMod 2) V, IsUnip X ⊥ S →
      (∀ c ∈ Y, (∀ x ∈ X, c * x = x * c) → ∀ s ∈ S, c s = s) →
      ∀ y ∈ Y, ∃ j : ℕ, ∀ s ∈ S, (y ^ 2 ^ j) s = s := by
    intro S hS hC y hy
    obtain ⟨k, x, hx, c, hcY, hcX, hyk⟩ := h2 y hy
    obtain ⟨j, hj⟩ := exists_pow_sub_mem isInv_bot hS hx
    refine ⟨k + j, fun s hs => ?_⟩
    have hcomm : Commute x c := (hcX x hx).symm
    have hcs : ∀ m : ℕ, (c ^ m) s = s := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hC c hcY hcX s hs]
    have hxs := hj s hs
    rw [mem_bot, sub_eq_zero] at hxs
    rw [pow_add, pow_mul, hyk, hcomm.mul_pow, LinearEquiv.mul_apply, hcs, hxs]
  by_cases hC : ∀ c ∈ Y, (∀ x ∈ X, c * x = x * c) → c = 1
  · refine ⟨U, hUY, hU0, ?_, ?_, le_rfl⟩
    · intro hUtop
      apply hprop
      have hle : U ≤ commSub X ⊤ := by
        rw [hUdef, ← iterComm_eq_stab isInv_top (le_max_right 1 (finrank (ZMod 2) V)),
          ← iterComm_one]
        exact iterComm_antitone isInv_top (le_max_left _ _)
      rw [hUtop] at hle
      exact eq_top_iff.mpr hle
    · by_contra hR0
      obtain ⟨r, -, hr0, hrfix⟩ := exists_fixed_of_pow hRY hR0
        (hpow _ hRu fun c hcY hcX s _ => by rw [hC c hcY hcX]; rfl)
      exact hr0 (hfix r hrfix)
  · push Not at hC
    obtain ⟨c₀, hc₀Y, hc₀X, hc₀1⟩ := hC
    set C : Subgroup (V ≃ₗ[ZMod 2] V) := Subgroup.centralizer (X : Set (V ≃ₗ[ZMod 2] V)) ⊓ Y
      with hCdef
    have hmemC : ∀ c, c ∈ C ↔ c ∈ Y ∧ ∀ x ∈ X, c * x = x * c := fun c => by
      rw [hCdef, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, fun x hx => (h₁ x hx).symm⟩,
        fun ⟨h₁, h₂⟩ => ⟨fun x hx => (h₂ x hx).symm, h₁⟩⟩
    set W := fixSpaceOf C with hWdef
    have hWY : IsInv Y W := by
      intro y hy v hv a ha
      have haC := (hmemC a).mp ha
      have hyay : y⁻¹ * a * y ∈ C := by
        refine (hmemC _).mpr ⟨Y.mul_mem (Y.mul_mem (Y.inv_mem hy) haC.1) hy, fun x hx => ?_⟩
        have hx' := hconj y hy x hx
        calc y⁻¹ * a * y * x = y⁻¹ * (a * (y * x * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * x * y⁻¹) * a) * y := by rw [haC.2 _ hx']
          _ = x * (y⁻¹ * a * y) := by group
      have h : a (y v) = y ((y⁻¹ * a * y) v) := by
        rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
        congr 1
        group
      rw [h, hv _ hyay]
    have hUW : U ≤ W := fun u hu a ha => hCU' a ((hmemC a).mp ha).1 ((hmemC a).mp ha).2 u hu
    refine ⟨W, hWY, fun h => hU0 (le_bot_iff.mp (h ▸ hUW)), ?_, ?_, hUW⟩
    · intro hWtop
      apply hc₀1
      refine LinearEquiv.ext fun v => ?_
      have hv : v ∈ W := hWtop ▸ mem_top
      exact hv c₀ ((hmemC c₀).mpr ⟨hc₀Y, hc₀X⟩)
    · have hRWY : IsInv Y (rad f W) := hWY.inf (isInv_orth hY hWY)
      have hRWX : IsInv X (rad f W) := fun x hx => hRWY x (hXY hx)
      have hiso : rad f W ≤ f.orthogonal (rad f W) := fun v hv =>
        LinearMap.BilinForm.mem_orthogonal_iff.mpr fun w hw =>
          LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2 w hw.1
      have hRWu : IsUnip X ⊥ (rad f W) := by
        rcases h1.dichotomy hRWX bot_le le_top with h | h
        · exact h
        · exact (isUnip_orth_top_iff hf hr hXle).mp (h.mono hiso le_rfl)
      by_contra hR0
      obtain ⟨r, -, hr0, hrfix⟩ := exists_fixed_of_pow hRWY hR0
        (hpow _ hRWu fun c hcY hcX s hs => hs.1 c ((hmemC c).mpr ⟨hcY, hcX⟩))
      exact hr0 (hfix r hrfix)

theorem dw2_2_3 (hf : f.Nondegenerate) (hr : f.IsRefl)
    (hY : Y ≤ TauCeti.BilinForm.isometryGroup f) (hO2 : S12NoNormalTwo Y)
    (hfix : ∀ v, (∀ y ∈ Y, y v = v) → v = 0) (hXY : X ≤ Y)
    (hXn : Y ≤ Subgroup.normalizer (X : Set (V ≃ₗ[ZMod 2] V)))
    (h2 : ∀ y ∈ Y, ∃ k : ℕ, ∃ x ∈ X, ∃ c ∈ Y, (∀ x' ∈ X, c * x' = x' * c) ∧ y ^ 2 ^ k = x * c)
    {d e : V ≃ₗ[ZMod 2] V} (hd : d ∈ X) (he : e ∈ X) (hd2 : IsSpTypeA f d 2)
    (he2 : IsSpTypeA f e 2) (hne : commSpace d ⊓ commSpace e ≠ ⊥)
    (hne' : commSpace d ⊓ commSpace e ≠ commSpace d) (h1 : OneFactor X)
    (hprop : commSub X ⊤ ≠ ⊤) :
    ∃ W : Submodule (ZMod 2) V, IsInv Y W ∧ W ≠ ⊥ ∧ W ≠ ⊤ ∧ rad f W = ⊥ ∧ stab X ⊤ ≤ W := by
  have hde : finrank (ZMod 2) ↥(commSpace d ⊓ commSpace e) = 1 := by
    have h3 := Submodule.one_le_finrank_iff.mpr hne
    have h4 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne')
    have h5 := hd2.2.2.2.1
    omega
  exact exists_regular_of_oneFactor hf hr hY hO2 hfix hXY hXn h2 hd he hd2.2.2.2.1
    he2.2.2.2.1 hde h1 hprop

end CFSG.LargeExtraspecial.DW

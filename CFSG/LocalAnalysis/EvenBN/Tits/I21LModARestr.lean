module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LUna

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Module Subgroup

section Stab

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def modA_stab (M : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | Stable g M ∧ Stable g⁻¹ M}
  mul_mem' := fun {g h} hg hh => ⟨fun u hu => hg.1 _ (hh.1 u hu), fun u hu => by
    rw [mul_inv_rev]
    exact hh.2 _ (hg.2 u hu)⟩
  one_mem' := ⟨fun u hu => hu, fun u hu => by simpa using hu⟩
  inv_mem' := fun {g} hg => ⟨hg.2, by simpa using hg.1⟩

@[expose] def modA_restr (M : Submodule (ZMod 2) V) : modA_stab M →* (M ≃ₗ[ZMod 2] M) where
  toFun g :=
    { toFun := fun u => ⟨(g : V ≃ₗ[ZMod 2] V) u, g.2.1 u u.2⟩
      invFun := fun u => ⟨(g : V ≃ₗ[ZMod 2] V)⁻¹ u, g.2.2 u u.2⟩
      map_add' := fun u v => Subtype.ext (map_add _ _ _)
      map_smul' := fun c u => Subtype.ext (map_smul _ _ _)
      left_inv := fun u => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  map_one' := LinearEquiv.ext fun u => Subtype.ext rfl
  map_mul' := fun g h => LinearEquiv.ext fun u => Subtype.ext rfl

theorem modA_restr_apply (M : Submodule (ZMod 2) V) (g : modA_stab M) (u : M) :
    ((modA_restr M g u : M) : V) = (g : V ≃ₗ[ZMod 2] V) u := rfl

theorem modA_le_stab {J : Subgroup (V ≃ₗ[ZMod 2] V)} {M : Submodule (ZMod 2) V}
    (hM : ∀ g ∈ J, Stable g M) : J ≤ modA_stab M :=
  fun g hg => ⟨hM g hg, hM g⁻¹ (J.inv_mem hg)⟩

@[expose] def modA_resJ (J : Subgroup (V ≃ₗ[ZMod 2] V)) (M : Submodule (ZMod 2) V)
    (hM : ∀ g ∈ J, Stable g M) : J →* (M ≃ₗ[ZMod 2] M) :=
  (modA_restr M).comp (Subgroup.inclusion (modA_le_stab hM))

theorem modA_resJ_apply (J : Subgroup (V ≃ₗ[ZMod 2] V)) (M : Submodule (ZMod 2) V)
    (hM : ∀ g ∈ J, Stable g M) (g : J) (u : M) :
    ((modA_resJ J M hM g u : M) : V) = (g : V ≃ₗ[ZMod 2] V) u := rfl

theorem modA_mem_stab_of_map_eq {g : V ≃ₗ[ZMod 2] V} {M : Submodule (ZMod 2) V}
    (h : M.map (g : V →ₗ[ZMod 2] V) = M) : g ∈ modA_stab M := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [← h]
    exact ⟨u, hu, rfl⟩
  · rw [← h] at hu
    obtain ⟨m, hm, rfl⟩ := hu
    simpa using hm

end Stab

section Rank

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

theorem modA_rk_one : rk (1 : V ≃ₗ[ZMod 2] V) = 0 := by
  unfold rk
  have : nu (1 : V ≃ₗ[ZMod 2] V) = 0 := by
    ext v
    simp [nu_apply]
  rw [this]
  simp

theorem modA_eq_one_of_rk_zero {g : V ≃ₗ[ZMod 2] V} (h : rk g = 0) : g = 1 := by
  have h0 : LinearMap.range (nu g) = ⊥ := Submodule.finrank_eq_zero.mp h
  refine LinearEquiv.ext fun v => ?_
  have hv : nu g v ∈ LinearMap.range (nu g) := ⟨v, rfl⟩
  rw [h0, Submodule.mem_bot, nu_apply] at hv
  exact sub_eq_zero.mp hv

theorem modA_rk_restr (M : Submodule (ZMod 2) V) (g : modA_stab M) :
    rk (modA_restr M g) = finrank (ZMod 2) (M.map (nu (g : V ≃ₗ[ZMod 2] V))) := by
  have hmap : (LinearMap.range (nu (modA_restr M g))).map M.subtype =
      M.map (nu (g : V ≃ₗ[ZMod 2] V)) := by
    ext x
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
      refine ⟨u, u.2, ?_⟩
      simp [nu_apply, modA_restr_apply]
    · rintro ⟨u, hu, rfl⟩
      refine ⟨nu (modA_restr M g) ⟨u, hu⟩, ⟨_, rfl⟩, ?_⟩
      simp [nu_apply, modA_restr_apply]
  unfold rk
  rw [← hmap, Submodule.finrank_map_subtype_eq]

theorem modA_rk_add {M N : Submodule (ZMod 2) V} (hc : IsCompl M N) {g : V ≃ₗ[ZMod 2] V}
    (hM : g ∈ modA_stab M) (hN : g ∈ modA_stab N) :
    rk g = rk (modA_restr M ⟨g, hM⟩) + rk (modA_restr N ⟨g, hN⟩) := by
  rw [modA_rk_restr, modA_rk_restr]
  unfold rk
  have hr : LinearMap.range (nu g) = M.map (nu g) ⊔ N.map (nu g) := by
    rw [← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top]
  have hmap : ∀ {P : Submodule (ZMod 2) V}, g ∈ modA_stab P → P.map (nu g) ≤ P := by
    intro P hP
    rintro _ ⟨u, hu, rfl⟩
    rw [nu_apply]
    exact P.sub_mem (hP.1 u hu) hu
  have hdisj : Disjoint (M.map (nu g)) (N.map (nu g)) :=
    Disjoint.mono (hmap hM) (hmap hN) hc.disjoint
  have h := Submodule.finrank_sup_add_finrank_inf_eq (M.map (nu g)) (N.map (nu g))
  rw [disjoint_iff.mp hdisj, finrank_bot, add_zero] at h
  rw [hr]
  exact h

theorem modA_rk_swap {V₁ V₂ : Submodule (ZMod 2) V} (hc : IsCompl V₁ V₂)
    (hdim : finrank (ZMod 2) V₁ = 4) (hV : finrank (ZMod 2) V = 8) {g : V ≃ₗ[ZMod 2] V}
    (hg : g * g = 1) (h12 : ∀ v ∈ V₁, g v ∈ V₂) : rk g = 4 := by
  have hup : 2 * rk g ≤ 8 := hV ▸ two_mul_rk_le g hg
  have hinj : Function.Injective ((nu g).domRestrict V₁) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have h1 : nu g (u : V) = 0 := hu
    rw [nu_apply, sub_eq_zero] at h1
    have h2 : (u : V) ∈ V₂ := h1 ▸ h12 u u.2
    have h3 : (u : V) ∈ V₁ ⊓ V₂ := ⟨u.2, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h3
    exact Subtype.ext h3
  have hr := LinearMap.finrank_range_of_inj hinj
  have hle : LinearMap.range ((nu g).domRestrict V₁) ≤ LinearMap.range (nu g) := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  have h := Submodule.finrank_mono hle
  rw [hr, hdim] at h
  unfold rk at hup ⊢
  omega

theorem modA_rk_ne_one (hV : finrank (ZMod 2) V = 4) {a g : V ≃ₗ[ZMod 2] V} (ha5 : a ^ 5 = 1)
    (hfix : ∀ v : V, a v = v → v = 0) (hg : g * g = 1) {k : ℕ} (hk : g * a * g⁻¹ = a ^ k) :
    rk g ≠ 1 := by
  intro hrk
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have ha1 : a ≠ 1 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hfix v (by rw [h]; rfl))
  have hord : orderOf a = 5 := orderOf_eq_prime ha5 ha1
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hkk : a ^ (k * k) = a := by
    have h2 : g * a ^ k * g⁻¹ = a := by
      calc g * a ^ k * g⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by rw [hk]
        _ = (g * g) * a * (g * g)⁻¹ := by group
        _ = a := by rw [hg]; simp
    calc a ^ (k * k) = (a ^ k) ^ k := pow_mul a k k
      _ = (g * a * g⁻¹) ^ k := by rw [hk]
      _ = g * a ^ k * g⁻¹ := conj_pow
      _ = a := h2
  have hmod : k * k ≡ 1 [MOD 5] := by
    have := (pow_eq_pow_iff_modEq (x := a)).mp (hkk.trans (pow_one a).symm)
    rwa [hord] at this
  have hr : k % 5 = 1 ∨ k % 5 = 4 := by
    have h1 : (k * k) % 5 = 1 := hmod
    have h3 : (k * k) % 5 = ((k % 5) * (k % 5)) % 5 := Nat.mul_mod _ _ _
    have h2 : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hh : k % 5 <;> omega
  have hak : a ^ k = a ^ (k % 5) := by rw [← hord, pow_mod_orderOf]
  rcases hr with h1 | h4
  · rw [hak, h1, pow_one] at hk
    have hag : a * g = g * a := by
      calc a * g = (g * a * g⁻¹) * g := by rw [hk]
        _ = g * a := by group
    have htriv := commuting_two_elt_trivial (U := ⊤) ha5 hag (by rw [finrank_top, hV])
      (fun u _ => Submodule.mem_top) (fun u _ => Submodule.mem_top) (fun u _ hu => hfix u hu)
      (k := 1) (by rw [pow_one, sq]; exact hg)
    have : g = 1 := LinearEquiv.ext fun v => htriv v Submodule.mem_top
    rw [this, modA_rk_one] at hrk
    exact absurd hrk (by norm_num)
  · rw [hak, h4] at hk
    have hj₂ : (a * g * a⁻¹) * (a * g * a⁻¹) = 1 := by
      calc (a * g * a⁻¹) * (a * g * a⁻¹) = a * (g * g) * a⁻¹ := by group
        _ = 1 := by rw [hg]; simp
    have hr₂ : rk (a * g * a⁻¹) = 1 := by rw [rk_conj, hrk]
    have hprod : g * (a * g * a⁻¹) = a ^ 3 := by
      calc g * (a * g * a⁻¹) = (g * a * g⁻¹) * a⁻¹ := by rw [hgi]; group
        _ = a ^ 3 := by
          rw [hk, show (4 : ℕ) = 3 + 1 from rfl, pow_succ]
          simp
    have hord3 : orderOf (a ^ 3) = 5 := by
      apply orderOf_eq_prime
      · rw [← pow_mul, show 3 * 5 = 5 * 3 from rfl, pow_mul, ha5, one_pow]
      · intro h
        have := orderOf_dvd_of_pow_eq_one h
        rw [hord] at this
        omega
    exact orderOf_mul_ne_five hg hj₂ hrk hr₂ (by rw [hprod, hord3])

end Rank

end CFSG.LocalAnalysis.EvenBN.Tits.I21L

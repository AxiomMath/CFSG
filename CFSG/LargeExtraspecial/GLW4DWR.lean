module

public import CFSG.LargeExtraspecial.S14W4DWRes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLW4

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S14
  CFSG.LargeExtraspecial.DW.W4 CFSG.GroupTheory.GLnTwoSplitting

variable {X : Type*} [Group X] [Finite X] {T : Setting X} {R : Subgroup X}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {π : T.M →* (V ≃ₗ[ZMod 2] V)}
  {W₁ W₂ : Submodule (ZMod 2) T.Qt}

theorem Lat4.surjective_res_R (hl : W4DW.Lat4 T R W₁ W₂) (A : W4Loc.Act T R π)
    (hcard : Nat.card T.Qt = 2 ^ 8) (hsimp : IsSimpleGroup ((R.subgroupOf T.M).map π))
    (hcardR : Nat.card ((R.subgroupOf T.M).map π) = 20160 ∨
      Nat.card ((R.subgroupOf T.M).map π) = 25920) :
    ∀ g : W₁ ≃ₗ[ZMod 2] W₁, ∃ r : T.M, (r : X) ∈ R ∧
      ∀ w : W₁, ((g w : W₁) : T.Qt) = ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w := by
  set R' := R.subgroupOf T.M
  set φ : R' →* (T.Qt ≃ₗ[ZMod 2] T.Qt) := (T.O.subtype.comp T.ρ).comp R'.subtype
  have hφ : ∀ (x : R') (u : T.Qt), u ∈ W₁ → φ x u ∈ W₁ :=
    fun x u hu => hl.inv₁ x.1 (mem_subgroupOf.mp x.2) u hu
  set f := S4.restrictHom φ W₁ hφ with hf
  set p := π.comp R'.subtype with hp
  have hres : ∀ x : R', f x = 1 ↔
      ∀ u ∈ W₁, ((T.ρ x : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u = u :=
    fun x => S4.restrictHom_eq_one_iff _ _ _ x
  have hrange : p.range = R'.map π := by rw [hp, MonoidHom.range_comp, Subgroup.range_subtype]
  have hpf : p.ker ≤ f.ker := by
    intro r hr
    have hQ : (r : T.M) ∈ T.Q := A.ker_R r r.2 hr
    rw [MonoidHom.mem_ker]
    refine (hres r).mpr fun u _ => ?_
    rw [T.ρ_eq_one_of_mem_Q hQ]
    rfl
  have hfp : f.ker ≤ p.ker := by
    have hsimp' : IsSimpleGroup p.range := by
      rw [hrange]
      exact hsimp
    have hN : (f.ker.map p.rangeRestrict).Normal :=
      (MonoidHom.normal_ker f).map _ p.rangeRestrict_surjective
    rcases hN.eq_bot_or_eq_top with h | h
    · intro r hr
      have h1 : p.rangeRestrict r ∈ f.ker.map p.rangeRestrict := mem_map_of_mem _ hr
      rw [h, mem_bot] at h1
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val h1)
    · exfalso
      have hall : ∀ r : R', f r = 1 := by
        intro r
        have h1 : p.rangeRestrict r ∈ f.ker.map p.rangeRestrict := h ▸ mem_top _
        obtain ⟨n, hn, hnr⟩ := h1
        have h2 : n⁻¹ * r ∈ p.ker := by
          have h3 : p n = p r := congrArg Subtype.val hnr
          rw [MonoidHom.mem_ker, map_mul, map_inv, h3, inv_mul_cancel]
        rw [show r = n * (n⁻¹ * r) by group, map_mul, MonoidHom.mem_ker.mp hn,
          MonoidHom.mem_ker.mp (hpf h2), one_mul]
      have hW₁ : W₁ ≠ ⊥ := fun h0 => by
        have := hl.card₁
        rw [h0, W4Loc.card_bot_submodule] at this
        norm_num at this
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW₁
      have hinvW : W4Dict.IsInv T R ((ZMod 2) ∙ w) := by
        intro r hr v hv
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
        have hrw : ((T.ρ r : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) w = w :=
          (hres ⟨r, hr⟩).mp (hall ⟨r, hr⟩) w hw
        rw [map_smul, hrw]
        exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self w)
      have hcard2 : Nat.card ((ZMod 2) ∙ w) = 2 := by
        rw [T.card_submodule, finrank_span_singleton hw0]
        norm_num
      rcases hl.all _ hinvW with h' | h' | h' | h' <;> rw [h'] at hcard2
      · rw [W4Loc.card_bot_submodule] at hcard2
        norm_num at hcard2
      · rw [hl.card₁] at hcard2
        norm_num at hcard2
      · rw [hl.card₂] at hcard2
        norm_num at hcard2
      · rw [W4Loc.card_top_submodule, hcard] at hcard2
        norm_num at hcard2
  have hker : f.ker = p.ker := le_antisymm hfp hpf
  have hcardf : Nat.card f.range = Nat.card p.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
      ← Nat.card_congr (QuotientGroup.quotientKerEquivRange p).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  have hGL : Nat.card (W₁ ≃ₗ[ZMod 2] W₁) = 20160 := by
    rw [card_linearEquiv_eq hl.finrank₁, CFSG.GH74.Exceptional.card_GL_four_two]
  have : Finite (W₁ ≃ₗ[ZMod 2] W₁) := Nat.finite_of_card_ne_zero (by rw [hGL]; norm_num)
  have hle : Nat.card f.range ≤ 20160 := hGL ▸ Subgroup.card_le_card_group f.range
  have h20160 : Nat.card f.range = Nat.card (W₁ ≃ₗ[ZMod 2] W₁) := by
    rw [hGL, hcardf, hrange]
    rcases hcardR with h | h
    · exact h
    · rw [hcardf, hrange, h] at hle
      norm_num at hle

  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp
    (Subgroup.eq_top_of_card_eq _ h20160)
  intro g
  obtain ⟨x, hx⟩ := hsurj g
  exact ⟨x.1, mem_subgroupOf.mp x.2, fun w => by rw [← hx]; rfl⟩

theorem ts_of_surjective_R {W : Submodule (ZMod 2) T.Qt} (hW : finrank (ZMod 2) W = 4)
    (hρ : ∀ f : W ≃ₗ[ZMod 2] W, ∃ m : T.M, ∀ u : W,
      ((f u : W) : T.Qt) = ((T.ρ m : T.O) : T.Qt ≃ₗ[ZMod 2] T.Qt) u) :
    ∀ w ∈ W, T.q w = 0 := by
  have hB : ∀ x y : W, polar T.q (x : T.Qt) y = 0 :=
    eq_zero_of_forall_linearEquiv_bilin (by omega) (fun x y : W => polar T.q (x : T.Qt) y)
      (fun x y y' => by
        change polar T.q (x : T.Qt) ((y : T.Qt) + y') = _
        rw [polar_add_right])
      (fun f x y => by
        obtain ⟨m, hm⟩ := hρ f
        rw [hm, hm]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (T.ρ m).2 _ _)
  have hQ := eq_zero_of_forall_linearEquiv_add (by omega) (fun x : W => T.q (x : T.Qt))
    (fun x y => by
      have h := hB x y
      rw [QuadraticMap.polar, sub_sub, sub_eq_zero] at h
      change T.q ((x : T.Qt) + y) = _
      exact h)
    (fun f x => by
      obtain ⟨m, hm⟩ := hρ f
      rw [hm]
      exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (T.ρ m).2 _)
  exact fun w hw => hQ ⟨w, hw⟩

end CFSG.LargeExtraspecial.GLW4

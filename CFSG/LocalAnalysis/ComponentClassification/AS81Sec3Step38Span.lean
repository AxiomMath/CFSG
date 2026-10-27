module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step38Tau

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent CFSG.Sporadic.Schreier.Tits.titsZMod2CharP

namespace CFSG.ComponentClassification.AS81

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.Open

section Span

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem eq_one_of_ne_zero_zmod_two {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod_two_eq_zero_or_one a).resolve_left h

theorem map_add_eq_polar (a b : V) : Q (a + b) = Q a + Q b + polar Q a b := by
  rw [polar]
  ring

theorem aniso_span_pair {a b : V} (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1) :
    ∀ w ∈ Submodule.span (ZMod 2) ({a, b} : Set V), Q w = 0 → w = 0 := by
  have hab' : Q (a + b) = 1 := by
    rw [map_add_eq_polar, ha, hb, hab]
    decide
  intro w hw hq
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
  rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
    rcases zmod_two_eq_zero_or_one t with rfl | rfl
  · rw [zero_smul, zero_smul, add_zero]
  · rw [zero_smul, one_smul, zero_add] at hq
    exact absurd (hb.symm.trans hq) one_ne_zero
  · rw [zero_smul, one_smul, add_zero] at hq
    exact absurd (ha.symm.trans hq) one_ne_zero
  · rw [one_smul, one_smul] at hq
    exact absurd (hab'.symm.trans hq) one_ne_zero

theorem finrank_span_pair_eq_two {a b : V} (ha : Q a = 1) (hb : Q b = 1) (hab : polar Q a b = 1) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) ({a, b} : Set V)) = 2 := by
  have hli : LinearIndependent (ZMod 2) ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := aniso_span_pair ha hb hab (s • a + t • b)
      (Submodule.mem_span_pair.mpr ⟨s, t, rfl⟩)
    rcases zmod_two_eq_zero_or_one s with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · rw [zero_smul, one_smul, zero_add] at hst
      rw [hst, map_zero] at hb
      exact absurd hb zero_ne_one
    · rw [zero_smul, one_smul, add_zero] at hst
      rw [hst, map_zero] at ha
      exact absurd ha zero_ne_one
    · rw [one_smul, one_smul] at hst
      have h1 := map_add_eq_polar (Q := Q) a b
      rw [hst, map_zero, ha, hb, hab] at h1
      exact absurd h1 (by decide)
  have h := finrank_span_eq_card hli
  rw [Matrix.range_cons_cons_empty] at h
  rw [h]
  rfl

variable [FiniteDimensional (ZMod 2) V]

theorem exists_singular_polar_eq_one (hQ : Q.polarBilin.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) V) {v : V} (hv : Q v = 1) : ∃ u, Q u = 0 ∧ polar Q u v = 1 := by
  by_contra hcon
  have hcon' : ∀ u, Q u = 0 → polar Q u v = 0 := by
    intro u hu
    by_contra h
    exact hcon ⟨u, hu, eq_one_of_ne_zero_zmod_two h⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact zero_ne_one hv
  obtain ⟨y, hy⟩ : ∃ y, polar Q y v = 1 := by
    by_contra h
    apply hv0
    refine hQ.1 v fun y => ?_
    rw [polarBilin_apply_apply, polar_comm]
    by_contra h'
    exact h ⟨y, eq_one_of_ne_zero_zmod_two h'⟩
  have hy1 : Q y = 1 := by
    by_contra h
    have h0 := hcon' y ((zmod_two_eq_zero_or_one _).resolve_right h)
    rw [hy] at h0
    exact one_ne_zero h0
  let f : V →ₗ[ZMod 2] ZMod 2 := Q.polarBilin.flip v
  have hf : ∀ h, f h = polar Q h v := fun h => by
    change Q.polarBilin h v = polar Q h v
    rw [polarBilin_apply_apply]
  have hH : ∀ h ∈ LinearMap.ker f, Q h = polar Q y h := by
    intro h hh
    rw [LinearMap.mem_ker, hf] at hh
    have hyh : Q (y + h) = 1 := by
      by_contra hne
      have h0 := hcon' (y + h) ((zmod_two_eq_zero_or_one _).resolve_right hne)
      rw [polar_add_left, hy, hh, add_zero] at h0
      exact one_ne_zero h0
    have e := map_add_eq_polar (Q := Q) y h
    rw [hyh, hy1] at e
    revert e
    generalize Q h = c
    generalize polar Q y h = d
    revert c d
    decide
  have hiso : LinearMap.ker f ≤ LinearMap.BilinForm.orthogonal Q.polarBilin (LinearMap.ker f) := by
    intro h₁ h₁H
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro h₂ h₂H
    change Q.polarBilin h₂ h₁ = 0
    rw [polarBilin_apply_apply]
    have e := map_add_eq_polar (Q := Q) h₂ h₁
    rw [hH _ (add_mem h₂H h₁H), hH _ h₂H, hH _ h₁H, polar_add_right] at e
    revert e
    generalize polar Q y h₂ = c
    generalize polar Q y h₁ = d
    generalize polar Q h₂ h₁ = e
    revert c d e
    decide
  have h1 := LinearMap.BilinForm.finrank_orthogonal hQ (LinearMap.ker f)
  have h2 := Submodule.finrank_mono hiso
  have h4 := LinearMap.finrank_range_add_finrank_ker f
  have h5 : finrank (ZMod 2) (LinearMap.range f) ≤ 1 :=
    (Submodule.finrank_le _).trans (by rw [Module.finrank_self])
  omega

theorem eq_top_of_aniso_le {W₀ W' : Submodule (ZMod 2) V} (hsup : W₀ ⊔ W' = ⊤)
    (horth : ∀ v ∈ W₀, ∀ w ∈ W', polar Q v w = 0) (hW₀ : finrank (ZMod 2) W₀ = 2)
    (hW₀a : ∀ w ∈ W₀, Q w = 0 → w = 0) (hW' : (Q.comp W'.subtype).polarBilin.Nondegenerate)
    (h3 : 3 ≤ finrank (ZMod 2) W') {U : Submodule (ZMod 2) V}
    (hU : ∀ L : Submodule (ZMod 2) V, finrank (ZMod 2) L = 2 → (∀ w ∈ L, Q w = 0 → w = 0) →
      L ≤ U) : U = ⊤ := by
  have hval : ∀ w ∈ W₀, w ≠ 0 → Q w = 1 := fun w hw hne =>
    eq_one_of_ne_zero_zmod_two fun h => hne (hW₀a w hw h)
  obtain ⟨w₁, hw₁, hw₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p := W₀) (by
    intro h
    rw [h, finrank_bot] at hW₀
    exact absurd hW₀ (by norm_num))
  have hlt : Submodule.span (ZMod 2) {w₁} < W₀ := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).mpr hw₁) fun h => ?_
    have h1 := finrank_span_singleton (K := ZMod 2) hw₁0
    rw [h, hW₀] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨w₂, hw₂, hw₂n⟩ := IsConcreteLE.exists_of_lt hlt
  have hw₂0 : w₂ ≠ 0 := fun h => hw₂n (h ▸ Submodule.zero_mem _)
  have hw₁₂ : w₁ + w₂ ≠ 0 := by
    intro h
    apply hw₂n
    have e : w₂ = w₁ := by
      rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
      exact h
    rw [e]
    exact Submodule.mem_span_singleton_self w₁
  have hq₁ := hval w₁ hw₁ hw₁0
  have hq₂ := hval w₂ hw₂ hw₂0
  have hq₁₂ := hval _ (add_mem hw₁ hw₂) hw₁₂
  have hp₁₂ : polar Q w₁ w₂ = 1 := by
    have e := map_add_eq_polar (Q := Q) w₁ w₂
    rw [hq₁, hq₂, hq₁₂] at e
    revert e
    generalize polar Q w₁ w₂ = c
    revert c
    decide
  have hplane : ∀ {a b : V}, Q a = 1 → Q b = 1 → polar Q a b = 1 →
      a ∈ U ∧ b ∈ U := by
    intro a b ha hb hab
    have hle := hU _ (finrank_span_pair_eq_two ha hb hab) (aniso_span_pair ha hb hab)
    exact ⟨hle (Submodule.subset_span (by simp)), hle (Submodule.subset_span (by simp))⟩
  have hw₁U : w₁ ∈ U := (hplane hq₁ hq₂ hp₁₂).1
  have hsing : ∀ v ∈ W', Q v = 0 → v ∈ U := by
    intro v hv hqv
    have h1 : Q (w₁ + v) = 1 := by
      rw [map_add_eq_polar, hq₁, hqv, horth w₁ hw₁ v hv]
      decide
    have h2 : polar Q (w₁ + v) w₂ = 1 := by
      rw [polar_add_left, hp₁₂, polar_comm, horth w₂ hw₂ v hv, add_zero]
    have h3 := (hplane h1 hq₂ h2).1
    have e : v = (w₁ + v) - w₁ := by abel
    rw [e]
    exact sub_mem h3 hw₁U
  have hW'U : W' ≤ U := by
    intro v hv
    rcases zmod_two_eq_zero_or_one (Q v) with h0 | h1
    · exact hsing v hv h0
    · obtain ⟨u, hu0, hu1⟩ := exists_singular_polar_eq_one (Q := Q.comp W'.subtype) hW' h3
        (v := ⟨v, hv⟩) h1
      have hu0' : Q (u : V) = 0 := hu0
      have hu1' : polar Q (u : V) v = 1 := hu1
      have hvu : Q (v + u) = 0 := by
        rw [map_add_eq_polar, h1, hu0', polar_comm, hu1']
        decide
      have e : v = (v + u) - u := by abel
      rw [e]
      exact sub_mem (hsing _ (add_mem hv u.2) hvu) (hsing _ u.2 hu0')
  have hW₀U : W₀ ≤ U := hU W₀ hW₀ hW₀a
  exact eq_top_iff.mpr (hsup ▸ sup_le hW₀U hW'U)

theorem eq_zero_of_fixed_of_sq_ne_one (h2 : finrank (ZMod 2) V = 2) {r : V ≃ₗ[ZMod 2] V}
    (hr2 : ∃ w', (r * r) w' ≠ w') {w : V} (hw : r w = w) : w = 0 := by
  by_contra hw0
  have hlt : Submodule.span (ZMod 2) {w} < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => ?_
    have h1 := finrank_span_singleton (K := ZMod 2) hw0
    rw [h, finrank_top, h2] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨w', -, hw'⟩ := IsConcreteLE.exists_of_lt hlt
  have hli : LinearIndependent (ZMod 2) ![w, w'] := by
    rw [LinearIndependent.pair_iff' hw0]
    intro a ha
    apply hw'
    rw [← ha]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  have hspan : Submodule.span (ZMod 2) ({w, w'} : Set V) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at h
    rw [h, h2]
    rfl
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp (hspan ▸ Submodule.mem_top : r w' ∈ _)
  have hb : b = 1 := by
    rcases zmod_two_eq_zero_or_one b with rfl | rfl
    · exfalso
      apply hw'
      rw [zero_smul, add_zero] at hab
      have h1 : r w' = r (a • w) := by rw [← hab, map_smul, hw]
      rw [r.injective h1]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
    · rfl
  rw [hb, one_smul] at hab
  obtain ⟨u, hu⟩ := hr2
  apply hu
  have hrw' : r (r w') = w' := by
    rw [← hab, map_add, map_smul, hw, ← hab, ← add_assoc, ← add_smul, ZModModule.add_self,
      zero_smul, zero_add]
  have hfix : ∀ y ∈ Submodule.span (ZMod 2) ({w, w'} : Set V), (r * r) y = y := by
    intro y hy
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [LinearEquiv.mul_apply, map_add, map_smul, hw, hrw']
  exact hfix u (hspan ▸ Submodule.mem_top)

end Span

namespace Sec38Hyp

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G}
  {x : G} {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U V₀ V Q₀ : Subgroup G}
  (H : Sec38Hyp G A A₁ R g E F x Zs P T Q B₀ z y D J U V₀ V Q₀)
include H

theorem exists_sub_W₀ {w : H.xsub.Qt} (hw : w ∈ H.xsub.clSub Q₀) :
    ∃ w' ∈ H.xsub.clSub Q₀, H.ρG ⟨x, H.x_mem_N⟩ w' - w' = w := by
  have hst := H.map_ρG_W₀ (n := ⟨x, H.x_mem_N⟩) H.q0.x_Q₀
  have hr2 : ∃ w' : H.xsub.clSub Q₀, (resLE _ hst * resLE _ hst) w' ≠ w' := by
    obtain ⟨a, ha, hne⟩ := H.ρx_sq_W₀
    refine ⟨⟨H.xsub.cl a, H.xsub.cl_mem_clSub ha (H.Q₀_le ha)⟩, fun h => hne ?_⟩
    have h1 := congrArg Subtype.val h
    rw [LinearEquiv.mul_apply, coe_resLE, coe_resLE] at h1
    rw [pow_two, LinearEquiv.mul_apply]
    exact h1
  have hfix : fixSpace (resLE _ hst) = ⊥ := by
    refine eq_bot_iff.mpr fun v hv => ?_
    rw [mem_fixSpace] at hv
    exact (Submodule.mem_bot _).mpr (eq_zero_of_fixed_of_sq_ne_one H.finrank_W₀ hr2 hv)
  have htop : commSpace (resLE _ hst) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := finrank_commSpace_add_finrank_fixSpace (resLE _ hst)
    rw [hfix, finrank_bot, add_zero] at h
    exact h
  have hmem : (⟨w, hw⟩ : H.xsub.clSub Q₀) ∈ commSpace (resLE _ hst) := htop ▸ Submodule.mem_top
  obtain ⟨v, hv⟩ := mem_commSpace.mp hmem
  refine ⟨v, v.2, ?_⟩
  have h1 := congrArg Subtype.val hv
  rw [Submodule.coe_sub, coe_resLE] at h1
  exact h1

theorem eq_top_of_invariant
    (htrans : ∀ L : Submodule (ZMod 2) H.xsub.Qt, finrank (ZMod 2) L = 2 →
      (∀ w ∈ L, H.xsub.q w = 0 → w = 0) → ∃ k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate,
        (H.xsub.clSub Q₀).map (k : H.xsub.Qt →ₗ[ZMod 2] H.xsub.Qt) = L)
    {W : Submodule (ZMod 2) H.xsub.Qt}
    (hW : ∀ k ∈ omegaGroup H.xsub.q H.xsub.q_nondegenerate, ∀ u ∈ W, k u ∈ W)
    (hW₀W : H.xsub.clSub Q₀ ≤ W) : W = ⊤ := by
  refine eq_top_of_aniso_le H.W₀_sup_W' (fun _ hv _ hw => H.polar_W₀_W' hv hw) H.finrank_W₀
    (fun _ hw hq => H.W₀_aniso hw hq) H.W'_nondegenerate (by rw [H.finrank_W']; norm_num) ?_
  intro L hL hLa
  obtain ⟨k, hk, hkL⟩ := htrans L hL hLa
  rw [← hkL]
  rintro _ ⟨w, hw, rfl⟩
  exact hW k hk w (hW₀W hw)

end Sec38Hyp

end CFSG.ComponentClassification.AS81

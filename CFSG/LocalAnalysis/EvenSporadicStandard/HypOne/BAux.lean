module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers

public section

namespace CFSG.EvenSporadicStandard.HypOne.BabyHyp

open Subgroup Module CFSG.ComponentClassification.M12Cover

theorem index_centralizer_eq_card_conj {G : Type*} [Group G] (g : G) :
    (centralizer ({g} : Set G)).index = Nat.card {y : G // IsConj g y} := by
  rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq]
  rfl

theorem eq_top_of_index_le_four {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : 24 < Nat.card G) (K : Subgroup G) (hK : K.index ≤ 4) : K = ⊤ := by
  by_contra hne
  have hcore : K.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal K.normalCore with h | h
    · exact h
    · exact absurd (top_le_iff.1 (h ▸ K.normalCore_le)) hne
  have h1 := K.index_normalCore_le_factorial_index
  rw [hcore, Subgroup.index_bot] at h1
  have h2 : Nat.factorial K.index ≤ Nat.factorial 4 := Nat.factorial_le hK
  have h3 : Nat.factorial 4 = 24 := rfl
  omega

theorem relIndex_le_index_of_finite {G : Type*} [Group G] [Finite G] (K L : Subgroup G) :
    K.relIndex L ≤ K.index := by
  have h1 := Subgroup.index_inf (H := K) (K := L)
  have h2 := Subgroup.index_inf_le (H := K) (K := L)
  have hL : 0 < L.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1] at h2
  exact Nat.le_of_mul_le_mul_right h2 hL

theorem index_map_le_of_surjective {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (K : Subgroup G) : (K.map f).index ≤ K.index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_map_dvd K hf)

theorem eq_one_of_commute_of_index_two {O : Type*} [Group O] (Ω : Subgroup O)
    (hΩ : Ω.index ∣ 2) (hcenΩ : Subgroup.center Ω = ⊥) (hcenO : Subgroup.center O = ⊥) (g : O)
    (hg : ∀ w ∈ Ω, g * w = w * g) : g = 1 := by
  by_cases hgΩ : g ∈ Ω
  · have hmem : (⟨g, hgΩ⟩ : Ω) ∈ Subgroup.center Ω :=
      mem_center_iff.2 fun w => Subtype.ext (hg w w.2).symm
    rw [hcenΩ, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · have hidx2 : Ω.index = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hΩ with h | h
      · exact absurd (Subgroup.index_eq_one.1 h ▸ mem_top g) hgΩ
      · exact h
    have hcentral : g ∈ Subgroup.center O := by
      rw [mem_center_iff]
      intro y
      by_cases hy : y ∈ Ω
      · exact (hg y hy).symm
      · have h1 : g⁻¹ * y ∈ Ω := by
          rw [mul_mem_iff_of_index_two hidx2]
          exact ⟨fun h => absurd (inv_mem_iff.1 h) hgΩ, fun h => absurd h hy⟩
        have h2 := hg _ h1
        have e : y = g⁻¹ * y * g := by
          calc y = g * (g⁻¹ * y) := by group
            _ = g⁻¹ * y * g := h2
        calc y * g = g * (g⁻¹ * y * g) := by group
          _ = g * y := by rw [← e]
    rw [hcenO, mem_bot] at hcentral
    exact hcentral

theorem finrank_range_le_finrank_map_ker_add_one {K W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [Module.Finite K W] (f : W →ₗ[K] W) (l : W →ₗ[K] K) :
    finrank K (LinearMap.range f) ≤ finrank K (Submodule.map f (LinearMap.ker l)) + 1 := by
  by_cases hl : l = 0
  · subst hl
    rw [LinearMap.ker_zero, Submodule.map_top]
    omega
  · obtain ⟨v₀, hv₀⟩ : ∃ v₀, l v₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hl (LinearMap.ext h)
    have htop : LinearMap.ker l ⊔ Submodule.span K {v₀} = ⊤ := by
      refine top_le_iff.1 fun w _ => ?_
      have hw : w - (l w / l v₀) • v₀ ∈ LinearMap.ker l := by
        rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv₀, sub_self]
      have : w = (w - (l w / l v₀) • v₀) + (l w / l v₀) • v₀ := by abel
      rw [this]
      exact Submodule.add_mem_sup hw
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v₀))
    have hrange : LinearMap.range f =
        Submodule.map f (LinearMap.ker l) ⊔ Submodule.span K {f v₀} := by
      rw [← Submodule.map_top, ← htop, Submodule.map_sup, Submodule.map_span, Set.image_singleton]
    rw [hrange]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.map f (LinearMap.ker l))
      (Submodule.span K {f v₀})
    have h2 : finrank K (Submodule.span K {f v₀}) ≤ 1 := by
      by_cases hz : f v₀ = 0
      · rw [hz, Submodule.span_singleton_eq_bot.2 rfl, finrank_bot]
        omega
      · rw [finrank_span_singleton hz]
    omega

theorem two_pow_le_card_map_ker {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (f : W →ₗ[ZMod 2] W) (l : W →ₗ[ZMod 2] ZMod 2) {r : ℕ}
    (hr : r ≤ finrank (ZMod 2) (LinearMap.range f)) :
    2 ^ (r - 1) ≤ Nat.card ↥(Submodule.map f (LinearMap.ker l)) := by
  have h1 := finrank_range_le_finrank_map_ker_add_one f l
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem ncard_le_card_of_exists_preimage {X V : Type*} [Finite X] (φ : X → V) (S : Set V)
    (h : ∀ v ∈ S, ∃ x, φ x = v) : Nat.card S ≤ Nat.card X := by
  classical
  refine Nat.card_le_card_of_injective (fun v : S => Classical.choose (h v.1 v.2)) ?_
  intro a b hab
  apply Subtype.ext
  have ha := Classical.choose_spec (h a.1 a.2)
  have hb := Classical.choose_spec (h b.1 b.2)
  rw [← ha, ← hb]
  exact congrArg φ hab

@[expose] def RootClassLarge {Y : Type*} [Group Y] (a : Y) : Prop :=
  ∀ n : centralizer ({a} : Set Y), (n : Y) * n = a →
    5 ≤ Nat.card {y : centralizer ({a} : Set Y) // IsConj n y}

theorem card_isConj_eq_of_mulEquiv {C C' : Type*} [Group C] [Group C'] (f : C ≃* C') (m : C) :
    Nat.card {y : C' // IsConj (f m) y} = Nat.card {y : C // IsConj m y} :=
  (Nat.card_congr (Equiv.subtypeEquiv f.toEquiv fun y =>
    ⟨fun h => f.toMonoidHom.map_isConj h, fun h => by
      simpa using f.symm.toMonoidHom.map_isConj h⟩)).symm

theorem RootClassLarge.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (h : RootClassLarge x) : RootClassLarge (e x) := by
  intro n hn
  set f := centralizerEquiv e x with hf
  have hfx : ∀ m : centralizer ({x} : Set X), ((f m : centralizer ({e x} : Set Y)) : Y) =
      e (m : X) := fun m => rfl
  obtain ⟨m, rfl⟩ := f.surjective n
  have hm : (m : X) * m = x := by
    apply e.injective
    rw [map_mul, ← hfx m]
    exact hn
  rw [card_isConj_eq_of_mulEquiv f m]
  exact h m hm

theorem RootClassLarge.of_isConj {Y : Type*} [Group Y] {a a' : Y} (hc : IsConj a a')
    (h : RootClassLarge a) : RootClassLarge a' := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have h1 := RootClassLarge.of_mulEquiv (MulAut.conj c) h
  rwa [MulAut.conj_apply, hc] at h1

end CFSG.EvenSporadicStandard.HypOne.BabyHyp

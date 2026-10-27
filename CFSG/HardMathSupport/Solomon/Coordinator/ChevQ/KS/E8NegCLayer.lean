module

public import CFSG.HardMathSupport.Lang.TwE6Step3.Glue
public import CFSG.LieType.Seitz.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8NegC

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Seitz CFSG.HardMathSupport.Lang.TwE6Step3

variable {G M : Type} [Group G] [Group M]

theorem mem_normalizer_of_conj_mem (ψ : G →* M) {E : Subgroup G} {P : Subgroup M}
    (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P) (e : E) :
    ψ e ∈ Subgroup.normalizer (P : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact hPnorm e e.2 u hu
  · intro hu
    have h := hPnorm (e : G)⁻¹ (E.inv_mem e.2) _ hu
    have e1 : ψ ((e : G)⁻¹) * (ψ e * u * (ψ e)⁻¹) * (ψ ((e : G)⁻¹))⁻¹ = u := by
      rw [map_inv]
      group
    rw [e1] at h
    exact h

noncomputable def layerAction (ψ : G →* M) (E : Subgroup G) (P : Subgroup M)
    (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P) : E →* MulAut P :=
  P.normalizerMonoidHom.comp
    ((ψ.comp E.subtype).codRestrict _ (mem_normalizer_of_conj_mem ψ hPnorm))

theorem layerAction_apply (ψ : G →* M) {E : Subgroup G} {P : Subgroup M}
    (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P) (e : E) (u : P) :
    ((layerAction ψ E P hPnorm e u : P) : M) = ψ e * u * (ψ e)⁻¹ := by
  simp only [layerAction, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem isElemAbelian_layerAction_range (ψ : G →* M) {E : Subgroup G} (hE : IsElemAbelian 3 E)
    {P : Subgroup M} (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P) :
    IsElemAbelian 3 (layerAction ψ E P hPnorm).range := by
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, ?_⟩
  · obtain ⟨φ, ⟨x, rfl⟩⟩ := a
    obtain ⟨φ', ⟨x', rfl⟩⟩ := b
    apply Subtype.ext
    change layerAction ψ E P hPnorm x * layerAction ψ E P hPnorm x' =
      layerAction ψ E P hPnorm x' * layerAction ψ E P hPnorm x
    rw [← map_mul, ← map_mul, hE.1.is_comm.comm x x']
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hE.2 x x.2)
    rw [this, map_one]

theorem layer_le_hyperClosure_of_gen (ψ : G →* M) (hψ : Function.Injective ψ) {E : Subgroup G}
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 3) {y : G} (hy : y ∈ E) (hy1 : y ≠ 1)
    (P : Subgroup M) (hPψ : ∀ u ∈ P, ∃ g, ψ g = u) (hPy : ∀ u ∈ P, ψ y * u = u * ψ y)
    (hPnorm : ∀ e ∈ E, ∀ u ∈ P, ψ e * u * (ψ e)⁻¹ ∈ P)
    (hgen : Nat.card (layerAction ψ E P hPnorm).range = 3 ^ 2 →
      seitzHyperGamma 3 (layerAction ψ E P hPnorm).range = ⊤) :
    ∀ g : G, ψ g ∈ P → g ∈ hyperClosure 3 ⊤ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hEc]; norm_num)
  set β := layerAction ψ E P hPnorm with hβdef
  have hβ : ∀ (e : E) (u : P), ((β e u : P) : M) = ψ e * u * (ψ e)⁻¹ :=
    layerAction_apply ψ hPnorm
  have hβy : β ⟨y, hy⟩ = 1 := by
    ext u
    rw [hβ]
    change ψ y * (u : M) * (ψ y)⁻¹ = (u : M)
    rw [hPy u u.2, mul_inv_cancel_right]
  have hcomm : ∀ e : E, (e : G) ∉ Subgroup.zpowers y → ∀ g : G, ψ g ∈ P →
      ψ e * ψ g * (ψ e)⁻¹ = ψ g → g ∈ hyperClosure 3 ⊤ E := by
    intro e hey g hgP hfix
    have hgy : g * y = y * g := by
      apply hψ
      rw [map_mul, map_mul]
      exact (hPy _ hgP).symm
    have hge : g * e = e * g := by
      apply hψ
      rw [map_mul, map_mul]
      have h2 : ψ e * ψ g = ψ g * ψ e := by
        calc ψ e * ψ g = ψ e * ψ g * (ψ e)⁻¹ * ψ e := by group
          _ = ψ g * ψ e := by rw [hfix]
      exact h2.symm
    exact mem_hyperClosure_of_commute_pair hE hEc hy e.2 hy1 hey hgy hge
  have hβzp : ∀ e : E, (e : G) ∈ Subgroup.zpowers y → β e = 1 := by
    intro e he
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 he
    have : e = (⟨y, hy⟩ : E) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [this, map_zpow, hβy, one_zpow]
  have hmul := Subgroup.card_ker_mul_card_range β
  have hyo : orderOf y = 3 := orderOf_eq_prime (hE.2 y hy) hy1
  by_cases hcard : Nat.card β.range = 3 ^ 2
  ·
    have htop : seitzHyperGamma 3 β.range = ⊤ := hgen hcard
    set X : Subgroup M := (hyperClosure 3 ⊤ E).map ψ with hX
    have hle : seitzHyperGamma 3 β.range ≤ X.subgroupOf P := by
      refine iSup₂_le fun F hF => ?_
      obtain ⟨hFE, hFi⟩ := hF
      have hFne : F ≠ ⊥ := by
        rintro rfl
        rw [Subgroup.relIndex_bot_left, hcard] at hFi
        norm_num at hFi
      obtain ⟨⟨φ, hφF⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFne
      have hφ1' : φ ≠ 1 := fun h => hφ1 (Subtype.ext h)
      obtain ⟨e, rfl⟩ := hFE hφF
      have hey : (e : G) ∉ Subgroup.zpowers y := fun h => hφ1' (hβzp e h)
      intro u hu
      have hfix := (mem_fixedPoints.1 hu) (β e) hφF
      obtain ⟨g, hg⟩ := hPψ u u.2
      have hgP : ψ g ∈ P := hg ▸ u.2
      have hfix' : ψ e * ψ g * (ψ e)⁻¹ = ψ g := by
        have := congrArg (fun v : P => (v : M)) hfix
        simp only [hβ] at this
        rw [hg]
        exact this
      rw [Subgroup.mem_subgroupOf]
      exact ⟨g, hcomm e hey g hgP hfix', hg⟩
    intro g hgP
    have hmem : (⟨ψ g, hgP⟩ : P) ∈ X.subgroupOf P := hle (htop ▸ Subgroup.mem_top _)
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨g', hg', hgg'⟩ := hmem
    rw [hψ hgg'] at hg'
    exact hg'
  ·
    have hyker : (⟨y, hy⟩ : E) ∈ β.ker := hβy
    have hpker : 3 ∣ Nat.card β.ker := by
      have h1 : orderOf (⟨y, hy⟩ : E) = 3 := by
        rw [← hyo, ← Subgroup.orderOf_coe]
      have h2 := orderOf_dvd_natCard (⟨⟨y, hy⟩, hyker⟩ : β.ker)
      rw [Subgroup.orderOf_mk, h1] at h2
      exact h2
    obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
      (Subgroup.card_range_dvd β |>.trans (by rw [hEc]))
    have hi2 : i ≤ 1 := by
      by_contra hgt
      have : i = 2 ∨ i = 3 := by omega
      rcases this with rfl | rfl
      · exact hcard hi
      · rw [hi, hEc] at hmul
        have : Nat.card β.ker = 1 := by
          have : Nat.card β.ker * 27 = 1 * 27 := by
            rw [one_mul]
            exact hmul
          omega
        rw [this] at hpker
        norm_num at hpker
    have hkerge : 3 ^ 2 ≤ Nat.card β.ker := by
      have h1 : Nat.card β.range ≤ 3 := by
        rw [hi]
        calc 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi2
          _ = 3 := pow_one 3
      rw [hEc] at hmul
      nlinarith
    have hex : ∃ e : E, (e : G) ∉ Subgroup.zpowers y ∧ β e = 1 := by
      by_contra hno
      push Not at hno
      have hsub : (β.ker : Set E) ⊆ (Subgroup.zpowers (⟨y, hy⟩ : E) : Set E) := by
        intro e he
        by_contra hnot
        refine hno e (fun hmem => hnot ?_) he
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
        exact Subgroup.mem_zpowers_iff.2 ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
      have hcardle : Nat.card β.ker ≤ Nat.card (Subgroup.zpowers (⟨y, hy⟩ : E)) :=
        Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
      rw [Nat.card_zpowers] at hcardle
      have h1 : orderOf (⟨y, hy⟩ : E) = 3 := by
        rw [← hyo, ← Subgroup.orderOf_coe]
      rw [h1] at hcardle
      omega
    obtain ⟨e, hey, hβe⟩ := hex
    intro g hgP
    refine hcomm e hey g hgP ?_
    have := congrArg (fun v : P => (v : M)) (DFunLike.congr_fun hβe ⟨ψ g, hgP⟩)
    simp only [hβ] at this
    exact this

end KSE8NegC

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

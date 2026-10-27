module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotPositionCore

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.EvenSmallLie
open CFSG.ComponentClassification (OuterAutomorphisms.inner)

section Action

variable {G : Type*} [Group G]

@[expose] def normalizerConjAut (L : Subgroup G) : normalizer (L : Set G) →* MulAut L where
  toFun n :=
    { toFun := fun x => ⟨n * x * (n : G)⁻¹, (mem_normalizer_iff.mp n.2 x).mp x.2⟩
      invFun := fun x => ⟨(n : G)⁻¹ * x * n, by
        have := (mem_normalizer_iff.mp (inv_mem n.2) x).mp x.2
        simpa using this⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun x => by ext; simp [mul_assoc]
      map_mul' := fun x y => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun n m => by ext; simp [mul_assoc, MulAut.mul_apply]

theorem coe_normalizerConjAut_apply (L : Subgroup G) (n : normalizer (L : Set G)) (x : L) :
    ((normalizerConjAut L n x : L) : G) = n * x * (n : G)⁻¹ := rfl

variable {L : Subgroup G} {C : Type*} [Group C]

@[expose] noncomputable def normalizerAut (e : L ≃* C) : normalizer (L : Set G) →* MulAut C :=
  (MulAut.congr e).toMonoidHom.comp (normalizerConjAut L)

theorem coe_symm_normalizerAut_apply (e : L ≃* C) (n : normalizer (L : Set G)) (c : C) :
    ((e.symm (normalizerAut e n c) : L) : G) = n * (e.symm c : G) * (n : G)⁻¹ := by
  simp only [normalizerAut, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    coe_normalizerConjAut_apply]

theorem normalizerAut_eq_one_iff (e : L ≃* C) (n : normalizer (L : Set G)) :
    normalizerAut e n = 1 ↔ (n : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := coe_symm_normalizerAut_apply e n (e ⟨x, hx⟩)
    rw [h, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    change x = n * x * (n : G)⁻¹ at h1
    calc x * n = n * x * (n : G)⁻¹ * n := by rw [← h1]
      _ = n * x := by group
  · intro h
    refine MulEquiv.ext fun c => e.symm.injective (Subtype.ext ?_)
    rw [coe_symm_normalizerAut_apply, MulAut.one_apply,
      ← mem_centralizer_iff.1 h _ (e.symm c).2]
    group

theorem normalizerAut_of_mem (e : L ≃* C) (n : normalizer (L : Set G)) (l : L)
    (hnl : (n : G) = l) : normalizerAut e n = MulAut.conj (e l) := by
  refine MulEquiv.ext fun c => e.symm.injective (Subtype.ext ?_)
  rw [coe_symm_normalizerAut_apply, hnl, MulAut.conj_apply, map_mul, map_mul, map_inv,
    MulEquiv.symm_apply_apply]
  simp

@[expose] noncomputable def restrictAut (e : L ≃* C) {Y : Subgroup G}
    (hY : Y ≤ normalizer (L : Set G)) : Y →* MulAut C :=
  (normalizerAut e).comp (Subgroup.inclusion hY)

theorem card_eq_two_mul_card_range (e : L ≃* C) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) {Y : Subgroup G}
    (hYN : Y ≤ normalizer (L : Set G)) (hYt : Y ≤ centralizer ({t} : Set G)) (htY : t ∈ Y) :
    Nat.card Y = 2 * Nat.card (restrictAut e hYN).range := by
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have hker : (restrictAut e hYN).ker.map Y.subtype = zpowers t := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy1 : normalizerAut e (Subgroup.inclusion hYN y) = 1 := hy
      rw [normalizerAut_eq_one_iff] at hy1
      exact hKt ▸ mem_inf.2 ⟨hy1, hYt y.2⟩
    · intro hx
      have hxY : x ∈ Y := (zpowers_le.2 htY) hx
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      change normalizerAut e (Subgroup.inclusion hYN ⟨x, hxY⟩) = 1
      rw [normalizerAut_eq_one_iff]
      exact (mem_inf.1 (hKt.symm ▸ hx : x ∈ centralizer (L : Set G) ⊓
        centralizer ({t} : Set G))).1
  have hcard : Nat.card (restrictAut e hYN).ker = 2 := by
    rw [← card_map_of_injective Y.subtype_injective, hker, Nat.card_zpowers, ht]
  rw [← card_ker_mul_card_range (restrictAut e hYN), hcard]

theorem map_conj_inf_centralizer (g a b : G) :
    (centralizer ({a} : Set G) ⊓ centralizer ({b} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer ({g * a * g⁻¹} : Set G) ⊓ centralizer ({g * b * g⁻¹} : Set G) := by
  have key : ∀ (x c : G), x ∈ centralizer ({c} : Set G) ↔
      g * x * g⁻¹ ∈ centralizer ({g * c * g⁻¹} : Set G) := fun x c => by
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc g * x * g⁻¹ * (g * c * g⁻¹) = g * (x * c) * g⁻¹ := by group
        _ = g * (c * x) * g⁻¹ := by rw [h]
        _ = g * c * g⁻¹ * (g * x * g⁻¹) := by group
    · intro h
      calc x * c = g⁻¹ * (g * x * g⁻¹ * (g * c * g⁻¹)) * g := by group
        _ = g⁻¹ * (g * c * g⁻¹ * (g * x * g⁻¹)) * g := by rw [h]
        _ = c * x := by group
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_inf.2 ⟨(key x a).1 (mem_inf.1 hx).1, (key x b).1 (mem_inf.1 hx).2⟩
  · intro hy
    refine ⟨g⁻¹ * y * g, mem_inf.2 ⟨?_, ?_⟩, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rw [key]
      simpa [mul_assoc] using (mem_inf.1 hy).1
    · rw [key]
      simpa [mul_assoc] using (mem_inf.1 hy).2

theorem mulAut_conj_injective_of_center {D : Type*} [Group D] (hZ : center D = ⊥) :
    Function.Injective (MulAut.conj : D →* MulAut D) := by
  intro a b h
  have hc : b⁻¹ * a ∈ center D := mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut D => φ x) h
    simp only [MulAut.conj_apply] at hx
    calc x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [hx]
      _ = b⁻¹ * a * x := by group
  rw [hZ, mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

end Action

section Inner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem forall_inner_of_forall_not_dvd (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) (hZ : center C = ⊥) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (hcmp : ∀ w₀ : C, orderOf w₀ = 2 → ∀ β : MulAut C, orderOf β = 2 → β ∉ OuterAutomorphisms.inner C →
      ¬ Nat.card (centralizer ({w₀} : Set C)) ∣ Nat.card (centralizer ({β} : Set (MulAut C)))) :
    ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ := by
  intro g hne hmem
  have htK : t ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := hKt ▸ mem_zpowers t
  have htC : t ∈ centralizer (L : Set G) := htK.1
  have hN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    centralizer_le_normalizer_of_standard hset.standard htC ht
  have ht2 : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  obtain ⟨w, hwL, hw2, hgw⟩ := EPilot.exists_involution_of_conj_mem_sup_zpowers ht htC hne hmem
  set t' := g⁻¹ * t * g with ht'def
  have htt' : t ∈ centralizer ({t'} : Set G) :=
    EPilot.mem_centralizer_of_eq_or_eq_mul htC hwL hgw
  set s := g * t * g⁻¹ with hsdef
  have hst : s ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 htt'
    rw [ht'def] at h
    calc s * t = g * (t * (g⁻¹ * t * g)) * g⁻¹ := by rw [hsdef]; group
      _ = g * ((g⁻¹ * t * g) * t) * g⁻¹ := by rw [h]
      _ = t * s := by rw [hsdef]; group
  set Y := centralizer ({t} : Set G) ⊓ centralizer ({t'} : Set G) with hYdef
  set Y' := centralizer ({t} : Set G) ⊓ centralizer ({s} : Set G) with hY'def
  have hYt : Y ≤ centralizer ({t} : Set G) := inf_le_left
  have hY't : Y' ≤ centralizer ({t} : Set G) := inf_le_left
  have hYN : Y ≤ normalizer (L : Set G) := hYt.trans hN
  have hY'N : Y' ≤ normalizer (L : Set G) := hY't.trans hN
  have htY : t ∈ Y := mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl, htt'⟩
  have htY' : t ∈ Y' := mem_inf.2 ⟨mem_centralizer_singleton_iff.2 rfl,
    (EPilot.mem_centralizer_singleton_comm).1 hst⟩
  have hYY' : Nat.card Y = Nat.card Y' := by
    have e1 : g * t' * g⁻¹ = t := by rw [ht'def]; group
    have h : Y.map (MulAut.conj g).toMonoidHom = Y' := by
      rw [hYdef, hY'def, map_conj_inf_centralizer, e1, inf_comm]
    rw [← h, card_map_of_injective (MulAut.conj g).injective]
  have hρ : Nat.card (restrictAut e hYN).range = Nat.card (restrictAut e hY'N).range := by
    have h1 := card_eq_two_mul_card_range e ht hKt hYN hYt htY
    have h2 := card_eq_two_mul_card_range e ht hKt hY'N hY't htY'
    omega
  set w₀ := e ⟨w, hwL⟩ with hw₀def
  have hw₀2 : orderOf w₀ = 2 := by
    rw [hw₀def, MulEquiv.orderOf_eq, orderOf_mk, hw2]
  have hle1 : (centralizer ({w₀} : Set C)).map (MulAut.conj : C →* MulAut C) ≤
      (restrictAut e hYN).range := by
    rintro _ ⟨c, hc, rfl⟩
    have hcw : c * w₀ = w₀ * c := mem_centralizer_singleton_iff.1 hc
    set l := e.symm c with hldef
    have hlw : (l : G) * w = w * l := by
      have h := congrArg (fun x => ((e.symm x : L) : G)) hcw
      simp only [map_mul, hw₀def, MulEquiv.symm_apply_apply, Subgroup.coe_mul] at h
      exact h
    have hlt : (l : G) ∈ centralizer ({t} : Set G) := le_centralizer_of_mem_centralizer htC l.2
    have hlt' : (l : G) ∈ centralizer ({t'} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      rcases hgw with h | h
      · rw [h, hlw]
      · rw [h, ← mul_assoc, (mem_centralizer_singleton_iff.1 hlt), mul_assoc, hlw, mul_assoc]
    have hlY : (l : G) ∈ Y := mem_inf.2 ⟨hlt, hlt'⟩
    refine ⟨⟨l, hlY⟩, ?_⟩
    change normalizerAut e (Subgroup.inclusion hYN ⟨l, hlY⟩) = MulAut.conj c
    rw [normalizerAut_of_mem e _ l rfl, hldef, MulEquiv.apply_symm_apply]
  have hdvd1 : Nat.card (centralizer ({w₀} : Set C)) ∣ Nat.card (restrictAut e hYN).range := by
    rw [← card_map_of_injective (mulAut_conj_injective_of_center hZ)]
    exact card_dvd_of_le hle1
  set β := normalizerAut e ⟨s, hN hst⟩ with hβdef
  have hle2 : (restrictAut e hY'N).range ≤ centralizer ({β} : Set (MulAut C)) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hys : (y : G) * s = s * y := mem_centralizer_singleton_iff.1 (mem_inf.1 y.2).2
    change normalizerAut e (Subgroup.inclusion hY'N y) * β =
      β * normalizerAut e (Subgroup.inclusion hY'N y)
    rw [hβdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hys
  have hdvd : Nat.card (centralizer ({w₀} : Set C)) ∣
      Nat.card (centralizer ({β} : Set (MulAut C))) :=
    (hdvd1.trans (hρ ▸ dvd_refl _)).trans (card_dvd_of_le hle2)
  have hs2 : s * s = 1 := by
    calc s * s = g * (t * t) * g⁻¹ := by rw [hsdef]; group
      _ = 1 := by rw [ht2]; group
  have hβ2 : orderOf β = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hβdef, ← map_pow]
      have : (⟨s, hN hst⟩ : normalizer (L : Set G)) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, sq, hs2, Subgroup.coe_one])
      rw [this, map_one]
    · intro h1
      rw [hβdef, normalizerAut_eq_one_iff] at h1
      have hsK : s ∈ zpowers t := hKt ▸ mem_inf.2 ⟨h1, hst⟩
      rcases F4Pilot.eq_one_or_eq_of_mem_zpowers ht hsK with h | h
      · have : t = 1 := by
          have e1 : t = g⁻¹ * s * g := by rw [hsdef]; group
          rw [e1, h]
          group
        rw [this, orderOf_one] at ht
        exact absurd ht (by norm_num)
      · apply hne
        have h' : g * t * g⁻¹ = t := h
        rw [ht'def]
        calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [h']
          _ = t := by group
  have hβI : β ∈ OuterAutomorphisms.inner C := by
    by_contra hβI
    exact hcmp w₀ hw₀2 β hβ2 hβI hdvd
  obtain ⟨c, hc⟩ := hβI
  set l := e.symm c with hldef
  have hsl : ∀ x ∈ L, s * x * s⁻¹ = (l : G) * x * (l : G)⁻¹ := by
    intro x hx
    have h := coe_symm_normalizerAut_apply e ⟨s, hN hst⟩ (e ⟨x, hx⟩)
    rw [← hβdef, ← hc, MulAut.conj_apply, MulEquiv.symm_apply_apply, map_mul, map_mul, map_inv,
      MulEquiv.symm_apply_apply] at h
    simpa [hldef] using h.symm
  refine ⟨g⁻¹ * l * g, EPilot.conj_mem_conjugate l.2 g, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
    simp
  rw [hx']
  have et : t = g⁻¹ * s * g := by rw [hsdef]; group
  calc t * (g⁻¹ * x * g) * t⁻¹ = g⁻¹ * (s * x * s⁻¹) * g := by rw [et]; group
    _ = g⁻¹ * ((l : G) * x * (l : G)⁻¹) * g := by rw [hsl x hx]
    _ = g⁻¹ * l * g * (g⁻¹ * x * g) * (g⁻¹ * l * g)⁻¹ := by group

theorem forall_inner_of_two_pow_dvd (hset : StandardSetting G L) {C : Type*} [Group C]
    (e : L ≃* C) (hZ : center C = ⊥) {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (a : ℕ)
    (hA : ∀ w₀ : C, orderOf w₀ = 2 → 2 ^ a ∣ Nat.card (centralizer ({w₀} : Set C)))
    (hB : ∀ β : MulAut C, orderOf β = 2 → β ∉ OuterAutomorphisms.inner C →
      ¬ 2 ^ a ∣ Nat.card (centralizer ({β} : Set (MulAut C)))) :
    ∀ g : G, g⁻¹ * t * g ≠ t → g⁻¹ * t * g ∈ L ⊔ zpowers t →
      ∃ w' ∈ CFSG.conjugate L g, ∀ l ∈ CFSG.conjugate L g, t * l * t⁻¹ = w' * l * w'⁻¹ :=
  forall_inner_of_forall_not_dvd hset e hZ ht hKt fun w₀ hw₀ β hβ hβI hdvd =>
    hB β hβ hβI ((hA w₀ hw₀).trans hdvd)

end Inner

end CFSG.SeitzReduction.E6Pilot

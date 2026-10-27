module

public import CFSG.ClassicalInvolution.Balance.StrongPowOrthGen

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open Polynomial
open CFSG.ComponentClassification.CatalogueBOddQuadratic (exists_isotropic_of_three_le)
open scoped commutatorElement

theorem exists_add_sq_eq {R : Type} [Field R] [Finite R] (hodd : Odd (Nat.card R)) {c₁ c₂ : R}
    (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) (x : R) : ∃ s r : R, c₁ * (s * s) + c₂ * (r * r) = x := by
  have := Fintype.ofFinite R
  have hcard : Fintype.card R % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  have hf : degree (C c₁ * X ^ 2 - C x : R[X]) = 2 := by
    have h : degree (C x : R[X]) < degree (C c₁ * X ^ 2 : R[X]) := by
      rw [degree_C_mul_X_pow 2 h₁]
      exact lt_of_le_of_lt degree_C_le (by norm_num)
    rw [degree_sub_eq_left_of_degree_lt h, degree_C_mul_X_pow 2 h₁]
    norm_num
  have hg : degree (C c₂ * X ^ 2 : R[X]) = 2 := degree_C_mul_X_pow 2 h₂
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg hcard
  refine ⟨a, b, ?_⟩
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at hab
  linear_combination hab

section Plane

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem polar_self_ne_zero (h2 : (2 : F) ≠ 0) {b : V} (hQb : Q b ≠ 0) : polar Q b b ≠ 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul]
  exact mul_ne_zero h2 hQb

theorem map_eq_zero_of_polar_self' (h2 : (2 : F) ≠ 0) {x : V} (h : polar Q x x = 0) : Q x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, ← two_mul] at h
  exact (mul_eq_zero.mp h).resolve_left h2

theorem exists_orth_partner [FiniteDimensional F V] (h2 : (2 : F) ≠ 0) {A : Submodule F V}
    (hA : Module.finrank F A = 2) {b : V} (hb : b ∈ A) (hQb : Q b ≠ 0) :
    ∃ b' ∈ A, b' ≠ 0 ∧ polar Q b b' = 0 ∧ ∀ x ∈ A, ∃ α β : F, x = α • b + β • b' := by
  have hbb : polar Q b b ≠ 0 := polar_self_ne_zero h2 hQb
  set Λ : Submodule F V := A ⊓ LinearMap.ker (polarBilin Q b) with hΛ
  have hmemΛ : ∀ x, x ∈ Λ ↔ x ∈ A ∧ polar Q b x = 0 := fun x => by
    rw [hΛ, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
  have hdisj : Submodule.span F {b} ⊓ Λ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
    have := ((hmemΛ _).mp hx2).2
    rw [polar_smul_right_eq] at this
    have hc : c = 0 := (mul_eq_zero.mp this).resolve_right hbb
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hsplit : ∀ x ∈ A, ∃ α : F, x - α • b ∈ Λ := by
    intro x hx
    refine ⟨polar Q b x / polar Q b b, (hmemΛ _).mpr ⟨A.sub_mem hx (A.smul_mem _ hb), ?_⟩⟩
    rw [polar_sub_right, polar_smul_right_eq]
    field_simp
    ring
  have hsup : Submodule.span F {b} ⊔ Λ = A := by
    refine le_antisymm (sup_le ?_ inf_le_left) fun x hx => ?_
    · rw [Submodule.span_le]
      simpa using hb
    · obtain ⟨α, hα⟩ := hsplit x hx
      have : x = α • b + (x - α • b) := by abel
      rw [this]
      exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)) hα
  have hrank : Module.finrank F Λ = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {b}) Λ
    rw [hsup, hdisj, finrank_bot, finrank_span_singleton (fun h => hQb (by rw [h]; simp)), hA] at h
    omega
  have hne : Λ ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hrank
    omega
  obtain ⟨b', hb'Λ, hb'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hb'A := ((hmemΛ _).mp hb'Λ).1
  refine ⟨b', hb'A, hb'0, ((hmemΛ _).mp hb'Λ).2, fun x hx => ?_⟩
  obtain ⟨α, hα⟩ := hsplit x hx
  have hone := (finrank_eq_one_iff_of_nonzero' (⟨b', hb'Λ⟩ : Λ)
    (fun h => hb'0 (congrArg Subtype.val h))).mp hrank ⟨x - α • b, hα⟩
  obtain ⟨β, hβ⟩ := hone
  refine ⟨α, β, ?_⟩
  have := congrArg Subtype.val hβ
  simp only [SetLike.val_smul] at this
  rw [this]
  abel

theorem exists_mem_eq_of_plane [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) {A : Submodule F V} (hA : Module.finrank F A = 2)
    (hAan : ∀ x ∈ A, Q x = 0 → x = 0) (c : F) : ∃ x ∈ A, Q x = c := by
  have hpos : 0 < Module.finrank F A := by omega
  obtain ⟨b, hbA, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (show A ≠ ⊥ from fun h => by rw [h, finrank_bot] at hpos; omega)
  have hQb : Q b ≠ 0 := fun h => hb0 (hAan b hbA h)
  obtain ⟨b', hb'A, hb'0, hbb', hspan⟩ := exists_orth_partner h2 hA hbA hQb
  have hQb' : Q b' ≠ 0 := fun h => hb'0 (hAan b' hb'A h)
  obtain ⟨s, r, hsr⟩ := exists_add_sq_eq hodd hQb hQb' c
  refine ⟨s • b + r • b', A.add_mem (A.smul_mem _ hbA) (A.smul_mem _ hb'A), ?_⟩
  rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, polar_smul_left_eq,
    polar_smul_right_eq, hbb', ← hsr]
  ring

end Plane

section Commutator

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

@[expose] def eichlerParamSet (Q : QuadraticForm F V) (H : Subgroup (V ≃ₗ[F] V)) (e : V) :
    AddSubgroup V where
  carrier := {w | polar Q e w = 0 ∧ eichler Q e w ∈ H}
  add_mem' {w w'} hw hw' := ⟨by rw [polar_add_right, hw.1, hw'.1, add_zero], by
    rw [← eichler_mul hw.1 hw'.1]
    exact mul_mem hw.2 hw'.2⟩
  zero_mem' := ⟨polar_zero_right Q e, by
    rw [eichler_zero_right]
    exact one_mem H⟩
  neg_mem' {w} hw := ⟨by rw [polar_neg_right, hw.1, neg_zero], by
    rw [← eichler_inv hw.1]
    exact inv_mem hw.2⟩

theorem mem_eichlerParamSet {H : Subgroup (V ≃ₗ[F] V)} {e w : V} :
    w ∈ eichlerParamSet Q H e ↔ polar Q e w = 0 ∧ eichler Q e w ∈ H :=
  Iff.rfl

theorem commutator_eichler_eichler {u z e y : V} (hu : Q u = 0) (huz : polar Q u z = 0)
    (hey : polar Q e y = 0) (heu : polar Q e u = 0) (hez : polar Q e z = 0) :
    ⁅eichler Q u z, eichler Q e y⁆ =
      eichler Q e (polar Q y u • z - (polar Q y z + Q z * polar Q y u) • u) := by
  set w : V := polar Q y u • z - (polar Q y z + Q z * polar Q y u) • u with hw
  have hew : polar Q e w = 0 := by
    rw [hw, polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, hez, heu]
    simp
  have hgO := eichler_mem_orthogonalGroup Q u z
  have hge : eichler Q u z e = e := by
    rw [eichler_apply hu huz, heu, hez]
    simp
  have hgy : eichler Q u z y = y + w := by
    rw [eichler_apply hu huz, hw]
    abel
  have h1 : eichler Q u z * eichler Q e y * (eichler Q u z)⁻¹ = eichler Q e (y + w) := by
    rw [eichler_conj hgO, hge, hgy]
  rw [commutatorElement_def, h1, eichler_inv hey,
    eichler_mul (by rw [polar_add_right, hey, hew, add_zero])
      (by rw [polar_neg_right, hey, neg_zero])]
  congr 1
  abel

end Commutator

section Cross

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem eichler_mem_cross [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) {W T A : Submodule F V}
    (hWT : ∀ w ∈ W, ∀ t ∈ T, polar Q w t = 0) (hWA : ∀ w ∈ W, ∀ x ∈ A, polar Q w x = 0)
    (hTA : ∀ t ∈ T, ∀ x ∈ A, polar Q t x = 0) (hW2 : Module.finrank F W = 2)
    (hWan : ∀ x ∈ W, Q x = 0 → x = 0) (hA2 : Module.finrank F A = 2)
    (hAan : ∀ x ∈ A, Q x = 0 → x = 0) (hTan : ∀ x ∈ T, Q x = 0 → x = 0)
    {H : Subgroup (V ≃ₗ[F] V)} (hH₁ : elemOn Q (W ⊔ T) ≤ H) (hH₂ : elemOn Q (W ⊔ A) ≤ H)
    {e : V} (he : e ∈ W ⊔ T) (hQe : Q e = 0) (he0 : e ≠ 0) {x : V} (hx : x ∈ A) :
    eichler Q e x ∈ H := by
  obtain ⟨eW, heW, eT, heT, rfl⟩ := Submodule.mem_sup.mp he
  have heW0 : eW ≠ 0 := by
    rintro rfl
    rw [zero_add] at hQe he0
    exact he0 (hTan eT heT hQe)
  have hQeW : Q eW ≠ 0 := fun h => heW0 (hWan eW heW h)
  obtain ⟨a, haW, ha0, haB, -⟩ := exists_orth_partner h2 hW2 heW hQeW
  have hQa : Q a ≠ 0 := fun h => ha0 (hWan a haW h)
  obtain ⟨aA, haA, hQaA⟩ := exists_mem_eq_of_plane h2 hodd hA2 hAan (-Q a)
  have hQaA0 : Q aA ≠ 0 := by rw [hQaA]; exact neg_ne_zero.mpr hQa
  obtain ⟨a', ha'A, ha'0, haa', hspan⟩ := exists_orth_partner h2 hA2 haA hQaA0
  have hQa' : Q a' ≠ 0 := fun h => ha'0 (hAan a' ha'A h)
  have hWAa : polar Q a aA = 0 := hWA a haW aA haA
  have hu : Q (a + aA) = 0 := by
    rw [QuadraticMap.map_add Q, hWAa, hQaA]
    ring
  have hu_mem : a + aA ∈ W ⊔ A := Submodule.add_mem_sup haW haA
  have hTW : ∀ t ∈ T, ∀ w ∈ W, polar Q t w = 0 := fun t ht w hw => by
    rw [polar_comm]
    exact hWT w hw t ht
  have hea : polar Q (eW + eT) a = 0 := by
    rw [polar_add_left, haB, hTW eT heT a haW, add_zero]
  have heA : ∀ z ∈ A, polar Q (eW + eT) z = 0 := fun z hz => by
    rw [polar_add_left, hWA eW heW z hz, hTA eT heT z hz, add_zero]
  have heu : polar Q (eW + eT) (a + aA) = 0 := by
    rw [polar_add_right, hea, heA aA haA, add_zero]
  have hbb : polar Q a a ≠ 0 := polar_self_ne_zero h2 hQa
  set y : V := (polar Q a a)⁻¹ • a with hy
  have hyW : y ∈ W := W.smul_mem _ haW
  have hey : polar Q (eW + eT) y = 0 := by
    rw [hy, polar_smul_right_eq, hea, mul_zero]
  have hyu : polar Q y (a + aA) = 1 := by
    rw [hy, polar_add_right, polar_smul_left_eq, polar_smul_left_eq, hWAa, mul_zero, add_zero,
      inv_mul_cancel₀ hbb]
  have hstep : ∀ z ∈ A, polar Q aA z = 0 → eichler Q (eW + eT) (z - Q z • aA) ∈ H := by
    intro z hz hz0
    have huz : polar Q (a + aA) z = 0 := by
      rw [polar_add_left, hWA a haW z hz, hz0, add_zero]
    have hyz : polar Q y z = 0 := by
      rw [hy, polar_smul_left_eq, hWA a haW z hz, mul_zero]
    have hg : eichler Q (a + aA) z ∈ H := hH₂ (eichler_mem_elemOn hu_mem
      (Submodule.mem_sup_right hz))
    have hg' : eichler Q (eW + eT) y ∈ H := hH₁ (eichler_mem_elemOn he
      (Submodule.mem_sup_left hyW))
    have hcomm := commutator_eichler_eichler (Q := Q) hu huz hey heu (heA z hz)
    rw [hyu, hyz, zero_add, mul_one, one_smul] at hcomm
    have hmem : ⁅eichler Q (a + aA) z, eichler Q (eW + eT) y⁆ ∈ H := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')
    rw [hcomm] at hmem
    have hQa'mem : eichler Q (eW + eT) (Q z • a) ∈ H := hH₁ (eichler_mem_elemOn he
      (Submodule.mem_sup_left (W.smul_mem _ haW)))
    have hmul := mul_mem hmem hQa'mem
    rw [eichler_mul (by rw [polar_sub_right, heA z hz, polar_smul_right_eq, heu, mul_zero,
        sub_zero]) (by rw [polar_smul_right_eq, hea, mul_zero])] at hmul
    have e1 : z - Q z • (a + aA) + Q z • a = z - Q z • aA := by module
    rwa [e1] at hmul
  have hG : ∀ w, w ∈ eichlerParamSet Q H (eW + eT) ↔ polar Q (eW + eT) w = 0 ∧
      eichler Q (eW + eT) w ∈ H := fun w => mem_eichlerParamSet
  set G := eichlerParamSet Q H (eW + eT) with hGdef
  have hw : ∀ t : F, t • a' - (t ^ 2 * Q a') • aA ∈ G := fun t => by
    have hz : t • a' ∈ A := A.smul_mem _ ha'A
    have h := hstep (t • a') hz (by rw [polar_smul_right_eq, haa', mul_zero])
    rw [map_smul_eq_sq] at h
    exact (hG _).mpr ⟨by
      rw [polar_sub_right, polar_smul_right_eq, polar_smul_right_eq, heA a' ha'A, heA aA haA]
      ring, h⟩
  have hsq : ∀ t : F, ((-2 * t ^ 2 * Q a') • aA) ∈ G := fun t => by
    have := G.add_mem (hw t) (hw (-t))
    have e1 : t • a' - (t ^ 2 * Q a') • aA + ((-t) • a' - ((-t) ^ 2 * Q a') • aA) =
        (-2 * t ^ 2 * Q a') • aA := by module
    rwa [e1] at this
  have hc : ∀ c : F, c • aA ∈ G := fun c => by
    have hne : (-2 * Q a' : F) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2) hQa'
    obtain ⟨s, r, hsr⟩ := exists_add_sq_eq hodd (c₁ := (1 : F)) (c₂ := 1) one_ne_zero one_ne_zero
      (c / (-2 * Q a'))
    have hsr' : c = (-2 * Q a') * (s * s + r * r) := by
      simp only [one_mul] at hsr
      rw [eq_div_iff hne] at hsr
      linear_combination -hsr
    have hc' : c = (-2 * s ^ 2 * Q a') + (-2 * r ^ 2 * Q a') := by
      rw [hsr']
      ring
    rw [hc', add_smul]
    exact G.add_mem (hsq s) (hsq r)
  have hc2 : ∀ c : F, c • a' ∈ G := fun c => by
    have := G.add_mem (hw c) (hc (c ^ 2 * Q a'))
    simpa using this
  obtain ⟨α, β, rfl⟩ := hspan x hx
  exact ((hG _).mp (G.add_mem (hc α) (hc2 β))).2

end Cross

section Pivot

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

theorem elementaryGroup_le_of_pivot [Finite F] [FiniteDimensional F V] (h2 : (2 : F) ≠ 0)
    (hodd : Odd (Nat.card F)) (hQ : (polarBilin Q).Nondegenerate) {W T A B : Submodule F V}
    (hWT : ∀ w ∈ W, ∀ t ∈ T, polar Q w t = 0) (hWA : ∀ w ∈ W, ∀ x ∈ A, polar Q w x = 0)
    (hWB : ∀ w ∈ W, ∀ x ∈ B, polar Q w x = 0) (hTA : ∀ t ∈ T, ∀ x ∈ A, polar Q t x = 0)
    (hTB : ∀ t ∈ T, ∀ x ∈ B, polar Q t x = 0)
    (hW2 : Module.finrank F W = 2) (hWan : ∀ x ∈ W, Q x = 0 → x = 0)
    (hA2 : Module.finrank F A = 2) (hAan : ∀ x ∈ A, Q x = 0 → x = 0)
    (hB2 : Module.finrank F B = 2) (hBan : ∀ x ∈ B, Q x = 0 → x = 0)
    (hTan : ∀ x ∈ T, Q x = 0 → x = 0) (hT0 : T ≠ ⊥)
    (hsum : ∀ v : V, ∃ w ∈ W, ∃ t ∈ T, ∃ a ∈ A, ∃ b ∈ B, v = w + t + a + b)
    (hnd : PolarNondegOn Q (W ⊔ T)) {H : Subgroup (V ≃ₗ[F] V)}
    (hH₁ : elemOn Q (W ⊔ T) ≤ H) (hH₂ : elemOn Q (W ⊔ A) ≤ H) (hH₃ : elemOn Q (W ⊔ B) ≤ H) :
    elementaryGroup Q ≤ H := by
  have hdisj : W ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxT⟩ := Submodule.mem_inf.mp hx
    have h0 : polar Q x x = 0 := hWT x hxW x hxT
    have : x = 0 := hWan x hxW (map_eq_zero_of_polar_self' h2 h0)
    rw [this]
    exact Submodule.zero_mem _
  have hT1 : 1 ≤ Module.finrank F T := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    exact hT0 (Submodule.finrank_eq_zero.mp h)
  have h3 : 3 ≤ Module.finrank F (W ⊔ T : Submodule F V) := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq W T
    rw [hdisj, finrank_bot] at h
    omega
  have h3V : 3 ≤ Module.finrank F V := h3.trans (Submodule.finrank_le _)
  obtain ⟨⟨e, heS⟩, hev0, hevQ⟩ := exists_isotropic_of_three_le hodd (Q.restrict (W ⊔ T))
    (nondegenerate_polarBilin_restrict hnd) h3
  have he0 : e ≠ 0 := fun h => hev0 (Subtype.ext h)
  have hQe : Q e = 0 := hevQ
  obtain ⟨y, hyS, hye⟩ := hnd.exists_polar_ne_zero heS he0
  set h : V := (polar Q e y)⁻¹ • y with hh
  have hhS : h ∈ W ⊔ T := (W ⊔ T).smul_mem _ hyS
  have hh1 : polar Q e h = 1 := by rw [hh, polar_smul_right_eq, inv_mul_cancel₀ hye]
  set P : HypPair Q := HypPair.ofPolarEqOne hQe hh1 with hP
  have hPe : P.e = e := rfl
  have hPf : P.f ∈ W ⊔ T := by
    rw [hP, HypPair.ofPolarEqOne_f]
    exact (W ⊔ T).sub_mem hhS ((W ⊔ T).smul_mem _ heS)
  have hST : ∀ u ∈ W ⊔ T, ∀ x ∈ A, polar Q u x = 0 := fun u hu x hx => by
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
    rw [polar_add_left, hWA w hw x hx, hTA t ht x hx, add_zero]
  have hSTB : ∀ u ∈ W ⊔ T, ∀ x ∈ B, polar Q u x = 0 := fun u hu x hx => by
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
    rw [polar_add_left, hWB w hw x hx, hTB t ht x hx, add_zero]
  have key : ∀ u ∈ W ⊔ T, Q u = 0 → u ≠ 0 → ∀ v, polar Q u v = 0 → eichler Q u v ∈ H := by
    intro u hu hQu hu0 v huv
    obtain ⟨w, hw, t, ht, a, ha, b, hb, rfl⟩ := hsum v
    have hs : w + t ∈ W ⊔ T := Submodule.add_mem_sup hw ht
    have hua := hST u hu a ha
    have hub := hSTB u hu b hb
    have hus : polar Q u (w + t) = 0 := by
      rw [polar_add_right, polar_add_right, polar_add_right, hua, hub] at huv
      rw [polar_add_right]
      linear_combination huv
    rw [← eichler_mul (by rw [polar_add_right, hus, hua, add_zero]) hub,
      ← eichler_mul hus hua]
    refine mul_mem (mul_mem (hH₁ (eichler_mem_elemOn hu hs)) ?_) ?_
    · exact eichler_mem_cross h2 hodd hWT hWA hTA hW2 hWan hA2 hAan hTan hH₁ hH₂ hu hQu hu0 ha
    · exact eichler_mem_cross h2 hodd hWT hWB hTB hW2 hWan hB2 hBan hTan hH₁ hH₃ hu hQu hu0 hb
  refine elementaryGroup_le_of_plane hQ h3V P fun v hv₁ hv₂ => ⟨?_, ?_⟩
  · exact key P.e (by rw [hPe]; exact heS) P.Q_e P.e_ne_zero v hv₁
  · exact key P.f hPf P.Q_f P.f_ne_zero v hv₂

end Pivot

end CFSG.ClassicalInvolution.Balance.StrongBalance.Orth

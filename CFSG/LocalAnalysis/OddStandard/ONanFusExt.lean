module

public import CFSG.LocalAnalysis.OddStandard.ONanFusAB

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

abbrev repDFG (k : Fin 3) : Fin 7 := ![3, 5, 6] k

@[expose] def ord4E (k : Fin 3) : List AlpE :=
  allE.filter fun x => x * invE (repDFG k) = invE (repDFG k) * x ∧ x * x = zc

theorem ord4E_spec {k : Fin 3} {f : AlpE} (hf : f ∈ ord4E k) :
    f * invE (repDFG k) = invE (repDFG k) * f ∧ f * f = zc := by
  simpa [ord4E] using (List.mem_filter.1 hf).2

set_option maxRecDepth 100000 in
theorem cent_sq_E : ∀ (k : Fin 3) (x : AlpE), x * invE (repDFG k) = invE (repDFG k) * x →
    x * x = 1 ∨ x * x = zc := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cent_decomp_E : ∀ (k : Fin 3) (x : AlpE), x * invE (repDFG k) = invE (repDFG k) * x →
    ∃ a ∈ [1, invE (repDFG k)], ∃ f1 ∈ (1 :: ord4E k), ∃ f2 ∈ (1 :: ord4E k), x = a * f1 * f2 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cent_nonab_E : ∀ k : Fin 3, ∃ x y : AlpE, x * invE (repDFG k) = invE (repDFG k) * x ∧
    y * invE (repDFG k) = invE (repDFG k) * y ∧ x * y ≠ y * x := by
  decide +kernel

theorem d_eq_five_of_sq (hF : f2Check = true) {y : AlpE} (hd : y.d ≠ 0) (h4 : y ^ 4 = 1)
    (h2 : y ^ 2 ≠ 1) (hsq : y ^ 2 = bE) : y.d = 5 := by
  by_cases hodd : y.d = 1 ∨ y.d = 3
  · have h16 := orderOf_of_d_odd hF hodd
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h16] at this
    norm_num at this
  by_cases h246 : y.d = 2 ∨ y.d = 4 ∨ y.d = 6
  · rw [sq_of_order_four_d246 hF h246 h4 h2] at hsq
    exact absurd hsq (by decide)
  by_cases h7 : y.d = 7
  · rw [sq_of_order_four_d7 hF h7 h4 h2] at hsq
    exact absurd hsq (by decide)
  revert hd hodd h246 h7
  generalize y.d = d
  decide +revert

theorem sq_of_order_four_out (hF : f2Check = true) {y : AlpE} (hd : y.d ≠ 0) (h4 : y ^ 4 = 1)
    (h2 : y ^ 2 ≠ 1) : y ^ 2 = zc ∨ y ^ 2 = bE ∨ y ^ 2 = zc * bE := by
  by_cases hodd : y.d = 1 ∨ y.d = 3
  · have h16 := orderOf_of_d_odd hF hodd
    have := orderOf_dvd_of_pow_eq_one h4
    rw [h16] at this
    norm_num at this
  by_cases h246 : y.d = 2 ∨ y.d = 4 ∨ y.d = 6
  · exact Or.inl (sq_of_order_four_d246 hF h246 h4 h2)
  by_cases h5 : y.d = 5
  · exact Or.inr (Or.inl (sq_of_order_four_d5 hF h5 h4 h2))
  have h7 : y.d = 7 := by
    revert hd hodd h246 h5
    generalize y.d = d
    decide +revert
  rw [sq_of_order_four_d7 hF h7 h4 h2]
  exact Or.inr (Or.inr (by decide))

@[expose] def H5E : Subgroup AlpE where
  carrier := {y | y.d = 0 ∨ y.d = 5}
  one_mem' := Or.inl rfl
  mul_mem' := by
    intro x y hx hy
    change x.d = 0 ∨ x.d = 5 at hx
    change y.d = 0 ∨ y.d = 5 at hy
    show (x * y).d = 0 ∨ (x * y).d = 5
    rw [mul_d]
    rcases hx with h | h <;> rcases hy with h' | h' <;> rw [h, h'] <;> decide
  inv_mem' := by
    intro x hx
    change x.d = 0 ∨ x.d = 5 at hx
    show (x⁻¹).d = 0 ∨ (x⁻¹).d = 5
    rw [inv_d]
    rcases hx with h | h <;> rw [h] <;> decide

theorem mem_H5E {y : AlpE} : y ∈ H5E ↔ y.d = 0 ∨ y.d = 5 := Iff.rfl

theorem Vsub_le_H5E : Vsub ≤ H5E := fun _ hy => Or.inl hy

set_option maxRecDepth 100000 in
theorem card_H5E : Nat.card H5E = 128 := by
  have e : H5E ≃ {y : AlpE // y.d = 0 ∨ y.d = 5} := Equiv.subtypeEquivRight fun y => Iff.rfl
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

@[expose] def H5 : Subgroup G := H5E.map D.E.φ

theorem V_le_H5 : alpV v1 v2 v3 ≤ D.H5 := by
  rw [AlpEmb.alpV_eq_map D.E, H5]
  exact Subgroup.map_mono Vsub_le_H5E

theorem relIndex_V_H5 : (alpV v1 v2 v3).relIndex D.H5 = 2 := by
  have h := relIndex_mul_card (H := alpV v1 v2 v3) (K := D.H5)
  have hc : Nat.card D.H5 = 128 := by rw [H5, AlpEmb.card_map D.E, card_H5E]
  rw [inf_of_le_left D.V_le_H5, AlpEmb.card_alpV D.E, hc] at h
  omega

theorem mem_H5_of_sq {x : G} (hxP : x ∈ alpP v1 v2 v3 s t) (h4 : x ^ 4 = 1)
    (hsq : x ^ 2 = invRep v1 v2 v3 s t 1) : x ∈ D.H5 := by
  obtain ⟨y, rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hxP
  have hy4 : y ^ 4 = 1 := D.E.inj (by rw [map_pow, h4, map_one])
  have hysq : y ^ 2 = bE := D.E.inj (by rw [map_pow, hsq, D.invRep_eq 1, invE_one])
  have hy2 : y ^ 2 ≠ 1 := by
    rw [hysq]
    decide
  refine Subgroup.mem_map_of_mem _ ?_
  by_cases hd : y.d = 0
  · exact Or.inl hd
  · exact Or.inr (d_eq_five_of_sq D.hF hd hy4 hy2 hysq)

theorem W_le_of_sq {Y : Subgroup G} {u : G} (hu : u * u = 1)
    (hYV : 16 ≤ Nat.card (alpV v1 v2 v3 ⊓ Y : Subgroup G))
    (hsq : ∀ y ∈ Y, y * y = 1 ∨ y * y = u) : alpW v1 v2 v3 ≤ Y := by
  set X : Subgroup G := alpV v1 v2 v3 ⊓ Y with hX
  have hrel : (alpW v1 v2 v3).relIndex X ≤ 2 := by
    by_cases hXW : X ≤ alpW v1 v2 v3
    · rw [relIndex_eq_one.2 hXW]
      norm_num
    · obtain ⟨x0, hx0X, hx0W⟩ := IsConcreteLE.not_le_iff_exists.1 hXW
      have hx0sq : x0 * x0 = u := by
        rcases hsq x0 hx0X.2 with h | h
        · exact absurd (D.mem_W_iff.2 ⟨hx0X.1, h⟩) hx0W
        · exact h
      refine (relIndex_eq_two_iff.2 ⟨x0, hx0X, fun b hb => ?_⟩).le
      by_cases hbW : b ∈ alpW v1 v2 v3
      · refine Or.inr ⟨hbW, fun h => hx0W ?_⟩
        have := mul_mem (inv_mem hbW) h
        rwa [inv_mul_cancel_left] at this
      · refine Or.inl ⟨?_, hbW⟩
        have hbsq : b * b = u := by
          rcases hsq b hb.2 with h | h
          · exact absurd (D.mem_W_iff.2 ⟨hb.1, h⟩) hbW
          · exact h
        refine D.mem_W_iff.2 ⟨mul_mem hb.1 hx0X.1, ?_⟩
        have hc : x0 * b = b * x0 := mem_centralizer_iff.1 (D.V_le_centralizer_V hb.1) x0 hx0X.1
        calc b * x0 * (b * x0) = (b * b) * (x0 * x0) := by
              rw [mul_assoc, ← mul_assoc x0, hc]
              group
          _ = 1 := by rw [hbsq, hx0sq, hu]
  have h := relIndex_mul_card (H := alpW v1 v2 v3) (K := X)
  have hWX : Nat.card (alpW v1 v2 v3 ⊓ X : Subgroup G) ≥ 8 := by
    have hpos : 0 < (alpW v1 v2 v3).relIndex X := Nat.pos_of_ne_zero (by
      intro h0
      rw [h0, zero_mul] at h
      have := Nat.card_pos (α := X)
      omega)
    nlinarith
  have hle : alpW v1 v2 v3 ⊓ X ≤ alpW v1 v2 v3 := inf_le_left
  have heq : alpW v1 v2 v3 ⊓ X = alpW v1 v2 v3 :=
    eq_of_le_of_card_ge hle (by rw [AlpEmb.card_alpW D.E D.hF]; omega)
  intro w hw
  rw [← heq] at hw
  exact hw.2.2

theorem rep_ne_z (k : Fin 3) : invRep v1 v2 v3 s t (repDFG k) ≠ invRep v1 v2 v3 s t 0 := by
  intro h
  have := InClass.unique D (h ▸ D.inClass_rep (repDFG k)) (D.inClass_rep 0)
  have key : ∀ k : Fin 3, repDFG k ≠ 0 := by decide
  exact key k this

theorem ext_conj (k : Fin 3) (hfus : D.Fus (repDFG k) 0) :
    ∃ g : G, g⁻¹ * invRep v1 v2 v3 s t (repDFG k) * g = invRep v1 v2 v3 s t 0 ∧
      g⁻¹ * invRep v1 v2 v3 s t 0 * g = invRep v1 v2 v3 s t 1 ∧
      (∀ c ∈ alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t (repDFG k)} : Set G),
        g⁻¹ * c * g ∈ D.H5) ∧
      alpW v1 v2 v3 ≤ (alpP v1 v2 v3 s t ⊓
        centralizer ({invRep v1 v2 v3 s t (repDFG k)} : Set G)).map
          (MulAut.conj g⁻¹).toMonoidHom := by
  set r := invRep v1 v2 v3 s t (repDFG k) with hr
  set z := invRep v1 v2 v3 s t 0 with hz
  set b := invRep v1 v2 v3 s t 1 with hb
  set Cr := alpP v1 v2 v3 s t ⊓ centralizer ({r} : Set G) with hCr
  have hmemCr : ∀ {c : G}, c ∈ Cr ↔
      ∃ c' : AlpE, c' * invE (repDFG k) = invE (repDFG k) * c' ∧ D.E.φ c' = c := by
    intro c
    rw [hCr, hr, D.invRep_eq, AlpEmb.inf_centralizer_eq_map D.E, Subgroup.mem_map]
    simp only [mem_centralizer_singleton_iff]
  have hzc : ∀ c ∈ alpP v1 v2 v3 s t, c * z = z * c :=
    (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl)
  have hzSyl : IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({z} : Set G))
      (centralizer ({z} : Set G)) :=
    isSylowOf_inf_centralizer_of_le D.isSylowOf_P fun c hc =>
      mem_centralizer_singleton_iff.2 (hzc c hc)
  obtain ⟨h, hh⟩ := Fus.symm D hfus
  obtain ⟨g0, hg01, hg02⟩ := exists_conj_extremal D.isPGroup_P hzSyl (u := r) hh
  have hz2 : z * z = 1 := D.rep_sq 0
  have hb2 : b * b = 1 := D.rep_sq 1
  have hzCr : z ∈ Cr := ⟨D.z_mem_P, mem_centralizer_singleton_iff.2
    ((hzc r (AlpEmb.invRep_mem D.E _)).symm)⟩
  have hfac : ∀ {g : G}, g⁻¹ * r * g = z → ∀ a ∈ [1, invE (repDFG k)],
      g⁻¹ * D.E.φ a * g ∈ alpV v1 v2 v3 := by
    intro g hg a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · rw [map_one, mul_one, inv_mul_cancel]
      exact one_mem _
    · rw [← D.invRep_eq, ← hr, hg]
      exact D.rep_mem_V (i := 0) (by decide)
  have hord4 : ∀ f ∈ ord4E k, D.E.φ f ∈ Cr ∧ D.E.φ f * D.E.φ f = z := by
    intro f hf
    obtain ⟨h1, h2⟩ := ord4E_spec hf
    exact ⟨hmemCr.2 ⟨f, h1, rfl⟩, by rw [← map_mul, h2, AlpEmb.φ_zc D.E]; rfl⟩
  have hz' : g0⁻¹ * z * g0 = b ∨ g0⁻¹ * z * g0 = z * b := by
    obtain ⟨x', y', hx', hy', hxy⟩ := cent_nonab_E k
    have hnot :
        ¬ (g0⁻¹ * D.E.φ x' * g0 ∈ alpV v1 v2 v3 ∧ g0⁻¹ * D.E.φ y' * g0 ∈ alpV v1 v2 v3) := by
      rintro ⟨hxV, hyV⟩
      apply hxy
      apply D.E.inj
      have hc := mem_centralizer_iff.1 (D.V_le_centralizer_V hyV) _ hxV
      rw [map_mul, map_mul]
      have e1 : D.E.φ x' * D.E.φ y' =
          g0 * ((g0⁻¹ * D.E.φ x' * g0) * (g0⁻¹ * D.E.φ y' * g0)) * g0⁻¹ := by group
      have e2 : D.E.φ y' * D.E.φ x' =
          g0 * ((g0⁻¹ * D.E.φ y' * g0) * (g0⁻¹ * D.E.φ x' * g0)) * g0⁻¹ := by group
      rw [e1, e2, hc]
    obtain ⟨c', hc'C, hc'V⟩ : ∃ c' : AlpE, c' * invE (repDFG k) = invE (repDFG k) * c' ∧
        g0⁻¹ * D.E.φ c' * g0 ∉ alpV v1 v2 v3 := by
      by_cases hxV : g0⁻¹ * D.E.φ x' * g0 ∈ alpV v1 v2 v3
      · exact ⟨y', hy', fun hyV => hnot ⟨hxV, hyV⟩⟩
      · exact ⟨x', hx', hxV⟩
    obtain ⟨a, ha, f1, hf1, f2, hf2, rfl⟩ := cent_decomp_E k c' hc'C
    have hprod : g0⁻¹ * D.E.φ (a * f1 * f2) * g0 =
        (g0⁻¹ * D.E.φ a * g0) * (g0⁻¹ * D.E.φ f1 * g0) * (g0⁻¹ * D.E.φ f2 * g0) := by
      rw [map_mul, map_mul]
      group
    rw [hprod] at hc'V
    have haV := hfac hg01 a ha
    obtain ⟨f, hf, hfV⟩ : ∃ f ∈ ord4E k, g0⁻¹ * D.E.φ f * g0 ∉ alpV v1 v2 v3 := by
      by_contra hcon
      push Not at hcon
      have hfV : ∀ f ∈ (1 :: ord4E k), g0⁻¹ * D.E.φ f * g0 ∈ alpV v1 v2 v3 := by
        intro f hf
        rcases List.mem_cons.1 hf with rfl | hf
        · rw [map_one, mul_one, inv_mul_cancel]
          exact one_mem _
        · exact hcon f hf
      exact hc'V (mul_mem (mul_mem haV (hfV f1 hf1)) (hfV f2 hf2))
    obtain ⟨hfCr, hfsq⟩ := hord4 f hf
    set x := g0⁻¹ * D.E.φ f * g0 with hx
    have hxP : x ∈ alpP v1 v2 v3 s t := (hg02 _ hfCr).1
    have hxsq : x * x = g0⁻¹ * z * g0 := by rw [hx, ← hfsq]; group
    have hz'1 : g0⁻¹ * z * g0 ≠ 1 := by
      intro h1
      apply D.rep_ne_one 0
      calc z = g0 * (g0⁻¹ * z * g0) * g0⁻¹ := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨y, hy⟩ := (AlpEmb.mem_alpP_iff D.E).1 hxP
    have hyd : y.d ≠ 0 := fun hd => hfV (by
      rw [← hy, AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 hd))
    have hx4 : x ^ 4 = 1 := by
      have e : x ^ 4 = (x * x) * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rw [e, hxsq]
      calc g0⁻¹ * z * g0 * (g0⁻¹ * z * g0) = g0⁻¹ * (z * z) * g0 := by group
        _ = 1 := by rw [hz2]; group
    have hy4 : y ^ 4 = 1 := D.E.inj (by rw [map_pow, hy, hx4, map_one])
    have hy2 : y ^ 2 ≠ 1 := fun h1 => hz'1 (by rw [← hxsq, ← hy, ← map_mul, ← pow_two, h1,
      map_one])
    have hzz' : g0⁻¹ * z * g0 ≠ z := by
      intro h1
      apply D.rep_ne_z k
      calc r = g0 * (g0⁻¹ * r * g0) * g0⁻¹ := by group
        _ = g0 * (g0⁻¹ * z * g0) * g0⁻¹ := by rw [hg01, h1]
        _ = z := by group
    have heq : g0⁻¹ * z * g0 = D.E.φ (y ^ 2) := by rw [← hxsq, ← hy, map_pow, pow_two]
    rcases sq_of_order_four_out D.hF hyd hy4 hy2 with h | h | h
    · exact absurd (by rw [heq, h, AlpEmb.φ_zc D.E]; rfl) hzz'
    · exact Or.inl (by rw [heq, h, ← invE_one, ← D.invRep_eq 1])
    · exact Or.inr (by rw [heq, h, map_mul, ← invE_zero, ← invE_one, ← D.invRep_eq 0,
        ← D.invRep_eq 1])
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : G, g⁻¹ * r * g = z ∧ g⁻¹ * z * g = b ∧
      ∀ c ∈ Cr, g⁻¹ * c * g ∈ alpP v1 v2 v3 s t := by
    rcases hz' with h1 | h1
    · exact ⟨g0, hg01, h1, fun c hc => (hg02 c hc).1⟩
    · obtain ⟨c1, hc1⟩ := conj_bE_zc
      have hc1P : D.E.φ c1 ∈ alpP v1 v2 v3 s t := AlpEmb.φ_mem D.E c1
      have hbE : b = D.E.φ bE := by rw [hb, D.invRep_eq 1, invE_one]
      have hzE : z = D.E.φ zc := by rw [hz, D.invRep_eq 0, invE_zero]
      have hc1G : (D.E.φ c1)⁻¹ * b * D.E.φ c1 = z * b := by
        rw [hbE, hzE, ← map_inv, ← map_mul, ← map_mul, hc1, map_mul]
      refine ⟨g0 * (D.E.φ c1)⁻¹, ?_, ?_, fun c hc => ?_⟩
      · calc (g0 * (D.E.φ c1)⁻¹)⁻¹ * r * (g0 * (D.E.φ c1)⁻¹) =
            D.E.φ c1 * (g0⁻¹ * r * g0) * (D.E.φ c1)⁻¹ := by group
          _ = z := by rw [hg01, hzc _ hc1P, mul_inv_cancel_right]
      · calc (g0 * (D.E.φ c1)⁻¹)⁻¹ * z * (g0 * (D.E.φ c1)⁻¹) =
            D.E.φ c1 * (g0⁻¹ * z * g0) * (D.E.φ c1)⁻¹ := by group
          _ = D.E.φ c1 * ((D.E.φ c1)⁻¹ * b * D.E.φ c1) * (D.E.φ c1)⁻¹ := by rw [h1, hc1G]
          _ = b := by group
      · have h2 := (hg02 c hc).1
        rw [show (g0 * (D.E.φ c1)⁻¹)⁻¹ * c * (g0 * (D.E.φ c1)⁻¹) =
          D.E.φ c1 * (g0⁻¹ * c * g0) * (D.E.φ c1)⁻¹ by group]
        exact mul_mem (mul_mem hc1P h2) (inv_mem hc1P)
  have hH5 : ∀ c ∈ Cr, g⁻¹ * c * g ∈ D.H5 := by
    intro c hc
    obtain ⟨c', hc'C, rfl⟩ := hmemCr.1 hc
    obtain ⟨a, ha, f1, hf1, f2, hf2, rfl⟩ := cent_decomp_E k c' hc'C
    have hprod : g⁻¹ * D.E.φ (a * f1 * f2) * g =
        (g⁻¹ * D.E.φ a * g) * (g⁻¹ * D.E.φ f1 * g) * (g⁻¹ * D.E.φ f2 * g) := by
      rw [map_mul, map_mul]
      group
    have hfH : ∀ f ∈ (1 :: ord4E k), g⁻¹ * D.E.φ f * g ∈ D.H5 := by
      intro f hf
      rcases List.mem_cons.1 hf with rfl | hf
      · rw [map_one, mul_one, inv_mul_cancel]
        exact one_mem _
      · obtain ⟨hfCr, hfsq⟩ := hord4 f hf
        have hsq : (g⁻¹ * D.E.φ f * g) ^ 2 = b := by
          rw [pow_two, show g⁻¹ * D.E.φ f * g * (g⁻¹ * D.E.φ f * g) =
            g⁻¹ * (D.E.φ f * D.E.φ f) * g by group, hfsq, hg2]
        refine D.mem_H5_of_sq (hg3 _ hfCr) ?_ hsq
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two, hb2]
    rw [hprod]
    exact mul_mem (mul_mem (D.V_le_H5 (hfac hg1 a ha)) (hfH f1 hf1)) (hfH f2 hf2)
  refine ⟨g, hg1, hg2, hH5, ?_⟩
  set Y := Cr.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYH5 : Y ≤ D.H5 := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply] using hH5 c hc
  have hcardY : Nat.card Y = 32 := by
    rw [hY, card_map_of_injective (MulAut.conj g⁻¹).injective, hCr, hr,
      AlpEmb.card_centralizer_invRep D.E D.hF]
    have key : ∀ k : Fin 3, (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) (repDFG k) = 32 := by
      decide
    exact key k
  have hYV : 16 ≤ Nat.card (alpV v1 v2 v3 ⊓ Y : Subgroup G) := by
    have h1 := relIndex_mul_card (H := alpV v1 v2 v3) (K := Y)
    have h2 : (alpV v1 v2 v3).relIndex Y ≤ 2 := by
      rw [← D.relIndex_V_H5]
      exact relIndex_le_of_le_right hYH5 (by rw [D.relIndex_V_H5]; norm_num)
    rw [hcardY] at h1
    nlinarith
  refine D.W_le_of_sq hb2 hYV fun y hy => ?_
  obtain ⟨c, hc, rfl⟩ := hy
  obtain ⟨c', hc'C, rfl⟩ := hmemCr.1 hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have e : g⁻¹ * D.E.φ c' * g * (g⁻¹ * D.E.φ c' * g) = g⁻¹ * D.E.φ (c' * c') * g := by
    rw [map_mul]
    group
  rw [e]
  rcases cent_sq_E k c' hc'C with h | h
  · left
    rw [h, map_one, mul_one, inv_mul_cancel]
  · right
    rw [h, AlpEmb.φ_zc D.E]
    exact hg2

end FusCtx

end CFSG.OddStandard.ONanRec

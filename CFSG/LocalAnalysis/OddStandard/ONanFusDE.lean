module

public import CFSG.LocalAnalysis.OddStandard.ONanFusAB

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

set_option maxRecDepth 100000 in
theorem P1_d : ∀ x : AlpE, x * zc = zc * x → x * bE = bE * x →
    x.d = 0 ∨ x.d = 2 ∨ x.d = 5 ∨ x.d = 7 := by
  decide +kernel

theorem P1_comm_d : ∀ a b : Fin 8, (a = 0 ∨ a = 2 ∨ a = 5 ∨ a = 7) →
    (b = 0 ∨ b = 2 ∨ b = 5 ∨ b = 7) → dmul (dmul a b) (dinv (dmul b a)) = 0 := by
  decide

set_option maxRecDepth 100000 in
theorem inv_57_classE : ∀ x : AlpE, (x.d = 5 ∨ x.d = 7) → x * x = 1 →
    ∃ c : AlpE, c⁻¹ * invE 4 * c = x := by
  decide +kernel

theorem rep3_comm_bE : invE 3 * bE = bE * invE 3 := by decide

@[expose] def w0E : AlpE := ⟨0, 1, 0, 1⟩

theorem w0E_facts : w0E.d = 0 ∧ w0E * invE 3 = invE 3 * w0E ∧ w0E * w0E = zc := by decide

set_option maxRecDepth 100000 in
theorem CVd_sq : ∀ w : AlpE, w.d = 0 → w * invE 3 = invE 3 * w → w * w = 1 ∨ w * w = zc := by
  decide +kernel

@[expose] def K4E : List AlpE := [1, zc, bE, zc * bE]

set_option maxRecDepth 100000 in
theorem W_K4_index : ∀ w w' : AlpE, w.d = 0 → w * w = 1 → w'.d = 0 → w' * w' = 1 →
    w ∉ K4E → w' ∉ K4E → w * w' ∈ K4E := by
  decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

@[expose] def InK4 (_D : FusCtx G v1 v2 v3 s t) (w : G) : Prop :=
  w = 1 ∨ w = invRep v1 v2 v3 s t 0 ∨ w = invRep v1 v2 v3 s t 1 ∨
    w = invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1

theorem inK4_iff_model {y : AlpE} : D.InK4 (D.E.φ y) ↔ y ∈ K4E := by
  simp only [InK4, K4E, List.mem_cons, List.not_mem_nil, or_false, D.invRep_eq, invE_zero,
    invE_one, ← map_mul, ← map_one D.E.φ, D.E.inj.eq_iff]

theorem conj_K4 {y w : G} (hyz : y * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * y)
    (hyb : y * invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 1 * y) (hw : D.InK4 w) :
    y * w * y⁻¹ = w := by
  rcases hw with rfl | rfl | rfl | rfl
  · group
  · rw [hyz, mul_inv_cancel_right]
  · rw [hyb, mul_inv_cancel_right]
  · calc y * (invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1) * y⁻¹ =
        (y * invRep v1 v2 v3 s t 0 * y⁻¹) * (y * invRep v1 v2 v3 s t 1 * y⁻¹) := by group
      _ = invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1 := by
        rw [hyz, hyb, mul_inv_cancel_right, mul_inv_cancel_right]

theorem pow_four_mem_centralizer_V {y : G} (hyN : y ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hyz : y * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * y)
    (hyb : y * invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 1 * y) :
    y ^ 4 ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  have hyW : ∀ w ∈ alpW v1 v2 v3, y * w * y⁻¹ ∈ alpW v1 v2 v3 := fun w hw =>
    (mem_normalizer_iff.1 (D.normalizer_V_le_W hyN) w).1 hw
  have hyinvz : y⁻¹ * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * y⁻¹ :=
    calc y⁻¹ * invRep v1 v2 v3 s t 0 = y⁻¹ * (invRep v1 v2 v3 s t 0 * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * invRep v1 v2 v3 s t 0) * y⁻¹ := by rw [hyz]
      _ = invRep v1 v2 v3 s t 0 * y⁻¹ := by group
  have hyinvb : y⁻¹ * invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 1 * y⁻¹ :=
    calc y⁻¹ * invRep v1 v2 v3 s t 1 = y⁻¹ * (invRep v1 v2 v3 s t 1 * y) * y⁻¹ := by group
      _ = y⁻¹ * (y * invRep v1 v2 v3 s t 1) * y⁻¹ := by rw [hyb]
      _ = invRep v1 v2 v3 s t 1 * y⁻¹ := by group
  have hK4W : ∀ {w : G}, D.InK4 w → w ∈ alpW v1 v2 v3 := by
    intro w hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact sq_mul_sq_mem_alpW v1 v2 v3
    · exact (show v1 ^ 2 * v2 ^ 2 ∈ alpW v1 v2 v3 from
        mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    · exact mul_mem (sq_mul_sq_mem_alpW v1 v2 v3)
        (show v1 ^ 2 * v2 ^ 2 ∈ alpW v1 v2 v3 from
          mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
  have hidx : ∀ w ∈ alpW v1 v2 v3, ∀ w' ∈ alpW v1 v2 v3, ¬ D.InK4 w → ¬ D.InK4 w' →
      D.InK4 (w * w') := by
    intro w hw w' hw' hn hn'
    obtain ⟨hwV, hw2⟩ := D.mem_W_iff.1 hw
    obtain ⟨hw'V, hw'2⟩ := D.mem_W_iff.1 hw'
    rw [AlpEmb.alpV_eq_map D.E] at hwV hw'V
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hwV
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hw'V
    rw [D.inK4_iff_model] at hn hn'
    rw [← map_mul, D.inK4_iff_model]
    exact W_K4_index x x' hx (D.E.inj (by rw [map_mul, hw2, map_one])) hx'
      (D.E.inj (by rw [map_mul, hw'2, map_one])) hn hn'
  have hyWK : ∀ w ∈ alpW v1 v2 v3, D.InK4 (y * w * y⁻¹ * w⁻¹) := by
    intro w hw
    by_cases hwK : D.InK4 w
    · rw [D.conj_K4 hyz hyb hwK, mul_inv_cancel]
      exact Or.inl rfl
    · have hnot : ¬ D.InK4 (y * w * y⁻¹) := by
        intro hK
        apply hwK
        have h := D.conj_K4 hyinvz hyinvb hK
        rw [show y⁻¹ * (y * w * y⁻¹) * y⁻¹⁻¹ = w by group] at h
        rw [h]
        exact hK
      have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right (D.mem_W_iff.1 hw).2
      rw [hwinv]
      exact hidx _ (hyW w hw) w hw hnot hwK
  have hy2W : ∀ w ∈ alpW v1 v2 v3, (y * y) * w * (y * y)⁻¹ = w := by
    intro w hw
    set k := y * w * y⁻¹ * w⁻¹ with hk
    have hkK : D.InK4 k := hyWK w hw
    have hk2 : k * k = 1 := (D.mem_W_iff.1 (hK4W hkK)).2
    have h1 : y * w * y⁻¹ = k * w := by rw [hk]; group
    calc (y * y) * w * (y * y)⁻¹ = y * (y * w * y⁻¹) * y⁻¹ := by group
      _ = y * (k * w) * y⁻¹ := by rw [h1]
      _ = (y * k * y⁻¹) * (y * w * y⁻¹) := by group
      _ = k * (k * w) := by rw [D.conj_K4 hyz hyb hkK, h1]
      _ = w := by rw [← mul_assoc, hk2, one_mul]
  rw [mem_centralizer_iff]
  intro v hv
  have hy2N : y * y ∈ normalizer (alpV v1 v2 v3 : Set G) := mul_mem hyN hyN
  have hv' : (y * y) * v * (y * y)⁻¹ ∈ alpV v1 v2 v3 := (mem_normalizer_iff.1 hy2N v).1 hv
  have hvv : v * v ∈ alpW v1 v2 v3 := by
    rw [AlpEmb.alpV_eq_map D.E] at hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hv
    rw [← map_mul]
    refine D.mem_W_iff.2 ⟨?_, ?_⟩
    · rw [AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 (by rw [mul_d, mem_Vsub.1 hx]; rfl))
    · rw [← map_mul, ← map_one D.E.φ]
      congr 1
      have := pow_four_of_mem_V D.hF (mem_Vsub.1 hx)
      rw [← this]
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have hcomm : ∀ {a c : G}, a ∈ alpV v1 v2 v3 → c ∈ alpV v1 v2 v3 → a * c = c * a :=
    fun ha hc => mem_centralizer_iff.1 (D.V_le_centralizer_V hc) _ ha
  set u := (y * y) * v * (y * y)⁻¹ with hu
  set δ := u * v⁻¹ with hδ
  have hδV : δ ∈ alpV v1 v2 v3 := mul_mem hv' (inv_mem hv)
  have hsq : u * u = v * v := by
    rw [hu, show (y * y) * v * (y * y)⁻¹ * ((y * y) * v * (y * y)⁻¹) =
      (y * y) * (v * v) * (y * y)⁻¹ by group, hy2W _ hvv]
  have hδW : δ ∈ alpW v1 v2 v3 := by
    refine D.mem_W_iff.2 ⟨hδV, ?_⟩
    have hc := hcomm hv' (inv_mem hv)
    calc δ * δ = u * (v⁻¹ * u) * v⁻¹ := by rw [hδ]; group
      _ = u * (u * v⁻¹) * v⁻¹ := by rw [← hc]
      _ = (u * u) * (v⁻¹ * v⁻¹) := by group
      _ = 1 := by rw [hsq]; group
  have hy2v : u = δ * v := by rw [hδ]; group
  have hδ2 : δ * δ = 1 := (D.mem_W_iff.1 hδW).2
  have h4 : (y * y * (y * y)) * v * (y * y * (y * y))⁻¹ = v := by
    calc (y * y * (y * y)) * v * (y * y * (y * y))⁻¹ = (y * y) * u * (y * y)⁻¹ := by
          rw [hu]; group
      _ = ((y * y) * δ * (y * y)⁻¹) * ((y * y) * v * (y * y)⁻¹) := by rw [hy2v]; group
      _ = δ * (δ * v) := by rw [hy2W δ hδW, ← hu, hy2v]
      _ = v := by rw [← mul_assoc, hδ2, one_mul]
  have hy4 : y ^ 4 = y * y * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [hy4]
  calc v * (y * y * (y * y)) =
      ((y * y * (y * y)) * v * (y * y * (y * y))⁻¹) * (y * y * (y * y)) := by rw [h4]
    _ = (y * y * (y * y)) * v := by group

theorem z_mem_V' : invRep v1 v2 v3 s t 0 ∈ alpV v1 v2 v3 := D.rep_mem_V (i := 0) (by decide)

theorem b_mem_V : invRep v1 v2 v3 s t 1 ∈ alpV v1 v2 v3 := D.rep_mem_V (i := 1) (by decide)

theorem inClass_zb : D.InClass 1 (invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1) := by
  rw [D.invRep_eq 0, D.invRep_eq 1, invE_zero, invE_one, ← map_mul]
  exact D.inClass_of_model (by rw [invE_one]; exact conj_bE_zc)

theorem conj_K4_mem (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) {n : G}
    (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G)) {w : G} (hw : D.InK4 w) :
    D.InK4 (n⁻¹ * w * n) := by
  have hninv : n⁻¹ ∈ normalizer (alpV v1 v2 v3 : Set G) := inv_mem hn
  have hconjV : ∀ v ∈ alpV v1 v2 v3, n⁻¹ * v * n ∈ alpV v1 v2 v3 := fun v hv => by
    have := (mem_normalizer_iff.1 hninv v).1 hv
    rwa [inv_inv] at this
  rcases hw with rfl | hw
  · left
    group
  obtain ⟨i, hi, hi0⟩ : ∃ i : Fin 7, D.InClass i w ∧ D.Fus 0 i := by
    rcases hw with rfl | rfl | rfl
    · exact ⟨0, D.inClass_rep 0, Fus.refl D 0⟩
    · exact ⟨1, D.inClass_rep 1, hAB⟩
    · exact ⟨1, D.inClass_zb, hAB⟩
  have hwV : w ∈ alpV v1 v2 v3 := by
    rcases hw with rfl | rfl | rfl
    · exact D.z_mem_V'
    · exact D.b_mem_V
    · exact mul_mem D.z_mem_V' D.b_mem_V
  set x := n⁻¹ * w * n with hx
  have hxV : x ∈ alpV v1 v2 v3 := hconjV w hwV
  have hx2 : x * x = 1 := by
    calc x * x = n⁻¹ * (w * w) * n := by rw [hx]; group
      _ = 1 := by rw [hi.sq]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply hi.ne_one
    calc w = n * x * n⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h]; group
  obtain ⟨j, hj⟩ := D.exists_inClass (D.V_le_P hxV) hx2 hx1
  have hj2 := D.le_two_of_inClass_mem_V hj hxV
  have hfus : D.Fus 0 j := hi0.trans D (D.inClass_fus hi hj n rfl)
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · obtain ⟨c, hc, hcx⟩ := hj
    rw [D.z_central hc] at hcx
    exact Or.inr (Or.inl hcx.symm)
  · obtain ⟨c, hc, hcx⟩ := hj
    obtain ⟨c', rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hc
    rw [D.invRep_eq 1, invE_one, ← map_inv, ← map_mul, ← map_mul] at hcx
    rcases conj_bE c' with h | h
    · rw [h, ← invE_one, ← D.invRep_eq 1] at hcx
      exact Or.inr (Or.inr (Or.inl hcx.symm))
    · rw [h, map_mul, ← invE_zero, ← invE_one, ← D.invRep_eq 0, ← D.invRep_eq 1] at hcx
      exact Or.inr (Or.inr (Or.inr hcx.symm))
  · exact absurd hfus hAC

@[expose] def Yhat (_D : FusCtx G v1 v2 v3 s t) : Subgroup G :=
  normalizer (alpV v1 v2 v3 : Set G) ⊓ centralizer ({invRep v1 v2 v3 s t 0} : Set G) ⊓
    centralizer ({invRep v1 v2 v3 s t 1} : Set G)

theorem mem_Yhat {y : G} : y ∈ D.Yhat ↔ y ∈ normalizer (alpV v1 v2 v3 : Set G) ∧
    y * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * y ∧
    y * invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 1 * y := by
  simp only [Yhat, Subgroup.mem_inf, mem_centralizer_singleton_iff, and_assoc]

theorem conj_mem_Yhat (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) {n y : G}
    (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G)) (hy : y ∈ D.Yhat) : n⁻¹ * y * n ∈ D.Yhat := by
  obtain ⟨hyN, hyz, hyb⟩ := D.mem_Yhat.1 hy
  have hninv : n⁻¹ ∈ normalizer (alpV v1 v2 v3 : Set G) := inv_mem hn
  have hfix : ∀ {w : G}, D.InK4 w → (n⁻¹ * y * n) * w = w * (n⁻¹ * y * n) := by
    intro w hw
    have hw' : D.InK4 (n * w * n⁻¹) := by
      have := D.conj_K4_mem hAB hAC hninv hw
      rwa [inv_inv] at this
    have h1 := D.conj_K4 hyz hyb hw'
    calc n⁻¹ * y * n * w = n⁻¹ * (y * (n * w * n⁻¹) * y⁻¹) * y * n := by group
      _ = n⁻¹ * (n * w * n⁻¹) * y * n := by rw [h1]
      _ = w * (n⁻¹ * y * n) := by group
  refine D.mem_Yhat.2 ⟨mul_mem (mul_mem hninv hyN) hn, hfix (Or.inr (Or.inl rfl)),
    hfix (Or.inr (Or.inr (Or.inl rfl)))⟩

theorem Yhat_le_N : D.Yhat ≤ normalizer (alpV v1 v2 v3 : Set G) := fun _ hy => (D.mem_Yhat.1 hy).1

theorem N_le_normalizer_Yhat (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) :
    normalizer (alpV v1 v2 v3 : Set G) ≤ normalizer (D.Yhat : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro y
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · have := D.conj_mem_Yhat hAB hAC (inv_mem hn) hy
    rwa [inv_inv] at this
  · have := D.conj_mem_Yhat hAB hAC hn hy
    rwa [show n⁻¹ * (n * y * n⁻¹) * n = y by group] at this

theorem isSylowOf_P1 (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) :
    IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ D.Yhat) D.Yhat := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsSylowOf 2 (alpP v1 v2 v3 s t) (normalizer (alpV v1 v2 v3 : Set G)) :=
    D.isSylowOf_P.of_le D.P_le_normalizer_V le_top
  exact hP.inf_of_le_normalizer D.Yhat_le_N (D.N_le_normalizer_Yhat hAB hAC)

theorem exists_P1_same_act (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) {x : G} (hx : x ∈ D.Yhat) :
    ∃ p ∈ alpP v1 v2 v3 s t ⊓ D.Yhat, ∀ v ∈ alpV v1 v2 v3, x * v * x⁻¹ = p * v * p⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : D.Yhat →* MulAut (alpV v1 v2 v3) :=
    (alpV v1 v2 v3).normalizerMonoidHom.comp (Subgroup.inclusion D.Yhat_le_N)
  have hf : ∀ (q : D.Yhat) (v : alpV v1 v2 v3), ((f q v : alpV v1 v2 v3) : G) =
      (q : G) * v * (q : G)⁻¹ := fun q v => rfl
  have hfrange : IsPGroup 2 f.range := by
    refine IsPGroup.iff_orderOf.2 fun q => ?_
    obtain ⟨q0, hq0⟩ := q.2
    have hf4 : f (q0 ^ 4) = 1 := by
      refine MulEquiv.ext fun v => Subtype.ext ?_
      rw [hf, MulAut.one_apply, Subgroup.coe_pow]
      obtain ⟨hN, hz, hb⟩ := D.mem_Yhat.1 q0.2
      have h4 := D.pow_four_mem_centralizer_V hN hz hb
      rw [← mem_centralizer_iff.1 h4 v v.2, mul_inv_cancel_right]
    have hq4 : q ^ 4 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hq0, ← map_pow, hf4]
      rfl
    have hdvd : orderOf q ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by simpa using hq4)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  obtain ⟨Q, hQ⟩ := D.isSylowOf_P1 hAB hAC
  set Q' := Q.mapSurjective f.rangeRestrict_surjective with hQ'
  have htop : IsPGroup 2 (⊤ : Subgroup f.range) := hfrange.of_equiv Subgroup.topEquiv.symm
  have hQ'top : (Q' : Subgroup f.range) = ⊤ := (Q'.is_maximal' htop le_top).symm
  have hmem : f.rangeRestrict ⟨x, hx⟩ ∈ (Q' : Subgroup f.range) := by
    rw [hQ'top]
    exact mem_top _
  rw [hQ', Sylow.coe_mapSurjective] at hmem
  obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.1 hmem
  have hqP : (q : G) ∈ alpP v1 v2 v3 s t ⊓ D.Yhat := by
    rw [← hQ]
    exact ⟨q, hq, rfl⟩
  refine ⟨q, hqP, fun v hv => ?_⟩
  have h1 : f q = f ⟨x, hx⟩ := congrArg Subtype.val hqx
  have h2 := congrArg (fun φ : MulAut (alpV v1 v2 v3) => ((φ ⟨v, hv⟩ : alpV v1 v2 v3) : G)) h1
  simp only [hf] at h2
  exact h2.symm

@[expose] def SameAct (_D : FusCtx G v1 v2 v3 s t) (x x' : G) : Prop :=
  ∀ v ∈ alpV v1 v2 v3, x * v * x⁻¹ = x' * v * x'⁻¹

theorem SameAct.inv {x x' : G} (h : D.SameAct x x')
    (hx' : x' ∈ normalizer (alpV v1 v2 v3 : Set G)) :
    ∀ v ∈ alpV v1 v2 v3, x⁻¹ * v * x = x'⁻¹ * v * x' := by
  intro v hv
  have hw : x'⁻¹ * v * x' ∈ alpV v1 v2 v3 := by
    have := (mem_normalizer_iff.1 (inv_mem hx') v).1 hv
    rwa [inv_inv] at this
  have h1 := h _ hw
  rw [show x' * (x'⁻¹ * v * x') * x'⁻¹ = v by group] at h1
  calc x⁻¹ * v * x = x⁻¹ * (x * (x'⁻¹ * v * x') * x⁻¹) * x := by rw [h1]
    _ = x'⁻¹ * v * x' := by group

theorem SameAct.conj {c pc y py : G} (hc : D.SameAct c pc) (hy : D.SameAct y py)
    (hcN : c ∈ normalizer (alpV v1 v2 v3 : Set G)) (hpcN : pc ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hyN : y ∈ normalizer (alpV v1 v2 v3 : Set G)) :
    D.SameAct (c * y * c⁻¹) (pc * py * pc⁻¹) := by
  intro v hv
  have hinv := SameAct.inv D hc hpcN
  have hw : c⁻¹ * v * c ∈ alpV v1 v2 v3 := by
    have := (mem_normalizer_iff.1 (inv_mem hcN) v).1 hv
    rwa [inv_inv] at this
  have hw' : y * (c⁻¹ * v * c) * y⁻¹ ∈ alpV v1 v2 v3 := (mem_normalizer_iff.1 hyN _).1 hw
  calc c * y * c⁻¹ * v * (c * y * c⁻¹)⁻¹ = c * (y * (c⁻¹ * v * c) * y⁻¹) * c⁻¹ := by group
    _ = pc * (py * (pc⁻¹ * v * pc) * py⁻¹) * pc⁻¹ := by rw [hc _ hw', hy _ hw, hinv v hv]
    _ = pc * py * pc⁻¹ * v * (pc * py * pc⁻¹)⁻¹ := by group

theorem sameAct_mul_V {k x : G} (hk : k ∈ alpV v1 v2 v3)
    (hx : x ∈ normalizer (alpV v1 v2 v3 : Set G)) : D.SameAct (k * x) x := by
  intro v hv
  have hw : x * v * x⁻¹ ∈ alpV v1 v2 v3 := (mem_normalizer_iff.1 hx v).1 hv
  have hc : k * (x * v * x⁻¹) = (x * v * x⁻¹) * k :=
    (mem_centralizer_iff.1 (D.V_le_centralizer_V hw) _ hk)
  calc k * x * v * (k * x)⁻¹ = k * (x * v * x⁻¹) * k⁻¹ := by group
    _ = x * v * x⁻¹ := by rw [hc, mul_inv_cancel_right]

theorem fus_DE (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) : D.Fus 3 4 := by
  classical
  have hzc : ∀ c ∈ alpP v1 v2 v3 s t, c * invRep v1 v2 v3 s t 0 = invRep v1 v2 v3 s t 0 * c :=
    (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl)
  obtain ⟨g0, hg0⟩ := id hAB
  obtain ⟨h, hhN, hh⟩ := D.fuse_V (D.V_le_centralizer_V D.z_mem_V')
    (D.V_le_centralizer_V D.b_mem_V) ⟨g0⁻¹, by rw [inv_inv]; exact hg0⟩
  have hrP : invRep v1 v2 v3 s t 3 ∈ alpP v1 v2 v3 s t := AlpEmb.invRep_mem D.E 3
  have hrN := D.P_le_normalizer_V hrP
  have hrb : invRep v1 v2 v3 s t 3 * invRep v1 v2 v3 s t 1 =
      invRep v1 v2 v3 s t 1 * invRep v1 v2 v3 s t 3 := by
    rw [D.invRep_eq 3, D.invRep_eq 1, invE_one, ← map_mul, ← map_mul, rep3_comm_bE]
  have hrY : invRep v1 v2 v3 s t 3 ∈ D.Yhat := D.mem_Yhat.2 ⟨hrN, hzc _ hrP, hrb⟩
  set y := h⁻¹ * invRep v1 v2 v3 s t 3 * h with hy
  have hyY : y ∈ D.Yhat := D.conj_mem_Yhat hAB hAC hhN hrY
  have hyN := D.Yhat_le_N hyY
  have hy2 : y * y = 1 := by
    calc y * y = h⁻¹ * (invRep v1 v2 v3 s t 3 * invRep v1 v2 v3 s t 3) * h := by rw [hy]; group
      _ = 1 := by rw [D.rep_sq 3]; group
  have hypg : IsPGroup 2 (zpowers y) := by
    have hdvd : orderOf y ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hy2)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨c, hcY, hc⟩ := exists_conj_le_of_isSylowOf (D.isSylowOf_P1 hAB hAC)
    (zpowers_le.2 hyY) hypg
  have hcN := D.Yhat_le_N hcY
  set u := c * y * c⁻¹ with hu
  have huP1 : u ∈ alpP v1 v2 v3 s t ⊓ D.Yhat := hc y (mem_zpowers y)
  obtain ⟨pc, hpc, hpcact⟩ := D.exists_P1_same_act hAB hAC hcY
  obtain ⟨py, hpy, hpyact⟩ := D.exists_P1_same_act hAB hAC hyY
  have hpcN := D.Yhat_le_N hpc.2
  have hpyN := D.Yhat_le_N hpy.2
  have hcomm : pc * py * pc⁻¹ * py⁻¹ ∈ alpV v1 v2 v3 := by
    obtain ⟨pc', hpc'⟩ := (AlpEmb.mem_alpP_iff D.E).1 hpc.1
    obtain ⟨py', hpy'⟩ := (AlpEmb.mem_alpP_iff D.E).1 hpy.1
    have hd : ∀ {p : G} {p' : AlpE}, p ∈ alpP v1 v2 v3 s t ⊓ D.Yhat → D.E.φ p' = p →
        p'.d = 0 ∨ p'.d = 2 ∨ p'.d = 5 ∨ p'.d = 7 := by
      intro p p' hp hp'
      obtain ⟨-, hz, hb⟩ := D.mem_Yhat.1 hp.2
      refine P1_d p' (D.E.inj ?_) (D.E.inj ?_)
      · rw [map_mul, map_mul, hp', AlpEmb.φ_zc D.E]
        exact hz
      · rw [map_mul, map_mul, hp', ← invE_one, ← D.invRep_eq 1]
        exact hb
    rw [← hpc', ← hpy', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      AlpEmb.alpV_eq_map D.E]
    refine Subgroup.mem_map_of_mem _ (mem_Vsub.2 ?_)
    rw [show pc' * py' * pc'⁻¹ * py'⁻¹ = (pc' * py') * (py' * pc')⁻¹ by group, mul_d, mul_d, inv_d,
      mul_d]
    exact P1_comm_d _ _ (hd hpc hpc') (hd hpy hpy')
  have hact : D.SameAct u y := by
    intro v hv
    have h1 := SameAct.conj D hpcact hpyact hcN hpcN hyN v hv
    have h2 := D.sameAct_mul_V hcomm hpyN v hv
    rw [show pc * py * pc⁻¹ * py⁻¹ * py = pc * py * pc⁻¹ by group] at h2
    rw [h1, h2, hpyact v hv]
  obtain ⟨u', hu'⟩ := (AlpEmb.mem_alpP_iff D.E).1 huP1.1
  have hu'd : u'.d = 0 ∨ u'.d = 2 ∨ u'.d = 5 ∨ u'.d = 7 := by
    obtain ⟨-, hz, hb⟩ := D.mem_Yhat.1 huP1.2
    refine P1_d u' (D.E.inj ?_) (D.E.inj ?_)
    · rw [map_mul, map_mul, hu', AlpEmb.φ_zc D.E]
      exact hz
    · rw [map_mul, map_mul, hu', ← invE_one, ← D.invRep_eq 1]
      exact hb
  have hu2 : u * u = 1 := by
    calc u * u = c * (y * y) * c⁻¹ := by rw [hu]; group
      _ = 1 := by rw [hy2]; group
  rcases hu'd with h0 | h2 | h57 | h57
  ·
    exfalso
    have huV : u ∈ alpV v1 v2 v3 := by
      rw [← hu', AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 h0)
    have hrC : invRep v1 v2 v3 s t 3 ∈ centralizer (alpV v1 v2 v3 : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have hw : h⁻¹ * v * h ∈ alpV v1 v2 v3 := by
        have := (mem_normalizer_iff.1 (inv_mem hhN) v).1 hv
        rwa [inv_inv] at this
      have h1 := hact _ hw
      have h3 : u * (h⁻¹ * v * h) * u⁻¹ = h⁻¹ * v * h := by
        have hc' := mem_centralizer_iff.1 (D.V_le_centralizer_V hw) u huV
        rw [hc', mul_inv_cancel_right]
      rw [h3] at h1
      have h4 : invRep v1 v2 v3 s t 3 * v * (invRep v1 v2 v3 s t 3)⁻¹ = v := by
        calc invRep v1 v2 v3 s t 3 * v * (invRep v1 v2 v3 s t 3)⁻¹ =
            h * (y * (h⁻¹ * v * h) * y⁻¹) * h⁻¹ := by rw [hy]; group
          _ = v := by rw [← h1]; group
      calc v * invRep v1 v2 v3 s t 3 =
          (invRep v1 v2 v3 s t 3 * v * (invRep v1 v2 v3 s t 3)⁻¹) * invRep v1 v2 v3 s t 3 := by
            rw [h4]
        _ = invRep v1 v2 v3 s t 3 * v := by group
    have hrV : invRep v1 v2 v3 s t 3 ∈ alpV v1 v2 v3 := by
      rw [← AlpEmb.centralizer_alpV D.E D.hF]
      exact ⟨hrP, hrC⟩
    rw [D.invRep_eq 3, AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj, mem_Vsub] at hrV
    exact absurd hrV (by decide)
  ·
    exfalso
    have hur : u * (invRep v1 v2 v3 s t 3)⁻¹ ∈ alpV v1 v2 v3 := by
      rw [← hu', D.invRep_eq 3, ← map_inv, ← map_mul, AlpEmb.alpV_eq_map D.E]
      refine Subgroup.mem_map_of_mem _ (mem_Vsub.2 ?_)
      rw [mul_d, inv_d, h2]
      decide
    have hact2 : D.SameAct y (invRep v1 v2 v3 s t 3) := by
      intro v hv
      have h1 := D.sameAct_mul_V hur hrN v hv
      rw [show u * (invRep v1 v2 v3 s t 3)⁻¹ * invRep v1 v2 v3 s t 3 = u by group] at h1
      rw [← hact v hv, h1]
    obtain ⟨hw0d, hw0r, hw0sq⟩ := w0E_facts
    set w := h⁻¹ * D.E.φ w0E * h with hw
    have hw0V : D.E.φ w0E ∈ alpV v1 v2 v3 := by
      rw [AlpEmb.alpV_eq_map D.E]
      exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 hw0d)
    have hwV : w ∈ alpV v1 v2 v3 := by
      have := (mem_normalizer_iff.1 (inv_mem hhN) _).1 hw0V
      rwa [inv_inv] at this
    have hw0r' : invRep v1 v2 v3 s t 3 * D.E.φ w0E * (invRep v1 v2 v3 s t 3)⁻¹ = D.E.φ w0E := by
      rw [D.invRep_eq 3, ← map_mul, hw0r.symm, map_mul, mul_inv_cancel_right]
    have hwr : invRep v1 v2 v3 s t 3 * w = w * invRep v1 v2 v3 s t 3 := by
      have h1 := hact2 w hwV
      have h3 : y * w * y⁻¹ = w := by
        rw [hy, hw]
        calc h⁻¹ * invRep v1 v2 v3 s t 3 * h * (h⁻¹ * D.E.φ w0E * h) *
            (h⁻¹ * invRep v1 v2 v3 s t 3 * h)⁻¹ =
            h⁻¹ * (invRep v1 v2 v3 s t 3 * D.E.φ w0E * (invRep v1 v2 v3 s t 3)⁻¹) * h := by group
          _ = h⁻¹ * D.E.φ w0E * h := by rw [hw0r']
      rw [h3] at h1
      calc invRep v1 v2 v3 s t 3 * w =
          (invRep v1 v2 v3 s t 3 * w * (invRep v1 v2 v3 s t 3)⁻¹) * invRep v1 v2 v3 s t 3 := by
            group
        _ = w * invRep v1 v2 v3 s t 3 := by rw [← h1]
    obtain ⟨w', hw'⟩ := (AlpEmb.mem_alpP_iff D.E).1 (D.V_le_P hwV)
    have hw'd : w'.d = 0 := by
      have := hwV
      rw [← hw', AlpEmb.alpV_eq_map D.E, Subgroup.mem_map_iff_mem D.E.inj] at this
      exact this
    have hw'r : w' * invE 3 = invE 3 * w' :=
      D.E.inj (by rw [map_mul, map_mul, hw', ← D.invRep_eq 3]; exact hwr.symm)
    have hwsq : w * w = invRep v1 v2 v3 s t 1 := by
      rw [hw, show h⁻¹ * D.E.φ w0E * h * (h⁻¹ * D.E.φ w0E * h) =
        h⁻¹ * D.E.φ (w0E * w0E) * h by rw [map_mul]; group, hw0sq, AlpEmb.φ_zc D.E]
      exact hh
    rcases CVd_sq w' hw'd hw'r with h1 | h1
    · apply D.rep_ne_one 1
      rw [← hwsq, ← hw', ← map_mul, h1, map_one]
    · have : invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 0 := by
        rw [← hwsq, ← hw', ← map_mul, h1, AlpEmb.φ_zc D.E]
        rfl
      exact absurd (InClass.unique D (this ▸ D.inClass_rep 1) (D.inClass_rep 0)) (by decide)
  all_goals
    have hu'2 : u' * u' = 1 := D.E.inj (by rw [map_mul, hu', hu2, map_one])
    have hcls : D.InClass 4 u := by
      rw [← hu']
      exact D.inClass_of_model (inv_57_classE u' (by tauto) hu'2)
    exact D.inClass_fus (D.inClass_rep 3) hcls (h * c⁻¹) (by rw [hu, hy]; group)

end FusCtx

end CFSG.OddStandard.ONanRec

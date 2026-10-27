module

public import CFSG.LocalAnalysis.StandardType.GGTWDNatCheck2
public import Certificates.Data.Kernel.TWDK

public section

namespace CFSG.StandardType.TWDK

open Certificates.TWDK Certificates.DepASmall Certificates.TwoDepSmall Certificates.TwoDepSmallN
open CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p N : ℕ}

theorem kAll2_mem {α β : Type} (t : α → β → Bool) (cs : List α) :
    ∀ is : List β, kAll2 t cs is = true → ∀ c ∈ cs, ∃ i, t c i = true := by
  induction cs with
  | nil => intro _ _ c hc; simp at hc
  | cons c cs ih =>
    intro is h c' hc'
    cases is with
    | nil => simp [kAll2] at h
    | cons i is =>
      simp only [kAll2, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact ⟨i, h.1⟩
      · exact ih is h.2 c' hc'

theorem single_of_cover {F : List GGDepANPair} {S : List KSingleE} {R : List KResE}
    (hC : kCover N S R = true) (hS : ∀ i < S.length, kSingleAt p N F S i = true)
    (posn c0 mi ni : ℕ) (hpos : posn = 0 ∨ posn = 1) (hc0 : c0 < N - 1) (hmi : mi = 1 ∨ mi = 2)
    (hni : ni = 1 ∨ ni = 2) (hpat : ggTWNPat1B N posn c0 mi ni = true) :
    ∃ wits idx, kSingle p N F (posn, c0, mi, ni) wits idx = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c0 (List.mem_range.mpr hc0)
  rw [Bool.and_eq_true] at h2
  have h3 := List.all_eq_true.mp h2.1 mi (by rcases hmi with rfl | rfl <;> simp)
  have h4 := List.all_eq_true.mp h3 ni (by rcases hni with rfl | rfl <;> simp)
  have h5 : (posn, c0, mi, ni) ∈ S.map (·.1) := by simpa [hpat] using h4
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hS i hi
  simp only [kSingleAt, List.getElem?_eq_getElem hi] at h6
  rw [hek] at h6
  exact ⟨_, _, h6⟩

theorem res_of_cover {F : List GGDepANPair} {S : List KSingleE} {R : List KResE}
    (hC : kCover N S R = true) (hR : ∀ i < R.length, kResAt p N F R i = true)
    (posn c : ℕ) (hpos : posn = 0 ∨ posn = 1) (hc : c < N - 1)
    (hpat : ggTWNPat2B N posn c none = true) :
    ∃ sw ra ent, kRes p N F (posn, c) sw ra ent = true := by
  have h1 := List.all_eq_true.mp hC posn (by rcases hpos with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.mp h1 c (List.mem_range.mpr hc)
  rw [Bool.and_eq_true] at h2
  have h5 : (posn, c) ∈ R.map (·.1) := by simpa [hpat] using h2.2
  obtain ⟨e, he, hek⟩ := List.mem_map.mp h5
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
  have h6 := hR i hi
  simp only [kResAt, List.getElem?_eq_getElem hi] at h6
  rw [hek] at h6
  exact ⟨_, _, _, h6⟩

theorem kFrame_eq {F : List GGDepANPair} (hF : kFrameOK p N F = true) : F = kFrame p N := by
  simpa [kFrameOK] using hF

theorem kGen_eq {F : List GGDepANPair} (hF : kFrameOK p N F = true) (news : List GGDepANPair)
    (g : ℕ) : kGen N F news g = ggTWDGen p N news g := by
  rw [kFrame_eq hF]
  unfold kGen ggTWDGen
  split_ifs with h
  · have hg : g < (kFrame p N).length := by simp [kFrame]; omega
    rw [List.getD_eq_getElem (l := kFrame p N) (d := ([], [])) (n := g) hg]
    simp [kFrame]
  · rfl

theorem kWord_eq {F : List GGDepANPair} (hF : kFrameOK p N F = true) (news : List GGDepANPair)
    (q : GGDepANPair) (w : List ℕ) : kWord p N F news q w = ggTWDWord p N news q w := by
  simp only [kWord, ggTWDWord, kGen_eq hF]

theorem kTest_sound [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) {F : List GGDepANPair}
    (hF : kFrameOK p N F = true) {news : List GGDepANPair}
    (hnews : ∀ q ∈ news, GGTWDValid p N q) (w : KWit) (h : kTest p N F news w = true) :
    ∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g := by
  obtain ⟨g1, w1, g2, w2⟩ := w
  simp only [kTest, Bool.and_eq_true, kWord_eq hF, kGen_eq hF] at h
  exact ggTWDTv_sound hp2 hN hnews ⟨g1, w1, g2, w2⟩ h.1 h.2

theorem twDot_add_left (a b v : GGDepAE p N) :
    ggDepAdot (a + b) v = ggDepAdot a v + ggDepAdot b v := by
  simp [ggDepAdot, add_mul, Finset.sum_add_distrib]

theorem twDot_smul_left (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot (k • a) v = k * ggDepAdot a v := by
  simp [ggDepAdot, Finset.mul_sum, mul_assoc]

theorem twDot_sub_left (a b v : GGDepAE p N) :
    ggDepAdot (a - b) v = ggDepAdot a v - ggDepAdot b v := by
  simp [ggDepAdot, sub_mul, Finset.sum_sub_distrib]

theorem twDot_add_right (a v w : GGDepAE p N) :
    ggDepAdot a (v + w) = ggDepAdot a v + ggDepAdot a w := by
  simp [ggDepAdot, mul_add, Finset.sum_add_distrib]

theorem twDot_sub_right (a v w : GGDepAE p N) :
    ggDepAdot a (v - w) = ggDepAdot a v - ggDepAdot a w := by
  simp [ggDepAdot, mul_sub, Finset.sum_sub_distrib]

theorem twDot_smul_right (k : ZMod p) (a v : GGDepAE p N) :
    ggDepAdot a (k • v) = k * ggDepAdot a v := by
  simp [ggDepAdot, Finset.mul_sum, mul_left_comm]

theorem twDot_single_right (a : GGDepAE p N) (k : Fin N) :
    ggDepAdot a (Pi.single k 1) = a k := by
  simp [ggDepAdot, Pi.single_apply]

theorem twDot_single_left (k : Fin N) (v : GGDepAE p N) :
    ggDepAdot (Pi.single k 1) v = v k := by
  simp [ggDepAdot, Pi.single_apply]

@[expose] def vAt (v : GGDepAE p N) (k : ℕ) : ZMod p := if h : k < N then v ⟨k, h⟩ else 0

theorem vAt_val (v : GGDepAE p N) (j : Fin N) : vAt v j.val = v j := dif_pos j.isLt

theorem vAt_lt (v : GGDepAE p N) {k : ℕ} (hk : k < N) : vAt v k = v ⟨k, hk⟩ := dif_pos hk

theorem vAt_add (f g : GGDepAE p N) (k : ℕ) : vAt (f + g) k = vAt f k + vAt g k := by
  unfold vAt; split_ifs <;> simp

theorem vAt_smul (c : ZMod p) (f : GGDepAE p N) (k : ℕ) : vAt (c • f) k = c * vAt f k := by
  unfold vAt; split_ifs <;> simp

theorem twDot_x (hN : 1 ≤ N) (f : GGDepAE p N) : ggDepAdot f (ggDepAx p N) = vAt f (N - 1) := by
  rw [l05nND_dot_ax f hN, vAt_lt f (by omega : N - 1 < N)]

theorem twH_short (i : Fin (N - 1)) (hi : i.val + 2 < N) :
    ggDepAh p N i = Pi.single (⟨i.val, by omega⟩ : Fin N) 1 - Pi.single ⟨i.val + 1, by omega⟩ 1 := by
  have := i.isLt
  funext j
  simp only [ggDepAh, Pi.sub_apply, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | simp

theorem twA_short (i : Fin (N - 1)) (hi : i.val + 2 < N) :
    ggDepAα p N i = Pi.single (⟨i.val, by omega⟩ : Fin N) 1 - Pi.single ⟨i.val + 1, by omega⟩ 1 := by
  have := i.isLt
  funext j
  simp only [ggDepAα, Pi.sub_apply, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | simp

theorem twDot_h_short (f : GGDepAE p N) (i : Fin (N - 1)) (hi : i.val + 2 < N) :
    ggDepAdot f (ggDepAh p N i) = vAt f i.val - vAt f (i.val + 1) := by
  rw [twH_short i hi, twDot_sub_right, twDot_single_right, twDot_single_right, vAt_lt, vAt_lt]

theorem twDot_A_short (v : GGDepAE p N) (i : Fin (N - 1)) (hi : i.val + 2 < N) :
    ggDepAdot (ggDepAα p N i) v = vAt v i.val - vAt v (i.val + 1) := by
  rw [twA_short i hi, twDot_sub_left, twDot_single_left, twDot_single_left, vAt_lt, vAt_lt]

theorem twDot_A_x (hN : 1 ≤ N) (i : Fin (N - 1)) : ggDepAdot (ggDepAα p N i) (ggDepAx p N) = 0 := by
  rw [twDot_x hN, vAt_lt _ (by omega : N - 1 < N)]
  simp [ggDepAα, show N - 1 + 1 = N by omega]

@[expose] def twVec (a b : ZMod p) : GGDepAE p N := fun j => if j.val + 1 = N then b else a

theorem vAt_twVec (a b : ZMod p) {k : ℕ} (hk : k < N) :
    vAt (twVec (N := N) a b) k = if k + 1 = N then b else a := by
  rw [vAt_lt _ hk]; rfl

theorem twVec_dot_h (hpN : p ∣ N) (hN : 2 ≤ N) (a b : ZMod p) (i : Fin (N - 1)) :
    ggDepAdot (twVec a b) (ggDepAh p N i) = 0 := by
  have hiN := i.isLt
  by_cases hi : i.val + 2 < N
  · rw [twDot_h_short _ i hi, vAt_twVec (N := N) a b (k := i.val) (by omega),
      vAt_twVec (N := N) a b (k := i.val + 1) (by omega),
      if_neg (show ¬ (i.val + 1 = N) by omega), if_neg (show ¬ (i.val + 1 + 1 = N) by omega),
      sub_self]
  · have hi' : i.val + 2 = N := by omega
    have hN0 : (N : ZMod p) = 0 := by
      obtain ⟨k, hk⟩ := hpN
      rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    have hsum : ∀ j : Fin N, twVec a b j * ggDepAh p N i j =
        a - (if j = (⟨N - 1, by omega⟩ : Fin N) then a else 0) +
          (if j = (⟨N - 2, by omega⟩ : Fin N) then a else 0) := by
      intro j
      have := j.isLt
      simp only [twVec, ggDepAh, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | (exfalso; omega) | ring
    rw [ggDepAdot, Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, hN0]
    ring

@[expose] def twT (ψ : GGDepAE p N) : Module.End (ZMod p) (GGDepAE p N) :=
  LinearMap.id + (ggDepAform ψ).smulRight (ggDepAx p N)

theorem twT_apply (ψ v : GGDepAE p N) : twT ψ v = v + ggDepAdot ψ v • ggDepAx p N := by
  simp [twT, ggDepAform, ggDepAdot, LinearMap.smulRight_apply, smul_eq_mul]

theorem twDot_twT (f ψ v : GGDepAE p N) :
    ggDepAdot f (twT ψ v) = ggDepAdot (f + ggDepAdot f (ggDepAx p N) • ψ) v := by
  rw [twT_apply, twDot_add_right, twDot_smul_right, twDot_add_left, twDot_smul_left]
  ring

theorem twT_comp (ψ ψ' : GGDepAE p N) (h : ψ + (1 + ggDepAdot ψ (ggDepAx p N)) • ψ' = 0) :
    twT ψ * twT ψ' = 1 := by
  apply LinearMap.ext
  intro v
  rw [Module.End.mul_apply, Module.End.one_apply, twT_apply ψ, twT_apply ψ', twDot_add_right,
    twDot_smul_right]
  have h2 : ggDepAdot (ψ + (1 + ggDepAdot ψ (ggDepAx p N)) • ψ') v = 0 := by
    rw [h]; simp [ggDepAdot]
  rw [twDot_add_left, twDot_smul_left] at h2
  have h3 : ggDepAdot ψ' v + (ggDepAdot ψ v + ggDepAdot ψ' v * ggDepAdot ψ (ggDepAx p N)) = 0 := by
    linear_combination h2
  rw [add_assoc, ← add_smul, h3, zero_smul, add_zero]

theorem twT_comm (ψ c f : GGDepAE p N) (hψc : ggDepAdot ψ c = 0)
    (hfx : ggDepAdot f (ggDepAx p N) = 0) :
    twT ψ * ggDepARefl c f = ggDepARefl c f * twT ψ := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, l05nPT_refl_apply, twT_apply, twDot_sub_right, twDot_add_right,
    twDot_smul_right, hψc, hfx, mul_zero, sub_zero, add_zero]
  abel

theorem twApply_of_mul {e d : Module.End (ZMod p) (GGDepAE p N)} (h : d * e = 1)
    (w : GGDepAE p N) : d (e w) = w := by
  rw [← Module.End.mul_apply, h, Module.End.one_apply]

theorem twRefl_back {e d : Module.End (ZMod p) (GGDepAE p N)} (hde : d * e = 1)
    (c f f' : GGDepAE p N) (hf : ∀ v, ggDepAdot f' v = ggDepAdot f (d v)) :
    d * ggDepARefl (e c) f' * e = ggDepARefl c f := by
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply, l05nPT_refl_apply, map_sub, map_smul, hf, twApply_of_mul hde]

theorem twIsTv_conj {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1)
    (hde : d * e = 1) {g : Module.End (ZMod p) (GGDepAE p N)} (hg : GGDepAIsTv g) :
    GGDepAIsTv (d * g * e) := by
  have hv := twApply_of_mul hde
  have hv' := twApply_of_mul hed
  have hinj : Function.Injective d := fun a b hab => by rw [← hv' a, ← hv' b, hab]
  have hsurj : LinearMap.range e = ⊤ := LinearMap.range_eq_top.mpr fun w => ⟨d w, hv' w⟩
  have hcomp : d * g * e - LinearMap.id = d.comp ((g - LinearMap.id).comp e) := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.comp_apply, LinearMap.id_apply,
      map_sub, hv]
  refine ⟨?_, ?_⟩
  · rw [hcomp, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ hsurj]
    rw [← hg.1]
    exact (Submodule.equivMapOfInjective d hinj _).finrank_eq.symm
  · intro w
    simp only [Module.End.mul_apply]
    have h1 : d (g (e w)) - w = d (g (e w) - e w) := by rw [map_sub, hv]
    rw [h1, hv', hg.2]

theorem tv_back {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1) (hde : d * e = 1)
    {T T' : Set (Module.End (ZMod p) (GGDepAE p N))}
    (hT : ∀ s ∈ T', d * s * e ∈ Submonoid.closure T)
    (h : ∃ g ∈ Submonoid.closure T', GGDepAIsTv g) :
    ∃ g ∈ Submonoid.closure T, GGDepAIsTv g := by
  obtain ⟨g, hg, htv⟩ := h
  let C : Module.End (ZMod p) (GGDepAE p N) →* Module.End (ZMod p) (GGDepAE p N) :=
    { toFun := fun s => d * s * e
      map_one' := by simp only [mul_one, hde]
      map_mul' := fun s t => by
        simp only [mul_assoc]
        rw [← mul_assoc e d (t * e), hed, one_mul] }
  have hle : Submonoid.closure T' ≤ (Submonoid.closure T).comap C :=
    Submonoid.closure_le.mpr fun s hs => hT s hs
  exact ⟨d * g * e, hle hg, twIsTv_conj hed hde htv⟩

theorem tv_back_gens {e d : Module.End (ZMod p) (GGDepAE p N)} (hed : e * d = 1)
    (hde : d * e = 1)
    (hfr : ∀ i : Fin (N - 1), d * ggDepARefl (ggDepAh p N i) (ggDepAα p N i) * e =
      ggDepARefl (ggDepAh p N i) (ggDepAα p N i))
    {news : List GGDepANPair} {T : Set (Module.End (ZMod p) (GGDepAE p N))}
    (hfT : Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ⊆ T)
    (hq : ∀ q ∈ news, d * ggTWDRflOf p N q * e ∈ T)
    (h : ∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g) :
    ∃ g ∈ Submonoid.closure T, GGDepAIsTv g := by
  refine tv_back hed hde ?_ h
  rintro s (⟨i, rfl⟩ | ⟨q, hq', rfl⟩)
  · rw [hfr i]; exact Submonoid.subset_closure (hfT ⟨i, rfl⟩)
  · exact Submonoid.subset_closure (hq q hq')

theorem twNorm [Fact p.Prime] (hpN : p ∣ N) (hN : 5 ≤ N) (α : GGDepAE p N)
    (hx : vAt α (N - 1) ≠ 0) :
    ∃ e d : Module.End (ZMod p) (GGDepAE p N), e * d = 1 ∧ d * e = 1 ∧
      (∀ i : Fin (N - 1), d * ggDepARefl (ggDepAh p N i) (ggDepAα p N i) * e =
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∧
      (∀ c : Fin (N - 1), d (ggDepAh p N c) = ggDepAh p N c) ∧
      (∀ (c : Fin (N - 1)) (v : GGDepAE p N),
        ggDepAdot (ggDepAα p N c) (e v) = ggDepAdot (ggDepAα p N c) v) ∧
      (∀ f : GGDepAE p N, vAt f (N - 1) = 0 → ∀ v, ggDepAdot f (d v) = ggDepAdot f v) ∧
      ∃ α' : GGDepAE p N, (∀ v, ggDepAdot α' v = ggDepAdot α (d v)) ∧ vAt α' 0 = 0 ∧
        vAt α' (N - 1) = 1 := by
  generalize hs : vAt α (N - 1) = s at hx
  generalize ha0 : vAt α 0 = a0
  have hsi : s * s⁻¹ = 1 := mul_inv_cancel₀ hx
  have hN1 : 1 ≤ N := by omega
  have hl : ∀ a b : ZMod p, vAt (twVec (N := N) a b) (N - 1) = b := fun a b => by
    rw [vAt_twVec (N := N) a b (k := N - 1) (by omega), if_pos (show N - 1 + 1 = N by omega)]
  have hed : twT (N := N) (twVec a0 (s - 1)) * twT (twVec (-(a0 * s⁻¹)) (s⁻¹ - 1)) = 1 := by
    apply twT_comp
    rw [twDot_x hN1, hl]
    funext j
    simp only [twVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    split_ifs
    · linear_combination hsi
    · linear_combination (-a0) * hsi
  have hde : twT (N := N) (twVec (-(a0 * s⁻¹)) (s⁻¹ - 1)) * twT (twVec a0 (s - 1)) = 1 := by
    apply twT_comp
    rw [twDot_x hN1, hl]
    funext j
    simp only [twVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    split_ifs
    · linear_combination hsi
    · ring
  refine ⟨_, _, hed, hde, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [twT_comm _ _ _ (twVec_dot_h hpN (by omega) _ _ i) (twDot_A_x hN1 i), mul_assoc, hde,
      mul_one]
  · intro c
    rw [twT_apply, twVec_dot_h hpN (by omega), zero_smul, add_zero]
  · intro c v
    rw [twDot_twT, twDot_A_x hN1, zero_smul, add_zero]
  · intro f hf v
    rw [twDot_twT, twDot_x hN1, hf, zero_smul, add_zero]
  · refine ⟨α + s • twVec (-(a0 * s⁻¹)) (s⁻¹ - 1), fun v => ?_, ?_, ?_⟩
    · rw [twDot_twT, twDot_x hN1, hs]
    · rw [vAt_add, vAt_smul, vAt_twVec (N := N) _ _ (k := 0) (by omega),
        if_neg (show ¬ (0 + 1 = N) by omega), ha0]
      linear_combination (-a0) * hsi
    · rw [vAt_add, vAt_smul, hl, hs]
      linear_combination hsi

theorem twChain_eq (f : ℕ → ZMod p) (lo len c0 : ℕ) (n : ZMod p) (hc0 : lo ≤ c0 ∨ n = 0)
    (h : ∀ k, lo ≤ k → k < lo + len → f k - f (k + 1) = if k = c0 then n else 0) :
    ∀ d, d ≤ len → f (lo + d) = f lo - if c0 < lo + d then n else 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    rcases hc0 with hc | hc
    · rw [Nat.add_zero, if_neg (show ¬ c0 < lo by omega), sub_zero]
    · rw [hc, Nat.add_zero]; simp
  | succ d ih =>
    intro hd
    have h1 := h (lo + d) (by omega) (by omega)
    have h2 := ih (by omega)
    have key : f (lo + d + 1) = f (lo + d) - (if lo + d = c0 then n else 0) := by
      rw [← h1]; ring
    rw [show lo + (d + 1) = lo + d + 1 by omega, key, h2]
    split_ifs <;> first | (exfalso; omega) | ring

theorem kVec_toZ [Fact p.Prime] (pos c0 n a b t : ℕ) (j : Fin N) :
    ggDepANToZ p N (kVec p N pos c0 n a b t) j =
      if j.val + 1 = N then (t : ZMod p) else if kChain N pos j.val = true then
        (b : ZMod p) - (if c0 < j.val then (n : ZMod p) else 0) else (a : ZMod p) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hj : j.val < (kVec p N pos c0 n a b t).length := by simp [kVec]
  rw [ggDepANToZ, List.getD_eq_getElem (l := kVec p N pos c0 n a b t) (d := 0) (n := j.val) hj]
  simp only [kVec, List.getElem_map, List.getElem_range]
  split_ifs
  · rw [ZMod.natCast_mod]
  · rw [ZMod.natCast_mod, Nat.cast_add, Nat.cast_sub (Nat.mod_lt n hp0).le, ZMod.natCast_self,
      ZMod.natCast_mod]
    ring
  · rw [ZMod.natCast_mod, sub_zero]
  · rw [ZMod.natCast_mod]

theorem kVec_length (pos c0 n a b t : ℕ) : (kVec p N pos c0 n a b t).length = N := by
  simp [kVec]

theorem kAN_length (pos c0 m u : ℕ) : (kAN p N pos c0 m u).length = N := by
  unfold kAN; split_ifs <;> exact kVec_length _ _ _ _ _ _

theorem kVec_complete_gen [Fact p.Prime] (hN : 5 ≤ N) (pos lo nc c0 n : ℕ) (v : GGDepAE p N)
    (hch : ∀ j, kChain N pos j = true ↔ lo ≤ j ∧ j + 3 ≤ lo + N)
    (hnc : ∀ j, j + 1 < N → kChain N pos j = false → j = nc)
    (hc0 : lo ≤ c0 ∨ (n : ZMod p) = 0)
    (h : ∀ k, kChain N pos k = true → kChain N pos (k + 1) = true →
      vAt v k - vAt v (k + 1) = if k = c0 then (n : ZMod p) else 0) :
    ggDepANToZ p N (kVec p N pos c0 n (vAt v nc).val (vAt v lo).val (vAt v (N - 1)).val) = v := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  funext j
  rw [kVec_toZ]
  have hj := j.isLt
  by_cases hl : j.val + 1 = N
  · rw [if_pos hl, ZMod.natCast_zmod_val, show N - 1 = j.val by omega, vAt_val]
  · rw [if_neg hl]
    by_cases hc : kChain N pos j.val = true
    · rw [if_pos hc, ZMod.natCast_zmod_val]
      have hjc := (hch j.val).mp hc
      have hch' := twChain_eq (vAt v) lo (N - 3) c0 (n : ZMod p) hc0
        (fun k hk1 hk2 => h k ((hch k).mpr (by omega)) ((hch (k + 1)).mpr (by omega)))
        (j.val - lo) (by omega)
      rw [show lo + (j.val - lo) = j.val by omega, vAt_val] at hch'
      exact hch'.symm
    · rw [if_neg hc, ZMod.natCast_zmod_val,
        ← hnc j.val (by omega) (by simpa using hc), vAt_val]

@[expose] def kLo : GGTWPos → ℕ
  | .ends => 1
  | .adj => 0

@[expose] def kNc (N : ℕ) : GGTWPos → ℕ
  | .ends => 0
  | .adj => N - 2

theorem kLo_le_of_inJ {pos : GGTWPos} {c : ℕ} (h : ggTWInJ N pos c) : kLo pos ≤ c := by
  cases pos <;> simp only [ggTWInJ, kLo] at h ⊢ <;> omega

theorem kVec_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (c0 n : ℕ) (v : GGDepAE p N)
    (hc0 : kLo pos ≤ c0 ∨ (n : ZMod p) = 0)
    (h : ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if k = c0 then (n : ZMod p) else 0) :
    ggDepANToZ p N (kVec p N (ggTWPosNat pos) c0 n (vAt v (kNc N pos)).val (vAt v (kLo pos)).val
      (vAt v (N - 1)).val) = v := by
  cases pos
  · exact kVec_complete_gen hN _ 1 0 c0 n v
      (fun j => by simp [kChain, ggTWPosNat] <;> omega)
      (fun j hj hc => by simp [kChain, ggTWPosNat] at hc; omega) hc0 h
  · exact kVec_complete_gen hN _ 0 (N - 2) c0 n v
      (fun j => by simp [kChain, ggTWPosNat] <;> omega)
      (fun j hj hc => by simp [kChain, ggTWPosNat] at hc; omega) hc0 h

theorem kAN_complete [Fact p.Prime] (hN : 5 ≤ N) (pos : GGTWPos) (c0 m : ℕ) (v : GGDepAE p N)
    (hc0 : kLo pos ≤ c0 ∨ (m : ZMod p) = 0)
    (h : ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if k = c0 then (m : ZMod p) else 0)
    (h0 : vAt v 0 = 0) (h1 : vAt v (N - 1) = 1) :
    ∃ u < p, ggDepANToZ p N (kAN p N (ggTWPosNat pos) c0 m u) = v := by
  have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hv := kVec_complete hN pos c0 m v hc0 h
  rw [h1, ZMod.val_one] at hv
  cases pos
  · refine ⟨(vAt v 1).val, ZMod.val_lt _, ?_⟩
    simp only [kNc, kLo, h0, ZMod.val_zero] at hv
    simpa [kAN, ggTWPosNat] using hv
  · refine ⟨(vAt v (N - 2)).val, ZMod.val_lt _, ?_⟩
    simp only [kNc, kLo, h0, ZMod.val_zero] at hv
    simpa [kAN, ggTWPosNat] using hv

theorem twInJ_of_chain (hN : 5 ≤ N) (pos : GGTWPos) (k : ℕ)
    (h1 : kChain N (ggTWPosNat pos) k = true) (h2 : kChain N (ggTWPosNat pos) (k + 1) = true) :
    ggTWInJ N pos k ∧ k + 2 < N := by
  cases pos <;> simp [kChain, ggTWPosNat, ggTWInJ] at h1 h2 ⊢ <;> omega

theorem twChainH (hN : 5 ≤ N) (pos : GGTWPos) (c0 : ℕ) (n : ZMod p) (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepAα p N c) v = if c.val = c0 then n else 0) :
    ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if k = c0 then n else 0 := by
  intro k h1 h2
  obtain ⟨hJ, hk⟩ := twInJ_of_chain hN pos k h1 h2
  have := hv ⟨k, by omega⟩ hJ
  rwa [twDot_A_short v ⟨k, by omega⟩ hk] at this

theorem twChainA (hN : 5 ≤ N) (pos : GGTWPos) (c0 : ℕ) (n : ZMod p) (v : GGDepAE p N)
    (hv : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot v (ggDepAh p N c) = if c.val = c0 then n else 0) :
    ∀ k, kChain N (ggTWPosNat pos) k = true → kChain N (ggTWPosNat pos) (k + 1) = true →
      vAt v k - vAt v (k + 1) = if k = c0 then n else 0 := by
  intro k h1 h2
  obtain ⟨hJ, hk⟩ := twInJ_of_chain hN pos k h1 h2
  have := hv ⟨k, by omega⟩ hJ
  rwa [twDot_h_short v ⟨k, by omega⟩ hk] at this

theorem twNat_eq {x y : ℕ} (hx : x < p) (hy : y < p) (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hv

theorem twNDot_eq [Fact p.Prime] {la lh : List ℕ} (hla : la.length = N) (hlh : lh.length = N)
    {k : ℕ} (hk : k < p)
    (h : ggDepAdot (ggDepANToZ p N la) (ggDepANToZ p N lh) = (k : ZMod p)) :
    ggDepANDot p la lh = k := by
  rw [← ggDepANDot_cast la lh hla hlh] at h
  exact twNat_eq (by unfold ggDepANDot; exact Nat.mod_lt _ (Fact.out : p.Prime).pos) hk h

theorem twCast_two : (((2 % p : ℕ)) : ZMod p) = 2 := by
  rw [ZMod.natCast_mod]; norm_num

theorem twCast_neg_one [Fact p.Prime] : ((((p - 1) % p : ℕ)) : ZMod p) = -1 := by
  simpa using l05nND_cast_neg p 1 (Fact.out : p.Prime).one_lt.le

theorem twCast_neg [Fact p.Prime] (k : ℕ) : ((((p - k % p) % p : ℕ)) : ZMod p) = -(k : ZMod p) := by
  rw [l05nND_cast_neg p (k % p) (Nat.mod_lt k (Fact.out : p.Prime).pos).le, ZMod.natCast_mod]

theorem twMod_lt [Fact p.Prime] (k : ℕ) : k % p < p := Nat.mod_lt k (Fact.out : p.Prime).pos

theorem mem_kCells1 {pos c0 mi ni a b t u : ℕ} (ha : a < p) (hb : b < p) (ht : t < p)
    (hu : u < p)
    (hd : ggDepANDot p (kAN p N pos c0 ((p - mi % p) % p) u)
      (kVec p N pos c0 ((p - ni % p) % p) a b t) = 2 % p) :
    (kVec p N pos c0 ((p - ni % p) % p) a b t, kAN p N pos c0 ((p - mi % p) % p) u) ∈
      kCells1 p N pos c0 mi ni := by
  simp only [kCells1, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨a, ha, b, hb, t, ht, u, hu, by simp [hd]⟩

theorem mem_kOuter {pos c a b t a' b' : ℕ} (ha : a < p) (hb : b < p) (ht : t < p)
    (ha' : a' < p) (hb' : b' < p)
    (hd : ggDepANDot p (kVec p N pos c ((p - 1) % p) a' b' 0)
      (kVec p N pos c ((p - 1) % p) a b t) = 2 % p) :
    (kVec p N pos c ((p - 1) % p) a b t, kVec p N pos c ((p - 1) % p) a' b' 0) ∈
      kOuter p N pos c := by
  simp only [kOuter, List.mem_flatMap, List.mem_range, List.mem_filterMap]
  exact ⟨a, ha, b, hb, t, ht, a', ha', b', hb', by rw [if_pos (beq_iff_eq.mpr hd)]⟩

theorem mem_kInner {pos : ℕ} {o : GGDepANPair} {a b t u : ℕ} (ha : a < p) (hb : b < p)
    (ht : t < p) (hu : u < p)
    (h1 : ggDepANDot p o.2 (kVec p N pos 0 0 a b t) = (p - 1) % p)
    (h2 : ggDepANDot p (kAN p N pos 0 0 u) (kVec p N pos 0 0 a b t) = 2 % p)
    (h3 : ggDepANDot p (kAN p N pos 0 0 u) o.1 = (p - 1) % p) :
    (kVec p N pos 0 0 a b t, kAN p N pos 0 0 u) ∈ kInner p N pos o := by
  simp only [kInner, List.mem_flatMap, List.mem_range]
  refine ⟨a, ha, b, hb, t, ht, ?_⟩
  rw [if_pos (beq_iff_eq.mpr h1), List.mem_filterMap]
  exact ⟨u, List.mem_range.mpr hu, by simp [h2, h3]⟩

theorem twPat1_wit {pos : GGTWPos} {c0 : ℕ} {m n : ℤ} (h : GGTWPat1 N pos c0 m n) :
    ∃ mi ni : ℕ, (mi = 1 ∨ mi = 2) ∧ (ni = 1 ∨ ni = 2) ∧ m = -(mi : ℤ) ∧ n = -(ni : ℤ) := by
  obtain ⟨hm, hn⟩ := ggTWPat1_mn h
  rcases hm with rfl | rfl <;> rcases hn with rfl | rfl
  · exact ⟨1, 1, Or.inl rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨1, 2, Or.inl rfl, Or.inr rfl, rfl, rfl⟩
  · exact ⟨2, 1, Or.inr rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨2, 2, Or.inr rfl, Or.inr rfl, rfl, rfl⟩

theorem twPosNat_mem (pos : GGTWPos) : ggTWPosNat pos = 0 ∨ ggTWPosNat pos = 1 := by
  cases pos <;> simp [ggTWPosNat]

theorem twdk_cells1 [Fact p.Prime] (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N)
    {F : List GGDepANPair} {S : List KSingleE} {R : List KResE}
    (hF : kFrameOK p N F = true) (hC : kCover N S R = true)
    (hS : ∀ i < S.length, kSingleAt p N F S i = true) : GGTWDCells1 p N := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro pos c0 m n hpat ha αa hpair hdot hx
  obtain ⟨mi, ni, hmi, hni, rfl, rfl⟩ := twPat1_wit hpat
  have hpatB := (ggTWNPat1B_iff pos c0.val mi ni hmi hni).mpr hpat
  obtain ⟨wits, idx, hchk⟩ := single_of_cover hC hS (ggTWPosNat pos) c0.val mi ni
    (twPosNat_mem pos) c0.isLt hmi hni hpatB
  have hJ : kLo pos ≤ c0.val := kLo_le_of_inJ hpat.1
  rw [twDot_x (N := N) (by omega)] at hx
  obtain ⟨e, d, hed, hde, hfr, hdh, hea, -, α', hα', hα0, hα1⟩ := twNorm hpN hN αa hx
  have hH := kVec_complete hN pos c0.val ((p - ni % p) % p) (e ha) (Or.inl hJ)
    (twChainH hN pos c0.val _ (e ha) fun c hc => by
      rw [hea, (hpair c hc).2, twCast_neg]
      simp [Fin.ext_iff])
  obtain ⟨u, hu, hA⟩ := kAN_complete hN pos c0.val ((p - mi % p) % p) α' (Or.inl hJ)
    (twChainA hN pos c0.val _ α' fun c hc => by
      rw [hα', hdh, (hpair c hc).1, twCast_neg]
      simp [Fin.ext_iff]) hα0 hα1
  set lh := kVec p N (ggTWPosNat pos) c0.val ((p - ni % p) % p) (vAt (e ha) (kNc N pos)).val
    (vAt (e ha) (kLo pos)).val (vAt (e ha) (N - 1)).val with hlh
  set la := kAN p N (ggTWPosNat pos) c0.val ((p - mi % p) % p) u with hla
  have hd2 : ggDepANDot p la lh = 2 % p :=
    twNDot_eq (kAN_length _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
      (by rw [hA, hH, hα', twApply_of_mul hde, hdot, twCast_two])
  have hmem : (lh, la) ∈ kCells1 p N (ggTWPosNat pos) c0.val mi ni :=
    mem_kCells1 (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hu hd2
  obtain ⟨i, hi⟩ := kAll2_mem _ _ idx hchk _ hmem
  try dsimp only at hi
  have hval : GGTWDValid p N (lh, la) := ⟨kVec_length _ _ _ _ _ _, kAN_length _ _ _ _, hd2⟩
  have htv := kTest_sound hp2 hN hF (news := [(lh, la)])
    (fun q hq => by rw [List.mem_singleton] at hq; subst hq; exact hval) _ hi
  refine tv_back_gens hed hde hfr Set.subset_union_left ?_ htv
  intro q hq
  rw [List.mem_singleton] at hq
  subst hq
  change d * ggDepARefl (ggDepANToZ p N lh) (ggDepANToZ p N la) * e ∈ _
  rw [hH, hA, twRefl_back hde ha αa α' hα']
  exact Set.mem_union_right _ (Set.mem_singleton _)

theorem twdk_res2 [Fact p.Prime] (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N)
    {F : List GGDepANPair} {S : List KSingleE} {R : List KResE}
    (hF : kFrameOK p N F = true) (hC : kCover N S R = true)
    (hR : ∀ i < R.length, kResAt p N F R i = true) : GGTWDRes2 p N := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro pos c hpat ha1 αa1 ha2 αa2 hpair hx1 hx2
  have hpatB := (ggTWNPat2B_iff pos c.val none).mpr hpat
  obtain ⟨sw, ra, ent, hchk⟩ := res_of_cover hC hR (ggTWPosNat pos) c.val (twPosNat_mem pos)
    c.isLt hpatB
  have hJ : kLo pos ≤ c.val := kLo_le_of_inJ hpat.1
  rw [twDot_x (N := N) (by omega)] at hx1 hx2
  obtain ⟨e, d, hed, hde, hfr, hdh, hea, hd0, α', hα', hα0, hα1⟩ := twNorm hpN hN αa2 hx2
  have hα1d : ∀ v, ggDepAdot αa1 v = ggDepAdot αa1 (d v) := fun v => (hd0 αa1 hx1 v).symm
  obtain ⟨hb, h12, h21, h11, h22⟩ := hpair
  simp only [reduceCtorEq, if_false, if_true, eq_self_iff_true] at hb h12 h21
  have hH1 := kVec_complete hN pos c.val ((p - 1) % p) (e ha1) (Or.inl hJ)
    (twChainH hN pos c.val _ (e ha1) fun c' hc' => by
      rw [hea, (hb c' hc').2.1, twCast_neg_one]
      simp [Fin.ext_iff])
  have hA1 := kVec_complete hN pos c.val ((p - 1) % p) αa1 (Or.inl hJ)
    (twChainA hN pos c.val _ αa1 fun c' hc' => by
      rw [(hb c' hc').1, twCast_neg_one]
      simp [Fin.ext_iff])
  rw [hx1, ZMod.val_zero] at hA1
  have hH2 := kVec_complete hN pos 0 0 (e ha2) (Or.inr Nat.cast_zero)
    (twChainH hN pos 0 _ (e ha2) fun c' hc' => by
      rw [hea, (hb c' hc').2.2.2]
      simp)
  obtain ⟨u, hu, hA2⟩ := kAN_complete hN pos 0 0 α' (Or.inr Nat.cast_zero)
    (twChainA hN pos 0 _ α' fun c' hc' => by
      rw [hα', hdh, (hb c' hc').2.2.1]
      simp) hα0 hα1
  set lh1 := kVec p N (ggTWPosNat pos) c.val ((p - 1) % p) (vAt (e ha1) (kNc N pos)).val
    (vAt (e ha1) (kLo pos)).val (vAt (e ha1) (N - 1)).val with hlh1
  set la1 := kVec p N (ggTWPosNat pos) c.val ((p - 1) % p) (vAt αa1 (kNc N pos)).val
    (vAt αa1 (kLo pos)).val 0 with hla1
  set lh2 := kVec p N (ggTWPosNat pos) 0 0 (vAt (e ha2) (kNc N pos)).val
    (vAt (e ha2) (kLo pos)).val (vAt (e ha2) (N - 1)).val with hlh2
  set la2 := kAN p N (ggTWPosNat pos) 0 0 u with hla2
  have hp1 : (p - 1) % p < p := twMod_lt _
  have d11 : ggDepANDot p la1 lh1 = 2 % p :=
    twNDot_eq (kVec_length _ _ _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
      (by rw [hA1, hH1, hα1d, twApply_of_mul hde, h11, twCast_two])
  have d12 : ggDepANDot p la1 lh2 = (p - 1) % p :=
    twNDot_eq (kVec_length _ _ _ _ _ _) (kVec_length _ _ _ _ _ _) hp1
      (by rw [hA1, hH2, hα1d, twApply_of_mul hde, h12, twCast_neg_one])
  have d22 : ggDepANDot p la2 lh2 = 2 % p :=
    twNDot_eq (kAN_length _ _ _ _) (kVec_length _ _ _ _ _ _) (twMod_lt 2)
      (by rw [hA2, hH2, hα', twApply_of_mul hde, h22, twCast_two])
  have d21 : ggDepANDot p la2 lh1 = (p - 1) % p :=
    twNDot_eq (kAN_length _ _ _ _) (kVec_length _ _ _ _ _ _) hp1
      (by rw [hA2, hH1, hα', twApply_of_mul hde, h21, twCast_neg_one])
  have hmemO : (lh1, la1) ∈ kOuter p N (ggTWPosNat pos) c.val :=
    mem_kOuter (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) d11
  obtain ⟨en, hen⟩ := kAll2_mem _ _ ent hchk _ hmemO
  try dsimp only at hen
  have hback : ∀ news : List GGDepANPair, (∀ q ∈ news, q = (lh1, la1) ∨ q = (lh2, la2)) →
      (∃ g ∈ Submonoid.closure (ggTWDGens p N news), GGDepAIsTv g) →
      ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
          ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
            {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}), GGDepAIsTv g := by
    intro news hnews htv
    refine tv_back_gens hed hde hfr Set.subset_union_left ?_ htv
    intro q hq
    rcases hnews q hq with rfl | rfl
    · change d * ggDepARefl (ggDepANToZ p N lh1) (ggDepANToZ p N la1) * e ∈ _
      rw [hH1, hA1, twRefl_back hde ha1 αa1 αa1 hα1d]
      exact Set.mem_union_right _ (Set.mem_insert _ _)
    · change d * ggDepARefl (ggDepANToZ p N lh2) (ggDepANToZ p N la2) * e ∈ _
      rw [hH2, hA2, twRefl_back hde ha2 αa2 α' hα']
      exact Set.mem_union_right _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hv1 : GGTWDValid p N (lh1, la1) := ⟨kVec_length _ _ _ _ _ _, kVec_length _ _ _ _ _ _, d11⟩
  by_cases h0 : en.1 = 0
  · rw [if_pos h0] at hen
    have hmemI : (lh2, la2) ∈ kInner p N (ggTWPosNat pos) (lh1, la1) :=
      mem_kInner (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hu d12 d22 d21
    obtain ⟨j, hj⟩ := kAll2_mem _ _ _ hen _ hmemI
    try dsimp only at hj
    have hv2 : GGTWDValid p N (lh2, la2) := ⟨kVec_length _ _ _ _ _ _, kAN_length _ _ _ _, d22⟩
    refine hback _ (fun q hq => ?_) (kTest_sound hp2 hN hF ?_ _ hj)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      exact hq
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · exact hv1
      · exact hv2
  · rw [if_neg h0] at hen
    refine hback _ (fun q hq => ?_) (kTest_sound hp2 hN hF ?_ _ hen)
    · rw [List.mem_singleton] at hq
      exact Or.inl hq
    · intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact hv1

theorem twdk_sound [Fact p.Prime] (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N)
    (F : List GGDepANPair) (S : List KSingleE) (R : List KResE)
    (hF : kFrameOK p N F = true) (hC : kCover N S R = true)
    (hS : ∀ i < S.length, kSingleAt p N F S i = true)
    (hR : ∀ i < R.length, kResAt p N F R i = true) : GGTWDCertCells p N :=
  ⟨twdk_cells1 hp2 hpN hN hF hC hS, twdk_res2 hp2 hpN hN hF hC hR⟩

theorem twdk_cells [Fact p.Prime] (hp2 : p ≠ 2) (hpN : p ∣ N) (hN : 5 ≤ N)
    (F : List GGDepANPair) (S : List KSingleE) (R : List KResE)
    (hF : kFrameOK p N F = true) (hC : kCover N S R = true)
    (hS : ∀ i < S.length, kSingleAt p N F S i = true)
    (hR : ∀ i < R.length, kResAt p N F R i = true) : GGTWDCells p N :=
  ggTWDCells_of_cert (twdk_sound hp2 hpN hN F S R hF hC hS hR)

end CFSG.StandardType.TWDK

end

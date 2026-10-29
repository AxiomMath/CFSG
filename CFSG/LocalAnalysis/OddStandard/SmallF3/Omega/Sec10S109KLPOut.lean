module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109KLPInputs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S109CInputs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

structure KLCoord (B : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) : Prop where
  add : ∀ v w, IsEvenVec v → IsEvenVec w → φ (v + w) = φ v * φ w
  inj : ∀ v w, IsEvenVec v → IsEvenVec w → φ v = φ w → v = w
  mem : ∀ x : G, x ∈ B ↔ ∃ v, IsEvenVec v ∧ φ v = x

@[expose] def KLStab (L' : Subgroup G) (φ : (Fin 5 → ZMod 2) → G) : Prop :=
  ∀ σ ∈ alternatingGroup (Fin 5), permVec σ klV0 = klV0 →
    ∃ m ∈ normalizer (L' : Set G), ∀ v, IsEvenVec v → m * φ v * m⁻¹ = φ (permVec σ v)

theorem kl_even_zero : IsEvenVec (0 : Fin 5 → ZMod 2) := by
  simp [IsEvenVec]

theorem kl_even_add {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    IsEvenVec (v + w) := by
  unfold IsEvenVec at *
  simp [Finset.sum_add_distrib, hv, hw]

theorem kl_even_perm (σ : Equiv.Perm (Fin 5)) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    IsEvenVec (permVec σ v) := by
  unfold IsEvenVec permVec at *
  simpa [Function.comp] using (Equiv.sum_comp σ.symm v).trans hv

theorem kl_vec_add_self (v : Fin 5 → ZMod 2) : v + v = 0 := by
  funext i
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  exact h (v i)

theorem KLCoord.of_perm {B H : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    {Alt : Subgroup (Equiv.Perm (Fin 5))} (h : IsPermModuleVia IsEvenVec φ B H Alt) :
    KLCoord B φ :=
  ⟨h.1, h.2.1, h.2.2.1⟩

namespace KLCoord

variable {B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}

theorem map_zero (h : KLCoord B φ) : φ 0 = 1 := by
  have := h.add 0 0 kl_even_zero kl_even_zero
  simpa using this

theorem mem_of_even (h : KLCoord B φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) : φ v ∈ B :=
  (h.mem _).2 ⟨v, hv, rfl⟩

theorem mul_self (h : KLCoord B φ) {v : Fin 5 → ZMod 2} (hv : IsEvenVec v) :
    φ v * φ v = 1 := by
  rw [← h.add v v hv hv, kl_vec_add_self, h.map_zero]

theorem sq_eq_one (h : KLCoord B φ) {x : G} (hx : x ∈ B) : x * x = 1 := by
  obtain ⟨v, hv, rfl⟩ := (h.mem x).1 hx
  exact h.mul_self hv

theorem comm (h : KLCoord B φ) {v w : Fin 5 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w) :
    φ v * φ w = φ w * φ v := by
  rw [← h.add v w hv hw, ← h.add w v hw hv, add_comm]

end KLCoord

theorem kl_outer_mul [Finite G] {L : Subgroup G}
    (hout : (L ⊔ centralizer (L : Set G)).relIndex (normalizer (L : Set G)) ≤ 2) {x y : G}
    (hx : x ∈ normalizer (L : Set G)) (hy : y ∈ normalizer (L : Set G)) (hxo : ¬ InnerOn L x)
    (hyo : ¬ InnerOn L y) : InnerOn L (x * y) := by
  set N := normalizer (L : Set G) with hN
  set H' : Subgroup N := (L ⊔ centralizer (L : Set G)).subgroupOf N with hH'
  have hidx : H'.index ≤ 2 := hout
  have hne : H'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hx' : (⟨x, hx⟩ : N) ∉ H' := hxo
  have hy' : (⟨y, hy⟩ : N) ∉ H' := hyo
  have h2 : H'.index = 2 := by
    rcases (by omega : H'.index = 1 ∨ H'.index = 2) with h1 | h2
    · exact absurd (by rw [Subgroup.index_eq_one.mp h1]; trivial) hx'
    · exact h2
  have hmul := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
    ⟨fun h => absurd h hx', fun h => absurd h hy'⟩
  exact hmul

theorem kl_inner_of [Finite G] (hE : Asc82FactCE16) (hty : Asc82FactCTy) (hout : Asc82FactOut5)
    {L' B : Subgroup G} {φ : (Fin 5 → ZMod 2) → G} (hL' : IsPSp43 L') (hc : KLCoord B φ)
    (hBN : B ≤ normalizer (L' : Set G)) (hBC : B ⊓ centralizer (L' : Set G) = ⊥)
    (hB16 : Nat.card B = 16) (hY : KLStab L' φ)
    (hz0 : ¬ InducesTypeSome L' (φ (klF 0)) 5 1 4 (-1))
    (hz1 : ¬ InducesTypeSome L' (φ (klF 1)) 5 1 4 (-1)) : ∀ b ∈ B, InnerOn L' b := by
  classical
  have hrel := hout G L' hL'
  by_contra hnot
  push Not at hnot
  obtain ⟨b, hbB, hbo⟩ := hnot
  obtain ⟨hE1, hE2⟩ := hE G L' hL' B hBN hBC hB16 (fun x hx => hc.sq_eq_one hx)
  obtain ⟨x, hxB, hxty⟩ : ∃ x ∈ B, InducesTypeSome L' x 5 1 4 (-1) := by
    rcases hE1 with hle | hex
    · exact absurd (hle hbB) hbo
    · exact hex
  have hxout : ¬ InnerOn L' x := by
    have hx2 : x * x ∈ centralizer (L' : Set G) := by
      rw [hc.sq_eq_one hxB]
      exact Subgroup.one_mem _
    exact (hty G L' hL' x (hBN hxB) hx2).mpr (Or.inr hxty)
  obtain ⟨v, hv, rfl⟩ := (hc.mem x).1 hxB
  have hH0 : ∀ w, IsEvenVec w → w 0 = w 1 → InnerOn L' (φ w) := by
    intro w hw h01
    obtain ⟨y, hy, σ, hσ, hσ0, rfl⟩ := kl_H0_gen w hw h01
    obtain ⟨m, hm, hmact⟩ := hY σ hσ hσ0
    have hφy : φ y ∈ B := hc.mem_of_even hy
    have e : φ (y + permVec σ y) = φ y * (m * φ y * m⁻¹) := by
      rw [hc.add y _ hy (kl_even_perm σ hy), ← hmact y hy]
    rw [e]
    by_cases hin : InnerOn L' (φ y)
    · exact Subgroup.mul_mem _ hin (kl_innerOn_conj hm hin)
    · have hmN : m * φ y * m⁻¹ ∈ normalizer (L' : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hm (hBN hφy)) (Subgroup.inv_mem _ hm)
      have hout' : ¬ InnerOn L' (m * φ y * m⁻¹) := fun h => hin ((kl_innerOn_conj_iff hm).1 h)
      exact kl_outer_mul hrel (hBN hφy) hmN hin hout'
  have hvne : v 0 ≠ v 1 := fun h01 => hxout (hH0 v hv h01)
  have hv2 : vecWeight v = 2 := by
    rcases kl_outer_cases v hv hvne with h2 | h0 | h1
    · exact h2
    · rw [h0] at hxty
      exact absurd hxty hz0
    · rw [h1] at hxty
      exact absurd hxty hz1
  set O6 : Finset (Fin 5 → ZMod 2) :=
    Finset.univ.filter fun w => vecWeight w = 2 ∧ w 0 ≠ w 1 with hO6
  have h6 : O6.card = 6 := kl_O6_card
  have hF : ∀ y ∈ O6.image φ, y ∈ B ∧ InducesTypeSome L' y 5 1 4 (-1) := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hw2, hw01⟩ := (Finset.mem_filter.1 hw).2
    obtain ⟨σ, hσ, hσ0, hσv⟩ := kl_O6_trans v w hv2 hw2 hvne hw01
    obtain ⟨m, hm, hmact⟩ := hY σ hσ hσ0
    refine ⟨hc.mem_of_even (kl_isEven_of_weight_two w hw2), ?_⟩
    have e : φ w = m * φ v * m⁻¹ := by rw [hmact v hv, hσv]
    rw [e]
    exact kl_inducesTypeSome_conj hm hxty
  have hcard : (O6.image φ).card = 6 := by
    rw [Finset.card_image_of_injOn, h6]
    intro w hw w' hw' hww
    exact hc.inj w w' (kl_isEven_of_weight_two w (Finset.mem_filter.1 hw).2.1)
      (kl_isEven_of_weight_two w' (Finset.mem_filter.1 hw').2.1) hww
  have hle := hE2 _ hF
  omega

end CFSG.OddStandard.SmallF3.Omega

module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public section

namespace CFSG.GH74.GLS.SP.Local

open scoped commutatorElement

theorem y1_commutator_mul_left {G : Type} [Group G] (s t ω : G) (h : ω * t = t * ω) :
    ⁅s * ω, t⁆ = ⁅s, t⁆ := by
  have h' : ω * t * ω⁻¹ = t := by rw [h, mul_inv_cancel_right]
  calc ⁅s * ω, t⁆ = s * (ω * t * ω⁻¹) * s⁻¹ * t⁻¹ := by
        rw [commutatorElement_def]; group
    _ = ⁅s, t⁆ := by rw [h', commutatorElement_def]

theorem y1_commutator_mul_right {G : Type} [Group G] (s t ω : G) (h : ω * s = s * ω) :
    ⁅s, t * ω⁆ = ⁅s, t⁆ := by
  rw [← commutatorElement_inv (t * ω) s, y1_commutator_mul_left t s ω h, commutatorElement_inv]

open Subgroup in
theorem exists_y1 {G : Type} [Group G] (K₁ K₂ : Subgroup G) (w z : G)
    (hw : orderOf w = 2) (hKinf : K₁ ⊓ K₂ = zpowers w)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hinv₁ : ∀ x ∈ K₁, x * x = 1 → x = 1 ∨ x = w)
    (hz2 : z * z = 1) (hzw : z * w = w * z)
    (hz₁ : ∀ a ∈ K₁, z * a * z⁻¹ ∈ K₂) (hz₂ : ∀ a ∈ K₂, z * a * z⁻¹ ∈ K₁)
    (P : Subgroup G) (hPperf : ⁅P, P⁆ = P) (hPK : P ≤ K₁ ⊔ K₂) (hPz : ∀ p ∈ P, z * p = p * z)
    (u : G) (huP : u ∈ P) (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    ∃ y ∈ K₁, y * y = w ∧ u = y * (z * y * z⁻¹) := by
  obtain ⟨c, hc⟩ : ∃ c : G ≃* G, ∀ x, c x = z * x * z⁻¹ := ⟨MulAut.conj z, MulAut.conj_apply z⟩
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hcc : ∀ x, c (c x) = x := by
    intro x
    rw [hc, hc, hzi]
    calc z * (z * x * z) * z = z * z * x * (z * z) := by simp only [mul_assoc]
      _ = x := by rw [hz2, one_mul, mul_one]
  have hcw : c w = w := by rw [hc, hzw, mul_inv_cancel_right]
  have hc₁ : ∀ a ∈ K₁, c a ∈ K₂ := fun a ha => by rw [hc]; exact hz₁ a ha
  have hc₂ : ∀ a ∈ K₂, c a ∈ K₁ := fun a ha => by rw [hc]; exact hz₂ a ha
  have hZ₁ : ∀ ω ∈ zpowers w, ω ∈ K₁ := fun ω hω => by
    rw [← hKinf] at hω
    exact (Subgroup.mem_inf.1 hω).1
  have hZ₂ : ∀ ω ∈ zpowers w, ω ∈ K₂ := fun ω hω => by
    rw [← hKinf] at hω
    exact (Subgroup.mem_inf.1 hω).2
  have hcZ : ∀ ω ∈ zpowers w, c ω = ω := by
    intro ω hω
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hω
    rw [map_zpow, hcw]
  have hdec : ∀ p ∈ K₁ ⊔ K₂, ∃ a ∈ K₁, ∃ b ∈ K₂, p = a * b := by
    intro p hp
    rw [Subgroup.sup_eq_closure] at hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨x, hx, 1, K₂.one_mem, (mul_one x).symm⟩
      · exact ⟨1, K₁.one_mem, x, hx, (one_mul x).symm⟩
    | one => exact ⟨1, K₁.one_mem, 1, K₂.one_mem, (mul_one 1).symm⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihx
      obtain ⟨a', ha', b', hb', rfl⟩ := ihy
      refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
      calc a * b * (a' * b') = a * (b * a') * b' := by simp only [mul_assoc]
        _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
        _ = a * a' * (b * b') := by simp only [mul_assoc]
    | inv x _ ihx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihx
      refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
      rw [mul_inv_rev]
      exact (hcomm a⁻¹ (K₁.inv_mem ha) b⁻¹ (K₂.inv_mem hb)).symm
  have hcen : ∀ ω ∈ zpowers w, ∀ x ∈ K₁ ⊔ K₂, ω * x = x * ω := by
    intro ω hω x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec x hx
    have h1 := hcomm a ha ω (hZ₂ ω hω)
    have h2 := hcomm ω (hZ₁ ω hω) b hb
    calc ω * (a * b) = ω * a * b := (mul_assoc ω a b).symm
      _ = a * ω * b := by rw [← h1]
      _ = a * (ω * b) := mul_assoc a ω b
      _ = a * (b * ω) := by rw [h2]
      _ = a * b * ω := (mul_assoc a b ω).symm
  have hstep1 : ∀ p ∈ K₁ ⊔ K₂, z * p = p * z → ∃ a ∈ K₁, ∃ ω ∈ zpowers w, p = a * c a * ω := by
    intro p hp hzp
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec p hp
    have hcab : c a * c b = a * b := by
      rw [← map_mul, hc, hzp, mul_inv_cancel_right]
    have hE : c b * c a = a * b := by
      rw [hcomm (c b) (hc₂ b hb) (c a) (hc₁ a ha)]
      exact hcab
    obtain ⟨ω, hωZ, hcb⟩ : ∃ ω ∈ zpowers w, c b = a * ω := by
      refine ⟨a⁻¹ * c b, ?_, (mul_inv_cancel_left a (c b)).symm⟩
      have hK₂ : a⁻¹ * c b = b * (c a)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc]
        exact eq_mul_inv_of_mul_eq hE
      rw [← hKinf]
      refine Subgroup.mem_inf.2 ⟨K₁.mul_mem (K₁.inv_mem ha) (hc₂ b hb), ?_⟩
      rw [hK₂]
      exact K₂.mul_mem hb (K₂.inv_mem (hc₁ a ha))
    have hb' : b = c a * ω := by
      calc b = c (c b) := (hcc b).symm
        _ = c (a * ω) := by rw [hcb]
        _ = c a * c ω := map_mul c a ω
        _ = c a * ω := by rw [hcZ ω hωZ]
    refine ⟨a, ha, ω, hωZ, ?_⟩
    rw [hb']
    exact (mul_assoc a (c a) ω).symm
  obtain ⟨S, hS⟩ : ∃ S : Subgroup G, ∀ x, x ∈ S ↔ ∃ a ∈ K₁, x = a * c a := by
    refine ⟨{ carrier := {x | ∃ a ∈ K₁, x = a * c a}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
      refine ⟨a * a', K₁.mul_mem ha ha', ?_⟩
      calc a * c a * (a' * c a') = a * (c a * a') * c a' := by simp only [mul_assoc]
        _ = a * (a' * c a) * c a' := by rw [← hcomm a' ha' (c a) (hc₁ a ha)]
        _ = a * a' * c (a * a') := by rw [map_mul]; simp only [mul_assoc]
    · exact ⟨1, K₁.one_mem, by rw [map_one, mul_one]⟩
    · rintro _ ⟨a, ha, rfl⟩
      refine ⟨a⁻¹, K₁.inv_mem ha, ?_⟩
      rw [map_inv, mul_inv_rev]
      exact (hcomm a⁻¹ (K₁.inv_mem ha) (c a)⁻¹ (K₂.inv_mem (hc₁ a ha))).symm
  have hPS : P ≤ S := by
    refine hPperf.symm.le.trans (Subgroup.commutator_le.2 ?_)
    intro p hp q hq
    obtain ⟨a, ha, ω, hω, rfl⟩ := hstep1 p (hPK hp) (hPz p hp)
    obtain ⟨a', ha', ω', hω', rfl⟩ := hstep1 q (hPK hq) (hPz q hq)
    have hs : a * c a ∈ K₁ ⊔ K₂ := Subgroup.mul_mem_sup ha (hc₁ a ha)
    have hs' : a' * c a' ∈ K₁ ⊔ K₂ := Subgroup.mul_mem_sup ha' (hc₁ a' ha')
    have hω'H : ω' ∈ K₁ ⊔ K₂ := Subgroup.mem_sup_left (hZ₁ ω' hω')
    have e : ⁅a * c a * ω, a' * c a' * ω'⁆ = ⁅a * c a, a' * c a'⁆ := by
      rw [y1_commutator_mul_left (a * c a) (a' * c a' * ω') ω
          (hcen ω hω _ ((K₁ ⊔ K₂).mul_mem hs' hω'H)),
        y1_commutator_mul_right (a * c a) (a' * c a') ω' (hcen ω' hω' _ hs)]
    rw [e, commutatorElement_def]
    have hsS : a * c a ∈ S := (hS _).2 ⟨a, ha, rfl⟩
    have hsS' : a' * c a' ∈ S := (hS _).2 ⟨a', ha', rfl⟩
    exact S.mul_mem (S.mul_mem (S.mul_mem hsS hsS') (S.inv_mem hsS)) (S.inv_mem hsS')
  obtain ⟨y, hy, hu⟩ := (hS u).1 (hPS huP)
  have hcy : c y * y = y * c y := (hcomm y hy (c y) (hc₁ y hy)).symm
  have hyy : y * y * c (y * y) = 1 := by
    calc y * y * c (y * y) = y * y * (c y * c y) := by rw [map_mul]
      _ = y * (y * c y) * c y := by simp only [mul_assoc]
      _ = y * (c y * y) * c y := by rw [hcy]
      _ = y * c y * (y * c y) := by simp only [mul_assoc]
      _ = 1 := by rw [← hu]; exact hu2
  have hy2 : y * y ∈ zpowers w := by
    rw [← hKinf]
    refine Subgroup.mem_inf.2 ⟨K₁.mul_mem hy hy, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hyy]
    exact K₂.inv_mem (hc₁ _ (K₁.mul_mem hy hy))
  have hy2' : y * y = 1 ∨ y * y = w := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hy2
    have h := zpow_mod_orderOf w n
    rw [hw] at h
    simp only [Nat.cast_ofNat] at h
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [h0, zpow_zero] at h
      rw [← hn]
      exact h.symm
    · right
      rw [h1, zpow_one] at h
      rw [← hn]
      exact h.symm
  have hww : w * w = 1 := by
    have h := pow_orderOf_eq_one w
    rw [hw, pow_two] at h
    exact h
  rcases hy2' with h | h
  ·
    exfalso
    rcases hinv₁ y hy h with h1 | h1
    · apply hu1
      rw [hu, h1, map_one, mul_one]
    · apply hu1
      rw [hu, h1, hcw, hww]
  · refine ⟨y, hy, h, ?_⟩
    rw [hu, hc]

end CFSG.GH74.GLS.SP.Local

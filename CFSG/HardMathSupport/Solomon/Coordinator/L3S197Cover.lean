module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma513Ns
open scoped commutatorElement

variable {K : Type*} [Group K]

theorem mem_center_of_conj_eq {a b : K} (h : (MulAut.conj a : MulAut K) = MulAut.conj b) :
    b⁻¹ * a ∈ Subgroup.center K := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h1 := congrArg (fun f : MulAut K => f g) h
  simp only [MulAut.conj_apply] at h1
  calc g * (b⁻¹ * a) = b⁻¹ * (b * g * b⁻¹) * a := by group
    _ = b⁻¹ * (a * g * a⁻¹) * a := by rw [h1]
    _ = (b⁻¹ * a) * g := by group

theorem mul_conj_mul_inv (v : MulAut K) (a : K) :
    v * MulAut.conj a * v⁻¹ = MulAut.conj (v a) := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem cover_conj_formula (hK : commutator K = ⊤) {Ŵ : Type*} [Group Ŵ] {π : Ŵ →* MulAut K}
    {ι : K →* Ŵ} (hc : IsThreeCover π ι) (w : Ŵ) (k : K) :
    ι (π w k) = w * ι k * w⁻¹ := by
  have key : ∀ a : K, ∃ a' : K, w * ι a * w⁻¹ = ι a' ∧ (π w a)⁻¹ * a' ∈ Subgroup.center K := by
    intro a
    have h1 : π (w * ι a * w⁻¹) = MulAut.conj (π w a) := by
      rw [map_mul, map_mul, hc.conj, map_inv, mul_conj_mul_inv]
    obtain ⟨a', ha'⟩ := hc.inner _ (by rw [h1]; exact ⟨π w a, rfl⟩)
    refine ⟨a', ha'.symm, ?_⟩
    apply mem_center_of_conj_eq
    rw [← hc.conj, ha', h1]
  let S : Subgroup K :=
    { carrier := {k | ι (π w k) = w * ι k * w⁻¹}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ι (π w a) = w * ι a * w⁻¹ := ha
        have hb' : ι (π w b) = w * ι b * w⁻¹ := hb
        show ι (π w (a * b)) = w * ι (a * b) * w⁻¹
        rw [map_mul, map_mul, map_mul, ha', hb']
        group
      one_mem' := by
        show ι (π w 1) = w * ι 1 * w⁻¹
        simp
      inv_mem' := fun {a} ha => by
        have ha' : ι (π w a) = w * ι a * w⁻¹ := ha
        show ι (π w a⁻¹) = w * ι a⁻¹ * w⁻¹
        rw [map_inv, map_inv, map_inv, ha']
        group }
  have hcomm : ∀ a b : K, ⁅a, b⁆ ∈ S := by
    intro a b
    obtain ⟨a', ha1, ha2⟩ := key a
    obtain ⟨b', hb1, hb2⟩ := key b
    show ι (π w ⁅a, b⁆) = w * ι ⁅a, b⁆ * w⁻¹
    have e1 : w * ι ⁅a, b⁆ * w⁻¹ = ⁅w * ι a * w⁻¹, w * ι b * w⁻¹⁆ := by
      rw [map_commutatorElement]
      simp only [commutatorElement_def]
      group
    rw [e1, ha1, hb1, ← map_commutatorElement, map_commutatorElement]
    congr 1
    obtain ⟨z₁, hz₁⟩ : ∃ z₁ ∈ Subgroup.center K, a' = π w a * z₁ :=
      ⟨(π w a)⁻¹ * a', ha2, by group⟩
    obtain ⟨z₂, hz₂⟩ : ∃ z₂ ∈ Subgroup.center K, b' = π w b * z₂ :=
      ⟨(π w b)⁻¹ * b', hb2, by group⟩
    rw [hz₁.2, hz₂.2]
    have c1 := Subgroup.mem_center_iff.1 hz₁.1
    have c2 := Subgroup.mem_center_iff.1 hz₂.1
    simp only [commutatorElement_def]
    have e2 : ∀ (p q : K), p * z₁ * (q * z₂) * (p * z₁)⁻¹ * (q * z₂)⁻¹ =
        p * q * p⁻¹ * q⁻¹ := by
      intro p q
      calc p * z₁ * (q * z₂) * (p * z₁)⁻¹ * (q * z₂)⁻¹
          = p * (z₁ * (q * z₂) * z₁⁻¹) * p⁻¹ * z₂⁻¹ * q⁻¹ := by group
        _ = p * (q * z₂) * p⁻¹ * z₂⁻¹ * q⁻¹ := by rw [← c1 (q * z₂), mul_inv_cancel_right]
        _ = p * q * (z₂ * p⁻¹ * z₂⁻¹) * q⁻¹ := by group
        _ = p * q * p⁻¹ * q⁻¹ := by rw [← c2 p⁻¹, mul_inv_cancel_right]
    simpa [commutatorElement_def] using (e2 (π w a) (π w b)).symm
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← hK, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hcomm a b
  have : k ∈ S := hS ▸ Subgroup.mem_top k
  exact this

theorem exists_noncomm_of_cover (hK : commutator K = ⊤) {Ŵ : Type*} [Group Ŵ]
    {π : Ŵ →* MulAut K} {ι : K →* Ŵ} (hc : IsThreeCover π ι) {D : Subgroup (MulAut K)}
    (hrange : π.range = D ⊔ innerAut K) {x : K} (hx : (MulAut.conj x : MulAut K) ∈ D) {v : MulAut K}
    (hv : v ∈ D) (hvx : v x ≠ x) : ∃ a ∈ D.comap π, ∃ b ∈ D.comap π, a * b ≠ b * a := by
  have hvr : v ∈ π.range := hrange ▸ Subgroup.mem_sup_left hv
  obtain ⟨w, hw⟩ := hvr
  refine ⟨ι x, ?_, w, ?_, fun h => hvx ?_⟩
  · show π (ι x) ∈ D
    rw [hc.conj]
    exact hx
  · show π w ∈ D
    rw [hw]
    exact hv
  · have h1 := cover_conj_formula hK hc w x
    rw [hw, ← h, mul_assoc, mul_inv_cancel, mul_one] at h1
    exact hc.inj h1

theorem center_ne_bot_of_cover {Ŵ : Type*} [Group Ŵ] {π : Ŵ →* MulAut K} {ι : K →* Ŵ}
    (hc : IsThreeCover π ι) : Subgroup.center K ≠ ⊥ := by
  intro hZ
  have hnt : Nontrivial π.ker := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have := hc.card
    rw [hbot, Subgroup.card_bot] at this
    omega
  obtain ⟨⟨κ, hκ⟩, hκ1⟩ := exists_ne (1 : π.ker)
  have hκ1' : κ ≠ 1 := fun h => hκ1 (Subtype.ext h)
  obtain ⟨k, hk⟩ := hc.inner κ (by rw [hκ]; exact one_mem _)
  have h1 : (MulAut.conj k : MulAut K) = 1 := by
    rw [← hc.conj, hk]
    exact hκ
  have h2 : k ∈ Subgroup.center K := by
    have := mem_center_of_conj_eq (a := k) (b := 1) (by rw [h1, map_one])
    simpa using this
  rw [hZ, Subgroup.mem_bot] at h2
  rw [h2, map_one] at hk
  exact hκ1' hk.symm

end CFSG.HardMathSupport.Solomon.Coordinator

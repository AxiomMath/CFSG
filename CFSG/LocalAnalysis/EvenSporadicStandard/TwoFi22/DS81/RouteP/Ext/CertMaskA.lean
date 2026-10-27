module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Ext.MaskDual

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu Certificates.RouteP.M24Defect

private theorem certMask_list_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

private theorem certMask_sum_map_flatMap {α β γ : Type*} [AddCommMonoid γ] (L : List α)
    (F : α → List β) (g : β → γ) :
    ((L.flatMap F).map g).sum = (L.map fun a => ((F a).map g).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

theorem entriesOK_spec {ents : List (ℕ × ℕ × ℕ)} (h : entriesOK ents = true) :
    ∀ e ∈ ents, e.1 / 24 < 24 ∧ e.1 % 24 < 24 ∧ e.1 / 24 ≠ e.1 % 24 ∧ e.2.1 < 7 ∧
      e.2.2 < 2048 := by
  simp only [entriesOK] at h
  intro e he
  have h' := List.all_eq_true.mp h e he
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at h'
  exact ⟨h'.1.1.1.1, h'.1.1.1.2, h'.1.1.2, h'.1.2, h'.2⟩

theorem bucketsZero_spec {L : List (ℕ × ℕ)} (h : bucketsZero L = true) :
    (∀ c ∈ L, c.1 < 1152) ∧ ∀ κ < 1152, bucket L κ = 0 := by
  simp only [bucketsZero, Bool.and_eq_true] at h
  refine ⟨fun c hc => ?_, fun κ hκ => ?_⟩
  · exact of_decide_eq_true (List.all_eq_true.mp h.1 c hc)
  · exact beq_iff_eq.mp (List.all_eq_true.mp h.2 κ (List.mem_range.mpr hκ))

theorem combo_sum_eq_zero (tab : Array (List (ℕ × Bool))) (ents : List (ℕ × ℕ × ℕ))
    (hent : entriesOK ents = true) (hb : bucketsZero (comboContribs tab ents) = true)
    (d ψ : ℕ → ℕ)
    (hsys : ∀ p i m : ℕ, p / 24 < 24 → p % 24 < 24 → p / 24 ≠ p % 24 → i < 7 → m < 2048 →
      bp (fpart tab p m) (d i) = ((contribs tab p i m).map fun c => bp c.2 (ψ c.1)).sum) :
    ((List.range 7).map fun i => bp (comboF tab ents i) (d i)).sum = 0 := by
  have hE := entriesOK_spec hent
  obtain ⟨hk, hz⟩ := bucketsZero_spec hb
  have hA : ((List.range 7).map fun i => bp (comboF tab ents i) (d i)).sum =
      (ents.map fun e => bp (fpart tab e.1 e.2.2) (d e.2.1)).sum := by
    rw [certMask_list_sum_range]
    rw [sum_bp_regroup ents (fun e => e.2.1) (fun e => fpart tab e.1 e.2.2) d 7
      (fun e he => (hE e he).2.2.2.1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [comboF]
  have hB : (ents.map fun e => bp (fpart tab e.1 e.2.2) (d e.2.1)).sum =
      (ents.map fun e => ((contribs tab e.1 e.2.1 e.2.2).map
        fun c => bp c.2 (ψ c.1)).sum).sum := by
    congr 1
    refine List.map_congr_left fun e he => ?_
    have h1 := hE e he
    exact hsys e.1 e.2.1 e.2.2 h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2
  have hC : (ents.map fun e => ((contribs tab e.1 e.2.1 e.2.2).map
        fun c => bp c.2 (ψ c.1)).sum).sum =
      ((comboContribs tab ents).map fun c => bp c.2 (ψ c.1)).sum := by
    rw [← certMask_sum_map_flatMap ents (fun e => contribs tab e.1 e.2.1 e.2.2)
      (fun c => bp c.2 (ψ c.1))]
    simp only [comboContribs]
  have hD : ((comboContribs tab ents).map fun c => bp c.2 (ψ c.1)).sum =
      ∑ κ ∈ Finset.range 1152, bp (bucket (comboContribs tab ents) κ) (ψ κ) := by
    have hregroup := sum_bp_regroup (comboContribs tab ents) Prod.fst Prod.snd ψ 1152 hk
    simpa only [bucket] using hregroup
  have h0 : (∑ κ ∈ Finset.range 1152, bp (bucket (comboContribs tab ents) κ) (ψ κ)) = 0 := by
    refine Finset.sum_eq_zero fun κ hκ => ?_
    rw [hz κ (Finset.mem_range.mp hκ), bp_zero_left]
  rw [hA, hB, hC, hD]
  exact h0

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

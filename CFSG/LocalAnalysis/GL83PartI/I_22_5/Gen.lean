module

public import CFSG.LocalAnalysis.GL83PartI.I_22_5.GenOne
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.GenTwo

public section

namespace GL83.CompFam

open CFSG.Open

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B : Subgroup G}
  {𝒦 : Set (Subgroup G)}

theorem exists_not_mem_of_card_lt {A : Subgroup G}
    (hlt : Nat.card A < Nat.card B) : ∃ b ∈ B, b ∉ A := by
  by_contra h
  have hle : B ≤ A := fun b hb => by
    by_contra hbA
    exact h ⟨b, hb, hbA⟩
  exact absurd (Subgroup.card_le_of_le hle) (not_le.2 hlt)

theorem IsFam.layer_le_normJoin_two (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    (hbig : p ^ 2 * Nat.card (stab B K₀) ≤ Nat.card B) : layer 𝒦 ≤ normJoin hF K₀ := by
  have hp := (Fact.out : p.Prime)
  have hAB : stab B K₀ ≤ B := inf_le_left
  have hApos : 0 < Nat.card (stab B K₀) := Nat.card_pos
  have hp2 : 2 ≤ p := hp.two_le
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  have hlt1 : Nat.card (stab B K₀) < Nat.card B := by
    calc Nat.card (stab B K₀) < 4 * Nat.card (stab B K₀) := by omega
      _ ≤ p ^ 2 * Nat.card (stab B K₀) := Nat.mul_le_mul_right _ hp4
      _ ≤ Nat.card B := hbig
  obtain ⟨b, hb, hbA⟩ := exists_not_mem_of_card_lt hlt1
  have hord : orderOf b = p := hF.orderOf_eq hb hbA
  have hcard1 : Nat.card (stab B K₀ ⊔ Subgroup.zpowers b : Subgroup G) =
      p * Nat.card (stab B K₀) := card_sup_zpowers hF.elem hAB hb hbA
  have hlt2 : ¬ B ≤ stab B K₀ ⊔ Subgroup.zpowers b := by
    intro h
    have h5 := Subgroup.card_le_of_le h
    rw [hcard1] at h5
    have h6 : Nat.card (stab B K₀) < p * Nat.card (stab B K₀) := by nlinarith
    have h7 : p ^ 2 * Nat.card (stab B K₀) = p * (p * Nat.card (stab B K₀)) := by ring
    have h8 : p * Nat.card (stab B K₀) < p * (p * Nat.card (stab B K₀)) :=
      Nat.mul_lt_mul_of_pos_left h6 hp.pos
    omega
  obtain ⟨b', hb', hb'H⟩ : ∃ b' ∈ B, b' ∉ stab B K₀ ⊔ Subgroup.zpowers b := by
    by_contra hcon
    exact hlt2 fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
  have hb'A : b' ∉ stab B K₀ := fun h => hb'H (Subgroup.mem_sup_left h)
  have hord' : orderOf b' = p := hF.orderOf_eq hb' hb'A
  have hbH' : b ∉ stab B K₀ ⊔ Subgroup.zpowers b' := by
    intro h
    have hle : stab B K₀ ⊔ Subgroup.zpowers b ≤ stab B K₀ ⊔ Subgroup.zpowers b' :=
      sup_le le_sup_left ((Subgroup.zpowers_le).2 h)
    have hc2 : Nat.card (stab B K₀ ⊔ Subgroup.zpowers b' : Subgroup G) =
        p * Nat.card (stab B K₀) := card_sup_zpowers hF.elem hAB hb' hb'A
    have heq : stab B K₀ ⊔ Subgroup.zpowers b = stab B K₀ ⊔ Subgroup.zpowers b' :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hc2])
    apply hb'H
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b')
  refine hF.layer_le_normJoin_of_independent hK₀ hb hb' hbA hb'A ?_
  intro i j hij
  have h1 : cj ((b' ^ j.val)⁻¹ * b ^ i.val) K₀ = K₀ := by
    have := congrArg (cj (b' ^ j.val)⁻¹) hij
    rw [cj_inv_cj, ← cj_mul] at this
    exact this
  have hmem : (b' ^ j.val)⁻¹ * b ^ i.val ∈ stab B K₀ :=
    mem_stab.2 ⟨B.mul_mem (B.inv_mem (B.pow_mem hb' _)) (B.pow_mem hb _), h1⟩
  have hbi : b ^ ((i.val : ℕ) : ℤ) ∈ stab B K₀ ⊔ Subgroup.zpowers b' := by
    have hcomm : b' ^ j.val * ((b' ^ j.val)⁻¹ * b ^ i.val) =
        ((b' ^ j.val)⁻¹ * b ^ i.val) * b' ^ j.val :=
      hF.mul_comm_of_mem (B.pow_mem hb' _) (hAB hmem)
    have : b ^ i.val = ((b' ^ j.val)⁻¹ * b ^ i.val) * b' ^ j.val := by
      rw [← hcomm]; group
    rw [zpow_natCast, this]
    exact Subgroup.mul_mem_sup hmem (Subgroup.pow_mem _ (Subgroup.mem_zpowers b') _)
  have hdvd := (zpow_mem_iff_dvd hord hbH' _).1 hbi
  have hi0 : i = 0 := by
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (i.val : ℤ) p).2 hdvd
    simpa using h2
  refine ⟨hi0, ?_⟩
  subst hi0
  have hjA : b' ^ ((j.val : ℕ) : ℤ) ∈ stab B K₀ := by
    rw [zpow_natCast]
    have := (stab B K₀).inv_mem hmem
    simpa using this
  have hdvd' := (zpow_mem_iff_dvd hord' hb'A _).1 hjA
  have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd (j.val : ℤ) p).2 hdvd'
  simpa using h3

theorem IsFam.layer_le_normJoin_one (hF : IsFam p B 𝒦) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝒦)
    (hB : Nat.card B = p * Nat.card (stab B K₀)) (hC : ¬ stab B K₀ ≤ cen B K₀) :
    layer 𝒦 ≤ normJoin hF K₀ := by
  have hp := (Fact.out : p.Prime)
  have hAB : stab B K₀ ≤ B := inf_le_left
  have hApos : 0 < Nat.card (stab B K₀) := Nat.card_pos
  have hlt : Nat.card (stab B K₀) < Nat.card B := by
    rw [hB]
    have := hp.two_le
    nlinarith
  obtain ⟨b, hb, hbA⟩ := exists_not_mem_of_card_lt hlt
  obtain ⟨a₀, ha₀, ha₀C⟩ : ∃ a₀ ∈ stab B K₀, a₀ ∉ cen B K₀ := by
    by_contra hcon
    exact hC fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
  have hord : orderOf b = p := hF.orderOf_eq hb hbA
  have hsup : B ≤ stab B K₀ ⊔ Subgroup.zpowers b := by
    have hle : stab B K₀ ⊔ Subgroup.zpowers b ≤ B := sup_le hAB ((Subgroup.zpowers_le).2 hb)
    have hc := card_sup_zpowers hF.elem hAB hb hbA
    have heq : stab B K₀ ⊔ Subgroup.zpowers b = B :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hB])
    rw [heq]
  have horb : ∀ K ∈ 𝒦, ∃ i : ZMod p, K = cj (b ^ i.val) K₀ := by
    intro K hK
    obtain ⟨c, hcB, rfl⟩ := hF.trans K₀ hK₀ K hK
    have hcomm : ∀ h ∈ stab B K₀, ∀ k ∈ Subgroup.zpowers b, h * k = k * h :=
      zpowers_commute fun h hh => hF.mul_comm_of_mem (hAB hh) hb
    obtain ⟨a, ha, y, hy, hcy⟩ := (mem_sup_of_commute hcomm).1 (hsup hcB)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨(n : ZMod p), ?_⟩
    have hbn : b ^ n = b ^ ((n : ZMod p).val) := by
      rw [← zpow_natCast, ZMod.val_intCast, ← hord, zpow_mod_orderOf]
    rw [← hcy, hF.mul_comm_of_mem (hAB ha) (B.zpow_mem hb n), cj_mul, (mem_stab.1 ha).2, hbn]
  exact hF.layer_le_normJoin_cyclic hK₀ hb hbA ha₀ ha₀C horb

end GL83.CompFam

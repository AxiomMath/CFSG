module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10Char

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf10

variable {n : ℕ}

theorem loc_pow_four_of_cent : ∀ b : Wr 4, (∀ k ∈ kList, k.perm ≠ 1 → b * k * b⁻¹ = k) →
    b ^ 4 = 1 := by decide +kernel

theorem loc_pow_four_of_centStar : ∀ b : Wr 4, (∀ k ∈ kStarList, k.perm ≠ 1 → b * k * b⁻¹ = k) →
    b ^ 4 = 1 := by decide +kernel

theorem exists_moving_kList : ∃ k ∈ kList, ∀ i : Fin 4, k.perm i ≠ i := by decide +kernel

theorem exists_moving_kStarList : ∃ k ∈ kStarList, ∀ i : Fin 4, k.perm i ≠ i := by decide +kernel

theorem pow_conj_embed (ι : Fin 4 ↪ Fin n) {w : Wr n} {b : Wr 4} {c : Wr n}
    (hw : w = c * embed ι b) (hc : SupportedOn c (Set.range ι)ᶜ) (j : ℕ) (k : Wr 4) :
    w ^ j * embed ι k * (w ^ j)⁻¹ = embed ι (b ^ j * k * (b ^ j)⁻¹) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    have e1 : w ^ (j + 1) * embed ι k * (w ^ (j + 1))⁻¹ =
        w * (w ^ j * embed ι k * (w ^ j)⁻¹) * w⁻¹ := by
      rw [pow_succ']
      group
    rw [e1, ih k, conj_embed ι hw hc, pow_succ']
    congr 1
    group

theorem pow_four_conj_embed_of_cent (hn : 5 ≤ n) (α : Finset (Fin n)) (hα : α.card = 4) (c : Bool)
    (L : List (Wr 4)) (hL : ∀ k ∈ L, mkQ n (embed (emb α hα) k) ∈ memBar α hα c)
    (hmove : ∃ k ∈ L, ∀ i : Fin 4, k.perm i ≠ i)
    (hdec : ∀ b : Wr 4, (∀ k ∈ L, k.perm ≠ 1 → b * k * b⁻¹ = k) → b ^ 4 = 1)
    (w : Wr n) (h : ∀ y ∈ memBar α hα c, mkQ n w * y * (mkQ n w)⁻¹ = y) (k : Wr 4) :
    w ^ 4 * embed (emb α hα) k * (w ^ 4)⁻¹ = embed (emb α hα) k := by
  classical
  set ι := emb α hα with hι
  have hcent : ∀ k ∈ L, w * embed ι k * w⁻¹ = embed ι k ∨
      w * embed ι k * w⁻¹ = embed ι k * allOnes n := by
    intro k hk
    have h1 := h _ (hL k hk)
    have h2 : mkQ n (w * embed ι k * w⁻¹) = mkQ n (embed ι k) := by
      simpa only [map_mul, map_inv] using h1
    rcases mkQ_eq_iff.mp h2 with h3 | h3
    · left
      have : (w * embed ι k * w⁻¹)⁻¹ * embed ι k = 1 := h3
      exact inv_mul_eq_one.mp this
    · right
      have h4 : embed ι k = (w * embed ι k * w⁻¹) * allOnes n := by
        rw [← h3]
        group
      calc w * embed ι k * w⁻¹ = (w * embed ι k * w⁻¹) * (allOnes n * allOnes n) := by
            rw [allOnes_mul_self, mul_one]
        _ = (w * embed ι k * w⁻¹) * allOnes n * allOnes n := (mul_assoc _ _ _).symm
        _ = embed ι k * allOnes n := by rw [← h4]
  have hperm : ∀ k ∈ L, w.perm * (embed ι k).perm = (embed ι k).perm * w.perm := by
    intro k hk
    have : (w * embed ι k * w⁻¹).perm = (embed ι k).perm := by
      rcases hcent k hk with h1 | h1
      · rw [h1]
      · rw [h1, mul_perm]
        have : (allOnes n).perm = 1 := rfl
        rw [this, mul_one]
    rw [mul_perm, mul_perm, inv_perm] at this
    calc w.perm * (embed ι k).perm = (w.perm * (embed ι k).perm * w.perm⁻¹) * w.perm := by group
      _ = (embed ι k).perm * w.perm := by rw [this]
  obtain ⟨k₀, hk₀L, hk₀⟩ := hmove
  have hrange : ∀ x, x ∈ Set.range ι ↔ w.perm x ∈ Set.range ι := by
    have hsupp : ∀ x, x ∈ Set.range ι ↔ (embed ι k₀).perm x ≠ x := by
      intro x
      constructor
      · rintro ⟨i, rfl⟩
        rw [embed_perm, embedPerm_apply]
        exact fun h' => hk₀ i (ι.injective h')
      · intro hx
        by_contra hxr
        exact hx (embed_perm_of_not_mem ι k₀ hxr)
    have hcomm : ∀ x, w.perm ((embed ι k₀).perm x) = (embed ι k₀).perm (w.perm x) := fun x =>
      congrFun (congrArg (fun f : Equiv.Perm (Fin n) => (f : Fin n → Fin n)) (hperm k₀ hk₀L)) x
    intro x
    rw [hsupp x, hsupp (w.perm x)]
    constructor
    · intro hx hy
      apply hx
      apply w.perm.injective
      rw [hcomm x, hy]
    · intro hx hy
      apply hx
      rw [← hcomm x, hy]
  obtain ⟨b, c₀, hw, hc₀⟩ := exists_decomp ι w hrange
  obtain ⟨x₀, hx₀⟩ : ∃ x : Fin n, x ∉ Set.range ι := by
    have hlt : (Finset.univ.map ι).card < (Finset.univ : Finset (Fin n)).card := by
      rw [card_map_univ, Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨x, ?_⟩
    rw [range_eq_finset]
    exact_mod_cast hx
  have hb : ∀ k ∈ L, k.perm ≠ 1 → b * k * b⁻¹ = k := by
    intro k hk hkp
    apply embed_injective ι
    rw [← conj_embed ι hw hc₀ k]
    rcases hcent k hk with h1 | h1
    · exact h1
    · exfalso
      have h2 := congrArg (fun a : Wr n => a.vec x₀) h1
      rw [conj_embed ι hw hc₀ k, embed_vec_of_not_mem ι _ hx₀, mul_vec,
        embed_vec_of_not_mem ι _ hx₀] at h2
      have h3 : (allOnes n).vec ((embed ι k).perm.symm x₀) = 1 := rfl
      rw [h3, zero_add] at h2
      exact absurd h2 (by decide)
  have hb4 := hdec b hb
  rw [pow_conj_embed ι hw hc₀ 4 k, hb4]
  simp

theorem pow_four_cent_memBar (hn : 5 ≤ n) (α : Finset (Fin n)) (hα : α.card = 4) (c : Bool)
    (w : Wr n) (h : ∀ y ∈ memBar α hα c, mkQ n w * y * (mkQ n w)⁻¹ = y) (b' : Bool) :
    ∀ y ∈ memBar α hα b', (mkQ n w) ^ 4 * y * ((mkQ n w) ^ 4)⁻¹ = y := by
  have hk : ∀ k : Wr 4, w ^ 4 * embed (emb α hα) k * (w ^ 4)⁻¹ = embed (emb α hα) k := by
    cases c
    · exact pow_four_conj_embed_of_cent hn α hα false kStarList
        (fun k hk => mkQ_embed_mem_false α hα hk) exists_moving_kStarList
        loc_pow_four_of_centStar w h
    · exact pow_four_conj_embed_of_cent hn α hα true kList
        (fun k hk => mkQ_embed_mem_true α hα hk) exists_moving_kList loc_pow_four_of_cent w h
  rintro _ ⟨a, ha, rfl⟩
  have ha' : a ∈ (if b' then memK (emb α hα) else memKStar (emb α hα) : Subgroup (Wr n)) := by
    cases b' <;> exact ha
  obtain ⟨k, -, rfl⟩ : ∃ k ∈ (if b' then kQ else kQStar : Subgroup (Wr 4)),
      embed (emb α hα) k = a := by
    cases b'
    · exact ha'
    · exact ha'
  have := hk k
  rw [← map_pow]
  simpa only [map_mul, map_inv, map_pow] using congrArg (mkQ n) this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf19

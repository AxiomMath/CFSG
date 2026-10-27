module

public import Mathlib.Tactic.LinearCombination
public import CFSG.ClassicalInvolution.Q3.AE.E64

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

variable {n : ℕ}

theorem perm_comm_of_mkQ_comm {w k : Wr n} (h : mkQ n w * mkQ n k = mkQ n k * mkQ n w) :
    w.perm * k.perm = k.perm * w.perm := by
  rw [← map_mul, ← map_mul, mkQ_eq_iff] at h
  have h1 : ((w * k)⁻¹ * (k * w)).perm = 1 := by
    rcases h with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  rw [mul_perm, inv_perm, mul_perm, mul_perm] at h1
  have h2 : (w.perm * k.perm)⁻¹ * (k.perm * w.perm) = 1 := h1
  exact inv_mul_eq_one.mp h2

theorem exists_mem_memAt_perm (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    ∀ d ∈ [d₁, d₂, d₃], ∃ k ∈ memAt α h b, k.perm = embedPerm (emb α h) d := by
  intro d hd
  cases b
  · obtain ⟨a, ha, hap⟩ := exists_mem_kQStar_perm d hd
    exact ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, by rw [embed_perm, hap]⟩
  · obtain ⟨a, ha, hap⟩ := exists_mem_kQ_perm d hd
    exact ⟨embed (emb α h) a, ⟨a, ha, rfl⟩, by rw [embed_perm, hap]⟩

theorem d₁_ne : ∀ i : Fin 4, d₁ i ≠ i := by decide

theorem stab_of_comm (ι : Fin 4 ↪ Fin n) (q : Equiv.Perm (Fin n))
    (hq : q * embedPerm ι d₁ = embedPerm ι d₁ * q) {x : Fin n} (hx : x ∈ Set.range ι) :
    q x ∈ Set.range ι := by
  by_contra hqx
  obtain ⟨i, rfl⟩ := hx
  have h1 : q (embedPerm ι d₁ (ι i)) = embedPerm ι d₁ (q (ι i)) :=
    congrArg (fun f => f (ι i)) hq
  rw [embedPerm_of_not_mem ι d₁ hqx, embedPerm_apply] at h1
  exact d₁_ne i (ι.injective (q.injective h1))

theorem perm_stab_of_comm {α : Finset (Fin n)} {h : α.card = 4} {b : Bool} {w : Wr n}
    (hc : ∀ k ∈ memAt α h b, mkQ n w * mkQ n k = mkQ n k * mkQ n w) {x : Fin n} (hx : x ∈ α) :
    w.perm x ∈ α := by
  obtain ⟨k, hk, hkp⟩ := exists_mem_memAt_perm α h b d₁ (by simp)
  have h1 := perm_comm_of_mkQ_comm (hc k hk)
  rw [hkp] at h1
  have := stab_of_comm (emb α h) w.perm h1 (x := x) (by rw [range_emb]; exact hx)
  rw [range_emb] at this
  exact this

theorem perm_eq_one_of_stab {𝒜 : Set (Finset (Fin n))}
    (hsep : ∀ x y : Fin n, x ≠ y → ∃ β ∈ 𝒜, x ∈ β ∧ y ∉ β) {q : Equiv.Perm (Fin n)}
    (hq : ∀ β ∈ 𝒜, ∀ x ∈ β, q x ∈ β) : q = 1 := by
  refine Equiv.ext fun x => ?_
  by_contra hne
  obtain ⟨β, hβ, hxβ, hyβ⟩ := hsep x (q x) (fun h => hne h.symm)
  exact hyβ (hq β hβ x hxβ)

section Main

variable {A : Subgroup (Equiv.Perm (Fin n))}

theorem perm_mem_of_mem_aeBarOver {x : AEQ n} (hx : x ∈ aeBarOver A) :
    ∃ w : Wr n, mkQ n w = x ∧ w.perm ∈ A := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w, rfl, hw.2⟩

end Main

section Models

theorem e64_sep : ∀ x y : Fin 7, x ≠ y → ∃ ℓ ∈ fanoLines, x ∈ ℓᶜ ∧ y ∉ ℓᶜ := by decide +kernel

theorem e29_sep : ∀ x y : Fin 8, x ≠ y → ∃ β ∈ affinePlanes, x ∈ β ∧ y ∉ β := by decide +kernel

theorem e29_card : ∀ β ∈ affinePlanes, β.card = 4 := by decide +kernel

end Models

section Center

variable {A : Subgroup (Equiv.Perm (Fin n))}

theorem exists_zero_zero : ∀ i : Fin 4, i = 0 ∨ ∃ d ∈ [d₁, d₂, d₃], d 0 = i := by decide

theorem zmod_two_eq_of_add : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

theorem zmod_two_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem center_eq_bot_of_members {𝒜 : Set (Finset (Fin n))} (hn : 5 ≤ n)
    (hsep : ∀ x y : Fin n, x ≠ y → ∃ β ∈ 𝒜, x ∈ β ∧ y ∉ β)
    (hcard : ∀ β ∈ 𝒜, β.card = 4)
    (hconn : ∀ v : Fin n → ZMod 2, (∀ β ∈ 𝒜, ∀ x ∈ β, ∀ y ∈ β, v x = v y) →
      ∀ x y, v x = v y)
    (hmem : ∀ β ∈ 𝒜, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ aeBarOver A) :
    Subgroup.center ↥(aeBarOver A) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨w, hwc, hwA⟩ := perm_mem_of_mem_aeBarOver c.2
  have hcomm : ∀ β ∈ 𝒜, ∀ h4 : β.card = 4, ∀ k ∈ memAt β h4 true,
      mkQ n w * mkQ n k = mkQ n k * mkQ n w := by
    intro β hβ h4 k hk
    have hkH : mkQ n k ∈ aeBarOver A := hmem β hβ h4 true ⟨k, hk, rfl⟩
    have := Subgroup.mem_center_iff.mp hc ⟨mkQ n k, hkH⟩
    have h2 := congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hwc] at h2
    exact h2.symm
  have hp1 : w.perm = 1 :=
    perm_eq_one_of_stab hsep fun β hβ x hx => perm_stab_of_comm (hcomm β hβ (hcard β hβ)) hx
  have hv : ∀ β ∈ 𝒜, ∀ x ∈ β, ∀ y ∈ β, w.vec x = w.vec y := by
    intro β hβ
    have h4 := hcard β hβ
    have hinv : ∀ k ∈ memAt β h4 true, ∀ x, w.vec (k.perm x) = w.vec x := by
      intro k hk x
      have h1 := hcomm β hβ h4 k hk
      rw [← map_mul, ← map_mul, mkQ_eq_iff] at h1
      have hsupp := supportedOn_of_mem_memAt hk
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∉ (β : Set (Fin n)) := by
        by_contra hall
        have hall' : ∀ y : Fin n, y ∈ β := fun y => by
          by_contra hy
          exact hall ⟨y, hy⟩
        have : β = Finset.univ := Finset.eq_univ_iff_forall.mpr hall'
        rw [this, Finset.card_univ, Fintype.card_fin] at h4
        omega
      have hx₀' : x₀ ∉ Set.range (emb β h4) := by rw [range_emb]; exact hx₀
      have hvec : ∀ y, (((w * k)⁻¹ * (k * w)).vec y) = w.vec (k.perm y) + w.vec y := by
        intro y
        simp only [mul_vec, inv_vec, inv_perm, mul_perm, hp1, one_mul]
        simp only [Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply]
        have e : (Equiv.symm (1 : Equiv.Perm (Fin n))) (k.perm y) = k.perm y := rfl
        rw [e]
        have := zmod_two_add_self (k.vec (k.perm y))
        linear_combination this
      have h0 : ((w * k)⁻¹ * (k * w)).vec x₀ = 0 := by
        rw [hvec, (hsupp x₀ hx₀').2]
        exact zmod_two_add_self _
      have h1' : (w * k)⁻¹ * (k * w) = 1 := by
        rcases h1 with h1 | h1
        · exact h1
        · exfalso
          rw [h1] at h0
          have e1 : (allOnes n).vec x₀ = 1 := rfl
          rw [e1] at h0
          exact absurd h0 (by decide)
      have := congrArg (fun a => a.vec x) h1'
      simp only [hvec] at this
      exact zmod_two_eq_of_add _ _ this
    intro x hx y hy
    have hv0 : ∀ z ∈ β, w.vec z = w.vec (emb β h4 0) := by
      intro z hz
      have hz' : z ∈ Set.range (emb β h4) := by rw [range_emb]; exact hz
      obtain ⟨i, rfl⟩ := hz'
      rcases exists_zero_zero i with rfl | ⟨d, hd, hdi⟩
      · rfl
      · obtain ⟨k, hk, hkp⟩ := exists_mem_memAt_perm β h4 true d hd
        have := hinv k hk (emb β h4 0)
        rw [hkp, embedPerm_apply, hdi] at this
        exact this
    rw [hv0 x hx, hv0 y hy]
  have hconst := hconn w.vec hv
  have hw : w = 1 ∨ w = allOnes n := by
    rcases zmod_two_cases (w.vec ⟨0, by omega⟩) with h | h
    · left
      refine Wr.ext (funext fun x => ?_) hp1
      rw [← hconst x ⟨0, by omega⟩, ] at h
      exact h
    · right
      refine Wr.ext (funext fun x => ?_) hp1
      rw [← hconst x ⟨0, by omega⟩] at h
      exact h
  have hmk : mkQ n w = 1 := by
    rcases hw with rfl | rfl
    · exact map_one _
    · exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hwc, hmk]
  rfl

end Center

section Fix

@[expose] def OddAutInner {m : ℕ} (H : Subgroup (AEQ m)) : Prop :=
  ∀ σ : ↥H →* ↥H, (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) → ∃ h : ↥H, ∀ r, σ r = h * r * h⁻¹

@[expose] def FixTrivial {m : ℕ} (H : Subgroup (AEQ m)) (𝒜 : Set (Finset (Fin m))) : Prop :=
  ∀ α ∈ 𝒜, ∀ (h4 : α.card = 4) (b : Bool), ∀ σ : ↥H →* ↥H,
    (∃ a : ℕ, ∀ r, (⇑σ)^[3 ^ a] r = r) →
      (∀ x : ↥H, (x : AEQ m) ∈ memBar α h4 b → σ x = x) → ∀ r, σ r = r

theorem e64_conn : ∀ v : Fin 7 → ZMod 2, (∀ ℓ ∈ fanoLines, ∀ x ∈ ℓᶜ, ∀ y ∈ ℓᶜ, v x = v y) →
    ∀ x y, v x = v y := by decide +kernel

theorem e29_conn : ∀ v : Fin 8 → ZMod 2, (∀ β ∈ affinePlanes, ∀ x ∈ β, ∀ y ∈ β, v x = v y) →
    ∀ x y, v x = v y := by decide +kernel

theorem center_e64 (hmem : ∀ β ∈ e64Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ e64Sub) :
    Subgroup.center ↥e64Sub = ⊥ :=
  center_eq_bot_of_members (A := l32) (𝒜 := e64Sets) (by norm_num)
    (fun x y hxy => by
      obtain ⟨ℓ, hℓ, h1, h2⟩ := e64_sep x y hxy
      exact ⟨ℓᶜ, ⟨ℓ, hℓ, rfl⟩, h1, h2⟩)
    (fun β ⟨ℓ, hℓ, hβ⟩ => hβ ▸ fanoLines_compl_card ℓ hℓ)
    (fun v hv => e64_conn v fun ℓ hℓ x hx y hy => hv ℓᶜ ⟨ℓ, hℓ, rfl⟩ x hx y hy) hmem

theorem center_e29 (hmem : ∀ β ∈ e29Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ e29Sub) :
    Subgroup.center ↥e29Sub = ⊥ :=
  center_eq_bot_of_members (A := agl32) (𝒜 := e29Sets) (by norm_num)
    (fun x y hxy => e29_sep x y hxy) (fun β hβ => e29_card β hβ)
    (fun v hv => e29_conn v hv) hmem

theorem center_e64' {H : Subgroup (AEQ 7)} (hH : H = e64Sub)
    (hmem : ∀ β ∈ e64Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ H) :
    Subgroup.center ↥H = ⊥ := by
  subst hH
  exact center_e64 hmem

theorem center_e29' {H : Subgroup (AEQ 8)} (hH : H = e29Sub)
    (hmem : ∀ β ∈ e29Sets, ∀ hβ : β.card = 4, ∀ b, memBar β hβ b ≤ H) :
    Subgroup.center ↥H = ⊥ := by
  subst hH
  exact center_e29 hmem

end Fix

section Closure

@[expose] def OddClosure {m : ℕ} (H : Subgroup (AEQ m)) (𝒜 : Set (Finset (Fin m))) : Prop :=
  ∀ α ∈ 𝒜, ∀ h4 : α.card = 4, ∀ β ∈ 𝒜, ∀ h4' : β.card = 4,
    zBar β h4' ∈ Subgroup.closure
      {x : AEQ m | x ∈ H ∧ x * zBar α h4 = zBar α h4 * x ∧ x ^ 3 = 1}

end Closure

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf

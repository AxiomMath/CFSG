module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

@[expose] noncomputable def A0 (l : Cover →* E) (ζ : E) :
    Subgroup E :=
  zpowers (ilift l (8, 1, 0, 0)) ⊔ (zpowers (ilift l (4, 1, 1, 1)) ⊔ zpowers ζ)

namespace IsQSetting

theorem eq_of_mul_self_ker [Finite E] (hcyc : IsCyclic q.ker) (h4 : Nat.card q.ker = 4)
    {ζ : E} (hζk : ζ ∈ q.ker) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) {z : E} (hz : z ∈ q.ker)
    (hz2 : z * z = 1) : z = 1 ∨ z = ζ := by
  obtain ⟨g, -, hg⟩ := cyclic_four h4
  have hζg : (⟨ζ, hζk⟩ : q.ker) = g * g := by
    rcases (hg ⟨ζ, hζk⟩).1.1 (Subtype.ext hζ2) with h' | h'
    · exact absurd (congrArg Subtype.val h') hζ1
    · exact h'
  rcases (hg ⟨z, hz⟩).1.1 (Subtype.ext hz2) with h' | h'
  · exact Or.inl (congrArg Subtype.val h')
  · rw [← hζg] at h'
    exact Or.inr (congrArg Subtype.val h')


theorem exists_rep_A0 (h : IsQSetting q l) (ζ : E) {e : E} (he : q e ∈ Z0) :
    ∃ ω ∈ A0 l ζ, ω⁻¹ * e ∈ q.ker := by
  have hq4 : q (ilift l (4, 1, 1, 1)) = wordPerm (tg 4) := h.q_ilift (by norm_num)
  have hq8 : q (ilift l (8, 1, 0, 0)) = wordPerm (tg 8) := h.q_ilift (by norm_num)
  obtain ⟨k, hk, hke⟩ := mem_Z0.1 he
  have hω : ∃ ω ∈ A0 l ζ, q ω = q e := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [map_one, ← hke, wordPerm_tg_zero]⟩
    · exact ⟨_, mem_sup_right (mem_sup_left (mem_zpowers _)), by rw [hq4, hke]⟩
    · exact ⟨_, mem_sup_left (mem_zpowers _), by rw [hq8, hke]⟩
    · exact ⟨ilift l (4, 1, 1, 1) * ilift l (8, 1, 0, 0),
        mul_mem (mem_sup_right (mem_sup_left (mem_zpowers _))) (mem_sup_left (mem_zpowers _)),
        by rw [map_mul, hq4, hq8, tg4_mul_tg8, hke]⟩
  obtain ⟨ω, hω, hωe⟩ := hω
  exact ⟨ω, hω, by rw [MonoidHom.mem_ker, map_mul, map_inv, hωe, inv_mul_cancel]⟩

theorem inv_mem_A0 (h : IsQSetting q l) [Finite E] (hcyc : IsCyclic q.ker)
    (h4 : Nat.card q.ker = 4) {ζ : E} (hζk : ζ ∈ q.ker) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1)
    {e : E} (he : q e ∈ Z0) (he2 : e * e = 1) : e ∈ A0 l ζ := by
  have hA := (h.exists_A0 hζk hζ1 hζ2).1
  obtain ⟨ω, hω, hz⟩ := h.exists_rep_A0 ζ he
  have hzc := mem_center_iff.mp (h.ker_le hz)
  have hω2 := hA.1.2 ω hω
  have hez : e = ω * (ω⁻¹ * e) := by group
  have key : e * e = ω * ω * ((ω⁻¹ * e) * (ω⁻¹ * e)) := by
    generalize ω⁻¹ * e = z at hzc hez ⊢
    rw [hez]
    calc ω * z * (ω * z) = ω * (z * ω) * z := by group
      _ = ω * (ω * z) * z := by rw [← hzc ω]
      _ = ω * ω * (z * z) := by group
  rw [he2, hω2, one_mul] at key
  rw [hez]
  refine mul_mem hω (mem_sup_right (mem_sup_right ?_))
  rcases eq_of_mul_self_ker hcyc h4 hζk hζ1 hζ2 hz key.symm with h' | h'
  · rw [h']
    exact one_mem _
  · rw [h']
    exact mem_zpowers _

theorem A0_inf_ker (h : IsQSetting q l) [Finite E] (hcyc : IsCyclic q.ker)
    (h4 : Nat.card q.ker = 4) {ζ : E} (hζk : ζ ∈ q.ker) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) :
    A0 l ζ ⊓ q.ker = zpowers ζ := by
  have hA := (h.exists_A0 hζk hζ1 hζ2).1
  refine le_antisymm (fun z hz => ?_) (le_inf (le_sup_right.trans le_sup_right)
    (zpowers_le.2 hζk))
  obtain ⟨hzA, hzk⟩ := mem_inf.mp hz
  rcases eq_of_mul_self_ker hcyc h4 hζk hζ1 hζ2 hzk (hA.1.2 z hzA) with h' | h'
  · rw [h']
    exact one_mem _
  · rw [h']
    exact mem_zpowers _


theorem cce_props (h : IsQSetting q l) {κ : ℕ} {ζ : E} (hκ : KClass l κ ζ) (hζk : ζ ∈ q.ker)
    (hζ2 : ζ * ζ = 1) {k m : ℕ} (hd : (κ, k, m) ∈ cceIdx) :
    q (l (cv (tw k))) ∈ T0 ∧ (∀ x ∈ A0 l ζ, l (cv (tw k)) * x = x * l (cv (tw k))) ∧
      l (cv (tw k)) ^ 4 = 1 ∧
      q (l (cv (tw k)) * l (cv (tw k))) = wordPerm (tg m) := by
  obtain ⟨h4b, h8b, hfb, hsq⟩ := cce_spec hd
  have hk64 : k < 64 := by
    simp only [cceIdx, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hd
    omega
  have hc : ∀ {w : ℕ}, commBit κ k w false = true →
      l (cv (tw k)) * l (cv (tw w)) = l (cv (tw w)) * l (cv (tw k)) := by
    intro w hb
    have h1 := h.lift_comm_of_bit hκ hζ2 hb
    simp only [Bool.false_eq_true, ↓reduceIte] at h1
    generalize l (cv (tw k)) = x at h1 ⊢
    generalize l (cv (tw w)) = y at h1 ⊢
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  have hil : ∀ {d : ℕ × ℕ × ℕ × ℕ}, commBit κ k d.1 false = true →
      l (cv (tw k)) * ilift l d = ilift l d * l (cv (tw k)) := by
    intro d hb
    have h1 := hc hb
    have h2 := h.psi_comm (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
      Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4))) (l (cv (tw k)))
    unfold ilift
    generalize psi l (Multiplicative.ofAdd (-(d.2.1 : ZMod 4)),
      Multiplicative.ofAdd (-(d.2.2.1 : ZMod 4))) = z at h2 ⊢
    generalize l (cv (tw k)) = x at h1 h2 ⊢
    calc x * (l (cv (tw d.1)) * z) = x * l (cv (tw d.1)) * z := by group
      _ = l (cv (tw d.1)) * x * z := by rw [h1]
      _ = l (cv (tw d.1)) * (x * z) := by group
      _ = l (cv (tw d.1)) * (z * x) := by rw [h2]
      _ = l (cv (tw d.1)) * z * x := by group
  refine ⟨by rw [h.q_lift hk64]; exact tg_mem_T0 k hk64, fun x hx => ?_,
    h.lift_fourth_of_bit hκ hζ2 hfb, by rw [map_mul, h.q_lift hk64, hsq]⟩
  have hle : A0 l ζ ≤ centralizer {l (cv (tw k))} := by
    refine sup_le (zpowers_le.2 ?_) (sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_))
    · exact mem_centralizer_singleton_iff.mpr (hil (d := (8, 1, 0, 0)) h8b).symm
    · exact mem_centralizer_singleton_iff.mpr (hil (d := (4, 1, 1, 1)) h4b).symm
    · exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (h.ker_le hζk) _).symm
  exact (mem_centralizer_singleton_iff.mp (hle hx)).symm

theorem exists_cce (h : IsQSetting q l) [Finite E] (hcyc : IsCyclic q.ker)
    (h4 : Nat.card q.ker = 4) {ζ : E} (hζk : ζ ∈ q.ker) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) :
    ∃ s₁ s₂ : E, q s₁ ∈ T0 ∧ q s₂ ∈ T0 ∧ (∀ x ∈ A0 l ζ, s₁ * x = x * s₁) ∧
      (∀ x ∈ A0 l ζ, s₂ * x = x * s₂) ∧ s₁ ^ 4 = 1 ∧ s₂ ^ 4 = 1 ∧
      q (s₁ * s₁) = wordPerm (tg 4) ∧ q (s₂ * s₂) = wordPerm (tg 8) := by
  obtain ⟨κ, hκ⟩ := h.exists_kclass hcyc h4 hζk hζ1 hζ2
  have key : ∀ {k₁ k₂ : ℕ}, (κ, k₁, 4) ∈ cceIdx → (κ, k₂, 8) ∈ cceIdx →
      ∃ s₁ s₂ : E, q s₁ ∈ T0 ∧ q s₂ ∈ T0 ∧ (∀ x ∈ A0 l ζ, s₁ * x = x * s₁) ∧
        (∀ x ∈ A0 l ζ, s₂ * x = x * s₂) ∧ s₁ ^ 4 = 1 ∧ s₂ ^ 4 = 1 ∧
        q (s₁ * s₁) = wordPerm (tg 4) ∧ q (s₂ * s₂) = wordPerm (tg 8) := by
    intro k₁ k₂ h₁ h₂
    obtain ⟨a₁, b₁, c₁, d₁⟩ := h.cce_props hκ hζk hζ2 h₁
    obtain ⟨a₂, b₂, c₂, d₂⟩ := h.cce_props hκ hζk hζ2 h₂
    exact ⟨_, _, a₁, a₂, b₁, b₂, c₁, c₂, d₁, d₂⟩
  rcases hκ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact key (k₁ := 17) (k₂ := 23) (by decide) (by decide)
  · exact key (k₁ := 27) (k₂ := 18) (by decide) (by decide)
  · exact key (k₁ := 22) (k₂ := 25) (by decide) (by decide)

end IsQSetting

end CFSG.ComponentClassification.GrSLit.L34Facts

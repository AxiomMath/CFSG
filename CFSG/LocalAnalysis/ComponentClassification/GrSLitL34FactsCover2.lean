module

public import Certificates.Certificate22206
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCentralFourModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModelBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable

structure Cover2Parts : Prop where
  specs : ∀ s ∈ cover2Specs, cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2)
  even : ∀ d ∈ commData2, (d.2.2.1 = 0 ∨ d.2.2.1 = 2) ∧ (d.2.2.2.1 = 0 ∨ d.2.2.2.1 = 2)
  trans : transOK = true
  cce : cceOK = true

theorem cover2Parts : Cover2Parts := by
  obtain ⟨h1, h2, h3, h4⟩ := Certificates.certificate22206
  simp only [List.all_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h2
  exact ⟨h1, h2, h3, h4⟩

theorem cv_spec2
    {s : List (Fin 2 × Bool) × ℕ × ℕ × ℕ} (hs : s ∈ cover2Specs) :
    cv s.1 = cv (zword s.2.1 s.2.2.1 s.2.2.2) :=
  cover2Parts.specs s hs

theorem comm2_spec
    {d : ℕ × ℕ × ℕ × ℕ × ℕ} (hd : d ∈ commData2) :
    cv (tw d.1) * cv (tw d.2.1) * (cv (tw d.1))⁻¹ * (cv (tw d.2.1))⁻¹ =
      z₁ ^ d.2.2.1 * z₂ ^ d.2.2.2.1 * z₃ ^ d.2.2.2.2 := by
  have hs : (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2) ∈ cover2Specs :=
    List.mem_append_left _ (List.mem_map_of_mem (f := fun d : ℕ × ℕ × ℕ × ℕ × ℕ =>
      (commWord (tw d.1) (tw d.2.1), d.2.2.1, d.2.2.2.1, d.2.2.2.2)) hd)
  have h := cv_spec2 hs
  rw [commWord, cv_append, cv_append, cv_append, cv_invRev, cv_invRev, cv_zword] at h
  exact h

theorem fourth2_spec
    {d : ℕ × ℕ × ℕ × ℕ} (hd : d ∈ fourthData2) :
    cv (tw d.1) ^ 4 = z₁ ^ d.2.1 * z₂ ^ d.2.2.1 * z₃ ^ d.2.2.2 := by
  have hs : (wpow (tw d.1) 4, d.2.1, d.2.2.1, d.2.2.2) ∈ cover2Specs :=
    List.mem_append_right _ (List.mem_map_of_mem (f := fun d : ℕ × ℕ × ℕ × ℕ =>
      (wpow (tw d.1) 4, d.2.1, d.2.2.1, d.2.2.2)) hd)
  have h := cv_spec2 hs
  rw [cv_wpow, cv_zword] at h
  exact h

theorem commBit_spec {κ k w : ℕ} {f : Bool} (h : commBit κ k w f = true) :
    ∃ d ∈ commData2, d.1 = k ∧ d.2.1 = w ∧ kbit κ d.2.2.1 d.2.2.2.1 = f := by
  simp only [commBit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨d, hd, ⟨h1, h2⟩, h3⟩ := h
  exact ⟨d, hd, h1, h2, h3⟩

theorem fourthBit_spec {κ k : ℕ} (h : fourthBit κ k = true) :
    ∃ d ∈ fourthData2, d.1 = k ∧ (d.2.1 = 0 ∨ d.2.1 = 2) ∧ (d.2.2.1 = 0 ∨ d.2.2.1 = 2) ∧
      kbit κ d.2.1 d.2.2.1 = false := by
  simp only [fourthBit, List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨d, hd, ⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨d, hd, h1, h2, h3, h4⟩

theorem exists_trans {κ : ℕ} (hκ : κ ∈ [0, 1, 2]) {I : List ℕ}
    (hI : I ∈ uIdx) {k₁ k₂ : ℕ}
    (h₁ : k₁ ∈ I) (h₂ : k₂ ∈ I) (h₁0 : k₁ ≠ 0) (h₂0 : k₂ ≠ 0) (h₁₂ : k₁ ≠ k₂) (f₁ f₂ : Bool) :
    ∃ w ∈ I, commBit κ k₁ w f₁ = true ∧ commBit κ k₂ w f₂ = true := by
  have h := cover2Parts.trans
  simp only [transOK, List.all_eq_true, List.any_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.and_eq_true] at h
  rcases h κ hκ I hI k₁ h₁ k₂ h₂ with ((h0 | h0) | h0) | h
  · exact absurd h0 h₁0
  · exact absurd h0 h₂0
  · exact absurd h0 h₁₂
  · exact h f₁ (by cases f₁ <;> simp) f₂ (by cases f₂ <;> simp)

theorem cce_spec {d : ℕ × ℕ × ℕ} (hd : d ∈ cceIdx) :
    commBit d.1 d.2.1 4 false = true ∧ commBit d.1 d.2.1 8 false = true ∧
      fourthBit d.1 d.2.1 = true ∧
      wordPerm (tg d.2.1) * wordPerm (tg d.2.1) = wordPerm (tg d.2.2) := by
  have h := cover2Parts.cce
  simp only [cceOK, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h d hd
  exact ⟨h1, h2, h3, ((tabRep_wordTab _).comp (tabRep_wordTab _)).perm_eq (h4 ▸ tabRep_wordTab _)⟩

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

@[expose] def KClass (l : Cover →* E) (κ : ℕ) (ζ : E) : Prop :=
  (κ = 0 ∧ l z₁ ^ 2 = 1 ∧ l z₂ ^ 2 = ζ) ∨ (κ = 1 ∧ l z₂ ^ 2 = 1 ∧ l z₁ ^ 2 = ζ) ∨
    (κ = 2 ∧ l z₁ ^ 2 = ζ ∧ l z₂ ^ 2 = ζ)

theorem KClass.mem {κ : ℕ} {ζ : E} (h : KClass l κ ζ) : κ ∈ [0, 1, 2] := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem kbit_spec {κ : ℕ} {ζ : E} (h : KClass l κ ζ)
    (hζ : ζ * ζ = 1) {p r : ℕ} (hp : p = 0 ∨ p = 2) (hr : r = 0 ∨ r = 2) :
    l z₁ ^ p * l z₂ ^ r = if kbit κ p r then ζ else 1 := by
  have hz2 : ζ ^ 2 = 1 := by rw [pow_two, hζ]
  rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
    rcases hp with rfl | rfl <;> rcases hr with rfl | rfl <;>
    simp [kbit, h1, h2, ← pow_two, hz2]

namespace IsQSetting

theorem exists_kclass
    (h : IsQSetting q l) [Finite E] (hcyc : IsCyclic q.ker)
    (h4 : Nat.card q.ker = 4) {ζ : E} (hζk : ζ ∈ q.ker) (hζ1 : ζ ≠ 1) (hζ2 : ζ * ζ = 1) :
    ∃ κ, KClass l κ ζ := by
  obtain ⟨g, hg1, hg⟩ := cyclic_four h4
  have hζg : ζ = (g * g : q.ker) := by
    rcases (hg ⟨ζ, hζk⟩).1.1 (Subtype.ext hζ2) with h' | h'
    · exact absurd (congrArg Subtype.val h') hζ1
    · exact congrArg Subtype.val h'
  have hsq : ∀ c : Cover, c ∈ sigma.ker → l c ^ 2 = 1 ∨ l c ^ 2 = ζ := by
    intro c hc
    rw [pow_two, hζg]
    rcases (hg ⟨l c, h.l_mem_ker hc⟩).2 with h' | h'
    · exact Or.inl (congrArg Subtype.val h')
    · exact Or.inr (congrArg Subtype.val h')
  have hk1 : z₁ ∈ sigma.ker := MonoidHom.mem_ker.mpr sigma_z₁
  have hk2 : z₂ ∈ sigma.ker := MonoidHom.mem_ker.mpr sigma_z₂
  rcases hsq z₁ hk1 with h1 | h1 <;> rcases hsq z₂ hk2 with h2 | h2
  · exfalso
    apply hg1
    apply Subtype.ext
    exact h.ker_sq_of h1 h2 g.2
  · exact ⟨0, Or.inl ⟨rfl, h1, h2⟩⟩
  · exact ⟨1, Or.inr (Or.inl ⟨rfl, h2, h1⟩)⟩
  · exact ⟨2, Or.inr (Or.inr ⟨rfl, h1, h2⟩)⟩

theorem lift_comm2
    (h : IsQSetting q l) {d : ℕ × ℕ × ℕ × ℕ × ℕ}
    (hd : d ∈ commData2) :
    l (cv (tw d.1)) * l (cv (tw d.2.1)) * (l (cv (tw d.1)))⁻¹ * (l (cv (tw d.2.1)))⁻¹ =
      l z₁ ^ d.2.2.1 * l z₂ ^ d.2.2.2.1 := by
  have h1 := congrArg l (comm2_spec hd)
  simp only [map_mul, map_inv, map_pow, h.lz₃, one_pow, mul_one] at h1
  exact h1

theorem lift_comm_of_bit
    (h : IsQSetting q l) {κ : ℕ} {ζ : E} (hκ : KClass l κ ζ)
    (hζ : ζ * ζ = 1) {k w : ℕ} {f : Bool} (hb : commBit κ k w f = true) :
    l (cv (tw k)) * l (cv (tw w)) * (l (cv (tw k)))⁻¹ * (l (cv (tw w)))⁻¹ =
      if f then ζ else 1 := by
  obtain ⟨d, hd, rfl, rfl, hf⟩ := commBit_spec hb
  rw [h.lift_comm2 hd, kbit_spec hκ hζ (cover2Parts.even d hd).1 (cover2Parts.even d hd).2, hf]

theorem lift_fourth_of_bit
    (h : IsQSetting q l) {κ : ℕ} {ζ : E} (hκ : KClass l κ ζ)
    (hζ : ζ * ζ = 1) {k : ℕ} (hb : fourthBit κ k = true) : l (cv (tw k)) ^ 4 = 1 := by
  obtain ⟨d, hd, rfl, hp, hr, hf⟩ := fourthBit_spec hb
  have h1 := congrArg l (fourth2_spec hd)
  simp only [map_mul, map_pow, h.lz₃, one_pow, mul_one] at h1
  rw [h1, kbit_spec hκ hζ hp hr, hf]
  rfl

end IsQSetting

end CFSG.ComponentClassification.GrSLit.L34Facts

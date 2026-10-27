module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnGamma
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.IVK91
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnTransfer

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Sec14

theorem isSylow2In_inf_normal {Y : Type*} [Group Y] [Finite Y] {T N : Subgroup Y} [N.Normal]
    (hT : IsSylow2In T ⊤) : IsSylow2In (T ⊓ N) N := by
  obtain ⟨P, hP, hTP⟩ := exists_sylow2_ge (A := T ⊓ N) (H := N)
    (IsPGroup.to_le hT.2.1 inf_le_left) inf_le_right
  obtain ⟨P', hP', hPP'⟩ := exists_sylow2_ge (A := P) (H := ⊤) hP.2.1 le_top
  obtain ⟨g, -, hg⟩ := sylow2_exists_conj hT hP'
  have hle : Hconj g⁻¹ P ≤ T ⊓ N := by
    intro a ha
    have h1 : g⁻¹ * a * g ∈ P := by simpa [mem_Hconj] using ha
    have h2 : g⁻¹ * a * g ∈ Hconj g T := hg ▸ hPP' h1
    rw [mem_Hconj] at h2
    have h3 : a ∈ T := by simpa [mul_assoc] using h2
    have h4 : a ∈ N := by
      have := (inferInstance : N.Normal).conj_mem _ (hP.1 h1) g
      simpa [mul_assoc] using this
    exact Subgroup.mem_inf.2 ⟨h3, h4⟩
  have hcard : Nat.card P ≤ Nat.card ↥(T ⊓ N) := by
    calc Nat.card P = Nat.card (Hconj g⁻¹ P) := (Hconj_card g⁻¹ P).symm
      _ ≤ Nat.card ↥(T ⊓ N) := Subgroup.card_le_of_le hle
  have : T ⊓ N = P := Subgroup.eq_of_le_of_card_ge hTP hcard
  rw [this]
  exact hP

theorem normal_of_ctx (h91 : IVK_9_1) (hIG15 : IG_15_15) (hIG16 : IG_16_2) {Y : Type} [Group Y]
    [Finite Y] (hK : IsKGroupNative Y) (hodd : pPrimeCoreOf 2 (commutator Y) = ⊥)
    {T A A₁ A₂ : Subgroup Y} (h : Ctx16 T A A₁ A₂) (hAc : A ≤ commutator Y)
    {w₁ w₂ : Y} (hw₁ : w₁ ∈ A₁) (hw₂ : w₂ ∈ A₂) (hw₁1 : w₁ ≠ 1) (hw₂1 : w₂ ≠ 1)
    (hconj : ∀ v ∈ A, v ≠ 1 → (v ∈ A₁ ∨ v ∈ A₂) →
      ∃ g : Y, g * v * g⁻¹ = w₁ ∨ g * v * g⁻¹ = w₂)
    (hsing : ∃ α ∈ A, ∃ β ∈ A, α ≠ 1 ∧ α ∉ A₁ ∧ α ∉ A₂ ∧ β ≠ 1 ∧ β ∉ A₁ ∧ β ∉ A₂ ∧
      ∀ n ∈ commutator Y ⊓ Subgroup.normalizer (A : Set Y), n * α * n⁻¹ ≠ β) :
    A.Normal := by
  have hNF := no_fusion h.sylow h.le h.idx h.elem h.card h.cent
  have hTH : T ⊓ commutator Y = A := inf_commutator_eq hIG15 h.sylow h.le h.idx hNF hAc
  have hSyl : IsSylow2In A (commutator Y) := by
    have := isSylow2In_inf_normal (N := commutator Y) h.sylow
    rwa [hTH] at this
  have hfus := fusion_control hIG16 (H := commutator Y) hSyl (fun a ha b hb => h.comm_A ha hb)
  have hdich := h.dichotomy hAc hSyl hfus hw₁ hw₂ hw₁1 hw₂1 hconj
  rcases hdich with ⟨x₃, hx₃M, hfpf, hx₃c, hgen⟩ | hII
  swap
  · exfalso
    obtain ⟨α, hα, β, hβ, hα1, hαA₁, hαA₂, hβ1, hβA₁, hβA₂, hn⟩ := hsing
    obtain ⟨n, hnM, hnα⟩ := hII α hα β hβ hα1 hαA₁ hαA₂ hβ1 hβA₁ hβA₂
    exact hn n hnM hnα
  have hKH : IsKGroupNative ↥(commutator Y) :=
    SectionRank.IsKGroupCat.subgroup hK (commutator Y)
  have h9 := h91 Y (commutator Y) A hKH hSyl h.elem h.card
    (Or.inr ⟨x₃, hx₃M, 3, Or.inl rfl, hx₃c, fun s hs hs1 => hfpf s hs hs1, hgen⟩)
  rw [hodd, bot_sup_eq] at h9
  have hconjA : ∀ c ∈ commutator Y, ∀ a ∈ A, c * a * c⁻¹ ∈ A := fun c hc a ha =>
    h9.conj_mem ⟨a, hAc ha⟩ ha ⟨c, hc⟩
  have hAH : ∀ c ∈ commutator Y, Hconj c A = A := by
    intro c hc
    ext a
    rw [mem_Hconj]
    constructor
    · intro ha
      have := hconjA c⁻¹ ((commutator Y).inv_mem hc) _ ha
      simpa [mul_assoc] using this
    · exact hconjA c hc a
  refine ⟨fun n hn g => ?_⟩
  have hHg : Hconj g (commutator Y) = commutator Y := by
    ext t
    simp only [mem_Hconj]
    constructor
    · intro ht
      have := (inferInstance : (commutator Y).Normal).conj_mem _ ht g⁻¹
      simpa [mul_assoc] using this
    · intro ht
      exact (inferInstance : (commutator Y).Normal).conj_mem _ ht g
  have hB : IsSylow2In (Hconj g⁻¹ A) (commutator Y) := by
    have := sylow2_conj hSyl g⁻¹
    have hH' : Hconj g⁻¹ (commutator Y) = commutator Y := by
      have := hHg
      ext t
      simp only [mem_Hconj]
      constructor
      · intro ht
        have := (inferInstance : (commutator Y).Normal).conj_mem _ ht g
        simpa [mul_assoc] using this
      · intro ht
        have := (inferInstance : (commutator Y).Normal).conj_mem _ ht g⁻¹
        simpa [mul_assoc] using this
    rwa [hH'] at this
  obtain ⟨c, hc, hcB⟩ := sylow2_exists_conj hSyl hB
  have hBA : Hconj g⁻¹ A = A := by rw [hcB]; exact hAH c hc
  have : g * n * g⁻¹ ∈ Hconj g⁻¹ A := by
    rw [mem_Hconj]; simpa [mul_assoc] using hn
  rw [hBA] at this
  exact this

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

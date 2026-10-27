module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSSwap
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveWSylow

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup

variable {G : Type*} [Group G]

theorem mem_normalizer_inf_of_mem {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro z
  simp only [Subgroup.mem_inf] at hH hK ⊢
  rw [hH z, hK z]

variable [Finite G]

theorem false_of_swap_gen {W V S S₀ F W₀ A X : Subgroup G} {t : G} {k : ℕ}
    (hW : ∀ w ∈ W, w * w = 1) (hWV : Nat.card W = Nat.card V ^ 2) (ht : t * t = 1)
    (hWS : W ≤ S) (hSN : S ≤ normalizer (W : Set G)) (htS : t ∈ S)
    (htcomm : ∀ s ∈ S, t * s * t⁻¹ * s⁻¹ ∈ V)
    (hB : ∀ B : Subgroup G, B ≤ S → B ≤ centralizer (V : Set G) → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) → Nat.card B = Nat.card W → B = W)
    (hmax : ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P ≤ normalizer (W : Set G) → P = S)
    (hS2 : IsPGroup 2 S) (hS₀S : S₀ ≤ S) (hS₀C : S₀ ≤ centralizer (W₀ : Set G))
    (hSgen : S ≤ S₀ ⊔ F ⊔ zpowers t) (hScard : Nat.card S ≤ k * Nat.card S₀)
    (hinf : A ⊓ A.map (MulAut.conj t).toMonoidHom = ⊥)
    (hc : ∀ a ∈ A, ∀ b ∈ A.map (MulAut.conj t).toMonoidHom, a * b = b * a)
    (htW₀ : t ∈ normalizer (W₀ : Set G)) (hE1 : W₀ ⊓ A ≠ ⊥)
    (hFA : F ≤ A ⊔ A.map (MulAut.conj t).toMonoidHom) (hFW₀ : F ≤ normalizer (W₀ : Set G))
    (hX2 : IsPGroup 2 X) (hXA : X ≤ A) (hXW₀ : X ≤ normalizer (W₀ : Set G))
    (hXE : X ⊓ centralizer ((W₀ ⊓ A : Subgroup G) : Set G) = ⊥)
    (hk : k < 2 * Nat.card X ^ 2)
    (hkey : ∀ s ∈ S, s ∉ S₀ ⊔ F → s * s = 1 →
      Nat.card (W ⊓ centralizer ({s} : Set G) : Subgroup G) ≤ Nat.card V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A' : Subgroup G := A.map (MulAut.conj t).toMonoidHom with hA'
  set E : Subgroup G := W₀ ⊓ A with hE
  set E' : Subgroup G := W₀ ⊓ A' with hE'
  have hEE' : E.map (MulAut.conj t).toMonoidHom = E' := map_conj_inf_eq ht htW₀
  have hE'E : E'.map (MulAut.conj t).toMonoidHom = E := by
    rw [← hEE', map_conj_map_conj_of_mul_self ht]
  have hcA' : ∀ b ∈ A', ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hc a ha b hb).symm
  have hANA : A ⊔ A' ≤ normalizer (A : Set G) := sup_le_normalizer_of_commute hc
  have hANA' : A ⊔ A' ≤ normalizer (A' : Set G) := by
    rw [sup_comm]; exact sup_le_normalizer_of_commute hcA'
  set R₀ : Subgroup G := normalizer (W₀ : Set G) ⊓ normalizer (E : Set G) ⊓
    normalizer (E' : Set G) with hR₀
  have hmemR₀ : ∀ g, g ∈ normalizer (W₀ : Set G) → g ∈ A ⊔ A' → g ∈ R₀ := fun g hgW hgA =>
    Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hgW, mem_normalizer_inf_of_mem hgW (hANA hgA)⟩,
      mem_normalizer_inf_of_mem hgW (hANA' hgA)⟩
  have hCR₀ : centralizer (W₀ : Set G) ≤ R₀ :=
    le_inf (le_inf (centralizer_le_normalizer_of_le le_rfl)
      (centralizer_le_normalizer_of_le inf_le_left))
      (centralizer_le_normalizer_of_le inf_le_left)
  have hFR₀ : F ≤ R₀ := fun f hf => hmemR₀ f (hFW₀ hf) (hFA hf)
  have htNR₀ : t ∈ normalizer (R₀ : Set G) :=
    mem_normalizer_inf_of_swap (map_conj_eq_of_mem_normalizer htW₀) hEE' hE'E
  have htNE : t ∉ normalizer (E : Set G) := by
    intro htN
    have h1 : E.map (MulAut.conj t).toMonoidHom = E := map_conj_eq_of_mem_normalizer htN
    rw [hEE'] at h1
    apply hE1
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ E' := h1 ▸ hz
    have h3 : z ∈ A ⊓ A' := Subgroup.mem_inf.2 ⟨hz.2, hz'.2⟩
    rwa [hinf] at h3
  have htR₀ : t ∉ R₀ := fun htR => htNE (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 htR).1).2
  set R : Subgroup G := R₀ ⊔ zpowers t with hR
  have hRN : R ≤ normalizer (R₀ : Set G) := sup_le le_normalizer ((zpowers_le).2 htNR₀)
  have hS₀FR₀ : S₀ ⊔ F ≤ R₀ := sup_le (hS₀C.trans hCR₀) hFR₀
  have hSR : S ≤ R := hSgen.trans (sup_le (hS₀FR₀.trans le_sup_left) le_sup_right)
  set X' : Subgroup G := X.map (MulAut.conj t).toMonoidHom with hX'
  have hX'A' : X' ≤ A' := map_mono hXA
  have hX'c : Nat.card X' = Nat.card X :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hXR₀ : X ≤ R₀ := fun x hx => hmemR₀ x (hXW₀ hx) (mem_sup_left (hXA hx))
  have hX'R₀ : X' ≤ R₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 htNR₀ x).1 (hXR₀ hx)
  have hX'W₀ : X' ≤ normalizer (W₀ : Set G) := fun x hx =>
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hX'R₀ hx)).1).1
  have hX'N : X' ≤ normalizer (X : Set G) := by
    rw [le_normalizer_iff]
    intro b hb a ha
    rw [hcA' b (hX'A' hb) a (hXA ha), mul_inv_cancel_right]
    exact ha
  set B₀ : Subgroup G := X ⊔ X' with hB₀
  have hB₀2 : IsPGroup 2 B₀ := IsPGroup.to_sup_of_normal_left' hX2 (hX2.map _) hX'N
  have htB₀ : t ∈ normalizer (B₀ : Set G) := by
    refine mem_normalizer_of_mul_self_of_conj_mem ht fun z hz => ?_
    have h1 : B₀.map (MulAut.conj t).toMonoidHom ≤ B₀ := by
      rw [hB₀, Subgroup.map_sup, ← hX', map_conj_map_conj_of_mul_self ht, sup_comm]
    exact h1 ⟨z, hz, rfl⟩
  set T : Subgroup G := B₀ ⊔ zpowers t with hT
  have hT2 : IsPGroup 2 T := IsPGroup.to_sup_of_normal_left' hB₀2
    (isPGroup_zpowers_of_mul_self_eq_one ht) ((zpowers_le).2 htB₀)
  have hXT : X ≤ T := le_sup_left.trans le_sup_left
  have hX'T : X' ≤ T := le_sup_right.trans le_sup_left
  have htT : t ∈ T := mem_sup_right (mem_zpowers t)
  have hTR : T ≤ R := sup_le (sup_le (hXR₀.trans le_sup_left) (hX'R₀.trans le_sup_left))
    le_sup_right
  have hTW₀ : T ≤ normalizer (W₀ : Set G) :=
    sup_le (sup_le hXW₀ hX'W₀) ((zpowers_le).2 htW₀)
  have hTC : T ≤ normalizer (centralizer (W₀ : Set G) : Set G) := fun z hz =>
    mem_normalizer_centralizer_sOne (hTW₀ hz)
  have hX'E' : X' ⊓ centralizer (E' : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxC⟩
    have hxE : x ∈ X ⊓ centralizer (E : Set G) := by
      refine Subgroup.mem_inf.2 ⟨hx, mem_centralizer_iff.2 fun e he => ?_⟩
      have h1 := (mem_centralizer_iff.1 hxC) (t * e * t⁻¹) (hEE' ▸ ⟨e, he, rfl⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      have h2 : t * (e * x) * t⁻¹ = t * (x * e) * t⁻¹ := by
        rw [show t * (e * x) * t⁻¹ = t * e * t⁻¹ * (t * x * t⁻¹) by group, h1]
        group
      simpa using h2
    rw [hXE, Subgroup.mem_bot] at hxE
    rw [hxE, map_one]
    exact one_mem _
  have hchain : 2 * Nat.card X ^ 2 * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) ≤
      Nat.card T := by
    set H₁ : Subgroup G := T ⊓ centralizer (E : Set G) ⊓ centralizer (E' : Set G) with hH₁
    set H₂ : Subgroup G := T ⊓ centralizer (E : Set G) with hH₂
    set H₃ : Subgroup G := T ⊓ normalizer (E : Set G) with hH₃
    have hTNE : ∀ g ∈ T, g ∈ normalizer (E : Set G) → g ∈ normalizer (E' : Set G) →
        g ∈ normalizer (H₁ : Set G) ∧ g ∈ normalizer (H₂ : Set G) := by
      intro g hgT hgE hgE'
      have hgT' : g ∈ normalizer (T : Set G) := le_normalizer hgT
      exact ⟨mem_normalizer_inf_of_mem (mem_normalizer_inf_of_mem hgT'
        (mem_normalizer_centralizer_sOne hgE)) (mem_normalizer_centralizer_sOne hgE'),
        mem_normalizer_inf_of_mem hgT' (mem_normalizer_centralizer_sOne hgE)⟩
    have h0 : centralizer (W₀ : Set G) ⊓ T ≤ H₁ := by
      intro z hz
      obtain ⟨hzC, hzT⟩ := Subgroup.mem_inf.1 hz
      exact Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hzT, centralizer_le inf_le_left hzC⟩,
        centralizer_le inf_le_left hzC⟩
    have h1 : Nat.card X * Nat.card H₁ ≤ Nat.card H₂ := by
      have hN : X' ≤ normalizer (H₁ : Set G) := fun x hx =>
        (hTNE x (hX'T hx) (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hX'R₀ hx)).1).2
          (Subgroup.mem_inf.1 (hX'R₀ hx)).2).1
      have h2 := card_sup_mul_card_inf_of_le_normalizer_sOne hN
      have hinf1 : H₁ ⊓ X' = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have h3 : z ∈ X' ⊓ centralizer (E' : Set G) := Subgroup.mem_inf.2 ⟨hz.2, hz.1.2⟩
        rwa [hX'E'] at h3
      rw [hinf1, Subgroup.card_bot, mul_one, hX'c] at h2
      have hle : H₁ ⊔ X' ≤ H₂ := sup_le inf_le_left (le_inf hX'T fun x hx =>
        mem_centralizer_iff.2 fun e he => hc e he.2 x (hX'A' hx))
      rw [mul_comm]
      exact h2 ▸ Subgroup.card_le_of_le hle
    have h2 : Nat.card X * Nat.card H₂ ≤ Nat.card H₃ := by
      have hN : X ≤ normalizer (H₂ : Set G) := fun x hx =>
        (hTNE x (hXT hx) (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hXR₀ hx)).1).2
          (Subgroup.mem_inf.1 (hXR₀ hx)).2).2
      have h3 := card_sup_mul_card_inf_of_le_normalizer_sOne hN
      have hinf2 : H₂ ⊓ X = ⊥ := by
        rw [eq_bot_iff]
        intro z hz
        have h4 : z ∈ X ⊓ centralizer (E : Set G) := Subgroup.mem_inf.2 ⟨hz.2, hz.1.2⟩
        rwa [hXE] at h4
      rw [hinf2, Subgroup.card_bot, mul_one] at h3
      have hle : H₂ ⊔ X ≤ H₃ := sup_le (inf_le_inf_left T (centralizer_le_normalizer_of_le le_rfl))
        (le_inf hXT fun x hx => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (hXR₀ hx)).1).2)
      rw [mul_comm]
      exact h3 ▸ Subgroup.card_le_of_le hle
    have h3 : H₃ < T := by
      refine lt_of_le_of_ne inf_le_left fun h => htNE ?_
      have hm : t ∈ H₃ := h ▸ htT
      exact (Subgroup.mem_inf.1 hm).2
    have e3 := two_mul_card_le_of_lt h3
    have e0 := Subgroup.card_le_of_le h0
    calc 2 * Nat.card X ^ 2 * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G)
        ≤ 2 * Nat.card X ^ 2 * Nat.card H₁ := Nat.mul_le_mul_left _ e0
      _ = 2 * (Nat.card X * (Nat.card X * Nat.card H₁)) := by ring
      _ ≤ 2 * (Nat.card X * Nat.card H₂) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ ≤ 2 * Nat.card H₃ := Nat.mul_le_mul_left _ h2
      _ ≤ Nat.card T := e3
  obtain ⟨P, hP2, hPCT, hPcard⟩ := exists_isPGroup_sup_normalizer hT2 hTC (hS2.to_le hS₀S) hS₀C
  have hPR : P ≤ R := hPCT.trans (sup_le (hCR₀.trans le_sup_left) hTR)
  have hlt : Nat.card S < Nat.card P := by
    have hpos : 0 < Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) := Nat.card_pos
    have hS₀pos : 0 < Nat.card S₀ := Nat.card_pos
    have h1 : Nat.card S₀ * (2 * Nat.card X ^ 2 *
        Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G)) ≤
        Nat.card P * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) :=
      (Nat.mul_le_mul_left _ hchain).trans hPcard
    have h2 : (2 * Nat.card X ^ 2 * Nat.card S₀) *
        Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) ≤
        Nat.card P * Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) := by
      calc (2 * Nat.card X ^ 2 * Nat.card S₀) *
            Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G) =
          Nat.card S₀ * (2 * Nat.card X ^ 2 *
            Nat.card (centralizer (W₀ : Set G) ⊓ T : Subgroup G)) := by ring
        _ ≤ _ := h1
    have h8 := Nat.le_of_mul_le_mul_right h2 hpos
    have h9 : k * Nat.card S₀ < 2 * Nat.card X ^ 2 * Nat.card S₀ :=
      Nat.mul_lt_mul_of_pos_right hk hS₀pos
    omega
  obtain ⟨Q, hQ2, hSQ, hQR⟩ := exists_isPGroup_lt_of_card_lt hS2 hSR hP2 hPR hlt
  exact false_of_isPGroup_lt hW hWV ht hWS hSN htS htcomm hB hmax hQ2 hSQ
    (fun q hq r hr => (mem_normalizer_iff.1 (hRN (hQR hq)) r).1 hr) htR₀
    (fun s hs hsR hs2 => hkey s hs (fun h => hsR (hS₀FR₀ h)) hs2)

end CFSG.SeitzReduction.LinearPilot

module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieSL2
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.ComponentClassification.RankTwoOddLie

open Subgroup CFSG.Open CFSG.ComponentClassification.AS76b CFSG.ClassicalInvolution
open scoped MatrixGroups commutatorElement

variable {H : Type*} [Group H] {F : Type*} [Field F] {B T X : Subgroup H}

theorem exists_mul_of_mem_sup_of_le_centralizer {T C : Subgroup H}
    (hC : C ≤ centralizer (T : Set H)) {x : H} (hx : x ∈ T ⊔ C) : ∃ t ∈ T, ∃ c ∈ C, x = t * c := by
  have hTC : T ≤ normalizer (C : Set H) := fun t ht =>
    centralizer_le_normalizer _ ((Subgroup.le_centralizer_iff.mp hC) ht)
  have := coe_mul_of_left_le_normalizer_right T C hTC
  have hx' : x ∈ ((T ⊔ C : Subgroup H) : Set H) := hx
  rw [this] at hx'
  obtain ⟨t, ht, c, hc, rfl⟩ := hx'
  exact ⟨t, ht, c, hc, rfl⟩

theorem Hyp46.mem_of_twoGroup [Finite H] (h : Hyp46 B T X) {Q : Subgroup H} (hQB : Q ≤ T ⊔ B)
    (hQ2 : IsPGroup 2 Q) (hTQ : T ≤ normalizer (Q : Set H)) (hTQ1 : T ⊓ Q = ⊥)
    (hfaith : T ⊓ centralizer (Q : Set H) = ⊥) {z : H}
    (hz : ∀ x ∈ Q, x ^ 2 = 1 → x = 1 ∨ x = z) : z ∈ X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => h.elem.2 t ht
  set C : Subgroup H := Q ⊓ centralizer (T : Set H) with hCdef
  set K : Subgroup H := T ⊔ C with hKdef
  set S : Subgroup H := T ⊔ Q with hSdef
  have hCT : C ≤ centralizer (T : Set H) := inf_le_right
  have hKS : K ≤ S := sup_le_sup_left inf_le_left T
  have hKQ : ∀ x ∈ K, x ∈ Q → x ∈ C := by
    intro x hxK hxQ
    obtain ⟨t, ht, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hCT hxK
    have htQ : t ∈ Q := by
      have := Q.mul_mem hxQ (Q.inv_mem (Subgroup.mem_inf.mp hc).1)
      simpa using this
    have ht1 : t = 1 := by
      have : t ∈ T ⊓ Q := Subgroup.mem_inf.mpr ⟨ht, htQ⟩
      rw [hTQ1] at this
      exact Subgroup.mem_bot.mp this
    rw [ht1, one_mul]
    exact hc
  have hKne : ¬ S ≤ K := by
    intro hSK
    have hQC : Q ≤ centralizer (T : Set H) := fun q hq =>
      (Subgroup.mem_inf.mp (hKQ q (hSK (mem_sup_right hq)) hq)).2
    have hTC : T ≤ centralizer (Q : Set H) := Subgroup.le_centralizer_iff.mp hQC
    have hT1 : T = ⊥ := by rw [← hfaith]; exact (inf_eq_left.mpr hTC).symm
    have := h.four_le
    rw [hT1, Subgroup.card_bot] at this
    omega
  have hS2 : IsPGroup 2 S := IsPGroup.to_sup_of_normal_right' h.sylow.isPGroup hQ2 hTQ
  have : Group.IsNilpotent S := hS2.isNilpotent
  have hnc := (normalizerCondition_iff_only_full_group_self_normalizing.mp
    (Group.normalizerCondition_of_isNilpotent (G := S))) (K.subgroupOf S)
  obtain ⟨y, hyN, hyK⟩ : ∃ y ∈ normalizer ((K.subgroupOf S : Subgroup S) : Set S),
      y ∉ K.subgroupOf S := by
    by_contra hcon
    push Not at hcon
    apply hKne
    have htop := hnc (le_antisymm hcon Subgroup.le_normalizer)
    intro x hx
    have : (⟨x, hx⟩ : S) ∈ K.subgroupOf S := htop ▸ Subgroup.mem_top _
    exact mem_subgroupOf.mp this
  obtain ⟨t', ht', a, ha, hya⟩ : ∃ t' ∈ T, ∃ a ∈ Q, (y : H) = t' * a := by
    have := coe_mul_of_left_le_normalizer_right T Q hTQ
    have hy' : (y : H) ∈ ((T ⊔ Q : Subgroup H) : Set H) := y.2
    rw [this] at hy'
    obtain ⟨t', ht', a, ha, h'⟩ := hy'
    exact ⟨t', ht', a, ha, h'.symm⟩
  have hyNK : ∀ k ∈ K, (y : H) * k * (y : H)⁻¹ ∈ K := by
    intro k hk
    have := (mem_normalizer_iff.mp hyN ⟨k, hKS hk⟩).mp (mem_subgroupOf.mpr hk)
    simpa [mem_subgroupOf] using this
  have haT : ∀ t ∈ T, a * t * a⁻¹ ∈ K := by
    intro t ht
    have e1 : a * t * a⁻¹ = t'⁻¹ * ((y : H) * t * (y : H)⁻¹) * t' := by rw [hya]; group
    rw [e1]
    exact K.mul_mem (K.mul_mem (K.inv_mem (mem_sup_left ht')) (hyNK t (mem_sup_left ht)))
      (mem_sup_left ht')
  have haC : a ∉ C := by
    intro haC
    apply hyK
    rw [mem_subgroupOf, hya]
    exact K.mul_mem (mem_sup_left ht') (mem_sup_right haC)
  have hφC : ∀ t ∈ T, a * t * a⁻¹ * t⁻¹ ∈ C := by
    intro t ht
    refine hKQ _ (K.mul_mem (haT t ht) (K.inv_mem (mem_sup_left ht))) ?_
    have e1 : a * t * a⁻¹ * t⁻¹ = a * (t * a⁻¹ * t⁻¹) := by group
    rw [e1]
    exact Q.mul_mem ha ((mem_normalizer_iff.mp (hTQ ht) _).mp (Q.inv_mem ha))
  have hφmul : ∀ t₁ ∈ T, ∀ t₂ ∈ T, a * (t₁ * t₂) * a⁻¹ * (t₁ * t₂)⁻¹ =
      (a * t₁ * a⁻¹ * t₁⁻¹) * (a * t₂ * a⁻¹ * t₂⁻¹) := by
    intro t₁ ht₁ t₂ ht₂
    have hc2 : t₁ * (a * t₂ * a⁻¹ * t₂⁻¹) = (a * t₂ * a⁻¹ * t₂⁻¹) * t₁ :=
      (mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hφC t₂ ht₂)).2) t₁ ht₁
    calc a * (t₁ * t₂) * a⁻¹ * (t₁ * t₂)⁻¹
        = (a * t₁ * a⁻¹ * t₁⁻¹) * (t₁ * (a * t₂ * a⁻¹ * t₂⁻¹)) * t₁⁻¹ := by group
      _ = (a * t₁ * a⁻¹ * t₁⁻¹) * (a * t₂ * a⁻¹ * t₂⁻¹) := by rw [hc2]; group
  have hφsq : ∀ t ∈ T, (a * t * a⁻¹ * t⁻¹) ^ 2 = 1 := by
    intro t ht
    rw [sq, ← hφmul t ht t ht, ← sq, hT2 t ht]
    group
  have hφz : ∀ t ∈ T, a * t * a⁻¹ * t⁻¹ = 1 ∨ a * t * a⁻¹ * t⁻¹ = z := fun t ht =>
    hz _ (Subgroup.mem_inf.mp (hφC t ht)).1 (hφsq t ht)
  obtain ⟨s, hs, hsz⟩ : ∃ s ∈ T, a * s * a⁻¹ * s⁻¹ = z := by
    by_contra hcon
    push Not at hcon
    apply haC
    refine Subgroup.mem_inf.mpr ⟨ha, ?_⟩
    rw [mem_centralizer_iff]
    intro t ht
    have h1 : a * t * a⁻¹ * t⁻¹ = 1 := (hφz t ht).resolve_right (hcon t ht)
    calc t * a = (a * t * a⁻¹ * t⁻¹)⁻¹ * a * t := by group
      _ = a * t := by rw [h1]; group
  obtain ⟨t, ht, ht1, hat⟩ : ∃ t ∈ T, t ≠ 1 ∧ a * t * a⁻¹ * t⁻¹ = 1 := by
    obtain ⟨t₂, ht₂, ht₂1, ht₂s⟩ := h.exists_ne hs
    rcases hφz t₂ ht₂ with h1 | h1
    · exact ⟨t₂, ht₂, ht₂1, h1⟩
    · refine ⟨s * t₂, T.mul_mem hs ht₂, ?_, ?_⟩
      · intro h2
        apply ht₂s
        have h3 : t₂ = s⁻¹ := eq_inv_of_mul_eq_one_right h2
        rw [h3, inv_eq_of_mul_eq_one_left (by rw [← sq, hT2 s hs])]
      · rw [hφmul s hs t₂ ht₂, hsz, h1, ← sq, ← hsz]
        exact hφsq s hs
  have haN : a ∈ normalizer (X : Set H) := by
    refine h.inf_centralizer_le_of_mem ht ht1 (Subgroup.mem_inf.mpr ⟨hQB ha, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    calc a * t = (a * t * a⁻¹ * t⁻¹) * t * a := by group
      _ = t * a := by rw [hat]; group
  rw [← hsz]
  exact X.mul_mem ((mem_normalizer_iff.mp haN s).mp (h.le_X hs)) (X.inv_mem (h.le_X hs))

theorem Hyp46.false_of_centralInv_mem [Finite H] [Finite F] (h : Hyp46 B T X) (e : B ≃* SL(2, F))
    (hF : Odd (Nat.card F)) (hz : centralInv e ∈ X) : False := by
  have hBX : B ≤ normalizer (X : Set H) := fun b hb =>
    h.inf_centralizer_le hz (centralInv_ne_one e hF) 1 (by simpa using centralInv_sq e)
      (Subgroup.mem_inf.mpr ⟨mem_sup_right hb, by
        rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.mp (centralInv_mem_centralizer e)) b hb⟩)
  have hTC := h.le_centralizer_of_le_normalizer e hF h.le_normalizer hBX
  have hT1 : T = ⊥ := by rw [← h.faithful]; exact (inf_eq_left.mpr hTC).symm
  have := h.four_le
  rw [hT1, Subgroup.card_bot] at this
  omega

theorem Hyp46.centralInv_mem_of_le_sup [Finite H] [Finite F] (h : Hyp46 B T X) (e : B ≃* SL(2, F))
    (hF : Odd (Nat.card F)) (hinner : T ≤ B ⊔ centralizer (B : Set H)) : centralInv e ∈ X := by
  have hT2 : ∀ t ∈ T, t ^ 2 = 1 := fun t ht => h.elem.2 t ht
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBC : B ≤ normalizer (centralizer (B : Set H) : Set H) := fun b hb => by
    rw [mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro x hx
      have h1 := hc x hx
      have h2 := hc (b⁻¹ * x * b) (B.mul_mem (B.mul_mem (B.inv_mem hb) hx) hb)
      have h3 := hc b hb
      have h4 := hc b⁻¹ (B.inv_mem hb)
      calc x * (b * c * b⁻¹) = b * (b⁻¹ * x * b) * c * b⁻¹ := by group
        _ = b * c * (b⁻¹ * x * b) * b⁻¹ := by rw [mul_assoc b, h2, ← mul_assoc]
        _ = b * c * b⁻¹ * x := by group
    · intro hc
      rw [mem_centralizer_iff] at hc ⊢
      intro x hx
      have h2 := hc (b * x * b⁻¹) (B.mul_mem (B.mul_mem hb hx) (B.inv_mem hb))
      calc x * c = b⁻¹ * ((b * x * b⁻¹) * (b * c * b⁻¹)) * b := by group
        _ = b⁻¹ * ((b * c * b⁻¹) * (b * x * b⁻¹)) * b := by rw [h2]
        _ = c * x := by group
  have hdec : ∀ t ∈ T, ∃ b ∈ B, ∀ x ∈ B, t * x * t⁻¹ = b * x * b⁻¹ := by
    intro t ht
    have := coe_mul_of_left_le_normalizer_right B (centralizer (B : Set H)) hBC
    have ht' : t ∈ ((B ⊔ centralizer (B : Set H) : Subgroup H) : Set H) := hinner ht
    rw [this] at ht'
    obtain ⟨b, hb, c, hc, rfl⟩ := ht'
    refine ⟨b, hb, fun x hx => ?_⟩
    have hcx : x * c = c * x := (mem_centralizer_iff.mp hc) x hx
    calc b * c * x * (b * c)⁻¹ = b * (c * x) * c⁻¹ * b⁻¹ := by group
      _ = b * (x * c) * c⁻¹ * b⁻¹ := by rw [hcx]
      _ = b * x * b⁻¹ := by group
  set z := centralInv e
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ : ∃ t : T, t ≠ 1 := by
    have : Nontrivial T := Finite.one_lt_card_iff_nontrivial.mp (by linarith [h.four_le])
    exact _root_.exists_ne 1
  have ht₁1' : t₁ ≠ 1 := fun h1 => ht₁1 (Subtype.ext h1)
  obtain ⟨t₂, ht₂, ht₂1, ht₂₁⟩ := h.exists_ne ht₁
  obtain ⟨b₁, hb₁, hb₁t⟩ := hdec t₁ ht₁
  obtain ⟨b₂, hb₂, hb₂t⟩ := hdec t₂ ht₂
  have hnc : ∀ t ∈ T, t ≠ 1 → ∀ b ∈ B, (∀ x ∈ B, t * x * t⁻¹ = b * x * b⁻¹) →
      b ∉ centralizer (B : Set H) := by
    intro t ht ht1 b hb hbt hbC
    have htC : t ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := hbt x hx
      have h2 : b * x * b⁻¹ = x := by
        rw [← (mem_centralizer_iff.mp hbC) x hx]; group
      calc x * t = t * x * t⁻¹ * t := by rw [h1, h2]
        _ = t * x := by group
    apply ht1
    have : t ∈ T ⊓ centralizer (B : Set H) := Subgroup.mem_inf.mpr ⟨ht, htC⟩
    rw [h.faithful] at this
    exact Subgroup.mem_bot.mp this
  have hsqz : ∀ t ∈ T, t ≠ 1 → ∀ b ∈ B, (∀ x ∈ B, t * x * t⁻¹ = b * x * b⁻¹) → b ^ 2 = z := by
    intro t ht ht1 b hb hbt
    have hb2C : b ^ 2 ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      intro x hx
      have h1 : t * (t * x * t⁻¹) * t⁻¹ = x := by
        calc t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t * t)⁻¹ := by group
          _ = x := by rw [← sq, hT2 t ht]; group
      rw [hbt _ ((mem_normalizer_iff.mp (h.le_normalizer ht) x).mp hx), hbt x hx] at h1
      rw [sq]
      calc x * (b * b) = (b * (b * x * b⁻¹) * b⁻¹) * (b * b) := by rw [h1]
        _ = b * b * x := by group
    rcases eq_one_or_centralInv_of_mem_centralizer e (pow_mem hb 2) hb2C with h1 | h1
    · exfalso
      rcases eq_one_or_centralInv_of_sq e hF hb h1 with h2 | h2
      · exact hnc t ht ht1 b hb hbt (h2 ▸ one_mem _)
      · exact hnc t ht ht1 b hb hbt (h2 ▸ centralInv_mem_centralizer e)
    · exact h1
  have hb₁2 := hsqz t₁ ht₁ ht₁1' b₁ hb₁ hb₁t
  have hb₂2 := hsqz t₂ ht₂ ht₂1 b₂ hb₂ hb₂t
  have hcommC : ⁅b₁, b₂⁆ ∈ centralizer (B : Set H) := by
    have key : ∀ y ∈ B, b₁ * (b₂ * y * b₂⁻¹) * b₁⁻¹ = b₂ * (b₁ * y * b₁⁻¹) * b₂⁻¹ := by
      intro y hy
      have hc := hTc t₁ ht₁ t₂ ht₂
      have hy₁ : t₁ * (t₂ * y * t₂⁻¹) * t₁⁻¹ = t₂ * (t₁ * y * t₁⁻¹) * t₂⁻¹ := by
        calc t₁ * (t₂ * y * t₂⁻¹) * t₁⁻¹ = (t₁ * t₂) * y * (t₁ * t₂)⁻¹ := by group
          _ = (t₂ * t₁) * y * (t₂ * t₁)⁻¹ := by rw [hc]
          _ = t₂ * (t₁ * y * t₁⁻¹) * t₂⁻¹ := by group
      have hyB₂ : t₂ * y * t₂⁻¹ ∈ B := (mem_normalizer_iff.mp (h.le_normalizer ht₂) y).mp hy
      have hyB₁ : t₁ * y * t₁⁻¹ ∈ B := (mem_normalizer_iff.mp (h.le_normalizer ht₁) y).mp hy
      rwa [hb₁t _ hyB₂, hb₂t y hy, hb₂t _ hyB₁, hb₁t y hy] at hy₁
    rw [mem_centralizer_iff]
    intro x hx
    have hy : b₁⁻¹ * b₂⁻¹ * x * b₂ * b₁ ∈ B :=
      B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem (B.inv_mem hb₁) (B.inv_mem hb₂)) hx) hb₂) hb₁
    have h1 := key _ hy
    have h2 : b₂ * (b₁ * (b₁⁻¹ * b₂⁻¹ * x * b₂ * b₁) * b₁⁻¹) * b₂⁻¹ = x := by group
    rw [h2] at h1
    rw [commutatorElement_def]
    calc x * (b₁ * b₂ * b₁⁻¹ * b₂⁻¹)
        = (b₁ * (b₂ * (b₁⁻¹ * b₂⁻¹ * x * b₂ * b₁) * b₂⁻¹) * b₁⁻¹) *
            (b₁ * b₂ * b₁⁻¹ * b₂⁻¹) := by rw [h1]
      _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ * x := by group
  have hcomm : ⁅b₁, b₂⁆ = z := by
    rcases eq_one_or_centralInv_of_mem_centralizer e
        (by rw [commutatorElement_def]; exact B.mul_mem (B.mul_mem (B.mul_mem hb₁ hb₂)
          (B.inv_mem hb₁)) (B.inv_mem hb₂)) hcommC with h1 | h1
    · exfalso
      have hcm : b₁ * b₂ = b₂ * b₁ := commutatorElement_eq_one_iff_mul_comm.mp h1
      have hsq : (b₁ * b₂) ^ 2 = 1 := by
        rw [(Commute.mul_pow hcm 2), hb₁2, hb₂2, ← sq, centralInv_sq]
      have ht12 : t₁ * t₂ ≠ 1 := by
        intro h2
        apply ht₂₁
        have h3 : t₂ = t₁⁻¹ := eq_inv_of_mul_eq_one_right h2
        rw [h3, inv_eq_of_mul_eq_one_left (by rw [← sq, hT2 t₁ ht₁])]
      refine hnc (t₁ * t₂) (T.mul_mem ht₁ ht₂) ht12 (b₁ * b₂) (B.mul_mem hb₁ hb₂) ?_ ?_
      · intro x hx
        have hxB₂ : t₂ * x * t₂⁻¹ ∈ B := (mem_normalizer_iff.mp (h.le_normalizer ht₂) x).mp hx
        calc t₁ * t₂ * x * (t₁ * t₂)⁻¹ = t₁ * (t₂ * x * t₂⁻¹) * t₁⁻¹ := by group
          _ = b₁ * (b₂ * x * b₂⁻¹) * b₁⁻¹ := by rw [hb₁t _ hxB₂, hb₂t x hx]
          _ = b₁ * b₂ * x * (b₁ * b₂)⁻¹ := by group
      · rcases eq_one_or_centralInv_of_sq e hF (B.mul_mem hb₁ hb₂) hsq with h2 | h2
        · rw [h2]; exact one_mem _
        · rw [h2]; exact centralInv_mem_centralizer e
    · exact h1
  have hb₂N : b₂ ∈ normalizer (X : Set H) := by
    refine h.inf_centralizer_le_of_mem ht₂ ht₂1 (Subgroup.mem_inf.mpr ⟨mem_sup_right hb₂, ?_⟩)
    rw [mem_centralizer_singleton_iff]
    have := hb₂t b₂ hb₂
    calc b₂ * t₂ = t₂ * b₂ * t₂⁻¹ * t₂ := by rw [this]; group
      _ = t₂ * b₂ := by group
  have hkey : t₁ * b₂ * t₁⁻¹ * b₂⁻¹ = z := by
    rw [hb₁t b₂ hb₂, ← hcomm, commutatorElement_def]
  rw [← hkey]
  have e1 : t₁ * b₂ * t₁⁻¹ * b₂⁻¹ = t₁ * (b₂ * t₁⁻¹ * b₂⁻¹) := by group
  rw [e1]
  exact X.mul_mem (h.le_X ht₁) ((mem_normalizer_iff.mp hb₂N _).mp (X.inv_mem (h.le_X ht₁)))

private theorem sl2Three_centralizer_Q_aux :
    ∀ x : SL(2, ZMod 3), (∀ y : SL(2, ZMod 3), y ^ 4 = 1 → x * y = y * x) → x = 1 ∨ x = -1 := by
  decide +kernel

noncomputable def sl2EquivThree [Finite F] (h3 : Nat.card F = 3) : SL(2, F) ≃* SL(2, ZMod 3) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  exact sl2RingEquiv (FiniteField.ringEquivOfCardEq
    (by rw [← Nat.card_eq_fintype_card, h3, ZMod.card]))

def quatSub (J : Subgroup H) (e : J ≃* SL(2, ZMod 3)) : Subgroup H where
  carrier := {x | x ∈ J ∧ x ^ 4 = 1}
  one_mem' := ⟨J.one_mem, one_pow 4⟩
  mul_mem' := by
    rintro x y ⟨hx, hx4⟩ ⟨hy, hy4⟩
    refine ⟨J.mul_mem hx hy, ?_⟩
    have h1 : e ⟨x, hx⟩ ∈ sl2ThreeQ := by
      rw [mem_sl2ThreeQ_iff, ← map_pow, show (⟨x, hx⟩ : J) ^ 4 = 1 from Subtype.ext hx4, map_one]
    have h2 : e ⟨y, hy⟩ ∈ sl2ThreeQ := by
      rw [mem_sl2ThreeQ_iff, ← map_pow, show (⟨y, hy⟩ : J) ^ 4 = 1 from Subtype.ext hy4, map_one]
    have h3 := sl2ThreeQ.mul_mem h1 h2
    rw [mem_sl2ThreeQ_iff, ← map_mul, ← map_pow, map_eq_one_iff _ e.injective] at h3
    simpa using congrArg Subtype.val h3
  inv_mem' := by
    rintro x ⟨hx, hx4⟩
    exact ⟨J.inv_mem hx, by rw [inv_pow, hx4, inv_one]⟩

theorem Hyp46.false_of_sl2_three [Finite H] [Finite F] (h : Hyp46 B T X) (e : B ≃* SL(2, F))
    (h3 : Nat.card F = 3) : False := by
  have hF : Odd (Nat.card F) := by rw [h3]; decide
  by_cases hzT : centralInv e ∈ T
  · exact h.false_of_centralInv_mem e hF (h.le_X hzT)
  set e3 : B ≃* SL(2, ZMod 3) := e.trans (sl2EquivThree h3)
  set Q := quatSub B e3
  have hQB : Q ≤ B := fun x hx => hx.1
  have hBQ : ∀ b ∈ B, ∀ y ∈ Q, b * y * b⁻¹ ∈ Q := fun b hb y hy =>
    ⟨B.mul_mem (B.mul_mem hb hy.1) (B.inv_mem hb), by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩
  have hTQ : T ≤ normalizer (Q : Set H) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact ⟨(mem_normalizer_iff.mp (h.le_normalizer ht) y).mp hy.1,
        by rw [conj_pow, hy.2, mul_one, mul_inv_cancel]⟩
    · intro hy
      refine ⟨(mem_normalizer_iff.mp (h.le_normalizer ht) y).mpr hy.1, ?_⟩
      have h1 := hy.2
      rw [conj_pow] at h1
      calc y ^ 4 = t⁻¹ * (t * y ^ 4 * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
  have hQ2 : IsPGroup 2 Q := fun g => ⟨2, Subtype.ext (by simpa using g.2.2)⟩
  have hTQ1 : T ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htQ⟩ := Subgroup.mem_inf.mp ht
    rcases eq_one_or_centralInv_of_sq e hF htQ.1 (h.elem.2 t htT) with h1 | h1
    · exact Subgroup.mem_bot.mpr h1
    · exact absurd (h1 ▸ htT) hzT
  have hfaith : T ⊓ centralizer (Q : Set H) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨htT, htQ⟩ := Subgroup.mem_inf.mp ht
    have htB : t ∈ centralizer (B : Set H) := by
      refine mem_centralizer_of_commutator_mem e hF (h.le_normalizer htT) fun x hx => ?_
      set c := t * x * t⁻¹ * x⁻¹ with hcdef
      have hcB : c ∈ B := B.mul_mem ((mem_normalizer_iff.mp (h.le_normalizer htT) x).mp hx)
        (B.inv_mem hx)
      have hcQ : ∀ y ∈ Q, c * y = y * c := by
        intro y hy
        have hy' : x⁻¹ * y * x ∈ Q := by
          have := hBQ x⁻¹ (B.inv_mem hx) y hy
          simpa using this
        have h1 : t * y = y * t := ((mem_centralizer_iff.mp htQ) y hy).symm
        have h2 : t * (x⁻¹ * y * x) = (x⁻¹ * y * x) * t :=
          ((mem_centralizer_iff.mp htQ) _ hy').symm
        calc c * y = t * x * t⁻¹ * (x⁻¹ * y * x) * x⁻¹ := by rw [hcdef]; group
          _ = t * x * (t⁻¹ * ((x⁻¹ * y * x) * t)) * t⁻¹ * x⁻¹ := by group
          _ = t * x * (t⁻¹ * (t * (x⁻¹ * y * x))) * t⁻¹ * x⁻¹ := by rw [h2]
          _ = t * y * t⁻¹ * (t * x * t⁻¹ * x⁻¹) := by group
          _ = y * t * t⁻¹ * (t * x * t⁻¹ * x⁻¹) := by rw [h1]
          _ = y * c := by rw [hcdef]; group
      have hz : e3 ⟨c, hcB⟩ = 1 ∨ e3 ⟨c, hcB⟩ = -1 := by
        apply sl2Three_centralizer_Q_aux
        intro y' hy'
        set y := e3.symm y'
        have hyQ : (y : H) ∈ Q := ⟨y.2, by
          have : y ^ 4 = 1 := by rw [← map_pow, hy', map_one]
          simpa using congrArg Subtype.val this⟩
        have h1 : (⟨c, hcB⟩ : B) * y = y * ⟨c, hcB⟩ := Subtype.ext (hcQ _ hyQ)
        have h2 := congrArg e3 h1
        simpa [y] using h2
      have hcz : (⟨c, hcB⟩ : B) ∈ center B := by
        rw [mem_center_iff_of_equiv_sl2 e3, mem_center_sl2_iff]
        exact hz
      rw [mem_centralizer_iff]
      intro g hg
      rw [Subgroup.mem_center_iff] at hcz
      exact congrArg Subtype.val (hcz ⟨g, hg⟩)
    have : t ∈ T ⊓ centralizer (B : Set H) := Subgroup.mem_inf.mpr ⟨htT, htB⟩
    rwa [h.faithful] at this
  have hz : ∀ x ∈ Q, x ^ 2 = 1 → x = 1 ∨ x = centralInv e := fun x hx hx2 =>
    eq_one_or_centralInv_of_sq e hF hx.1 hx2
  exact h.false_of_centralInv_mem e hF
    (h.mem_of_twoGroup (hQB.trans le_sup_right) hQ2 hTQ hTQ1 hfaith hz)

end CFSG.ComponentClassification.RankTwoOddLie

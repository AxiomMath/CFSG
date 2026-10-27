module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] {L K₀ : Subgroup H}

theorem conj_mem_sup_of_normalizer (hK₀C : K₀ ≤ centralizer (L : Set H))
    (hinv : ∀ g ∈ normalizer (L : Set H), ∀ x ∈ K₀, g * x * g⁻¹ ∈ K₀) {g : H}
    (hg : g ∈ normalizer (L : Set H)) {w : H} (hw : w ∈ L ⊔ K₀) : g * w * g⁻¹ ∈ L ⊔ K₀ := by
  obtain ⟨ℓ, hℓ, k, hk, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hK₀C hw
  have e : g * (ℓ * k) * g⁻¹ = (g * ℓ * g⁻¹) * (g * k * g⁻¹) := by group
  rw [e]
  exact mul_mem_sup ((mem_normalizer_iff.1 hg ℓ).1 hℓ) (hinv g hg k hk)

theorem comm_mem_sup_of_inner (hK₀C : K₀ ≤ centralizer (L : Set H))
    (hmul : ∀ x ∈ centralizer (L : Set H), ∀ y ∈ centralizer (L : Set H),
      x * y ∈ K₀ ↔ (x ∈ K₀ ↔ y ∈ K₀))
    (hinv : ∀ g ∈ normalizer (L : Set H), ∀ x ∈ K₀, g * x * g⁻¹ ∈ K₀) {a b : H}
    (ha : a ∈ L ⊔ centralizer (L : Set H)) (hb : b ∈ normalizer (L : Set H)) :
    a * b * a⁻¹ * b⁻¹ ∈ L ⊔ K₀ := by
  obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer le_rfl ha
  have hbc : b * c⁻¹ * b⁻¹ ∈ centralizer (L : Set H) :=
    conj_mem_centralizer hb ((centralizer (L : Set H)).inv_mem hc)
  have hk : c * (b * c⁻¹ * b⁻¹) ∈ K₀ := by
    refine (hmul c hc _ hbc).2 ?_
    constructor
    · intro hcK
      have := hinv b hb c⁻¹ (K₀.inv_mem hcK)
      exact this
    · intro h
      have h1 := hinv b⁻¹ (inv_mem hb) _ h
      have e : b⁻¹ * (b * c⁻¹ * b⁻¹) * b⁻¹⁻¹ = c⁻¹ := by group
      rw [e] at h1
      simpa using K₀.inv_mem h1
  have hℓ'' : b * ℓ⁻¹ * b⁻¹ ∈ L := (mem_normalizer_iff.1 hb ℓ⁻¹).1 (L.inv_mem hℓ)
  have hcomm : (b * ℓ⁻¹ * b⁻¹) * (c * (b * c⁻¹ * b⁻¹)) =
      (c * (b * c⁻¹ * b⁻¹)) * (b * ℓ⁻¹ * b⁻¹) :=
    mem_centralizer_iff.1 (hK₀C hk) _ hℓ''
  have e : ℓ * c * b * (ℓ * c)⁻¹ * b⁻¹ =
      (ℓ * (b * ℓ⁻¹ * b⁻¹)) * (c * (b * c⁻¹ * b⁻¹)) := by
    calc ℓ * c * b * (ℓ * c)⁻¹ * b⁻¹ = ℓ * (c * (b * c⁻¹ * b⁻¹)) * (b * ℓ⁻¹ * b⁻¹) := by group
      _ = ℓ * ((c * (b * c⁻¹ * b⁻¹)) * (b * ℓ⁻¹ * b⁻¹)) := by group
      _ = ℓ * ((b * ℓ⁻¹ * b⁻¹) * (c * (b * c⁻¹ * b⁻¹))) := by rw [hcomm]
      _ = (ℓ * (b * ℓ⁻¹ * b⁻¹)) * (c * (b * c⁻¹ * b⁻¹)) := by group
  rw [e]
  exact mul_mem_sup (L.mul_mem hℓ hℓ'') hk

theorem comm_mem_sup (hL : commutator ↥L = ⊤) (hout : OutTwo (↥L ⧸ center ↥L))
    (hK₀C : K₀ ≤ centralizer (L : Set H))
    (hmul : ∀ x ∈ centralizer (L : Set H), ∀ y ∈ centralizer (L : Set H),
      x * y ∈ K₀ ↔ (x ∈ K₀ ↔ y ∈ K₀))
    (hinv : ∀ g ∈ normalizer (L : Set H), ∀ x ∈ K₀, g * x * g⁻¹ ∈ K₀) {a b : H}
    (ha : a ∈ normalizer (L : Set H)) (hb : b ∈ normalizer (L : Set H)) :
    a * b * a⁻¹ * b⁻¹ ∈ L ⊔ K₀ := by
  have hiff : ∀ (g : H) (hg : g ∈ normalizer (L : Set H)),
      (∃ l : ↥L ⧸ center ↥L, normalizerAction L ⟨g, hg⟩ = MulAut.conj l) ↔
        g ∈ L ⊔ centralizer (L : Set H) := fun g hg => by
    rw [← normalizerAction_mem_range_conj_iff hL ⟨g, hg⟩]
    constructor
    · rintro ⟨l, hl⟩
      exact ⟨l, hl.symm⟩
    · rintro ⟨l, hl⟩
      exact ⟨l, hl.symm⟩
  rcases hout (normalizerAction L ⟨a, ha⟩) (normalizerAction L ⟨b, hb⟩) with h | h | h
  · exact comm_mem_sup_of_inner hK₀C hmul hinv ((hiff a ha).1 h) hb
  · have h1 := comm_mem_sup_of_inner hK₀C hmul hinv ((hiff b hb).1 h) ha
    have e : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem h1
  · obtain ⟨l, hl⟩ := h
    have hab : a⁻¹ * b ∈ normalizer (L : Set H) := mul_mem (inv_mem ha) hb
    have h3 : normalizerAction L ⟨a⁻¹ * b, hab⟩ = MulAut.conj l := by
      rw [← hl]
      have : (⟨a⁻¹ * b, hab⟩ : normalizer (L : Set H)) =
          (⟨a, ha⟩ : normalizer (L : Set H))⁻¹ * ⟨b, hb⟩ := Subtype.ext rfl
      rw [this, map_mul, map_inv]
    have h4 := comm_mem_sup_of_inner hK₀C hmul hinv ((hiff _ hab).1 ⟨l, h3⟩) ha
    have h5 : a * ((a⁻¹ * b) * a * (a⁻¹ * b)⁻¹ * a⁻¹) * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
    have h6 := conj_mem_sup_of_normalizer hK₀C hinv ha h4
    rw [h5] at h6
    exact (inv_mem_iff).1 h6

end CFSG.EvenSporadicStandard.Induction.Closing

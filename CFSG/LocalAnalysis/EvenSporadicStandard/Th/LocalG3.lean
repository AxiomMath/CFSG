module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalData3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalG2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5Aa
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.W5AaFacts

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup

variable {G : Type} [Group G]

theorem ThLocalWitness.toLocalIn_top {S A B : Subgroup G} {z : G} (W : ThLocalWitness S A B z) :
    ThLocalIn ⊤ S A B z where
  S_le := le_top
  B_le := le_top
  pgroup := W.pgroup
  maximal := fun Y _ hY hle => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heq := (W.pgroup.toSylow W.index_odd).is_maximal' hY hle
    intro y hy
    rw [heq] at hy
    exact hy
  z_sq := W.z_sq
  z_ne_one := W.z_ne_one
  z_mem := W.z_mem
  center_le := W.center_le
  mem_A_iff := W.mem_A_iff
  A_comm := W.A_comm
  A_sq := W.A_sq
  A_card := W.A_card
  z_mem_A := W.z_mem_A
  mem_B_iff := fun x _ => W.mem_B_iff x
  B_card := W.B_card
  trans := fun a ha h => by
    obtain ⟨n, hn, hz⟩ := W.trans a ha h
    exact ⟨n, trivial, hn, hz⟩
  surj := fun f h1 h2 h3 => by
    obtain ⟨n, hn⟩ := W.surj f h1 h2 h3
    exact ⟨n, trivial, hn⟩

section Comm

variable [Finite G] {L S A B Aa : Subgroup G} {z b : G}

theorem ThLocalIn2.comm_mem_Aa (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) {β t : G}
    (hβ : β ∈ B) (ht : t ∈ S) : β * t * β⁻¹ * t⁻¹ ∈ Aa := by
  have hAa : ∀ s ∈ S, ∀ x ∈ Aa, s * x * s⁻¹ ∈ Aa := fun s hs =>
    W2.conj_mem_of_conj_B (W.conj_mem_B_of_normalizes_S (mem_iff_conj_of_mem hs))
  have hB : ∀ s ∈ S, ∀ y ∈ B, s * y * s⁻¹ ∈ B := fun s hs =>
    W.conj_mem_B_of_normalizes_S (mem_iff_conj_of_mem hs)
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact W2.b_sq)
  rcases W2.mem_Aa_or_mul_b W hβ with h | h
  · have := Aa.mul_mem h (hAa t ht _ (Aa.inv_mem h))
    simpa [mul_assoc] using this
  · set c := β * b with hc
    have hβ' : β = c * b := by rw [hc, mul_assoc, ← pow_two, W2.b_sq, mul_one]
    set d := t * b * t⁻¹ with hd
    have hdB : d ∈ B := hB t ht b W2.b_mem
    have hdb : d * b ∈ Aa := by
      rcases W2.mem_Aa_or_mul_b W hdB with h1 | h1
      · exfalso
        have h2 := hAa t⁻¹ (S.inv_mem ht) d h1
        apply W2.b_not_mem
        have e : t⁻¹ * d * t⁻¹⁻¹ = b := by simp only [hd]; group
        rwa [e] at h2
      · exact h1
    have e : β * t * β⁻¹ * t⁻¹ = c * (d * b)⁻¹ * (t * c⁻¹ * t⁻¹) := by
      rw [hβ']
      simp only [hd, mul_inv_rev, hbinv]
      group
    rw [e]
    exact Aa.mul_mem (Aa.mul_mem h (Aa.inv_mem hdb)) (hAa t ht _ (Aa.inv_mem h))

end Comm

structure ThLocalIn3 (L S A B Aa : Subgroup G) : Prop where
  transv : ∀ g ∈ L, (∀ a ∈ A, g * a * g⁻¹ ∈ A) → g ∉ B →
    (∃ H : Subgroup G, H ≤ A ∧ Nat.card H = 8 ∧ ∀ a ∈ H, g * a = a * g) →
    ∀ K : Subgroup G, K ≤ Aa → (∀ x ∈ K, g * x = x * g) → Nat.card K ≤ 16
  center_quotient : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B

theorem ThLocalWitness3.toLocalIn3 {L : Subgroup G} {S₀ A₀ B₀ Aa₀ : Subgroup ↥L}
    (W : ThLocalWitness3 S₀ A₀ B₀ Aa₀) :
    ThLocalIn3 L (S₀.map L.subtype) (A₀.map L.subtype) (B₀.map L.subtype)
      (Aa₀.map L.subtype) := by
  have hmem : ∀ K : Subgroup ↥L, ∀ x : G, x ∈ K.map L.subtype ↔ ∃ h : x ∈ L, (⟨x, h⟩ : L) ∈ K :=
    fun K x => by
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.2, hy⟩
      · rintro ⟨h, hx⟩
        exact ⟨⟨x, h⟩, hx, rfl⟩
  have hle : ∀ K : Subgroup G, K ≤ L → (K.comap L.subtype).map L.subtype = K := fun K hK => by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hK hx⟩, hx, rfl⟩
  have hcardeq : ∀ K : Subgroup G, K ≤ L →
      Nat.card (K.comap L.subtype) = Nat.card K := fun K hK => by
    have e1 : Nat.card ((K.comap L.subtype).map L.subtype) = Nat.card (K.comap L.subtype) :=
      Subgroup.card_map_of_injective L.subtype_injective
    rw [hle K hK] at e1
    exact e1.symm
  refine ⟨fun g hgL hgA hgB hH K hKAa hKc => ?_, fun s hs hsc => ?_⟩
  · obtain ⟨H, hHA, hHc, hHg⟩ := hH
    have hHL : H ≤ L := fun x hx => by
      obtain ⟨h, _⟩ := (hmem A₀ x).1 (hHA hx)
      exact h
    have hKL : K ≤ L := fun x hx => by
      obtain ⟨h, _⟩ := (hmem Aa₀ x).1 (hKAa hx)
      exact h
    set g' : ↥L := ⟨g, hgL⟩ with hg'
    have h1 : ∀ a ∈ A₀, g' * a * g'⁻¹ ∈ A₀ := fun a ha => by
      have := hgA (a : G) ((hmem A₀ _).2 ⟨a.2, by simpa using ha⟩)
      obtain ⟨h, h2⟩ := (hmem A₀ _).1 this
      have e : g' * a * g'⁻¹ = (⟨g * (a : G) * g⁻¹, h⟩ : ↥L) := Subtype.ext (by simp [hg'])
      rw [e]
      exact h2
    have h2 : g' ∉ B₀ := fun h => hgB ((hmem B₀ _).2 ⟨hgL, h⟩)
    have h3 : ∃ H' : Subgroup ↥L, H' ≤ A₀ ∧ Nat.card H' = 8 ∧ ∀ a ∈ H', g' * a = a * g' := by
      refine ⟨H.comap L.subtype, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨h, h2⟩ := (hmem A₀ _).1 (hHA hx)
        simpa using h2
      · rw [hcardeq H hHL]
        exact hHc
      · intro a ha
        exact Subtype.ext (hHg _ ha)
    have h4 := W.transv g' h1 h2 h3 (K.comap L.subtype)
      (fun x hx => by
        obtain ⟨h, h2⟩ := (hmem Aa₀ _).1 (hKAa hx)
        simpa using h2)
      (fun x hx => Subtype.ext (hKc _ hx))
    rw [← hcardeq K hKL]
    exact h4
  · obtain ⟨hsL, hs0⟩ := (hmem S₀ s).1 hs
    have := W.center_quotient ⟨s, hsL⟩ hs0 (fun x hx => by
      have h1 := hsc (x : G) ((hmem S₀ _).2 ⟨x.2, by simpa using hx⟩)
      obtain ⟨h, h2⟩ := (hmem Aa₀ _).1 h1
      have e : (⟨s, hsL⟩ : ↥L) * x * (⟨s, hsL⟩ : ↥L)⁻¹ * x⁻¹ =
          ⟨s * (x : G) * s⁻¹ * (x : G)⁻¹, h⟩ := Subtype.ext (by simp)
      rw [e]
      exact h2)
    exact (hmem B₀ s).2 ⟨hsL, this⟩

theorem ThLocalData3.exists_localIn3 {L : Subgroup G} (h : ThLocalData3 ↥L) :
    ∃ (S A B : Subgroup G) (z : G) (Aa : Subgroup G) (b : G),
      ThLocalIn L S A B z ∧ ThLocalIn2 B A Aa b ∧ ThLocalIn3 L S A B Aa := by
  obtain ⟨S₀, A₀, B₀, z₀, Aa₀, b₀, W, W2, W3⟩ := h
  exact ⟨_, _, _, _, _, _, W.toLocalIn, W2.toLocalIn2, W3.toLocalIn3⟩

end CFSG.EvenSporadicStandard.ThStd

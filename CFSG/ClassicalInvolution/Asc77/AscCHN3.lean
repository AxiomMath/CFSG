module

public import CFSG.ClassicalInvolution.Asc77.AscCHN2
public import CFSG.ClassicalInvolution.Asc77.AscT7Z13
public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace CHN

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' : Subgroup G} {z : G}


theorem le_normalizer_of_perfect_centralizer (hs : Hyp23Setting p f Ω K K' z) {L : Subgroup G}
    (hLz : L ≤ Subgroup.centralizer ({z} : Set G)) (hL : L ≤ ⁅L, L⁆) :
    L ≤ Subgroup.normalizer (K : Set G) ∧ L ≤ Subgroup.normalizer (K' : Set G) := by
  classical
  have hst := hs.stand
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hdich : ∀ ℓ ∈ L, (conjSub ℓ K = K ∧ conjSub ℓ K' = K') ∨
      (conjSub ℓ K = K' ∧ conjSub ℓ K' = K) := by
    intro ℓ hℓ
    have hℓz : ℓ * z * ℓ⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLz hℓ)
      calc ℓ * z * ℓ⁻¹ = z * ℓ * ℓ⁻¹ := by rw [this]
        _ = z := by group
    have h1 : conjSub ℓ K ∈ twinSet Ω K :=
      ⟨hst.hyp.conjInvariant ℓ K hKΩ, z, hs.hz, hℓz ▸ hs.hz.conj ℓ⟩
    have h2 : conjSub ℓ K' ∈ twinSet Ω K :=
      ⟨hst.hyp.conjInvariant ℓ K' hK'Ω, z, hs.hz, hℓz ▸ hzK'.conj ℓ⟩
    rw [hs.twinSet_eq] at h1 h2
    have hne : conjSub ℓ K ≠ conjSub ℓ K' := fun h => hs.hne (conjSub_injective ℓ h).symm
    rcases Set.mem_insert_iff.mp h1 with h1 | h1 <;> rcases Set.mem_insert_iff.mp h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, Set.mem_singleton_iff.mp h2⟩
    · exact Or.inr ⟨Set.mem_singleton_iff.mp h1, h2⟩
    · exact absurd ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm) hne
  have hfix : ∀ w ∈ L, conjSub w K = K ∧ conjSub w K' = K' :=
    T7Z.fix_of_perfect_two (fun w S => conjSub w S) (fun x y S => conjSub_mul x y S)
      (fun S => conjSub_one S) hL hdich
  have hnorm : ∀ (S : Subgroup G), (∀ w ∈ L, conjSub w S = S) →
      L ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := conj_mem_conjSub (n := w) hh
      rwa [hS w hw] at this
    · intro hh
      have hh' : w * h * w⁻¹ ∈ conjSub w S := by rwa [hS w hw]
      rw [mem_conjSub_iff] at hh'
      have e1 : w⁻¹ * (w * h * w⁻¹) * w = h := by group
      rwa [e1] at hh'
  exact ⟨hnorm K fun w hw => (hfix w hw).1, hnorm K' fun w hw => (hfix w hw).2⟩

theorem commutes_of_perfect_centralizer_e (hs : Hyp23Setting p f Ω K K' z) (hex : ExactMembers Ω)
    {L : Subgroup G} (hLz : L ≤ Subgroup.centralizer ({z} : Set G)) (hL : L ≤ ⁅L, L⁆) {e : G}
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (hLe : ∀ ℓ ∈ L, ℓ * e = e * ℓ)
    (hC : ∀ k ∈ K, ∀ k' ∈ K, e * k * e⁻¹ = k → e * k' * e⁻¹ = k' → k * k' = k' * k) :
    ∀ x ∈ K, ∀ y ∈ L, x * y = y * x := by
  have hst := hs.stand
  have hq : 5 ≤ p ^ f := hst.five
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    omega
  obtain ⟨zK, hzK⟩ := hst.hyp.classical K hst.mem
  obtain ⟨eK⟩ := hzK.nonempty_equiv_sl2 (hex K hst.mem)
  exact commutes_of_perfect_of_abelian_centralizer h4 ⟨eK⟩ hL
    (le_normalizer_of_perfect_centralizer hs hLz hL).1 heK hLe hC

end CHN

end CFSG.ClassicalInvolution.Asc77

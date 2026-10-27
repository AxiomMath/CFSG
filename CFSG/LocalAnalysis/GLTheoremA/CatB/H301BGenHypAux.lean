module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenXs
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

private theorem eq_of_hyperplane_le_of_mem {p : ℕ} (hp : p.Prime) {H K B : Subgroup G}
    (hHK : H ≤ K) (hKB : K ≤ B) (hHc : Nat.card H * p = Nat.card B) {b : G} (hbK : b ∈ K)
    (hbH : b ∉ H) : K = B := by
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hHK
  obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hKB
  have hpmn : p = m * n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := H))
    rw [hHc, hn, hm, mul_assoc]
  have hm1 : m ≠ 1 := by
    rintro rfl
    apply hbH
    rw [Subgroup.eq_of_le_of_card_ge hHK (by rw [hm, mul_one])]
    exact hbK
  have hn1 : n = 1 := by
    rcases Nat.prime_mul_iff.1 (by rw [← hpmn]; exact hp) with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact absurd h hm1
  exact Subgroup.eq_of_le_of_card_ge hKB (by rw [hn, hn1, mul_one])

theorem mem_centralizer_of_hyperplane {p : ℕ} (hp : p.Prime) {H B : Subgroup G}
    (hHB : H ≤ B) (hHc : Nat.card H * p = Nat.card B) {b x : G} (hbB : b ∈ B) (hbH : b ∉ H)
    (hxH : x ∈ Subgroup.centralizer (H : Set G)) (hxb : b * x = x * b) :
    x ∈ Subgroup.centralizer (B : Set G) := by
  have hK : B ⊓ Subgroup.centralizer ({x} : Set G) = B :=
    eq_of_hyperplane_le_of_mem hp (le_inf hHB fun h hh =>
      Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hxH h hh))
      inf_le_left hHc (Subgroup.mem_inf.2 ⟨hbB, Subgroup.mem_centralizer_singleton_iff.2 hxb⟩) hbH
  refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
  have hcK : c ∈ B ⊓ Subgroup.centralizer ({x} : Set G) := by rw [hK]; exact hc
  exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hcK).2

theorem card_center_map_eq_two {R Z : Subgroup G} (hR : timmesfeldIsExtraspecial ↥R)
    (hZ : Z = (Subgroup.center ↥R).map R.subtype) : Nat.card Z = 2 := by
  rw [hZ, Subgroup.card_map_of_injective R.subtype_injective]
  exact hR.2.2.2

theorem normalizer_le_centralizer_center {R Z : Subgroup G}
    (hR : timmesfeldIsExtraspecial ↥R) (hZ : Z = (Subgroup.center ↥R).map R.subtype) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.centralizer (Z : Set G) :=
  normalizer_le_centralizer_of_radical (card_center_map_eq_two hR hZ)
    (by rw [hZ]; exact Subgroup.map_subtype_le _)
    (fun z hz r hr => (mem_center_map_iff.1 (hZ ▸ hz)).2 r hr)
    (fun s hs h => by rw [hZ]; exact mem_center_map_iff.2 ⟨hs, fun r hr => (h r hr).symm⟩)

theorem coprime_card_of_le_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R X : Subgroup G} (hR : IsPGroup 2 R) (hXR : X ≤ R) : Nat.Coprime p (Nat.card X) := by
  obtain ⟨n, hn⟩ := (hR.to_le hXR).exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)

theorem le_of_hyperplane_centralizers {p : ℕ} (hp : p.Prime) {B X P : Subgroup G}
    (hB : IsElemAbelian p B) (hB1 : B ≠ ⊥) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hX : Nat.Coprime p (Nat.card X))
    (h : ∀ H : Subgroup G, H ≤ B → Nat.card H * p = Nat.card B →
      X ⊓ Subgroup.centralizer (H : Set G) ≤ P) : X ≤ P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ :=
    (CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p B hB).exists_card_eq
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := by
    refine ⟨r - 1, ?_⟩
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, pow_zero, Subgroup.card_eq_one] at hr
      exact absurd hr hB1
    · omega
  rw [← CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation p s hp B X hB
    hr.ge hBX hX]
  exact iSup₂_le fun H hH => h H hH.1 (by rw [hH.2, hr, pow_succ])

end CFSG.LocalAnalysis.GLTheoremA.H301B

end

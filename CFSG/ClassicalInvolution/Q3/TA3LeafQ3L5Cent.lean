module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3L5T2

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q3L5

open CFSG CFSG.ClassicalInvolution
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.maxPerfect_of_model (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    {P : Type} [Group P] {ι : P →* G} (hι : Function.Injective ι) (hιN : ι.range = N) {u : P}
    (hιu : ι u = t) {H₀ : Subgroup P} [Group.IsPerfect H₀]
    (hH₀ : H₀ ≤ Subgroup.centralizer {u})
    (hmax : ∀ M : Subgroup P, M ≤ Subgroup.centralizer {u} → ⁅M, M⁆ = M → M ≤ H₀)
    (hodd : NoOddNormal H₀) :
    (H₀.map ι ≤ N ∧ H₀.map ι ≤ Subgroup.centralizer {t} ∧ ⁅H₀.map ι, H₀.map ι⁆ = H₀.map ι) ∧
    (∀ M : Subgroup G, M ≤ N → M ≤ Subgroup.centralizer {t} → ⁅M, M⁆ = M → M ≤ H₀.map ι) ∧
      R ≤ Subgroup.centralizer (H₀.map ι : Set G) := by
  have hmaxG : ∀ M : Subgroup G, M ≤ N → M ≤ Subgroup.centralizer {t} → ⁅M, M⁆ = M →
      M ≤ H₀.map ι := by
    intro M hMN hMt hMp
    have hMr : M ≤ ι.range := hιN ▸ hMN
    have hM0 : ⁅M.comap ι, M.comap ι⁆ = M.comap ι := Subgroup.map_injective hι (by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hMr, hMp])
    have hM0t : M.comap ι ≤ Subgroup.centralizer {u} := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hMt hx)
      rw [← hιu, ← map_mul, ← map_mul] at h1
      exact hι h1
    rw [← Subgroup.map_comap_eq_self hMr]
    exact Subgroup.map_mono (hmax _ hM0t hM0)
  have hHN : H₀.map ι ≤ N := hιN ▸ Subgroup.map_le_range ι H₀
  have hHt : H₀.map ι ≤ Subgroup.centralizer {t} := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hιu, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hH₀ hx)]
  have : Group.IsPerfect ↥(H₀.map ι) := by
    rw [← Subgroup.range_subtype H₀, ← MonoidHom.range_comp]
    exact Group.IsPerfect.range _
  exact ⟨⟨hHN, hHt, Subgroup.commutator_eq_self⟩, hmaxG,
    TightDatum.le_centralizer_of_maxPerfect hD hHN hHt hmaxG (hodd.map ι hι)⟩

omit [Finite G] in
theorem mem_centralizer_of_model {P : Type} [Group P] {ι : P →* G} (hι : Function.Injective ι)
    {u : P} (hιu : ι u = t) {H₀ : Subgroup P} {p : P}
    (ht : ι p ∈ Subgroup.centralizer {t}) (hH : ι p ∈ Subgroup.centralizer (H₀.map ι : Set G)) :
    p ∈ Subgroup.centralizer {u} ∧ p ∈ Subgroup.centralizer (H₀ : Set P) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul, hιu]
    exact Subgroup.mem_centralizer_singleton_iff.mp ht
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    apply hι
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hH (ι h) ⟨h, hh, rfl⟩

theorem TightDatum.false_of_u₂ (hD : TightDatum R S t) {N : Subgroup G} [N.Normal]
    {ι : SL(4 + 1, ZMod 3) →* G} (hι : Function.Injective ι) (hιN : ι.range = N)
    (hιu : ι u₂ = t) {s : G} (hsR : s ∈ R) (hsN : s ∈ N) (hs4 : orderOf s = 4) : False := by
  obtain ⟨-, -, hRH⟩ := TightDatum.maxPerfect_of_model hD hι hιN hιu H₂_le perfect_le_H₂
    noOddNormal_H₂
  obtain ⟨p, rfl⟩ : s ∈ ι.range := hιN ▸ hsN
  obtain ⟨hpu, hpH⟩ := mem_centralizer_of_model hι hιu (hD.cent hsR) (hRH hsR)
  have h2 : ι p ^ 2 = 1 := by rw [sq, ← map_mul, mul_self_of_mem_H₂ hpu hpH, map_one]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hs4] at this
  norm_num at this

end CFSG.ClassicalInvolution.Q3.TA3.Q3L5

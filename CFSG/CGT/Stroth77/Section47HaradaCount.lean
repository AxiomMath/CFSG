module

public import CFSG.GroupTheory.ThompsonTransferCount
public import CFSG.CGT.Stroth77.Section42Fusion

public section

namespace CFSG.CGT.Stroth77

namespace Stroth47

variable {G : Type*} [Group G] [Finite G]

theorem card_inf_centralizer_dvd {S : Subgroup G} {p : G} (hp : p ∈ S) (w : G) :
    Nat.card ↥(S ⊓ Subgroup.centralizer {w}) ∣
      Nat.card ↥(S ⊓ Subgroup.centralizer {p⁻¹ * w * p}) := by
  have hle : (S ⊓ Subgroup.centralizer {w}).map (MulAut.conj p⁻¹).toMonoidHom ≤
      S ⊓ Subgroup.centralizer {p⁻¹ * w * p} := by
    rintro z ⟨s, hs, rfl⟩
    obtain ⟨hsS, hsw⟩ := Subgroup.mem_inf.mp hs
    have hsw' : w * s = s * w := Subgroup.mem_centralizer_iff.mp hsw w rfl
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact S.mul_mem (S.mul_mem (S.inv_mem hp) hsS) hp
    · rw [Subgroup.mem_centralizer_iff]
      rintro z rfl
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc p⁻¹ * w * p * (p⁻¹ * s * p) = p⁻¹ * (w * s) * p := by group
        _ = p⁻¹ * (s * w) * p := by rw [hsw']
        _ = p⁻¹ * s * p * (p⁻¹ * w * p) := by group
  rw [← Subgroup.card_map_of_injective (K := S ⊓ Subgroup.centralizer {w})
    (f := (MulAut.conj p⁻¹).toMonoidHom) (MulAut.conj p⁻¹).injective]
  exact Subgroup.card_dvd_of_le hle

theorem false_of_harada_count [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (S : Sylow 2 G) {D U P : Subgroup G} {x z uv : G} {j : ℕ} (hUS : U ≤ S)
    (hU : U.relIndex S = 2) (hPU : P ≤ U) (hxS : x ∈ S) (hxU : x ∉ U) (hxz : x ^ 2 ^ j = z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (huvD : uv ∈ Subgroup.normalizer (D : Set G))
    (huv : uv * uv = 1)
    (h3 : ∀ y ∈ D, y * y = 1 → y ≠ 1 → IsConj y z → ∃ p ∈ P, p⁻¹ * y * p = z)
    (h5 : ∀ y ∈ (S : Subgroup G), y * y ∈ D ∨ y * y * uv ∈ D)
    (h6 : ∀ y ∈ U, y * uv ∈ D → y * y = 1 → ¬ IsConj y z)
    (h6' : ∀ y ∈ (S : Subgroup G), y ∉ U → y * y = 1 → ¬ IsConj y z)
    (h8 : ∀ y ∈ (S : Subgroup G), y ∉ U → ∀ l : ℕ, 2 ≤ l → y ^ 2 ^ l = z →
      ∀ (g : G) (k : ℕ), y = g⁻¹ * x ^ (2 * k) * g → False)
    (h8c : ∀ y ∈ (S : Subgroup G), y ∉ U → y * y = z → ∀ (g : G) (k : ℕ), 1 ≤ k →
      y = g⁻¹ * x ^ 2 ^ k * g →
      2 ^ (k + 1) * Nat.card ↥((S : Subgroup G) ⊓ Subgroup.centralizer {y}) ∣
        Nat.card ↥(Subgroup.centralizer {x ^ 2 ^ k}))
    (hconj : ∀ g : G, g⁻¹ * x * g ∉ U) : False := by
  refine EvenSporadicStandard.not_exists_normal_index_two_of_nonabelian hnonab
    (ThompsonTransferCount.exists_normal_index_two_of_count S.isPGroup' S.not_dvd_index hU hxS
      hxU hconj ?_)
  intro g k hk hgS hgU
  set y := g⁻¹ * x ^ 2 ^ k * g with hy
  have h2k : 2 * 2 ^ (k - 1) = 2 ^ k := by
    rw [← pow_succ']
    congr 1
    omega
  have hk' : x ^ (2 * 2 ^ (k - 1)) ≠ 1 := by
    rw [h2k]
    rintro h1
    apply hgU
    rw [hy, h1]
    simpa using U.one_mem
  obtain ⟨l, -, hl, -⟩ := Stroth42.exists_pow_eq_of_even hxz hz2 hz1 hk'
  rw [h2k] at hl
  have hrz : IsConj (y ^ 2 ^ l) z := by
    rw [hy, Stroth42.conj_pow', hl]
    exact Stroth42.isConj_of_conj_eq rfl
  rcases Nat.eq_zero_or_pos l with rfl | hl1
  · rw [pow_zero, pow_one] at hrz
    exact absurd hrz (h6' y hgS hgU (Stroth42.mul_self_eq_one_of_isConj hrz hz2))
  · have hrD := Stroth42.pow_mem_of_mul_self hl1 huvD huv hz2
      (Stroth42.mul_self_mem_of_relIndex hU hgS) (h5 y hgS) h6 hrz
    obtain ⟨p, hpU, hp⟩ := Stroth42.exists_conj_pow_eq hPU hz2 hz1 h3 hrD hrz
    have hy'S : p⁻¹ * y * p ∈ (S : Subgroup G) :=
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem (hUS hpU)) hgS)
        (hUS hpU)
    have hy'U : p⁻¹ * y * p ∉ U := fun h' => hgU (by
      have := U.mul_mem (U.mul_mem hpU h') (U.inv_mem hpU)
      rwa [show p * (p⁻¹ * y * p) * p⁻¹ = y by group] at this)
    have hy'eq : p⁻¹ * y * p = (g * p)⁻¹ * x ^ 2 ^ k * (g * p) := by rw [hy]; group
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | hl2
    · rw [pow_one, sq] at hp
      exact (mul_dvd_mul_left _ (card_inf_centralizer_dvd (hUS hpU) y)).trans
        (h8c _ hy'S hy'U hp (g * p) k hk hy'eq)
    · exact (h8 _ hy'S hy'U l hl2 hp (g * p) (2 ^ (k - 1)) (by rw [hy'eq, h2k])).elim

end Stroth47

end CFSG.CGT.Stroth77

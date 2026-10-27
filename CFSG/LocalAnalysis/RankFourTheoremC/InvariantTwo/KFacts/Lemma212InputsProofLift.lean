module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup

theorem exists_lift_pow_eq_one {p : ℕ} (hp : p.Prime) {S L : Type} [Group S] [Group L]
    (φ : S →* L) (hφ : Function.Surjective φ) (Z : Subgroup S) [IsCyclic Z]
    (hZ : Z ≤ center S) (hker : φ.ker ≤ Z) (hcenter : center L ≤ Z.map φ)
    (hnt : center L ≠ ⊥) (hZp : IsPGroup p (center L)) {d : L} (hd : d ^ p = 1) :
    ∃ s : S, s ^ p = 1 ∧ ∃ c ∈ center L, φ s = d * c := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Z)
  have hZg : Z = zpowers (g : S) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      exact mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      exact zpow_mem g.2 k
  have hgc : ∀ x : S, Commute (g : S) x := fun x => (mem_center_iff.1 (hZ g.2) x).symm
  set c := φ (g : S) with hc
  have hmapZ : Z.map φ = zpowers c := by
    rw [hZg, MonoidHom.map_zpowers]
  have hcZ : c ∈ center L := by
    have h1 : c ∈ Z.map φ := Subgroup.mem_map_of_mem φ g.2
    refine (mem_center_iff.2 fun x => ?_)
    obtain ⟨s, rfl⟩ := hφ x
    rw [hc, ← map_mul, ← map_mul, (hgc s).eq]
  have hcen : center L = zpowers c :=
    le_antisymm (hmapZ ▸ hcenter) ((zpowers_le).2 hcZ)
  have hc1 : c ≠ 1 := by
    intro h1
    apply hnt
    rw [hcen, h1, zpowers_one_eq_bot]
  have hpord : p ∣ orderOf c := by
    obtain ⟨k, hk⟩ := hZp ⟨c, hcZ⟩
    have hk' : c ^ (p ^ k) = 1 := congrArg Subtype.val hk
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hk')
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hc1 (orderOf_eq_one_iff.1 (by simpa using hio))
    rw [hio]
    exact dvd_pow_self p hi0
  obtain ⟨s₀, hs₀⟩ := hφ d
  have hs₀p : s₀ ^ p ∈ Z := hker (by rw [MonoidHom.mem_ker, map_pow, hs₀, hd])
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (hZg ▸ hs₀p)
  have hcj : c ^ j = 1 := by
    rw [hc, ← map_zpow, hj, map_pow, hs₀, hd]
  have hpj : (p : ℤ) ∣ j :=
    (Int.natCast_dvd_natCast.2 hpord).trans (orderOf_dvd_iff_zpow_eq_one.2 hcj)
  obtain ⟨j', rfl⟩ := hpj
  refine ⟨s₀ * (g : S) ^ (-j'), ?_, c ^ (-j'), ?_, ?_⟩
  · have h1 : Commute s₀ ((g : S) ^ (-j')) := ((hgc s₀).symm).zpow_right (-j')
    have h2 : ((g : S) ^ (-j')) ^ p = (g : S) ^ (-((p : ℤ) * j')) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      ring
    rw [h1.mul_pow, h2, ← hj, zpow_neg, mul_inv_cancel]
  · exact zpow_mem hcZ _
  · rw [map_mul, map_zpow, hs₀]

end CFSG.LocalAnalysis.RankFourTheoremC

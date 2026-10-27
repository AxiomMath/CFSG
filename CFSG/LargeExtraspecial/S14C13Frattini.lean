module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LargeExtraspecial.S14

open Subgroup

theorem centralizer_sup_eq_top {M : Type*} [Group M] [Finite M] {M0 N : Subgroup M}
    [M0.Normal] {t : M} (ht1 : t ≠ 1) (htN : t ∈ N) (hN0 : N ≤ M0)
    (hN2 : IsPGroup 2 N)
    (hZ : ∀ x : M, x * t = t * x → (∀ n ∈ N, x * n = n * x) → x = 1 ∨ x = t) :
    centralizer ({t} : Set M) ⊔ M0 = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN2' : IsPGroup 2 (N.subgroupOf M0) := hN2.of_equiv (subgroupOfEquivOfLe hN0).symm
  obtain ⟨P, hP⟩ := hN2'.exists_le_sylow
  set P' : Subgroup M := (P : Subgroup M0).map M0.subtype
  have hNP : N ≤ P' := fun n hn => ⟨⟨n, hN0 hn⟩, hP (mem_subgroupOf.mpr hn), rfl⟩
  have hC : ∀ x : M, (∀ p ∈ P', x * p = p * x) → x = 1 ∨ x = t := fun x hx =>
    hZ x (hx t (hNP htN)) fun n hn => hx n (hNP hn)
  have htZ : ∀ p ∈ P', t * p = p * t := by
    have hPp : IsPGroup 2 (P : Subgroup M0) := P.isPGroup'
    have : Nontrivial (P : Subgroup M0) := ⟨⟨⟨⟨t, hN0 htN⟩, hP (mem_subgroupOf.mpr htN)⟩, 1,
      fun h => ht1 (congrArg (fun y : (P : Subgroup M0) => ((y : M0) : M)) h)⟩⟩
    have := hPp.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : center (P : Subgroup M0))
    have hzc : ∀ p ∈ P', (((z : (P : Subgroup M0)) : M0) : M) * p = p * ((z : _) : M0) := by
      rintro _ ⟨p, hp, rfl⟩
      have := (mem_center_iff.mp z.2) ⟨p, hp⟩
      exact congrArg (fun y : (P : Subgroup M0) => ((y : M0) : M)) this.symm
    rcases hC _ hzc with h | h
    · exact absurd (Subtype.ext (Subtype.ext (Subtype.ext h))) hz1
    · rw [← h]
      exact hzc
  have hnorm : normalizer (P' : Set M) ≤ centralizer ({t} : Set M) := by
    intro g hg
    rw [mem_centralizer_singleton_iff]
    have hgP : ∀ p, p ∈ P' ↔ g * p * g⁻¹ ∈ P' := mem_normalizer_iff.mp hg
    have hc : ∀ p ∈ P', (g * t * g⁻¹) * p = p * (g * t * g⁻¹) := by
      intro p hp
      have hp' : g⁻¹ * p * g ∈ P' := by
        have := (hgP (g⁻¹ * p * g)).mpr (by simpa [mul_assoc] using hp)
        exact this
      have := htZ _ hp'
      calc g * t * g⁻¹ * p = g * (t * (g⁻¹ * p * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * p * g) * t) * g⁻¹ := by rw [this]
        _ = p * (g * t * g⁻¹) := by group
    rcases hC _ hc with h | h
    · exact absurd (conj_eq_one_iff.mp h) ht1
    · calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [h]
  have hF := Sylow.normalizer_sup_eq_top (N := M0) P
  exact eq_top_iff.mpr (hF.symm.le.trans (sup_le_sup_right hnorm _))

end CFSG.LargeExtraspecial.S14

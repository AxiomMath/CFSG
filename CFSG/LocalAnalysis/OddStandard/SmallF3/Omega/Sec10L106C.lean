module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10S105S
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Conj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10_exists_g [Finite G] (h37 : Asc82Lemma37) (h103 : Asc82Lemma103)
    (h105 : Asc82Lemma105) (hb : Asc82Basic10) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) :
    ∃ g ∈ normalizer (S : Set G), g⁻¹ * t * g = t * z ∧ g⁻¹ * z * g = z := by
  obtain ⟨-, -, htnotL, htS, -, -⟩ := hb G t L S z hctx.toSec10Z
  obtain ⟨g0, hg0⟩ := h105 G t L S z K1 K2 hctx
  have hz2 : orderOf z = 2 := hctx.toSec10Z.pocket.1
  have ht2 : orderOf t = 2 := hctx.involution
  have hzL : z ∈ L := (hctx.pocket1.2.1 hctx.pocket1.1).1
  have hzt : z * t = t * z := (hctx.central t htS).symm
  have hST : S ≤ centralizer ({t * z} : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hst : s * t = t * s :=
      Subgroup.mem_centralizer_singleton_iff.mp (hctx.sylow.1 hs)
    have hsz : s * z = z * s := hctx.central s hs
    calc s * (t * z) = (s * t) * z := by group
      _ = (t * s) * z := by rw [hst]
      _ = t * (s * z) := by group
      _ = t * (z * s) := by rw [hsz]
      _ = (t * z) * s := by group
  have hS1syl : IsSylow2Of (CFSG.conjugate S g0) (centralizer ({t * z} : Set G)) := by
    have h := hctx.sylow.conjugate g0
    rw [conjugate_centralizer_singleton t g0, hg0] at h
    exact h
  have hS2 : IsPGroup 2 S := hctx.sylow.2.1
  have hSsyl : IsSylow2Of S (centralizer ({t * z} : Set G)) := by
    obtain ⟨P, hPsyl, hSP⟩ := exists_isSylow2Of_ge hS2 hST
    obtain ⟨c1, -, hc1⟩ := IsSylow2Of.exists_conj_mem hS1syl hPsyl
    have hmap : P.map (MulAut.conj c1⁻¹).toMonoidHom = CFSG.conjugate S g0 := by
      apply le_antisymm
      · intro y hy
        obtain ⟨x, hxP, rfl⟩ := Subgroup.mem_map.mp hy
        show (MulAut.conj c1⁻¹) x ∈ CFSG.conjugate S g0
        rw [MulAut.conj_apply, inv_inv]
        exact (hc1 x).mp hxP
      · intro y hy
        refine Subgroup.mem_map.mpr ⟨c1 * y * c1⁻¹, (hc1 _).mpr ?_, ?_⟩
        · have h : c1⁻¹ * (c1 * y * c1⁻¹) * c1 = y := by group
          rwa [h]
        · show (MulAut.conj c1⁻¹) (c1 * y * c1⁻¹) = y
          rw [MulAut.conj_apply]; group
    have hcardP : Nat.card P = Nat.card S := by
      have h1 : Nat.card P = Nat.card (P.map (MulAut.conj c1⁻¹).toMonoidHom) :=
        (Subgroup.card_map_of_injective
          (f := (MulAut.conj c1⁻¹).toMonoidHom) (MulAut.conj c1⁻¹).injective).symm
      rw [h1, hmap]
      simpa [CFSG.conjugate] using
        Subgroup.card_map_of_injective (f := (MulAut.conj g0⁻¹).toMonoidHom)
          (MulAut.conj g0⁻¹).injective
    have hSPeq : S = P := Subgroup.eq_of_le_of_card_ge hSP (le_of_eq hcardP)
    rw [hSPeq]
    exact hPsyl
  obtain ⟨c, hcT, hcsc⟩ := IsSylow2Of.exists_conj_mem hS1syl hSsyl
  set g : G := g0 * c⁻¹ with hgdef
  have hcomm : c * (t * z) = (t * z) * c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcT
  have hg_conj : CFSG.conjugate S g = S := by
    ext x
    have h1 : x ∈ CFSG.conjugate S g ↔ g * x * g⁻¹ ∈ S := mem_conjugate_iff'
    have h2 : g * x * g⁻¹ = g0 * (c⁻¹ * x * c) * g0⁻¹ := by
      rw [hgdef]; group
    have h3 : g0 * (c⁻¹ * x * c) * g0⁻¹ ∈ S ↔
        c⁻¹ * x * c ∈ CFSG.conjugate S g0 :=
      (mem_conjugate_iff' (H := S) (g := g0) (x := c⁻¹ * x * c)).symm
    rw [h1, h2, h3]
    exact (hcsc x).symm
  have hgN : g ∈ normalizer (S : Set G) := mem_normalizer_of_conjugate_eq hg_conj
  have ht2sq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  have hzsq : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hg_t : g⁻¹ * t * g = t * z := by
    calc g⁻¹ * t * g = c * (g0⁻¹ * t * g0) * c⁻¹ := by rw [hgdef]; group
      _ = c * (t * z) * c⁻¹ := by rw [hg0]
      _ = t * z := by rw [hcomm]; group
  have htz_ne_one : t * z ≠ 1 := by
    intro h1
    have ht_eq_z : t = z := by
      have hz_eq_t : z = t := by
        have h : z = t * (t * z) := by rw [← mul_assoc, ht2sq, one_mul]
        rw [h1, mul_one] at h
        exact h
      exact hz_eq_t.symm
    exact htnotL (by rw [ht_eq_z]; exact hzL)
  have hg_z : g⁻¹ * z * g = z := by
    have hz_centerIn : z ∈ centerIn S := by
      rw [centerIn, Subgroup.mem_map]
      refine ⟨⟨z, hctx.mem_S⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hctx.central (y : G) y.2)
    have hz_omega : z ∈ omega1 (centerIn S) := by
      rw [omega1]
      exact Subgroup.subset_closure ⟨hz_centerIn, by rw [pow_two]; exact hzsq⟩
    have hconj_omega : g⁻¹ * z * g ∈ omega1 (centerIn S) :=
      sec10_conj_mem_omega1 hgN hz_omega
    have hconj_sup : g⁻¹ * z * g ∈ zpowers z ⊔ zpowers t := by
      rwa [h103 G t L S z hctx.toSec10Z] at hconj_omega
    have hconj_ord : orderOf (g⁻¹ * z * g) = 2 := by
      rw [orderOf_conjugate_eq]; exact hz2
    rcases sec10_two_elem_cases hzt hz2 ht2 hconj_sup hconj_ord with h | h | h
    · exact h
    · exact absurd h (sec10_not_conj_z h37 hctx g)
    · exfalso
      have htzsq : (t * z) * (t * z) = 1 := by
        calc (t * z) * (t * z) = t * (z * t) * z := by group
          _ = t * (t * z) * z := by rw [hzt]
          _ = (t * t) * (z * z) := by group
          _ = 1 := by rw [ht2sq, hzsq, one_mul]
      have hconj_tz : g⁻¹ * (t * z) * g = 1 := by
        calc g⁻¹ * (t * z) * g = (g⁻¹ * t * g) * (g⁻¹ * z * g) := by group
          _ = (t * z) * (t * z) := by rw [hg_t, h]
          _ = 1 := htzsq
      have htz_eq_one : t * z = 1 := by
        calc t * z = g * (g⁻¹ * (t * z) * g) * g⁻¹ := by group
          _ = g * 1 * g⁻¹ := by rw [hconj_tz]
          _ = 1 := by group
      exact htz_ne_one htz_eq_one
  exact ⟨g, hgN, hg_t, hg_z⟩

end CFSG.OddStandard.SmallF3.Omega

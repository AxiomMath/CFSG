module

public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalLift

open scoped Pointwise

variable {H H' : Type*} [Group H] [Group H'] [Finite H]

private theorem comap_le_of_le_map (π : H →* H') {M : Subgroup H}
    (hker : π.ker ≤ M) {R' : Subgroup H'} (hR'M : R' ≤ M.map π) :
    R'.comap π ≤ M := by
  intro x hx
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp (hR'M hx)
  have hxm : x * m⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, mul_inv_cancel]
  have hx' : x = (x * m⁻¹) * m := by group
  rw [hx']
  exact M.mul_mem (hker hxm) hm

private theorem exists_isSylowOf_map_eq {r : ℕ} [Fact r.Prime] (π : H →* H')
    (hπ : Function.Surjective π) {M : Subgroup H} (hker : π.ker ≤ M) {R' : Subgroup H'}
    (hR'p : IsPGroup r R') (hR'M : R' ≤ M.map π) :
    ∃ R : Subgroup H, CFSG.ABGLocalTools.IsSylowOf r R (R'.comap π) ∧ R ≤ M ∧
      R.map π = R' := by
  classical
  let W : Subgroup H := R'.comap π
  have hWM : W ≤ M := comap_le_of_le_map π hker hR'M
  have hWmap : W.map π = R' := Subgroup.map_comap_eq_self_of_surjective hπ R'
  haveI hR'fin : Finite ↥R' := by
    haveI : Finite ↥(M.map π) :=
      Finite.of_surjective (π.subgroupMap M) (MonoidHom.subgroupMap_surjective π M)
    exact Finite.of_injective (Subgroup.inclusion hR'M) (Subgroup.inclusion_injective hR'M)
  let φ : W →* R' := (π.comp W.subtype).codRestrict R' fun w =>
    Subgroup.mem_comap.mp (show (w : H) ∈ R'.comap π from w.2)
  have hφ : Function.Surjective φ := by
    intro y
    have hy : (y : H') ∈ W.map π := by rw [hWmap]; exact y.2
    obtain ⟨w, hw, hwπ⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨w, hw⟩, Subtype.ext hwπ⟩
  obtain ⟨S : Sylow r W⟩ := (inferInstance : Nonempty (Sylow r W))
  let R : Subgroup H := (S : Subgroup W).map W.subtype
  have hRsyl : CFSG.ABGLocalTools.IsSylowOf r R W := ⟨S, rfl⟩
  have hSmap : (S : Subgroup W).map φ = ⊤ := by
    rw [← Sylow.coe_mapSurjective hφ S]
    refine Subgroup.eq_top_of_card_eq ((S.mapSurjective hφ : Sylow r R') : Subgroup R') ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR'p
    rw [Sylow.card_eq_multiplicity, hn, Nat.factorization_pow_self (Fact.out : r.Prime)]
  have hRmap : R.map π = R' := by
    have hcomp : π.comp W.subtype = R'.subtype.comp φ := by
      ext w
      rfl
    calc R.map π = (S : Subgroup W).map (π.comp W.subtype) := by
          rw [Subgroup.map_map]
      _ = (S : Subgroup W).map (R'.subtype.comp φ) := by rw [hcomp]
      _ = ((S : Subgroup W).map φ).map R'.subtype := by rw [Subgroup.map_map]
      _ = (⊤ : Subgroup R').map R'.subtype := by rw [hSmap]
      _ = R' := by rw [Subgroup.map_top, Subgroup.range_subtype]
  exact ⟨R, hRsyl, hRsyl.le.trans hWM, hRmap⟩

theorem normalizer_le_map_of_forall {r : ℕ} [Fact r.Prime] (π : H →* H')
    (hπ : Function.Surjective π) {M : Subgroup H} (hker : π.ker ≤ M) {R' : Subgroup H'}
    (hR'p : IsPGroup r R') (hR'M : R' ≤ M.map π)
    (hN : ∀ R : Subgroup H, IsPGroup r R → R ≤ M → R.map π = R' →
      Subgroup.normalizer (R : Set H) ≤ M) :
    Subgroup.normalizer (R' : Set H') ≤ M.map π := by
  classical
  let W : Subgroup H := R'.comap π
  have hWM : W ≤ M := comap_le_of_le_map π hker hR'M
  obtain ⟨R, hRsyl, hRM, hRmap⟩ := exists_isSylowOf_map_eq π hπ hker hR'p hR'M
  have hNR : Subgroup.normalizer (R : Set H) ≤ M :=
    hN R hRsyl.isPGroup hRM hRmap
  have hfr : (Subgroup.normalizer (W : Set H) : Set H) ⊆
      (Subgroup.normalizer (R : Set H) : Set H) * (W : Set H) := by
    intro x hx
    have hx' : x⁻¹ ∈ Subgroup.normalizer (W : Set H) := Subgroup.inv_mem _ hx
    have hR₀ : CFSG.ABGLocalTools.IsSylowOf r
        (R.map (MulAut.conj x⁻¹).toMonoidHom) W := by
      refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
      · rintro y ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hx' z).mp (hRsyl.le hz)
      · rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hRsyl.card_eq]
    obtain ⟨k, hk, hconj⟩ := hRsyl.exists_mem_conj hR₀
    refine Set.mem_mul.mpr ⟨x * k, ?_, k⁻¹, Subgroup.inv_mem _ hk, by group⟩
    change x * k ∈ Subgroup.normalizer (R : Set H)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [show (x * k) * y * (x * k)⁻¹ = x * (k * y * k⁻¹) * x⁻¹ by group]
    have hmem : ∀ w : H, w ∈ R.map (MulAut.conj x⁻¹).toMonoidHom ↔
        x * w * x⁻¹ ∈ R := by
      intro w
      rw [Subgroup.mem_map_equiv]
      change (MulAut.conj x⁻¹)⁻¹ w ∈ R ↔ x * w * x⁻¹ ∈ R
      rw [MulAut.conj_inv_apply, inv_inv]
    rw [← hmem (k * y * k⁻¹), hconj (k * y * k⁻¹)]
    rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
  have hNW : Subgroup.normalizer (W : Set H) ≤ M := by
    intro x hx
    obtain ⟨n, hn, w, hw, hnw⟩ := Set.mem_mul.mp (hfr hx)
    rw [← hnw]
    exact M.mul_mem (hNR hn) (hWM hw)
  have hcomap : (Subgroup.normalizer (R' : Set H')).comap π =
      Subgroup.normalizer (W : Set H) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective R' hπ]
  intro y hy
  obtain ⟨x, rfl⟩ := hπ y
  refine Subgroup.mem_map.mpr ⟨x, hNW ?_, rfl⟩
  rw [← hcomap]
  exact hy

theorem exists_isPGroup_map_eq {r : ℕ} [Fact r.Prime] (π : H →* H')
    (hπ : Function.Surjective π) {M : Subgroup H} (hker : π.ker ≤ M) {R' : Subgroup H'}
    (hR'p : IsPGroup r R') (hR'M : R' ≤ M.map π) :
    ∃ R : Subgroup H, IsPGroup r R ∧ R ≤ M ∧ R.map π = R' := by
  obtain ⟨R, hRsyl, hRM, hRmap⟩ := exists_isSylowOf_map_eq π hπ hker hR'p hR'M
  exact ⟨R, hRsyl.isPGroup, hRM, hRmap⟩

theorem two_le_pRank_of_map {r : ℕ} [Fact r.Prime] [Finite H'] (hr2 : r ≠ 2)
    (π : H →* H') {R : Subgroup H} (hR : IsPGroup r R)
    (h : 2 ≤ CFSG.Open.pRank r (R.map π)) : 2 ≤ CFSG.Open.pRank r R := by
  classical
  have hr := (Fact.out : r.Prime)
  have hodd : Odd r := hr.odd_of_ne_two hr2
  have hRnc : ¬ IsCyclic R := by
    intro hcyc
    haveI : Finite ↥(R.map π) :=
      Finite.of_surjective (π.subgroupMap R) (MonoidHom.subgroupMap_surjective π R)
    have hcyc' : IsCyclic ↥(R.map π) :=
      isCyclic_of_surjective (π.subgroupMap R) (MonoidHom.subgroupMap_surjective π R)
    have hle := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc'
    omega
  obtain ⟨B, hBea, hBcard⟩ :=
    CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two hodd hR hRnc
  let E : Subgroup H := B.map R.subtype
  have hEea : CFSG.Open.IsElemAbelian r E :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hBea).map R.subtype
  have hEcard : Nat.card E = r ^ 2 := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hBcard]
  exact CFSG.SectionRank.le_pRank hr.one_lt (H := R) (E := E)
    (Subgroup.map_subtype_le B) hEea hEcard

end CFSG.LocalLift

end

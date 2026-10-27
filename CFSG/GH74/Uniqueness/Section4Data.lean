module

public import CFSG.GH74.Uniqueness.CorZD

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section Data

variable {Y : Type} [Group Y] [Finite Y]

structure ZDData (Y : Type) [Group Y] [Finite Y] (Z : Set Y) (M : Subgroup Y) (u : Y) : Prop where
  mem : u ∈ M
  sq : u ^ 2 = 1
  sup : commutator Y ⊔ zpowers u = ⊤
  inf : commutator Y ⊓ zpowers u = ⊥
  comm : ⁅zpowers u, commutator Y⁆ ≤ pPrimeCore 2 Y
  le_comm : pPrimeCore 2 Y ≤ commutator Y
  le_M : pPrimeCore 2 Y ≤ M
  bar : ∃ (K : Type) (_ : Group K) (φ : ↥(commutator Y) →* K), Function.Surjective φ ∧
    φ.ker = (pPrimeCore 2 Y).subgroupOf (commutator Y) ∧ CFSG.BenderSuzuki.IsBenderGroup K ∧
    ∃ S : Sylow 2 K, (M.subgroupOf (commutator Y)).map φ = normalizer ((S : Subgroup K) : Set K)
  zset : ∀ z ∈ Z, (∃ d ∈ commutator Y, z = u * d) ∧ ∀ o ∈ pPrimeCore 2 Y, z ≠ u * o

theorem bender_borel_iff_exists_hom (M : Subgroup Y) :
    (CFSG.BenderSuzuki.IsBenderGroup (derivedBar Y) ∧ IsBorel (derivedBarImage M)) ↔
      ∃ (K : Type) (_ : Group K) (φ : ↥(commutator Y) →* K), Function.Surjective φ ∧
        φ.ker = (pPrimeCore 2 Y).subgroupOf (commutator Y) ∧
        CFSG.BenderSuzuki.IsBenderGroup K ∧
        ∃ S : Sylow 2 K, (M.subgroupOf (commutator Y)).map φ = normalizer ((S : Subgroup K) : Set K) := by
  have hMeq : (M ⊓ commutator Y).subgroupOf (commutator Y) = M.subgroupOf (commutator Y) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  constructor
  · rintro ⟨hB, S, hS⟩
    refine ⟨derivedBar Y, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
      QuotientGroup.ker_mk' _, hB, S, ?_⟩
    rw [← hS]
    unfold derivedBarImage
    rw [hMeq]
  · rintro ⟨K, _, φ, hφ, hker, hK, S, hS⟩
    have : Finite K := Finite.of_surjective φ hφ
    let e : derivedBar Y ≃* K :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
    have he : ∀ x : ↥(commutator Y), e (QuotientGroup.mk' _ x) = φ x := fun x => rfl
    refine ⟨isBenderGroup_of_mulEquiv e hK, Sylow.mapSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective S, ?_⟩
    have hcoe : ((Sylow.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective S : Sylow 2 _) :
        Subgroup (derivedBar Y)) = (S : Subgroup K).map e.symm.toMonoidHom :=
      Sylow.coe_mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective S
    rw [hcoe, ← Subgroup.map_normalizer_eq_of_bijective _ e.symm.bijective, ← hS]
    unfold derivedBarImage
    rw [hMeq, Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp φ = QuotientGroup.mk' _ := by
      ext x
      simp [← he]
    rw [hcomp]

theorem zdConclusion_iff (Z : Set Y) (M : Subgroup Y) :
    ZDConclusion Y Z M ↔ Open.twoRank Y ≤ 1 ∨ ∃ u, ZDData Y Z M u := by
  unfold ZDConclusion
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨u, hu, hsq, hsup, hinf, hcomm, hle, hleM, hB, hBo, hz⟩
    exact ⟨u, ⟨hu, hsq, hsup, hinf, hcomm, hle, hleM,
      (bender_borel_iff_exists_hom M).mp ⟨hB, hBo⟩, hz⟩⟩
  · rintro ⟨u, ⟨hu, hsq, hsup, hinf, hcomm, hle, hleM, hbar, hz⟩⟩
    obtain ⟨hB, hBo⟩ := (bender_borel_iff_exists_hom M).mpr hbar
    exact ⟨u, hu, hsq, hsup, hinf, hcomm, hle, hleM, hB, hBo, hz⟩

end Data

end CFSG.GH74.Uniqueness

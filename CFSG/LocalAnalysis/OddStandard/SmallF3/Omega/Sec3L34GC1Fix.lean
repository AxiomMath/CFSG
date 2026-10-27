module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Iso

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {u x : G} {K : Subgroup G} {𝒪 : Set (Subgroup G)}

theorem L34GOrb.c0_fixed [Finite G] (hNF : Asc82FactNoncentralFixed) (hO : L34GOrb u x K 𝒪)
    (hxN : x ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G)) :
    ∀ S ∈ l34gImg (sSup 𝒪) '' 𝒪,
      CFSG.conjugate S ((sSup 𝒪).normalizerMonoidHom ⟨x, hxN⟩) = S →
        ∃ c ∈ l34gImg (sSup 𝒪) (sSup 𝒪 ⊓ centralizer ({x} : Set G)), c ∈ S ∧ c ≠ 1 := by
  rintro S ⟨J, hJ, rfl⟩ hfix
  have hJx : CFSG.conjugate J x ∈ 𝒪 :=
    hO.conj J hJ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have himg : l34gImg (sSup 𝒪) (CFSG.conjugate J x) = l34gImg (sSup 𝒪) J :=
    (l34gImg_conjugate hxN).symm.trans hfix
  have hxJ : x ∈ normalizer (J : Set G) :=
    sec63P_conjugate_eq_iff.1
      (le_antisymm (hO.img_le hJx hJ himg.le) (hO.img_le hJ hJx himg.ge))
  obtain ⟨e, he, -, hnc⟩ := hNF G J (hO.inFStar J hJ) x hO.invol hxJ
  have heE : e ∈ sSup 𝒪 := le_sSup hJ he.1
  have heN : e ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) := Subgroup.le_normalizer heE
  refine ⟨(sSup 𝒪).normalizerMonoidHom ⟨e, heN⟩, mem_l34gImg.2 ⟨e, heN, ⟨heE, he.2⟩, rfl⟩,
    mem_l34gImg.2 ⟨e, heN, he.1, rfl⟩, fun h1 => ?_⟩
  have hall := (l34gAct_eq_one_iff heN).1 h1
  exact hnc fun g hg => hall g (le_sSup hJ hg)

theorem L34GOrb.c0_swap [Finite G] (hO : L34GOrb u x K 𝒪)
    (hxN : x ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G)) :
    ∀ S ∈ l34gImg (sSup 𝒪) '' 𝒪,
      CFSG.conjugate S ((sSup 𝒪).normalizerMonoidHom ⟨x, hxN⟩) ≠ S →
        ∀ d ∈ S, d * ((sSup 𝒪).normalizerMonoidHom ⟨x, hxN⟩ * d *
          ((sSup 𝒪).normalizerMonoidHom ⟨x, hxN⟩)⁻¹) ∈
            l34gImg (sSup 𝒪) (sSup 𝒪 ⊓ centralizer ({x} : Set G)) := by
  rintro S ⟨J, hJ, rfl⟩ hne d hd
  have hJx : CFSG.conjugate J x ∈ 𝒪 :=
    hO.conj J hJ x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hJne : CFSG.conjugate J x ≠ J := fun h => hne (by rw [l34gImg_conjugate hxN, h])
  have hcomm := hO.commute hJx hJ hJne
  obtain ⟨j, hjN, hjJ, rfl⟩ := mem_l34gImg.1 hd
  have hx2 : x * x = 1 := sec63P_mul_self hO.invol
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have ha : x * j * x⁻¹ ∈ CFSG.conjugate J x := by
    rw [sec63P_mem_conjugate_iff]
    have h : x * (x * j * x⁻¹) * x⁻¹ = j := by
      rw [hxinv]
      calc x * (x * j * x) * x = (x * x) * j * (x * x) := by group
        _ = j := by rw [hx2, one_mul, mul_one]
    rw [h]
    exact hjJ
  have hjE : j ∈ sSup 𝒪 := le_sSup hJ hjJ
  have haE : x * j * x⁻¹ ∈ sSup 𝒪 := le_sSup hJx ha
  have hj'N : j * (x * j * x⁻¹) ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    Subgroup.le_normalizer ((sSup 𝒪).mul_mem hjE haE)
  have e1 : x * j = (x * j * x⁻¹) * x := by group
  have e2 : x * (x * j * x⁻¹) = j * x := by
    rw [hxinv]
    calc x * (x * j * x) = (x * x) * j * x := by group
      _ = j * x := by rw [hx2, one_mul]
  have hcx : x * (j * (x * j * x⁻¹)) = (j * (x * j * x⁻¹)) * x :=
    calc x * (j * (x * j * x⁻¹)) = (x * j) * (x * j * x⁻¹) := (mul_assoc _ _ _).symm
      _ = ((x * j * x⁻¹) * x) * (x * j * x⁻¹) := by rw [← e1]
      _ = (x * j * x⁻¹) * (x * (x * j * x⁻¹)) := mul_assoc _ _ _
      _ = (x * j * x⁻¹) * (j * x) := by rw [e2]
      _ = ((x * j * x⁻¹) * j) * x := (mul_assoc _ _ _).symm
      _ = (j * (x * j * x⁻¹)) * x := by rw [hcomm _ ha j hjJ]
  refine mem_l34gImg.2 ⟨j * (x * j * x⁻¹), hj'N, ⟨(sSup 𝒪).mul_mem hjE haE, ?_⟩, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2 hcx.symm
  · have hsub : (⟨j * (x * j * x⁻¹), hj'N⟩ : normalizer ((sSup 𝒪 : Subgroup G) : Set G)) =
        ⟨j, hjN⟩ * (⟨x, hxN⟩ * ⟨j, hjN⟩ * ⟨x, hxN⟩⁻¹) := rfl
    rw [hsub, map_mul, map_mul, map_mul, map_inv]

end CFSG.OddStandard.SmallF3.Omega

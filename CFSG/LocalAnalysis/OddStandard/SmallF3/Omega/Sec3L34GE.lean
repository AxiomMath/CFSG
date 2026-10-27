module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GFacts
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GLayer
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_exists_e [Finite G] (hNF : Asc82FactNoncentralFixed) {x y : G} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hxy : x * y = y * x) {I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({y} : Set G))) (hIF : InFStar I) :
    ∃ e z : G, orderOf e = 2 ∧ e * x = x * e ∧ e * y = y * e ∧ e ∈ fstarLayer y ∧
      z ∈ fstarLayer y ∧ e * z ≠ z * e := by
  have hxC : x ∈ centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxy
  by_cases hfix : CFSG.conjugate I x = I
  ·
    have hxN : x ∈ normalizer (I : Set G) := sec63P_conjugate_eq_iff.mp hfix
    obtain ⟨e, he, heord, hne⟩ := hNF G I hIF x hx hxN
    simp only [not_forall, not_imp] at hne
    obtain ⟨g, hgI, hge⟩ := hne
    exact ⟨e, g, heord, Subgroup.mem_centralizer_singleton_iff.mp he.2,
      Subgroup.mem_centralizer_singleton_iff.mp (hI.1 he.1),
      le_fstarLayer hI hIF he.1, le_fstarLayer hI hIF hgI, hge⟩
  ·
    have hI' : IsComponentIn (CFSG.conjugate I x) (centralizer ({y} : Set G)) := hI.conjugate hxC
    have hI'F : InFStar (CFSG.conjugate I x) := hIF.conjugate x
    have hne' : I ≠ CFSG.conjugate I x := fun h => hfix h.symm
    have hcomm : ∀ a ∈ I, ∀ b ∈ CFSG.conjugate I x, a * b = b * a :=
      hI.commute_of_ne hI' hne'
    have hyN : y ∈ normalizer (I : Set G) := by
      rw [← sec63P_conjugate_eq_iff]
      exact conjugate_eq_self_of_le_centralizer hI.1
    obtain ⟨a, ha, haord, hane⟩ := hNF G I hIF y hy hyN
    simp only [not_forall, not_imp] at hane
    obtain ⟨g, hgI, hag⟩ := hane
    have haa : a * a = 1 := sec63P_mul_self haord
    have hxx : x * x = 1 := sec63P_mul_self hx
    have hbI' : x * a * x⁻¹ ∈ CFSG.conjugate I x := sec63P_conj_mem_conjugate hx ha.1
    have hab : a * (x * a * x⁻¹) = (x * a * x⁻¹) * a :=
      hcomm a ha.1 (x * a * x⁻¹) hbI'
    have hbb : (x * a * x⁻¹) * (x * a * x⁻¹) = 1 := by
      calc (x * a * x⁻¹) * (x * a * x⁻¹) = x * (a * a) * x⁻¹ := by group
        _ = 1 := by rw [haa]; group
    have hxbx : x * (x * a * x⁻¹) * x⁻¹ = a := by
      calc x * (x * a * x⁻¹) * x⁻¹ = (x * x) * a * (x * x)⁻¹ := by group
        _ = a := by rw [hxx]; group
    have hxex : x * (a * (x * a * x⁻¹)) * x⁻¹ = a * (x * a * x⁻¹) := by
      calc x * (a * (x * a * x⁻¹)) * x⁻¹
          = (x * a * x⁻¹) * (x * (x * a * x⁻¹) * x⁻¹) := by group
        _ = (x * a * x⁻¹) * a := by rw [hxbx]
        _ = a * (x * a * x⁻¹) := hab.symm
    have hee : (a * (x * a * x⁻¹)) * (a * (x * a * x⁻¹)) = 1 := by
      calc (a * (x * a * x⁻¹)) * (a * (x * a * x⁻¹))
          = a * ((x * a * x⁻¹) * a) * (x * a * x⁻¹) := by group
        _ = a * (a * (x * a * x⁻¹)) * (x * a * x⁻¹) := by rw [← hab]
        _ = (a * a) * ((x * a * x⁻¹) * (x * a * x⁻¹)) := by group
        _ = 1 := by rw [haa, hbb]; group
    have he1 : a * (x * a * x⁻¹) ≠ 1 := by
      intro heq
      have hba : x * a * x⁻¹ = a := by
        calc x * a * x⁻¹ = a⁻¹ * (a * (x * a * x⁻¹)) := by group
          _ = a⁻¹ * 1 := by rw [heq]
          _ = a := by rw [sec63P_inv_eq haord]; group
      have haI' : a ∈ CFSG.conjugate I x := by rw [← hba]; exact hbI'
      exact hag (hcomm g hgI a haI').symm
    have hxe : a * (x * a * x⁻¹) * x = x * (a * (x * a * x⁻¹)) := by
      calc a * (x * a * x⁻¹) * x
          = (x * (a * (x * a * x⁻¹)) * x⁻¹) * x := by rw [hxex]
        _ = x * (a * (x * a * x⁻¹)) := by rw [mul_assoc, inv_mul_cancel, mul_one]
    have hay : a * y = y * a := Subgroup.mem_centralizer_singleton_iff.mp ha.2
    have hby : (x * a * x⁻¹) * y = y * (x * a * x⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hI'.1 hbI')
    have hye : a * (x * a * x⁻¹) * y = y * (a * (x * a * x⁻¹)) := by
      calc a * (x * a * x⁻¹) * y = a * ((x * a * x⁻¹) * y) := by group
        _ = a * (y * (x * a * x⁻¹)) := by rw [hby]
        _ = (a * y) * (x * a * x⁻¹) := by group
        _ = (y * a) * (x * a * x⁻¹) := by rw [hay]
        _ = y * (a * (x * a * x⁻¹)) := by group
    have hgb : g * (x * a * x⁻¹) = (x * a * x⁻¹) * g :=
      hcomm g hgI (x * a * x⁻¹) hbI'
    have hez : a * (x * a * x⁻¹) * g ≠ g * (a * (x * a * x⁻¹)) := by
      intro heq
      have h1 : a * g * (x * a * x⁻¹) = g * a * (x * a * x⁻¹) := by
        calc a * g * (x * a * x⁻¹) = a * (g * (x * a * x⁻¹)) := by group
          _ = a * ((x * a * x⁻¹) * g) := by rw [hgb]
          _ = a * (x * a * x⁻¹) * g := by group
          _ = g * (a * (x * a * x⁻¹)) := heq
          _ = g * a * (x * a * x⁻¹) := by group
      exact hag (mul_right_cancel h1)
    have heord : orderOf (a * (x * a * x⁻¹)) = 2 := by
      apply orderOf_eq_prime
      · simpa [pow_two] using hee
      · exact he1
    exact ⟨a * (x * a * x⁻¹), g, heord, hxe, hye,
      (fstarLayer y).mul_mem (le_fstarLayer hI hIF ha.1) (le_fstarLayer hI' hI'F hbI'),
      le_fstarLayer hI hIF hgI, hez⟩

end CFSG.OddStandard.SmallF3.Omega

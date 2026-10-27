module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_lbal_step [Finite G] (hLB : AschLBalance G) (hA2 : AschA2 G) {v x u : G}
    {D : Subgroup G} (hv : orderOf v = 2) (hx : orderOf x = 2) (hu : orderOf u = 2)
    (hxv : x * v = v * x) (hDv : IsComponentIn D (centralizer ({v} : Set G)))
    (hDF : InFStar D) (huD : u ∈ D) (hne : CFSG.conjugate D x ≠ D) :
    ∃ I : Subgroup G, IsComponentIn I (centralizer ({u} : Set G)) ∧ InFStar I ∧
      CFSG.conjugate D x ≤ I ⊔ CFSG.conjugate I v := by
  have hx_mem : x ∈ centralizer ({v} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxv
  have hD' : IsComponentIn (CFSG.conjugate D x) (centralizer ({v} : Set G)) :=
    hDv.conjugate hx_mem
  have hD'F : InFStar (CFSG.conjugate D x) := hDF.conjugate x
  have hcomm : ∀ a ∈ D, ∀ b ∈ CFSG.conjugate D x, a * b = b * a :=
    hDv.commute_of_ne hD' hne.symm
  have huv : v * u = u * v :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hDv.1 huD)).symm
  have hD'leCu : CFSG.conjugate D x ≤ centralizer ({u} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcomm u huD b hb).symm
  have hle : CFSG.conjugate D x ≤ centralizer ({v, u} : Set G) := by
    rw [centralizer_pair_eq_inf]
    exact le_inf hD'.1 hD'leCu
  have hH' : centralizer ({v, u} : Set G) ≤ centralizer ({v} : Set G) := by
    rw [centralizer_pair_eq_inf]
    exact inf_le_left
  have hD'pair : IsComponentIn (CFSG.conjugate D x) (centralizer ({v, u} : Set G)) :=
    hD'.mono hle hH'
  obtain ⟨I, hI, hleI⟩ := hLB v u hv hu huv (CFSG.conjugate D x) hD'pair
  exact ⟨I, hI, hA2 v u hv hu huv (CFSG.conjugate D x) I hD'pair hI hleI hD'F, hleI⟩

end CFSG.OddStandard.SmallF3.Omega

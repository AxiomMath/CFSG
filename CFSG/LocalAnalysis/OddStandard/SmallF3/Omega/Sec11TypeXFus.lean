module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L118A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem t11_no_conj_i2m [Finite G] (hp : Asc82Pre11) {t : G} {L S : Subgroup G} {z : G}
    {K1 K2 : Subgroup G} (hctx : Sec10Ctx G t L S z K1 K2) (hyp : Hyp111 t S L) {u : G}
    (huL : u ∈ L) (hu : InducesTypeSome L u 5 1 2 (-1)) :
    ¬ ∃ k : G, k⁻¹ * t * k = t * u := by
  rintro ⟨k, hk⟩
  obtain ⟨hpsp, htC, -⟩ := hp.basic G t L S z hctx.toSec10Z
  obtain ⟨u0, hu0B, hu02, hu0ty, hu0n⟩ := sec11A_exists_u0 hp hctx
  obtain ⟨l, hl, hlu⟩ := hp.facts.factsC.i2m G L hpsp u0 u (secB_le_L S L hu0B) huL hu0ty hu
  have hlt : l * t = t * l := Subgroup.mem_centralizer_iff.mp htC l hl
  have hconj : (k * l⁻¹)⁻¹ * t * (k * l⁻¹) = t * u0 := by
    rw [← hlu] at hk
    calc (k * l⁻¹)⁻¹ * t * (k * l⁻¹) = l * (k⁻¹ * t * k) * l⁻¹ := by group
      _ = l * (t * (l⁻¹ * u0 * l)) * l⁻¹ := by rw [hk]
      _ = (l * t) * l⁻¹ * u0 := by group
      _ = (t * l) * l⁻¹ * u0 := by rw [hlt]
      _ = t * u0 := by group
  have hA : t * u0 ∈ secA t S L :=
    (secA t S L).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))
      (Subgroup.mem_sup_left hu0B)
  have hTop : t * u0 ∈ conjClassIn ⊤ t :=
    ⟨(k * l⁻¹)⁻¹, Subgroup.mem_top _, by rw [inv_inv]; exact hconj.symm⟩
  rcases hp.r10.l1011 G t L S z K1 K2 hctx with h | ⟨-, hcls, hM, -, -⟩
  · exact sec11_not_alt1 hyp h
  · have hmem : t * u0 ∈ conjClassIn (secM t S L) t := by
      rw [← hcls]
      exact ⟨hTop, hA⟩
    rw [hM] at hmem
    rcases hmem with h1 | ⟨m, hm, hmeq⟩
    · have hu01 : u0 = 1 := by
        have h1' : t * u0 = t * 1 := by rw [mul_one]; exact h1
        exact mul_left_cancel h1'
      rw [hu01, orderOf_one] at hu02
      omega
    · obtain ⟨-, hmL⟩ := hm
      have hmt : m * t = t * m := Subgroup.mem_centralizer_iff.mp htC m hmL
      have hu0eq : u0 = m * z * m⁻¹ := by
        have e : t * u0 = t * (m * z * m⁻¹) := by
          rw [hmeq]
          calc m * (t * z) * m⁻¹ = (m * t) * z * m⁻¹ := by group
            _ = (t * m) * z * m⁻¹ := by rw [hmt]
            _ = t * (m * z * m⁻¹) := by group
        exact mul_left_cancel e
      exact hu0n (hu0eq ▸ IsI4PlusIn.conj_of_mem hctx.toSec10Z.pocket hmL)

end CFSG.OddStandard.SmallF3.Omega

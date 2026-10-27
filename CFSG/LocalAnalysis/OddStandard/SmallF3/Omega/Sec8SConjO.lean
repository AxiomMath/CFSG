module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8Fink
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11S1111Odd

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

variable {G : Type} [Group G]

theorem sec8s_conj_oddCore [Finite G] {t : G} {L S : Subgroup G} {z g : G} {B E : Subgroup G}
    (hE : Sec8E G t L S z g B E) {y : G} (hyt : y * t = t * y)
    (hyB : y ∈ normalizer (B : Set G)) :
    ∃ o ∈ oddCoreIn (Nsub8 t B), o⁻¹ * y ∈ normalizer (E : Set G) := by
  classical
  set O : Subgroup G := oddCoreIn (Nsub8 t B) with hO
  set M : Subgroup G := E ⊔ O with hM
  have hyZ : y ∈ normalizer (zpowers t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have ht : MulAut.conj y t = t := by
      rw [MulAut.conj_apply, hyt]
      group
    have hmap : (zpowers t).map (MulAut.conj y).toMonoidHom = zpowers t := by
      rw [MonoidHom.map_zpowers]
      show zpowers (MulAut.conj y t) = zpowers t
      rw [ht]
    simpa [MulEquiv.toMonoidHom_eq_coe] using hmap
  have hyN : y ∈ Nsub8 t B := by
    show y ∈ normalizer ((zpowers t ⊔ B : Subgroup G) : Set G)
    exact Subgroup.inf_normalizer_le_normalizer_sup (zpowers t) B
      (Subgroup.mem_inf.mpr ⟨hyZ, hyB⟩)
  have hON : O ≤ Nsub8 t B := by
    rw [hO]; exact (oddCoreIn_normal (Nsub8 t B)).1
  have hOnorm : (O.subgroupOf (Nsub8 t B)).Normal := by
    rw [hO]; exact (oddCoreIn_normal (Nsub8 t B)).2
  have hOnormN : Nsub8 t B ≤ normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON).mp hOnorm
  have hMN : M ≤ Nsub8 t B := by
    rw [hM]
    exact sup_le hE.le_N (oddCoreIn_normal (Nsub8 t B)).1
  have hMnormN : (M.subgroupOf (Nsub8 t B)).Normal := by
    rw [hM, hO]
    exact hE.normal
  have hMn : Nsub8 t B ≤ normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMN).mp hMnormN
  have hyM : y ∈ normalizer (M : Set G) := hMn hyN
  let f : G →* G := (MulAut.conj y).toMonoidHom
  let E' : Subgroup G := E.map f
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (p := 2) (n := 8) hE.elem.2
  have hE'2 : IsPGroup 2 E' := by
    show IsPGroup 2 (E.map f)
    exact hE2.map f
  have hyO : y ∈ normalizer (O : Set G) := hOnormN hyN
  have hOmap : O.map f = O := by
    simpa [f] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyO)
  have hMmap : M.map f = M := by
    simpa [f] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hyM)
  have hE'O : E' ⊔ O = M := by
    calc E' ⊔ O = E.map f ⊔ O.map f := by
          rw [show E' = E.map f from rfl, hOmap]
      _ = (E ⊔ O).map f := (Subgroup.map_sup E O f).symm
      _ = M.map f := by rw [hM]
      _ = M := hMmap
  have hE'M : E' ≤ M := by
    intro x hx
    rw [show E' = E.map f from rfl, Subgroup.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have heM : e ∈ M := Subgroup.mem_sup_left he
    have h := (Subgroup.mem_normalizer_iff.mp hyM e).mp heM
    simpa [f, MulAut.conj_apply] using h
  have hNn : ∀ x ∈ M, ∀ n ∈ O, x * n * x⁻¹ ∈ O := fun x hx n hn =>
    Subgroup.le_normalizer_iff.mp hOnormN x (hMN hx) n hn
  have hoddO : Odd (Nat.card O) := by
    rw [hO]; exact odd_card_oddCoreIn (Nsub8 t B)
  have hEsyl : IsSylow2Of E M :=
    sec11_isSylow2Of_of_sup_odd (P := E) (N := O) (X := M)
      hE2 le_sup_left le_sup_right hNn hoddO hM
  have hE'syl : IsSylow2Of E' M :=
    sec11_isSylow2Of_of_sup_odd (P := E') (N := O) (X := M)
      hE'2 hE'M le_sup_right hNn hoddO hE'O.symm
  obtain ⟨a, haM, ha⟩ := hEsyl.exists_conj_mem hE'syl
  have hay : a⁻¹ * y ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 : f w ∈ E' ↔ w ∈ E := by
      show f w ∈ E.map f ↔ w ∈ E
      exact Subgroup.mem_map_iff_mem (f := f)
        (by simpa [f] using (MulAut.conj y).injective)
    have hfw : f w = y * w * y⁻¹ := by simp [f, MulAut.conj_apply]
    rw [hfw] at h1
    have h2 := ha (y * w * y⁻¹)
    have h3 : a⁻¹ * (y * w * y⁻¹) * a = (a⁻¹ * y) * w * (a⁻¹ * y)⁻¹ := by group
    rw [h3] at h2
    exact h1.symm.trans h2
  have hOnormM : M ≤ normalizer (O : Set G) := hMN.trans hOnormN
  have hEnO : E ≤ normalizer (O : Set G) := le_sup_left.trans hOnormM
  have haMul : a ∈ ((E : Set G) * (O : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right E O hEnO]
    exact haM
  rw [Set.mem_mul] at haMul
  obtain ⟨e₀, he₀, o, ho, heo⟩ := haMul
  have he₀M : e₀ ∈ M := Subgroup.mem_sup_left he₀
  have ho' : e₀ * o * e₀⁻¹ ∈ O :=
    (Subgroup.mem_normalizer_iff.mp (hOnormM he₀M) o).mp ho
  have ha_eq : (e₀ * o * e₀⁻¹) * e₀ = a := by rw [← heo]; group
  refine ⟨e₀ * o * e₀⁻¹, ?_, ?_⟩
  · exact ho'
  · have hconj : (e₀ * o * e₀⁻¹)⁻¹ * y = e₀ * (a⁻¹ * y) := by
      rw [← ha_eq]; group
    rw [hconj]
    exact (normalizer (E : Set G)).mul_mem
      ((Subgroup.le_normalizer (H := E)) he₀) hay

end CFSG.OddStandard.SmallF3.Omega

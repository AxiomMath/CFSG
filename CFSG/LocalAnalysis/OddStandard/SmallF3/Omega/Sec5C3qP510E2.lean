module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510E
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qP510Cls

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
  {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {Q₁ Q₂ : Subgroup G} {a b : G}

theorem sec5p510_E_normal {E R : Subgroup G} (hle : E ≤ R) (hrel : E.relIndex R = 2) :
    ∀ d ∈ R, ∀ e ∈ E, d * e * d⁻¹ ∈ E := by
  haveI : (E.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two hrel
  intro d hd e he
  have hmem : (⟨d, hd⟩ : ↥R) * ⟨e, hle he⟩ * (⟨d, hd⟩ : ↥R)⁻¹ ∈ E.subgroupOf R :=
    Subgroup.Normal.conj_mem inferInstance _ (Subgroup.mem_subgroupOf.mpr he) _
  exact Subgroup.mem_subgroupOf.mp hmem

theorem sec5p510_conj_mem_ab (h : Sec510Ctx G t L S z r ρ B A φ) (hab : Sec510Ab t z a b φ A)
    {R : Subgroup G}
    (hE : ∀ d ∈ R, ∀ e ∈ sec5p510_E t a b, d * e * d⁻¹ ∈ sec5p510_E t a b)
    {d x : G} (hd : d ∈ R) (hdt : d * t = t * d) (hx : x = a ∨ x = b) :
    d * x * d⁻¹ = a ∨ d * x * d⁻¹ = b := by
  obtain ⟨-, hae, hbe⟩ := sec5p510_E_gens t a b
  have hx1 : x ∈ wclass φ 1 := by
    rcases hx with rfl | rfl
    · exact hab.mem₁
    · exact hab.mem₂
  have hxE : x ∈ sec5p510_E t a b := by
    rcases hx with rfl | rfl
    · exact hae
    · exact hbe
  have hconjE : d * x * d⁻¹ ∈ sec5p510_E t a b := hE d hd x hxE
  have hconjA : d * x * d⁻¹ ∈ A := sec5p510_E_le_A h hab hconjE
  have hxΔ : x ∈ conjClassIn (normalizer (A : Set G)) t := by
    rw [h.delta]
    exact Or.inr hx1
  obtain ⟨m, -, hxm⟩ := hxΔ
  have hg : ((d * m)⁻¹)⁻¹ * t * (d * m)⁻¹ = d * x * d⁻¹ := by
    rw [inv_inv, hxm]
    group
  have hΔ : d * x * d⁻¹ ∈ conjClassIn (normalizer (A : Set G)) t := by
    have := sec5p510_tG_inter_A h (g := (d * m)⁻¹) (by rw [hg]; exact hconjA)
    rwa [hg] at this
  rw [h.delta] at hΔ
  rcases sec5p510_E_inter_delta h hab hconjE hΔ with hxt | hxa | hxb
  · exfalso
    have hxt' : x = t := by
      have : d * x = d * t := by
        calc d * x = d * x * d⁻¹ * d := by group
          _ = t * d := by rw [hxt]
          _ = d * t := hdt.symm
      exact mul_left_cancel this
    rw [hxt'] at hx1
    exact Set.disjoint_left.mp (h.model.perm.disjoint_wclass (by norm_num : (1 : ℕ) ≠ 6)) hx1
      h.model.t_mem_wclass
  · exact Or.inl hxa
  · exact Or.inr hxb

private theorem sec5p510_closure_comm {s : Set G} (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    ∀ x ∈ Subgroup.closure s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
  have h1 : ∀ x ∈ s, ∀ y ∈ Subgroup.closure s, x * y = y * x := by
    intro x hx y hy
    have hle : Subgroup.closure s ≤ centralizer ({x} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro w hw
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hs w hw x hx
    have := hle hy
    rw [Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  intro x hx y hy
  have hle : Subgroup.closure s ≤ centralizer ({y} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact h1 w hw y hy
  have := hle hx
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this

theorem sec5p510_false_of_centralizes (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6)
    (h4 : Asc82FactReflCentQ6) (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A) (hR16 : Nat.card ↥(sec5p510_R S Q₁ Q₂) = 16)
    {d : G} (hdR : d ∈ sec5p510_R S Q₁ Q₂) (hdE : d ∉ sec5p510_E t a b)
    (hdt : d * t = t * d) (hda : d * a = a * d) (hdb : d * b = b * d) : False := by
  have hER := sec5p510_E_le_R hy h4 h hQ hab
  have hE8 := sec5p510_card_E h hab
  have hEd : sec5p510_E t a b ≤ centralizer ({d} : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hx with hx | hx | hx <;> rw [hx]
    · exact hdt.symm
    · exact hda.symm
    · exact hdb.symm
  let s : Set G := (sec5p510_E t a b : Set G) ∪ {d}
  have hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact sec5p510_A_comm h (sec5p510_E_le_A h hab hx) (sec5p510_E_le_A h hab hy)
    · rw [Set.mem_singleton_iff.mp hy]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEd hx)
    · rw [Set.mem_singleton_iff.mp hx]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hEd hy)).symm
    · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
  have hcomm := sec5p510_closure_comm hs
  have hEE' : sec5p510_E t a b ≤ Subgroup.closure s :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hdE' : d ∈ Subgroup.closure s := Subgroup.subset_closure (Or.inr rfl)
  have hE'R : Subgroup.closure s ≤ sec5p510_R S Q₁ Q₂ := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (hx | hx)
    · exact hER hx
    · rw [Set.mem_singleton_iff.mp hx]
      exact hdR
  have hdvd1 := Subgroup.card_dvd_of_le hEE'
  have hdvd2 := Subgroup.card_dvd_of_le hE'R
  rw [hE8] at hdvd1
  rw [hR16] at hdvd2
  have hpos : 0 < Nat.card ↥(Subgroup.closure s) := Nat.card_pos
  obtain ⟨m, hm⟩ := hdvd1
  have hm_le : 8 * m ≤ 16 := by
    rw [← hm]
    exact Nat.le_of_dvd (by norm_num) hdvd2
  have hm0 : m ≠ 0 := by
    rintro rfl
    omega
  have hRE' : Subgroup.closure s = sec5p510_R S Q₁ Q₂ := by
    have hm2 : m = 1 ∨ m = 2 := by omega
    rcases hm2 with rfl | rfl
    · exfalso
      have heq : sec5p510_E t a b = Subgroup.closure s :=
        Subgroup.eq_of_le_of_card_ge hEE' (by omega)
      exact hdE (heq ▸ hdE')
    · exact Subgroup.eq_of_le_of_card_ge hE'R (by omega)
  have hcommR : ∀ x ∈ sec5p510_R S Q₁ Q₂, ∀ y ∈ sec5p510_R S Q₁ Q₂, x * y = y * x := by
    rw [← hRE']
    exact hcomm
  have hrel : (centralizer (L : Set G)).relIndex (sec5p510_R S Q₁ Q₂) = 8 := by
    have := sec5p510_R_card h.toSec5Ctx hQ hCS
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := (sec5p510_R_index hy hD h.toSec5Ctx hQ).2 hrel
  apply hxy
  rw [hcommR x hx y hy, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem sec5p510_swap (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (h4 : Asc82FactReflCentQ6)
    (hCS : S ⊓ centralizer (L : Set G) = zpowers t)
    (h : Sec510Ctx G t L S z r ρ B A φ) (hQ : Sec510Q G L z Q₁ Q₂)
    (hab : Sec510Ab t z a b φ A)
    (hrel : (sec5p510_E t a b).relIndex (sec5p510_R S Q₁ Q₂) = 2)
    {d : G} (hdR : d ∈ sec5p510_R S Q₁ Q₂) (hdE : d ∉ sec5p510_E t a b) :
    d * a * d⁻¹ = b ∧ d * b * d⁻¹ = a := by
  have hER := sec5p510_E_le_R hy h4 h hQ hab
  have hR16 : Nat.card ↥(sec5p510_R S Q₁ Q₂) = 16 := by
    have h1 := Subgroup.relIndex_mul_card (H := sec5p510_E t a b) (K := sec5p510_R S Q₁ Q₂)
    rw [inf_of_le_left hER, sec5p510_card_E h hab, hrel] at h1
    omega
  have hnorm := sec5p510_E_normal hER hrel
  have hdt : d * t = t * d :=
    Subgroup.mem_centralizer_singleton_iff.mp (h.sylow.1 hdR.1)
  have hda := sec5p510_conj_mem_ab h hab hnorm hdR hdt (Or.inl rfl)
  have hdb := sec5p510_conj_mem_ab h hab hnorm hdR hdt (Or.inr rfl)
  have hinj : ∀ x y : G, d * x * d⁻¹ = d * y * d⁻¹ → x = y := by
    intro x y hxy
    have := mul_right_cancel hxy
    exact mul_left_cancel this
  rcases hda with hda | hda <;> rcases hdb with hdb | hdb
  · exact absurd (hinj b a (hdb.trans hda.symm)) (Ne.symm hab.ne)
  · exfalso
    refine sec5p510_false_of_centralizes hy hD h4 hCS h hQ hab hR16 hdR hdE hdt ?_ ?_
    · calc d * a = d * a * d⁻¹ * d := by group
        _ = a * d := by rw [hda]
    · calc d * b = d * b * d⁻¹ * d := by group
        _ = b * d := by rw [hdb]
  · exact ⟨hda, hdb⟩
  · exact absurd (hinj a b (hda.trans hdb.symm)) hab.ne

end CFSG.OddStandard.SmallF3.Omega

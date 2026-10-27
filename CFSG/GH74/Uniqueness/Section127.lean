module

public import CFSG.GH74.Uniqueness.Section126Thompson
public import CFSG.GH74.Uniqueness.Section127Conj
public import CFSG.GH74.Uniqueness.Section126Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X} {c : Ctx12 Z M} {n i : ℕ}

theorem shears_of_mem_centralizer
    (S : ZDSetup X Z M) (h126 : Lemma126Stmt Z M) (h : LData c n i)
    {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) (hzu : u * c.z = c.z * u) :
    Shears Z M u := by
  by_contra hns
  obtain ⟨-, hrest⟩ := h126 c n i h u
    (Subgroup.mem_inf.mpr ⟨huD, Subgroup.mem_centralizer_singleton_iff.mpr hzu⟩) hu2
  obtain ⟨-, -, hc, hd⟩ := hrest hns
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  have hu1 : u * u = 1 := sec126_involution_mul_self hu2
  have hz1 : c.z * c.z = 1 := sec126_involution_mul_self hz2
  have huZ := S.sec126_not_mem_of_mem_dGrp c.htM huD
  have hne : u ≠ c.z := fun he => huZ (he ▸ c.hz)
  have huz2 : orderOf (u * c.z) = 2 := sec126_orderOf_mul_eq_two_of_commute hu1 hz1 hzu hne
  have hnc : ¬ IsConj u c.z := fun hc' => huZ (S.invariant.isConj_mem c.hz hc')
  have hcard := card_mul_card_centralizer_eq_of_single_class hu2 hz2 huz2 hnc hc hd
  have hle : centralizer ({u} : Set X) ⊓ centralizer ({c.z} : Set X) ≤
      centralizer ({u * c.z} : Set X) := by
    intro g hg
    obtain ⟨hgu, hgz⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hgu hgz ⊢
    calc g * (u * c.z) = (g * u) * c.z := by rw [mul_assoc]
      _ = (u * g) * c.z := by rw [hgu]
      _ = u * (g * c.z) := by rw [mul_assoc]
      _ = u * (c.z * g) := by rw [hgz]
      _ = (u * c.z) * g := by rw [mul_assoc]
  have hcard' : Nat.card X * Nat.card ↥(centralizer ({u} : Set X) ⊓
        centralizer ({c.z} : Set X)) ≤
      Nat.card ↥(centralizer ({u} : Set X)) * Nat.card ↥(centralizer ({c.z} : Set X)) := by
    rw [← hcard]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
  have hcomm := commute_of_card_inf_le hzu hcard'
  have hZc : Z ⊆ (centralizer ({u} : Set X) : Set X) := by
    intro y hy
    have hconj : IsConj c.z y := by
      have := S.eq_conjClass c.hz
      rw [this] at hy
      exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hconj).symm
  have hle2 : Subgroup.closure Z ≤ centralizer ({u} : Set X) := (Subgroup.closure_le _).mpr hZc
  rw [S.gen] at hle2
  have hu1' : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu2
    omega
  exact S.sec126_centralizer_singleton_ne_top hu1' (top_le_iff.mp hle2)

theorem shears_of_involution
    (S : ZDSetup X Z M) (h126 : Lemma126Stmt Z M) (h : LData c n i)
    {u : X} (huD : u ∈ c.D) (hu2 : orderOf u = 2) : Shears Z M u := by
  obtain ⟨d, hd, hdu⟩ := S.exists_conj_centralizer_of_involution c.ht c.htM c.hz c.hzM huD hu2
  have hdM : d ∈ M := (Subgroup.mem_inf.mp hd).1
  have hu₁D : d⁻¹ * u * d ∈ c.D := c.D.mul_mem (c.D.mul_mem (c.D.inv_mem hd) huD) hd
  have hsh := shears_of_mem_centralizer S h126 h hu₁D (sec126_orderOf_conj_eq_two hu2 d)
    (Subgroup.mem_centralizer_singleton_iff.mp hdu)
  exact Shears.sec126_of_conj h hdM hsh

theorem lemma127_core (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M) (h : LData c n i) {u : X}
    (huD : u ∈ c.D) (hu2 : orderOf u = 2) (hsh : Shears Z M u) {u' z' : X} (hu'c : IsConj u u')
    (hz'Z : z' ∈ Z) (hz'M : z' ∈ M) (hcomm : u' * z' = z' * u') : IsConj u (u' * z') := by
  have hall := Shears.sec126_all_conj h124 h huD hu2 hsh
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  have hz'H : z' ∈ zHull Z M := Subgroup.subset_closure ⟨hz'Z, hz'M⟩
  have hu'M : u' ∈ M :=
    S.prodDisc.centralizer_le_of_mem hz'Z hz'M (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
  obtain ⟨m, hm, hmu⟩ := S.sec126_exists_conj_of_isConj huM hu2 hu'M hu'c
  have hz₁H : m * z' * m⁻¹ ∈ zHull Z M := h.sec126_conj_mem_zHull' hm hz'H
  have hz₁1 : m * z' * m⁻¹ ≠ 1 := by
    intro h1
    have h2 : z' = 1 := by
      calc z' = m⁻¹ * (m * z' * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    have h3 := S.invariant.1 z' hz'Z
    rw [h2, orderOf_one] at h3
    omega
  have hz₁c : u * (m * z' * m⁻¹) = (m * z' * m⁻¹) * u := by
    calc u * (m * z' * m⁻¹) = m * (u' * z') * m⁻¹ := by rw [← hmu]; group
      _ = m * (z' * u') * m⁻¹ := by rw [hcomm]
      _ = (m * z' * m⁻¹) * u := by rw [← hmu]; group
  have hmem : u * (m * z' * m⁻¹) ∈ deltaSet Z M u :=
    ⟨m * z' * m⁻¹, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_centralizer_singleton_iff.mpr hz₁c.symm, hz₁H⟩, hz₁c⟩
  have hne : u * (m * z' * m⁻¹) ≠ u := by
    intro h1
    apply hz₁1
    have h2 : u * (m * z' * m⁻¹) = u * 1 := by rw [h1, mul_one]
    exact mul_left_cancel h2
  have h1 := hall _ hmem hne
  have h2 : IsConj (u * (m * z' * m⁻¹)) (u' * z') := by
    refine isConj_iff.mpr ⟨m⁻¹, ?_⟩
    rw [inv_inv, ← hmu]
    group
  exact h1.trans h2

theorem ZDSetup.lemma127
    (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M)
    (h126 : Lemma126Stmt Z M) : Lemma127Stmt Z M := by
  intro c n i h u hu hu2
  have hsh := shears_of_involution S h126 h hu hu2
  refine ⟨hsh, ?_⟩
  intro u' z' hu'c hz'c hcomm
  have hz'Z : z' ∈ Z := S.invariant.isConj_mem c.hz hz'c.symm
  obtain ⟨g, hg⟩ := S.prodDisc.exists_conj_mem_subgroup S.invariant hz'Z
  have hcomm' : g⁻¹ * u' * g * (g⁻¹ * z' * g) = g⁻¹ * z' * g * (g⁻¹ * u' * g) := by
    calc g⁻¹ * u' * g * (g⁻¹ * z' * g) = g⁻¹ * (u' * z') * g := by group
      _ = g⁻¹ * (z' * u') * g := by rw [hcomm]
      _ = g⁻¹ * z' * g * (g⁻¹ * u' * g) := by group
  have hu'' : IsConj u (g⁻¹ * u' * g) :=
    hu'c.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
  have key := lemma127_core S h124 h hu hu2 hsh hu'' (S.invariant.2 z' hz'Z g) hg hcomm'
  have e : g⁻¹ * u' * g * (g⁻¹ * z' * g) = g⁻¹ * (u' * z') * g := by group
  rw [e] at key
  exact key.trans (isConj_iff.mpr ⟨g, by group⟩)

end CFSG.GH74.Uniqueness

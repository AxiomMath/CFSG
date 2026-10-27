module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GConj

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

structure L34GOrb (u x : G) (K : Subgroup G) (𝒪 : Set (Subgroup G)) : Prop where
  invol : orderOf x = 2
  xK : ∀ k ∈ K, x * k = k * x
  comp : ∀ J ∈ 𝒪, IsComponentIn J (centralizer ({u} : Set G))
  inFStar : ∀ J ∈ 𝒪, InFStar J
  conj : ∀ J ∈ 𝒪, ∀ t ∈ K ⊔ zpowers x, CFSG.conjugate J t ∈ 𝒪

theorem l34g_orb_of_component {u x : G} {K I : Subgroup G}
    (hI : IsComponentIn I (centralizer ({u} : Set G))) (hIF : InFStar I) (hx : orderOf x = 2)
    (hxu : x * u = u * x) (hKu : ∀ k ∈ K, k * u = u * k) (hxK : ∀ k ∈ K, x * k = k * x) :
    L34GOrb u x K {J | ∃ t ∈ K ⊔ zpowers x, J = CFSG.conjugate I t} := by
  have hKc : K ≤ centralizer ({u} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hKu k hk
  have hxc : x ∈ centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxu
  have hTc : K ⊔ zpowers x ≤ centralizer ({u} : Set G) :=
    sup_le hKc (Subgroup.zpowers_le.mpr hxc)
  refine ⟨hx, hxK, ?_, ?_, ?_⟩
  · rintro J ⟨t, ht, rfl⟩
    exact hI.conjugate (hTc ht)
  · rintro J ⟨t, ht, rfl⟩
    exact hIF.conjugate t
  · rintro J ⟨t, ht, rfl⟩ s hs
    refine ⟨t * s, (K ⊔ zpowers x).mul_mem ht hs, ?_⟩
    exact l34g_conjugate_conjugate I t s

variable {u x : G} {K : Subgroup G} {𝒪 : Set (Subgroup G)}

theorem L34GOrb.T_normalizes (hO : L34GOrb u x K 𝒪) {t : G} (ht : t ∈ K ⊔ zpowers x) :
    t ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) := by
  have key : ∀ s ∈ K ⊔ zpowers x, ∀ a ∈ sSup 𝒪, s * a * s⁻¹ ∈ sSup 𝒪 := by
    intro s hs a ha
    have hle : sSup 𝒪 ≤ (sSup 𝒪).comap (MulAut.conj s).toMonoidHom := by
      apply sSup_le
      intro J hJ j hj
      rw [Subgroup.mem_comap]
      refine le_sSup (hO.conj J hJ s⁻¹ ((K ⊔ zpowers x).inv_mem hs)) ?_
      rw [conjugate_inv_eq_map_conj]
      exact Subgroup.mem_map.mpr ⟨j, hj, rfl⟩
    have hmem := hle ha
    rw [Subgroup.mem_comap] at hmem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  rw [Subgroup.mem_normalizer_iff]
  intro e
  constructor
  · intro he
    exact key t ht e he
  · intro he
    have h := key t⁻¹ ((K ⊔ zpowers x).inv_mem ht) (t * e * t⁻¹) he
    rwa [show t⁻¹ * (t * e * t⁻¹) * (t⁻¹)⁻¹ = e by group] at h

theorem L34GOrb.commute [Finite G] (hO : L34GOrb u x K 𝒪) {J J' : Subgroup G} (hJ : J ∈ 𝒪)
    (hJ' : J' ∈ 𝒪) (hne : J ≠ J') : ∀ a ∈ J, ∀ b ∈ J', a * b = b * a := by
  intro a ha b hb
  exact (hO.comp J hJ).commute_of_ne (hO.comp J' hJ') hne a ha b hb

theorem L34GOrb.normal [Finite G] (hO : L34GOrb u x K 𝒪) {J : Subgroup G} (hJ : J ∈ 𝒪) :
    ∀ e ∈ sSup 𝒪, ∀ j ∈ J, e * j * e⁻¹ ∈ J := by
  have hle : sSup 𝒪 ≤ normalizer (J : Set G) := by
    apply sSup_le
    intro J' hJ'
    by_cases hEq : J' = J
    · rw [hEq]
      exact Subgroup.le_normalizer
    · intro a ha
      exact Subgroup.centralizer_le_normalizer (J : Set G) (by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (hO.commute hJ' hJ hEq a ha b hb).symm)
  intro e he j hj
  have hnorm := hle he
  rw [Subgroup.mem_normalizer_iff] at hnorm
  exact (hnorm j).1 hj

theorem L34GOrb.perfect_member [Finite G] (hO : L34GOrb u x K 𝒪) {J : Subgroup G} (hJ : J ∈ 𝒪) :
    ⁅J, J⁆ = J :=
  Subgroup.isPerfect_iff.mp (hO.comp J hJ).isQuasisimple.1

theorem L34GOrb.perfect [Finite G] (hO : L34GOrb u x K 𝒪) : ⁅sSup 𝒪, sSup 𝒪⁆ = sSup 𝒪 := by
  apply le_antisymm
  · exact Subgroup.commutator_le_self (sSup 𝒪)
  · apply sSup_le
    intro J hJ
    rw [← hO.perfect_member hJ]
    exact Subgroup.commutator_mono (le_sSup hJ) (le_sSup hJ)

theorem L34GOrb.central_iff [Finite G] (hO : L34GOrb u x K 𝒪) {J : Subgroup G} (hJ : J ∈ 𝒪)
    {j : G} (hj : j ∈ J) :
    (∀ e ∈ sSup 𝒪, e * j = j * e) ↔ ∀ g ∈ J, g * j = j * g := by
  constructor
  · intro h g hg
    exact h g (le_sSup hJ hg)
  · intro h e he
    have hle : sSup 𝒪 ≤ centralizer ({j} : Set G) := by
      apply sSup_le
      intro J' hJ'
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hEq : J' = J
      · rw [hEq] at ha
        exact h a ha
      · exact hO.commute hJ' hJ hEq a ha j hj
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)

end CFSG.OddStandard.SmallF3.Omega

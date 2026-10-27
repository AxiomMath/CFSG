module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Sylow

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec10Z_isolated [Finite G] {S : Subgroup G} {t z : G} (hS : IsSylow2Of S ⊤)
    (hSz : ∀ s ∈ S, s * z = z * s) (htS : t ∈ S) (ht2 : t * t = 1) (hz2 : z * z = 1)
    (hsc : ∀ h ∈ centralizer ({z} : Set G), h⁻¹ * t * h ∈ S → h⁻¹ * t * h = t) :
    ∀ h ∈ centralizer ({z} : Set G),
      (h * t * h⁻¹) * t = t * (h * t * h⁻¹) → h * t * h⁻¹ = t := by
  set H : Subgroup G := centralizer ({z} : Set G) with hH
  intro h hh hut
  let u : G := h * t * h⁻¹
  have hu : u = h * t * h⁻¹ := rfl
  have hS_le_H : S ≤ H := by
    intro s hs
    rw [hH, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (hSz s hs).symm
  have hrel : S.relIndex H * H.relIndex ⊤ = S.relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex S H ⊤ hS_le_H le_top
  have hSH : IsSylow2Of S H := by
    refine ⟨hS_le_H, hS.2.1, ?_⟩
    intro h2
    exact hS.2.2 (hrel ▸ h2.mul_right (H.relIndex ⊤))
  have hHt : t ∈ H := hS_le_H htS
  have hHzC : z ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rfl
  have hHz : z ∈ H := hH.symm ▸ hHzC
  have hHu : u ∈ H := by
    rw [hu]
    exact H.mul_mem (H.mul_mem hh hHt) (H.inv_mem hh)
  have htz : Commute t z := hSz t htS
  have hhz : Commute h z :=
    (Subgroup.mem_centralizer_iff.mp (hH ▸ hh) z (Set.mem_singleton z)).symm
  have hcomm_ht : Commute (h * t) z := hhz.mul_left htz
  have hcomm_hinv : Commute h⁻¹ z := hhz.inv_left
  have huz : Commute u z := by
    rw [hu]
    exact hcomm_ht.mul_left hcomm_hinv
  have hut' : u * t = t * u := by
    rw [hu]
    exact hut
  have htu : Commute t u := hut'.symm
  have hu2 : u * u = 1 := by
    rw [hu, show (h * t * h⁻¹) * (h * t * h⁻¹) = h * (t * t) * h⁻¹ by group]
    rw [ht2, mul_one, mul_inv_cancel]
  have hcomm_all : ∀ a ∈ ({t, u, z} : Set G), ∀ b ∈ ({t, u, z} : Set G), Commute a b := by
    intro a ha b hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
    · subst a; subst b; exact Commute.refl t
    · subst a; subst b; exact htu
    · subst a; subst b; exact htz
    · subst a; subst b; exact hut'
    · subst a; subst b; exact Commute.refl u
    · subst a; subst b; exact huz
    · subst a; subst b; exact htz.symm
    · subst a; subst b; exact huz.symm
    · subst a; subst b; exact Commute.refl z
  let E : Subgroup G := Subgroup.closure ({t, u, z} : Set G)
  have hcomm_gen : ({t, u, z} : Set G).Pairwise Commute :=
    fun a ha b hb _ => hcomm_all a ha b hb
  haveI : IsMulCommutative E := isMulCommutative_closure hcomm_gen
  have hsq : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun y _ => y * y = 1) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact ht2
      · exact hu2
      · exact hz2
    · exact one_mul 1
    · intro x y hx hy hx2 hy2
      have hxy : Commute x y :=
        Subgroup.mul_comm_of_mem_isMulCommutative (H := E) hx hy
      calc (x * y) * (x * y) = x * x * (y * y) := (hxy.mul_mul_mul_comm x y).symm
        _ = 1 * 1 := by rw [hx2, hy2]
        _ = 1 := one_mul 1
    · intro x hx hx2
      rw [← mul_inv_rev, hx2, inv_one]
  have hE2 : IsPGroup 2 E := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro x
    refine ⟨1, ?_⟩
    have hx2 : (x : G) * (x : G) = 1 := hsq x x.2
    have hxx : x * x = (1 : ↥E) := by
      apply Subtype.ext
      simpa using hx2
    simpa [pow_two] using hxx
  have hE_le_H : E ≤ H := by
    change Subgroup.closure ({t, u, z} : Set G) ≤ H
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hHt
    · exact hHu
    · exact hHz
  obtain ⟨Q, hQ, hEQ⟩ := exists_isSylow2Of_ge hE2 hE_le_H
  obtain ⟨a, ha, hconj⟩ := hSH.exists_conj_mem hQ
  have htE : t ∈ E := Subgroup.subset_closure (k := ({t, u, z} : Set G)) (by simp)
  have huE : u ∈ E := Subgroup.subset_closure (k := ({t, u, z} : Set G)) (by simp)
  have htQ : t ∈ Q := hEQ htE
  have hta : a⁻¹ * t * a = t := hsc a (hH ▸ ha) ((hconj t).mp htQ)
  have huQ : u ∈ Q := hEQ huE
  have hconj_u : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) = a⁻¹ * u * a := by
    rw [hu]
    group
  have hmem_u : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) ∈ S := by
    rw [hconj_u]
    exact (hconj u).mp huQ
  have hha : h⁻¹ * a ∈ H := H.mul_mem (H.inv_mem hh) ha
  have hsc_u : (h⁻¹ * a)⁻¹ * t * (h⁻¹ * a) = t := hsc (h⁻¹ * a) (hH ▸ hha) hmem_u
  have hua : a⁻¹ * u * a = t := hconj_u ▸ hsc_u
  have hua' : a⁻¹ * u * a = a⁻¹ * t * a := by rw [hua, hta]
  have hut_eq : u = t := mul_left_cancel (mul_right_cancel hua')
  rw [hu] at hut_eq
  exact hut_eq

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UHSNoG
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.USylow

import CFSG.LocalAnalysis.OddStandard.SwapPartner.LemmaGCent
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.UD8

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdSec.SwapPattern

variable {G : Type} [Group G] {z : G} {ι ιd : Perm (Fin 10) →* G} {Kh : Subgroup G}

theorem HSCtx.isCyclic_of_isPGroup (C : HSCtx z ι ιd Kh) [Finite G] {U : Subgroup G}
    (hU : IsPGroup 2 U)
    (hUle : U ≤ centralizer ({z * ι τ₀} : Set G) ⊓ centralizer (Kh : Set G)) : IsCyclic ↥U := by
  classical
  let F := C.frame
  let g : G := gElt ιd
  let x : G := z * ι τ₀
  have h : D8Rel z g x := F.d8
  let D : Subgroup G := closure ({z, g} : Set G)
  let Y : Subgroup G := centralizer (Agrp ι : Set G) ⊓ centralizer ({x} : Set G)
  have hUY : U ≤ Y := by
    refine le_trans hUle ?_
    refine le_inf ?_ ?_
    · exact le_trans inf_le_right (Subgroup.centralizer_le C.khat.agrp_le)
    · exact inf_le_left
  have hzY : z ∈ Y := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro a ha
      obtain ⟨ρ, -, rfl⟩ := mem_Agrp_iff.mp ha
      exact (F.z_comm_sigma ρ).symm
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h.x_comm_z
  have hgY : g ∈ Y := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro a ha
      obtain ⟨ρ, -, rfl⟩ := mem_Agrp_iff.mp ha
      exact (F.g_comm ρ).symm
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h.x_comm_g
  have hDY : D ≤ Y := by
    change closure ({z, g} : Set G) ≤ Y
    rw [Subgroup.closure_le]
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact hzY
    · exact hgY
  have hmax : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Y → Nat.card ↥Q ≤ 2 ^ 3 := by
    intro Q hQ hQY
    have hQA : Q ≤ centralizer (Agrp ι : Set G) := le_trans hQY inf_le_left
    have hQx : Q ≤ centralizer ({x} : Set G) := le_trans hQY inf_le_right
    have hcard := C.h8 Q hQ hQA hQx
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num]
    exact hcard
  have hD : Nat.card ↥D = 2 ^ 3 := by
    change Nat.card ↥(closure ({z, g} : Set G)) = 2 ^ 3
    rw [h.card]
    norm_num
  obtain ⟨c, hcY, hc⟩ :=
    exists_conj_le_of_forall_card_le (Y := Y) (D := D) (U := U) (k := 3)
      hDY hD hmax hU hUY
  have hcx_mem : c ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp hcY).2
  let U' : Subgroup G := U.map (MulAut.conj c).toMonoidHom
  have hU'D : U' ≤ D := by
    change U.map (MulAut.conj c).toMonoidHom ≤ D
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    simpa using hc u hu
  have hconjx : ∀ u ∈ U, MulAut.conj c u ∈ centralizer ({x} : Set G) := by
    intro u hu
    have hux_mem : u ∈ centralizer ({x} : Set G) := (Subgroup.mem_inf.mp (hUle hu)).1
    rw [mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1 : Commute x c := (mem_centralizer_iff.mp hcx_mem) x rfl
    have h2 : Commute x u := (mem_centralizer_iff.mp hux_mem) x rfl
    have h3 : Commute x c⁻¹ := (mem_centralizer_iff.mp (inv_mem hcx_mem)) x rfl
    have hcomm : Commute (MulAut.conj c u) x :=
      Commute.mul_left (Commute.mul_left h1.symm h2.symm) h3.symm
    exact hcomm.symm
  have hconjK : ∀ u ∈ U, MulAut.conj c u ∈ centralizer (Kh : Set G) := by
    intro u hu
    have hux_mem : u ∈ centralizer (Kh : Set G) := (Subgroup.mem_inf.mp (hUle hu)).2
    rw [mem_centralizer_iff]
    intro k hk
    have hk' : c⁻¹ * k * c ∈ Kh := by
      simpa using C.conj_mem (inv_mem hcx_mem) hk
    have huk' : (c⁻¹ * k * c) * u = u * (c⁻¹ * k * c) :=
      (mem_centralizer_iff.mp hux_mem) (c⁻¹ * k * c) hk'
    show k * (c * u * c⁻¹) = (c * u * c⁻¹) * k
    calc k * (c * u * c⁻¹)
        = c * ((c⁻¹ * k * c) * u) * c⁻¹ := by group
      _ = c * (u * (c⁻¹ * k * c)) * c⁻¹ := by rw [huk']
      _ = (c * u * c⁻¹) * k := by group
  have hU'x : U' ≤ centralizer ({x} : Set G) := by
    change U.map (MulAut.conj c).toMonoidHom ≤ centralizer ({x} : Set G)
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    exact hconjx u hu
  have hU'K : U' ≤ centralizer (Kh : Set G) := by
    change U.map (MulAut.conj c).toMonoidHom ≤ centralizer (Kh : Set G)
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap]
    exact hconjK u hu
  have hU'D0 : U' ≤ centralizer ({x} : Set G) ⊓ centralizer (Kh : Set G) :=
    le_inf hU'x hU'K
  have hxD0 : x ∈ centralizer ({x} : Set G) ⊓ centralizer (Kh : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rfl
    · rw [mem_centralizer_iff]
      intro k hk
      exact ((mem_centralizer_iff.mp (C.khat.le hk)) x rfl).symm
  let S : Subgroup G := U' ⊔ Subgroup.zpowers x
  have hSD0 : S ≤ centralizer ({x} : Set G) ⊓ centralizer (Kh : Set G) := by
    change U' ⊔ Subgroup.zpowers x ≤ centralizer ({x} : Set G) ⊓ centralizer (Kh : Set G)
    exact sup_le hU'D0 (Subgroup.zpowers_le.mpr hxD0)
  have hSD : S ≤ D := by
    change U' ⊔ Subgroup.zpowers x ≤ D
    exact sup_le hU'D (Subgroup.zpowers_le.mpr h.x_mem)
  have hxS : x ∈ S := by
    change x ∈ U' ⊔ Subgroup.zpowers x
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hzS : z ∉ S := by
    intro hzS
    have hzK : z ∈ centralizer (Kh : Set G) := (Subgroup.mem_inf.mp (hSD0 hzS)).2
    exact C.not_centralizes_z fun k hk => ((mem_centralizer_iff.mp hzK) k hk).symm
  have hgS : g ∉ S := by
    intro hgS
    have hgK : g ∈ centralizer (Kh : Set G) := (Subgroup.mem_inf.mp (hSD0 hgS)).2
    exact C.not_centralizes_g fun k hk => ((mem_centralizer_iff.mp hgK) k hk).symm
  have hScyc : IsCyclic ↥S := by
    rcases h.subgroup_cases (S := S) hSD hxS hzS with hseq | hseq | hseq
    · rw [hseq]; infer_instance
    · exfalso
      have hgS' : g ∈ S := by
        rw [hseq]
        exact subset_closure (Set.mem_insert g {x})
      exact hgS hgS'
    · rw [hseq]; infer_instance
  haveI : IsCyclic ↥S := hScyc
  have hU'S : U' ≤ S := by
    change U' ≤ U' ⊔ Subgroup.zpowers x
    exact le_sup_left
  have hU'cyc : IsCyclic ↥U' := Subgroup.isCyclic_of_le hU'S
  have e : ↥U ≃* ↥U' :=
    U.equivMapOfInjective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective
  exact e.isCyclic.mpr hU'cyc

end CFSG.OddStandard.AltStdSec.SwapPartner

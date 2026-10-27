module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617P
public import CFSG.GH74.GLS.C3.Layer1.Th2P617M

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem false_of_adapted
    (hL34 : B_gen4_noL34_elem) (h102 : B_ivk_10_2) (hG : C3Hyp G)
    (hs : Th2Std x y K T S) (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7)))
    (hQ2 : pRank 2 ↥(T ⊓ CxK x K) ≤ 2) (h4 : 4 < Nat.card ↥(T ⊓ CxK x K))
    {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) {b : G} {J : Subgroup G}
    (hobs : Obstr52 B b J) (hbx : b ≠ x) (hPb : ∀ p ∈ T ⊓ K, p * b = b * p) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, E, z, hU, hES, hE2, hBdef, hzU, hz1, hzz, hzc, hzu, hP8⟩ := exists_dec617 hs h7 hB
  obtain ⟨eK⟩ := h7
  have hcen := centerlessBar_of_A7 ⟨eK⟩
  have hcd := hs.commDisj hcen
  have hE4 : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hE4.2.1
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hEQ : E ≤ T ⊓ CxK x K := hES.1
  have hUP : U ≤ T ⊓ K := hU.1
  have hUB : U ≤ B := hBdef ▸ le_sup_left
  have hEB : E ≤ B := hBdef ▸ le_sup_right
  obtain ⟨u, hu, e, he, hbue⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hBc u (hUB hu) q (hEB hq)) (hBdef ▸ hobs.mem : b ∈ U ⊔ E)
  have huc : ∀ p ∈ T ⊓ K, p * u = u * p := by
    intro p hp
    have h1 := hPb p hp
    rw [hbue] at h1
    have h2 : p * u * e = u * p * e := by
      calc p * u * e = p * (u * e) := by group
        _ = (u * e) * p := h1
        _ = u * (e * p) := by group
        _ = u * (p * e) := by rw [← hcd.comm p hp e (hEQ he)]
        _ = u * p * e := by group
    exact mul_right_cancel h2
  rcases hzu u (hUP hu) huc with hu1 | huz
  ·
    rw [hu1, one_mul] at hbue
    exact false_of_E hG hs ⟨eK⟩ hB hobs hES hEB hP8 hbx (hbue ▸ he)
  · by_cases he1 : e = 1
    · rw [huz, he1, mul_one] at hbue
      exact false_of_z hL34 h102 hG hs ⟨eK⟩ hQ2 h4 hB hobs hU hES hE2 hBdef hzU hz1 hzz hzc hzu hP8 hbue
    · rw [huz] at hbue
      exact false_of_zE hL34 h102 hG hs ⟨eK⟩ hQ2 hB hobs hU hES hE2 hBdef hzU hz1 hzc hzu hP8 he he1 hbue

end CFSG.GH74.GLS.Th2.Obs

module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1442a
public import CFSG.Quasithin.Vol2.Ch12Sec8OneA7Cert

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

namespace L1442

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx
open CFSG.Quasithin.H13.L1442.Ctx_F4

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx_F4 G T L V V₂ g a D)
include C

theorem false_of_concl4_F4 (hC4 : G112Concl4 (D.img (l32nH T V))) :
    False := by
  classical
  set H := C.g111 with hH
  obtain ⟨S', hS'syl, hXS', -⟩ := H.four
  have hS'Γ := L128P.isSylowTwoOf_of_stabilizer hS'syl H.odd_index
  have hS'v : ∀ s ∈ S', s (D.π a) = D.π a := fun s hs' =>
    MulAction.mem_stabilizer_iff.1 (hS'syl.1 hs').2
  obtain ⟨Up, hUpS, hUpv, hvUp, hcases⟩ :=
    H13.a7NatFact12813 D.V D.B _ S' (D.π a) hC4 H.alt H.nondegenerate H.isometry hS'Γ H.point
      hS'v
  rcases hcases with h2 | ⟨-, Y, hYΓ, hYv, hYe, hY9⟩
  ·
    have hUE : ∀ w ∈ Up, w ∈ D.hat (l32nE T V V₂ g) → w = 0 := by
      intro w hwU hwW
      by_contra hw0
      have hspan : (⟨w, hwW⟩ : D.hat (l32nE T V V₂ g)) ∉
          (ZMod 2) ∙ (⟨D.π a, H.mem_W⟩ : D.hat (l32nE T V V₂ g)) := by
        intro hmem
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
        have hc' : c • D.π a = w := by
          have := congrArg Subtype.val hc
          simpa using this
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · exact hw0 (by rw [← hc', zero_smul])
        · rw [one_smul] at hc'
          exact hvUp (by rw [hc']; exact hwU)
      obtain ⟨f, hf, hker⟩ := Submodule.exists_le_ker_of_notMem hspan
      have hfv : f ⟨D.π a, H.mem_W⟩ = 0 :=
        LinearMap.mem_ker.1 (hker (Submodule.mem_span_singleton_self _))
      obtain ⟨x, hxX, hx⟩ := H.transvection_full f hfv
      have h1 := hx ⟨w, hwW⟩
      have hf1 : f ⟨w, hwW⟩ = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hf
      rw [hf1, one_smul] at h1
      have h1' : x w = w + D.π a := by simpa using h1
      have hxw : x w ∈ Up := hUpS x (hXS' hxX) w hwU
      apply hvUp
      have e : D.π a = x w - w := by
        rw [h1']
        abel
      rw [e]
      exact Up.sub_mem hxw hwU

    have hXU : ∀ x ∈ D.img (CFSG.conjugate (l32nW T V V₂) g), ∀ u ∈ Up, x u = u := by
      intro x hx u hu
      have h1 := H.commutator_le x hx u (hUpv u hu)
      have h2 : x u - u ∈ Up := Up.sub_mem (hUpS x (hXS' hx) u hu) hu
      exact sub_eq_zero.1 (hUE _ h2 h1)
    have hX2 := h2 _ hXS' C.X_elem_F4 hXU
    have hlow := C.lower_F4
    rw [hC4.1] at hlow
    norm_num at hlow
    omega
  · exact C.no_E9_F4 hYΓ hY9 (fun x hx y hy => congrArg Subtype.val
      (hYe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hYe.2 hYv

end Ctx

end L1442

end CFSG.Quasithin.H13

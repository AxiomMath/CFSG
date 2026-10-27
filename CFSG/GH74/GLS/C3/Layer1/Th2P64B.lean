module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617
public import CFSG.GH74.GLS.C3.Layer1.BkP34N
public import CFSG.GH74.GLS.C3.Layer1.Th2L627Syl

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Obstr52.exists_outer_involution {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hG4 : pRank 2 G ≤ 4) (hB : CFSG.IsElementaryAbelian 2 ↥B) :
    ∃ f ∈ B, orderOf f = 2 ∧ C3.Layer1.P34.InducesFAutL2A7 f J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  obtain ⟨D, hD⟩ := h.exists_D
  obtain ⟨⟨e⟩, hBinv⟩ := hD.B_inv (h.normalizes hG4 hB)
  obtain ⟨t, ht, -, hBt⟩ := hBinv e
  have htmem : t ∈ (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e) := by
    rw [hBt]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨m, hm, hmt⟩ := Subgroup.mem_map.1 htmem
  have hmB : (m : G) ∈ B := hm
  have ht1 : t ≠ 1 := ht.isCycle.ne_one
  have hf1 : (m : G) ≠ 1 := by
    intro h1
    have : m = 1 := Subtype.ext h1
    rw [this, map_one] at hmt
    exact ht1 hmt.symm
  have hα : barAct J m ∉ innAut (kBar J) := by
    intro hin
    obtain ⟨k, hk⟩ := hin
    have h1 : a7Act J e m = t := hmt
    have h2 : a7Act J e m = ((e k : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
      show (Bal.a7Theta e).symm (barAct J m) = _
      rw [← hk]
      refine (Bal.a7Theta e).symm_apply_eq.2 ?_
      rw [Bal.a7Theta_even, e.symm_apply_apply]
    have h3 : Equiv.Perm.sign t = 1 := by
      rw [← h1, h2]
      exact Equiv.Perm.mem_alternatingGroup.1 (e k).2
    obtain ⟨x, y, hxy, rfl⟩ := ht
    rw [Equiv.Perm.sign_swap hxy] at h3
    exact absurd h3 (by decide)
  refine ⟨m, hmB, orderOf_eq_prime (by rw [sq]; exact hBsq _ hmB) hf1, m.2, ?_, Or.inr ⟨⟨e⟩, hα⟩⟩
  intro h1
  exact hα (by rw [show barAct J m = 1 from h1]; exact one_mem _)

theorem Obstr52.not_isCentralInvolution
    {B : Subgroup G} {b : G} {J : Subgroup G} (h : Obstr52 B b J) (hG : C3Hyp G)
    (hB : CFSG.IsElementaryAbelian 2 ↥B) (hA : Nonempty (kBar J ≃* alternatingGroup (Fin 7)))
    (hN2 : twoPartCard (CxK b J) = 2) : ¬ IsCentralInvolution b := by
  intro hc
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  obtain ⟨f, hfB, hf2, hind⟩ := h.exists_outer_involution hG4 hB
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  have hfC : f ∈ centralizer ({b} : Set G) := mem_centralizer_singleton_iff.2 (hBc f hfB b h.mem)
  have hnorm : ∀ c ∈ centralizer ({b} : Set G), ∀ k ∈ J, c * k * c⁻¹ ∈ J := fun c hc k hk =>
    (Subgroup.mem_normalizer_iff.mp (h.normalizes_centralizer hG4 hB c hc) k).mp hk
  have hQ2 : ∀ A : Subgroup G, A ≤ CMK (centralizer ({b} : Set G)) J →
      CFSG.IsElementaryAbelian 2 ↥A → Nat.card ↥A ≤ 2 := by
    intro A hA' hAel
    have := Th2.L627.card_le_twoPartCard (CFSG.IsElementaryAbelian.isPGroup 2 ↥A) hA'
    rwa [show twoPartCard (CMK (centralizer ({b} : Set G)) J) = 2 from hN2] at this
  have hyp : C3.Layer1.Bk.Prop34HypN G b J :=
    { simple := hG.kproper.1
      nonab := hG.kproper.2.1
      central := hc
      comp := h.comp
      normal := hnorm
      shape := Or.inr hA
      sylowQ := C3.Layer1.Thm1.exists_Q_of_card_le_two hQ2 }
  exact C3.Layer1.Bk.prop34N_false hyp hfC hf2 hind

end CFSG.GH74.GLS.Th2.Obs

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GXC6Def

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem l34g_isSubnormal_trans {Y : Type} [Group Y] {H K J : Subgroup Y} (hHK : H ≤ K)
    (hKJ : K ≤ J) (h₁ : (H.subgroupOf K).IsSubnormal) (h₂ : (K.subgroupOf J).IsSubnormal) :
    (H.subgroupOf J).IsSubnormal := by
  refine Subgroup.IsSubnormal.trans (Subgroup.subgroupOf_mono J hHK) ?_ h₂
  set e : K.subgroupOf J ≃* K := Subgroup.subgroupOfEquivOfLe hKJ with he
  have heq : (H.subgroupOf J).subgroupOf (K.subgroupOf J) =
      (H.subgroupOf K).comap e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    rfl
  rw [heq]
  exact h₁.comap _

theorem l34g_pocket_pair {Y : Type} [Group Y] [Finite Y] {X K : Subgroup Y} {y : Y}
    (hK : Sl23PocketIn X y K) : ∃ u ∈ K, orderOf u = 3 ∧ y * u = u * y := by
  obtain ⟨u, huK, hu⟩ := l34g_exists_order_three_of_sl23Mod hK.2.2.2
  refine ⟨u, huK, hu, ?_⟩
  have h : u ∈ centralizer ({y} : Set Y) := (hK.2.1 huK).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  exact h.symm

theorem l34g_kgA_of_c6 {Y : Type} [Group Y] [Finite Y] (hC : L34GC6 Y) {y : Y} {B : Subgroup Y}
    (hy : orderOf y = 2) (hB : Sl23PocketIn ⊤ y B) {σ : MulAut Y} (hσ : σ * σ = 1)
    (hfix : ∀ b ∈ B, σ b = b) : σ = 1 ∨ σ = MulAut.conj y := by
  obtain ⟨u, huB, hu3, hcomm⟩ := l34g_pocket_pair hB
  exact hC σ hσ y u hy hu3 hcomm (hfix y hB.1) (hfix u huB)

theorem l34g_kgB_of_c6 {Y : Type} [Group Y] [Finite Y] (hC : L34GC6 Y) {σ : MulAut Y}
    (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) {J : Subgroup Y} (hJ : IsComponentIn J (L34GFix σ)) {b : Y}
    (hb : b ∈ J) (hI : IsI4PlusIn J b) : IsI4PlusIn (⊤ : Subgroup Y) b := by
  obtain ⟨hb2, K, hK⟩ := hI
  obtain ⟨u, huK, hu3, hcomm⟩ := l34g_pocket_pair hK
  have hKJ : K ≤ J := fun k hk => (hK.2.1 hk).1
  have hfix : ∀ j ∈ J, σ j = j := fun j hj => (l34g_mem_fix σ j).mp (hJ.1 hj)
  have hσb : σ = MulAut.conj b :=
    (hC σ hσ b u hb2 hu3 hcomm (hfix b hb) (hfix u (hKJ huK))).resolve_left hσ1
  rw [hσb, l34g_fix_conj] at hJ
  have hJC : J ≤ centralizer ({b} : Set Y) := hJ.1
  have hKJ' : (K.subgroupOf J).IsSubnormal := by
    have h := hK.2.2.1
    rwa [inf_of_le_left hJC] at h
  refine ⟨hb2, K, hK.1, le_inf le_top (fun k hk => (hK.2.1 hk).2), ?_, hK.2.2.2⟩
  rw [top_inf_eq]
  exact l34g_isSubnormal_trans hKJ hJC hKJ' hJ.2.2

end CFSG.OddStandard.SmallF3.Omega

module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreXLayer

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {X : Type} [Group X] [Finite X]

structure OneComponent (Y : Subgroup X) (e v : X) (L : Subgroup X) : Prop where
  component : CFSG.IsComponent L
  unique : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L
  layer_eq : CFSG.layer X = L
  normal : L.Normal
  mem : e ∈ L
  not_le : ¬ L ≤ Y
  mem_centralizer : v ∈ Subgroup.centralizer (L : Set X)
  eq_of_mem_centralizer : ∀ k ∈ Subgroup.centralizer (L : Set X), orderOf k = 2 → k = e
  center_isCyclic : IsCyclic (Subgroup.center L)
  center_le : (Subgroup.center L).map L.subtype ≤ CFSG.Open.pCore 2 X

namespace BaseConfig

variable {Y : Subgroup X} {e v : X}

theorem component_center_isCyclic (hc : BaseConfig Y e) {L : Subgroup X}
    (hL : CFSG.IsComponent L) :
    IsCyclic (Subgroup.center L) ∧ (Subgroup.center L).map L.subtype ≤ CFSG.Open.pCore 2 X := by
  obtain ⟨hZ2, hZO⟩ := component_center_le_twoCore hc.oddCore_eq_bot hL
  refine ⟨?_, hZO⟩
  obtain ⟨n, hn⟩ := hZ2.exists_card_eq
  have hce : ∀ w : Subgroup.center L, orderOf w = 2 → ((w : L) : X) = e := fun w hw =>
    hc.eq_of_mem_twoCore (hZO (Subgroup.mem_map_of_mem L.subtype w.2))
      (by rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]; exact hw)
  let : CommGroup (Subgroup.center L) := IsMulCommutative.instCommGroup
  exact TwoRankLowerBound.Helpers.abelian_two_group_cyclic_of_unique_involution_of_card_eq_pow n
    _ hZ2 hn fun w w' hw hw' => Subtype.ext (Subtype.ext ((hce w hw).trans (hce w' hw').symm))

omit [Finite X] in
theorem layer_eq_of_unique {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hunique : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L) : CFSG.layer X = L :=
  le_antisymm (sSup_le fun L' hL' => (hunique L' hL').le) (le_sSup hL)

theorem eq_of_mem_centralizer_of_not_le (hc : BaseConfig Y e) {L : Subgroup X} [L.Normal]
    (hLY : ¬ L ≤ Y) {k : X} (hk : k ∈ Subgroup.centralizer (L : Set X)) (hk2 : orderOf k = 2) :
    k = e := by
  by_contra hne
  obtain ⟨g, hgY⟩ := hc.exists_conj_mem hk2
  have hgk : g⁻¹ * k * g ∈ Subgroup.centralizer (L : Set X) := by
    simpa using (Subgroup.normal_centralizer (H := L)).conj_mem k hk g⁻¹
  have hgne : g⁻¹ * k * g ≠ e := by
    intro h'
    apply hne
    calc k = g * (g⁻¹ * k * g) * g⁻¹ := by group
      _ = g * e * g⁻¹ := by rw [h']
      _ = e := by rw [(hc.commute_center g).eq, mul_inv_cancel_right]
  apply hLY
  intro l hl
  refine hc.involution_centralizer_le hgY ((orderOf_inv_mul_mul g k).trans hk2) hgne ?_
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hgk l hl)

theorem exists_oneComponent (hc : BaseConfig Y e) (hrank : 3 ≤ twoRank X) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hall : ∀ L : Subgroup X, CFSG.IsComponent L → e ∈ L) :
    ∃ L : Subgroup X, OneComponent Y e v L := by
  obtain ⟨L, hL, hLY⟩ := hc.exists_component_not_le hrank hv hvn
  have hunique : ∀ L' : Subgroup X, CFSG.IsComponent L' → L' = L := fun L' hL' =>
    hc.component_unique hv hvn hL hLY hL'
  have hlayer := layer_eq_of_unique hL hunique
  have hnormal : L.Normal := hlayer ▸ layer_normal
  obtain ⟨hZc, hZO⟩ := hc.component_center_isCyclic hL
  exact ⟨L, hL, hunique, hlayer, hnormal, hall L hL, hLY, mem_centralizer_component hvn hL,
    fun k hk hk2 => hc.eq_of_mem_centralizer_of_not_le hLY hk hk2, hZc, hZO⟩

end BaseConfig

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem mem_center (hL : OneComponent Y e v L) (hc : BaseConfig Y e) :
    (⟨e, hL.mem⟩ : L) ∈ Subgroup.center L :=
  Subgroup.mem_center_iff.mpr fun l => Subtype.ext (hc.commute_center l).eq

omit [Finite X] in
theorem centralizer_normal (hL : OneComponent Y e v L) :
    (Subgroup.centralizer (L : Set X)).Normal := by
  have := hL.normal
  infer_instance

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

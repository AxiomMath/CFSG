module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightNormalizerExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightSplitExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightNonsplitExtension
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RankOnePairIndexTwo

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

theorem exists_order_four_commute_of_full_linear {G : Type*} [Group G] [Finite G]
    {U Y : Subgroup G} [IsElementaryAbelian 2 U] (hU8 : Nat.card U = 8) (hUY : U ≤ Y)
    (hnormal : ∀ y ∈ Y, ∀ x ∈ U, y * x * y⁻¹ ∈ U)
    (hcent : Subgroup.centralizer (U : Set G) ⊓ Y = U)
    (hfull : ∀ σ : MulAut U, ∃ y ∈ Y, ∀ x : U, ((σ x : U) : G) = y * x * y⁻¹)
    {x : G} (hxY : x ∈ Y) (hx2 : orderOf x = 2) (hxU : x ∉ U) :
    ∃ y ∈ Y, orderOf y = 4 ∧ Commute x y := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' := U.subgroupOf Y with hU'
  have _ : U'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hnormal g g.2 n hn⟩
  have _ : IsElementaryAbelian 2 U' := IsElementaryAbelian.subgroupOf hUY
  let e : U' ≃* U := Subgroup.subgroupOfEquivOfLe hUY
  have he : ∀ w : U', ((e w : U) : G) = ((w : Y) : G) := fun w => rfl
  have hU'8 : Nat.card U' = 8 := by rw [Nat.card_congr e.toEquiv, hU8]
  have hcent' : Subgroup.centralizer (U' : Set Y) = U' := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy
      rw [← hcent]
      refine ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => ?_, y.2⟩
      have := hy ⟨h, hUY hh⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hh)
      exact congrArg Subtype.val this
    · intro hy h hh
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hh
      apply Subtype.ext
      exact mul_comm_of_mem hh hy
  have hfull' : ∀ σ : MulAut U', ∃ y : Y, ∀ x : U', ((σ x : U') : Y) = y * x * y⁻¹ := by
    intro σ
    obtain ⟨y, hy, hyσ⟩ := hfull (MulAut.congr e σ)
    refine ⟨⟨y, hy⟩, fun w => Subtype.ext ?_⟩
    have := hyσ (e w)
    change ((e (σ (e.symm (e w))) : U) : G) = _ at this
    rw [MulEquiv.symm_apply_apply, he, he] at this
    simpa using this
  have hx' : orderOf (⟨x, hxY⟩ : Y) = 2 := by rw [Subgroup.orderOf_mk]; exact hx2
  have hxU' : (⟨x, hxY⟩ : Y) ∉ U' := by
    rw [Subgroup.mem_subgroupOf]; exact hxU
  by_cases hsplit : ∃ K : Subgroup Y, U' ⊓ K = ⊥ ∧ U' ⊔ K = ⊤
  · obtain ⟨y, hy4, hcomm⟩ :=
      split_eight_linear_three_extension_outside_involution_four_centralizers hU'8 hcent'
        hfull' hsplit _ hx' hxU'
    refine ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy4, ?_⟩
    exact congrArg Subtype.val hcomm.eq
  · obtain ⟨-, -, -, -, -, -, -, -, h4⟩ :=
      nonsplit_eight_linear_three_extension_involutions_and_four_centralizers hU'8 hcent'
        hfull' hsplit
    obtain ⟨y, hyc, hy4⟩ := h4 _ hx' hxU'
    refine ⟨y, y.2, by rw [Subgroup.orderOf_coe]; exact hy4, ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hyc)).symm

theorem exceptional_eight_involution_coset_normalizer_exclusion
    {G : Type*} [Group G] [Finite G] (hindex : ∀ H : Subgroup G, H.index ≠ 2)
    {u : G} (hu : orderOf u = 2)
    {U : Subgroup G} [IsElementaryAbelian 2 U] (hU8 : Nat.card U = 8)
    (hUu : U ≤ Subgroup.centralizer {u}) (huU : u ∉ U)
    {E N : Subgroup G} (hE : E = Subgroup.zpowers u ⊔ U)
    (hN : N = Subgroup.normalizer (u • (U : Set G)))
    (hcent : Subgroup.centralizer (u • (U : Set G)) = E)
    [(E.subgroupOf N).Normal] [IsSimpleGroup (N ⧸ E.subgroupOf N)]
    (hnonab : ∃ a b : N ⧸ E.subgroupOf N, a * b ≠ b * a)
    (hcard : Nat.card (N ⧸ E.subgroupOf N) = 168)
    (hconj : ∀ x ∈ u • (U : Set G), IsConj u x)
    (hdisj : ∀ x ∈ U, x ≠ 1 → ¬ IsConj u x)
    (hno4 : ∀ x ∈ Subgroup.centralizer {u}, orderOf x ≠ 4) :
    ∀ S : Sylow 2 G, ¬ (S : Subgroup G) ≤ N := by
  classical
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S hSN
  obtain ⟨⟨hUN, hUnormal⟩, -, -, Y, hYN, hYnormal, hUY, -, -, hYindex, hCY, hfullY, -⟩ :=
    exceptional_eight_involution_coset_normalizer_produces_full_linear_extension hu hU8 hUu
      huU hE hN hcent hnonab hcard hconj hno4
  have hnormalY : ∀ y ∈ Y, ∀ x ∈ U, y * x * y⁻¹ ∈ U := by
    intro y hy x hx
    have := hUnormal.conj_mem ⟨x, hUN hx⟩ (by rw [Subgroup.mem_subgroupOf]; exact hx)
      ⟨y, hYN hy⟩
    rw [Subgroup.mem_subgroupOf] at this
    exact this
  have hSY : ¬ (S : Subgroup G) ≤ Y := by
    intro hle
    have hdvd : Nat.card (S : Subgroup G) ∣ Nat.card Y := Subgroup.card_dvd_of_le hle
    have hNY : Nat.card N = 2 * Nat.card Y := by
      have h1 := (Y.subgroupOf N).index_mul_card
      rw [← Subgroup.relIndex, hYindex,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv] at h1
      exact h1.symm
    have hNG : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
    have hSG := (S : Subgroup G).index_mul_card
    obtain ⟨k, hk⟩ := hdvd
    have hodd := S.not_dvd_index
    apply hodd
    have hpos : 0 < Nat.card (S : Subgroup G) := Nat.card_pos
    rw [hNY, hk, ← hSG] at hNG
    have : 2 * k * Nat.card (S : Subgroup G) ∣ (S : Subgroup G).index * Nat.card (S : Subgroup G) := by
      rw [show 2 * k * Nat.card (S : Subgroup G) = 2 * (Nat.card (S : Subgroup G) * k) by ring]
      exact hNG
    exact dvd_trans (Dvd.intro k rfl) (Nat.dvd_of_mul_dvd_mul_right hpos this)
  have hV : (Y ⊓ (S : Subgroup G)).relIndex (S : Subgroup G) = 2 := by
    rw [Subgroup.inf_relIndex_right]
    have hle : Y.relIndex (S : Subgroup G) ≤ 2 :=
      calc Y.relIndex (S : Subgroup G) ≤ Y.relIndex N :=
            Subgroup.relIndex_le_of_le_right hSN (by rw [hYindex]; omega)
        _ = 2 := hYindex
    have hne1 : Y.relIndex (S : Subgroup G) ≠ 1 := fun h1 => hSY (Subgroup.relIndex_eq_one.mp h1)
    have hne0 : Y.relIndex (S : Subgroup G) ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  obtain ⟨g, hg⟩ := (CFSG.ProperTwoGeneratedCore.RankOnePair.index_two_mod_four_subgroups_meet_involution_classes
    hindex).2 S (Y ⊓ (S : Subgroup G)) inf_le_right hV u hu
  set x := g⁻¹ * u * g with hx
  have hxY : x ∈ Y := (Subgroup.mem_inf.mp hg).1
  have hux : IsConj u x := isConj_iff.mpr ⟨g⁻¹, by rw [hx, inv_inv]⟩
  have hx2 : orderOf x = 2 := by
    have := (MulAut.conj g⁻¹).orderOf_eq u
    rw [MulAut.conj_apply, inv_inv] at this
    rw [hx, this, hu]
  have hxU : x ∉ U := by
    intro hxU
    refine hdisj x hxU ?_ hux
    intro h1
    rw [h1, orderOf_one] at hx2
    exact absurd hx2 (by decide)
  obtain ⟨y, -, hy4, hcomm⟩ :=
    exists_order_four_commute_of_full_linear hU8 hUY hnormalY hCY hfullY hxY hx2 hxU
  refine hno4 (g * y * g⁻¹) ?_ ?_
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hu' : u = g * x * g⁻¹ := by rw [hx]; group
    rw [hu']
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
      _ = g * (x * y) * g⁻¹ := by rw [hcomm.eq]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · have := (MulAut.conj g).orderOf_eq y
    rw [MulAut.conj_apply] at this
    rw [this, hy4]

end CFSG.ProperTwoGeneratedCore.ExceptionalEight

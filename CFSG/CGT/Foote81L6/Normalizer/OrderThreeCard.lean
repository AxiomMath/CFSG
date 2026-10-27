module

public import CFSG.CGT.Foote81L6.Normalizer.OrderThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Quasithin.Background.FixVZPowersMem

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commV_le_commSub [Finite V] (hV : ∀ v : V, v * v = 1) {x : MulAut V} (hx3 : x ^ 3 = 1) :
    commV (Subgroup.zpowers x) ≤ commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers x) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨y, hy, v, rfl⟩
  have hv : v ∈ commV (Subgroup.zpowers x) ⊔ fixV (Subgroup.zpowers x) := by
    rw [commV_zpowers_sup_eq hV hx3]; trivial
  obtain ⟨u, hu, c, hc, rfl⟩ := Subgroup.mem_sup.1 hv
  have hyc : y c = c := hc y hy
  refine Subgroup.subset_closure ⟨y, hy, u, hu, ?_⟩
  calc y u * u⁻¹ = (y u * c) * (c⁻¹ * u⁻¹) := by group
    _ = y (u * c) * (u * c)⁻¹ := by rw [map_mul, hyc, mul_inv_rev]

private theorem four_le_card {S : Subgroup V} [Finite S] (hV : ∀ v : V, v * v = 1) {b₀ b₁ : V}
    (hb₀S : b₀ ∈ S) (hb₁S : b₁ ∈ S) (hb₀1 : b₀ ≠ 1) (hb₁1 : b₁ ≠ 1) (hb : b₀ ≠ b₁) :
    4 ≤ Nat.card S := by
  have h01 : b₀ * b₁ ≠ 1 := fun h => hb (by
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_left (hV b₁)])
  have h02 : b₀ * b₁ ≠ b₀ := fun h => hb₁1 (mul_left_cancel (h.trans (mul_one b₀).symm))
  have h03 : b₀ * b₁ ≠ b₁ := fun h => hb₀1 (mul_right_cancel (h.trans (one_mul b₁).symm))
  have hsub : ({1, b₀, b₁, b₀ * b₁} : Set V) ⊆ (S : Set V) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact S.one_mem
    · exact hb₀S
    · exact hb₁S
    · exact S.mul_mem hb₀S hb₁S
  have hcard : ({1, b₀, b₁, b₀ * b₁} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hb₀1.symm, hb₁1.symm, h01.symm⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hb, h02.symm⟩),
      Set.ncard_pair h03.symm]
  have e : Nat.card ↥S = (S : Set V).ncard := Nat.card_coe_set_eq _
  rw [← hcard, e]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem card_commV_zpowers_eq_four [Finite V] (hV : ∀ v : V, v * v = 1)
    (hcard : Nat.card V = 2 ^ 6) {x : MulAut V} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {W : Subgroup V} (hW : Nat.card W ≤ 16) (hUW : commV (Subgroup.zpowers x) ≤ W) {b₀ b₁ : V}
    (hb₀W : b₀ ∈ W) (hb₁W : b₁ ∈ W) (hb₀ : x b₀ = b₀) (hb₁ : x b₁ = b₁) (hb₀1 : b₀ ≠ 1)
    (hb₁1 : b₁ ≠ 1) (hb : b₀ ≠ b₁) : Nat.card (commV (Subgroup.zpowers x)) = 4 := by
  classical
  set U := commV (Subgroup.zpowers x) with hUdef
  set S := W ⊓ fixV (Subgroup.zpowers x) with hSdef
  have hinf0 := commV_zpowers_inf_eq hV hx3
  have hinf : U ⊓ S = ⊥ := eq_bot_iff.2 ((inf_le_inf_left _ inf_le_right).trans hinf0.le)
  have hS4 : 4 ≤ Nat.card S := four_le_card hV
    (Subgroup.mem_inf.2 ⟨hb₀W, mem_fixV_zpowers_iff_apply.2 hb₀⟩)
    (Subgroup.mem_inf.2 ⟨hb₁W, mem_fixV_zpowers_iff_apply.2 hb₁⟩) hb₀1 hb₁1 hb
  have hUS : Nat.card ↥(U ⊔ S) = Nat.card U * Nat.card S :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer U S
      (by rw [CommGroup.normalizer_eq_top]; exact le_top) (disjoint_iff.mpr hinf)
  have h16 : Nat.card ↥(U ⊔ S) ≤ 16 :=
    (Subgroup.card_le_of_le (sup_le hUW inf_le_left)).trans hW
  have hU4 : Nat.card U ≤ 4 := by
    by_contra h5
    have : 5 * 4 ≤ Nat.card U * Nat.card S := Nat.mul_le_mul (by omega) hS4
    omega
  obtain ⟨v, hv⟩ := B1.exists_moved_of_ne_one hx1
  set c := x v * v⁻¹ with hc
  have hcU : c ∈ U := Subgroup.subset_closure ⟨x, Subgroup.mem_zpowers x, v, rfl⟩
  have hc1 : c ≠ 1 := fun h => hv (mul_inv_eq_one.1 h)
  have hxc : x c ∈ U := apply_mem_commV_zpowers hcU
  have hxc1 : x c ≠ c := by
    intro h
    have hcfix : c ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff_apply.2 h
    have : c ∈ U ⊓ fixV (Subgroup.zpowers x) := ⟨hcU, hcfix⟩
    rw [hinf0, Subgroup.mem_bot] at this
    exact hc1 this
  have hxc1' : x c ≠ 1 := fun h => hc1 (by rwa [map_eq_one_iff _ x.injective] at h)
  have h3 : 3 ≤ Nat.card U := by
    have hsub : ({1, c, x c} : Set V) ⊆ (U : Set V) := by
      intro y hy
      rcases hy with rfl | rfl | rfl
      · exact U.one_mem
      · exact hcU
      · exact hxc
    have hnc : ({1, c, x c} : Set V).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hc1.symm, hxc1'.symm⟩),
        Set.ncard_pair hxc1.symm]
    have e : Nat.card ↥U = (U : Set V).ncard := Nat.card_coe_set_eq _
    rw [← hnc, e]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hdvd : Nat.card U ∣ 2 ^ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card U
  obtain ⟨i, hi, hUi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hUi] at hU4 h3 ⊢
  interval_cases i <;> simp_all

end CFSG.CGT.Foote81L6.Normalizer

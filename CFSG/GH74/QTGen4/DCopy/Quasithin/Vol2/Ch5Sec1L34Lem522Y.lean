module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem522S331
public import CFSG.Quasithin.Vol2.Ch5Sec1L34BorelThree
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped Pointwise

section Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem card_B_eq_three_F4 (h510 : Stmt5_1_10_F4) : Nat.card B = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := h.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  obtain ⟨-, -, hBorel, hBK, -⟩ := h510 G T M L H B D n h.hyp h.notation59
  have hMK := h.hyp.borel_eq hBorel
  have hTK : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf h.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hker : π.ker ≤ (T ⊓ K).subgroupOf K := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 K := ⟨x, by assumption, rfl⟩
    exact CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK hx'
  have hS : IsSylowTwoOf (((T ⊓ K).subgroupOf K).map π) ⊤ := by
    refine ⟨le_top, IsPGroup.map (A4.isPGroup_subgroupOf_of_le hTK.1 hTK.2.1) _, ?_⟩
    have h1 : ((((T ⊓ K).subgroupOf K).map π).subgroupOf ⊤).index =
        (((T ⊓ K).subgroupOf K).map π).index := Subgroup.relIndex_top_right _
    rw [h1, Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) hker]
    exact hTK.2.2
  obtain ⟨y', hy'N, hy'3⟩ := exists_orderOf_eq_three_mem_normalizer h.l34 hS
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) y'
  have hyN : (y : G) ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
    apply mem_normalizer_of_forall_conj_mem'
    intro t ht
    set t' : ↥K := ⟨t, ht.2⟩ with ht'
    have hmem : π (y * t' * y⁻¹) ∈ ((T ⊓ K).subgroupOf K).map π := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy'N _).mp ⟨t', ht, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := hmem
    have hk : s'⁻¹ * (y * t' * y⁻¹) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs'e, inv_mul_cancel]
    have h1 : y * t' * y⁻¹ ∈ (T ⊓ K).subgroupOf K := by
      have e : y * t' * y⁻¹ = s' * (s'⁻¹ * (y * t' * y⁻¹)) := by group
      rw [e]
      exact Subgroup.mul_mem _ hs' (hker hk)
    exact Subgroup.mem_subgroupOf.mp h1
  have hyMK : (y : G) ∈ M ⊓ K := by
    rw [hMK]
    exact ⟨y.2, hyN⟩
  have h3MK : 3 ∣ Nat.card ↥(M ⊓ K) := by
    have h1 : 3 ∣ orderOf y := by
      rw [← hy'3]
      exact orderOf_map_dvd _ y
    have h2 := orderOf_dvd_natCard (⟨(y : G), hyMK⟩ : ↥(M ⊓ K))
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe] at h2
    exact h1.trans h2
  obtain ⟨hBle, -, j, hj⟩ := hBK
  have e1 := B.relIndex_mul_card (M ⊓ K)
  rw [inf_eq_left.mpr hBle, hj] at e1
  rw [← e1] at h3MK
  have h3B : 3 ∣ Nat.card B :=
    (Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h3MK
  exact Nat.dvd_antisymm (h.card_B_dvd_three_F4 h510 l34BorelFact) h3B

end Hyp5_1_14

end Setting

end CFSG.Quasithin.H13

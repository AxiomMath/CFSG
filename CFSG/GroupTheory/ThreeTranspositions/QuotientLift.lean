module

public import CFSG.GroupTheory.ThreeTranspositions.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
import CFSG.GH74.GLS.Stage1.Thm6.Lift

public section

namespace CFSG.GroupTheory.ThreeTranspositions

theorem hasE9_of_hasE9_quotient {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) (h : HasE9 (G ⧸ N)) : HasE9 G := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨xb, yb, hx, hy, hxy, hyx⟩ := h
  set Abar : Subgroup (G ⧸ N) := Subgroup.closure ({xb, yb} : Set (G ⧸ N)) with hAbar
  have hpair : ({xb, yb} : Set (G ⧸ N)).Pairwise Commute := by
    intro a ha b hb hne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hne
    · exact hxy
    · exact hxy.symm
    · exact absurd rfl hne
  haveI hAcomm : IsMulCommutative ↥Abar := Subgroup.isMulCommutative_closure hpair
  have hA3 : ∀ z : ↥Abar, z ^ 3 = 1 := by
    intro z
    apply Subtype.ext
    show (z : G ⧸ N) ^ 3 = 1
    refine Subgroup.closure_induction (p := fun w _ => w ^ 3 = 1) ?_ ?_ ?_ ?_ z.2
    · intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with hw | hw
      · rw [hw]; simpa [hx] using pow_orderOf_eq_one xb
      · rw [hw]; simpa [hy] using pow_orderOf_eq_one yb
    · exact one_pow 3
    · intro x y hx hy ihx ihy
      have hc : Commute x y := by
        have h := congrArg (Subtype.val : ↥Abar → G ⧸ N)
          (mul_comm' (⟨x, hx⟩ : ↥Abar) ⟨y, hy⟩)
        show x * y = y * x
        simpa using h
      rw [hc.mul_pow, ihx, ihy, mul_one]
    · intro x hx ihx
      rw [inv_pow, ihx, inv_one]
  have hAbarP : IsPGroup 3 ↥Abar := fun z => ⟨1, by simpa using hA3 z⟩
  obtain ⟨A, hAp, hAmap, hAdisj⟩ :=
    CFSG.GH74.GLS.Stage1.Thm6.exists_lift_pSubgroup N hN Abar hAbarP
  let f : ↥A →* G ⧸ N := (QuotientGroup.mk' N).domRestrict A
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have hmemN : (a : G)⁻¹ * b ∈ N := QuotientGroup.eq.mp hab
    have hmemA : (a : G)⁻¹ * b ∈ A := A.mul_mem (A.inv_mem a.2) b.2
    have hbot : (a : G)⁻¹ * b ∈ A ⊓ N := ⟨hmemA, hmemN⟩
    rw [hAdisj] at hbot
    have h1 : (a : G)⁻¹ * b = 1 := by simpa using hbot
    have h2 : (a : G) = b := by
      calc (a : G) = (a : G) * ((a : G)⁻¹ * b) := by rw [h1, mul_one]
        _ = b := by group
    exact h2
  have hxbA : xb ∈ Abar := Subgroup.subset_closure (Set.mem_insert _ _)
  have hybA : yb ∈ Abar := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨x, hxA, hxeq⟩ := Subgroup.mem_map.mp (by rw [hAmap]; exact hxbA)
  obtain ⟨y, hyA, hyeq⟩ := Subgroup.mem_map.mp (by rw [hAmap]; exact hybA)
  have hxord : orderOf (⟨x, hxA⟩ : ↥A) = 3 := by
    rw [← orderOf_injective f hf ⟨x, hxA⟩]
    simpa [f, hxeq] using hx
  have hyord : orderOf (⟨y, hyA⟩ : ↥A) = 3 := by
    rw [← orderOf_injective f hf ⟨y, hyA⟩]
    simpa [f, hyeq] using hy
  have hcommA : Commute (⟨x, hxA⟩ : ↥A) (⟨y, hyA⟩ : ↥A) := by
    apply hf
    rw [map_mul, map_mul]
    simp only [f, MonoidHom.domRestrict_apply]
    rw [hxeq, hyeq]
    exact hxy.eq
  have hmemZp : (⟨y, hyA⟩ : ↥A) ∉ Subgroup.zpowers (⟨x, hxA⟩ : ↥A) := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hyx
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      have h := congrArg f hk
      rw [map_zpow] at h
      simp only [f, MonoidHom.domRestrict_apply] at h
      rwa [hxeq, hyeq] at h⟩
  exact HasE9.map_injective A.subtype A.subtype_injective
    ⟨⟨x, hxA⟩, ⟨y, hyA⟩, hxord, hyord, hcommA, hmemZp⟩

theorem two_le_pRank_of_hasE9_subgroup {A : Type*} [Group A] [Finite A] (H : Subgroup A)
    (h : HasE9 ↥H) : 2 ≤ CFSG.Open.pRank 3 H := by
  obtain ⟨x, y, hx, hy, hxy, hyx⟩ := h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.GroupTheory.two_le_pRank_of_commute (p := 3) (H := H) (x := (x : A))
    (y := (y : A)) x.2 y.2 (by rw [Subgroup.orderOf_coe, hx]) (by rw [Subgroup.orderOf_coe, hy])
    (hxy.map H.subtype) ?_
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact hyx (Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩)

theorem not_hasE9_quotient_pPrimeCore {A : Type*} [Group A] [Finite A] (H : Subgroup A)
    (hr : CFSG.Open.pRank 3 H ≤ 1) : ¬ HasE9 (↥H ⧸ CFSG.pPrimeCore 3 ↥H) := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥H) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have h2 := two_le_pRank_of_hasE9_subgroup H
    (hasE9_of_hasE9_quotient (CFSG.pPrimeCore 3 ↥H) hN h)
  omega

end CFSG.GroupTheory.ThreeTranspositions

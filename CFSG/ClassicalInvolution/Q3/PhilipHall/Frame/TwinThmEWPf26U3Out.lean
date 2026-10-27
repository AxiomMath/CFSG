module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf20U3Model
public import CFSG.ClassicalInvolution.Q3.TL4ConnBendOut
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

open CFSG.ComponentClassification.OuterAutomorphisms Subgroup CFSG.BenderSuzuki
  CFSG.GH74.Uniqueness.Bender


theorem u3_eq_one_or_eq_of_mem_zpowers_sq {X : Type*} [Group X] {u v : X} (hv : v * v = 1)
    (h : u ∈ Subgroup.zpowers v) : u = 1 ∨ u = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hv, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hv, one_zpow, one_mul]

theorem u3_two_group_cases {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) (hB : IsBenderGroup ↥L)
    (S : Subgroup G) (hS : IsPGroup 2 ↥S) :
    ∀ x ∈ S, ∀ y ∈ S, x * x ∈ L → y * y ∈ L → x ∈ L ∨ y ∈ L ∨ x * y ∈ L := by
  classical
  intro x hx y hy hx2 hy2
  let ψ : G →* Outer ↥L := (QuotientGroup.mk' (inner ↥L)).comp MulAut.conjNormal
  have hker : ∀ g : G, ψ g = 1 → g ∈ L := by
    intro g hg
    have h1 : (MulAut.conjNormal g : MulAut ↥L) ∈ inner ↥L :=
      (QuotientGroup.eq_one_iff (N := inner ↥L) _).mp hg
    obtain ⟨f, hf⟩ := MonoidHom.mem_range.mp h1
    set f₀ : G := (f : G) with hf₀
    have hc : g⁻¹ * f₀ ∈ centralizer (L : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun α : MulAut ↥L => ((α ⟨w, hw⟩ : ↥L) : G)) hf
      simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h2
      calc w * (g⁻¹ * f₀) = g⁻¹ * (g * w * g⁻¹) * f₀ := by group
        _ = g⁻¹ * (f₀ * w * f₀⁻¹) * f₀ := by rw [← h2]
        _ = g⁻¹ * f₀ * w := by group
    rw [hC, mem_bot, inv_mul_eq_one] at hc
    rw [hc]
    exact f.2
  have hker' : ∀ g ∈ L, ψ g = 1 := by
    intro g hg
    refine (QuotientGroup.eq_one_iff (N := inner ↥L) _).mpr ⟨⟨g, hg⟩, ?_⟩
    exact MulAut.conjNormal_val.symm
  have hsq : ∀ g : G, g * g ∈ L → ψ g * ψ g = 1 := fun g hg => by
    rw [← map_mul]
    exact hker' _ hg
  have hTot := CFSG.ClassicalInvolution.Q3.TL4.Bend.twoTot_outer (F := ↥L) hB
  have hP : IsPGroup 2 ↥(S.map ψ) := hS.map ψ
  rcases hTot _ hP (ψ x) ⟨x, hx, rfl⟩ (ψ y) ⟨y, hy, rfl⟩ with h | h
  · rcases u3_eq_one_or_eq_of_mem_zpowers_sq (hsq y hy2) h with h1 | h1
    · exact Or.inl (hker x h1)
    · exact Or.inr (Or.inr (hker (x * y) (by rw [map_mul, h1]; exact hsq y hy2)))
  · rcases u3_eq_one_or_eq_of_mem_zpowers_sq (hsq x hx2) h with h1 | h1
    · exact Or.inr (Or.inl (hker y h1))
    · exact Or.inr (Or.inr (hker (x * y) (by rw [map_mul, h1]; exact hsq x hx2)))

theorem u3_invols_commute {G : Type} [Group G] [Finite G] (L : Subgroup G) [L.Normal]
    [IsSimpleGroup ↥L] (hnab : ¬ IsMulCommutative ↥L) {n : ℕ} (e : ↥L ≃* PSU3Model n)
    (S : Sylow 2 G) {x y : G} (hx : x ∈ (S : Subgroup G) ⊓ L) (hy : y ∈ (S : Subgroup G) ⊓ L)
    (hx2 : x * x = 1) : x * y = y * x := by
  classical
  obtain ⟨P, hPeq⟩ := CFSG.Glauberman.sylow_inf_normal (p := 2) S (N := L)
  have hB := psu3_benderType hnab e
  obtain ⟨t, hc⟩ := hB.exists_benderCore P
  have hxP : (⟨x, hx.2⟩ : ↥L) ∈ (P : Subgroup ↥L) := by
    rw [hPeq]
    exact Subgroup.mem_subgroupOf.mpr hx
  have hyP : (⟨y, hy.2⟩ : ↥L) ∈ (P : Subgroup ↥L) := by
    rw [hPeq]
    exact Subgroup.mem_subgroupOf.mpr hy
  by_cases hx1 : (⟨x, hx.2⟩ : ↥L) = 1
  · have : x = 1 := congrArg Subtype.val hx1
    rw [this]
    simp
  · have hord : orderOf (⟨x, hx.2⟩ : ↥L) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact Subtype.ext hx2) hx1
    have hmem := hc.center_of_involution _ (le_borel _ hxP) hord
    have := (mem_rootCenter_iff.mp hmem).2 _ hyP
    exact (congrArg Subtype.val this).symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW

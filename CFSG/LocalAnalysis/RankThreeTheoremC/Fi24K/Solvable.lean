module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

open CFSG.HardMathSupport.Dickson.I271 Subgroup

theorem normalizer_le_normalizer_zpowers {G : Type} [Group G] [Finite G] {c : G}
    {F : Subgroup G} (hL : SevenLine 7 c F) :
    normalizer (F : Set G) ≤ normalizer ((zpowers c : Subgroup G) : Set G) := by
  have hZmap : ∀ h ∈ normalizer (F : Set G), ∀ z ∈ Subgroup.zpowers c,
      h * z * h⁻¹ ∈ Subgroup.zpowers c := by
    intro h hh z hz
    have hzF : z ∈ F := (Subgroup.zpowers_le.mpr hL.mem) hz
    have hmemF : h * z * h⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hh z).mp hzF
    refine hL.center_le hmemF ?_
    intro q hq
    have hqh : h⁻¹ * q * h ∈ F := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) q).mp hq
    have hzq : z * (h⁻¹ * q * h) = (h⁻¹ * q * h) * z := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← hk]
      exact (show Commute c (h⁻¹ * q * h) from hL.comm_w hqh).zpow_left k
    calc (h * z * h⁻¹) * q = h * (z * (h⁻¹ * q * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * q * h) * z) * h⁻¹ := by rw [hzq]
      _ = q * (h * z * h⁻¹) := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hZmap g hg x
  · intro hx
    have hthis := hZmap g⁻¹ (Subgroup.inv_mem _ hg) (g * x * g⁻¹) hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at hthis

theorem isSolvable_normalizer_zpowers {G : Type} [Group G] [Finite G] {c : G}
    {F : Subgroup G} (hL : SevenLine 7 c F)
    (hC : Nat.card (centralizer ({c} : Set G)) = 7 ^ 3 * 6) :
    IsSolvable (normalizer ((zpowers c : Subgroup G) : Set G)) := by
  have hfact : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let C : Subgroup G := Subgroup.centralizer ({c} : Set G)
  let N : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)
  have hFC : F ≤ C := hL.le_cent
  haveI hCn : (F.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFC]
    exact Subgroup.le_normalizer_iff.mpr hL.norm
  have hFcard : Nat.card ↥(F.subgroupOf C) = 7 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hL.card_eq]
  haveI hFp : IsPGroup 7 ↥(F.subgroupOf C) := IsPGroup.of_card (n := 3) hFcard
  haveI : Group.IsNilpotent ↥(F.subgroupOf C) := hFp.isNilpotent
  haveI : Group.IsSolvable ↥(F.subgroupOf C) := IsNilpotent.to_isSolvable
  have hquot : Nat.card (↥C ⧸ F.subgroupOf C) = 6 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (F.subgroupOf C)
    rw [hC, hFcard] at h1
    have h2 : Nat.card (↥C ⧸ F.subgroupOf C) * 7 ^ 3 = 6 * 7 ^ 3 := by
      calc Nat.card (↥C ⧸ F.subgroupOf C) * 7 ^ 3 = 7 ^ 3 * 6 := h1.symm
        _ = 6 * 7 ^ 3 := by ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  let _ : Fintype (↥C ⧸ F.subgroupOf C) := Fintype.ofFinite _
  haveI : Group.IsSolvable (↥C ⧸ F.subgroupOf C) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 1) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
      (by rw [Fintype.card_eq_nat_card, hquot]; norm_num)
  have hCsolv : Group.IsSolvable ↥C :=
    Group.isSolvable_of_subgroup_quotient (F.subgroupOf C)
  have hCN : C ≤ N := by
    have h := Subgroup.centralizer_le_normalizer ((Subgroup.zpowers c : Subgroup G) : Set G)
    simpa [C, N, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using h
  let f : ↥C →* ↥N := Subgroup.inclusion hCN
  let ρ : ↥N →* MulAut ↥(Subgroup.zpowers c) :=
    (Subgroup.zpowers c).normalizerMonoidHom
  have hker : ρ.ker ≤ f.range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxc : (x : G) ∈ C := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : ρ x ⟨c, Subgroup.mem_zpowers c⟩ = ⟨c, Subgroup.mem_zpowers c⟩ := by
        rw [hx, MulAut.one_apply]
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxc⟩, Subtype.ext rfl⟩
  haveI : Group.IsSolvable ↥C := hCsolv
  haveI : IsCyclic ↥(Subgroup.zpowers c) := Subgroup.isCyclic_zpowers c
  haveI : Group.IsSolvable (MulAut ↥(Subgroup.zpowers c)) :=
    CFSG.ProperTwoGeneratedCore.cyclic_automorphism_solvable _
  exact Group.isSolvable_of_ker_le_range f ρ hker

end CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K

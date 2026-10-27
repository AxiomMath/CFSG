module

public import CFSG.Fischer.Classification.PartII.O2G.Section
public import CFSG.Fischer.Classification.PartII.O2Two
public import CFSG.Fischer.Classification.PartII.O2Bridge

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin LocalR3

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem ncard_twinClass_lqMap (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d a : G} (hd : d ∈ D) (ha : a ∈ LocalClass D d) :
    (twinClass (LocalImages D d) (lqMap D d a)).ncard = (twinClass (LocalClass D d) a).ncard := by
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  rw [O2Bridge.twinClass_lqMap hP hZ hS hd ha, (hι.injOn.mono fun b hb => hb.2.1).ncard_image]

end O2G

open O2G

theorem o2_r_ne_two {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : NonabelianCommutator G) (hs : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {a : G} (ha : a ∈ LocalClass D d) :
    {b | LocalU.IsTwin (LocalClass D d) a b}.ncard ≠ 2 := by
  intro htwo
  have hP := hH.pair
  have hZ := hH.center
  have hS := hH.simple
  have := Pair.finite hP
  have hPH := Pair.pair_localQuotient hP hZ hS hna hd
  have hι := Pair.isChart_lqMap hP (Pair.starImage_injective_of_simple hP hZ hS hd)
  have h2H : ∀ x ∈ LocalImages D d, (twinClass (LocalImages D d) x).ncard = 2 := by
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hι.exists_eq hx
    rw [ncard_twinClass_lqMap hP hZ hS hd hf, ncard_twinClass_eq hP hZ hS hd hf ha]
    exact htwo
  have hsec : ∀ y ∈ D, y * d ≠ d * y →
      O2Mod.IsTwinSection (LocalImages D d) (lqMap D d '' muSet D d y) := fun y hy hyd =>
    O2Bridge.isTwinSection_image hP hZ hS hd (o2_O1 hH hna hd h2 hy hyd).1
      (o2_O1 hH hna hd h2 hy hyd).2
  simp only [IsSymplecticType, not_forall, not_or] at hs
  obtain ⟨a₀, ha₀, b₀, hb₀, z₀, hz₀, hab₀, hza₀, hzb₀, hzl₀⟩ := hs
  obtain ⟨g, hg, hga⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd ha
  obtain ⟨h, hha, hhg⟩ := Pair.exists_conj_pair_of_not_commute hP hZ hS hna ha₀ hb₀ ha.1 hg.1
    hab₀ fun e => hga e.symm
  set z := h * z₀ * h⁻¹ with hzdef
  have hzD : z ∈ D := Pair.conj_mem hP hz₀ h
  have hza : z * a ≠ a * z := by
    rw [← hha, hzdef, Ne, conj_commute_iff]
    exact hza₀
  have hzg : z * g ≠ g * z := by
    rw [← hhg, hzdef, Ne, conj_commute_iff]
    exact hzb₀
  have hzl : z * (a * g * a) ≠ a * g * a * z := by
    have e : a * g * a = h * (a₀ * b₀ * a₀) * h⁻¹ := by rw [← hha, ← hhg]; group
    rw [e, hzdef, Ne, conj_commute_iff]
    exact hzl₀
  have hag : a * g ≠ g * a := fun e => hga e.symm
  have haga : a * g * a ∈ LocalClass D d := Pair.mul_mul_mem_localClass_of_mem hP ha hg
  have hmap := LocalU.lqMap_mul_mul ha hg
  by_cases hzd : z * d = d * z
  ·
    have hzloc : z ∈ LocalClass D d := ⟨hzD, fun e => hza (by rw [e, ha.2.2]), hzd⟩
    obtain ⟨y, hy, hyd⟩ := O2Twin.exists_not_commute_of_mem hP hZ hd
    have hμ := hsec y hy fun e => hyd e.symm
    have hc := hμ.commute_of_two hPH h2H (hι.mem ha) (hι.mem hg) (hι.mem hzloc)
      (fun e => hag ((hι.comm_iff a ha g hg).2 e))
      (fun e => hzg ((hι.comm_iff z hzloc g hg).2 e.symm))
      (fun e => hza ((hι.comm_iff z hzloc a ha).2 e.symm))
    rw [← hmap] at hc
    exact hzl ((hι.comm_iff z hzloc _ haga).2 hc)
  ·
    have hμ := hsec z hzD hzd
    have hsub : muSet D d z ⊆ LocalClass D d := fun x hx => hx.1
    have hnot : ∀ x ∈ LocalClass D d, x * z ≠ z * x → lqMap D d x ∉ lqMap D d '' muSet D d z := by
      rintro x hx hxz ⟨m, hm, hmx⟩
      rw [hι.injOn (hsub hm) hx hmx] at hm
      exact hxz hm.2.2.2
    have hmem := hμ.mul_mul_mem_of_two hPH h2H (hι.mem ha) (hnot a ha fun e => hza e.symm)
      (hι.mem hg) (hnot g hg fun e => hzg e.symm)
      (fun e => hag ((hι.comm_iff a ha g hg).2 e))
    rw [← hmap] at hmem
    obtain ⟨m, hm, hmx⟩ := hmem
    rw [hι.injOn (hsub hm) haga hmx] at hm
    exact hzl hm.2.2.2.symm

end CFSG.Fischer.Classification

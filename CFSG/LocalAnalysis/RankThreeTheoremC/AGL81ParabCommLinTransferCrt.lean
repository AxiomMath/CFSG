module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import Mathlib.Tactic.LinearCombination
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

theorem exists_zpow_split {G : Type*} [Group G] {m o : ℕ} (hmo : Nat.Coprime m o) {g : G}
    (hgo : (g ^ m) ^ o = 1) :
    ∃ a b : ℤ, g = g ^ (b * (o : ℤ)) * (g ^ m) ^ a ∧ (g ^ (b * (o : ℤ))) ^ m = 1 := by
  have hbez : ((Nat.gcd m o : ℕ) : ℤ) = m * Nat.gcdA m o + o * Nat.gcdB m o :=
    Nat.gcd_eq_gcd_ab m o
  rw [hmo.gcd_eq_one] at hbez
  refine ⟨Nat.gcdA m o, Nat.gcdB m o, ?_, ?_⟩
  · have h1 : Nat.gcdB m o * (o : ℤ) + (m : ℤ) * Nat.gcdA m o = 1 := by
      linear_combination -hbez
    rw [← zpow_natCast g m, ← zpow_mul, ← zpow_add, h1, zpow_one]
  · have h2 : (g ^ (Nat.gcdB m o * (o : ℤ))) ^ m = ((g ^ m) ^ o) ^ Nat.gcdB m o := by
      rw [← zpow_natCast (g ^ (Nat.gcdB m o * (o : ℤ))) m, ← zpow_natCast (g ^ m) o,
        ← zpow_natCast g m, ← zpow_mul, ← zpow_mul, ← zpow_mul]
      congr 1
      ring
    rw [h2, hgo, one_zpow]

theorem isNilpotent_comap_of_isPGroup {G H : Type} [Group G] [Finite G] [Group H] (π : G →* H)
    (hker : π.ker ≤ Subgroup.center G) {T : Subgroup H} (hT : IsPGroup 2 T) :
    Group.IsNilpotent ↥(T.comap π) := by
  set f : ↥(T.comap π) →* H := π.comp (T.comap π).subtype
  have hrange : f.range ≤ T := by
    rintro _ ⟨x, rfl⟩
    exact x.2
  haveI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  haveI : Group.IsNilpotent ↥f.range := (hT.to_le hrange).isNilpotent
  refine Subgroup.isNilpotent_of_ker_le_center f.rangeRestrict ?_
  intro x hx
  have hx1 : π (x : G) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hx1) (y : G))

theorem exists_mul_of_comap_isPGroup {G H : Type} [Group G] [Finite G] [Group H] (π : G →* H)
    (hker : π.ker ≤ Subgroup.center G) {o : ℕ} (ho : Odd o) (hz : ∀ z ∈ π.ker, z ^ o = 1)
    {T : Subgroup H} [T.Normal] (hT : IsPGroup 2 T) {g : G} (hg : π g ∈ T) :
    ∃ s ∈ CFSG.pCore 2 G, ∃ z ∈ π.ker, g = s * z := by
  have hnil := isNilpotent_comap_of_isPGroup π hker hT
  haveI hNn : (T.comap π).Normal := inferInstance
  obtain ⟨k, hk⟩ := hT ⟨π g, hg⟩
  have hk' : π g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hu : g ^ 2 ^ k ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hk']
  obtain ⟨a, b, hg_eq, hs⟩ :=
    exists_zpow_split (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 ho)) (hz _ hu)
  have hsN : g ^ (b * (o : ℤ)) ∈ T.comap π := by
    rw [Subgroup.mem_comap, map_zpow]
    exact Subgroup.zpow_mem _ hg _
  let sN : ↥(T.comap π) := ⟨g ^ (b * (o : ℤ)), hsN⟩
  have hsN2 : sN ^ 2 ^ k = 1 := Subtype.ext hs
  have hP : IsPGroup 2 ↥(Subgroup.zpowers sN) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    refine ⟨k, Subtype.ext ?_⟩
    change (sN ^ n) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hsN2, one_zpow]
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hsS : sN ∈ (S : Subgroup ↥(T.comap π)) := hS (Subgroup.mem_zpowers sN)
  have hmem : g ^ (b * (o : ℤ)) ∈ (S : Subgroup ↥(T.comap π)).map (T.comap π).subtype :=
    Subgroup.mem_map.2 ⟨sN, hsS, rfl⟩
  exact ⟨g ^ (b * (o : ℤ)), Sylow.map_le_pCore hNn hnil 2 S hmem, _,
    Subgroup.zpow_mem _ hu a, hg_eq⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin

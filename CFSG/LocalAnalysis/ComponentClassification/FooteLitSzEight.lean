module

public import CFSG.Goldschmidt.Steps.G3MFSz8
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGoldschmidtBender
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAschbacherOne

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter)
open scoped commutatorElement

theorem isQuasisimple_of_isCoverOverTwo {Y X : Type*} [Group Y] [Group X] [hX : IsSimpleGroup X]
    (hna : ∃ a b : X, a * b ≠ b * a) {π : Y →* X} (hπs : Function.Surjective π)
    (hKZ : π.ker ≤ center Y) (hKC : π.ker ≤ commutator Y) :
    CFSG.IsQuasisimple Y ∧ π.ker = center Y := by
  obtain ⟨a, b, hab⟩ := hna
  have hZK : center Y ≤ π.ker := by
    have hn : ((center Y).map π).Normal :=
      (Subgroup.normal_of_characteristic _).map π hπs
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      apply hab
      obtain ⟨y, hy, rfl⟩ : b ∈ (center Y).map π := h ▸ mem_top b
      obtain ⟨x, rfl⟩ := hπs a
      rw [← map_mul, ← map_mul, mem_center_iff.mp hy x]
  have hker : π.ker = center Y := le_antisymm hKZ hZK
  have hXperf : commutator X = ⊤ := by
    rcases (commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      apply hab
      have h1 : ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup X), ⊤⁆ :=
        commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · rw [_root_.commutator_def]
      exact h
  have hperf : commutator Y = ⊤ := by
    have hmap : (commutator Y).map π = ⊤ := by
      rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hπs, ← _root_.commutator_def, hXperf]
    have h1 := comap_map_eq π (commutator Y)
    rw [hmap, comap_top, sup_eq_left.mpr hKC] at h1
    exact h1.symm
  have e : Y ⧸ center Y ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπs)
  refine ⟨⟨⟨hperf⟩, e.isSimpleGroup_congr.mpr hX, ⟨e.symm a, e.symm b, fun h => hab ?_⟩⟩, hker⟩
  apply e.symm.injective
  rw [map_mul, map_mul, h]

theorem sz_one_simple_nonabelian [Finite (Open.Sz 1)] :
    IsSimpleGroup (Open.Sz 1) ∧ ∃ a b : Open.Sz 1, a * b ≠ b * a := by
  have hB : Open.fusionIsBenderGroup (Open.Sz 1) := Or.inr (Or.inr ⟨1, le_rfl, ⟨MulEquiv.refl _⟩⟩)
  refine ⟨QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB, ?_⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 (Open.Sz 1)))
  obtain ⟨-, -, -, hZ, hQ⟩ := Open.bender_suzuki_borel_full 1 le_rfl Q
  by_contra hcon
  push Not at hcon
  have hc : center (Q : Subgroup (Open.Sz 1)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (hcon _ _)
  rw [hc, card_top] at hZ
  rw [hZ] at hQ
  norm_num at hQ

theorem sq_eq_one_of_sq_mem_center_sz {Y : Type*} [Group Y] [Finite Y]
    (h : IsCoverOverTwo Y (Open.Sz 1)) {y : Y} (hy : y ^ 2 ∈ center Y) : y ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπs, hKZ, hKC, hK2⟩ := h
  have : Finite (Open.Sz 1) := Finite.of_surjective π hπs
  obtain ⟨hsimp, hna⟩ := sz_one_simple_nonabelian
  obtain ⟨-, hker⟩ := isQuasisimple_of_isCoverOverTwo hna hπs hKZ hKC
  have hZ2 : ∀ z ∈ center Y, z ^ 2 = 1 := by
    intro z hz
    rw [← hker] at hz
    have h1 := Subgroup.orderOf_dvd_natCard π.ker hz
    rw [hK2] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  have hπy : π y ^ 2 = 1 := by
    rw [← map_pow]
    rw [← hker] at hy
    exact hy
  by_cases hy1 : π y = 1
  · have hyZ : y ∈ center Y := hker ▸ (MonoidHom.mem_ker.mpr hy1)
    exact hZ2 y hyZ
  have hyp : IsPGroup 2 (zpowers (π y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hπy hy1
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  have hyQ : π y ∈ (Q : Subgroup (Open.Sz 1)) := hQ (mem_zpowers _)
  have hB := Open.bender_suzuki_borel_full 1 le_rfl
  have hyZ : π y ∈ sylowCenter (Q : Subgroup (Open.Sz 1)) :=
    AschbacherToolkit.Goldschmidt.mem_sylowCenter_of_sq_eq_one hB (by norm_num) Q hyQ hπy
  have hkerp : IsPGroup 2 π.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  set T : Sylow 2 Y := Q.comapOfKerIsPGroup π hkerp
    (by rw [MonoidHom.range_eq_top.mpr hπs]; exact le_top) with hTdef
  have hyT : y ∈ (T : Subgroup Y) := hyQ
  have hb : ∀ x ∈ (T : Subgroup Y), y * x * y⁻¹ * x⁻¹ ∈ center Y := by
    intro x hx
    rw [← hker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hxQ : π x ∈ (Q : Subgroup (Open.Sz 1)) := hx
    rw [((mem_sylowCenter.mp hyZ).2 (π x) hxQ).symm]
    group
  exact (Goldschmidt.MFSz8.comm_and_sq_of_benderBorel hB (by norm_num) π hπs hker hZ2 T hyT hyT
    hb hb).2

end CFSG.ComponentClassification.FooteLit

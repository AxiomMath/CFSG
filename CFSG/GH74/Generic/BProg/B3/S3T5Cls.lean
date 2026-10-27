module

public import CFSG.GH74.Generic.BProg.B3.S3T5Facts
public import CFSG.GH74.Generic.BProg.B3.LocBalL3

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3T5

namespace W

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.ClassicalInvolution.Balance Subgroup

theorem exists_four_le {X : Type*} [Group X] [Finite X] {F : Subgroup X}
    (hF4 : 2 ^ 2 ≤ Nat.card F) (hF2 : ∀ f ∈ F, f * f = 1) :
    ∃ D : Subgroup X, D ≤ F ∧ Nat.card D = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥F := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hF2 g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  have h2n : 2 ≤ n := by
    by_contra hlt
    have h1 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨D', hD'⟩ := Sylow.exists_subgroup_card_pow_prime 2
    (show 2 ^ 2 ∣ Nat.card F by rw [hn]; exact pow_dvd_pow 2 h2n)
  refine ⟨D'.map F.subtype, Subgroup.map_subtype_le D', ?_⟩
  rw [Subgroup.card_map_of_injective F.subtype_injective, hD']
  norm_num

theorem deltaCore_anti {X : Type*} [Group X] {D F : Subgroup X} (h : D ≤ F) :
    deltaCore F ≤ deltaCore D :=
  le_deltaCore fun _ hd hd1 => deltaCore_le_involutionOddCore (h hd) hd1

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (hc : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hkc : k ∈ center K := Subgroup.mem_center_iff.mpr fun g => by
    have h1 : k * g * k⁻¹ = g := by
      have := congrArg (fun φ : MulAut K => φ g) hk
      simpa only [MulAut.conj_apply, MulAut.one_apply] using this
    calc g * k = k * g * k⁻¹ * k := by rw [h1]
      _ = k * g := by group
  rw [hc, Subgroup.mem_bot] at hkc
  exact hkc

theorem isLocallyKBalanced_two_of_l3 (hF2 : L3OuterOddCore) {Kt : Type} [Group Kt] [Finite Kt]
    (hK : IsL3OddGt3 Kt) (hc : center Kt = ⊥) : Th2.Bal.IsLocallyKBalanced 2 Kt := by
  classical
  intro H hInn F hF4 hFsq
  by_cases hout : ∃ f ∈ F, (f : MulAut Kt) ∉ (MulAut.conj : Kt →* MulAut Kt).range
  · obtain ⟨f, hfF, hfo⟩ := hout
    have hf1 : f ≠ 1 := by
      rintro rfl
      exact hfo ⟨1, map_one _⟩
    have hbot := hF2 Kt hK H hInn f (hFsq f hfF) hfo
    exact le_bot_iff.mp ((deltaCore_le_involutionOddCore hfF hf1).trans hbot.le)
  · push Not at hout
    have hinj := conj_injective_of_center_eq_bot hc
    set B₀ : Subgroup Kt := (F.map H.subtype).comap (MulAut.conj : Kt →* MulAut Kt)
    have hB₀2 : ∀ k ∈ B₀, k * k = 1 := by
      intro k hk
      obtain ⟨f, hfF, hfk⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hk)
      apply hinj
      rw [map_mul, map_one, ← hfk]
      exact congrArg Subtype.val (hFsq f hfF)
    have hFB : F ≤ (B₀.map (MulAut.conj : Kt →* MulAut Kt)).subgroupOf H := by
      intro f hfF
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨k, hk⟩ := hout f hfF
      refine ⟨k, ?_, hk⟩
      show MulAut.conj k ∈ F.map H.subtype
      rw [hk]
      exact Subgroup.mem_map_of_mem H.subtype hfF
    have hBH : B₀.map (MulAut.conj : Kt →* MulAut Kt) ≤ H := by
      rintro _ ⟨k, -, rfl⟩
      exact hInn ⟨k, rfl⟩
    obtain ⟨D, hDF, hD4⟩ := exists_four_le hF4 hFsq
    have hloc := (locBal32_L3_gen hK B₀ hB₀2 H hInn hBH).2 D (hDF.trans hFB) hD4
      (fun d hd => hFsq d (hDF hd))
    exact le_bot_iff.mp ((deltaCore_anti hDF).trans hloc.le)

end W

end S3T5

end CFSG.GH74.Generic.BProg.B3

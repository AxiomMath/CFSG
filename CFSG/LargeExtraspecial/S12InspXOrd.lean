module

public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
public import CFSG.LargeExtraspecial.S12Classify

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

theorem card_dvd_card_mul_card_outer_of_normal {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} [N.Normal] (hC : centralizer (N : Set H) = ⊥) (hZ : center N = ⊥) :
    Nat.card H ∣ Nat.card N * Nat.card (Outer N) := by
  set ψ : H →* MulAut N := MulAut.conjNormal with hψ
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hC]
    intro h hh
    rw [mem_centralizer_iff]
    intro n hn
    have e := congrArg (fun σ : MulAut N => ((σ ⟨n, hn⟩ : N) : H)) (MonoidHom.mem_ker.mp hh)
    simp only [hψ, MulAut.conjNormal_apply, MulAut.one_apply] at e
    calc n * h = h * n * h⁻¹ * h := by rw [e]
      _ = h * n := by group
  have hA : inner N ≤ ψ.range := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(n : H), ?_⟩
    rw [hψ, MulAut.conjNormal_val]
  have h1 := CFSG.LocalAnalysis.ComponentInitial.card_dvd_card_mul_card_outer hZ hA
  rwa [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv] at h1

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem le_seven_of_two_pow_dvd_card_Xbar12
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7) {g : G} {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card (S.Xbar12 g)) : k ≤ 7 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPc⟩ := Sylow.exists_subgroup_card_pow_prime 2 hk
  have hle : P.map (S.Xbar12 g).subtype ≤ S.Mbar :=
    (map_subtype_le P).trans Xbar12_le_Mbar
  have hc : Nat.card ((P.map (S.Xbar12 g).subtype).subgroupOf S.Mbar) = 2 ^ k := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      card_map_of_injective (subtype_injective _), hPc]
  have h7 := hP _ (IsPGroup.of_card hc)
  rw [hc] at h7
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h7

theorem card_Mbar_dvd_card_Xbar12_mul_card_outer {g : G} {t : S.O} (hS : S.S12Standing g t) :
    Nat.card S.Mbar ∣ Nat.card (S.Xbar12 g) * Nat.card (Outer (S.Xbar12 g)) := by
  set N := (S.Xbar12 g).subgroupOf S.Mbar with hNdef
  have hN : N.Normal := ⟨fun n hn m => by
    rw [hNdef, mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 m.2) (n : S.O)).mp hn
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this⟩
  have hC : centralizer (N : Set S.Mbar) = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have hmC : (m : S.O) ∈ S.CXbar12 g := by
      refine ⟨m.2, mem_centralizer_iff.mpr fun y hy => ?_⟩
      have h := mem_centralizer_iff.mp hm ⟨y, Xbar12_le_Mbar hy⟩
        (show (⟨y, Xbar12_le_Mbar hy⟩ : S.Mbar) ∈ N from hy)
      exact congrArg Subtype.val h
    rw [hS.cent, mem_bot] at hmC
    exact (mem_bot).mpr (Subtype.ext hmC)
  have hZ : center N = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : ((z : S.Mbar) : S.O) = 1 := hS.center_trivial _ z.2 fun x hx => by
      have h := mem_center_iff.mp hz ⟨⟨x, Xbar12_le_Mbar hx⟩, hx⟩
      exact congrArg (fun w : N => ((w : S.Mbar) : S.O)) h
    exact (mem_bot).mpr (Subtype.ext (Subtype.ext h1))
  have h := card_dvd_card_mul_card_outer_of_normal hC hZ
  have e : N ≃* S.Xbar12 g := subgroupOfEquivOfLe Xbar12_le_Mbar
  rwa [Nat.card_congr e.toEquiv, Nat.card_congr (equivalence e).toEquiv] at h

theorem three_pow_four_dvd_of_insp4 {g : G} {t : S.O} (hS : S.S12Standing g t)
    (hM : 25920 ∣ Nat.card S.Mbar) :
    3 ^ 4 ∣ Nat.card (S.Xbar12 g) * Nat.card (Outer (S.Xbar12 g)) :=
  ((by norm_num : 3 ^ 4 ∣ 25920).trans hM).trans (card_Mbar_dvd_card_Xbar12_mul_card_outer hS)

end Setting

end CFSG.LargeExtraspecial

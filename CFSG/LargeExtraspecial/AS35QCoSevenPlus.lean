module

public import CFSG.LargeExtraspecial.AS35QCoSeven

import CFSG.GF2Type.Smith1979.W4AsE11Surv

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo.Seven

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem card_subtype_modEq_card_fixed {p : ℕ} [Fact p.Prime] {g : V ≃ₗ[ZMod 2] V}
    (hg : g ^ p = 1) {P : V → Prop} (hP : ∀ v, P v → P (g v)) :
    Nat.card {v : V // P v} ≡ Nat.card {v : V // P v ∧ g v = v} [MOD p] := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype {v : V // P v} := Fintype.ofFinite _
  let f : Function.End {v : V // P v} := fun v => ⟨g v, hP v v.2⟩
  have hfp : ∀ k : ℕ, ∀ v : {v : V // P v}, ((f ^ k) v : V) = (g ^ k) v := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
      intro v
      rw [pow_succ', pow_succ', LinearEquiv.mul_apply]
      exact congrArg g (ih v)
  have hf : f ^ p ^ 1 = 1 := by
    funext v
    apply Subtype.ext
    rw [pow_one, hfp, hg]
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq hf
  rw [← Nat.card_eq_fintype_card] at h
  convert h using 1
  rw [Fintype.card_eq_nat_card]
  apply Nat.card_congr
  exact {
    toFun := fun v => ⟨⟨v.1, v.2.1⟩, by
      change f _ = _
      apply Subtype.ext
      exact v.2.2⟩
    invFun := fun v => ⟨v.1.1, v.1.2, congrArg Subtype.val (v.2 : f v.1 = v.1)⟩
    left_inv := fun v => rfl
    right_inv := fun v => rfl }


namespace Hyp

variable {q : QuadraticForm (ZMod 2) V} {x : V ≃ₗ[ZMod 2] V}

theorem eq_one_of_commute_of_totallySingular (hx : Hyp q x) {W : Submodule (ZMod 2) V}
    (hW4 : finrank (ZMod 2) W = 4) (hW : ∀ v ∈ W, q v = 0) {c : V ≃ₗ[ZMod 2] V}
    (hc : ∀ v, q (c v) = q v) (hc3 : c ^ 3 = 1) (hcx : c * x = x * c) : c = 1 := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h136 : Nat.card {v : V // q v = 0} = 136 :=
    CFSG.GF2Type.Smith1979.W4As.card_singular_eq_136 hx.nondeg hx.dim hW4 hW
  have hxc : ∀ v, x (c v) = c (x v) := fun v => by
    have := congrArg (fun m : V ≃ₗ[ZMod 2] V => m v) hcx
    exact this.symm
  have h7 := card_subtype_modEq_card_fixed (p := 7) hx.pow (P := fun v => q v = 0)
    (fun v hv => by rw [hx.isom]; exact hv)
  rw [h136] at h7
  have hF2 : Nat.card ↥(fixSpace x) = 4 := by
    rw [natCard_submodule, hx.finrank_fixSpace.1]
    norm_num
  have hS1le : Nat.card {v : V // q v = 0 ∧ x v = v} ≤ 4 := by
    rw [← hF2]
    exact Nat.card_le_card_of_injective (fun v => ⟨v.1, mem_fixSpace.mpr v.2.2⟩)
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hS1pos : 0 < Nat.card {v : V // q v = 0 ∧ x v = v} := by
    haveI : Nonempty {v : V // q v = 0 ∧ x v = v} :=
      ⟨⟨0, by rw [QuadraticMap.map_zero], map_zero x⟩⟩
    exact Nat.card_pos
  have hS1 : Nat.card {v : V // q v = 0 ∧ x v = v} = 3 := by
    unfold Nat.ModEq at h7
    omega
  have h3 := card_subtype_modEq_card_fixed (p := 3) hc3 (P := fun v => q v = 0 ∧ x v = v)
    (fun v hv => ⟨by rw [hc]; exact hv.1, by rw [hxc, hv.2]⟩)
  rw [hS1] at h3
  have hinj : Function.Injective
      (fun v : {v : V // (q v = 0 ∧ x v = v) ∧ c v = v} =>
        (⟨v.1, v.2.1⟩ : {v : V // q v = 0 ∧ x v = v})) :=
    fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab)
  have hS2le : Nat.card {v : V // (q v = 0 ∧ x v = v) ∧ c v = v} ≤ 3 := by
    rw [← hS1]
    exact Nat.card_le_card_of_injective _ hinj
  have hS2pos : 0 < Nat.card {v : V // (q v = 0 ∧ x v = v) ∧ c v = v} := by
    haveI : Nonempty {v : V // (q v = 0 ∧ x v = v) ∧ c v = v} :=
      ⟨⟨0, ⟨by rw [QuadraticMap.map_zero], map_zero x⟩, map_zero c⟩⟩
    exact Nat.card_pos
  have hS2 : Nat.card {v : V // (q v = 0 ∧ x v = v) ∧ c v = v} = 3 := by
    unfold Nat.ModEq at h3
    omega
  have hbij := hinj.bijective_of_nat_card_le (by rw [hS1, hS2])
  have hfix : ∀ v : V, q v = 0 → x v = v → c v = v := by
    intro v hq hxv
    obtain ⟨u, hu⟩ := hbij.2 ⟨v, hq, hxv⟩
    have h : (u.1 : V) = v := congrArg Subtype.val hu
    rw [← h]
    exact u.2.2
  have hF'ge : 3 ≤ Nat.card ↥(fixSpace x ⊓ fixSpace c) := by
    rw [← hS1]
    exact Nat.card_le_card_of_injective
      (fun v => ⟨v.1, Submodule.mem_inf.mpr
        ⟨mem_fixSpace.mpr v.2.2, mem_fixSpace.mpr (hfix v.1 v.2.1 v.2.2)⟩⟩)
      (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hF'dim : finrank (ZMod 2) ↥(fixSpace x ⊓ fixSpace c) = 2 := by
    have hle : finrank (ZMod 2) ↥(fixSpace x ⊓ fixSpace c) ≤ 2 :=
      le_trans (Submodule.finrank_mono inf_le_left) (le_of_eq hx.finrank_fixSpace.1)
    by_contra hne
    have h1 : finrank (ZMod 2) ↥(fixSpace x ⊓ fixSpace c) ≤ 1 := by omega
    have h2 : Nat.card ↥(fixSpace x ⊓ fixSpace c) ≤ 2 := by
      rw [natCard_submodule]
      calc 2 ^ finrank (ZMod 2) ↥(fixSpace x ⊓ fixSpace c) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    omega
  have hFle : fixSpace x ≤ fixSpace c := by
    have heq : fixSpace x ⊓ fixSpace c = fixSpace x :=
      Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hF'dim, hx.finrank_fixSpace.1])
    calc fixSpace x = fixSpace x ⊓ fixSpace c := heq.symm
      _ ≤ fixSpace c := inf_le_right
  have hcomm : commSpace x ≤ fixSpace c :=
    hx.commSpace_le_fixSpace_of_comm hcx (Or.inr hc3)
  ext v
  have hv : v ∈ fixSpace x ⊔ commSpace x := by
    rw [hx.fixSpace_sup_commSpace]
    exact Submodule.mem_top
  obtain ⟨f, hf, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, mem_fixSpace.mp (hFle hf), mem_fixSpace.mp (hcomm hu)]
  rfl

end Hyp

end CFSG.LargeExtraspecial.AS35QCo.Seven

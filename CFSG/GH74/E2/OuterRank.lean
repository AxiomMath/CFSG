module

public import CFSG.GH74.E2.Ext2
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public import CFSG.GH74.E2.FrattiniRank
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.OuterRankInputs
public meta import CFSG.GH74.E2.OuterRankInputs
public import Certificates.Certificate5016

public section

namespace CFSG.GH74.E2.OuterRank

open CFSG.Semidihedral

attribute [local instance] CFSG.GH74.E2.OuterRank.instDecEqSD

theorem chiL_map_one_check : Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (1 : SD).left)) = 1 :=
  Certificates.certificate5016.2.2.2.2.2.1

theorem chiL_map_mul_check : ∀ x y : SD,
    Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd (x * y).left)) =
      Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd x.left)) * Multiplicative.ofAdd (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd y.left)) :=
  Certificates.certificate5016.2.2.2.2.2.2.1

theorem chiR_map_mul_check : ∀ x y : SD, (x * y).right = x.right * y.right :=
  Certificates.certificate5016.2.2.2.2.2.2.2

@[expose] def chiL : SD →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd
    (ZMod.castHom (by decide : 2 ∣ modulus 4) (ZMod 2) (Multiplicative.toAdd g.left))
  map_one' := chiL_map_one_check
  map_mul' := chiL_map_mul_check

@[expose] def chiR : SD →* Multiplicative (ZMod 2) where
  toFun g := g.right
  map_one' := rfl
  map_mul' := chiR_map_mul_check

theorem chi_surj :
    ∀ v w : Multiplicative (ZMod 2), ∃ m : SD, chiL m = v ∧ chiR m = w :=
  Certificates.certificate5016.1

theorem nf_spec :
    ∀ a : SD, R0 ^ (nf a).1 * S0 ^ (nf a).2 = a :=
  Certificates.certificate5016.2.1

theorem rel :
    R0 ^ 8 = 1 ∧ R0 ^ 4 ≠ 1 ∧ S0 * S0 = 1 ∧ S0 ≠ 1 ∧ S0 * R0 * S0⁻¹ = R0 ^ 3 :=
  Certificates.certificate5016.2.2.1

theorem aut_apply
    (α : MulAut SD) (x : SD) : α x = ap (α R0) (α S0) x := by
  conv_lhs => rw [← nf_spec x]
  simp [ap, map_mul, map_pow]

theorem imgs_chi : ∀ a b : SD, Rel5 a b →
    (chiL a = chiL R0 ∧ chiR a = chiR R0 ∧ chiL b = chiL S0 ∧ chiR b = chiR S0) :=
  Certificates.certificate5016.2.2.2.1

@[expose] def Concl (w : SD) : Prop := chiL w = 1 ∧ chiR w = 1

instance instDecidableConcl
    (w : SD) : Decidable (Concl w) := inferInstanceAs (Decidable (_ ∧ _))

theorem fix_w : ∀ a b w : SD, Rel5 a b → Hyp3 a b w → Concl w :=
  Certificates.certificate5016.2.2.2.2.1

theorem rel5_aut (α : MulAut SD) : Rel5 (α R0) (α S0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := rel
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, h1, map_one]
  · intro h
    apply h2
    apply α.injective
    rw [map_pow, h, map_one]
  · rw [← map_mul, h3, map_one]
  · intro h
    apply h4
    apply α.injective
    rw [h, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, h5, map_pow]

theorem chi_aut
    (α : MulAut SD) (g : SD) : chiL (α g) = chiL g ∧ chiR (α g) = chiR g := by
  obtain ⟨hL1, hR1, hL2, hR2⟩ := imgs_chi _ _ (rel5_aut α)
  conv_lhs => rw [← nf_spec g]
  conv_rhs => rw [← nf_spec g]
  simp [map_mul, map_pow, hL1, hR1, hL2, hR2]

theorem chi_w (α : MulAut SD) (w : SD) (hfix : α w = w)
    (hsq : ∀ m : SD, α (α m) = w * m * w⁻¹) : chiL w = 1 ∧ chiR w = 1 := by
  refine fix_w (α R0) (α S0) w (rel5_aut α) ⟨?_, ?_, ?_⟩
  · rw [← aut_apply, hfix]
  · rw [← aut_apply, hsq]
  · rw [← aut_apply, hsq]

@[expose] def bitChar : Bool → Multiplicative (ZMod 2)
  | false => 1
  | true => Multiplicative.ofAdd 1

@[expose] def f3 (d : Ext2Data SD) (x : Ext2 SD d) :
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (bitChar x.bit, chiL x.base, chiR x.base)

theorem f3_mul
    (d : Ext2Data SD) (x y : Ext2 SD d) : f3 d (x * y) = f3 d x * f3 d y := by
  obtain ⟨hwL, hwR⟩ := chi_w d.α d.w d.fix d.sq
  obtain ⟨m₁, b₁⟩ := x
  obtain ⟨m₂, b₂⟩ := y
  cases b₁ <;> cases b₂
  · simp [f3, bitChar, map_mul]
  · simp [f3, bitChar, map_mul]
  · simp [f3, bitChar, map_mul, (chi_aut d.α m₂).1, (chi_aut d.α m₂).2]
  · simp only [f3, bitChar, Ext2.mk_mul_mk_tt, map_mul, (chi_aut d.α m₂).1, hwL, mul_one,
      (chi_aut d.α m₂).2, hwR, Prod.mk_mul_mk, Prod.mk.injEq, and_true]
    decide

@[expose] def f3Hom (d : Ext2Data SD) : Ext2 SD d →*
    Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) where
  toFun := f3 d
  map_one' := by simp [f3, bitChar]
  map_mul' := f3_mul d

theorem f3Hom_surjective
    (d : Ext2Data SD) : Function.Surjective (f3Hom d) := by
  rintro ⟨u, v, w⟩
  obtain ⟨m, hm1, hm2⟩ := chi_surj v w
  have hu : ∀ u : Multiplicative (ZMod 2), ∃ b : Bool, bitChar b = u := by decide
  obtain ⟨b, hb⟩ := hu u
  exact ⟨⟨m, b⟩, by simp [f3Hom, f3, hb, hm1, hm2]⟩

theorem rank_ext2_sd
    (d : Ext2Data SD) : 3 ≤ Group.rank (Ext2 SD d) := by
  have h1 := Group.rank_le_of_surjective (f3Hom d) (f3Hom_surjective d)
  have h2 : 2 ^ Group.rank (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2)) = 8 := by
    rw [two_pow_rank_eq_card_of_exponent_two]
    · simp
    · decide
  have h3 : Group.rank (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ×
      Multiplicative (ZMod 2)) = 3 := by
    have : (2 : ℕ) ^ Group.rank (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) ×
        Multiplicative (ZMod 2)) = 2 ^ 3 := by rw [h2]; norm_num
    exact Nat.pow_right_injective (le_refl 2) this
  omega

end CFSG.GH74.E2.OuterRank

namespace CFSG.GH74.E2

open Subgroup

theorem rank_ge_three_of_sd16_index_two
    {P : Type*} [Group P] [Finite P] (A : Subgroup P)
    (hA : A.index = 2) (eA : ↥A ≃* OuterRank.SD) : 3 ≤ Group.rank P := by
  obtain ⟨n, hn⟩ : ∃ n : P, n ∉ A := by
    by_contra h
    push Not at h
    have : A = ⊤ := eq_top_iff.2 fun x _ => h x
    rw [this, Subgroup.index_top] at hA
    omega
  obtain ⟨d0, e, -, -⟩ := exists_ext2_equiv A hA hn eA
  rw [Group.rank_congr e]
  exact OuterRank.rank_ext2_sd d0

end CFSG.GH74.E2

namespace CFSG.GH74.E2

open Subgroup

theorem rank_quot_ge_three
    {S : Type*} [Group S] [Finite S] (T TK : Subgroup S) [T.Normal]
    (hdisj : TK ⊓ T = ⊥) (eK : ↥TK ≃* OuterRank.SD) (hidx : (TK ⊔ T).index = 2) :
    3 ≤ Group.rank (S ⧸ T) := by
  let π : S →* S ⧸ T := QuotientGroup.mk' T
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective T
  have hinj : Function.Injective (π.comp TK.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxT : (x : S) ∈ T := by
      have := QuotientGroup.eq_one_iff (N := T) (x : S) |>.1 hx
      exact this
    have : (x : S) ∈ TK ⊓ T := ⟨x.2, hxT⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hA : (TK.map π).index = 2 := by
    have h1 : (TK.map π).comap π = TK ⊔ T := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← Subgroup.index_comap_of_surjective (f := π) _ hπ, h1, hidx]
  have hr : (π.comp TK.subtype).range = TK.map π := by
    ext y
    simp [MonoidHom.mem_range, Subgroup.mem_map]
  let eA : ↥(TK.map π) ≃* OuterRank.SD :=
    ((MulEquiv.subgroupCongr hr).symm.trans (MonoidHom.ofInjective hinj).symm).trans eK
  exact rank_ge_three_of_sd16_index_two (TK.map π) hA eA

end CFSG.GH74.E2

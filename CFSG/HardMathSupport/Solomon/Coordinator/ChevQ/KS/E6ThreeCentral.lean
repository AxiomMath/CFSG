module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open scoped Pointwise

@[expose] def IsThreeCentral (Q : Type) [Group Q] (z : Q) : Prop :=
  orderOf z = 3 ∧ ∃ S : Sylow 3 Q, (S : Subgroup Q) ≤ Subgroup.centralizer ({z} : Set Q)

def autFixedIn {Q : Type} [Group Q] (A : Subgroup (MulAut Q)) (Z : Subgroup Q) : Subgroup Q where
  carrier := {x | x ∈ Z ∧ ∀ g : A, g • x = x}
  one_mem' := ⟨Z.one_mem, fun g => smul_one g⟩
  mul_mem' := fun ⟨hx, hxA⟩ ⟨hy, hyA⟩ =>
    ⟨Z.mul_mem hx hy, fun g => by rw [smul_mul', hxA g, hyA g]⟩
  inv_mem' := fun ⟨hx, hxA⟩ => ⟨Z.inv_mem hx, fun g => by rw [smul_inv', hxA g]⟩

theorem mem_autFixedIn {Q : Type} [Group Q] (A : Subgroup (MulAut Q)) (Z : Subgroup Q) (x : Q) :
    x ∈ autFixedIn A Z ↔ x ∈ Z ∧ ∀ g : A, g • x = x :=
  Iff.rfl

theorem exists_fixed_sylow {Q : Type} [Group Q] [Finite Q] (A : Subgroup (MulAut Q))
    (hA : IsPGroup 3 A) : ∃ S : Sylow 3 Q, ∀ g : A, g • S = S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 Q) :=
    Finite.of_injective (fun S : Sylow 3 Q => ((S : Subgroup Q) : Set Q))
      (fun S T h => Sylow.ext (SetLike.coe_injective h))
  obtain ⟨S, hS⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 Q)
    (not_dvd_card_sylow 3 Q)
  exact ⟨S, MulAction.mem_fixedPoints.mp hS⟩

theorem smul_mem_centre_of_fixed {Q : Type} [Group Q] (A : Subgroup (MulAut Q))
    (S : Subgroup Q) (hS : ∀ g : A, g • S = S) (g : A) {x : Q} (hxS : x ∈ S)
    (hxC : x ∈ Subgroup.centralizer (S : Set Q)) :
    g • x ∈ S ∧ g • x ∈ Subgroup.centralizer (S : Set Q) := by
  have hgS : g • S = S := hS g
  refine ⟨?_, ?_⟩
  · have h1 : g • x ∈ g • S := Subgroup.smul_mem_pointwise_smul x g S hxS
    rwa [hgS] at h1
  · refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
    have hs' : s ∈ g • S := by rw [hgS]; exact hs
    obtain ⟨y, hyS, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists s g S).mp hs'
    have hyx : y * x = x * y := Subgroup.mem_centralizer_iff.mp hxC y hyS
    rw [← smul_mul', hyx, smul_mul']

theorem exists_fixed_order_three {Q : Type} [Group Q] [Finite Q] (A : Subgroup (MulAut Q))
    (hA : IsPGroup 3 A) (Z : Subgroup Q) (hinv : ∀ g : A, ∀ x ∈ Z, g • x ∈ Z)
    (hdvd : 3 ∣ Nat.card Z) : ∃ z ∈ Z, orderOf z = 3 ∧ ∀ g : A, g • z = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : MulAction A Z :=
    { smul := fun g x => ⟨g • x.1, hinv g x.1 x.2⟩
      one_smul := fun x => Subtype.ext (one_smul _ x.1)
      mul_smul := fun g h x => Subtype.ext (mul_smul g h x.1) }
  have hcount : Nat.card Z ≡ Nat.card (MulAction.fixedPoints A Z) [MOD 3] :=
    hA.card_modEq_card_fixedPoints Z
  have hfix3 : 3 ∣ Nat.card (MulAction.fixedPoints A Z) :=
    Nat.modEq_zero_iff_dvd.mp (hcount.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  have hFeq : Nat.card (autFixedIn A Z) = Nat.card (MulAction.fixedPoints A Z) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, ((mem_autFixedIn A Z x.1).mp x.2).1⟩,
          MulAction.mem_fixedPoints.mpr fun g =>
            Subtype.ext (((mem_autFixedIn A Z x.1).mp x.2).2 g)⟩
        invFun := fun y => ⟨y.1.1, (mem_autFixedIn A Z _).mpr
          ⟨y.1.2, fun g => congrArg Subtype.val (MulAction.mem_fixedPoints.mp y.2 g)⟩⟩
        left_inv := fun x => Subtype.ext rfl
        right_inv := fun y => Subtype.ext (Subtype.ext rfl) }
  have hF3 : 3 ∣ Nat.card (autFixedIn A Z) := by
    rw [hFeq]
    exact hfix3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hF3
  have hxF := (mem_autFixedIn A Z x.1).mp x.2
  exact ⟨x.1, hxF.1, (Subgroup.orderOf_coe x).trans hx, hxF.2⟩

theorem exists_fixed_threeCentral {Q : Type} [Group Q] [Finite Q] (A : Subgroup (MulAut Q))
    (hA : IsPGroup 3 A) (h3 : 3 ∣ Nat.card Q) :
    ∃ z : Q, IsThreeCentral Q z ∧ ∀ φ ∈ A, φ z = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := exists_fixed_sylow A hA
  have hS' : ∀ g : A, g • (S : Subgroup Q) = (S : Subgroup Q) := fun g =>
    congrArg (fun P : Sylow 3 Q => (P : Subgroup Q)) (hS g)
  have hSpg : IsPGroup 3 (S : Subgroup Q) := S.isPGroup'
  obtain ⟨Z, hZdef⟩ : ∃ Z : Subgroup Q,
      Z = (S : Subgroup Q) ⊓ Subgroup.centralizer ((S : Subgroup Q) : Set Q) := ⟨_, rfl⟩
  have hmemZ : ∀ x, x ∈ Z ↔ x ∈ (S : Subgroup Q) ∧
      x ∈ Subgroup.centralizer ((S : Subgroup Q) : Set Q) := fun x => by
    rw [hZdef, Subgroup.mem_inf]
  have hZpg : IsPGroup 3 Z := IsPGroup.to_le hSpg fun x hx => ((hmemZ x).mp hx).1
  have hinv : ∀ g : A, ∀ x ∈ Z, g • x ∈ Z := by
    intro g x hx
    obtain ⟨hxS, hxC⟩ := (hmemZ x).mp hx
    exact (hmemZ (g • x)).mpr (smul_mem_centre_of_fixed A (S : Subgroup Q) hS' g hxS hxC)
  have hQ : (Nat.card Q : ℕ) ≠ 0 := (Nat.card_pos : 0 < Nat.card Q).ne'
  have hk : 0 < (Nat.card Q).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hQ h3
  have hSc : Nat.card (S : Subgroup Q) = 3 ^ (Nat.card Q).factorization 3 :=
    Sylow.card_eq_multiplicity S
  haveI : Nontrivial ↥(S : Subgroup Q) :=
    (IsPGroup.nontrivial_iff_card hSpg).mpr ⟨_, hk, hSc⟩
  haveI : Nontrivial ↥(Subgroup.center (S : Subgroup Q)) := IsPGroup.center_nontrivial hSpg
  obtain ⟨c, hc⟩ := exists_ne (1 : ↥(Subgroup.center (S : Subgroup Q)))
  have hc1 : (c : ↥(S : Subgroup Q)) ≠ 1 := fun h => hc (Subtype.ext h)
  have hx0ne : ((c : ↥(S : Subgroup Q)) : Q) ≠ 1 := fun h => hc1 (Subtype.ext h)
  have hx0C : ((c : ↥(S : Subgroup Q)) : Q) ∈ Subgroup.centralizer ((S : Subgroup Q) : Set Q) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  have hx0Z : ((c : ↥(S : Subgroup Q)) : Q) ∈ Z :=
    (hmemZ _).mpr ⟨(c : ↥(S : Subgroup Q)).2, hx0C⟩
  haveI : Nontrivial ↥Z := ⟨⟨⟨_, hx0Z⟩, 1, fun h => hx0ne (congrArg Subtype.val h)⟩⟩
  obtain ⟨n, hn, hZc⟩ := (IsPGroup.nontrivial_iff_card hZpg).mp inferInstance
  have hZdvd : 3 ∣ Nat.card Z := by
    rw [hZc]
    exact dvd_pow_self 3 hn.ne'
  obtain ⟨z, hzZ, hord, hfix⟩ := exists_fixed_order_three A hA Z hinv hZdvd
  have hzC : z ∈ Subgroup.centralizer ((S : Subgroup Q) : Set Q) := ((hmemZ z).mp hzZ).2
  refine ⟨z, ⟨hord, S, ?_⟩, fun φ hφ => hfix ⟨φ, hφ⟩⟩
  intro s hs
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  rw [Set.mem_singleton_iff.mp hh]
  exact (Subgroup.mem_centralizer_iff.mp hzC s hs).symm

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end

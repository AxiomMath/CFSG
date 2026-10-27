module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ComponentInitial.BlockSylowOrder
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped Pointwise

variable {K : Type*} [Group K]

theorem isElementaryAbelian_of_le {p : ℕ} {A B : Subgroup K} (hA : CFSG.IsElementaryAbelian p A)
    (hBA : B ≤ A) : CFSG.IsElementaryAbelian p B := CFSG.IsElementaryAbelian.of_le hA hBA

theorem mulAut_smul_eq_map (α : MulAut K) (H : Subgroup K) : α • H = H.map α.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  rfl

theorem exists_sylow_two_smul_eq [Finite K] (α : MulAut K) (hα : α * α = 1) :
    ∃ S : Sylow 2 K, α • S = S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (Sylow 2 K) := Fintype.ofFinite _
  let f : Function.End (Sylow 2 K) := fun S => α • S
  have hf : f ^ 2 ^ 1 = 1 := by
    funext S
    show α • α • S = S
    rw [smul_smul, hα, one_smul]
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have h1 := card_sylow_modEq_one 2 K
  rw [Nat.card_eq_fintype_card] at h1
  by_contra hne
  push Not at hne
  have hempty : Fintype.card (Function.fixedPoints f) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun S => hne S.1 S.2⟩
  rw [hempty] at h
  have h2 := h.symm.trans h1
  exact absurd h2 (by decide)

theorem map_conjSub_characteristic_eq {S : Subgroup K} {A : Subgroup S} [hA : A.Characteristic]
    (g : K) {σ : MulAut K} (hσ : (conjSub g S).map σ.toMonoidHom = conjSub g S) :
    (conjSub g (A.map S.subtype)).map σ.toMonoidHom = conjSub g (A.map S.subtype) := by
  set τ : MulAut K := (MulAut.conj g)⁻¹ * σ * MulAut.conj g with hτdef
  have hcomp : ∀ X : Subgroup K, (conjSub g X).map σ.toMonoidHom = conjSub g (X.map τ.toMonoidHom) :=
    fun X => by
      rw [conjSub, conjSub, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext x
      simp [hτdef]
      group
  have hτ : S.map τ.toMonoidHom = S := by
    have h1 := hcomp S
    rw [hσ] at h1
    have h2 := congrArg (conjSub g⁻¹) h1
    rw [conjSub_inv_conjSub, conjSub_inv_conjSub] at h2
    exact h2.symm
  have hchar := (Subgroup.characteristic_iff_map_eq.1 hA) (restrictAut τ S hτ)
  have h1 : (A.map S.subtype).map τ.toMonoidHom = A.map S.subtype := by
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨restrictAut τ S hτ a, ?_, rfl⟩
      rw [← hchar]
      exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      rw [← hchar] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      exact ⟨b, ⟨b, hb, rfl⟩, rfl⟩
  rw [hcomp, h1]

theorem card_le_sq_card_fixed [Finite K] {A : Subgroup K} (hA : CFSG.IsElementaryAbelian 2 A)
    {σ : MulAut K} (hσA : A.map σ.toMonoidHom = A) (hσ : σ * σ = 1) :
    Nat.card A ≤ Nat.card ↥(A ⊓ fixedSubgroup σ) ^ 2 := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hσmem : ∀ x ∈ A, σ x ∈ A := fun x hx => hσA ▸ ⟨x, hx, rfl⟩
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    rw [← MulAut.mul_apply, hσ, MulAut.one_apply]
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx
  let φ : A →* A :=
    { toFun := fun x => ⟨x * σ x, mul_mem x.2 (hσmem x x.2)⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul, map_mul]
        calc (x : K) * y * (σ x * σ y) = x * (y * σ x) * σ y := by group
          _ = x * (σ x * y) * σ y := by rw [hcomm _ y.2 _ (hσmem x x.2)]
          _ = x * σ x * (y * σ y) := by group }
  have hker : φ.ker.map A.subtype = A ⊓ fixedSubgroup σ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h1 : (y : K) * σ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
      refine mem_inf.2 ⟨y.2, ?_⟩
      change σ y = y
      calc σ (y : K) = (y : K) * ((y : K) * σ y) := by rw [← mul_assoc, hsq _ y.2, one_mul]
        _ = y := by rw [h1, mul_one]
    · intro hx
      obtain ⟨hxA, hxσ⟩ := mem_inf.1 hx
      refine ⟨⟨x, hxA⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_), rfl⟩
      change x * σ x = 1
      rw [show σ x = x from hxσ, hsq x hxA]
  have hrange : φ.range.map A.subtype ≤ A ⊓ fixedSubgroup σ := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    refine mem_inf.2 ⟨mul_mem y.2 (hσmem y y.2), ?_⟩
    change σ ((y : K) * σ y) = (y : K) * σ y
    rw [map_mul, hσσ, hcomm _ (hσmem y y.2) _ y.2]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have hk : Nat.card φ.ker = Nat.card ↥(A ⊓ fixedSubgroup σ) := by
    rw [← hker]
    exact (Subgroup.card_map_of_injective (f := A.subtype) A.subtype_injective).symm
  have hr : Nat.card φ.range ≤ Nat.card ↥(A ⊓ fixedSubgroup σ) := by
    rw [Nat.card_congr (φ.range.equivMapOfInjective A.subtype A.subtype_injective).toEquiv]
    exact Subgroup.card_le_of_le hrange
  rw [h1, hk, sq]
  exact Nat.mul_le_mul_right _ hr

theorem characteristic_Sylow_eight_subgroup_fixed_four_group [Finite K] (S : Sylow 2 K)
    {A : Subgroup (S : Subgroup K)} [A.Characteristic] (hAel : CFSG.IsElementaryAbelian 2 A)
    (hA8 : 8 ≤ Nat.card A) (α : MulAut K) (hα : α * α = 1) :
    (∃ V : Subgroup K, V ≤ fixedSubgroup α ∧ CFSG.IsElementaryAbelian 2 V ∧ Nat.card V = 4) ∧
      2 ≤ CFSG.pRank 2 (fixedSubgroup α) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S₁, hS₁⟩ := exists_sylow_two_smul_eq α hα
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq K S S₁
  have hS₁G : ((g • S : Sylow 2 K) : Subgroup K) = conjSub g (S : Subgroup K) := by
    rw [Sylow.coe_subgroup_smul, conjSub_eq_mulAut_smul]
  have hσ : (conjSub g (S : Subgroup K)).map α.toMonoidHom = conjSub g (S : Subgroup K) := by
    rw [← hS₁G]
    have h1 := congrArg (fun T : Sylow 2 K => (T : Subgroup K)) hS₁
    simp only [Sylow.pointwise_smul_def] at h1
    rw [← mulAut_smul_eq_map]
    exact h1
  set A₁ := conjSub g ((A : Subgroup (S : Subgroup K)).map (S : Subgroup K).subtype) with hA₁def
  have hA₁α : A₁.map α.toMonoidHom = A₁ := map_conjSub_characteristic_eq g hσ
  have hAG : CFSG.IsElementaryAbelian 2 A₁ := by
    have := hAel
    have : CFSG.IsElementaryAbelian 2 ((A : Subgroup (S : Subgroup K)).map
        (S : Subgroup K).subtype) := CFSG.IsElementaryAbelian.map_subtype
    exact CFSG.IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hA₁card : Nat.card A₁ = Nat.card A := by
    rw [hA₁def, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (S : Subgroup K).subtype_injective]
  set F := A₁ ⊓ fixedSubgroup α with hFdef
  have hF := card_le_sq_card_fixed hAG hA₁α hα
  rw [hA₁card] at hF
  have hF2 : IsPGroup 2 F := (CFSG.IsElementaryAbelian.isPGroup 2 A₁ |>.to_le inf_le_left)
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 hF2
  have he2 : 2 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e <;> simp_all <;> omega
  have h4 : 2 ^ 2 ∣ Nat.card F := by rw [he]; exact Nat.pow_dvd_pow 2 he2
  obtain ⟨V', hV'⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  set V := V'.map F.subtype with hVdef
  have hVF : V ≤ F := Subgroup.map_subtype_le _
  have hVcard : Nat.card V = 4 := by
    rw [hVdef, Subgroup.card_map_of_injective F.subtype_injective, hV']
    norm_num
  have hVel : CFSG.IsElementaryAbelian 2 V := isElementaryAbelian_of_le hAG (hVF.trans inf_le_left)
  have hVfix : V ≤ fixedSubgroup α := hVF.trans inf_le_right
  refine ⟨⟨V, hVfix, hVel, hVcard⟩, ?_⟩
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  have hpow : ∀ v : V, v ^ 2 = 1 := fun v =>
    Subtype.ext (by
      simpa using CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V) (v : K) v.2)
  exact CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun u v => mul_comm' u v) hpow
    (by rw [hVcard]; norm_num) (Subgroup.inclusion hVfix) (Subgroup.inclusion_injective hVfix)
    le_top

end CFSG.LocalAnalysis.ComponentInitial

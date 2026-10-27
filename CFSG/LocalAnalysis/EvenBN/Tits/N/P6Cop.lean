module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.StarBasic
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Comm

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open

theorem exists_mul_fixed {M : Type*} [CommGroup M] (hexp : ∀ m : M, m * m = 1)
    {A : Subgroup (MulAut M)} [Fintype A] (hodd : Odd (Fintype.card A)) {Z' : Subgroup M}
    (htriv : ∀ a ∈ A, ∀ m : M, a m * m⁻¹ ∈ Z') (m : M) :
    ∃ z ∈ Z', ∃ u : M, (∀ a ∈ A, a u = u) ∧ m = z * u := by
  classical
  set u : M := ∏ b : A, (b : MulAut M) m with hu
  set p : M := ∏ b : A, ((b : MulAut M) m * m⁻¹) with hp
  have hpZ : p ∈ Z' := Subgroup.prod_mem Z' fun b _ => htriv b b.2 m
  have hfix : ∀ a ∈ A, a u = u := by
    intro a ha
    rw [hu, map_prod]
    refine Fintype.prod_equiv (Equiv.mulLeft (⟨a, ha⟩ : A)) _ _ fun b => ?_
    rfl
  have hup : u = p * m := by
    obtain ⟨k, hk⟩ := hodd
    have h1 : u = ∏ b : A, (((b : MulAut M) m * m⁻¹) * m) := by
      rw [hu]
      exact Finset.prod_congr rfl fun b _ => by group
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hk, hp]
    have : m ^ (2 * k + 1) = m := by
      rw [pow_succ, pow_mul, sq, hexp, one_pow, one_mul]
    rw [this]
  refine ⟨p⁻¹, inv_mem hpZ, u, hfix, ?_⟩
  rw [hup]
  group

open scoped IsMulCommutative in
open scoped commutatorElement in
theorem false_of_odd_action {G : Type*} [Group G] [Finite G] {V Z W : Subgroup G}
    {Ot : Subgroup (MulAut ↥V)} (hV : IsElemAbelian 2 V) (hZV : Z ≤ V)
    (hWH : W ≤ normalizer (V : Set G)) (hOodd : Odd (Nat.card Ot))
    (hOn : ∀ h ∈ normalizer (V : Set G), ∀ a ∈ Ot, actFun V h * a * (actFun V h)⁻¹ ∈ Ot)
    (hOtriv : ∀ a ∈ Ot, ∀ v : ↥V, ((a v : ↥V) : G) * (v : G)⁻¹ ∈ Z)
    (hWZ : ∀ w ∈ W, ∀ z ∈ Z, w * z = z * w) (hVW : ⁅V, W⁆ = Z)
    (hnt : ∃ a ∈ Ot, ∃ v : ↥V, (v : G) ∈ Z ∧ a v ≠ v) : False := by
  haveI : IsMulCommutative ↥V := hV.1
  classical
  haveI : Fintype Ot := Fintype.ofFinite _
  have hexp : ∀ m : ↥V, m * m = 1 := fun m => Subtype.ext (by simpa [sq] using hV.2 m m.2)
  have hodd' : Odd (Fintype.card Ot) := by rwa [← Nat.card_eq_fintype_card]
  set Z' : Subgroup ↥V := Z.subgroupOf V with hZ'
  have htriv : ∀ a ∈ Ot, ∀ m : ↥V, a m * m⁻¹ ∈ Z' := fun a ha m => hOtriv a ha m
  let U : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ V, ∀ a ∈ Ot, a ⟨g, hg⟩ = ⟨g, hg⟩}
      mul_mem' := by
        rintro g₁ g₂ ⟨h1, f1⟩ ⟨h2, f2⟩
        refine ⟨mul_mem h1 h2, fun a ha => ?_⟩
        have e : (⟨g₁ * g₂, mul_mem h1 h2⟩ : ↥V) = ⟨g₁, h1⟩ * ⟨g₂, h2⟩ := rfl
        rw [e, map_mul, f1 a ha, f2 a ha]
      one_mem' := by
        refine ⟨V.one_mem, fun a _ => ?_⟩
        have e : (⟨1, V.one_mem⟩ : ↥V) = 1 := rfl
        rw [e, map_one]
      inv_mem' := by
        rintro g ⟨hg, f⟩
        refine ⟨inv_mem hg, fun a ha => ?_⟩
        have e : (⟨g⁻¹, inv_mem hg⟩ : ↥V) = (⟨g, hg⟩ : ↥V)⁻¹ := rfl
        rw [e, map_inv, f a ha] }
  have hUinv : ∀ h ∈ normalizer (V : Set G), ∀ g ∈ U, h * g * h⁻¹ ∈ U := by
    rintro h hh g ⟨hg, hf⟩
    have hhV : h * g * h⁻¹ ∈ V := (mem_normalizer_iff.1 hh g).1 hg
    refine ⟨hhV, fun a ha => ?_⟩
    have hconj : actFun V h⁻¹ * a * (actFun V h⁻¹)⁻¹ ∈ Ot := hOn h⁻¹ (inv_mem hh) a ha
    rw [actFun_inv V hh, inv_inv] at hconj
    have hx : actFun V h ⟨g, hg⟩ = ⟨h * g * h⁻¹, hhV⟩ :=
      Subtype.ext (actFun_apply_coe V hh ⟨g, hg⟩)
    rw [← hx]
    have h1 := hf _ hconj
    have h2 : actFun V h (((actFun V h)⁻¹ * a * actFun V h) ⟨g, hg⟩) = actFun V h ⟨g, hg⟩ := by
      rw [h1]
    rwa [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self] at h2
  have hcomm : ⁅V, W⁆ ≤ U := by
    refine Subgroup.commutator_le.2 fun v hv w hw => ?_
    obtain ⟨z', hz', u, hu, hvu⟩ := exists_mul_fixed (A := Ot) hexp hodd' htriv ⟨v, hv⟩
    have hz : (z' : G) ∈ Z := hz'
    have huU : (u : G) ∈ U := ⟨u.2, hu⟩
    have hv_eq : v = (z' : G) * (u : G) := congrArg Subtype.val hvu
    have hwN := hWH hw
    have hq : w * (u : G)⁻¹ * w⁻¹ ∈ U := hUinv w hwN _ (inv_mem huU)
    have hqV : w * (u : G)⁻¹ * w⁻¹ ∈ V := hq.1
    have hzw : w * (z' : G) = (z' : G) * w := hWZ w hw _ hz
    have hzu : (z' : G) * (u : G) = (u : G) * (z' : G) :=
      mul_comm_of_isElemAbelian hV (hZV hz) u.2
    have hzq : (z' : G) * (w * (u : G)⁻¹ * w⁻¹) = (w * (u : G)⁻¹ * w⁻¹) * (z' : G) :=
      mul_comm_of_isElemAbelian hV (hZV hz) hqV
    have hwz' : w * (z' : G)⁻¹ * w⁻¹ = (z' : G)⁻¹ := by
      calc w * (z' : G)⁻¹ * w⁻¹ = (w * (z' : G) * w⁻¹)⁻¹ := by group
        _ = (z' : G)⁻¹ := by rw [hzw]; group
    have key : ⁅v, w⁆ = (u : G) * (w * (u : G)⁻¹ * w⁻¹) := by
      rw [hv_eq, commutatorElement_def]
      calc (z' : G) * u * w * ((z' : G) * u)⁻¹ * w⁻¹
          = (z' : G) * u * (w * (u : G)⁻¹ * w⁻¹) * (w * (z' : G)⁻¹ * w⁻¹) := by group
        _ = (z' : G) * (u * (w * (u : G)⁻¹ * w⁻¹)) * (z' : G)⁻¹ := by rw [hwz']; group
        _ = (u * (w * (u : G)⁻¹ * w⁻¹)) * (z' : G) * (z' : G)⁻¹ := by
            rw [← mul_assoc (z' : G) u, hzu, mul_assoc (u : G) (z' : G), hzq, ← mul_assoc]
        _ = (u : G) * (w * (u : G)⁻¹ * w⁻¹) := by group
    rw [key]
    exact mul_mem huU hq
  obtain ⟨a, ha, v, hvZ, hav⟩ := hnt
  have hvU : (v : G) ∈ U := hcomm (hVW ▸ hvZ)
  obtain ⟨hvV, hfix⟩ := hvU
  exact hav (hfix a ha)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6

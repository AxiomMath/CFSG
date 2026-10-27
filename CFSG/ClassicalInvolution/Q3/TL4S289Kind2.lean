module

public import CFSG.ClassicalInvolution.Q3.TL4S289Kind
public import CFSG.ClassicalInvolution.Q3.TL4VtxAut
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Model

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.Blueprint

namespace S289

variable {X : Type} [Group X]

theorem exists_mul_center_of_simple_quot [Finite X] (hS : IsSimpleGroup (X ⧸ Subgroup.center X))
    {C : Subgroup X} (hC : IsComponent C) (g : X) : ∃ c ∈ C, c⁻¹ * g ∈ Subgroup.center X := by
  rcases (hC.2.map (QuotientGroup.mk'_surjective
    (Subgroup.center X))).eq_bot_or_top_of_isSimpleGroup hS with h | h
  · exfalso
    apply not_le_of_comm hC (fun x _ y hy => Subgroup.mem_center_iff.mp hy x)
    intro c hc
    have h1 : QuotientGroup.mk' (Subgroup.center X) c ∈ C.map (QuotientGroup.mk' _) := ⟨c, hc, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · have h1 : QuotientGroup.mk' (Subgroup.center X) g ∈ C.map (QuotientGroup.mk' _) :=
      h ▸ Subgroup.mem_top _
    obtain ⟨c, hc, hcg⟩ := h1
    exact ⟨c, hc, QuotientGroup.eq.mp hcg⟩

theorem sp6_autOddFree [Finite X] (hS : LieModel (X ⧸ Subgroup.center X) .PSp 3 2 1)
    {C : Subgroup X} (hC : IsComponent C) : Q3NM.AutOddFree ↥C := by
  have hsimp : IsSimpleGroup (X ⧸ Subgroup.center X) := Vtx.isSimpleGroup_of_exLie (Or.inl hS)
  set θ : ↥C →* X ⧸ Subgroup.center X := (QuotientGroup.mk' (Subgroup.center X)).comp C.subtype
    with hθdef
  have hθ : Function.Surjective θ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
    obtain ⟨c, hc, hcg⟩ := exists_mul_center_of_simple_quot hsimp hC g
    exact ⟨⟨c, hc⟩, QuotientGroup.eq.mpr hcg⟩
  have hker : θ.ker = Subgroup.center ↥C := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : (x : X) ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hx
      rw [Subgroup.mem_center_iff] at h1 ⊢
      exact fun y => Subtype.ext (h1 y)
    · intro hx
      refine (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_center_iff.mpr fun g => ?_)
      obtain ⟨c, hc, hcg⟩ := exists_mul_center_of_simple_quot hsimp hC g
      have hxc : c * x = x * c := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hx) ⟨c, hc⟩)
      have hz := Subgroup.mem_center_iff.mp hcg
      calc g * x = c * (c⁻¹ * g) * x := by group
        _ = c * x * (c⁻¹ * g) := by rw [mul_assoc, ← hz x, mul_assoc]
        _ = x * c * (c⁻¹ * g) := by rw [hxc]
        _ = x * g := by group
  have e : ↥C ⧸ Subgroup.center ↥C ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  have hEx : PhilipHall.QuaternionBridge.ExLie (↥C ⧸ Subgroup.center ↥C) :=
    Or.inl (LieType.CurtisTits.lieModel_of_mulEquiv e.symm hS)
  exact Vtx.autOddFree_of_quot_center hC.1.1 (Vtx.autOddFree_of_exLie hEx)

theorem sq_mem_of_index_dvd_six [Finite X] {N : Subgroup X} [N.Normal] (hidx : N.index ∣ 6)
    {σ : X} (hσ : σ ^ 4 = 1) : σ * σ ∈ N := by
  have h1 : orderOf (σ : X ⧸ N) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one])
  have h2 : orderOf (σ : X ⧸ N) ∣ 6 :=
    (orderOf_dvd_natCard _).trans (by rw [← Subgroup.index_eq_card]; exact hidx)
  have h3 : orderOf (σ : X ⧸ N) ∣ Nat.gcd 4 6 := Nat.dvd_gcd h1 h2
  rw [show Nat.gcd 4 6 = 2 by norm_num] at h3
  have h4 : (σ : X ⧸ N) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h3
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two] at h4
  exact h4

theorem exists_sq_eq_of_typeRFam [Finite X] {Φ : Set (Subgroup X)} (h : TypeRFam 3 Φ)
    {L : Subgroup X} (hL : L ∈ Φ) {a : X} (ha : IsUniqueInvolution L a) :
    ∃ σ ∈ L, σ ^ 4 = 1 ∧ σ * σ = a := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  have hP := isSylow2In_map_subtype L P
  obtain ⟨e⟩ := h.quat L hL _ hP
  set σ : X := ((e.symm (QuaternionGroup.a 1) : ↥((P : Subgroup ↥L).map L.subtype)) : X)
    with hσdef
  have hσL : σ ∈ L := hP.1 (e.symm _).2
  have hσ4 : σ ^ 4 = 1 := by
    have h1 : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (3 - 2))) ^ 4 = 1 := by decide
    have h2 := congrArg (fun q => ((e.symm q : ↥((P : Subgroup ↥L).map L.subtype)) : X)) h1
    simpa only [map_pow, map_one, Subgroup.coe_pow, OneMemClass.coe_one] using h2
  refine ⟨σ, hσL, hσ4, ?_⟩
  have hsq : σ * σ * (σ * σ) = 1 := by
    calc σ * σ * (σ * σ) = σ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := hσ4
  rcases ha.unique (σ * σ) (L.mul_mem hσL hσL) hsq with h1 | h1
  · exfalso
    have h2 : (QuaternionGroup.a 1 : QuaternionGroup (2 ^ (3 - 2))) *
        QuaternionGroup.a 1 = 1 := by
      apply e.symm.injective
      apply Subtype.ext
      simpa only [map_mul, map_one, Subgroup.coe_mul, OneMemClass.coe_one] using h1
    exact absurd h2 (by decide)
  · exact h1

end S289

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Layer
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Shape
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2Stmt
public import CFSG.GH74.Orders.Sporadic
public import CFSG.GH74.Orders.LieType

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.LocalCores CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.E2 CFSG.GH74.GLS.Stage1.Thm6.Sec13
open scoped commutatorElement

namespace CFSG.GH74.GLS.C3.Layer1.Bk.B810

theorem factorization_two_pow_mul_odd {m : ℕ} (hm : Odd m) (k : ℕ) :
    (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have h2 : m.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    have := Nat.odd_iff.1 hm
    omega)
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, h2]
  simp

theorem card_of_shape_M12 {K : Type} [Group K] [Finite K]
    (h : Shape2M12 K) : Nat.card K = 2 ^ 7 * 1485 := by
  obtain ⟨-, hZ, hM⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K), hZ,
    CFSG.GH74.card_of_isSporadic_M12 hM]
  norm_num

theorem card_of_shape_Sz8 {K : Type} [Group K] [Finite K]
    (h : Shape2Sz8 K) : Nat.card K = 2 ^ 7 * 455 := by
  obtain ⟨-, hZ, hS⟩ := h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K), hZ,
    CFSG.GH74.card_of_lieModel_twistedB2 hS]
  decide

theorem false_of_two_M12
    {X : Type} [Group X] [Finite X] {z : X} (hz2 : orderOf z = 2)
    (hzc : z ∈ center X) {S V K : Subgroup X} (hSK : S ≤ K) (hVS : V ≤ S) (hzV : z ∈ V)
    (hVcard : Nat.card V = 32) (hVcomm : ∀ x ∈ V, x * x ∈ zpowers z ∧ ∀ y ∈ V, ⁅x, y⁆ ∈ zpowers z)
    (hK : Shape2M12 ↥K) : False := by
  obtain ⟨-, hZcard, hM⟩ := hK
  have hVK : V ≤ K := hVS.trans hSK
  have hzK : z ∈ K := hVK hzV
  have hzKc : (⟨z, hzK⟩ : ↥K) ∈ center ↥K :=
    Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_center_iff.1 hzc g)
  have hZ : ∀ t ∈ zpowers z, ∀ ht : t ∈ K, (⟨t, ht⟩ : ↥K) ∈ center ↥K := fun t htz ht =>
    Subgroup.mem_center_iff.2 fun g => Subtype.ext
      (Subgroup.mem_center_iff.1 (Subgroup.zpowers_le.2 hzc htz) g)
  let f : ↥K →* ↥K ⧸ center ↥K := QuotientGroup.mk' (center ↥K)
  let V₁ : Subgroup ↥K := V.subgroupOf K
  let A : Subgroup (↥K ⧸ center ↥K) := V₁.map f
  have hA : IsElemAb2 A := by
    rintro _ ⟨v, hv, rfl⟩
    have hvV : (v : X) ∈ V := hv
    refine ⟨?_, ?_⟩
    · rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).2
        (hZ ((v : X) * v) (hVcomm _ hvV).1 (K.mul_mem v.2 v.2))
    · rintro _ ⟨w, hw, rfl⟩
      have hwV : (w : X) ∈ V := hw
      set c : ↥K := v * w * v⁻¹ * w⁻¹ with hcdef
      have hc : (c : X) = ⁅(v : X), (w : X)⁆ := by simp [hcdef, commutatorElement_def]
      have hcZ : c ∈ center ↥K :=
        hZ (c : X) (by rw [hc]; exact (hVcomm _ hvV).2 _ hwV) c.2
      have hfc : f c = 1 := (QuotientGroup.eq_one_iff c).2 hcZ
      have hvw : v * w = c * (w * v) := by simp only [hcdef]; group
      show f v * f w = f w * f v
      rw [← map_mul, ← map_mul, hvw, map_mul, hfc, one_mul]
  have hzK2 : orderOf (⟨z, hzK⟩ : ↥K) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz2
  have hZeq : zpowers (⟨z, hzK⟩ : ↥K) = center ↥K :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzKc)
      (by rw [Nat.card_zpowers, hzK2, hZcard])
  have hZV : center ↥K ≤ V₁ := by
    rw [← hZeq]
    exact Subgroup.zpowers_le.2 (show (⟨z, hzK⟩ : ↥K) ∈ V₁ from hzV)
  let g : ↥V₁ →* ↥K ⧸ center ↥K := f.comp V₁.subtype
  have hrange : g.range = A := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (center ↥K).subgroupOf V₁ := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show f (v : ↥K) = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hkercard : Nat.card g.ker = 2 := by
    rw [hker]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv).trans hZcard
  have hV1card : Nat.card ↥V₁ = 32 := by
    rw [← hVcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range g
  rw [hkercard, hrange, hV1card] at hmul
  have hAcard : Nat.card ↥A = 16 := by omega
  have := Bk.M12.m12_rank_le_three hM A hA
  omega

theorem false_of_two_Sz8 {X : Type} [Group X] [Finite X] {S K P : Subgroup X}
    (hS : IsSylowOf 2 S ⊤) (hScard : Nat.card S = 2 ^ 7) (hKn : K.Normal)
    (hKcard : Nat.card K = 2 ^ 7 * 455) (hPperf : ⁅P, P⁆ = P) (hP3 : 3 ∣ Nat.card P) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXfact : (Nat.card X).factorization 2 = 7 := by
    have h := hS.card_eq
    rw [hScard, Subgroup.card_top] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  have hmul := Subgroup.card_mul_index K
  rw [hKcard] at hmul
  have hodd : ¬ 2 ∣ K.index := by
    intro h2
    obtain ⟨j, hj⟩ := h2
    have h8 : 2 ^ 8 ∣ Nat.card X := by
      rw [← hmul, hj]
      exact ⟨455 * j, by ring⟩
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h8
    omega
  have hodd' : Odd (Nat.card (X ⧸ K)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.2 (by omega)
  have hsolv : Group.IsSolvable (X ⧸ K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
  have hPK : P ≤ K := perfect_le_of_solvable_quotient K hsolv hPperf
  have := dvd_trans hP3 (Subgroup.card_dvd_of_le hPK)
  rw [hKcard] at this
  omega

theorem b_p810_J2_proved
    (hG : GenericKnownFacts) (hF : E2ComponentFacts) : B_p810_J2 := by
  intro X _ _ hgen hcomp z hz2 hzc hpc hpp S hS hScard hScent V hVS hzV hVcard hVcomm P hPperf hP3
  obtain ⟨K₀, hK₀, hcen₀⟩ := exists_component_center_ne_bot hz2 hzc hpc hpp hS hScent hP3
  have hshape₀ := shape_of_center_ne_bot hG hF hgen (hcomp K₀ hK₀) hcen₀
  have hfact : (Nat.card K₀).factorization 2 = 7 := by
    rcases hshape₀ with h | h
    · rw [card_of_shape_M12 h]
      exact factorization_two_pow_mul_odd (by decide) 7
    · rw [card_of_shape_Sz8 h]
      exact factorization_two_pow_mul_odd (by decide) 7
  obtain ⟨g, hg⟩ := exists_conj_sylow_le hS hScard hfact
  have hK : IsComponent (K₀.map (MulAut.conj g).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj g) hK₀
  have e : ↥K₀ ≃* ↥(K₀.map (MulAut.conj g).toMonoidHom) :=
    K₀.equivMapOfInjective _ (MulAut.conj g).injective
  have hshape : Shape2M12 ↥(K₀.map (MulAut.conj g).toMonoidHom) ∨
      Shape2Sz8 ↥(K₀.map (MulAut.conj g).toMonoidHom) :=
    hshape₀.imp (Shape2M12.of_mulEquiv e) (Shape2Sz8.of_mulEquiv e)
  rcases hshape with hM | hSz
  · exact false_of_two_M12 hz2 hzc hg hVS hzV hVcard hVcomm hM
  · have hKcard := card_of_shape_Sz8 hSz
    have hKn : (K₀.map (MulAut.conj g).toMonoidHom).Normal := by
      refine ⟨fun n hn x => ?_⟩
      have hx : IsComponent ((K₀.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom) :=
        isComponent_map_mulEquiv (MulAut.conj x) hK
      have hxK := eq_of_isComponent_of_sylow_le hz2 hS hScent hK hg hx
      rw [← hxK]
      exact Subgroup.mem_map.2 ⟨n, hn, by simp [MulAut.conj_apply]⟩
    exact false_of_two_Sz8 hS hScard hKn hKcard hPperf hP3

end CFSG.GH74.GLS.C3.Layer1.Bk.B810

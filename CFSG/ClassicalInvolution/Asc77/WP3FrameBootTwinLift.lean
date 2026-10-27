module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameBootTwinCtx
import CFSG.ClassicalInvolution.RouteD.TwinYElement
import CFSG.ClassicalInvolution.Asc77.AscE187Img
import CFSG.ClassicalInvolution.Asc77.ModOApi
import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
import CFSG.ClassicalInvolution.Balance.GoodDataBasic
import CFSG.ClassicalInvolution.Balance.WeakFrameExistsBasic
import CFSG.ClassicalInvolution.Asc77.AscE187Basic
import CFSG.ClassicalInvolution.Asc77.AscE187Cop
import CFSG.ClassicalInvolution.Asc77.AscThmABasic
import CFSG.ClassicalInvolution.Balance.WeakFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)
open CFSG.ClassicalInvolution.RouteD.TwinY
open scoped commutatorElement MatrixGroups

local notation "LTag" => CFSG.Assembly.LowTwoRank.StatedLieTag

section Elements

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_order_four {N : Subgroup G} {w : G} (hN : IsClassicalMember p f N w)
    (hodd : Odd (Nat.card (GaloisField p f))) :
    ∃ a ∈ N, a * a * w⁻¹ ∈ oddCoreIn N ∧ ∃ k ∈ N, a * k * a⁻¹ * k⁻¹ ∉ oddCoreIn N := by
  obtain ⟨e⟩ := hN.nonempty_equiv
  set B₀ : SL(2, GaloisField p f) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hB₀
  have hWB : slW (GaloisField p f) * B₀ ≠ B₀ * slW (GaloisField p f) := by
    intro h
    have := congrArg (fun x : SL(2, GaloisField p f) =>
      (x : Matrix (Fin 2) (Fin 2) (GaloisField p f)) 0 0) h
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
    simp [slW, hB₀, Matrix.mul_apply, Fin.sum_univ_two] at this
  have hw2 : w * w = 1 := (isCentralInvolution_of_isClassicalMember hN).sq
  set wq : ↥N ⧸ classicalInvolutionOddCore ↥N := QuotientGroup.mk ⟨w, hN.mem⟩ with hwq
  have hord : orderOf wq = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hwq, ← QuotientGroup.mk_pow]
      have : (⟨w, hN.mem⟩ : ↥N) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hw2)
      rw [this]
      rfl
    · intro h1
      have hO : (⟨w, hN.mem⟩ : ↥N) ∈ classicalInvolutionOddCore ↥N :=
        (QuotientGroup.eq_one_iff _).mp h1
      have h2 : orderOf (⟨⟨w, hN.mem⟩, hO⟩ : ↥(classicalInvolutionOddCore ↥N)) = 2 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
        exact hN.orderOf_eq_two
      have h3 := orderOf_dvd_natCard (⟨⟨w, hN.mem⟩, hO⟩ : ↥(classicalInvolutionOddCore ↥N))
      rw [h2] at h3
      exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥N))
        (even_iff_two_dvd.mpr h3)
  have hwqe : wq = e.symm (-1) := (orderOf_eq_two_iff_of_equiv_sl2 hodd e wq).mp hord
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm (slW (GaloisField p f)))
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm B₀)
  refine ⟨a, a.2, ?_, k, k.2, ?_⟩
  · have h1 : (QuotientGroup.mk (a * a * (⟨w, hN.mem⟩ : ↥N)⁻¹) :
        ↥N ⧸ classicalInvolutionOddCore ↥N) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ha, ← hwq, hwqe,
        ← map_mul, sl2_w_mul_self, mul_inv_cancel]
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    have h3 := mem_oddCoreIn_of_mem_classicalInvolutionOddCore h2
    simpa using h3
  · intro hmem
    have hO := mem_classicalInvolutionOddCore_of_mem_oddCoreIn hmem
    have h1 : (QuotientGroup.mk (a * k * a⁻¹ * k⁻¹) :
        ↥N ⧸ classicalInvolutionOddCore ↥N) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hO
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ha, hk] at h1
    have h2 : e.symm (slW (GaloisField p f) * B₀ * (slW (GaloisField p f))⁻¹ * B₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact h1
    have h3 := e.symm.injective (h2.trans (map_one e.symm).symm)
    apply hWB
    calc slW (GaloisField p f) * B₀
        = (slW (GaloisField p f) * B₀ * (slW (GaloisField p f))⁻¹ * B₀⁻¹) *
            (B₀ * slW (GaloisField p f)) := by group
      _ = B₀ * slW (GaloisField p f) := by rw [h3, one_mul]

omit [Finite G] in
theorem exists_zpowers_involution_of_sq_mem {x : G} {N : Subgroup G} (hN : Odd (Nat.card N))
    (hx2 : x * x ∈ N) : ∃ u ∈ Subgroup.zpowers x, u * u = 1 ∧ u * x⁻¹ ∈ N := by
  obtain ⟨k, hk⟩ := hN
  have h1 : (⟨x * x, hx2⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
  have h2 : (x * x) ^ Nat.card N = 1 := congrArg Subtype.val h1
  refine ⟨x ^ Nat.card N, Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _, ?_, ?_⟩
  · calc x ^ Nat.card N * x ^ Nat.card N = (x * x) ^ Nat.card N := by
          rw [← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := h2
  · have : x ^ Nat.card N * x⁻¹ = (x * x) ^ k := by
      rw [hk, pow_succ, mul_inv_cancel_right, pow_mul, sq]
    rw [this]
    exact Subgroup.pow_mem _ (by
      have : (x * x) ∈ N := hx2
      exact this) _

end Elements

section Lift

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

structure TwinLift (C : TwinShapeCtx p f Ω z) where
  K₁ : Subgroup G
  T₁ : Subgroup G
  J : Subgroup G
  u : G
  t : G
  R₁ : Subgroup (compModel C.D C.i₁).K
  hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  hK₁ : K₁ ∈ Ω
  hK₁z : IsUniqueInvolution K₁ z
  hT₁ : T₁ ∈ Ω
  hT₁z : IsUniqueInvolution T₁ z
  hK₁img : modOdd z K₁ = (C.psi C.i₀).range
  hT₁img : modOdd z T₁ = (C.psi C.i₂).range
  hJ : J ∈ tqMembers Ω z
  hJt : IsClassicalMember p f J t
  hJimg : modOdd z (exactCore z J) = R₁.map (C.psi C.i₁)
  ht : t ∈ Subgroup.centralizer ({z} : Set G)
  hu : u ∈ Subgroup.centralizer ({z} : Set G)
  hu_mem : u ∈ K₁ ⊔ T₁
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hut : t * u = u * t
  hu_comm : ∀ y ∈ (C.psi C.i₁).range,
    oddQuotMk z ⟨u, hu⟩ * y = y * oddQuotMk z ⟨u, hu⟩

structure TwinLiftCore (C : TwinShapeCtxCore p f Ω z) where
  K₁ : Subgroup G
  T₁ : Subgroup G
  J : Subgroup G
  u : G
  t : G
  R₁ : Subgroup (compModel C.D C.i₁).K
  hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  hK₁ : K₁ ∈ Ω
  hK₁z : IsUniqueInvolution K₁ z
  hT₁ : T₁ ∈ Ω
  hT₁z : IsUniqueInvolution T₁ z
  hK₁img : modOdd z K₁ = (C.psi C.i₀).range
  hT₁img : modOdd z T₁ = (C.psi C.i₂).range
  hJ : J ∈ tqMembers Ω z
  hJt : IsClassicalMember p f J t
  hJimg : modOdd z (exactCore z J) = R₁.map (C.psi C.i₁)
  ht : t ∈ Subgroup.centralizer ({z} : Set G)
  hu : u ∈ Subgroup.centralizer ({z} : Set G)
  hu_mem : u ∈ K₁ ⊔ T₁
  hu2 : u * u = 1
  hu1 : u ≠ 1
  huz : u ≠ z
  hut : t * u = u * t
  hu_comm : ∀ y ∈ (C.psi C.i₁).range,
    oddQuotMk z ⟨u, hu⟩ * y = y * oddQuotMk z ⟨u, hu⟩

@[expose] def TwinLift.toCore {C : TwinShapeCtx p f Ω z} (L : TwinLift C) :
    TwinLiftCore C.toCore where
  K₁ := L.K₁
  T₁ := L.T₁
  J := L.J
  u := L.u
  t := L.t
  R₁ := L.R₁
  hR₁ := L.hR₁
  hK₁ := L.hK₁
  hK₁z := L.hK₁z
  hT₁ := L.hT₁
  hT₁z := L.hT₁z
  hK₁img := L.hK₁img
  hT₁img := L.hT₁img
  hJ := L.hJ
  hJt := L.hJt
  hJimg := L.hJimg
  ht := L.ht
  hu := L.hu
  hu_mem := L.hu_mem
  hu2 := L.hu2
  hu1 := L.hu1
  huz := L.huz
  hut := L.hut
  hu_comm := L.hu_comm

@[expose] def TwinLiftCore.toLift {C : TwinShapeCtx p f Ω z} (L : TwinLiftCore C.toCore) :
    TwinLift C where
  K₁ := L.K₁
  T₁ := L.T₁
  J := L.J
  u := L.u
  t := L.t
  R₁ := L.R₁
  hR₁ := L.hR₁
  hK₁ := L.hK₁
  hK₁z := L.hK₁z
  hT₁ := L.hT₁
  hT₁z := L.hT₁z
  hK₁img := L.hK₁img
  hT₁img := L.hT₁img
  hJ := L.hJ
  hJt := L.hJt
  hJimg := L.hJimg
  ht := L.ht
  hu := L.hu
  hu_mem := L.hu_mem
  hu2 := L.hu2
  hu1 := L.hu1
  huz := L.huz
  hut := L.hut
  hu_comm := L.hu_comm


namespace TwinShapeCtxCore

variable (C : TwinShapeCtxCore p f Ω z)

theorem exists_lift (S : C.Spec) : Nonempty (TwinLiftCore C) := by
  classical
  have hodd : Odd (Nat.card (GaloisField p f)) := odd_natCard_galoisField C.hp C.hq
  have hzC := XCtx.hzC z
  have hz2 : z * z = 1 := C.hKz.sq
  obtain ⟨T, hTΩ, hTcl, hTmod⟩ := C.exists_twin S
  have hKcl := C.K_cl
  have hKC : C.K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember hKcl
  have hTC : T ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_isClassicalMember hTcl
  have hKmod : modOdd z C.K = (C.psi C.i₀).range := by
    have := S.hK₀
    rwa [C.exactCore_K] at this
  obtain ⟨a, haK, ha2, k, hkK, hka⟩ := exists_order_four hKcl hodd
  obtain ⟨a', ha'T, ha'2, -⟩ := exists_order_four hTcl hodd
  have haC : a ∈ Subgroup.centralizer ({z} : Set G) := hKC haK
  have ha'C : a' ∈ Subgroup.centralizer ({z} : Set G) := hTC ha'T
  have hkC : k ∈ Subgroup.centralizer ({z} : Set G) := hKC hkK
  have hOK : oddCoreIn C.K ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hKcl.subnormal
  have hOT : oddCoreIn T ≤ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hTcl.subnormal
  have hsq : ∀ (b : G) (hb : b ∈ Subgroup.centralizer ({z} : Set G)),
      b * b * z⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) →
      oddQuotMk z ⟨b, hb⟩ * oddQuotMk z ⟨b, hb⟩ = oddQuotMk z ⟨z, hzC⟩ := by
    intro b hb ho
    have hbC : b * b * z⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem hb hb) (inv_mem hzC)
    have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn ho hbC
    have e : (⟨b * b * z⁻¹, hbC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨b, hb⟩ * ⟨b, hb⟩ * ⟨z, hzC⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  have hā2 := hsq a haC (hOK ha2)
  have hā'2 := hsq a' ha'C (hOT ha'2)
  have hā : oddQuotMk z ⟨a, haC⟩ ∈ (C.psi C.i₀).range := by
    rw [← hKmod]; exact oddQuotMk_mem_modOdd haK haC
  have hā' : oddQuotMk z ⟨a', ha'C⟩ ∈ (C.psi C.i₂).range := by
    rw [← hTmod]; exact oddQuotMk_mem_modOdd ha'T ha'C
  have hkbar : oddQuotMk z ⟨k, hkC⟩ ∈ (C.psi C.i₀).range := by
    rw [← hKmod]; exact oddQuotMk_mem_modOdd hkK hkC
  have hcomm : ∀ {i j : Fin C.D.card}, i ≠ j → ∀ x ∈ (C.psi i).range, ∀ y ∈ (C.psi j).range,
      x * y = y * x := by
    rintro i j hij _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact C.psi_commute hij a b
  have hnc : ∀ c : OddQuot z, (∀ q, c * q = q * c) →
      oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ ≠ c := by
    intro c hc hcc
    have h2 : oddQuotMk z ⟨a', ha'C⟩ * oddQuotMk z ⟨k, hkC⟩ =
        oddQuotMk z ⟨k, hkC⟩ * oddQuotMk z ⟨a', ha'C⟩ :=
      (hcomm C.ne₀₂.symm _ hā' _ hkbar)
    have h3 : oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨k, hkC⟩ =
        oddQuotMk z ⟨k, hkC⟩ * oddQuotMk z ⟨a, haC⟩ := by
      have h1 : oddQuotMk z ⟨a, haC⟩ = c * (oddQuotMk z ⟨a', ha'C⟩)⁻¹ := by
        rw [← hcc]; group
      have h4 : (oddQuotMk z ⟨a', ha'C⟩)⁻¹ * oddQuotMk z ⟨k, hkC⟩ =
          oddQuotMk z ⟨k, hkC⟩ * (oddQuotMk z ⟨a', ha'C⟩)⁻¹ := by
        have := congrArg (fun x => (oddQuotMk z ⟨a', ha'C⟩)⁻¹ * x * (oddQuotMk z ⟨a', ha'C⟩)⁻¹) h2
        simpa [mul_assoc] using this.symm
      rw [h1, mul_assoc, h4, ← mul_assoc, hc, mul_assoc]
    have hcK : a * k * a⁻¹ * k⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem (mul_mem haC hkC) (inv_mem haC)) (inv_mem hkC)
    have h5 : oddQuotMk z ⟨a * k * a⁻¹ * k⁻¹, hcK⟩ = 1 := by
      have e : (⟨a * k * a⁻¹ * k⁻¹, hcK⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨a, haC⟩ * ⟨k, hkC⟩ * ⟨a, haC⟩⁻¹ * ⟨k, hkC⟩⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, h3]
      group
    have hmem : a * k * a⁻¹ * k⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) :=
      ⟨_, oddQuotMk_eq_one_iff.mp h5, rfl⟩
    have hKK : a * k * a⁻¹ * k⁻¹ ∈ C.K :=
      mul_mem (mul_mem (mul_mem haK hkK) (inv_mem haK)) (inv_mem hkK)
    exact hka (inf_oddCoreIn_le hKC ⟨hKK, hmem⟩)
  have hū1 : oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ ≠ 1 := hnc 1 (fun q => by simp)
  have hūz : oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ ≠ oddQuotMk z ⟨z, hzC⟩ :=
    hnc _ (fun q => oddQuotMk_central hzC q)
  have hū2 : (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) *
      (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) = 1 := by
    have hc02 := hcomm C.ne₀₂ _ hā _ hā'
    calc (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) *
        (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩)
        = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨a', ha'C⟩ * oddQuotMk z ⟨a, haC⟩) *
            oddQuotMk z ⟨a', ha'C⟩ := by group
      _ = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) *
            oddQuotMk z ⟨a', ha'C⟩ := by rw [← hc02]
      _ = (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a, haC⟩) *
            (oddQuotMk z ⟨a', ha'C⟩ * oddQuotMk z ⟨a', ha'C⟩) := by group
      _ = 1 := by
        rw [hā2, hā'2, ← map_mul]
        have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
          Subtype.ext hz2
        rw [this, map_one]
  have hxC : a * a' ∈ Subgroup.centralizer ({z} : Set G) := mul_mem haC ha'C
  have hxsq : a * a' * (a * a') ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) := by
    have hC : a * a' * (a * a') ∈ Subgroup.centralizer ({z} : Set G) := mul_mem hxC hxC
    have e : (⟨a * a' * (a * a'), hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨a, haC⟩ * ⟨a', ha'C⟩ * (⟨a, haC⟩ * ⟨a', ha'C⟩) := rfl
    have h1 : oddQuotMk z ⟨a * a' * (a * a'), hC⟩ = 1 := by
      rw [e, map_mul, map_mul]
      exact hū2
    exact ⟨_, oddQuotMk_eq_one_iff.mp h1, rfl⟩
  obtain ⟨u₀, hu₀x, hu₀2, hu₀O⟩ := exists_zpowers_involution_of_sq_mem
    (odd_card_oddCoreIn (Subgroup.centralizer ({z} : Set G))) hxsq
  have hu₀C : u₀ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.zpowers_le.mpr hxC hu₀x
  have hu₀KT : u₀ ∈ C.K ⊔ T := Subgroup.zpowers_le.mpr (Subgroup.mul_mem_sup haK ha'T) hu₀x
  have hu₀bar : oddQuotMk z ⟨u₀, hu₀C⟩ =
      oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ := by
    have hC : u₀ * (a * a')⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem hu₀C (inv_mem hxC)
    have h1 := oddQuotMk_eq_one_of_mem_oddCoreIn hu₀O hC
    have e : (⟨u₀ * (a * a')⁻¹, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨u₀, hu₀C⟩ * (⟨a, haC⟩ * ⟨a', ha'C⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, map_mul] at h1
    exact mul_inv_eq_one.mp h1
  have hu₀1 : u₀ ≠ 1 := by
    intro h
    apply hū1
    rw [← hu₀bar]
    have : (⟨u₀, hu₀C⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext h
    rw [this, map_one]
  have hu₀z : u₀ ≠ z := by
    intro h
    apply hūz
    rw [← hu₀bar]
    congr 1
    exact Subtype.ext h
  obtain ⟨R₁, hR₁, hmem⟩ := C.D.meets C.i₁
  have hRimg : R₁.map (C.psi C.i₁) ∈ memberImages (exactFamily Ω z) z := by
    rw [← map_sectionQuotientHom_family C.hs.normalizes]
    exact ⟨_, hmem, Subgroup.map_map _ _ _⟩
  obtain ⟨M, hM, hMR⟩ := hRimg
  obtain ⟨N, hN, rfl⟩ := hM.1
  have hNmod : modOdd z (exactCore z N) = R₁.map (C.psi C.i₁) := hMR
  obtain ⟨w, hw⟩ := C.hΩ.classical N hN.1
  have hwC := C.involution_mem_centralizer hN hw
  have hwE := C.involution_mem_exactCore hN hw
  have hwsq := (isCentralInvolution_of_isClassicalMember hw).sq
  have hwbar : oddQuotMk z ⟨w, hwC⟩ ∈ (C.psi C.i₁).range := by
    have := oddQuotMk_mem_modOdd hwE hwC
    rw [hNmod] at this
    obtain ⟨r, -, hr⟩ := this
    exact ⟨r, hr⟩
  have hcomm₁ : oddQuotMk z ⟨u₀, hu₀C⟩ * oddQuotMk z ⟨w, hwC⟩ =
      oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨u₀, hu₀C⟩ := by
    have h01 := hcomm C.ne₀₁ _ hā _ hwbar
    have h21 := hcomm C.ne₁₂.symm _ hā' _ hwbar
    rw [hu₀bar]
    calc oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ * oddQuotMk z ⟨w, hwC⟩
        = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨a', ha'C⟩ * oddQuotMk z ⟨w, hwC⟩) := by group
      _ = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨a', ha'C⟩) := by rw [h21]
      _ = (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨w, hwC⟩) * oddQuotMk z ⟨a', ha'C⟩ := by group
      _ = (oddQuotMk z ⟨w, hwC⟩ * oddQuotMk z ⟨a, haC⟩) * oddQuotMk z ⟨a', ha'C⟩ := by rw [h01]
      _ = oddQuotMk z ⟨w, hwC⟩ * (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) := by group
  obtain ⟨o₁, ho₁, o₂, ho₂, hc⟩ := exists_conj_commuting z hu₀C hwC hu₀2 hwsq hcomm₁
  have ho₁C : o₁ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₁
  have ho₂C : o₂ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₂
  have huC : o₁ * u₀ * o₁⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₁C hu₀C) (inv_mem ho₁C)
  have htC : o₂ * w * o₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₂C hwC) (inv_mem ho₂C)
  have hbar : ∀ (o v : G) (ho : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
      (hoC : o ∈ Subgroup.centralizer ({z} : Set G)) (hvC : v ∈ Subgroup.centralizer ({z} : Set G))
      (hC : o * v * o⁻¹ ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨o * v * o⁻¹, hC⟩ = oddQuotMk z ⟨v, hvC⟩ := by
    intro o v ho hoC hvC hC
    have h1 : oddQuotMk z ⟨o, hoC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn ho hoC
    have : (⟨o * v * o⁻¹, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨o, hoC⟩ * ⟨v, hvC⟩ * ⟨o, hoC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, h1]
    simp
  have himg : ∀ (o : G) (M : Subgroup G), o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) →
      o ∈ Subgroup.centralizer ({z} : Set G) →
      modOdd z (exactCore z (conjSub o M)) = modOdd z (exactCore z M) := by
    intro o M ho hoC
    have : exactCore z (conjSub o M) = conjSub o (exactCore z M) :=
      triangleResidual_conjSub M hoC
    rw [this]
    exact modOdd_conjSub_of_mem_oddCoreIn ho
  have hzfix : ∀ o : G, o ∈ Subgroup.centralizer ({z} : Set G) → o * z * o⁻¹ = z :=
    fun o ho => conj_eq_of_mem_centralizer_singleton ho
  have hubar : oddQuotMk z ⟨o₁ * u₀ * o₁⁻¹, huC⟩ =
      oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ :=
    (hbar o₁ u₀ ho₁ ho₁C hu₀C huC).trans hu₀bar
  refine ⟨{
    K₁ := conjSub o₁ C.K
    T₁ := conjSub o₁ T
    J := conjSub o₂ N
    u := o₁ * u₀ * o₁⁻¹
    t := o₂ * w * o₂⁻¹
    R₁ := R₁
    hR₁ := hR₁
    hK₁ := C.hΩ.conjInvariant o₁ C.K C.hK
    hK₁z := by
      have := C.hKz.conj o₁
      rwa [hzfix o₁ ho₁C] at this
    hT₁ := C.hΩ.conjInvariant o₁ T hTΩ
    hT₁z := by
      have := (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq hTcl).conj o₁
      rwa [hzfix o₁ ho₁C] at this
    hK₁img := (modOdd_conjSub_of_mem_oddCoreIn ho₁).trans hKmod
    hT₁img := (modOdd_conjSub_of_mem_oddCoreIn ho₁).trans hTmod
    hJ := conjSub_mem_tqMembers C.hΩ.conjInvariant ho₂C hN
    hJt := hw.conj o₂
    hJimg := (himg o₂ N ho₂ ho₂C).trans hNmod
    ht := htC
    hu := huC
    hu_mem := by
      have h1 : o₁ * u₀ * o₁⁻¹ ∈ conjSub o₁ (C.K ⊔ T) := conj_mem_conjSub hu₀KT
      have h2 : conjSub o₁ (C.K ⊔ T) = conjSub o₁ C.K ⊔ conjSub o₁ T := Subgroup.map_sup _ _ _
      rwa [h2] at h1
    hu2 := by
      calc o₁ * u₀ * o₁⁻¹ * (o₁ * u₀ * o₁⁻¹) = o₁ * (u₀ * u₀) * o₁⁻¹ := by group
        _ = 1 := by rw [hu₀2]; group
    hu1 := by
      intro h
      apply hu₀1
      calc u₀ = o₁⁻¹ * (o₁ * u₀ * o₁⁻¹) * o₁ := by group
        _ = 1 := by rw [h]; group
    huz := by
      intro h
      apply hu₀z
      calc u₀ = o₁⁻¹ * (o₁ * u₀ * o₁⁻¹) * o₁ := by group
        _ = o₁⁻¹ * z * o₁ := by rw [h]
        _ = z := by
          have := hzfix o₁⁻¹ (inv_mem ho₁C)
          rwa [inv_inv] at this
    hut := by
      have := hc.symm
      exact this
    hu_comm := by
      intro y hy
      rw [hubar]
      obtain ⟨y', rfl⟩ := hy
      have h01 := hcomm C.ne₀₁ _ hā _ ⟨y', rfl⟩
      have h21 := hcomm C.ne₁₂.symm _ hā' _ ⟨y', rfl⟩
      calc oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩ * C.psi C.i₁ y'
          = oddQuotMk z ⟨a, haC⟩ * (oddQuotMk z ⟨a', ha'C⟩ * C.psi C.i₁ y') := by group
        _ = oddQuotMk z ⟨a, haC⟩ * (C.psi C.i₁ y' * oddQuotMk z ⟨a', ha'C⟩) := by rw [h21]
        _ = (oddQuotMk z ⟨a, haC⟩ * C.psi C.i₁ y') * oddQuotMk z ⟨a', ha'C⟩ := by group
        _ = (C.psi C.i₁ y' * oddQuotMk z ⟨a, haC⟩) * oddQuotMk z ⟨a', ha'C⟩ := by rw [h01]
        _ = C.psi C.i₁ y' * (oddQuotMk z ⟨a, haC⟩ * oddQuotMk z ⟨a', ha'C⟩) := by group }⟩

end TwinShapeCtxCore

namespace TwinShapeCtx

variable (C : TwinShapeCtx p f Ω z)

theorem exists_lift (S : C.Spec) : Nonempty (TwinLift C) :=
  (C.toCore.exists_lift S.toCore).map TwinLiftCore.toLift

end TwinShapeCtx

end Lift

end CFSG.ClassicalInvolution.Asc77

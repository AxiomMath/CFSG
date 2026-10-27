module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiA
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2W1

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Concl

@[expose] def CentInvConcl (r : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (β : MulAut A),
    β * β = 1 → β ≠ 1 → (∀ x ∈ Q, β x = x) → β = MulAut.conj (quatInvolution r e)

theorem centInvConcl_of_model {r : ℕ} (hCent : Z2BigModelCent r) (hr : 4 ≤ r) {X : Type}
    [Group X] [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : CentInvConcl r X := by
  intro Q e β hβ2 hβ1 hfix
  have hH2 : IsPGroup 2 ↥(Subgroup.zpowers β) :=
    CFSG.ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one hβ2
  have hHfix : ∀ γ ∈ Subgroup.zpowers β, ∀ x ∈ Q, γ x = x := by
    intro γ hγ x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hγ
    have hxinv : β⁻¹ x = x := by
      calc β⁻¹ x = β⁻¹ (β x) := by rw [hfix x hx]
        _ = x := MulAut.inv_apply_self X β x
    exact zpow_induction_left (g := β) (P := fun γ => γ x = x) (by simp)
      (fun a ha => by rw [MulAut.mul_apply, ha, hfix x hx])
      (fun a ha => by rw [MulAut.mul_apply, ha]; exact hxinv) k
  exact ((hCent hr X p f hm Q e).2 (Subgroup.zpowers β) hH2 hHfix).2.2 β
    (Subgroup.mem_zpowers β) hβ2 hβ1

theorem quatInvolution_equivMapOfInjective {r : ℕ} {A B : Type} [Group A] [Group B]
    (φ : A ≃* B) (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r ((Q.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e) =
      φ (quatInvolution r e) := by
  simp only [quatInvolution, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  exact Subgroup.coe_equivMapOfInjective_apply Q φ.toMonoidHom φ.injective (e.symm _)

theorem centInvConcl_congr {r : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : CentInvConcl r B) : CentInvConcl r A := by
  intro Q e β hβ2 hβ1 hfix
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  have hβ'2 : MulAut.congr φ β * MulAut.congr φ β = 1 := by
    rw [← map_mul, hβ2, map_one]
  have hβ'1 : MulAut.congr φ β ≠ 1 := by
    intro h
    exact hβ1 ((MulAut.congr φ).injective (by rw [h, map_one]))
  have hfix' : ∀ x ∈ Q', MulAut.congr φ β x = x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show MulAut.congr φ β (φ y) = φ y
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hfix y hy]
  have hkey := hB Q' e' (MulAut.congr φ β) hβ'2 hβ'1 hfix'
  have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
    quatInvolution_equivMapOfInjective φ Q e
  apply (MulAut.congr φ).injective
  rw [hkey, hquat, mulAut_congr_conj φ (quatInvolution r e)]

end Concl

section QuatImage

variable {G : Type} [Group G] [Finite G]

theorem exists_quatImage {r : ℕ} {Λ Q : Subgroup G} {d : G} (hQΛ : Q ≤ Λ) (hdΛ : d ∈ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d) :
    ∃ (Qb : Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
      (eb : ↥Qb ≃* QuaternionGroup (2 ^ (r - 2))),
      quatInvolution r eb = QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) ∧
        ∀ y ∈ Qb, ∃ (q : G) (hq : q ∈ Λ), q ∈ Q ∧
          y = QuotientGroup.mk (⟨q, hq⟩ : ↥Λ) := by
  let O := classicalInvolutionOddCore ↥Λ
  let ι : ↥(Q.subgroupOf Λ) →* ↥Λ ⧸ O := (QuotientGroup.mk' O).comp (Q.subgroupOf Λ).subtype
  have hι : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyO : (y : ↥Λ) ∈ O := (QuotientGroup.eq_one_iff _).mp hy
    have hyQ : (((y : ↥Λ) : G)) ∈ Q := Subgroup.mem_subgroupOf.mp y.2
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hyQ⟩
    have hj' : ((y : ↥Λ) : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have h1 : ((y : ↥Λ) : G) = 1 :=
      eq_one_of_mem_oddCoreOf (mem_oddCoreOf_iff.mpr ⟨(y : ↥Λ).2, hyO⟩) hj'
    exact Subtype.ext (Subtype.ext h1)
  let Qb : Subgroup (↥Λ ⧸ O) := ι.range
  let eb : ↥Qb ≃* QuaternionGroup (2 ^ (r - 2)) :=
    (MonoidHom.ofInjective hι).symm.trans ((Subgroup.subgroupOfEquivOfLe hQΛ).trans e)
  refine ⟨Qb, eb, ?_, ?_⟩
  · change ((eb.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))) :
        ↥Qb) : ↥Λ ⧸ O) = QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ)
    change ι ((Subgroup.subgroupOfEquivOfLe hQΛ).symm
      (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2)))))) = _
    change QuotientGroup.mk _ = _
    congr 1
    exact Subtype.ext hd
  · intro y hy
    obtain ⟨q', rfl⟩ := MonoidHom.mem_range.mp hy
    refine ⟨((q' : ↥Λ) : G), (q' : ↥Λ).2, Subgroup.mem_subgroupOf.mp q'.2, ?_⟩
    rfl

theorem actsTriv_or_actsLike_of_concl {r : ℕ} {Λ Q : Subgroup G} {d c : G} (hQΛ : Q ≤ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d)
    (hcN : c ∈ Subgroup.normalizer (Λ : Set G)) (hcc : ActsTriv Λ (c * c))
    (hcQ : ∀ q ∈ Q, c * q * c⁻¹ = q)
    (hC : CentInvConcl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) :
    ActsTriv Λ c ∨ ActsLike Λ c d := by
  have hdΛ : d ∈ Λ := hd ▸ hQΛ (e.symm (QuaternionGroup.a
    ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))).2
  obtain ⟨Qb, eb, hquat, hmem⟩ := exists_quatImage hQΛ hdΛ hQ2 e hd
  let β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) := actAut Λ ⟨c, hcN⟩
  have hββ : β * β = 1 := by
    show actAut Λ ⟨c, hcN⟩ * actAut Λ ⟨c, hcN⟩ = 1
    rw [← map_mul]
    exact (actAut_eq_one_iff (Subgroup.mul_mem _ hcN hcN)).mpr hcc
  have hfix : ∀ y ∈ Qb, β y = y := by
    intro y hy
    obtain ⟨q, hq, hqQ, rfl⟩ := hmem y hy
    have hL : (Λ.normalizerMonoidHom ⟨c, hcN⟩ ⟨q, hq⟩ : ↥Λ) = ⟨q, hq⟩ :=
      Subtype.ext (by
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
        exact hcQ q hqQ)
    show actAut Λ ⟨c, hcN⟩ (QuotientGroup.mk (⟨q, hq⟩ : ↥Λ)) =
      QuotientGroup.mk (⟨q, hq⟩ : ↥Λ)
    rw [actAut_mk, hL]
  by_cases hβ1 : β = 1
  · left
    exact (actAut_eq_one_iff hcN).mp hβ1
  · right
    have hkey := hC Qb eb β hββ hβ1 hfix
    rw [hquat] at hkey
    exact (actAut_eq_conj_iff hcN hdΛ).mp hkey

end QuatImage

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

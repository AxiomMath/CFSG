module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2BigPiA

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Concl

@[expose] def CentAConcl (r : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (x : A),
    (∀ y ∈ Q, x * y = y * x) → (∃ k : ℕ, x ^ 2 ^ k = 1) → x = 1 ∨ x = quatInvolution r e

@[expose] def CentBConcl (r : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (β : MulAut A),
    β * β = 1 → (∀ x ∈ Q, β x = x) → β = 1 ∨ β = MulAut.conj (quatInvolution r e)

theorem centAConcl_of_model {r : ℕ} (hCent : Z2BigModelCent r) (hr : 4 ≤ r) {X : Type} [Group X]
    [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : CentAConcl r X := by
  intro Q e x hxQ hx2
  exact (hCent hr X p f hm Q e).1 x hxQ hx2

theorem centBConcl_of_model {r : ℕ} (hCent : Z2BigModelCent r) (hr : 4 ≤ r) {X : Type} [Group X]
    [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : CentBConcl r X := by
  intro Q e β hββ hβQ
  by_cases hβ1 : β = 1
  · exact Or.inl hβ1
  · right
    have hH2 : IsPGroup 2 ↥(Subgroup.zpowers β) := by
      have hdvd : orderOf β ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hββ)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
    have hHfix : ∀ γ ∈ Subgroup.zpowers β, ∀ x ∈ Q, γ x = x := by
      intro γ hγ x hx
      have hle : Subgroup.zpowers β ≤ MulAction.stabilizer (MulAut X) x :=
        Subgroup.zpowers_le.mpr (by
          rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
          exact hβQ x hx)
      have hmem := hle hγ
      rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hmem
    exact (hCent hr X p f hm Q e).2 (Subgroup.zpowers β) hH2 hHfix |>.2.2 β
      (Subgroup.mem_zpowers β) hββ hβ1

private theorem mulAut_congr_conj_cent {A B : Type} [Group A] [Group B] (φ : A ≃* B) (m : A) :
    MulAut.congr φ (MulAut.conj m) = MulAut.conj (φ m) := by
  ext x
  change φ (m * φ.symm x * m⁻¹) = φ m * x * (φ m)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem quatInvolution_equivMapOfInjective_cent {r : ℕ} {A B : Type} [Group A] [Group B]
    (φ : A ≃* B) (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r ((Q.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e) =
      φ (quatInvolution r e) := by
  simp only [quatInvolution, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  exact Subgroup.coe_equivMapOfInjective_apply Q φ.toMonoidHom φ.injective (e.symm _)

theorem centAConcl_congr {r : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : CentAConcl r B) : CentAConcl r A := by
  intro Q e x hxQ hx2
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  have hxQ' : ∀ y ∈ Q', φ x * y = y * φ x := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change φ x * φ z = φ z * φ x
    rw [← map_mul, ← map_mul, hxQ z hz]
  have hx2' : ∃ k : ℕ, (φ x) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx2
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  rcases hB Q' e' (φ x) hxQ' hx2' with h | h
  · left
    apply φ.injective
    rw [h, map_one]
  · right
    have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
      quatInvolution_equivMapOfInjective_cent φ Q e
    apply φ.injective
    rw [h, hquat]

theorem centBConcl_congr {r : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : CentBConcl r B) : CentBConcl r A := by
  intro Q e β hββ hβQ
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  let β' : MulAut B := MulAut.congr φ β
  have hβ'β' : β' * β' = 1 := by
    change MulAut.congr φ β * MulAut.congr φ β = 1
    rw [← map_mul, hββ, map_one]
  have hβ'Q' : ∀ y ∈ Q', β' y = y := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    change MulAut.congr φ β (φ z) = φ z
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hβQ z hz]
  rcases hB Q' e' β' hβ'β' hβ'Q' with h | h
  · left
    apply (MulAut.congr φ).injective
    rw [map_one]
    exact h
  · right
    have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
      quatInvolution_equivMapOfInjective_cent φ Q e
    apply (MulAut.congr φ).injective
    rw [mulAut_congr_conj_cent φ (quatInvolution r e), ← hquat]
    exact h

end Concl

section Lambda

variable {G : Type} [Group G] [Finite G]

theorem exists_centData {r : ℕ} {Λ Q : Subgroup G} {d : G} (hQΛ : Q ≤ Λ) (hdΛ : d ∈ Λ)
    (hQ2 : IsPGroup 2 ↥Q) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (hd : quatInvolution r e = d) :
    ∃ (Qb : Subgroup (↥Λ ⧸ classicalInvolutionOddCore ↥Λ))
      (eb : ↥Qb ≃* QuaternionGroup (2 ^ (r - 2))),
      quatInvolution r eb = QuotientGroup.mk (⟨d, hdΛ⟩ : ↥Λ) ∧
        ∀ q : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ, q ∈ Qb ↔
          ∃ (y : G) (hy : y ∈ Q), q = QuotientGroup.mk (⟨y, hQΛ hy⟩ : ↥Λ) := by
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
  · intro q
    constructor
    · intro hq
      obtain ⟨y', hy'⟩ := MonoidHom.mem_range.mp hq
      refine ⟨((y' : ↥Λ) : G), Subgroup.mem_subgroupOf.mp y'.2, ?_⟩
      rw [← hy']
      rfl
    · rintro ⟨y, hy, rfl⟩
      exact MonoidHom.mem_range.mpr
        ⟨⟨⟨y, hQΛ hy⟩, Subgroup.mem_subgroupOf.mpr hy⟩, rfl⟩

theorem cent_a_of_concl {r : ℕ} {Λ Q : Subgroup G} (hQΛ : Q ≤ Λ) (hQ2 : IsPGroup 2 ↥Q)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    (hC : CentAConcl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) {x : G} (hxΛ : x ∈ Λ)
    (hxQ : ∀ y ∈ Q, x * y = y * x) (hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1) :
    x ∈ oddCoreOf Λ ∨ x * (quatInvolution r e)⁻¹ ∈ oddCoreOf Λ := by
  have hdΛ : quatInvolution r e ∈ Λ :=
    hQΛ (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))).2
  obtain ⟨Qb, eb, hqe, hmem⟩ := exists_centData hQΛ hdΛ hQ2 e rfl
  have hxQbar : ∀ y ∈ Qb,
      QuotientGroup.mk (⟨x, hxΛ⟩ : ↥Λ) * y = y * QuotientGroup.mk (⟨x, hxΛ⟩ : ↥Λ) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := (hmem q).mp hq
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hxQ y hy)
  have hx2bar : ∃ k : ℕ,
      (QuotientGroup.mk (⟨x, hxΛ⟩ : ↥Λ) : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hx2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow]
    rw [show (⟨x, hxΛ⟩ : ↥Λ) ^ 2 ^ k = 1 from Subtype.ext (by simpa using hk)]
    rfl
  rcases hC Qb eb (QuotientGroup.mk (⟨x, hxΛ⟩ : ↥Λ)) hxQbar hx2bar with h | h
  · left
    exact mem_oddCoreOf_iff.mpr ⟨hxΛ, (QuotientGroup.eq_one_iff _).mp h⟩
  · right
    rw [hqe] at h
    exact mul_inv_mem_oddCoreOf_of_mk_eq hxΛ hdΛ h

theorem cent_b_of_concl {r : ℕ} {Λ Q : Subgroup G} (hQΛ : Q ≤ Λ) (hQ2 : IsPGroup 2 ↥Q)
    (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2)))
    (hC : CentBConcl r (↥Λ ⧸ classicalInvolutionOddCore ↥Λ)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (Λ : Set G)) (hx2 : x * x = 1)
    (hxQ : ∀ y ∈ Q, x * y = y * x) : InnerModOdd Λ x := by
  have hdΛ : quatInvolution r e ∈ Λ :=
    hQΛ (e.symm (QuaternionGroup.a ((2 ^ (r - 2) : ℕ) : ZMod (2 * 2 ^ (r - 2))))).2
  obtain ⟨Qb, eb, hqe, hmem⟩ := exists_centData hQΛ hdΛ hQ2 e rfl
  have hββ : actAut Λ ⟨x, hxN⟩ * actAut Λ ⟨x, hxN⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (Λ : Set G))) * ⟨x, hxN⟩ = 1 := by
      refine Subtype.ext ?_
      show x * x = 1
      exact hx2
    rw [h1, map_one]
  have hβQb : ∀ q ∈ Qb, actAut Λ ⟨x, hxN⟩ q = q := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := (hmem q).mp hq
    rw [actAut_mk]
    have hL : (Λ.normalizerMonoidHom ⟨x, hxN⟩ ⟨y, hQΛ hy⟩ : ↥Λ) = ⟨y, hQΛ hy⟩ := by
      refine Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      rw [hxQ y hy]
      group
    rw [hL]
  rcases hC Qb eb (actAut Λ ⟨x, hxN⟩) hββ hβQb with h | h
  · apply (actAut_mem_innGrp_iff hxN).mp
    rw [h]
    exact MonoidHom.mem_range.mpr ⟨1, by rw [map_one]⟩
  · apply (actAut_mem_innGrp_iff hxN).mp
    rw [hqe] at h
    exact MonoidHom.mem_range.mpr
      ⟨QuotientGroup.mk (⟨quatInvolution r e, hdΛ⟩ : ↥Λ), h.symm⟩

end Lambda

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.LinkZ2L2Big2

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TL4.Z2W
open CFSG.Blueprint

section Act

variable {G : Type} [Group G]

@[expose] noncomputable def actAut (Λ : Subgroup G) :
    ↥(Subgroup.normalizer (Λ : Set G)) →* MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) where
  toFun x := QuotientGroup.congr _ _ (Λ.normalizerMonoidHom x)
    (CFSG.ComponentClassification.OddCore.char_invariant _)
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    change QuotientGroup.mk ((Λ.normalizerMonoidHom 1) y) = QuotientGroup.mk y
    rw [map_one]
    rfl
  map_mul' x y := by
    refine MulEquiv.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    change QuotientGroup.mk ((Λ.normalizerMonoidHom (x * y)) z) =
      QuotientGroup.mk ((Λ.normalizerMonoidHom x) ((Λ.normalizerMonoidHom y) z))
    rw [map_mul]
    rfl

theorem actAut_mk {Λ : Subgroup G} (x : ↥(Subgroup.normalizer (Λ : Set G))) (y : ↥Λ) :
    actAut Λ x (QuotientGroup.mk y) = QuotientGroup.mk (Λ.normalizerMonoidHom x y) := rfl

private theorem mk_eq_of_mul_inv_mem_oddCoreOf {Λ : Subgroup G} {a b : G} (ha : a ∈ Λ)
    (hb : b ∈ Λ) (h : a * b⁻¹ ∈ oddCoreOf Λ) :
    (QuotientGroup.mk (⟨a, ha⟩ : ↥Λ) : ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =
      QuotientGroup.mk ⟨b, hb⟩ := by
  rw [QuotientGroup.eq]
  obtain ⟨hΛ, hO⟩ := mem_oddCoreOf_iff.mp h
  have h1 : ((⟨b, hb⟩ : ↥Λ)⁻¹ * (⟨a * b⁻¹, hΛ⟩ : ↥Λ)⁻¹ *
      ((⟨b, hb⟩ : ↥Λ)⁻¹)⁻¹) ∈ classicalInvolutionOddCore ↥Λ :=
    Subgroup.Normal.conj_mem inferInstance (⟨a * b⁻¹, hΛ⟩ : ↥Λ)⁻¹
      (Subgroup.inv_mem _ hO) (⟨b, hb⟩ : ↥Λ)⁻¹
  convert h1 using 1
  ext
  simp only [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_mk]
  group

theorem actAut_eq_one_iff [Finite G] {Λ : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Λ : Set G)) :
    actAut Λ ⟨x, hx⟩ = 1 ↔ ActsTriv Λ x := by
  constructor
  · intro h z hz
    have hzx : x * z * x⁻¹ ∈ Λ := (Subgroup.mem_normalizer_iff.mp hx z).mp hz
    have hcongr := congrArg
      (fun β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =>
        β (QuotientGroup.mk (⟨z, hz⟩ : ↥Λ))) h
    simp only [actAut_mk] at hcongr
    have hcongr' : (QuotientGroup.mk (⟨x * z * x⁻¹, hzx⟩ : ↥Λ) :
        ↥Λ ⧸ classicalInvolutionOddCore ↥Λ) = QuotientGroup.mk (⟨z, hz⟩ : ↥Λ) := by
      have hL : (Λ.normalizerMonoidHom ⟨x, hx⟩ ⟨z, hz⟩ : ↥Λ) = ⟨x * z * x⁻¹, hzx⟩ :=
        Subtype.ext (by
          simpa using Subgroup.normalizerMonoidHom_apply_apply_coe Λ ⟨x, hx⟩ ⟨z, hz⟩)
      change QuotientGroup.mk (Λ.normalizerMonoidHom ⟨x, hx⟩ ⟨z, hz⟩) =
        QuotientGroup.mk (⟨z, hz⟩ : ↥Λ) at hcongr
      rwa [hL] at hcongr
    exact mul_inv_mem_oddCoreOf_of_mk_eq hzx hz hcongr'
  · intro h
    refine MulEquiv.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [actAut_mk]
    change QuotientGroup.mk (Λ.normalizerMonoidHom ⟨x, hx⟩ z) = QuotientGroup.mk z
    have hzx : x * ↑z * x⁻¹ ∈ Λ := (Subgroup.mem_normalizer_iff.mp hx (z : G)).mp z.2
    have hL : (Λ.normalizerMonoidHom ⟨x, hx⟩ z : ↥Λ) = ⟨x * ↑z * x⁻¹, hzx⟩ :=
      Subtype.ext (by
        simpa using Subgroup.normalizerMonoidHom_apply_apply_coe Λ ⟨x, hx⟩ z)
    rw [hL]
    exact mk_eq_of_mul_inv_mem_oddCoreOf hzx z.2 (h (z : G) z.2)

theorem actAut_eq_conj_iff [Finite G] {Λ : Subgroup G} {x w : G}
    (hx : x ∈ Subgroup.normalizer (Λ : Set G)) (hw : w ∈ Λ) :
    actAut Λ ⟨x, hx⟩ = MulAut.conj (QuotientGroup.mk (⟨w, hw⟩ : ↥Λ)) ↔ ActsLike Λ x w := by
  constructor
  · intro h z hz
    have hzx : x * z * x⁻¹ ∈ Λ := (Subgroup.mem_normalizer_iff.mp hx z).mp hz
    have hzw : w * z * w⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hw hz) (Λ.inv_mem hw)
    have hcongr := congrArg
      (fun β : MulAut (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) =>
        β (QuotientGroup.mk (⟨z, hz⟩ : ↥Λ))) h
    simp only [actAut_mk, MulAut.conj_apply] at hcongr
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul] at hcongr
    have hL : (Λ.normalizerMonoidHom ⟨x, hx⟩ ⟨z, hz⟩ : ↥Λ) = ⟨x * z * x⁻¹, hzx⟩ :=
      Subtype.ext (by
        simpa using Subgroup.normalizerMonoidHom_apply_apply_coe Λ ⟨x, hx⟩ ⟨z, hz⟩)
    have hR : ((⟨w, hw⟩ : ↥Λ) * ⟨z, hz⟩ * (⟨w, hw⟩ : ↥Λ)⁻¹) = ⟨w * z * w⁻¹, hzw⟩ := rfl
    rw [hL, hR] at hcongr
    exact mul_inv_mem_oddCoreOf_of_mk_eq hzx hzw hcongr
  · intro h
    refine MulEquiv.ext fun q => ?_
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [actAut_mk, MulAut.conj_apply]
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hzx : x * ↑z * x⁻¹ ∈ Λ := (Subgroup.mem_normalizer_iff.mp hx (z : G)).mp z.2
    have hzw : w * ↑z * w⁻¹ ∈ Λ := Λ.mul_mem (Λ.mul_mem hw z.2) (Λ.inv_mem hw)
    have hL : (Λ.normalizerMonoidHom ⟨x, hx⟩ z : ↥Λ) = ⟨x * ↑z * x⁻¹, hzx⟩ :=
      Subtype.ext (by
        simpa using Subgroup.normalizerMonoidHom_apply_apply_coe Λ ⟨x, hx⟩ z)
    have hR : ((⟨w, hw⟩ : ↥Λ) * z * (⟨w, hw⟩ : ↥Λ)⁻¹) = ⟨w * ↑z * w⁻¹, hzw⟩ := rfl
    rw [hL, hR]
    exact mk_eq_of_mul_inv_mem_oddCoreOf hzx hzw (h (z : G) z.2)

theorem actAut_mem_innGrp_iff [Finite G] {Λ : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (Λ : Set G)) :
    actAut Λ ⟨x, hx⟩ ∈ innGrp (↥Λ ⧸ classicalInvolutionOddCore ↥Λ) ↔ InnerModOdd Λ x := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := MonoidHom.mem_range.mp h
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨w, hw, (actAut_eq_conj_iff hx hw).mp hq.symm⟩
  · rintro ⟨w, hw, h⟩
    exact MonoidHom.mem_range.mpr
      ⟨QuotientGroup.mk (⟨w, hw⟩ : ↥Λ), ((actAut_eq_conj_iff hx hw).mpr h).symm⟩

theorem actAut_pow {Λ : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (Λ : Set G)) (m : ℕ) :
    actAut Λ ⟨x ^ m, Subgroup.pow_mem _ hx m⟩ = actAut Λ ⟨x, hx⟩ ^ m := by
  rw [← map_pow]
  rfl

@[expose] noncomputable def conjQuotEquiv (g : G) (Λ : Subgroup G) :
    ↥(conjSub g Λ) ⧸ classicalInvolutionOddCore ↥(conjSub g Λ) ≃*
      ↥Λ ⧸ classicalInvolutionOddCore ↥Λ :=
  QuotientGroup.congr _ _
    ((Subgroup.equivMapOfInjective Λ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm)
    (by
      have h := CFSG.ComponentClassification.OddCore.equiv_invariant
        ((Subgroup.equivMapOfInjective Λ (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective).symm)
      exact h)

end Act

section Concl

variable {A : Type} [Group A]

@[expose] def PiCycConcl (r E : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut A)),
    IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
      ∀ g ∈ H, 2 ^ E < orderOf g → g ^ (orderOf g / 2) = MulAut.conj (quatInvolution r e)

@[expose] def PiQuatConcl (r : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut A)),
    IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
      ∀ (m : ℕ), 1 ≤ m → ∀ B : Subgroup (MulAut A), B ≤ H →
        ∀ eB : ↥B ≃* QuaternionGroup (2 ^ m),
          ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B) : MulAut A) =
            MulAut.conj (quatInvolution r e)

@[expose] def Pi4Concl (r : ℕ) (A : Type) [Group A] : Prop :=
  ∀ (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) (H : Subgroup (MulAut A)),
    IsPGroup 2 ↥H → (∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) →
      ∀ g ∈ H, ∀ K : ℕ, 2 ≤ K → orderOf g = 2 ^ K →
        g ^ 2 ^ (K - 1) = MulAut.conj (quatInvolution r e) ∨ g ^ 2 ^ (K - 1) ∉ innGrp A

theorem piCycConcl_of_model {r : ℕ} (hCyc : Z2BigModelPiCyc r) (hr : 4 ≤ r) {X : Type} [Group X]
    [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : PiCycConcl r (padicValNat 2 f) X :=
  fun Q e H h2 hN g hg ho => hCyc hr X p f hm Q e H h2 hN g hg ho

theorem piQuatConcl_of_model {r : ℕ} (hQuat : Z2BigModelPiQuat r) (hr : 4 ≤ r) {X : Type}
    [Group X] [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : PiQuatConcl r X :=
  fun Q e H h2 hN m hm1 B hB eB => hQuat hr X p f hm Q e H h2 hN m hm1 B hB eB

theorem pi4Concl_of_model {r : ℕ} (hPi4 : Z2BigModelPi4 r) (hr : 4 ≤ r) {X : Type}
    [Group X] [Finite X] {p f : ℕ} (hm : Z2BigLinkModel r X p f) : Pi4Concl r X :=
  fun Q e H h2 hN g hg K hK ho => hPi4 hr X p f hm Q e H h2 hN g hg K hK ho

private theorem mulAut_congr_conj {A B : Type} [Group A] [Group B] (φ : A ≃* B) (m : A) :
    MulAut.congr φ (MulAut.conj m) = MulAut.conj (φ m) := by
  ext x
  change φ (m * φ.symm x * m⁻¹) = φ m * x * (φ m)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem map_equivMap_normalizes {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    {Q : Subgroup A} {H : Subgroup (MulAut A)}
    (hN : ∀ β ∈ H, ∀ x ∈ Q, β x ∈ Q) :
    ∀ β ∈ H.map (MulAut.congr φ).toMonoidHom, ∀ x ∈ Q.map φ.toMonoidHom,
      β x ∈ Q.map φ.toMonoidHom := by
  intro β hβ x hx
  obtain ⟨β₀, hβ₀, rfl⟩ := hβ
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨β₀ y, hN β₀ hβ₀ y hy, ?_⟩
  show φ (β₀ y) = MulAut.congr φ β₀ (φ y)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem quatInvolution_equivMapOfInjective {r : ℕ} {A B : Type} [Group A] [Group B]
    (φ : A ≃* B) (Q : Subgroup A) (e : ↥Q ≃* QuaternionGroup (2 ^ (r - 2))) :
    quatInvolution r ((Q.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans e) =
      φ (quatInvolution r e) := by
  simp only [quatInvolution, MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
  exact Subgroup.coe_equivMapOfInjective_apply Q φ.toMonoidHom φ.injective (e.symm _)

theorem piCycConcl_congr {r E : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : PiCycConcl r E B) : PiCycConcl r E A := by
  intro Q e H h2 hN g hg ho
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  let H' : Subgroup (MulAut B) := H.map (MulAut.congr φ).toMonoidHom
  have h2' : IsPGroup 2 ↥H' := IsPGroup.map h2 _
  have hN' : ∀ β ∈ H', ∀ x ∈ Q', β x ∈ Q' := map_equivMap_normalizes φ hN
  have hg' : MulAut.congr φ g ∈ H' := ⟨g, hg, rfl⟩
  have hord : orderOf (MulAut.congr φ g) = orderOf g :=
    MulEquiv.orderOf_eq (MulAut.congr φ) g
  have ho' : 2 ^ E < orderOf (MulAut.congr φ g) := by rwa [hord]
  have hkey := hB Q' e' H' h2' hN' (MulAut.congr φ g) hg' ho'
  have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
    quatInvolution_equivMapOfInjective φ Q e
  apply (MulAut.congr φ).injective
  rw [map_pow, ← hord, hkey, hquat, ← mulAut_congr_conj φ (quatInvolution r e)]

theorem piQuatConcl_congr {r : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : PiQuatConcl r B) : PiQuatConcl r A := by
  intro Q e H h2 hN m hm1 B₀ hB₀ eB
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  let H' : Subgroup (MulAut B) := H.map (MulAut.congr φ).toMonoidHom
  let B₀' : Subgroup (MulAut B) := B₀.map (MulAut.congr φ).toMonoidHom
  let eB' : ↥B₀' ≃* QuaternionGroup (2 ^ m) :=
    (B₀.equivMapOfInjective (MulAut.congr φ).toMonoidHom
      (MulAut.congr φ).injective).symm.trans eB
  have h2' : IsPGroup 2 ↥H' := IsPGroup.map h2 _
  have hN' : ∀ β ∈ H', ∀ x ∈ Q', β x ∈ Q' := map_equivMap_normalizes φ hN
  have hB₀' : B₀' ≤ H' := by
    intro γ hγ
    obtain ⟨γ₀, hγ₀, rfl⟩ := hγ
    exact ⟨γ₀, hB₀ hγ₀, rfl⟩
  have hkey := hB Q' e' H' h2' hN' m hm1 B₀' hB₀' eB'
  have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
    quatInvolution_equivMapOfInjective φ Q e
  have hcoe : ((eB'.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B₀') :
        MulAut B) =
      MulAut.congr φ ((eB.symm (QuaternionGroup.a ((2 ^ m : ℕ) : ZMod (2 * 2 ^ m))) : ↥B₀) :
        MulAut A) := by
    simp only [eB', MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
    exact Subgroup.coe_equivMapOfInjective_apply B₀ (MulAut.congr φ).toMonoidHom
      (MulAut.congr φ).injective (eB.symm _)
  apply (MulAut.congr φ).injective
  rw [← hcoe, hkey, hquat, ← mulAut_congr_conj φ (quatInvolution r e)]

theorem pi4Concl_congr {r : ℕ} {A B : Type} [Group A] [Group B] (φ : A ≃* B)
    (hB : Pi4Concl r B) : Pi4Concl r A := by
  intro Q e H h2 hN g hg K hK ho
  let Q' : Subgroup B := Q.map φ.toMonoidHom
  let ψ : ↥Q ≃* ↥Q' := Q.equivMapOfInjective φ.toMonoidHom φ.injective
  let e' : ↥Q' ≃* QuaternionGroup (2 ^ (r - 2)) := ψ.symm.trans e
  let H' : Subgroup (MulAut B) := H.map (MulAut.congr φ).toMonoidHom
  have h2' : IsPGroup 2 ↥H' := IsPGroup.map h2 _
  have hN' : ∀ β ∈ H', ∀ x ∈ Q', β x ∈ Q' := map_equivMap_normalizes φ hN
  have hg' : MulAut.congr φ g ∈ H' := ⟨g, hg, rfl⟩
  have hord : orderOf (MulAut.congr φ g) = orderOf g :=
    MulEquiv.orderOf_eq (MulAut.congr φ) g
  have ho' : orderOf (MulAut.congr φ g) = 2 ^ K := by rw [hord, ho]
  have hquat : quatInvolution r e' = φ (quatInvolution r e) :=
    quatInvolution_equivMapOfInjective φ Q e
  rcases hB Q' e' H' h2' hN' (MulAut.congr φ g) hg' K hK ho' with h | h
  · left
    apply (MulAut.congr φ).injective
    rw [map_pow, h, hquat, ← mulAut_congr_conj φ (quatInvolution r e)]
  · right
    intro hmem
    apply h
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨φ a, by rw [← mulAut_congr_conj φ a, ha, map_pow]⟩

end Concl

end CFSG.CGT.PushingUpLit.SolKNA.R4.Z2Big

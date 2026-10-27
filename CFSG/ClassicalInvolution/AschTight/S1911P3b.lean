module

public import CFSG.ClassicalInvolution.AschTight.E2StarTargets
public import CFSG.ClassicalInvolution.AschTight.S1911FusB

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77

section Act

variable {Y₀ : Type} [Group Y₀] (Y₁ : Subgroup Y₀)

@[expose] noncomputable def quotAut :
    MulAut ↥Y₁ →* MulAut (↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁) where
  toFun φ := QuotientGroup.congr _ _ φ (CFSG.ComponentClassification.OddCore.equiv_invariant φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

variable [Y₁.Normal]

@[expose] noncomputable def secAct : Y₀ →* MulAut (↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁) :=
  (quotAut Y₁).comp MulAut.conjNormal

theorem secAct_mk (y : Y₀) (x : ↥Y₁) :
    secAct Y₁ y (QuotientGroup.mk x) = QuotientGroup.mk (MulAut.conjNormal y x) := rfl

theorem secAct_of_mem {y : Y₀} (hy : y ∈ Y₁) :
    secAct Y₁ y = MulAut.conj (QuotientGroup.mk (⟨y, hy⟩ : ↥Y₁)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [secAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

end Act

section Lift

theorem exists_pGroup_bijective {H Q : Type} [Group H] [Group Q] [Finite H] (f : H →* Q)
    (hf : Function.Surjective f) (hker : Odd (Nat.card f.ker)) (hQ : IsPGroup 2 Q) :
    ∃ T : Subgroup H, IsPGroup 2 T ∧ Function.Bijective (f.comp T.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 H) := inferInstance
  refine ⟨T, T.isPGroup', ⟨?_, ?_⟩⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    apply Subtype.ext
    exact eq_one_of_isPGroup_of_mem_odd hker (show (x : H) ∈ f.ker from hx)
      (T.isPGroup'.to_le (Subgroup.zpowers_le.mpr x.2))
  · intro q
    have htop : (T.mapSurjective hf : Subgroup Q) = ⊤ :=
      ((T.mapSurjective hf).is_maximal' (hQ.to_subgroup ⊤) le_top).symm
    have hq : q ∈ (T : Subgroup H).map f := by
      rw [← Sylow.coe_mapSurjective hf, htop]
      trivial
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩

end Lift

section LiftFixed

variable {Y₀ : Type} [Group Y₀] [Finite Y₀] (Y₁ : Subgroup Y₀) [Y₁.Normal]

theorem exists_lift_of_fixed {s : Y₀} (hs : s * s = 1) {A : Subgroup Y₀} (hAY : A ≤ Y₁)
    (hsA : s ∈ Subgroup.normalizer (A : Set Y₀))
    {P : Subgroup (↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁)} (hP2 : IsPGroup 2 P)
    (hPA : P ≤ (A.subgroupOf Y₁).map (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₁)))
    (hfix : ∀ x ∈ P, secAct Y₁ s x = x) :
    ∃ Q : Subgroup Y₀, Q ≤ A ∧ (∀ x ∈ Q, s * x = x * s) ∧ IsPGroup 2 Q ∧
      Nonempty (↥Q ≃* ↥P) := by
  have hsY : s ∈ Subgroup.normalizer ((Y₁ : Subgroup Y₀) : Set Y₀) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (inferInstance : Y₁.Normal).conj_mem x hx s
    · intro hx
      have := (inferInstance : Y₁.Normal).conj_mem _ hx s⁻¹
      simpa [mul_assoc] using this
  have hsO : s ∈ Subgroup.normalizer ((oddCoreOf Y₁ : Subgroup Y₀) : Set Y₀) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer hsY
  have hOA : Odd (Nat.card ↥(A ⊓ oddCoreOf Y₁)) :=
    (oddCoreOf_odd_natCard Y₁).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)
  have hsOA : s ∈ Subgroup.normalizer ((A ⊓ oddCoreOf Y₁ : Subgroup Y₀) : Set Y₀) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact and_congr (Subgroup.mem_normalizer_iff.mp hsA x) (Subgroup.mem_normalizer_iff.mp hsO x)
  set g : ↥(A ⊓ Subgroup.centralizer ({s} : Set Y₀)) →* (↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₁)).comp
      (Subgroup.inclusion (inf_le_left.trans hAY)) with hg
  set Q₀ := P.comap g with hQ₀
  set g₀ : ↥Q₀ →* ↥P := (g.comp Q₀.subtype).codRestrict P (fun x => x.2) with hg₀
  have hsurj : Function.Surjective g₀ := by
    rintro ⟨p, hp⟩
    obtain ⟨x, hxA, hxp⟩ := hPA hp
    have hxA' : (x : Y₀) ∈ A := Subgroup.mem_subgroupOf.mp hxA
    have hk : (x : Y₀)⁻¹ * (s * (x : Y₀) * s⁻¹) ∈ A ⊓ oddCoreOf Y₁ := by
      refine Subgroup.mem_inf.mpr
        ⟨A.mul_mem (A.inv_mem hxA') ((Subgroup.mem_normalizer_iff.mp hsA _).mp hxA'), ?_⟩
      rw [mem_oddCoreOf_iff]
      refine ⟨Y₁.mul_mem (Y₁.inv_mem x.2) (MulAut.conjNormal s x).2, ?_⟩
      have e : (⟨(x : Y₀)⁻¹ * (s * (x : Y₀) * s⁻¹), Y₁.mul_mem (Y₁.inv_mem x.2)
          (MulAut.conjNormal s x).2⟩ : ↥Y₁) = x⁻¹ * MulAut.conjNormal s x := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      rw [e, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        ← secAct_mk]
      have h1 : (QuotientGroup.mk x : ↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁) = p := hxp
      rw [h1, hfix p hp, inv_mul_cancel]
    obtain ⟨o, ho, hso⟩ := exists_mul_mem_centralizer_of_odd hOA hs hsOA hk
    have hyA : (x : Y₀) * o ∈ A := A.mul_mem hxA' ho.1
    have hyC : (x : Y₀) * o ∈ Subgroup.centralizer ({s} : Set Y₀) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (x : Y₀) * o * s = s * ((x : Y₀) * o) * s⁻¹ * s := by rw [hso]
        _ = s * ((x : Y₀) * o) := by group
    have hgy : g ⟨(x : Y₀) * o, hyA, hyC⟩ = p := by
      obtain ⟨hoY, hoO⟩ := mem_oddCoreOf_iff.mp ho.2
      have e : (Subgroup.inclusion (inf_le_left.trans hAY) ⟨(x : Y₀) * o, hyA, hyC⟩ : ↥Y₁) =
          x * ⟨o, hoY⟩ := rfl
      have h0 : (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y₁)) (⟨o, hoY⟩ : ↥Y₁) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hoO
      rw [hg, MonoidHom.comp_apply, e, map_mul, h0, mul_one]
      exact hxp
    exact ⟨⟨⟨(x : Y₀) * o, hyA, hyC⟩, show g _ ∈ P from hgy ▸ hp⟩, Subtype.ext hgy⟩
  have hker : Odd (Nat.card g₀.ker) := by
    have hle : (g₀.ker.map ((A ⊓ Subgroup.centralizer ({s} : Set Y₀)).subtype.comp
        Q₀.subtype)) ≤ oddCoreOf Y₁ := by
      rintro _ ⟨y, hy, rfl⟩
      have hy1 : g₀ y = 1 := hy
      have hy2 : g (y : ↥(A ⊓ Subgroup.centralizer ({s} : Set Y₀))) = 1 :=
        congrArg Subtype.val hy1
      rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy2
      exact mem_oddCoreOf_iff.mpr ⟨_, hy2⟩
    have hinj : Function.Injective ((A ⊓ Subgroup.centralizer ({s} : Set Y₀)).subtype.comp
        Q₀.subtype) :=
      (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
    rw [Nat.card_congr (Subgroup.equivMapOfInjective g₀.ker _ hinj).toEquiv]
    exact (oddCoreOf_odd_natCard Y₁).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  obtain ⟨T, hT2, hTbij⟩ := exists_pGroup_bijective g₀ hsurj hker hP2
  refine ⟨(T.map Q₀.subtype).map (A ⊓ Subgroup.centralizer ({s} : Set Y₀)).subtype, ?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans inf_le_left
  · rintro _ ⟨y, -, rfl⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp y.2.2).symm
  · exact (hT2.map Q₀.subtype).map _
  · exact ⟨((Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm.trans
      (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm).trans
        (MulEquiv.ofBijective _ hTbij)⟩

end LiftFixed

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

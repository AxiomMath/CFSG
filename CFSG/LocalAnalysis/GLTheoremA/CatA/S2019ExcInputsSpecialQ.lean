module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3Heis
import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
import CFSG.RankThree.PartOne.S9.OddCore.TorsionBridge
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open scoped commutatorElement

@[expose] def IsS2019SpecialQ (q Q : ℕ) (H : Type*) [Group H] : Prop :=
  IsPGroup q H ∧ (∀ x : H, x ^ q = 1) ∧ Nat.card H = Q ^ 3 ∧
    Nat.card (Subgroup.center H) = Q ∧
    ∀ (Z : Subgroup H) [Z.Normal], Z ≤ Subgroup.center H → Z.relIndex (Subgroup.center H) = q →
      CFSG.IsExtraspecialPGroup q (H ⧸ Z)

section Transport

variable {H H' : Type*} [Group H] [Group H']

theorem IsS2019SpecialQ.of_mulEquiv {q Q : ℕ} (e : H ≃* H') (h : IsS2019SpecialQ q Q H) :
    IsS2019SpecialQ q Q H' := by
  obtain ⟨hp, hexp, hcard, hZ, hext⟩ := h
  have hcen := CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3.map_center_mulEquiv e
  refine ⟨hp.of_equiv e, fun y => ?_, ?_, ?_, fun Z' _ hZ' hidx => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_pow, hexp, map_one]
  · rw [← hcard]
    exact (Nat.card_congr e.toEquiv).symm
  · rw [← hcen, Subgroup.card_map_of_injective e.injective, hZ]
  · set Z := Z'.comap e.toMonoidHom with hZdef
    have hZmap : Z.map e.toMonoidHom = Z' :=
      Subgroup.map_comap_eq_self_of_surjective e.surjective Z'
    have hZle : Z ≤ Subgroup.center H := by
      intro z hz
      have h1 : e z ∈ Subgroup.center H' := hZ' hz
      rw [← hcen] at h1
      obtain ⟨w, hw, hwz⟩ := h1
      rwa [e.injective hwz] at hw
    have hidx' : Z.relIndex (Subgroup.center H) = q := by
      rw [hZdef, Subgroup.relIndex_comap, hcen, hidx]
    have := hext Z hZle hidx'
    exact CFSG.RankThree.PartOne.Torsion37.isExtraspecialPGroup_of_mulEquiv
      (QuotientGroup.congr Z Z' e hZmap) this

theorem exists_subgroup_of_injective {Y : Type*} [Group Y] {q Q : ℕ} (φ : H →* Y)
    (hφ : Function.Injective φ) (h : IsS2019SpecialQ q Q H) :
    ∃ R : Subgroup Y, IsPGroup q R ∧ (∀ r ∈ R, r ^ q = 1) ∧ Nat.card R = Q ^ 3 ∧
      Nat.card (Subgroup.center ↥R) = Q ∧
      ∀ (Z : Subgroup ↥R) [Z.Normal], Z ≤ Subgroup.center ↥R →
        Z.relIndex (Subgroup.center ↥R) = q → CFSG.IsExtraspecialPGroup q (↥R ⧸ Z) := by
  obtain ⟨hp, hexp, hcard, hZ, hext⟩ := h.of_mulEquiv (MonoidHom.ofInjective hφ)
  refine ⟨φ.range, hp, fun r hr => ?_, hcard, hZ, hext⟩
  have := hexp ⟨r, hr⟩
  exact congrArg Subtype.val this

end Transport

@[expose] def HasS2019SpecialQ (q Q : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ (H : Type) (_ : Group H), IsS2019SpecialQ q Q H ∧ ∃ φ : H →* Y, Function.Injective φ

namespace HasS2019SpecialQ

variable {q Q : ℕ} {Y Y' : Type} [Group Y] [Group Y']

theorem exists_subgroup (h : HasS2019SpecialQ q Q Y) :
    ∃ R : Subgroup Y, IsPGroup q R ∧ (∀ r ∈ R, r ^ q = 1) ∧ Nat.card R = Q ^ 3 ∧
      Nat.card (Subgroup.center ↥R) = Q ∧
      ∀ (Z : Subgroup ↥R) [Z.Normal], Z ≤ Subgroup.center ↥R →
        Z.relIndex (Subgroup.center ↥R) = q → CFSG.IsExtraspecialPGroup q (↥R ⧸ Z) := by
  obtain ⟨H, _, hH, φ, hφ⟩ := h
  exact exists_subgroup_of_injective φ hφ hH

theorem of_injective (h : HasS2019SpecialQ q Q Y) (ψ : Y →* Y') (hψ : Function.Injective ψ) :
    HasS2019SpecialQ q Q Y' := by
  obtain ⟨H, _, hH, φ, hφ⟩ := h
  exact ⟨H, inferInstance, hH, ψ.comp φ, hψ.comp hφ⟩

theorem of_mulEquiv (h : HasS2019SpecialQ q Q Y) (e : Y ≃* Y') : HasS2019SpecialQ q Q Y' :=
  h.of_injective e.toMonoidHom e.injective

end HasS2019SpecialQ

section Projective

open CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}

theorem injective_mk_comp {X : Type*} [Group X] (ψ : X →* H)
    (hψ : ∀ x (c : K), (((ψ x : H) : GL ι K) : Matrix ι ι K) = Matrix.scalar ι c → x = 1) :
    Function.Injective ((QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)).comp ψ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨c, hc⟩ := hx
  exact hψ x c (by rw [← hc, Matrix.GeneralLinearGroup.coe_scalar])

theorem eq_one_of_coe_eq_scalar {X : Type*} [Group X] (ψ : X →* H) (hψ : Function.Injective ψ)
    (i : ι) (hi : ∀ x, (((ψ x : H) : GL ι K) : Matrix ι ι K) i i = 1) (x : X) (c : K)
    (hx : (((ψ x : H) : GL ι K) : Matrix ι ι K) = Matrix.scalar ι c) : x = 1 := by
  have hc : c = 1 := by
    have := hi x
    rwa [hx, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
  apply hψ
  rw [map_one]
  apply Subtype.ext
  apply Units.ext
  rw [hx, hc, map_one, Subgroup.coe_one, Units.val_one]

theorem hasS2019SpecialQ_statedProj {X : Type} [Group X] {q Q : ℕ} (hX : IsS2019SpecialQ q Q X)
    (ψ : X →* H)
    (hψ : ∀ x (c : K), (((ψ x : H) : GL ι K) : Matrix ι ι K) = Matrix.scalar ι c → x = 1) :
    HasS2019SpecialQ q Q (StatedProj H) :=
  ⟨X, inferInstance, hX, _, injective_mk_comp ψ hψ⟩

end Projective

section Quotient

variable {H : Type} [Group H] [Finite H]

theorem isExtraspecialPGroup_quotient_of_commutator_surjective {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) (hexp : ∀ x : H, x ^ p = 1)
    (hcomm : commutator H = Subgroup.center H)
    (hsurj : ∀ x : H, x ∉ Subgroup.center H → ∀ z ∈ Subgroup.center H, ∃ y : H, ⁅x, y⁆ = z)
    (Z : Subgroup H) [Z.Normal] (hZ : Z ≤ Subgroup.center H)
    (hidx : Z.relIndex (Subgroup.center H) = p) : CFSG.IsExtraspecialPGroup p (H ⧸ Z) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' Z with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hcen : Subgroup.center (H ⧸ Z) = (Subgroup.center H).map π := by
    apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := hπs y
      by_contra hx
      have hxZ : x ∉ Subgroup.center H := fun h => hx ⟨x, h, rfl⟩
      obtain ⟨z, hzC, hzZ⟩ : ∃ z ∈ Subgroup.center H, z ∉ Z := by
        by_contra hall
        push Not at hall
        have hle : Subgroup.center H ≤ Z := fun z hz => hall z hz
        have h1 : Z.relIndex (Subgroup.center H) = 1 := Subgroup.relIndex_eq_one.mpr hle
        rw [hidx] at h1
        exact hp.one_lt.ne' h1
      obtain ⟨g, hg⟩ := hsurj x hxZ z hzC
      apply hzZ
      have h1 := Subgroup.mem_center_iff.1 hy (π g)
      have h2 : π ⁅x, g⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact h1.symm
      rw [← hg]
      exact (QuotientGroup.eq_one_iff _).1 h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := hπs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
  have hpq : IsPGroup p (H ⧸ Z) := hH.to_quotient Z
  have hcomm' : commutator (H ⧸ Z) = Subgroup.center (H ⧸ Z) := by
    rw [hcen, ← hcomm, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hπs]
  have hexp' : ∀ y : H ⧸ Z, y ^ p = 1 := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    rw [← map_pow, hexp, map_one]
  have hfrat : frattini (H ⧸ Z) = Subgroup.center (H ⧸ Z) := by
    rw [CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3.frattini_eq_commutator_of_exponent hp hpq hexp',
      hcomm']
  refine ⟨hpq, hcomm', hfrat, ?_⟩
  rw [hcen, ← hidx]
  have hker : (π.comp (Subgroup.center H).subtype).ker =
      Z.subgroupOf (Subgroup.center H) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_subtype,
      hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : (π.comp (Subgroup.center H).subtype).range = (Subgroup.center H).map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv, hker]
  rfl

end Quotient

section Heisenberg

open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 CFSG.GH74.GLS.IVK.Proofs2.Lemma41dU3
open CFSG.LocalAnalysis.ComponentInitial

theorem isS2019SpecialQ_heis {F : Type} [Field F] [Finite F] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    [CharP F q] : IsS2019SpecialQ q (Nat.card F) (Heis F) := by
  have hexp : ∀ x : Heis F, x ^ q = 1 := Heis.pow_prime_eq_one hq hq2
  have hpg : IsPGroup q (Heis F) := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  haveI : Finite (Heis F) := Finite.of_equiv _ Heis.equivProd.symm
  refine ⟨hpg, hexp, Heis.card_eq, Heis.card_center, fun Z _ hZ hidx => ?_⟩
  refine isExtraspecialPGroup_quotient_of_commutator_surjective hq hpg hexp
    (by rw [_root_.commutator_def]; exact Heis.commutator_eq_center) ?_ Z hZ hidx
  intro x hx z hz
  rw [Heis.mem_center] at hx hz
  by_cases ha : x.a = 0
  · have hb : x.b ≠ 0 := fun hb => hx ⟨ha, hb⟩
    refine ⟨⟨-(z.c / x.b), 0, 0⟩, ?_⟩
    rw [Heis.commutator_eq]
    ext
    · exact hz.1.symm
    · exact hz.2.symm
    · simp only [ha, zero_mul, zero_sub]
      field_simp
  · refine ⟨⟨0, z.c / x.a, 0⟩, ?_⟩
    rw [Heis.commutator_eq]
    ext
    · exact hz.1.symm
    · exact hz.2.symm
    · simp only [zero_mul, sub_zero]
      field_simp

theorem isS2019SpecialQ_uheis {q f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData q f K)
    (hq2 : q ≠ 2) : IsS2019SpecialQ q (q ^ f) (UHeis h) := by
  have hexp : ∀ x : UHeis h, x ^ q = 1 := UHeis.pow_prime_eq_one hq2
  have hpg : IsPGroup q (UHeis h) := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  refine ⟨hpg, hexp, UHeis.card_eq h, UHeis.card_center h, fun Z _ hZ hidx => ?_⟩
  refine isExtraspecialPGroup_quotient_of_commutator_surjective h.prime hpg hexp
    (by rw [_root_.commutator_def]; exact UHeis.commutator_eq_center) ?_ Z hZ hidx
  intro x hx z hz
  rw [UHeis.mem_center] at hx hz
  have hbx : h.bar x.a ≠ 0 := (map_ne_zero h.bar).2 hx
  have hN0 : x.a * h.bar x.a ≠ 0 := mul_ne_zero hx hbx
  have hbarN : h.bar (x.a * h.bar x.a) = x.a * h.bar x.a := by
    rw [map_mul, h.bar_bar, mul_comm]
  have hzc : z.c + h.bar z.c = 0 := by
    have := z.hc
    rw [hz] at this
    simpa using this
  have hw : z.c / (x.a * h.bar x.a) ∈ h.barSub.range := by
    rw [h.range_barSub, UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_div₀, hbarN,
      ← add_div, hzc, zero_div]
  obtain ⟨t, ht⟩ := hw
  rw [UnitaryFieldData.barSub_apply] at ht
  obtain ⟨c, hc⟩ := UHeis.exists_c (h := h) (-(x.a * t))
  refine ⟨⟨-(x.a * t), c, hc⟩, ?_⟩
  ext
  · rw [UHeis.commutator_a, hz]
  · rw [UHeis.commutator_c]
    have hz' : z.c = x.a * h.bar x.a * (h.bar t - t) := by
      rw [ht]
      field_simp
    simp only [map_neg, map_mul]
    rw [hz']
    ring

theorem hasS2019SpecialQ_quotient_center_of_sl3 {G : Type} [Group G] {F : Type} [Field F]
    [Finite F] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) [CharP F q]
    (ρ : Matrix.SpecialLinearGroup (Fin 3) F →* G) (hρ : Function.Injective ρ) :
    HasS2019SpecialQ q (Nat.card F) (G ⧸ Subgroup.center G) := by
  refine ⟨Heis F, inferInstance, isS2019SpecialQ_heis hq hq2,
    (QuotientGroup.mk' _).comp (ρ.comp heisSL), ?_⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    MonoidHom.comp_apply] at hx
  have hc : heisSL x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hρ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hx (ρ g)
  have h := Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hc 0
  rw [coe_heisSL] at h
  have h00 : heisMat x 0 0 = 1 := by simp [heisMat]
  rw [h00] at h
  have ha := congrFun (congrFun h 0) 1
  have hb := congrFun (congrFun h 1) 2
  have hc' := congrFun (congrFun h 0) 2
  simp [heisMat] at ha hb hc'
  ext
  · exact ha.symm
  · exact hb.symm
  · exact hc'.symm

end Heisenberg

end CFSG.LocalAnalysis.GLTheoremA.S2019

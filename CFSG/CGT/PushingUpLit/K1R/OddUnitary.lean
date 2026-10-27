module

public import CFSG.CGT.PushingUpLit.K1R.OddConfig
public import CFSG.LocalAnalysis.SteinbergSFOddUnitaryFixedRootSelector

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup Module CFSG.Assembly.LowTwoRank CFSG.Blueprint OddClassicalRankOne
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBUnitaryB
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.SymplecticFourStandard
open CFSG.LocalAnalysis.SymplecticFourStandard.OddUnitaryRoot
open CFSG.CGT.PushingUpLit.K1R (NoFourConfig)

namespace OddUnitaryInner

section Lift

open CatalogueBFixedCentralQuotient

theorem exists_fixed_root_lift_weak {U : Type*} [Group U] [Finite U] (Z : Subgroup U) [Z.Normal]
    (hZ : Z ≤ center U) (φ : MulAut U) (hφZ : Z.map φ.toMonoidHom = Z)
    (hφφ : ∀ g, φ (φ g) = g) {P : Type*} [Group P] (β : MulAut P) (ι : P →* U ⧸ Z)
    (hι : Function.Injective ι) (hιβ : ∀ y, ι (β y) = onQuotient Z φ hφZ (ι y))
    (hN : (ι.range.subgroupOf (fixedSubgroup (onQuotient Z φ hφZ))).Normal)
    {K : Type*} [Field K] (h : NoFourConfig β K) :
    ∃ Y : Subgroup U, CFSG.Assembly.IsComponentOf Y (fixedSubgroup φ) ∧
      ∃ (A : Subgroup Y) (_ : A.Normal), (∀ a ∈ A, (a : U) ∈ Z) ∧
        Nonempty (Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  set β' := onQuotient Z φ hφZ with hβ'
  obtain ⟨S, hSn, hSs, hSnab, ⟨eS⟩, -⟩ := h
  set X := S.map (fixedSubgroup β).subtype with hXdef
  have hX : CFSG.Assembly.IsComponentOf X (fixedSubgroup β) :=
    isComponentOf_map_subtype S hSn hSs hSnab
  have hmap : (fixedSubgroup β).map ι = ι.range ⊓ fixedSubgroup β' := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change β' (ι y) = ι y
      rw [← hιβ]
      exact congrArg ι hy
    · rintro ⟨⟨y, rfl⟩, hz⟩
      refine ⟨y, ?_, rfl⟩
      change β y = y
      apply hι
      rw [hιβ]
      exact hz
  have hX₁ := SymmetricLocal.isComponentOf_map_of_injective ι hι hX
  rw [hmap] at hX₁
  have hX₂ : CFSG.Assembly.IsComponentOf (X.map ι) (fixedSubgroup β') :=
    OddClassSelector.isComponentOf_of_normal_le hX₁ inf_le_right (by
      rw [Subgroup.inf_subgroupOf_right]
      exact hN)
  obtain ⟨Y, hY, ⟨σY, hσYs, -, hσY⟩, -⟩ := OddClassSelector.central_lift Z hZ φ hφZ hφφ hX₂
  refine ⟨Y, hY, ⟨σY.ker, inferInstance, fun a ha => ?_, ⟨?_⟩⟩⟩
  · have h1 : QuotientGroup.mk' Z (a : U) = 1 := by
      rw [← hσY a, MonoidHom.mem_ker.mp ha]
      rfl
    exact (QuotientGroup.eq_one_iff _).mp h1
  · exact (QuotientGroup.quotientKerEquivOfSurjective σY hσYs).trans
      ((X.equivMapOfInjective ι hι).symm.trans
        ((S.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eS))

end Lift

section Model

open Matrix

variable {p f : ℕ} {E : Type} [Field E] {r ε : ℕ}

theorem hyperbolic_inner_false (h : UnitaryFieldData p f E) (hp : p ≠ 2) (hr : 1 ≤ r)
    (hε : ε ≤ 1) (hn : 3 ≤ 2 * r + ε) {K : Type*} [Field K] {n : ℕ} (hn2 : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (β : MulAut (hypPSU h r ε)) (hβ : orderOf β = 2)
    (hcfg : NoFourConfig β K) (A : GL (HypIndex r ε) E) (σ : E ≃+* E)
    (hx : (⟨A, σ⟩ : SemiGL (HypIndex r ε) E) ∈ semilinearSimilitudes h r ε)
    (hσ1 : σ = RingEquiv.refl E) (hA : A ∈ hypUnitary h r ε)
    (hβA : semilinearAutHom h hr hε ⟨_, hx⟩ = β) : False := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  have hdim : finrank E (HypIndex r ε → E) = 2 * r + ε := UnitaryHigher.finrank_hypIndex_fun
  have hsq : semilinearAutHom h hr hε (⟨⟨A, σ⟩, hx⟩ * ⟨⟨A, σ⟩, hx⟩) = 1 := by
    rw [map_mul, hβA, ← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hβ])
  obtain ⟨hσσ, c, hc⟩ := (semilinearAutHom_eq_one_iff h hr hε hn _).mp hsq
  change σ * σ = RingEquiv.refl E at hσσ
  change A * glAut σ A = GeneralLinearGroup.scalar (HypIndex r ε) c at hc
  let ι : hypPSU h r ε →* sesqProjUnitary h (hypForm h r ε) :=
    (projSpecial h (hypForm h r ε)).subtype.comp (hypModelEquiv h).toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp (hypModelEquiv h).injective
  have hιr : ι.range = projSpecial h (hypForm h r ε) := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (hypModelEquiv h).surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have happly : ∀ g : hypSU h r ε,
      β (hypProj h r ε g) = hypProj h r ε ⟨_, conj_mem_hypSU hx g⟩ := by
    intro g
    rw [← hβA]
    exact semilinearAutHom_apply h hr hε _ g
  have hZc := sesqNormOneScalars_le_center h (hypForm h r ε)
  subst hσ1
  exfalso
  have hAA : A * A = GeneralLinearGroup.scalar (HypIndex r ε) c := by
    have h1 : glAut (RingEquiv.refl E) A = A :=
      congrArg (fun φ : MulAut (GL (HypIndex r ε) E) => φ A) (map_one glAut)
    rwa [h1] at hc
  have hcN : h.norm (c : E) = 1 := by
    have hU := mul_mem hA hA
    rw [hAA, mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram] at hU
    have h2 := congrFun (congrFun hU (.inl ⟨0, hr⟩)) (hypPartner (.inl ⟨0, hr⟩))
    simpa [hypGram_apply] using h2
  have hAord : orderOf (QuotientGroup.mk ⟨A, hA⟩ : hypUnitaryMod h r ε) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, pow_two]
      exact ⟨c, hcN, pow_zero c, by rw [Subgroup.coe_mul, hAA]⟩
    · intro h1
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨c', -, -, hc'⟩ := h1
      have hΦ1 := (semilinearAutHom_eq_one_iff h hr hε hn ⟨⟨A, RingEquiv.refl E⟩, hx⟩).mpr
        ⟨rfl, c', hc'⟩
      rw [hβA] at hΦ1
      rw [hΦ1, orderOf_one] at hβ
      exact absurd hβ (by norm_num)
  set T : sesqUnitaryGroup (hypForm h r ε) := hypUnitaryEquiv h ⟨A, hA⟩ with hTdef
  have hT : orderOf (QuotientGroup.mk T : sesqProjUnitary h (hypForm h r ε)) = 2 := by
    rw [hTdef, ← hypUnitaryModEquiv_mk, MulEquiv.orderOf_eq]
    exact hAord
  have he : ∀ y, ι (β y) =
      MulAut.conj (QuotientGroup.mk' (sesqNormOneScalars h (hypForm h r ε)) T) (ι y) := by
    intro y
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε y
    rw [happly]
    refine hypModelEquiv_conj h ⟨A, hA⟩ g _ ?_
    have hg : glAut (RingEquiv.refl E) (g : GL (HypIndex r ε) E) =
        (g : GL (HypIndex r ε) E) :=
      congrArg (fun φ : MulAut (GL (HypIndex r ε) E) => φ (g : GL (HypIndex r ε) E))
        (map_one glAut)
    change A * glAut (RingEquiv.refl E) (g : GL (HypIndex r ε) E) * A⁻¹ = _
    rw [hg]
  have hφZ := OddClassSelector.map_conj_eq_of_le_center hZc T
  rw [← OddClassSelector.onQuotient_conj T hφZ] at he
  have hTT : T * T ∈ center (sesqUnitaryGroup (hypForm h r ε)) := by
    apply hZc
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, ← pow_two, ← hT,
      pow_orderOf_eq_one]
  have hφφ : ∀ g, MulAut.conj T (MulAut.conj T g) = g := by
    intro g
    rw [MulAut.conj_apply, MulAut.conj_apply]
    have h1 := mem_center_iff.mp hTT g
    calc T * (T * g * T⁻¹) * T⁻¹ = (T * T) * g * (T * T)⁻¹ := by group
      _ = g := by rw [← h1, mul_inv_cancel_right]
  obtain ⟨Y, hY, ⟨Ak, _, hAZ, ⟨eQ⟩⟩⟩ := exists_fixed_root_lift_weak _ hZc _ hφZ hφφ β ι hι
    he (by rw [hιr]; exact (projSpecial_normal h _).subgroupOf _) hcfg
  rw [CatalogueBUnitaryB.fixedSubgroup_conj] at hY
  exact inner_case_false h hp (by rw [hdim]; omega) (hypForm_isSymm h)
    (hypForm_separatingLeft h) hT hY Ak hAZ hn2 hK eQ

end Model

theorem odd_unitary_inner_false (K : Type) [Field K] [Fintype K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Fintype.card K = 2 ^ n) {D : Type} [Group D] (α : MulAut D) (hα : orderOf α = 2)
    (hin : α ∈ (MulAut.conj : D →* MulAut D).range) (hcfg : NoFourConfig α K) (d p f : ℕ)
    (hp : p ≠ 2) (hM : StatedClassicalModel D .PSU d p f) : False := by
  classical
  obtain ⟨⟨hprime, hf, hd3, -⟩, E₀, _, _, hE₀, ⟨e⟩⟩ := hM
  have hud : UnitaryFieldData p f E₀ := ⟨hprime, hf, by rw [hE₀, ← pow_mul, mul_comm]⟩
  obtain ⟨r, ε, hr, hε, rfl⟩ : ∃ r ε, 1 ≤ r ∧ ε ≤ 1 ∧ d = 2 * r + ε :=
    ⟨d / 2, d % 2, by omega, by omega, by omega⟩
  obtain ⟨R, hR⟩ := (unitary_hyperbolic_model_transport hud hr hε).1
  let θ : D ≃* hypPSU hud r ε := e.trans (hypPSUEquivStatedProj hud hR (by omega)).symm
  obtain ⟨g, hg⟩ := hin
  obtain ⟨s, hs⟩ := hypProj_surjective hud r ε (θ g)
  have hxs := inl_mem_semilinearSimilitudes (h := hud) s
  have hsU : (s : GL (HypIndex r ε) E₀) ∈ hypUnitary hud r ε := (mem_gramSU.mp s.2).1
  have hΦ : semilinearAutHom hud hr hε ⟨_, hxs⟩ = MulAut.congr θ α := by
    refine MulEquiv.ext fun y => ?_
    obtain ⟨x, rfl⟩ := hypProj_surjective hud r ε y
    rw [semilinearAutHom_apply, ← hg]
    change _ = θ (MulAut.conj g (θ.symm (hypProj hud r ε x)))
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, ← hs,
      ← map_mul, ← map_inv, ← map_mul]
    congr 1
  exact hyperbolic_inner_false hud hp hr hε (by omega) hn (by rw [Nat.card_eq_fintype_card, hK])
    (MulAut.congr θ α) (by rw [MulEquiv.orderOf_eq]; exact hα)
    (hcfg.of_mulEquiv θ fun x => by
      change θ (α x) = θ (α (θ.symm (θ x)))
      rw [MulEquiv.symm_apply_apply]) (s : GL (HypIndex r ε) E₀) 1 hxs rfl hsU hΦ

end OddUnitaryInner

end CFSG.LocalAnalysis.EvenBN.GMSK

namespace CFSG.CGT.PushingUpLit.K1R

open CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.LocalAnalysis.EvenBN.GMSK.OddClassicalRankOne

theorem innerKernelSelector_oddUnitary :
    InnerKernelSelector fun D _ => ∃ d p f : ℕ, p ≠ 2 ∧ LieModel D .PSU d p f := by
  refine InnerKernelSelector.of_false ?_
  intro D _ _ _ ⟨d, p, f, hp, hM⟩ n hn K _ _ hK α hα hin S hSα hSn hSK hnf
  exact OddUnitaryInner.odd_unitary_inner_false K hn hK α hα hin
    (noFourConfig_of_data hn hK hSα hSn hSK hnf) d p f hp
    (statedClassicalModel_of_lieModel (by decide) hM)

end CFSG.CGT.PushingUpLit.K1R

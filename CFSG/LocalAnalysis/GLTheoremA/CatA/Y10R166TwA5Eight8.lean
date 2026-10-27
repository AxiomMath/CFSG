module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SUBlocks4
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Eight4
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

namespace TwA5Eight

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.SeitzReduction.UnitaryPilot
open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def twA5Omega : rootsOfUnity 3 F :=
  ⟨(twA5Lambda (F := F) : Fˣ) ^ 3, by
    rw [mem_rootsOfUnity]
    rw [← pow_mul]
    exact twA5Lambda_pow_nine (F := F)⟩

theorem twA5Omega_pow_three : (twA5Omega (F := F) : Fˣ) ^ 3 = 1 :=
  (mem_rootsOfUnity (M := F) 3 (twA5Omega (F := F) : Fˣ)).mp (twA5Omega (F := F)).2

theorem twA5Omega_val_pow_three : ((twA5Omega (F := F) : Fˣ) : F) ^ 3 = 1 :=
  coe_pow_eq_one (twA5Omega_pow_three (F := F))

theorem twA5Omega_norm (h : UnitaryFieldData 2 3 F) :
    h.norm ((twA5Omega (F := F) : Fˣ) : F) = 1 :=
  norm_eq_one_of_pow_three h (twA5Omega_val_pow_three (F := F))

theorem twA5Omega_inv_mul_self :
    (((twA5Omega (F := F) : Fˣ) : F) * ((twA5Omega (F := F) : Fˣ) : F))⁻¹ =
      ((twA5Omega (F := F) : Fˣ) : F) := by
  apply inv_eq_of_mul_eq_one_right
  calc ((twA5Omega (F := F) : Fˣ) : F) * ((twA5Omega (F := F) : Fˣ) : F) *
        ((twA5Omega (F := F) : Fˣ) : F) =
      ((twA5Omega (F := F) : Fˣ) : F) ^ 3 := by ring
    _ = 1 := twA5Omega_val_pow_three (F := F)

theorem twA5Omega_inv_mul_inv :
    (((twA5Omega (F := F) : Fˣ) : F))⁻¹ * (((twA5Omega (F := F) : Fˣ) : F))⁻¹ =
      ((twA5Omega (F := F) : Fˣ) : F) := by
  rw [← mul_inv, twA5Omega_inv_mul_self]

theorem twA5Omega_ne_one (h : UnitaryFieldData 2 3 F) :
    (twA5Omega (F := F) : Fˣ) ≠ 1 := by
  intro h1
  have h3 : ((twA5Lambda (F := F) : Fˣ)) ^ 3 = 1 := h1
  have hdvd := orderOf_dvd_of_pow_eq_one h3
  have hord : orderOf ((twA5Lambda (F := F) : Fˣ)) = 9 := by
    rw [Subgroup.orderOf_coe, orderOf_twA5Lambda h]
  rw [hord] at hdvd
  norm_num at hdvd

variable (h : UnitaryFieldData 2 3 F)

@[expose] noncomputable def twA5EParam (n : rootsOfUnity 9 F) (p q : rootsOfUnity 3 F) :
    twA5Param (F := F) :=
  ⟨((n : Fˣ), (p : Fˣ), (q : Fˣ), (p : Fˣ) * (q : Fˣ)), by
    rw [mem_twA5Param]
    refine ⟨(mem_rootsOfUnity (M := F) 9 (n : Fˣ)).mp n.2,
      (mem_rootsOfUnity (M := F) 3 (p : Fˣ)).mp p.2,
      (mem_rootsOfUnity (M := F) 3 (q : Fˣ)).mp q.2, ?_⟩
    rw [mul_pow, (mem_rootsOfUnity (M := F) 3 (p : Fˣ)).mp p.2,
      (mem_rootsOfUnity (M := F) 3 (q : Fˣ)).mp q.2, mul_one]⟩

theorem twA5EParam_mul (n n' : rootsOfUnity 9 F) (p p' q q' : rootsOfUnity 3 F) :
    twA5EParam (F := F) n p q * twA5EParam (F := F) n' p' q' =
      twA5EParam (F := F) (n * n') (p * p') (q * q') := by
  apply Subtype.ext
  ext <;> simp [twA5EParam, mul_mul_mul_comm]

@[expose] noncomputable def twA5EParamHom :
    (rootsOfUnity 9 F × (rootsOfUnity 3 F × rootsOfUnity 3 F)) →* twA5Param (F := F) where
  toFun x := twA5EParam (F := F) x.1 x.2.1 x.2.2
  map_one' := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    show ((1 : Fˣ) * (1 : Fˣ)) = 1
    rw [mul_one]
  map_mul' x y := (twA5EParam_mul (F := F) x.1 y.1 x.2.1 y.2.1 x.2.2 y.2.2).symm

@[expose] noncomputable def twA5EHom :
    (rootsOfUnity 9 F × (rootsOfUnity 3 F × rootsOfUnity 3 F)) →* unitaryPSU h 6 :=
  (unitaryProj h 6).comp ((twA5Hom h).comp (twA5EParamHom (F := F)))

theorem twA5EHom_apply (x : rootsOfUnity 9 F × (rootsOfUnity 3 F × rootsOfUnity 3 F)) :
    twA5EHom h x = unitaryProj h 6 (twA5Hom h (twA5EParamHom (F := F) x)) := rfl

theorem coe_twA5Hom_EParam (n : rootsOfUnity 9 F) (p q : rootsOfUnity 3 F) :
    ((twA5Hom h (twA5EParam (F := F) n p q) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) =
      diagonal (twA5Entries (F := F) (n : Fˣ) (p : Fˣ) (q : Fˣ)
        ((p : Fˣ) * (q : Fˣ))) := by
  rw [twA5Hom_apply]
  unfold twA5Diag twA5EParam
  rw [coe_diagSU]

@[expose] noncomputable def twA5JParam (p q : rootsOfUnity 3 F) : twA5Param (F := F) :=
  ⟨((1 : Fˣ), (p : Fˣ), (q : Fˣ), ((p : Fˣ) * (q : Fˣ))⁻¹), by
    rw [mem_twA5Param]
    refine ⟨by simp, (mem_rootsOfUnity (M := F) 3 (p : Fˣ)).mp p.2,
      (mem_rootsOfUnity (M := F) 3 (q : Fˣ)).mp q.2, ?_⟩
    rw [inv_pow, mul_pow, (mem_rootsOfUnity (M := F) 3 (p : Fˣ)).mp p.2,
      (mem_rootsOfUnity (M := F) 3 (q : Fˣ)).mp q.2, mul_one, inv_one]⟩

theorem twA5JParam_mul (p p' q q' : rootsOfUnity 3 F) :
    twA5JParam (F := F) p q * twA5JParam (F := F) p' q' =
      twA5JParam (F := F) (p * p') (q * q') := by
  apply Subtype.ext
  ext <;> simp [twA5JParam, mul_inv]
  group

@[expose] noncomputable def twA5JParamHom :
    (rootsOfUnity 3 F × rootsOfUnity 3 F) →* twA5Param (F := F) where
  toFun x := twA5JParam (F := F) x.1 x.2
  map_one' := by
    apply Subtype.ext
    unfold twA5JParam
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    show ((1 : Fˣ) * (1 : Fˣ))⁻¹ = 1
    rw [mul_one, inv_one]
  map_mul' x y := (twA5JParam_mul (F := F) x.1 y.1 x.2 y.2).symm

@[expose] noncomputable def twA5JHom :
    (rootsOfUnity 3 F × rootsOfUnity 3 F) →* unitaryPSU h 6 :=
  (unitaryProj h 6).comp ((twA5Hom h).comp (twA5JParamHom (F := F)))

theorem twA5JHom_apply (p q : rootsOfUnity 3 F) :
    twA5JHom h (p, q) = unitaryProj h 6 (twA5Hom h (twA5JParam (F := F) p q)) := rfl

theorem coe_twA5Hom_JParam (p q : rootsOfUnity 3 F) :
    ((twA5Hom h (twA5JParam (F := F) p q) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) =
      diagonal (twA5Entries (F := F) (1 : Fˣ) (p : Fˣ) (q : Fˣ)
        (((p : Fˣ) * (q : Fˣ))⁻¹)) := by
  rw [twA5Hom_apply]
  unfold twA5Diag twA5JParam
  rw [coe_diagSU]

theorem twA5JHom_eq_one_iff {p q : rootsOfUnity 3 F} :
    twA5JHom h (p, q) = 1 ↔ (p : Fˣ) = 1 ∧ (q : Fˣ) = 1 := by
  constructor
  · intro h1
    have h1' : unitaryProj h 6 (twA5Hom h (twA5JParam (F := F) p q)) = 1 := h1
    have hmem : twA5Hom h (twA5JParam (F := F) p q) ∈ unitaryScalars h 6 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker]
      exact h1'
    obtain ⟨c, -, -, hmat⟩ := mem_unitaryScalars.mp hmem
    have hmat' := congrArg (fun z : GL (Fin 6) F => ((z : Matrix (Fin 6) (Fin 6) F))) hmat
    rw [coe_twA5Hom_JParam] at hmat'
    have h0 := congrFun (congrFun hmat' 0) 0
    have h2 := congrFun (congrFun hmat' 2) 2
    have h3 := congrFun (congrFun hmat' 3) 3
    simp only [Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at h0 h2 h3
    have hc : (c : F) = 1 := by simpa [twA5Entries] using h0.symm
    exact ⟨Units.ext (by simpa [twA5Entries, hc] using h2),
      Units.ext (by simpa [twA5Entries, hc] using h3)⟩
  · rintro ⟨hp, hq⟩
    have hp' : p = 1 := Subtype.ext hp
    have hq' : q = 1 := Subtype.ext hq
    subst hp'
    subst hq'
    have hparam : twA5JParam (F := F) (1 : rootsOfUnity 3 F) 1 = 1 := by
      apply Subtype.ext
      unfold twA5JParam
      refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
      show ((1 : Fˣ) * (1 : Fˣ))⁻¹ = 1
      rw [mul_one, inv_one]
    rw [twA5JHom_apply, hparam, map_one, map_one]

theorem twA5JHom_injective : Function.Injective (twA5JHom h) := by
  intro x y hxy
  have h1 : twA5JHom h (x * y⁻¹) = 1 := by
    rw [map_mul, hxy, map_inv, mul_inv_cancel]
  obtain ⟨hp, hq⟩ := (twA5JHom_eq_one_iff h).mp h1
  have hx : x.1 = y.1 := by
    have h2 : ((x * y⁻¹).1 : Fˣ) = 1 := hp
    refine mul_inv_eq_one.mp ?_
    exact Subtype.ext h2
  have hy : x.2 = y.2 := by
    have h2 : ((x * y⁻¹).2 : Fˣ) = 1 := hq
    refine mul_inv_eq_one.mp ?_
    exact Subtype.ext h2
  exact Prod.ext hx hy

theorem twA5JParam_lift_mem_block (p q : rootsOfUnity 3 F) :
    twA5Hom h (twA5JParam (F := F) p q) ∈ unitaryBlock h suFiveIndex := by
  rw [twA5Hom_apply]
  unfold twA5Diag
  apply diagSU_mem_unitaryBlock
  intro k hk
  simp only [suFiveIndex, Finset.mem_erase, Finset.mem_univ, and_true, not_not] at hk
  subst hk
  change twA5Entries (F := F) (1 : Fˣ) (p : Fˣ) (q : Fˣ)
    (((p : Fˣ) * (q : Fˣ))⁻¹) 5 = 1
  simp [twA5Entries]

theorem card_twA5JHom_range : Nat.card (twA5JHom h).range = 9 := by
  haveI : Finite F := h.finite
  have h3 : Nat.card (rootsOfUnity 3 F) = 3 := by
    apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
    rw [twA5_card_F h]
    norm_num
  rw [← Nat.card_congr (MonoidHom.ofInjective (twA5JHom_injective h)).toEquiv]
  rw [Nat.card_prod, h3]

theorem twA5Jrange_le_B : (twA5JHom h).range ≤
    (twA5Hom h).range.map (unitaryProj h 6) := by
  rintro _ ⟨x, rfl⟩
  exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨twA5JParamHom x, rfl⟩)

theorem twA5Jrange_le_J : (twA5JHom h).range ≤ blockSU h suFiveIndex := by
  rintro _ ⟨x, rfl⟩
  exact unitaryProj_mem_blockSU h (twA5JParam_lift_mem_block h x.1 x.2)

theorem twA5Jrange_isElemAbelian :
    IsElemAbelian 3 (twA5JHom h).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]
  · exact (twA5Bar_isElemAbelian h (twA5_card_F h)).2 a (twA5Jrange_le_B h ha)

theorem card_rootsOfUnity_three (h : UnitaryFieldData 2 3 F) :
    Nat.card (rootsOfUnity 3 F) = 3 := by
  haveI : Finite F := h.finite
  apply CFSG.LinearGroups.card_rootsOfUnity_of_dvd
  rw [twA5_card_F h]
  norm_num

theorem twA5EHom_eq_one_iff {n : rootsOfUnity 9 F} {p q : rootsOfUnity 3 F} :
    twA5EHom h (n, p, q) = 1 ↔
      ((p : Fˣ) = 1 ∧ (q : Fˣ) = 1 ∧ ((n : Fˣ) ^ 3 = 1)) := by
  constructor
  · intro h1
    have h1' : unitaryProj h 6 (twA5Hom h (twA5EParam (F := F) n p q)) = 1 := h1
    have hmem : twA5Hom h (twA5EParam (F := F) n p q) ∈ unitaryScalars h 6 := by
      rw [← ker_unitaryProj, MonoidHom.mem_ker]
      exact h1'
    obtain ⟨c, -, -, hmat⟩ := mem_unitaryScalars.mp hmem
    have hmat' := congrArg (fun z : GL (Fin 6) F => ((z : Matrix (Fin 6) (Fin 6) F))) hmat
    rw [coe_twA5Hom_EParam] at hmat'
    have h0 := congrFun (congrFun hmat' 0) 0
    have h2 := congrFun (congrFun hmat' 2) 2
    have h3 := congrFun (congrFun hmat' 3) 3
    have h5 := congrFun (congrFun hmat' 5) 5
    simp only [Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, twA5Entries_zero, twA5Entries_two, twA5Entries_three,
      twA5Entries_five] at h0 h2 h3 h5
    have hpF : ((p : Fˣ) : F) = 1 := by
      have h := h2.trans h0.symm
      exact mul_left_cancel₀ (Units.ne_zero (n : Fˣ)) (by rw [mul_one]; exact h)
    have hqF : ((q : Fˣ) : F) = 1 := by
      have h := h3.trans h0.symm
      exact mul_left_cancel₀ (Units.ne_zero (n : Fˣ)) (by rw [mul_one]; exact h)
    have hpU : (p : Fˣ) = 1 := Units.ext hpF
    have hqU : (q : Fˣ) = 1 := Units.ext hqF
    have hn5 : ((n : Fˣ) ^ 5)⁻¹ = (n : Fˣ) := by
      apply Units.ext
      have h := h5.trans h0.symm
      rw [hpU, hqU] at h
      simpa using h
    have hn6 : (n : Fˣ) ^ 6 = 1 := by
      calc (n : Fˣ) ^ 6 = (n : Fˣ) ^ 5 * (n : Fˣ) := by
            rw [show (6 : ℕ) = 5 + 1 by norm_num, pow_succ]
        _ = (n : Fˣ) ^ 5 * ((n : Fˣ) ^ 5)⁻¹ := by rw [hn5]
        _ = 1 := mul_inv_cancel _
    have hn3 : (n : Fˣ) ^ 3 = 1 := by
      have h9 : (n : Fˣ) ^ 9 = 1 :=
        (mem_rootsOfUnity (M := F) 9 (n : Fˣ)).mp n.2
      have hdvd : orderOf (n : Fˣ) ∣ 3 := by
        have hg : orderOf (n : Fˣ) ∣ Nat.gcd 6 9 :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hn6) (orderOf_dvd_of_pow_eq_one h9)
        simpa using hg
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    exact ⟨Units.ext hpF, Units.ext hqF, hn3⟩
  · rintro ⟨hp, hq, hn3⟩
    have hparam : twA5EParam (F := F) n p q = twA5ScalarParam (F := F) ⟨n, hn3⟩ := by
      apply Subtype.ext
      simp only [twA5EParam, twA5ScalarParam, Subtype.coe_mk]
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
      · exact hp
      · exact hq
      · rw [hp, hq, mul_one]
    rw [twA5EHom_apply]
    change unitaryProj h 6 (twA5Hom h (twA5EParam (F := F) n p q)) = 1
    rw [hparam]
    have hmem : twA5Hom h (twA5ScalarParam (F := F) ⟨n, hn3⟩) ∈ (unitaryProj h 6).ker := by
      rw [ker_unitaryProj]
      exact twA5Hom_scalarParam_mem h ⟨n, hn3⟩
    exact MonoidHom.mem_ker.mp hmem

theorem card_ker_twA5EHom (h : UnitaryFieldData 2 3 F) :
    Nat.card (twA5EHom h).ker = 3 := by
  haveI : Finite F := h.finite
  apply le_antisymm
  · let g : (twA5EHom h).ker → rootsOfUnity 3 F := fun x =>
      ⟨(x.1.1 : Fˣ), (mem_rootsOfUnity (M := F) 3 _).mpr
        ((twA5EHom_eq_one_iff h).mp x.2).2.2⟩
    have hinj : Function.Injective g := by
      intro x y hxy
      obtain ⟨hx1, hx2, -⟩ := (twA5EHom_eq_one_iff h).mp x.2
      obtain ⟨hy1, hy2, -⟩ := (twA5EHom_eq_one_iff h).mp y.2
      have hn : x.1.1 = y.1.1 := Subtype.ext
        (congrArg (fun z : rootsOfUnity 3 F => (z : Fˣ)) hxy)
      have hp : x.1.2.1 = y.1.2.1 := by
        apply Subtype.ext
        rw [hx1, hy1]
      have hq : x.1.2.2 = y.1.2.2 := by
        apply Subtype.ext
        rw [hx2, hy2]
      exact Subtype.ext (Prod.ext hn (Prod.ext hp hq))
    have hle := Nat.card_le_card_of_injective g hinj
    rwa [card_rootsOfUnity_three h] at hle
  · let g : rootsOfUnity 3 F → (twA5EHom h).ker := fun a =>
      ⟨((⟨(a : Fˣ), (mem_rootsOfUnity (M := F) 9 _).mpr (by
          rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, a.2, one_pow])⟩ :
            rootsOfUnity 9 F), ((1 : rootsOfUnity 3 F), (1 : rootsOfUnity 3 F))), by
        rw [MonoidHom.mem_ker, twA5EHom_eq_one_iff]
        exact ⟨rfl, rfl, a.2⟩⟩
    have hinj : Function.Injective g := by
      intro a b hab
      have h := congrArg (fun x : (twA5EHom h).ker => (x.1.1 : Fˣ)) hab
      exact Subtype.ext h
    have hge := Nat.card_le_card_of_injective g hinj
    rwa [card_rootsOfUnity_three h] at hge

theorem card_twA5E (h : UnitaryFieldData 2 3 F) :
    Nat.card (twA5EHom h).range = 27 := by
  haveI : Finite F := h.finite
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (twA5EHom h).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (twA5EHom h)).toEquiv] at hcard
  have hdom : Nat.card (rootsOfUnity 9 F × (rootsOfUnity 3 F × rootsOfUnity 3 F)) = 81 := by
    rw [Nat.card_prod, twA5_card_rootsOfUnity_nine h, Nat.card_prod,
      card_rootsOfUnity_three h]
  rw [card_ker_twA5EHom h, hdom] at hcard
  omega

theorem twA5E_le_B : (twA5EHom h).range ≤ (twA5Hom h).range.map (unitaryProj h 6) := by
  rintro _ ⟨x, rfl⟩
  exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨twA5EParamHom x, rfl⟩)

theorem twA5E_isElemAbelian (h : UnitaryFieldData 2 3 F) :
    IsElemAbelian 3 (twA5EHom h).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]
  · exact (twA5Bar_isElemAbelian h (twA5_card_F h)).2 a (twA5E_le_B h ha)

theorem twA5X_mem_E : twA5X h ∈ (twA5EHom h).range := by
  refine MonoidHom.mem_range.mpr ⟨(twA5Lambda (F := F), 1, 1), ?_⟩
  change unitaryProj h 6 (twA5Hom h (twA5EParam (F := F) (twA5Lambda (F := F)) 1 1)) =
    twA5X h
  have hparam : twA5EParam (F := F) (twA5Lambda (F := F)) (1 : rootsOfUnity 3 F) 1 =
      twA5XParam (F := F) := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    show ((1 : Fˣ) * (1 : Fˣ)) = 1
    rw [mul_one]
  rw [hparam, twA5X]

@[expose] noncomputable def twA5E2 : unitaryPSU h 6 :=
  twA5EHom h ((1 : rootsOfUnity 9 F), (1 : rootsOfUnity 3 F), twA5Omega (F := F))

@[expose] noncomputable def twA5E3 : unitaryPSU h 6 :=
  twA5EHom h ((1 : rootsOfUnity 9 F), twA5Omega (F := F), (1 : rootsOfUnity 3 F))

theorem twA5E2_mem_E : twA5E2 h ∈ (twA5EHom h).range :=
  MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem twA5E3_mem_E : twA5E3 h ∈ (twA5EHom h).range :=
  MonoidHom.mem_range.mpr ⟨_, rfl⟩

theorem twA5Entries_E2 :
    twA5Entries (F := F) (1 : Fˣ) (1 : Fˣ) (twA5Omega (F := F) : Fˣ)
        ((1 : Fˣ) * (twA5Omega (F := F) : Fˣ)) =
      (fun i : Fin 6 => if i ∈ ({0, 1, 2} : Finset (Fin 6)) then (1 : F)
        else ((twA5Omega (F := F) : Fˣ) : F)) := by
  funext i
  fin_cases i <;> simp [twA5Entries, twA5Omega_inv_mul_self, twA5Omega_inv_mul_inv]

theorem twA5Entries_E3 :
    twA5Entries (F := F) (1 : Fˣ) (twA5Omega (F := F) : Fˣ) (1 : Fˣ)
        ((twA5Omega (F := F) : Fˣ) * (1 : Fˣ)) =
      (fun i : Fin 6 => if i ∈ ({0, 1, 3} : Finset (Fin 6)) then (1 : F)
        else ((twA5Omega (F := F) : Fˣ) : F)) := by
  funext i
  fin_cases i <;> simp [twA5Entries, twA5Omega_inv_mul_self, twA5Omega_inv_mul_inv]


private theorem unitaryBlock_pair_mul_diagSU {d : Fin 6 → F} (hd01 : d 0 = d 1)
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
    {B : unitarySU 2 3 F 6} (hB : B ∈ unitaryBlock h ({0, 1} : Finset (Fin 6))) :
    B * diagSU h d hd hdet = diagSU h d hd hdet * B := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_diagSU]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : i ∈ ({0, 1} : Finset (Fin 6))
  · by_cases hj : j ∈ ({0, 1} : Finset (Fin 6))
    · have hdi : d i = d j := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [hd01]
      rw [hdi, mul_comm]
    · have h0 : ((B : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
        have h1 := (mem_unitaryBlock h).1 hB i j (Or.inr hj)
        have hij : i ≠ j := by rintro rfl; exact hj hi
        simpa [Matrix.one_apply, hij] using h1
      rw [h0, zero_mul, mul_zero]
  · by_cases hj : j ∈ ({0, 1} : Finset (Fin 6))
    · have h0 : ((B : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
        have h1 := (mem_unitaryBlock h).1 hB i j (Or.inl hi)
        have hij : i ≠ j := by rintro rfl; exact hi hj
        simpa [Matrix.one_apply, hij] using h1
      rw [h0, zero_mul, mul_zero]
    · have h1 := (mem_unitaryBlock h).1 hB i j (Or.inl hi)
      by_cases hij : i = j
      · subst hij
        rw [h1]
        simp
      · have h0 : ((B : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
          simpa [Matrix.one_apply, hij] using h1
        rw [h0, zero_mul, mul_zero]

private theorem mem_unitaryBlockDiag_of_proj_centralizer_diagSU
    {I : Finset (Fin 6)} (hI : I ⊆ suFiveIndex) {l ν : F} (hlν : l ≠ ν)
    {d : Fin 6 → F} (hv : ∀ i, d i = if i ∈ I then l else ν)
    (hd : ∀ i, h.norm (d i) = 1) (hdet : ∏ i, d i = 1)
    {A : unitarySU 2 3 F 6} (hA : A ∈ unitaryBlock h suFiveIndex)
    (hc : unitaryProj h 6 A * unitaryProj h 6 (diagSU h d hd hdet) =
      unitaryProj h 6 (diagSU h d hd hdet) * unitaryProj h 6 A) :
    A ∈ unitaryBlockDiag h I := by
  have h5 : 5 ∉ I := by
    intro hmem
    have := hI hmem
    simp [suFiveIndex] at this
  have hν0 : ν ≠ 0 := by
    have hd5 : h.norm ν = 1 := by
      have h := hd 5
      rwa [hv 5, if_neg h5] at h
    rintro rfl
    rw [show h.norm (0 : F) = 0 by simp [UnitaryFieldData.norm]] at hd5
    exact zero_ne_one hd5
  rw [← map_mul, ← map_mul] at hc
  obtain ⟨c, -, -, hmat⟩ :=
    mem_unitaryScalars.mp ((QuotientGroup.eq (s := unitaryScalars h 6)).mp hc)
  have h1 : ((diagSU h d hd hdet * A : unitarySU 2 3 F 6) : GL (Fin 6) F) =
      ((A * diagSU h d hd hdet : unitarySU 2 3 F 6) : GL (Fin 6) F) *
        GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← hmat, ← Subgroup.coe_mul, mul_inv_cancel_left]
  have h2 : diagonal d * ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      (((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) * diagonal d) *
        diagonal (fun _ : Fin 6 => (c : F)) := by
    have h := congrArg (fun g : GL (Fin 6) F => ((g : Matrix (Fin 6) (Fin 6) F))) h1
    simpa only [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, coe_diagSU] using h
  have hA55 : ((A : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) 5 5 = 1 := by
    have h := (mem_unitaryBlock h).1 hA 5 5 (Or.inl (by simp [suFiveIndex]))
    simpa using h
  have h55 := congrFun (congrFun h2 5) 5
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_diagonal] at h55
  have hν5 : d 5 = ν := by rw [hv 5, if_neg h5]
  rw [hA55, hν5] at h55
  simp only [mul_one, one_mul] at h55
  have hc1 : (c : F) = 1 := by
    have h : ν * (1 : F) = ν * (c : F) := by simpa using h55
    exact (mul_left_cancel₀ hν0 h).symm
  have hcU : c = 1 := Units.ext hc1
  have hcomm : A * diagSU h d hd hdet = diagSU h d hd hdet * A := by
    have h1' : ((diagSU h d hd hdet * A : unitarySU 2 3 F 6) : GL (Fin 6) F) =
        ((A * diagSU h d hd hdet : unitarySU 2 3 F 6) : GL (Fin 6) F) := by
      rw [h1, hcU]
      simp
    exact Subtype.ext (Units.ext (by
      have h := congrArg (fun g : GL (Fin 6) F => ((g : Matrix (Fin 6) (Fin 6) F))) h1'
      simpa only [Subgroup.coe_mul, Units.val_mul] using h.symm))
  rw [← centralizer_diagSU_eq_unitaryBlockDiag h hlν hv hd hdet]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm

private theorem unitaryBlock_pair_le_centralizer_twA5E :
    (unitaryBlock h ({0, 1} : Finset (Fin 6))).map (unitaryProj h 6) ≤
      Subgroup.centralizer ((twA5EHom h).range : Set (unitaryPSU h 6)) := by
  rintro _ ⟨B, hB, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hz
  obtain ⟨n, p, q⟩ := x
  have hcomm : B * twA5Hom h (twA5EParam (F := F) n p q) =
      twA5Hom h (twA5EParam (F := F) n p q) * B := by
    rw [twA5Hom_apply]
    unfold twA5Diag
    exact unitaryBlock_pair_mul_diagSU (h := h)
      (d := twA5Entries (F := F) (n : Fˣ) (p : Fˣ) (q : Fˣ) ((p : Fˣ) * (q : Fˣ)))
      rfl
      (twA5Entries_norm h (n : Fˣ) (p : Fˣ) (q : Fˣ) ((p : Fˣ) * (q : Fˣ))
        (norm_eq_one_of_pow_nine h (coe_pow_eq_one n.2))
        (norm_eq_one_of_pow_three h (coe_pow_eq_one p.2))
        (norm_eq_one_of_pow_three h (coe_pow_eq_one q.2))
        (by
          rw [Units.val_mul, norm_mul_eq h,
            norm_eq_one_of_pow_three h (coe_pow_eq_one p.2),
            norm_eq_one_of_pow_three h (coe_pow_eq_one q.2), one_mul]))
      (twA5Entries_prod (F := F) (n : Fˣ) (p : Fˣ) (q : Fˣ) ((p : Fˣ) * (q : Fˣ)))
      hB
  have hmap := congrArg (unitaryProj h 6) hcomm
  change twA5EHom h (n, p, q) * unitaryProj h 6 B =
    unitaryProj h 6 B * twA5EHom h (n, p, q)
  exact hmap.symm

theorem twA5_e3_range :
    GLAPLayer 3 (blockSU h suFiveIndex ⊓
      Subgroup.centralizer ((twA5EHom h).range : Set (unitaryPSU h 6))) ≠ ⊥ := by
  haveI : Finite F := h.finite
  refine glaPLayer_ne_bot_of_map_unitaryBlockDiag_inf_card_eq_two h
    (q := 3) (by norm_num) (by norm_num) (I := ({0, 1} : Finset (Fin 6)))
    (J₁ := ({0, 1, 2} : Finset (Fin 6))) (J₂ := ({0, 1, 3} : Finset (Fin 6)))
    ?_ ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · exact ⟨2, by decide⟩
  · refine le_inf ?_ (unitaryBlock_pair_le_centralizer_twA5E h)
    exact Subgroup.map_mono (unitaryBlock_mono (h := h) (by decide))
  · intro z hz
    obtain ⟨hzJ, hzC⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨A, hA, rfl⟩ := (mem_blockSU h).1 hzJ
    have hz2 : unitaryProj h 6 A * twA5E2 h = twA5E2 h * unitaryProj h 6 A :=
      ((Subgroup.mem_centralizer_iff.1 hzC) (twA5E2 h) (twA5E2_mem_E h)).symm
    have hz3 : unitaryProj h 6 A * twA5E3 h = twA5E3 h * unitaryProj h 6 A :=
      ((Subgroup.mem_centralizer_iff.1 hzC) (twA5E3 h) (twA5E3_mem_E h)).symm
    have hA12 : A ∈ unitaryBlockDiag h ({0, 1, 2} : Finset (Fin 6)) := by
      refine mem_unitaryBlockDiag_of_proj_centralizer_diagSU (h := h)
        (I := ({0, 1, 2} : Finset (Fin 6))) (l := (1 : F))
        (ν := ((twA5Omega (F := F) : Fˣ) : F))
        (d := twA5Entries (F := F) (1 : Fˣ) (1 : Fˣ) (twA5Omega (F := F) : Fˣ)
          ((1 : Fˣ) * (twA5Omega (F := F) : Fˣ)))
        (hI := ?_) (hlν := ?_) (hv := ?_) (hd := ?_) (hdet := ?_) (hA := hA) (hc := ?_)
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> simp [suFiveIndex]
      · intro hh
        exact twA5Omega_ne_one h (Units.ext hh.symm)
      · intro i
        exact congrFun (twA5Entries_E2 (F := F)) i
      · exact twA5Entries_norm h (1 : Fˣ) (1 : Fˣ)
          (twA5Omega (F := F) : Fˣ) ((1 : Fˣ) * (twA5Omega (F := F) : Fˣ))
          (by simp [UnitaryFieldData.norm])
          (by simp [UnitaryFieldData.norm])
          (by simpa using twA5Omega_norm h)
          (by
            rw [Units.val_mul, norm_mul_eq h, twA5Omega_norm h]
            rw [show h.norm ((1 : Fˣ) : F) = 1 by simp [UnitaryFieldData.norm], one_mul])
      · exact twA5Entries_prod (F := F) (1 : Fˣ) (1 : Fˣ)
          (twA5Omega (F := F) : Fˣ) ((1 : Fˣ) * (twA5Omega (F := F) : Fˣ))
      · exact hz2
    have hA13 : A ∈ unitaryBlockDiag h ({0, 1, 3} : Finset (Fin 6)) := by
      refine mem_unitaryBlockDiag_of_proj_centralizer_diagSU (h := h)
        (I := ({0, 1, 3} : Finset (Fin 6))) (l := (1 : F))
        (ν := ((twA5Omega (F := F) : Fˣ) : F))
        (d := twA5Entries (F := F) (1 : Fˣ) (twA5Omega (F := F) : Fˣ) (1 : Fˣ)
          ((twA5Omega (F := F) : Fˣ) * (1 : Fˣ)))
        (hI := ?_) (hlν := ?_) (hv := ?_) (hd := ?_) (hdet := ?_) (hA := hA) (hc := ?_)
      · intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl <;> simp [suFiveIndex]
      · intro hh
        exact twA5Omega_ne_one h (Units.ext hh.symm)
      · intro i
        exact congrFun (twA5Entries_E3 (F := F)) i
      · exact twA5Entries_norm h (1 : Fˣ) (twA5Omega (F := F) : Fˣ) (1 : Fˣ)
          ((twA5Omega (F := F) : Fˣ) * (1 : Fˣ))
          (by simp [UnitaryFieldData.norm])
          (by simpa using twA5Omega_norm h)
          (by simp [UnitaryFieldData.norm])
          (by
            rw [Units.val_mul, norm_mul_eq h, twA5Omega_norm h]
            rw [show h.norm ((1 : Fˣ) : F) = 1 by simp [UnitaryFieldData.norm], one_mul])
      · exact twA5Entries_prod (F := F) (1 : Fˣ) (twA5Omega (F := F) : Fˣ)
          (1 : Fˣ) ((twA5Omega (F := F) : Fˣ) * (1 : Fˣ))
      · exact hz3
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨hA12, hA13⟩)
  · norm_num

theorem twA5_e3 : ∃ E : Subgroup (unitaryPSU h 6),
    E ≤ (twA5Hom h).range.map (unitaryProj h 6) ∧ IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 3 ∧ twA5X h ∈ E ∧
      GLAPLayer 3 (blockSU h suFiveIndex ⊓
        Subgroup.centralizer (E : Set (unitaryPSU h 6))) ≠ ⊥ :=
  ⟨(twA5EHom h).range, twA5E_le_B h, twA5E_isElemAbelian h,
    by rw [card_twA5E h]; norm_num, twA5X_mem_E h, twA5_e3_range h⟩


end TwA5Eight

end CFSG.LocalAnalysis.GLTheoremA.Y10F

module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGKind2Char
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveCard
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeLowCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

@[expose] noncomputable def FGKind2E0 (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1) :
    Subgroup ↥(FGKind2D hQ g) :=
  ((omegaGroup (nondegenerate_restrict_fixSp hQ hgg)).map
    ((blockHom hgg).comp (MonoidHom.inl _ _))).subgroupOf (FGKind2D hQ g)

theorem fg_kind2_mem_E0_iff (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    {x : ↥(FGKind2D hQ g)} :
    x ∈ FGKind2E0 hQ hgg ↔ ∃ a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hgg),
      blockHom hgg (a, 1) = (x : OGroup Q) := by
  unfold FGKind2E0
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact Iff.rfl

instance fg_kind2_E0_normal (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1) :
    (FGKind2E0 hQ hgg).Normal := by
  constructor
  intro x hx y
  rw [fg_kind2_mem_E0_iff] at hx ⊢
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨p, hp⟩ := (show (y : OGroup Q) ∈ (blockHom hgg).range from
    fg_kind2_D_le_range hQ hgg y.2)
  refine ⟨p.1 * a * p.1⁻¹, (omegaGroup_normal _).conj_mem _ ha p.1, ?_⟩
  have hcalc : (y : OGroup Q) * (x : OGroup Q) * (y : OGroup Q)⁻¹ =
      blockHom hgg (p.1 * a * p.1⁻¹, 1) := by
    rw [← hax, ← hp]
    change blockHom hgg p * blockHom hgg (a, 1) * (blockHom hgg p)⁻¹ =
      blockHom hgg (p.1 * a * p.1⁻¹, 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Prod.ext rfl (by simp)
  exact hcalc.symm

theorem fg_kind2_finrank_fixSp (hdim : Module.finrank (ZMod 3) V = 6) {g : OGroup Q}
    (hgg : g * g = 1) {α : ℤˣ} (hty : invType g = (1, α)) :
    Module.finrank (ZMod 3) (fixSp g) = 5 := by
  have hcdim : Module.finrank (ZMod 3) (commSp g) = 1 := congrArg Prod.fst hty
  have h := finrank_fixSp_add_finrank_commSp (Q := Q) g
  rw [hcdim, hdim] at h
  omega

theorem fg_kind2_E0_lieModel (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ} (hty : invType g = (1, α)) :
    LieModel ↥(FGKind2E0 hQ hgg) .PSp 2 3 1 := by
  have hUdim := fg_kind2_finrank_fixSp hdim hgg hty
  have hW : 2 ≤ Module.finrank (ZMod 3) (fixSp g) := by omega
  have hQU : (Q.restrict (fixSp g)).Nondegenerate := nondegenerate_restrict_fixSp hQ hgg
  have hfileModelU : LieModel (omegaGroup hQU) .PSp 2 3 1 := by
    have hZ : Subgroup.center (omegaGroup hQU) = ⊥ :=
      Subgroup.eq_bot_of_card_eq (Subgroup.center (omegaGroup hQU))
        (natCard_center_omegaGroup_five hQU hUdim)
    exact LieModel.of_mulEquiv ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot) (lieModel_quotient_center_omegaGroup_five hQU hUdim)
  let φ : OGroup (Q.restrict (fixSp g)) →* OGroup Q := (blockHom hgg).comp (MonoidHom.inl _ _)
  have hφinj : Function.Injective φ := fun a b hab =>
    congrArg Prod.fst (blockHom_injective hgg hab)
  have hEle : (omegaGroup hQU).map φ ≤ FGKind2D hQ g := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨blockHom_left_mem_omegaGroup hQ hgg hW ha,
      Subgroup.mem_centralizer_singleton_iff.mpr (ff_blockHom_inl_commute hgg a)⟩
  exact hfileModelU.of_mulEquiv
    ((Subgroup.equivMapOfInjective _ φ hφinj).trans (Subgroup.subgroupOfEquivOfLe hEle).symm)

theorem fg_kind2_E0_isPGroup_quotient (hQ : Q.Nondegenerate)
    {g : OGroup Q} (hgg : g * g = 1) {α : ℤˣ} (hty : invType g = (1, α)) :
    IsPGroup 2 (↥(FGKind2D hQ g) ⧸ FGKind2E0 hQ hgg) := by
  have hcdim : Module.finrank (ZMod 3) (commSp g) = 1 := congrArg Prod.fst hty
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (FGKind2E0 hQ hgg) x
  refine ⟨1, ?_⟩
  rw [pow_one, pow_two, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    fg_kind2_mem_E0_iff]
  obtain ⟨p, hp⟩ := (show (y : OGroup Q) ∈ (blockHom hgg).range from
    fg_kind2_D_le_range hQ hgg y.2)
  have hWfin : Nat.card (OGroup (Q.restrict (commSp g))) = 2 :=
    natCard_oGroup_one (nondegenerate_restrict_commSp hQ hgg) hcdim
  have hp2 : p.2 * p.2 = 1 := by
    have hdvd : orderOf p.2 ∣ 2 := by
      rw [← hWfin]
      exact orderOf_dvd_natCard p.2
    rw [orderOf_dvd_iff_pow_eq_one] at hdvd
    simpa [pow_two] using hdvd
  have hpp : p * p = (p.1 * p.1, p.2 * p.2) := rfl
  refine ⟨p.1 * p.1, mul_self_mem_omegaGroup _ p.1, ?_⟩
  rw [Subgroup.coe_mul, ← hp, ← map_mul, hpp, hp2]

theorem fg_kind2_chi_eq_one_of_mem_E0 (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    {x : ↥(FGKind2D hQ g)} (hx : x ∈ FGKind2E0 hQ hgg) : FGKind2Chi hQ hgg x = 1 := by
  obtain ⟨a, -, hax⟩ := (fg_kind2_mem_E0_iff hQ hgg).mp hx
  have hmem : blockHom hgg (a, 1) ∈ FGKind2D hQ g := hax ▸ x.2
  have h := fg_kind2_chi_blockHom hQ hgg a 1 hmem
  rw [← h]
  congr 1
  exact Subtype.ext hax.symm

theorem fg_kind2_mem_E0_of_involution (hQ : Q.Nondegenerate) {g : OGroup Q} (hgg : g * g = 1)
    {x : ↥(FGKind2D hQ g)} (hxx : x * x = 1) (hχ : FGKind2Chi hQ hgg x = 1) :
    x ∈ FGKind2E0 hQ hgg := by
  obtain ⟨a, ha⟩ := fg_kind2_exists_blockHom hQ hgg x
  rw [hχ] at ha
  have hxx' : (x : OGroup Q) * (x : OGroup Q) = 1 := by
    have h := congrArg Subtype.val hxx
    simpa using h
  have haa : a * a = 1 := by
    have h1 : blockHom hgg (a * a, 1) = blockHom hgg 1 := by
      have : (a * a, (1 : OGroup (Q.restrict (commSp g)))) = (a, 1) * (a, 1) := by
        simp [Prod.mk_mul_mk]
      rw [this, map_mul, ha, hxx', map_one]
    exact congrArg Prod.fst (blockHom_injective hgg h1)
  have hinv := (involution_mem_omegaGroup_iff hQ hxx').mp x.2.1
  have hty : invType (x : OGroup Q) = invType a := by
    rw [← ha]
    exact ff_invType_blockHom_inl hQ hgg haa
  have hd : invDim (x : OGroup Q) = invDim a := congrArg Prod.fst hty
  have hs : invSign (x : OGroup Q) = invSign a := congrArg Prod.snd hty
  have haΩ : a ∈ omegaGroup (nondegenerate_restrict_fixSp hQ hgg) :=
    (involution_mem_omegaGroup_iff (nondegenerate_restrict_fixSp hQ hgg) haa).mpr
      ⟨hd ▸ hinv.1, by rw [← hs, ← hd]; exact hinv.2⟩
  exact (fg_kind2_mem_E0_iff hQ hgg).mpr ⟨a, haΩ, ha⟩

end CFSG.OddStandard.SmallF3.Omega

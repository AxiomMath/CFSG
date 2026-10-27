module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleRankOne
public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Bridge
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

open CFSG.Open CFSG.ShultStronglyClosedTI
open scoped commutatorElement

section CentralQuotient

variable {Y : Type} [Group Y]

theorem central_comm {Z : Subgroup Y} (hZ : Z ≤ Subgroup.center Y) (a b : ↥Z) : a * b = b * a :=
  Subtype.ext ((Subgroup.mem_center_iff.mp (hZ b.2)) a.1)

theorem isSolvable_of_central_quotient (Z : Subgroup Y) [Z.Normal] (hZ : Z ≤ Subgroup.center Y)
    [Group.IsSolvable (Y ⧸ Z)] : Group.IsSolvable Y := by
  have : Group.IsSolvable ↥Z := Group.isSolvable_of_comm (central_comm hZ)
  refine Group.isSolvable_of_ker_le_range Z.subtype (QuotientGroup.mk' Z) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

theorem isSolvable_of_central_quotient_subgroup (Z : Subgroup Y) [Z.Normal]
    (hZ : Z ≤ Subgroup.center Y) (M : Subgroup Y)
    (hM : Group.IsSolvable ↥(M.map (QuotientGroup.mk' Z))) : Group.IsSolvable ↥M := by
  have : Group.IsSolvable ↥(Z.subgroupOf M) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subtype.ext
      ((Subgroup.mem_center_iff.mp (hZ (Subgroup.mem_subgroupOf.mp b.2))) (a.1 : Y)))
  refine Group.isSolvable_of_ker_le_range (Z.subgroupOf M).subtype
    ((QuotientGroup.mk' Z).subgroupMap M) ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxZ : (x : Y) ∈ Z := by
    have := congrArg Subtype.val hx
    rw [MonoidHom.subgroupMap_apply_coe] at this
    exact (QuotientGroup.eq_one_iff _).mp this
  exact ⟨⟨x, hxZ⟩, rfl⟩

theorem commutator_mul_central_left {m z g : Y} (hz : z ∈ Subgroup.center Y) :
    ⁅m * z, g⁆ = ⁅m, g⁆ := by
  have h : z * g * z⁻¹ = g := by rw [← Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  calc ⁅m * z, g⁆ = m * (z * g * z⁻¹) * m⁻¹ * g⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅m, g⁆ := by rw [h, commutatorElement_def]

theorem commutator_mul_central_right {m z g : Y} (hz : z ∈ Subgroup.center Y) :
    ⁅g, m * z⁆ = ⁅g, m⁆ := by
  have h : z * g⁻¹ * z⁻¹ = g⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hz g⁻¹, mul_inv_cancel_right]
  calc ⁅g, m * z⁆ = g * m * (z * g⁻¹ * z⁻¹) * m⁻¹ := by simp only [commutatorElement_def]; group
    _ = ⁅g, m⁆ := by rw [h, commutatorElement_def]

theorem commutator_le_of_sup_central (Z : Subgroup Y) [Z.Normal] (hZ : Z ≤ Subgroup.center Y)
    (M : Subgroup Y) (hMZ : M ⊔ Z = ⊤) : commutator Y ≤ M := by
  rw [commutator_eq_closure]
  rw [Subgroup.closure_le]
  rintro _ ⟨g₁, g₂, rfl⟩
  have h₁ : g₁ ∈ ((M ⊔ Z : Subgroup Y) : Set Y) := by rw [hMZ]; trivial
  have h₂ : g₂ ∈ ((M ⊔ Z : Subgroup Y) : Set Y) := by rw [hMZ]; trivial
  rw [Subgroup.mul_normal] at h₁ h₂
  obtain ⟨m₁, hm₁, z₁, hz₁, rfl⟩ := h₁
  obtain ⟨m₂, hm₂, z₂, hz₂, rfl⟩ := h₂
  rw [commutator_mul_central_left (hZ hz₁), commutator_mul_central_right (hZ hz₂),
    commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)

end CentralQuotient

section Bender

theorem a312For_of_bender_central_quotient {Y : Type} [Group Y] [Finite Y]
    (hq : CFSG.IsQuasisimple Y) (Z : Subgroup Y) [Z.Normal] (hZ : Z ≤ Subgroup.center Y)
    (hB : fusionIsBenderGroup (Y ⧸ Z)) : A312For Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (Y ⧸ Z) :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 2 Y))
  refine A312For.of_solvable_overgroups hq (P : Subgroup Y)
    (CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P) fun M hPM hMtop => ?_
  let Q : Sylow 2 (Y ⧸ Z) := P.mapSurjective (QuotientGroup.mk'_surjective Z)
  have hQM : (Q : Subgroup (Y ⧸ Z)) ≤ M.map (QuotientGroup.mk' Z) := by
    rw [Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hPM
  have hMtop' : M.map (QuotientGroup.mk' Z) ≠ ⊤ := by
    intro h
    apply hMtop
    have hMZ : M ⊔ Z = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' Z)) h
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    have := commutator_le_of_sup_central Z hZ M hMZ
    rw [hq.1.commutator_eq_top] at this
    exact top_le_iff.mp this
  exact isSolvable_of_central_quotient_subgroup Z hZ M
    (CFSG.QuasithinUnique.Unc25G2.A312Sub.bender_overgroups hB Q hQM hMtop')

theorem card_psu3_two : Nat.card (PSU3 2 1) = 72 := by
  have h := CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.unitaryFieldData_galoisField
    (f := 1) le_rfl
  have hmul := CFSG.ClassicalGroups.UnitaryFlag.card_hypPSU_mul h (r := 1) (ε := 1)
  have hZ := CFSG.ClassicalGroups.UnitaryFlag.card_hypScalars h (r := 1) (ε := 1) (by omega)
  have hS := (CFSG.ClassicalGroups.UnitaryFlag.card_hypSU h (r := 1) (ε := 1) (by omega)).1
  have hS' : Nat.card (CFSG.ClassicalGroups.UnitaryFlag.hypSU h 1 1) = 216 := by
    have hI : Finset.Icc 2 (2 * 1 + 1) = {2, 3} := by decide
    rw [hI, Finset.prod_pair (by norm_num)] at hS
    norm_num at hS
    exact_mod_cast hS
  rw [hS', hZ] at hmul
  rw [Nat.card_congr (CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut.psu3EquivHypPSU
    le_rfl).symm.toEquiv]
  norm_num at hmul ⊢
  omega

end Bender

section SU3

local notation "StSU" => CFSG.Assembly.LowTwoRank.StatedSU
local notation "StScal" => CFSG.Assembly.LowTwoRank.StatedScalars

theorem sl3evenMinus : FamSl3evenMinus := by
  intro X _ _ e hq he _ hX
  obtain ⟨K, hF, hFin, hK, ⟨φ⟩⟩ := hX
  have hq' := CFSG.LocalCores.isQuasisimple_of_mulEquiv φ hq
  refine A312For.of_mulEquiv φ ?_
  have hcard : Nat.card K = 2 ^ (2 * e) := by rw [hK, ← pow_mul, mul_comm]
  let Z : Subgroup ↥(StSU 3 (2 ^ e) K) := (StScal (Fin 3) K).subgroupOf (StSU 3 (2 ^ e) K)
  have hZc : Z ≤ Subgroup.center ↥(StSU 3 (2 ^ e) K) := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro y
    have hz' : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact Subgroup.mem_subgroupOf.mp hz
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz' (y : GL (Fin 3) K))
  rcases Nat.lt_or_ge e 2 with he1 | he2
  · exfalso
    have he1' : e = 1 := by omega
    subst he1'
    let ψ : (↥(StSU 3 (2 ^ 1) K) ⧸ Z) ≃* PSU3 2 1 :=
      (glaSUFieldEquiv (binaryFieldEquiv (2 * 1) (by omega) hcard) (2 ^ 1)).trans
        (glaSUCanonicalEquivNative 1)
    have hfin : Finite (PSU3 2 1) := Nat.finite_of_card_ne_zero (by rw [card_psu3_two]; norm_num)
    have hsolv : Group.IsSolvable (PSU3 2 1) :=
      isSolvable_of_card_two_three (a := 3) (b := 2) (by rw [card_psu3_two]; norm_num)
    have : Group.IsSolvable (↥(StSU 3 (2 ^ 1) K) ⧸ Z) :=
      Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
    have : Group.IsSolvable ↥(StSU 3 (2 ^ 1) K) := isSolvable_of_central_quotient Z hZc
    exact CFSG.LocalAnalysis.ComponentInitial.not_isSolvable_of_isQuasisimple hq' this
  · exact a312For_of_bender_central_quotient hq' Z hZc
      (Or.inr (Or.inl ⟨e, he2, ⟨glaSU3EquivNative e he2 hcard⟩⟩))

end SU3


end CFSG.QuasithinUnique.Vol2Native.A312L

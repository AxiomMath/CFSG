module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryCenter
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryInv
public import CFSG.Quasithin.Background.SylowOddCentralKernel
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryTrans

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Quasithin CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.SymplecticFourStandard.SingleCommParts
open scoped Pointwise

variable {m : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 m K}

theorem omegaOneOf_sylow_eq_center (h : UnitaryFieldData 2 m K)
    (R : Sylow 2 ↥(unitarySU 2 m K 3)) :
    omegaOneOf (R : Subgroup ↥(unitarySU 2 m K 3)) =
      (Subgroup.center ↥(R : Subgroup ↥(unitarySU 2 m K 3))).map
        (R : Subgroup ↥(unitarySU 2 m K 3)).subtype := by
  apply le_antisymm
  · rw [omegaOneOf]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxR, hx2⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hxR⟩, model3_unitary_involution_central h R ⟨x, hxR⟩ (by simpa [pow_two] using hx2), rfl⟩
  · obtain ⟨L, hL, hZ, -⟩ := model3_unitary_center_eq_point h R
    rw [hZ, isotropicTransvectionGroup]
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨a, haL, c, hc, hg⟩
    haveI : CharP K 2 := h.charP
    have hTR : isotropicTransvectionGroup h 3 L ≤ (R : Subgroup ↥(unitarySU 2 m K 3)) := by
      rw [← hZ]
      exact Subgroup.map_subtype_le _
    have hgR : g ∈ (R : Subgroup ↥(unitarySU 2 m K 3)) :=
      hTR (Subgroup.subset_closure ⟨a, haL, c, hc, hg⟩)
    have hg2 : g * g = 1 := by
      apply unitarySU_ext_mulVecLin
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mulVecLin_mul, hg,
        hermTransvection_comp (stdHermForm h 3) (hL.2 a haL)]
      rw [show c + c = 0 from CharTwo.add_self_eq_zero c, hermTransvection_zero]
      simp
    exact Subgroup.subset_closure ⟨hgR, by simpa [pow_two] using hg2⟩

theorem omegaOneOf_sylow_eq_isotropicTransvectionGroup (R : Sylow 2 ↥(unitarySU 2 m K 3)) :
    ∃ L ∈ isotropicLines h 3,
      omegaOneOf (R : Subgroup ↥(unitarySU 2 m K 3)) =
        isotropicTransvectionGroup h 3 L := by
  obtain ⟨L, hL, hZ, -⟩ := model3_unitary_center_eq_point h R
  exact ⟨L, hL, (omegaOneOf_sylow_eq_center h R).trans hZ⟩

theorem exists_sylow_omegaOneOf_eq_isotropicTransvectionGroup
    {L : Submodule K (Fin 3 → K)} (hL : L ∈ isotropicLines h 3) :
    ∃ R : Sylow 2 ↥(unitarySU 2 m K 3),
      omegaOneOf (R : Subgroup ↥(unitarySU 2 m K 3)) =
        isotropicTransvectionGroup h 3 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := h.finite
  obtain ⟨R₀⟩ := Sylow.nonempty (p := 2) (G := ↥(unitarySU 2 m K 3))
  obtain ⟨L₀, hL₀, hZ₀, -⟩ := model3_unitary_center_eq_point h R₀
  obtain ⟨g, hg⟩ := model3U4_trans h ⟨L₀, hL₀⟩ ⟨L, hL⟩
  have hker : (MulAut.conj g).toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (MulAut.conj g).toMonoidHom).mpr (MulAut.conj g).injective
  have hodd : Odd (Nat.card (MulAut.conj g).toMonoidHom.ker) := by
    rw [hker, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  refine ⟨Sylow.mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective R₀, ?_⟩
  have hg' : g • L₀ = L := by
    have h2 := congrArg Subtype.val hg
    rwa [SubMulAction.val_smul] at h2
  rw [Sylow.coe_mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective R₀,
    ← omegaOneOf_map_of_odd_ker (MulAut.conj g).toMonoidHom hodd R₀.isPGroup',
    omegaOneOf_sylow_eq_center h R₀, hZ₀, (unitary_point_conjugation h g hL₀).2.1, hg']

theorem eq_of_isotropicTransvectionGroup_eq {L L' : Submodule K (Fin 3 → K)}
    (hL : L ∈ isotropicLines h 3) (hL' : L' ∈ isotropicLines h 3)
    (hTL : isotropicTransvectionGroup h 3 L = isotropicTransvectionGroup h 3 L') : L = L' := by
  haveI : CharP K 2 := h.charP
  obtain ⟨a, ha0, ha, hLa⟩ := exists_eq_span_of_mem_isotropicLines hL
  obtain ⟨a', ha'0, ha', hL'a'⟩ := exists_eq_span_of_mem_isotropicLines hL'
  have h1mem : (1 : K) ∈ h.traceZero := by
    rw [UnitaryFieldData.mem_traceZero, UnitaryFieldData.trace, map_one]
    exact CharTwo.add_self_eq_zero 1
  have haL : a ∈ L := hLa.symm ▸ Submodule.mem_span_singleton_self a
  have haL' : a' ∈ L' := hL'a'.symm ▸ Submodule.mem_span_singleton_self a'
  obtain ⟨g, hgT, hg⟩ := exists_mem_isotropicTransvectionGroup h hL haL (c := 1) h1mem
  have hgT' : g ∈ isotropicTransvectionGroup h 3 L' := hTL ▸ hgT
  obtain ⟨-, -, hrange, -⟩ := unitary_point_subgroup h hL' haL' ha'0
  obtain ⟨c₀, hc₀⟩ := hrange ▸ hgT'
  have hlin : hermTransvection (stdHermForm h 3) a 1 =
      hermTransvection (stdHermForm h 3) a' c₀.toAdd := by
    rw [← hg, ← hc₀, mulVecLin_ptTransvectionHom]
  obtain ⟨x, hx⟩ := exists_stdHermForm_eq_one h ha0
  have ha_mem : a ∈ K ∙ a' := by
    have hev := LinearMap.congr_fun hlin x
    rw [hermTransvection_apply, hermTransvection_apply, hx] at hev
    simp only [one_mul, one_smul] at hev
    have h' : a = (c₀.toAdd * stdHermForm h 3 a' x) • a' := add_left_cancel hev
    rw [h']
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a')
  have hspan : K ∙ a ≤ K ∙ a' := (Submodule.span_singleton_le_iff_mem _ _).mpr ha_mem
  have hfin : Module.finrank K (K ∙ a) = Module.finrank K (K ∙ a') := by
    rw [finrank_span_singleton ha0, finrank_span_singleton ha'0]
  have hEq : K ∙ a = K ∙ a' := Submodule.eq_of_le_of_finrank_eq hspan hfin
  rw [hLa, hL'a', hEq]


private theorem hypFlag_one_mem_hypIsotropicLines (h : UnitaryFieldData 2 m K) :
    hypFlag h 1 1 1 ∈ hypIsotropicLines h 1 1 := by
  rw [mem_hypIsotropicLines,
    hypFlag_eq_posFlag h (le_rfl : 1 ≤ 1) (show 1 ≤ 2 * 1 + 1 by norm_num),
    finrank_posFlag (le_refl 1)]
  exact ⟨rfl, fun a ha => posFlag_isotropic h (le_rfl : 1 ≤ 1) a ha a ha⟩

private theorem map_hypBorel_eq_pointStabilizer
    {Rmat : Matrix (Fin (2 * 1 + 1)) (HypIndex 1 1) K} (hR : IsHypTransport h Rmat) :
    (hypBorel h 1 1).map (hypTransport h hR).toMonoidHom =
      MulAction.stabilizer ↥(unitarySU 2 m K 3)
        (transportSubspace h hR (hypFlag h 1 1 1)) := by
  ext g
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    have hb' : b ∈ hypBorel h 1 1 := hb
    rw [mem_hypBorel] at hb'
    change (hypTransport h hR) b • transportSubspace h hR (hypFlag h 1 1 1) =
      transportSubspace h hR (hypFlag h 1 1 1)
    rw [← transportSubspace_smul hR b (hypFlag h 1 1 1), hb' 1 le_rfl le_rfl]
  · intro hg
    obtain ⟨b, rfl⟩ := (hypTransport h hR).surjective g
    refine Subgroup.mem_map_of_mem _ ?_
    rw [mem_hypBorel]
    intro i hi1 hir
    obtain rfl : i = 1 := le_antisymm hir hi1
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [← transportSubspace_smul hR b (hypFlag h 1 1 1)] at hg
    exact (transportSubspace h hR).injective hg

private theorem eq_hypUnitriangular_of_isPGroup_le_hypBorel
    {Q : Subgroup (hypSU h 1 1)} (hQ : IsPGroup 2 Q) (hQB : Q ≤ hypBorel h 1 1)
    (hQcard : Nat.card Q = (2 ^ m) ^ 3) : Q = hypUnitriangular h 1 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := h.finite
  have hU2 : IsPGroup 2 (hypUnitriangular h 1 1) := by
    obtain ⟨-, ⟨P, hP⟩, -⟩ := unitary_order_and_Sylow h (r := 1) (ε := 1) le_rfl le_rfl
    rw [← hP]
    exact P.isPGroup'
  have hU2B : IsPGroup 2 ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)) :=
    hU2.comap_subtype
  have hUnorm : ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)).Normal :=
    normal_hypUnitriangular (h := h) (r := 1) (ε := 1) le_rfl
  have hcard : Nat.card (↥(hypBorel h 1 1) ⧸
      (hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)) = (2 ^ m) ^ 2 - 1 := by
    rw [card_quotient_hypUnitriangular (h := h) (r := 1) (ε := 1) le_rfl,
      range_hypDiagHom_odd (h := h) (r := 1) le_rfl, Subgroup.card_top, card_fun_units h 1]
    norm_num
  have hoddq : Odd ((2 ^ m) ^ 2 - 1) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact model3U4_not_two_dvd h
  have hodd : Odd ((hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1)).index := by
    rw [Subgroup.index_eq_card, hcard]
    exact hoddq
  let U₁ : Sylow 2 ↥(hypBorel h 1 1) :=
    hU2B.toSylow (Odd.not_two_dvd_nat hodd)
  have hU₁coe : (U₁ : Subgroup ↥(hypBorel h 1 1)) =
      (hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1) :=
    IsPGroup.toSylow_coe hU2B (Odd.not_two_dvd_nat hodd)
  letI : Unique (Sylow 2 ↥(hypBorel h 1 1)) :=
    Sylow.unique_of_normal U₁ (by rw [hU₁coe]; exact hUnorm)
  have hQ2 : IsPGroup 2 (Q.subgroupOf (hypBorel h 1 1)) := hQ.comap_subtype
  obtain ⟨Q', hQ'⟩ := hQ2.exists_le_sylow
  have hQ'eq : Q' = U₁ := Subsingleton.elim _ _
  have hle : Q.subgroupOf (hypBorel h 1 1) ≤
      (hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1) := by
    rw [← hU₁coe, ← hQ'eq]
    exact hQ'
  have hQle : Q ≤ hypUnitriangular h 1 1 := by
    intro x hx
    have hxQ : (⟨x, hQB hx⟩ : ↥(hypBorel h 1 1)) ∈
        Q.subgroupOf (hypBorel h 1 1) := Subgroup.mem_subgroupOf.mpr hx
    have hxU : (⟨x, hQB hx⟩ : ↥(hypBorel h 1 1)) ∈
        (hypUnitriangular h 1 1).subgroupOf (hypBorel h 1 1) := hle hxQ
    exact Subgroup.mem_subgroupOf.mp hxU
  refine Subgroup.eq_of_le_of_card_ge hQle ?_
  have hUcard : Nat.card (hypUnitriangular h 1 1) = (2 ^ m) ^ 3 := by
    rw [card_hypUnitriangular h le_rfl]
  rw [hUcard, hQcard]

private theorem eq_of_isPGroup_le_map_hypBorel {L : Submodule K (Fin 3 → K)}
    (e : hypSU h 1 1 ≃* ↥(unitarySU 2 m K 3))
    (hB : (hypBorel h 1 1).map e.toMonoidHom = MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    {S S' : Subgroup ↥(unitarySU 2 m K 3)} (hS : IsPGroup 2 S) (hS' : IsPGroup 2 S')
    (hSle : S ≤ MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    (hS'le : S' ≤ MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    (hScard : Nat.card S = (2 ^ m) ^ 3) (hS'card : Nat.card S' = (2 ^ m) ^ 3) : S = S' := by
  haveI : Finite K := h.finite
  have hS0 : S.map e.symm.toMonoidHom ≤ hypBorel h 1 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyB : y ∈ (hypBorel h 1 1).map e.toMonoidHom := hB ▸ hSle hy
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp hyB
    rw [← hyx, ← hbe]
    change e.symm (e b) ∈ hypBorel h 1 1
    rw [e.symm_apply_apply]
    exact hb
  have hS'0 : S'.map e.symm.toMonoidHom ≤ hypBorel h 1 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyB : y ∈ (hypBorel h 1 1).map e.toMonoidHom := hB ▸ hS'le hy
    obtain ⟨b, hb, hbe⟩ := Subgroup.mem_map.mp hyB
    rw [← hyx, ← hbe]
    change e.symm (e b) ∈ hypBorel h 1 1
    rw [e.symm_apply_apply]
    exact hb
  have hcardS : Nat.card (S.map e.symm.toMonoidHom) = (2 ^ m) ^ 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hScard]
  have hcardS' : Nat.card (S'.map e.symm.toMonoidHom) = (2 ^ m) ^ 3 := by
    rw [Subgroup.card_map_of_injective e.symm.injective, hS'card]
  have hEq : S.map e.symm.toMonoidHom = S'.map e.symm.toMonoidHom :=
    (eq_hypUnitriangular_of_isPGroup_le_hypBorel
      (IsPGroup.map hS e.symm.toMonoidHom) hS0 hcardS).trans
      (eq_hypUnitriangular_of_isPGroup_le_hypBorel
        (IsPGroup.map hS' e.symm.toMonoidHom) hS'0 hcardS').symm
  exact Subgroup.map_injective e.symm.injective hEq

theorem eq_of_isPGroup_le_pointStabilizer {L : Submodule K (Fin 3 → K)}
    (hL : L ∈ isotropicLines h 3) {S S' : Subgroup ↥(unitarySU 2 m K 3)}
    (hS : IsPGroup 2 S) (hS' : IsPGroup 2 S')
    (hSle : S ≤ MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    (hS'le : S' ≤ MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    (hScard : Nat.card S = (2 ^ m) ^ 3) (hS'card : Nat.card S' = (2 ^ m) ^ 3) : S = S' := by
  classical
  obtain ⟨Rmat, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let e : hypSU h 1 1 ≃* ↥(unitarySU 2 m K 3) := hypTransport h hR
  let L₀ : Submodule K (Fin 3 → K) := transportSubspace h hR (hypFlag h 1 1 1)
  have hL₀ : L₀ ∈ isotropicLines h 3 :=
    (transportSubspace_mem_isotropicLines hR _).mpr (hypFlag_one_mem_hypIsotropicLines h)
  have hB₀ : (hypBorel h 1 1).map e.toMonoidHom =
      MulAction.stabilizer ↥(unitarySU 2 m K 3) L₀ := map_hypBorel_eq_pointStabilizer hR
  obtain ⟨g, hg⟩ := model3U4_trans h ⟨L₀, hL₀⟩ ⟨L, hL⟩
  have hg' : g • L₀ = L := by
    have h2 := congrArg Subtype.val hg
    rwa [SubMulAction.val_smul] at h2
  refine eq_of_isPGroup_le_map_hypBorel (h := h) (L := L) (e := e.trans (MulAut.conj g)) ?_
    hS hS' hSle hS'le hScard hS'card
  have hfun : (e.trans (MulAut.conj g)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
    apply MonoidHom.ext
    intro b
    rfl
  rw [hfun, ← Subgroup.map_map, hB₀,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj g L₀, hg']

theorem eq_of_sylow_le_pointStabilizer {L : Submodule K (Fin 3 → K)}
    (hL : L ∈ isotropicLines h 3) {S S' : Sylow 2 ↥(unitarySU 2 m K 3)}
    (hS : (S : Subgroup ↥(unitarySU 2 m K 3)) ≤
      MulAction.stabilizer ↥(unitarySU 2 m K 3) L)
    (hS' : (S' : Subgroup ↥(unitarySU 2 m K 3)) ≤
      MulAction.stabilizer ↥(unitarySU 2 m K 3) L) : S = S' := by
  apply Sylow.ext
  exact eq_of_isPGroup_le_pointStabilizer hL S.isPGroup' S'.isPGroup' hS hS'
    (model3U4_card_sylow h S) (model3U4_card_sylow h S')

theorem eq_of_omegaOneOf_sylow_eq (h : UnitaryFieldData 2 m K)
    {R R' : Sylow 2 ↥(unitarySU 2 m K 3)}
    (hΩ : omegaOneOf (R : Subgroup ↥(unitarySU 2 m K 3)) =
      omegaOneOf (R' : Subgroup ↥(unitarySU 2 m K 3))) : R = R' := by
  obtain ⟨L, hL, hZ, hfix⟩ := model3_unitary_center_eq_point h R
  obtain ⟨L', hL', hZ', hfix'⟩ := model3_unitary_center_eq_point h R'
  have hZR : omegaOneOf (R : Subgroup ↥(unitarySU 2 m K 3)) =
      isotropicTransvectionGroup h 3 L :=
    (omegaOneOf_sylow_eq_center h R).trans hZ
  have hZR' : omegaOneOf (R' : Subgroup ↥(unitarySU 2 m K 3)) =
      isotropicTransvectionGroup h 3 L' :=
    (omegaOneOf_sylow_eq_center h R').trans hZ'
  have hT : isotropicTransvectionGroup h 3 L = isotropicTransvectionGroup h 3 L' := by
    rw [← hZR, hΩ, hZR']
  have hLL' : L = L' := eq_of_isotropicTransvectionGroup_eq hL hL' hT
  subst hLL'
  exact eq_of_sylow_le_pointStabilizer hL
    (fun g hg => MulAction.mem_stabilizer_iff.mpr (hfix g hg))
    (fun g hg => MulAction.mem_stabilizer_iff.mpr (hfix' g hg))


theorem exists_isotropic_sup_eq_top {L₁ L₂ : Submodule K (Fin 3 → K)}
    (h₁ : L₁ ∈ isotropicLines h 3) (h₂ : L₂ ∈ isotropicLines h 3) (hne : L₁ ≠ L₂) :
    ∃ L₃ ∈ isotropicLines h 3, L₁ ⊔ L₂ ⊔ L₃ = ⊤ := by
  classical
  haveI : CharP K 2 := h.charP
  haveI : Finite K := h.finite
  haveI : Fintype K := Fintype.ofFinite K
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have hcard : Nat.card (Units.map h.normHom).ker = 2 ^ m + 1 :=
    h.card_ker_normUnits_and_surjective.1
  have hcard' : Fintype.card ↥(Units.map h.normHom).ker = 2 ^ m + 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hlt : 1 < Fintype.card ↥(Units.map h.normHom).ker := by
    rw [hcard']
    exact Nat.lt_succ_iff.mpr (Nat.one_le_pow m 2 (by norm_num))
  obtain ⟨u, hu1⟩ :=
    Fintype.exists_ne_of_one_lt_card hlt (1 : ↥(Units.map h.normHom).ker)
  have hnorm : h.norm (((u : Kˣ) : K)) = 1 := by
    have hu := u.2
    rwa [UnitaryFieldData.mem_ker_normUnits] at hu
  have ht1 : (((u : Kˣ) : K)) ≠ 1 := by
    intro hc
    apply hu1
    exact Subtype.ext (Units.ext hc)
  let t : K := ((u : Kˣ) : K)
  let C : Fin 3 → K := ![t, 1, 0]
  let A : Fin 3 → K := ![1, 1, 0]
  let B : Fin 3 → K := ![0, 1, 1]
  have ht_norm : h.norm t = 1 := hnorm
  have ht1' : t ≠ 1 := ht1
  have hC0 : C ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp [C] at this
  have hCiso : stdHermForm h 3 C C = 0 := by
    have hb : h.bar t * t = 1 := by
      rw [mul_comm]
      exact ht_norm
    simp [stdHermForm_apply, C, Fin.sum_univ_three, hb, h2]
  have hAiso : stdHermForm h 3 A A = 0 := by
    simp [stdHermForm_apply, A, Fin.sum_univ_three, h2]
  have hBiso : stdHermForm h 3 B B = 0 := by
    simp [stdHermForm_apply, B, Fin.sum_univ_three, h2]
  have hA0 : A ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [A] at this
  have hB0 : B ≠ 0 := by
    intro h0
    have := congrFun h0 1
    simp [B] at this
  have hAC : K ∙ A ∈ isotropicLines h 3 := span_mem_isotropicLines hA0 hAiso
  have hBC : K ∙ B ∈ isotropicLines h 3 := span_mem_isotropicLines hB0 hBiso
  have hCC : K ∙ C ∈ isotropicLines h 3 := span_mem_isotropicLines hC0 hCiso
  have hAB : (⟨K ∙ A, hAC⟩ : isotropicLines h 3) ≠ ⟨K ∙ B, hBC⟩ := by
    intro hEq
    have hval : (K ∙ A : Submodule K (Fin 3 → K)) = K ∙ B :=
      congrArg (fun L : isotropicLines h 3 => (L : Submodule K (Fin 3 → K))) hEq
    have hmem : (A : Fin 3 → K) ∈ (K ∙ B : Submodule K (Fin 3 → K)) := by
      rw [← hval]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := congrFun hc 0
    simp [A, B] at this
  let e₀ : Fin 3 → K := ![1, 0, 0]
  let e₁ : Fin 3 → K := ![0, 1, 0]
  let e₂ : Fin 3 → K := ![0, 0, 1]
  let S : Submodule K (Fin 3 → K) := K ∙ A ⊔ K ∙ B ⊔ K ∙ C
  have hA : A ∈ S :=
    Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
  have hB : B ∈ S :=
    Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have hC : C ∈ S := Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have htne : t + 1 ≠ 0 := fun h0 => ht1' (CharTwo.add_eq_zero.mp h0)
  have hCA : C + A = (t + 1) • e₀ := by
    ext i
    fin_cases i <;> simp [C, A, e₀, h2]
  have hAe₀ : A + e₀ = e₁ := by
    ext i
    fin_cases i <;> simp [A, e₀, e₁, h2]
  have hBe₁ : B + e₁ = e₂ := by
    ext i
    fin_cases i <;> simp [B, e₁, e₂, h2]
  have he₀ : e₀ ∈ S := by
    have hsum : C + A ∈ S := Submodule.add_mem _ hC hA
    rw [hCA] at hsum
    have hsm := Submodule.smul_mem S ((t + 1)⁻¹) hsum
    rwa [smul_smul, inv_mul_cancel₀ htne, one_smul] at hsm
  have he₁ : e₁ ∈ S := by
    have hsum : A + e₀ ∈ S := Submodule.add_mem _ hA he₀
    rwa [hAe₀] at hsum
  have he₂ : e₂ ∈ S := by
    have hsum : B + e₁ ∈ S := Submodule.add_mem _ hB he₁
    rwa [hBe₁] at hsum
  have hs₀ : (Pi.single 0 (1 : K) : Fin 3 → K) = e₀ := by
    funext i
    fin_cases i <;> simp [e₀]
  have hs₁ : (Pi.single 1 (1 : K) : Fin 3 → K) = e₁ := by
    funext i
    fin_cases i <;> simp [e₁]
  have hs₂ : (Pi.single 2 (1 : K) : Fin 3 → K) = e₂ := by
    funext i
    fin_cases i <;> simp [e₂]
  have hspan : K ∙ A ⊔ K ∙ B ⊔ K ∙ C = ⊤ := by
    rw [Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K (Fin 3))]
    intro i
    fin_cases i
    · rw [Pi.basisFun_apply]
      change (Pi.single 0 (1 : K) : Fin 3 → K) ∈ S
      rw [hs₀]
      exact he₀
    · rw [Pi.basisFun_apply]
      change (Pi.single 1 (1 : K) : Fin 3 → K) ∈ S
      rw [hs₁]
      exact he₁
    · rw [Pi.basisFun_apply]
      change (Pi.single 2 (1 : K) : Fin 3 → K) ∈ S
      rw [hs₂]
      exact he₂
  have hne' : (⟨L₁, h₁⟩ : isotropicLines h 3) ≠ ⟨L₂, h₂⟩ := by
    intro hEq
    exact hne (congrArg Subtype.val hEq)
  obtain ⟨g, hgA, hgB⟩ := model3U4_two_trans h ⟨L₁, h₁⟩ ⟨L₂, h₂⟩
    ⟨K ∙ A, hAC⟩ ⟨K ∙ B, hBC⟩ hne' hAB
  let L₃ : Submodule K (Fin 3 → K) := g⁻¹ • (K ∙ C)
  have hL₃ : L₃ ∈ isotropicLines h 3 := by
    have hm := (isotropicLines h 3).smul_mem g⁻¹ hCC
    simpa [L₃] using hm
  refine ⟨L₃, hL₃, ?_⟩
  let f : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    Matrix.mulVecLin (((g : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Matrix.mulVec_injective_of_invertible
      (A := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
    simpa [f, Matrix.mulVecLin_apply] using hxy
  have hmapA : L₁.map f = K ∙ A := by
    have h := congrArg Subtype.val hgA
    rw [SubMulAction.val_smul, Subgroup.smul_def, smul_eq_map] at h
    simpa [f] using h
  have hmapB : L₂.map f = K ∙ B := by
    have h := congrArg Subtype.val hgB
    rw [SubMulAction.val_smul, Subgroup.smul_def, smul_eq_map] at h
    simpa [f] using h
  have hmapC : L₃.map f = K ∙ C := by
    have hL₃eq : L₃ = (K ∙ C).map
        (Matrix.mulVecLin (((g⁻¹ : ↥(unitarySU 2 m K 3)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) := by
      show g⁻¹ • (K ∙ C) = (K ∙ C).map
        (Matrix.mulVecLin (((g⁻¹ : ↥(unitarySU 2 m K 3)) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K))
      rw [Subgroup.smul_def, smul_eq_map]
    rw [hL₃eq, ← Submodule.map_comp, ← Matrix.mulVecLin_mul]
    rw [show ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((g⁻¹ : ↥(unitarySU 2 m K 3)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (1 : Matrix (Fin 3) (Fin 3) K) from by
      rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
        Units.val_one]]
    rw [Matrix.mulVecLin_one, Submodule.map_id]
  have htop : (L₁ ⊔ L₂ ⊔ L₃).map f = ⊤ := by
    rw [Submodule.map_sup, Submodule.map_sup, hmapA, hmapB, hmapC, hspan]
  have htop' : (L₁ ⊔ L₂ ⊔ L₃).map f = (⊤ : Submodule K (Fin 3 → K)).map f := by
    rw [htop, Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hf_inj)]
  exact Submodule.map_injective_of_injective hf_inj htop'

end CFSG.ClassicalGroups.UnitaryFlag

end

module

public import CFSG.LargeExtraspecial.DW3Data
public import CFSG.LargeExtraspecial.DWTransCaseI
public import CFSG.LargeExtraspecial.TSComplements
public import CFSG.LargeExtraspecial.SettingRhoM
public import CFSG.Quasithin.Vol2.Ch6GL32Parab
public import CFSG.GroupTheory.SimpleGroupActionFixedPoint

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Subgroup Module QuadraticMap CFSG.GroupTheory.GLnTwoSplitting
  CFSG.RankThree.Literature.FSmith

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {A : Subgroup G}
  [IsElementaryAbelian 2 A]

namespace MaxEA

theorem exists_mem_conjSub_inf_not_mem_QG (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) (h2 : 2 ≤ S.width) :
    ∃ y : G, y ∈ conjSub A h ⊓ S.M ∧ y ∉ S.QG := by
  by_contra hno
  push Not at hno
  have hle : ((conjSub A h ⊓ S.M : Subgroup G) : Subgroup G) ≤ S.QG := fun y hy => hno y hy
  have hsub : (((conjSub A h ⊓ S.M : Subgroup G) : Subgroup G) : Set G) ⊆
      ({1, h * S.z * h⁻¹} : Set G) := by
    intro y hy
    rcases hA.eq_of_mem_conjSub_of_mem_QG hM hxQ hxA hy.1 (hle hy) with rfl | rfl <;> simp
  have hcard := hA.card_conjSub_inf_M_ge hxQ hxA
  have hpow : 2 ^ 2 ≤ 2 ^ S.width := Nat.pow_le_pow_right (by norm_num) h2
  have hsmall : Nat.card (conjSub A h ⊓ S.M : Subgroup G) ≤ 2 := by
    calc Nat.card (conjSub A h ⊓ S.M : Subgroup G)
        = (((conjSub A h ⊓ S.M : Subgroup G) : Subgroup G) : Set G).ncard :=
          Nat.card_coe_set_eq _
      _ ≤ ({1, h * S.z * h⁻¹} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          have h1 := Set.ncard_insert_le (1 : G) ({h * S.z * h⁻¹} : Set G)
          have h2 := Set.ncard_singleton (h * S.z * h⁻¹)
          omega
  omega

theorem exists_involution_of_not_mem (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) (h2 : 2 ≤ S.width) :
    ∃ y : G, y ∈ conjSub A h ⊓ S.M ∧ y ∉ S.QG ∧ y * y = 1 ∧
      y * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * y := by
  obtain ⟨y, hyC, hyQ⟩ := hA.exists_mem_conjSub_inf_not_mem_QG hM hxQ hxA h2
  have hyx : h * S.z * h⁻¹ ∈ conjSub A h := conj_mem_conjSub hA.z_mem
  refine ⟨y, hyC, hyQ, ?_, MaxEA.comm_of_mem (A := conjSub A h) hyC.1 hyx⟩
  simpa [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) y hyC.1

private noncomputable def axisKernelImage (S : Setting G) (A : Subgroup G) (h : G) :
    Submodule (ZMod 2) S.Qt :=
  (LinearMap.ker (axisForm S A (h * S.z * h⁻¹))).map (S.clSub A).subtype

private noncomputable def caseISub (S : Setting G) (A : Subgroup G) (h : G) :
    Submodule (ZMod 2) S.Qt :=
  axisKernelImage S A h ⊔ Submodule.span (ZMod 2) {S.cl (h * S.z * h⁻¹)}

private theorem axisKernelImage_le_clSub (S : Setting G) (A : Subgroup G) (h : G) :
    axisKernelImage S A h ≤ S.clSub A := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := Submodule.mem_map.mp hv
  exact w.2

private theorem cl_conj_notMem_clSub (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    S.cl (h * S.z * h⁻¹) ∉ S.clSub A := by
  intro hv
  exact hxA (by rw [← hA.clPre_clSub]; exact ⟨hxQ, hv⟩)

private theorem polar_axisKernelImage {h : G}
    {v : S.Qt} (hv : v ∈ axisKernelImage S A h) :
    polar S.q v (S.cl (h * S.z * h⁻¹)) = 0 := by
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
  have h := LinearMap.mem_ker.mp hu
  rw [axisForm_apply] at h
  exact h

private theorem axisKernelImage_inf_span (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    axisKernelImage S A h ⊓ Submodule.span (ZMod 2) {S.cl (h * S.z * h⁻¹)} = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  have hvA : v ∈ S.clSub A := axisKernelImage_le_clSub S A h hv.1
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv.2
  rcases zmod2_cases c with h0 | h1
  · rw [h0, zero_smul] at hc
    exact hc.symm
  · rw [h1, one_smul] at hc
    exact absurd (hc.symm ▸ hvA) (hA.cl_conj_notMem_clSub hxQ hxA)

private theorem finrank_axisKernelImage (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    finrank (ZMod 2) (axisKernelImage S A h) = S.width - 1 := by
  have hfin := (Submodule.equivMapOfInjective (S.clSub A).subtype
    (S.clSub A).subtype_injective
    (LinearMap.ker (axisForm S A (h * S.z * h⁻¹)))).finrank_eq
  change finrank (ZMod 2) (Submodule.map (S.clSub A).subtype
    (LinearMap.ker (axisForm S A (h * S.z * h⁻¹)))) = S.width - 1
  rw [← hfin, hA.finrank_ker_axisForm hxQ hxA]

private theorem finrank_caseISub (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) (h2 : 2 ≤ S.width) :
    finrank (ZMod 2) (caseISub S A h) = S.width := by
  have hx0 : S.cl (h * S.z * h⁻¹) ≠ 0 := fun h0 =>
    hA.cl_conj_notMem_clSub hxQ hxA (h0 ▸ Submodule.zero_mem _)
  have hspan : finrank (ZMod 2) (Submodule.span (ZMod 2) {S.cl (h * S.z * h⁻¹)}) = 1 :=
    finrank_span_singleton hx0
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (axisKernelImage S A h)
    (Submodule.span (ZMod 2) {S.cl (h * S.z * h⁻¹)})
  rw [hA.axisKernelImage_inf_span hxQ hxA, finrank_bot, add_zero,
    hA.finrank_axisKernelImage hxQ hxA, hspan] at hsup
  change finrank (ZMod 2) ↥(axisKernelImage S A h ⊔
    Submodule.span (ZMod 2) {S.cl (h * S.z * h⁻¹)}) = S.width
  rw [hsup]
  omega

private theorem q_caseISub (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) :
    ∀ v ∈ caseISub S A h, S.q v = 0 := by
  intro v hv
  rw [caseISub, Submodule.mem_sup] at hv
  obtain ⟨a, ha, b, hb, rfl⟩ := hv
  have haq : S.q a = 0 := q_clSub (A := A) (axisKernelImage_le_clSub S A h ha)
  have hbq : S.q b = 0 := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    rcases zmod2_cases c with h0 | h1
    · rw [h0, zero_smul] at hc
      rw [← hc, QuadraticMap.map_zero]
    · rw [h1, one_smul] at hc
      rw [← hc]
      exact (S.q_cl_eq_zero_iff hxQ).mpr (by
        simpa [pow_two] using mul_self_of_mem (A := conjSub A h) (conj_mem_conjSub hA.z_mem))
  have hpolar : polar S.q a b = 0 := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
    rcases zmod2_cases c with h0 | h1
    · rw [h0, zero_smul] at hc
      rw [← hc, QuadraticMap.polar_zero_right]
    · rw [h1, one_smul] at hc
      rw [← hc]
      exact polar_axisKernelImage ha
  rw [QuadraticMap.map_add S.q a b, haq, hbq, hpolar]
  simp

private theorem caseISub_maxEA (hA : MaxEA S A) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) (h2 : 2 ≤ S.width) :
    MaxEA S (S.clPre (caseISub S A h)) := by
  have hw := hA.finrank_caseISub hxQ hxA h2
  refine ⟨S.clPre_le_QG _, ?_⟩
  rw [S.card_clPre, S.card_submodule, hw, ← pow_succ']

private theorem centralizes_caseISub (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
    {y : G} (hyC : y ∈ conjSub A h ⊓ S.M) :
    ∀ b ∈ S.clPre (caseISub S A h), y * b = b * y := by
  intro b hb
  let x : G := h * S.z * h⁻¹
  have hxQ' : x ∈ S.QG := hxQ
  have hxA' : x ∉ A := hxA
  have hyz : y * S.z = S.z * y := S.z_comm hyC.2
  have hyx : y * x = x * y :=
    MaxEA.comm_of_mem (A := conjSub A h) hyC.1 (conj_mem_conjSub hA.z_mem)
  have hbcl : S.cl b ∈ caseISub S A h := hb.2
  rw [caseISub, Submodule.mem_sup] at hbcl
  obtain ⟨w, hw, t, ht, hwt⟩ := hbcl
  obtain ⟨u, hu, huw⟩ := Submodule.mem_map.mp hw
  obtain ⟨a, haA, haQ, hacl⟩ := S.mem_clSub_iff.mp u.2
  have hacw : S.cl a = w := by
    rw [hacl]
    exact huw
  have huw' : (u : S.Qt) = w := huw
  have hφ : polar S.q w (S.cl x) = 0 := by
    have h := LinearMap.mem_ker.mp hu
    rw [axisForm_apply] at h
    change polar S.q (u : S.Qt) (S.cl x) = 0 at h
    rwa [huw'] at h
  have hφa : polar S.q (S.cl a) (S.cl x) = 0 := by rwa [← hacw] at hφ
  have hax : a * x = x * a := (S.polar_cl_eq_zero_iff haQ hxQ').mp hφa
  have hya : y * a = a * y :=
    (hA.commute_of_commute hM hxQ hxA haA hax hyC.1 hyz).symm
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ht
  rcases zmod2_cases c with h0 | h1
  · have ht0 : t = 0 := by rw [← hc, h0, zero_smul]
    have hclb : S.cl b = S.cl a := by rw [← hwt, ht0, add_zero, hacw]
    rcases (S.cl_eq_cl_iff haQ hb.1).mp hclb.symm with h | h
    · rw [h]; exact hya
    · rw [h]
      calc y * (a * S.z) = (y * a) * S.z := by rw [mul_assoc]
        _ = (a * y) * S.z := by rw [hya]
        _ = a * (y * S.z) := by rw [mul_assoc]
        _ = a * (S.z * y) := by rw [hyz]
        _ = (a * S.z) * y := by rw [mul_assoc]
  · have ht1 : t = S.cl x := by rw [← hc, h1, one_smul]
    have hclb : S.cl b = S.cl (a * x) := by
      rw [← hwt, ht1, ← hacw, ← S.cl_mul haQ hxQ']
    have haxQ : a * x ∈ S.QG := S.QG.mul_mem haQ hxQ'
    have hyax : y * (a * x) = (a * x) * y := by
      calc y * (a * x) = (y * a) * x := by rw [mul_assoc]
        _ = (a * y) * x := by rw [hya]
        _ = a * (y * x) := by rw [mul_assoc]
        _ = a * (x * y) := by rw [hyx]
        _ = (a * x) * y := by rw [← mul_assoc]
    rcases (S.cl_eq_cl_iff haxQ hb.1).mp hclb.symm with h | h
    · rw [h]; exact hyax
    · rw [h]
      calc y * ((a * x) * S.z) = (y * (a * x)) * S.z :=
            (mul_assoc y (a * x) S.z).symm
        _ = ((a * x) * y) * S.z := by rw [hyax]
        _ = (a * x) * (y * S.z) := mul_assoc (a * x) y S.z
        _ = (a * x) * (S.z * y) := by rw [hyz]
        _ = ((a * x) * S.z) * y := (mul_assoc (a * x) S.z y).symm

theorem exists_involution_maxEA_of_not_mem (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) (h2 : 2 ≤ S.width) :
    ∃ y : G, y ∈ conjSub A h ∧ y ∈ S.M ∧ y ∉ S.QG ∧ y * y = 1 ∧
      ∃ A' : Subgroup G, IsElementaryAbelian 2 A' ∧ MaxEA S A' ∧
        ∀ a ∈ A', y * a = a * y := by
  obtain ⟨y, hyC, hyQ, hy2, -⟩ :=
    hA.exists_involution_of_not_mem hM hxQ hxA h2
  refine ⟨y, hyC.1, hyC.2, hyQ, hy2, S.clPre (caseISub S A h), ?_,
    hA.caseISub_maxEA hxQ hxA h2, hA.centralizes_caseISub hM hxQ hxA hyC⟩
  exact CFSG.LargeExtraspecial.DW.W4.isElementaryAbelian_clPre
    (hA.q_caseISub hxQ)

@[expose, instance_reducible] noncomputable def tsComplAction (hM : S.M ≤ normalizer (A : Set G)) :
    MulAction S.Mbar (tsCompl S.q (S.clSub A)) where
  smul g W :=
    ⟨W.1.map (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt), by
      haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
      exact map_mem_tsCompl (((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
        (fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (g : S.O).2 v)
        (fun u hu => apply_mem_clSub hM g.2 hu) W.2⟩
  one_smul W := by
    apply Subtype.ext
    show W.1.map (↑(((1 : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
      S.Qt →ₗ[ZMod 2] S.Qt) = W.1
    rw [show ((((1 : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) =
      (1 : S.Qt →ₗ[ZMod 2] S.Qt) from rfl]
    exact Submodule.map_id W.1
  mul_smul g h W := by
    apply Subtype.ext
    show W.1.map (↑((((g * h : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
        S.Qt →ₗ[ZMod 2] S.Qt) =
      (W.1.map (↑(((h : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt →ₗ[ZMod 2] S.Qt)).map
        (↑(((g : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) : S.Qt →ₗ[ZMod 2] S.Qt)
    rw [← Submodule.map_comp]
    congr 1

private theorem mem_normalizer_Qa_of_mem_M {h y : G}
    (hyx : y * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * y) :
    y ∈ normalizer (S.Qa h : Set G) := by
  have hyM : y ∈ (S.conjBy h).M := by
    rw [(S.conjBy h).mem_M_iff, Setting.conjBy_z]
    exact hyx
  exact (S.conjBy h).M_le_normalizer_QG hyM

private theorem clSub_inf_mem_tsCompl (hA : MaxEA S A)
    (hM : S.M ≤ normalizer (A : Set G)) {h : G}
    (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A) :
    S.clSub (S.QG ⊓ S.Qa h) ∈ tsCompl S.q (S.clSub A) := by
  haveI : IsElementaryAbelian 2 (S.QG ⊓ S.Qa h : Subgroup G) :=
    S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  have hB := hA.maxEA_inf hM hxQ hxA
  constructor
  · refine IsCompl.of_eq ?_ ?_
    · rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_bot]
      exact hA.eq_zero_of_mem_clSub_inf hM hxQ hxA hv.2 hv.1
    · rw [eq_top_iff]
      intro v _
      obtain ⟨b, hb, hsub⟩ := hA.exists_sub_mem hM hxQ hxA v
      have hv : v = (v - b) + b := by abel
      rw [hv]
      exact Submodule.mem_sup.mpr ⟨v - b, hsub, b, hb, rfl⟩
  · intro w hw
    exact q_clSub (A := S.QG ⊓ S.Qa h) hw

private theorem map_clSub_inf_eq_of_mem_normalizer {h y : G} (hyM : y ∈ S.M)
    (hyx : y * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * y) :
    (S.clSub (S.QG ⊓ S.Qa h)).map
      (((⟨y, hyM⟩ : S.M) |> S.ρ) : S.Qt →ₗ[ZMod 2] S.Qt) =
      S.clSub (S.QG ⊓ S.Qa h) := by
  have hyQ := S.M_le_normalizer_QG hyM
  have hyQa := mem_normalizer_Qa_of_mem_M (S := S) hyx
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨b, hb, hbQ, hbv⟩ := S.mem_clSub_iff.mp hv
    rw [← hbv]
    have hybQ : y * b * y⁻¹ ∈ S.QG := (mem_normalizer_iff.mp hyQ b).mp hbQ
    have hybQa : y * b * y⁻¹ ∈ S.Qa h := (mem_normalizer_iff.mp hyQa b).mp hb.2
    change ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl b) ∈
      S.clSub (S.QG ⊓ S.Qa h)
    rw [S.ρ_cl ⟨y, hyM⟩ hbQ]
    exact S.cl_mem_clSub ⟨hybQ, hybQa⟩ hybQ
  · intro v hv
    obtain ⟨b, hb, hbQ, hbv⟩ := S.mem_clSub_iff.mp hv
    rw [← hbv]
    have hybQ : y⁻¹ * b * y ∈ S.QG := by
      simpa using (mem_normalizer_iff.mp (Subgroup.inv_mem _ hyQ) b).mp hbQ
    have hybQa : y⁻¹ * b * y ∈ S.Qa h := by
      simpa using (mem_normalizer_iff.mp (Subgroup.inv_mem _ hyQa) b).mp hb.2
    refine ⟨S.cl (y⁻¹ * b * y), S.cl_mem_clSub ⟨hybQ, hybQa⟩ hybQ, ?_⟩
    change ((S.ρ ⟨y, hyM⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (y⁻¹ * b * y)) = S.cl b
    rw [S.ρ_cl ⟨y, hyM⟩ hybQ]
    congr 1
    group



private theorem rhoM_smul_B (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
    {y : G} (hyC : y ∈ conjSub A h ⊓ S.M) :
    (tsComplAction (S := S) (A := A) hM).smul (S.ρM ⟨y, hyC.2⟩)
      ⟨S.clSub (S.QG ⊓ S.Qa h), hA.clSub_inf_mem_tsCompl hM hxQ hxA⟩ =
      ⟨S.clSub (S.QG ⊓ S.Qa h), hA.clSub_inf_mem_tsCompl hM hxQ hxA⟩ := by
  apply Subtype.ext
  have hyx : y * (h * S.z * h⁻¹) = (h * S.z * h⁻¹) * y :=
    MaxEA.comm_of_mem (A := conjSub A h) hyC.1 (conj_mem_conjSub hA.z_mem)
  change (S.clSub (S.QG ⊓ S.Qa h)).map
      (↑(((S.ρM ⟨y, hyC.2⟩ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
        S.Qt →ₗ[ZMod 2] S.Qt) = S.clSub (S.QG ⊓ S.Qa h)
  rw [show (((S.ρM ⟨y, hyC.2⟩ : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (((S.ρ ⟨y, hyC.2⟩ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) from rfl]
  exact map_clSub_inf_eq_of_mem_normalizer hyC.2 hyx

private theorem rhoM_sq_eq_one_of_sq_eq_one {y : G} (hyM : y ∈ S.M) (hy2 : y * y = 1) :
    S.ρM ⟨y, hyM⟩ * S.ρM ⟨y, hyM⟩ = 1 := by
  have hy2M : (⟨y, hyM⟩ : S.M) * ⟨y, hyM⟩ = 1 := by
    apply Subtype.ext
    simpa [pow_two] using hy2
  rw [← map_mul, hy2M, map_one]


theorem exists_hyp_of_not_mem (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
    (hw : S.width = 3) :
    ∃ W₂ : Submodule (ZMod 2) S.Qt, ∃ H : W3.Hyp S (S.clSub A) W₂,
      Function.Surjective H.res := by
  letI : MulAction S.Mbar (tsCompl S.q (S.clSub A)) := tsComplAction (S := S) (A := A) hM
  have h2w : 2 ≤ S.width := by omega
  obtain ⟨y, hyC, hyQ, hy2, -⟩ := hA.exists_involution_of_not_mem hM hxQ hxA h2w
  let B : Submodule (ZMod 2) S.Qt := S.clSub (S.QG ⊓ S.Qa h)
  have hBmem : B ∈ tsCompl S.q (S.clSub A) := hA.clSub_inf_mem_tsCompl hM hxQ hxA
  obtain ⟨e⟩ := hA.nonempty_Mbar_mulEquiv_of_not_mem hM hxQ hxA
  rw [hw] at e
  haveI : IsSimpleGroup (GL (Fin 3) (ZMod 2)) :=
    CFSG.Quasithin.H13.L619.isSimpleGroup_GL_zmod_two (by norm_num)
  haveI : IsSimpleGroup S.Mbar := MulEquiv.isSimpleGroup e
  have hcardMbar : Nat.card S.Mbar = 168 := by
    rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.H13.L619.card_GL32]
  let x₀ : tsCompl S.q (S.clSub A) := ⟨B, hBmem⟩
  have hstab : S.ρM ⟨y, hyC.2⟩ ∈ MulAction.stabilizer S.Mbar x₀ := by
    rw [MulAction.mem_stabilizer_iff]
    change (tsComplAction (S := S) (A := A) hM).smul (S.ρM ⟨y, hyC.2⟩) x₀ = x₀
    exact rhoM_smul_B hA hM hxQ hxA hyC
  have hne : S.ρM ⟨y, hyC.2⟩ ≠ 1 := by
    intro h1
    rw [S.ρM_eq_one_iff] at h1
    exact hyQ h1
  have hsq : S.ρM ⟨y, hyC.2⟩ * S.ρM ⟨y, hyC.2⟩ = 1 :=
    rhoM_sq_eq_one_of_sq_eq_one hyC.2 hy2
  have hord : orderOf (S.ρM ⟨y, hyC.2⟩) = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using hsq) hne
  have h2dvd : 2 ∣ Nat.card (MulAction.stabilizer S.Mbar x₀) := by
    let g : MulAction.stabilizer S.Mbar x₀ := ⟨S.ρM ⟨y, hyC.2⟩, hstab⟩
    have hg : orderOf g = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    have hdiv : orderOf g ∣ Nat.card (MulAction.stabilizer S.Mbar x₀) :=
      orderOf_dvd_natCard g
    rwa [hg] at hdiv
  haveI : FiniteDimensional (ZMod 2) S.Qt := Module.Finite.of_finite
  haveI : IsElementaryAbelian 2 (S.QG ⊓ S.Qa h : Subgroup G) :=
    S.isElementaryAbelian_QG_inf_Qa (hA.conj_ne_z hxA)
  have hXcard : Nat.card (tsCompl S.q (S.clSub A)) = 8 := by
    refine card_tsCompl_eq_eight S.q_nondegenerate hBmem.1 (fun u hu => q_clSub hu)
      (fun b hb => q_clSub (A := S.QG ⊓ S.Qa h) hb) ?_
    rw [hA.finrank_clSub, hw]
  obtain ⟨W₂, hW₂fix⟩ :=
    CFSG.GroupTheory.exists_fixed_of_card_eq_168 hcardMbar hXcard x₀ h2dvd
  let H : W3.Hyp S (S.clSub A) W₂ :=
    { compl := W₂.2.1
      inv₁ := fun m w hw => MaxEA.apply_mem_clSub hM ⟨m, rfl⟩ hw
      inv₂ := fun m w hw => by
        have hsmul : W₂.1.map
            (↑(((S.ρM m : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) :
              S.Qt →ₗ[ZMod 2] S.Qt) = W₂.1 :=
          congrArg Subtype.val (hW₂fix (S.ρM m))
        have hmem : (((S.ρM m : S.Mbar) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W₂.1 := by
          rw [← hsmul]
          exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
        simpa [S.coe_ρM m] using hmem
      ts₁ := fun w hw => q_clSub (A := A) hw
      ts₂ := fun w hw => W₂.2.2 w hw
      width := hw }
  have hres_eq : ∀ m : S.M, H.res m = resAt S A hM (S.ρM m) := by
    intro m
    refine LinearEquiv.ext fun u => Subtype.ext ?_
    rw [H.coe_res_apply, coe_resAt_apply]
    rfl
  refine ⟨W₂, H, ?_⟩
  intro f
  obtain ⟨x, hx⟩ := (hA.resAt_bijective_of_not_mem hM hxQ hxA).2 f
  obtain ⟨m, rfl⟩ := S.ρM_surjective x
  exact ⟨m, by rw [hres_eq m]; exact hx⟩


theorem exists_split_of_not_mem (hA : MaxEA S A) (hM : S.M ≤ normalizer (A : Set G))
    {h : G} (hxQ : h * S.z * h⁻¹ ∈ S.QG) (hxA : h * S.z * h⁻¹ ∉ A)
    (hw : S.width = 3) :
    ∃ (W₁ W₂ : Submodule (ZMod 2) S.Qt) (H : W3.Hyp S W₁ W₂),
      Function.Surjective H.res ∧
        ∃ x : G, x ∈ S.M ∧ x ∉ S.QG ∧ x * x = 1 ∧
          ∃ A' : Subgroup G, IsElementaryAbelian 2 A' ∧ MaxEA S A' ∧
            ∀ a ∈ A', x * a = a * x := by
  obtain ⟨W₂, H, hH⟩ := hA.exists_hyp_of_not_mem hM hxQ hxA hw
  obtain ⟨y, hyC, hyM, hyQ, hy2, A', hA'el, hA'max, hA'c⟩ :=
    hA.exists_involution_maxEA_of_not_mem hM hxQ hxA (by omega : 2 ≤ S.width)
  exact ⟨S.clSub A, W₂, H, hH, y, hyM, hyQ, hy2, A', hA'el, hA'max, hA'c⟩

end MaxEA

end CFSG.LargeExtraspecial.DW

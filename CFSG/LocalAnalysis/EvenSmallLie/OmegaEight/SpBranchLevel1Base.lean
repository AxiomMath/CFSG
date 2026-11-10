
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSetting
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAut
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1CheckBase

@[expose] public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

attribute [local irreducible] sAct sMt sGinv p9List p9Index a9LinTab a9CoTab sNfTab sMTab sKOrb
  sCanon sTree sInvList sY sLeavesLit fpArr

variable {G : Type*} [Group G]

def tCode : Eps → ℕ
  | .plus => 64
  | .minus => 75

def tInv : Eps → ℕ × ℕ
  | .plus => (1439, 10336)
  | .minus => (1439, 9312)

theorem tM_code (ε : Eps) : (SModel.tM ε).code = tCode ε := by cases ε <;> rfl

theorem mem_sMarked (ε : Eps) : (tCode ε, tInv ε) ∈ sMarked := by
  cases ε <;> simp [sMarked, tCode, tInv]

noncomputable def sIso {S : Subgroup G}
    (e : S ≃* SModel) : CodeIso S 65536 sMul :=
  SModel.codeIso.ofEquiv e

theorem sIso_f {S : Subgroup G} (e : S ≃* SModel) (s : S) :
    (sIso e).f s = (e s).code := rfl

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem not_max_S
    [Finite G] (hH : Hyp ε t TH E₁ S)
    (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) :
    ¬ ∀ P : Subgroup G, IsPGroup 2 P → S ≤ P → P = S := by
  obtain ⟨e, he⟩ := hH.sylow.iso
  have hS := t1Enum_check
  unfold t1EnumCheck at hS
  simp only [Bool.and_eq_true] at hS
  obtain ⟨hinv, hcls, hchi, hts⟩ := groupKillC_spec hS.2
  have htS : t ∈ S := hH.t_mem_S
  have hft : (sIso e).f ⟨t, htS⟩ = tCode ε := by
    rw [sIso_f, ((he ⟨t, htS⟩).1).1 rfl, tM_code]
  have hk := hts _ (mem_sMarked ε)
  rw [← hft] at hk
  exact not_max_of_killAt_rep hH.sylow.pgroup hH.sylow.TH_le hH.TH_le hH.TH_max htS hH.t_sq
    (sIso e) sMul_zero_zero hinv sGens_lt sGen hGt hchi (kRepsC_lt hcls)
    (repProp_kRepsC htS (sIso e) sMul_zero_zero hinv sGens_lt sGen (m := 4) (by norm_num) hcls _)
    hk rfl

end Hyp

theorem sF_lt (k : ℕ) (ds : List ℕ) (c : ℕ) :
    sAutData.F sMul k ds c < 65536 := sMul_lt _ _

theorem mem_sLeaves {k : ℕ}
    (hk : k < 8) {ds : List ℕ} (hds : ds ∈ sAutData.fSearch sMul sInv k) :
    ∃ m, m < (sLeaves k).length ∧ (sLeaves k).getD m [] = ds := by
  have h := t1Enum_check
  unfold t1EnumCheck sLeavesCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hL : sLeaves k = sAutData.fSearch sMul sInv k := h.1.1.1 k hk
  rw [← hL] at hds
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hds
  exact ⟨m, hm, List.getD_eq_getElem _ _ hm⟩

theorem exists_norm
    {S : Subgroup G} (e : S ≃* SModel) {x : G}
    (hx : x ∈ normalizer (S : Set G)) (hxS : x ∉ S) :
    ∃ σ : S, ∃ hx' : (σ : G)⁻¹ * x ∈ normalizer (S : Set G), (σ : G)⁻¹ * x ∉ S ∧
      ∃ k, k < 8 ∧ ∃ m, m < (sLeaves k).length ∧
        ∀ s : S, (e (conjEquiv hx' s)).code = sFm k m (e s).code := by
  set γ : SModel ≃* SModel := e.symm.trans ((conjEquiv hx).trans e)
  obtain ⟨s₀, k, hk, ds, hds, hγ⟩ := sClassify SModel.codeIso γ
  obtain ⟨m, hm, hmds⟩ := mem_sLeaves hk hds
  set σ : S := e.symm s₀
  have hσN : (σ : G) ∈ normalizer (S : Set G) := le_normalizer σ.2
  have hx' : (σ : G)⁻¹ * x ∈ normalizer (S : Set G) := mul_mem (inv_mem hσN) hx
  refine ⟨σ, hx', fun h => hxS ?_, k, hk, m, hm, fun s => ?_⟩
  · have : x = (σ : G) * ((σ : G)⁻¹ * x) := by group
    rw [this]; exact mul_mem σ.2 h
  · set w : SModel := ⟨sAutData.F sMul k ds (e s).code, sF_lt k ds _⟩
    have hγs : γ (e s) = s₀ * w * s₀⁻¹ := by
      apply SModel.ext
      have h1 := hγ (e s)
      rw [SModel.codeIso_f, SModel.codeIso_f, SModel.codeIso_f, sConj, cconj] at h1
      rw [SModel.code_mul, SModel.code_mul, SModel.code_inv, h1]
    have hconj : conjEquiv hx' s = σ⁻¹ * conjEquiv hx s * σ := by
      apply Subtype.ext
      simp only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hγe : γ (e s) = e (conjEquiv hx s) := by
      simp only [γ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hconj, map_mul, map_mul, map_inv, ← hγe, hγs]
    simp only [σ, MulEquiv.apply_symm_apply]
    rw [show s₀⁻¹ * (s₀ * w * s₀⁻¹) * s₀ = w by group]
    show sAutData.F sMul k ds (e s).code = sAutData.F sMul k ((sLeaves k).getD m []) (e s).code
    rw [hmds]

theorem sFTab_get (k m : ℕ) {c : ℕ} (hc : c < 65536) : (sFTab k m)[c]! = sFm k m c := by
  unfold sFTab
  rw [getElem!_pos _ c (by simpa using hc), Array.getElem_map]
  simp only [List.getElem_toArray, List.getElem_range]
  have hW : (if sAutData.nfE c < 128 then (sWTab k m)[sAutData.nfE c]!
      else wprodN sMul 7 (sAutData.ys sMul k ((sLeaves k).getD m [])) (sAutData.nfE c)) =
      wprodN sMul 7 (sAutData.ys sMul k ((sLeaves k).getD m [])) (sAutData.nfE c) := by
    split
    · rename_i h
      unfold sWTab
      rw [getElem!_pos _ _ (by simpa using h), Array.getElem_map]
      simp
    · rfl
  have hL : (if sAutData.nfA c < 512 then (sLTab k)[sAutData.nfA c]!
      else a9K.lin (sAutData.Pk k (sAutData.nfA c))) =
      a9K.lin (sAutData.Pk k (sAutData.nfA c)) := by
    split
    · rename_i h
      unfold sLTab
      rw [getElem!_pos _ _ (by simpa using h), Array.getElem_map]
      simp
    · rfl
  rw [hW, hL]
  rfl

theorem t1List_length : t1List.length = 64 := by decide

theorem t1Mul_zero (F : Array ℕ) (z : ℕ) : t1Mul F z 0 0 = 0 := by
  unfold t1Mul extMul
  rw [ite_eq_left (by norm_num : 0 < 65536), ite_eq_left (by norm_num : 0 < 65536)]
  exact sMul_zero_zero

theorem t1Gens_lt : ∀ g ∈ t1Gens, g < 131072 := by decide

theorem getD_map_lt {α β : Type*} {f : α → β} {l : List α} {j : ℕ} (hj : j < l.length) (a : α)
    (b : β) : (l.map f).getD j b = f (l.getD j a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getD_eq_getElem _ _ hj]

theorem mem_sZList_of {F : ℕ → ℕ}
    (u : SModel) (hFF : ∀ y : SModel, F (F y.code) = (u * y * u⁻¹).code)
    (hFu : F u.code = u.code) : u.code ∈ sZList F := by
  unfold sZList
  rw [List.mem_filter]
  refine ⟨List.mem_range.2 u.lt, ?_⟩
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨fun j hj => ?_, hFu⟩
  have hgj : sGens.getD j 0 < 65536 := by
    rw [List.getD_eq_getElem _ _ hj]; exact sGens_lt _ (List.getElem_mem hj)
  set y : SModel := ⟨sGens.getD j 0, hgj⟩
  rw [getD_map_lt hj 0 0]
  change sMul u.code y.code = sMul (F (F y.code)) u.code
  rw [hFF, ← SModel.code_mul, ← SModel.code_mul]
  congr 1
  group

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem normalizes_E₁ (hH : Hyp ε t TH E₁ S) {e : S ≃* SModel}
    (he : ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧ ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM))
    {x : G} (hx : x ∈ normalizer (S : Set G)) (hx2 : x * x ∈ S) {F : ℕ → ℕ}
    (hF : ∀ s : S, (e (conjEquiv hx s)).code = F (e s).code) (hfix : sFixE F = true) :
    x ∈ normalizer (E₁ : Set G) := by
  have hFE : ∀ y ∈ E₁, x * y * x⁻¹ ∈ E₁ := by
    intro y hy
    have hyS : y ∈ S := hH.sylow.E₁_le hy
    have hcode : (e ⟨y, hyS⟩).code < 128 := ((he ⟨y, hyS⟩).2).1 hy
    have h1 : (e (conjEquiv hx ⟨y, hyS⟩)).code < 128 := by
      rw [hF]
      unfold sFixE at hfix
      rw [List.all_eq_true] at hfix
      exact decide_eq_true_iff.1 (hfix _ (List.mem_range.2 hcode))
    exact ((he (conjEquiv hx ⟨y, hyS⟩)).2).2 h1
  refine mem_normalizer_iff.2 fun y => ⟨fun hy => hFE y hy, fun hy => ?_⟩
  have hxx : x * x ∈ normalizer (E₁ : Set G) := hH.sylow.le_normalizer hx2
  have h1 := hFE _ hy
  have h2 := (mem_normalizer_iff.1 (inv_mem hxx) _).1 h1
  have e2 : (x * x)⁻¹ * (x * (x * y * x⁻¹) * x⁻¹) * (x * x)⁻¹⁻¹ = y := by group
  rwa [e2] at h2

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch

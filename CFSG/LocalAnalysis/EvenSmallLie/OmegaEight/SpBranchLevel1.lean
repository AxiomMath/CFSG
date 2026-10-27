
module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT1Check

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

attribute [local irreducible] sAct sMt sGinv p9List p9Index a9LinTab a9CoTab sNfTab sMTab sKOrb
  sCanon sTree sInvList sY sLeavesLit fpArr

variable {G : Type*} [Group G]

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

end Hyp

theorem t1Kill_all
    {d : ℕ × ℕ × ℕ × Bool}
    (hd : d ∈ t1List) : t1Kill d.1 d.2.1 d.2.2.1 d.2.2.2 sMarked = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  rw [t1List_length] at hi
  have key : ∀ a, t1KillRange a = true → a ≤ i → i < a + 10 →
      t1Kill t1List[i].1 t1List[i].2.1 t1List[i].2.2.1 t1List[i].2.2.2 sMarked = true := by
    intro a ha hai hia
    unfold t1KillRange at ha
    rw [List.all_eq_true] at ha
    have hlen : i - a < ((t1List.drop a).take 10).length := by
      simp [t1List_length]; omega
    have := ha _ (List.getElem_mem hlen)
    simp only [List.getElem_take, List.getElem_drop, Nat.add_sub_cancel' hai] at this
    exact this
  have h10 : i / 10 < 7 := by omega
  interval_cases h : i / 10
  · exact key 0 t1KillRange_check_0 (by omega) (by omega)
  · exact key 10 t1KillRange_check_10 (by omega) (by omega)
  · exact key 20 t1KillRange_check_20 (by omega) (by omega)
  · exact key 30 t1KillRange_check_30 (by omega) (by omega)
  · exact key 40 t1KillRange_check_40 (by omega) (by omega)
  · exact key 50 t1KillRange_check_50 (by omega) (by omega)
  · exact key 60 t1KillRange_check_60 (by omega) (by omega)

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem level1
    [Finite G]
    (hH : Hyp ε t TH E₁ S) (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) {e : S ≃* SModel}
    (he : ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧ ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM)) :
    ∃ x : G, ∃ hx : x ∈ normalizer (S : Set G), x ∉ S ∧ ∃ hx2 : x * x ∈ S,
      ∃ k m, k < 8 ∧ m < (sLeaves k).length ∧ sFixE (sFm k m) = false ∧
        (k, m, (e ⟨x * x, hx2⟩).code, false) ∈ t1List ∧
        (∀ s : S, (e (conjEquiv hx s)).code = sFm k m (e s).code) ∧
        ¬ ∀ P : Subgroup G, IsPGroup 2 P → S ⊔ zpowers x ≤ P → P = S ⊔ zpowers x := by
  have htS : t ∈ S := hH.t_mem_S
  obtain ⟨x₀, hx₀N, hx₀S, hx₀2⟩ := exists_step (hH.not_max_S hGt)
  obtain ⟨σ, hx, hxS, k, hk, m, hm, hF⟩ := exists_norm e hx₀N hx₀S
  set x := (σ : G)⁻¹ * x₀
  have hx2 : x * x ∈ S := by
    have e1 : x * x = (σ : G)⁻¹ * (x₀ * (σ : G)⁻¹ * x₀⁻¹) * (x₀ * x₀) := by
      simp only [x]; group
    rw [e1]
    exact mul_mem (mul_mem (inv_mem σ.2) ((mem_normalizer_iff.1 hx₀N _).1 (inv_mem σ.2))) hx₀2
  set z := (e ⟨x * x, hx2⟩).code
  have hmove : sFixE (sFm k m) = false := by
    by_contra hfix
    rw [Bool.not_eq_false] at hfix
    have hxE := hH.normalizes_E₁ he hx hx2 hF hfix
    have hp := isPGroup_sup_zpowers hH.sylow.pgroup hx hx2
    have hle : S ⊔ zpowers x ≤ normalizer (E₁ : Set G) :=
      sup_le hH.sylow.le_normalizer (zpowers_le.2 hxE)
    have := hH.sylow.maximal _ hle hp le_sup_left
    exact hxS (this ▸ mem_sup_right (mem_zpowers x))
  set u : SModel := e ⟨x * x, hx2⟩
  have hFF : ∀ y : SModel, sFm k m (sFm k m y.code) = (u * y * u⁻¹).code := by
    intro y
    have h1 := hF (e.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    have h2 := hF (conjEquiv hx (e.symm y))
    rw [← h1, ← h2]
    congr 1
    have : conjEquiv hx (conjEquiv hx (e.symm y)) = ⟨x * x, hx2⟩ * e.symm y * ⟨x * x, hx2⟩⁻¹ := by
      apply Subtype.ext
      simp only [conjEquiv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hz : z ∈ sZList (sFm k m) := by
    refine mem_sZList_of u hFF ?_
    have h1 := hF ⟨x * x, hx2⟩
    rw [← h1]
    congr 2
    apply Subtype.ext
    simp only [conjEquiv_apply, x]
    group
  have hcand : (k, m, z) ∈ t1Cands := by
    unfold t1Cands
    refine List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
      List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, ?_⟩⟩
    rw [hmove, ite_eq_right (by decide)]
    exact List.mem_map.2 ⟨z, hz, rfl⟩
  have hcov := t1Enum_check
  unfold t1EnumCheck at hcov
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at hcov
  have hex := hcov.1.2 _ hcand
  obtain ⟨d, hd, hdd⟩ := hex
  have hd' : (k, m, z, d.2.2.2) ∈ t1List := by
    have e1 : d = (k, m, z, d.2.2.2) := by
      obtain ⟨dk, dm, dz, dn5⟩ := d
      simp only at hdd ⊢
      rw [hdd.1.1, hdd.1.2, hdd.2]
    rw [← e1]; exact hd
  set dn5 := d.2.2.2
  clear_value dn5
  clear hd hdd
  have hd := hd'
  have hkill := t1Kill_all hd
  simp only at hkill
  have hF₁ : ∀ s : S, (sIso e).f ⟨x * s * x⁻¹, (mem_normalizer_iff.1 hx s).1 s.2⟩ =
      (fun c => (sFTab k m)[c]!) ((sIso e).f s) := by
    intro s
    rw [sIso_f, sIso_f]
    show _ = (sFTab k m)[(e s).code]!
    rw [sFTab_get _ _ (e s).lt]
    exact hF s
  let Φ₁ := (sIso e).extCodeIso hx hxS hx2 hF₁
  have hft : Φ₁.f ⟨t, mem_sup_left htS⟩ = tCode ε := by
    change (sIso e).extF x _ = _
    rw [CodeIso.extF_of_mem _ _ htS, sIso_f, ((he ⟨t, htS⟩).1).1 rfl, tM_code]
  unfold t1Kill at hkill
  obtain ⟨hinv, hcls, hchi, hts⟩ := groupKillC_spec hkill
  have hk1 := hts _ (mem_sMarked ε)
  rw [← hft] at hk1
  have hG₁ := (sIso e).gen_ext sMul_zero_zero (fun c => (sFTab k m)[c]!) z sGens_lt sGen
  have hp := isPGroup_sup_zpowers hH.sylow.pgroup hx hx2
  have hTH₁ : TH ≤ S ⊔ zpowers x := hH.sylow.TH_le.trans le_sup_left
  have hrep := repProp_kRepsC (mem_sup_left htS) Φ₁ (t1Mul_zero _ _) hinv t1Gens_lt hG₁
    (m := 8) (by norm_num) hcls (tInv ε)
  cases dn5
  · exact ⟨x, hx, hxS, hx2, k, m, hk, hm, hmove, hd, hF,
      not_max_of_killAt_rep hp hTH₁ hH.TH_le hH.TH_max (mem_sup_left htS) hH.t_sq Φ₁
        (t1Mul_zero _ _) hinv t1Gens_lt hG₁ hGt hchi (kRepsC_lt hcls) hrep hk1 rfl⟩
  · exact (false_of_killAt_rep hp hTH₁ hH.TH_le hH.TH_max (mem_sup_left htS) hH.t_sq Φ₁
      (t1Mul_zero _ _) hinv t1Gens_lt hG₁ hGt hchi hrep hk1).elim

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch

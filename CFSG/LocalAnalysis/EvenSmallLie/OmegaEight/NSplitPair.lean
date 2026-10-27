module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitSylow
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSetting

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SpBranch
open CFSG.EvenSmallLie.UnitarySix.YamadaPar
open scoped Pointwise

attribute [local irreducible] sAct sMt sGinv p9List p9Index

variable {G : Type*} [Group G]

namespace Branch

variable {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G} (hB : Branch ε t Q TH ψ)
include hB


theorem t_mem_TH [Finite G] : t ∈ TH := by
  have hN : t ∈ normalizer (TH : Set G) := by
    refine mem_normalizer_iff.2 fun y => ?_
    have hyt : ∀ y ∈ TH, t * y * t⁻¹ = y := fun y hy => by
      rw [← mem_centralizer_singleton_iff.1 (hB.TH_le hy), mul_inv_cancel_right]
    constructor
    · intro hy; rw [hyt y hy]; exact hy
    · intro hy
      have h := hyt _ hy
      have h1 : t * (t * y * t⁻¹) * t⁻¹ = y := by
        calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t⁻¹ * t⁻¹) := by group
          _ = y := by rw [hB.t_mul_t, hB.t_inv, hB.t_mul_t, one_mul, mul_one]
      rw [h1] at h
      rw [h]; exact hy
  have hsq : t * t ∈ TH := by rw [hB.t_mul_t]; exact one_mem _
  have hp := isPGroup_sup_zpowers hB.TH_pgroup hN hsq
  have hle : TH ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le hB.TH_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have := hB.TH_max _ hle hp le_sup_left
  rw [← this]
  exact mem_sup_right (mem_zpowers t)

theorem conj_t_form (n : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ w, qfV ε w = 0 ∧ ((n : G)⁻¹ * t * n) = t * ψ w := by
  obtain ⟨w, hw⟩ := hB.conj_t_eq (inv_mem n.2)
  refine ⟨w, (hB.Zset_eq w).1 ⟨(n : G)⁻¹, inv_mem n.2, hw⟩, ?_⟩
  rw [← hw, inv_inv]

omit [Group G] hB
  in
theorem code_of_kV {u : ℕ} (hu : u < 128) {w : V6} (h : kV ε u = mk7 w 1) :
    u = kapCode ε (vecBits w + 64) := by
  obtain ⟨h1, -⟩ := (dictFacts ε).1
  have hlt : vecBits w + 64 < 128 := by have := vecBits_lt w; omega
  have h2 : toVec 7 (vecBits w + 64) = mk7 w 1 := by
    rw [toVec7_eq]
    have e1 : (vecBits w + 64) % 64 = vecBits w := by have := vecBits_lt w; omega
    have e2 : (vecBits w + 64).testBit 6 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      have := vecBits_lt w
      omega
    rw [e1, e2, toVec_vecBits]
    rfl
  have h3 : kapInv ε u = vecBits w + 64 :=
    toVec_injective_lt (n := 7) (h1 u hu).2.2.1 hlt (h.trans h2.symm)
  rw [← (h1 u hu).2.2.2.1, h3]

theorem sylowModel [Finite G] : ∃ S : Subgroup G, SylowModel ε t TH (Q ⊔ zpowers t) S := by
  classical
  have hfac : (Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))).factorization 2 =
      16 := by
    rw [hB.card_N, show 128 * 1451520 = 2 ^ 16 * 2835 by rfl,
      factorization_two_mul 16 2835 (by decide)]
  have hJcard : Nat.card hB.jHom.range = 2 ^ (Nat.card
      (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))).factorization 2 := by
    rw [hfac, ← Nat.card_congr (MonoidHom.ofInjective hB.jHom_injective).toEquiv,
      SModel.codeIso.card_univ]
    rfl
  let P : Sylow 2 (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :=
    Sylow.ofCard hB.jHom.range hJcard
  obtain ⟨S₀, hS₀⟩ := hB.thN_pgroup.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))
    P S₀
  have hS₀P : (S₀ : Subgroup (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))) =
      MulAut.conj n • hB.jHom.range := by
    rw [← hn, Sylow.coe_subgroup_smul]
    rfl
  let S : Subgroup G :=
    (S₀ : Subgroup (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))).map
      (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)).subtype
  have hmemS : ∀ y (hy : y ∈ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)),
      y ∈ S ↔ (⟨y, hy⟩ : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) ∈ S₀ := by
    intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro h
      exact ⟨_, h, rfl⟩
  have hSN : S ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hTH : TH ≤ S := fun y hy =>
    (hmemS y (hB.TH_le_normalizer hy)).2 (hS₀ (show _ ∈ thN t Q TH from hy))
  have hker : hB.piHom.ker ≤ (S₀ : Subgroup _) := by
    have hp : IsPGroup 2 hB.piHom.ker := IsPGroup.of_card (n := 7) (by rw [hB.card_ker]; rfl)
    exact hp.le_sylow_of_normal S₀
  have hE : Q ⊔ zpowers t ≤ S := fun y hy =>
    (hmemS y (E_le_N hy)).2 (hker ((hB.piHom_eq_one_iff ⟨y, E_le_N hy⟩).2 hy))
  have hpS : IsPGroup 2 S := S₀.isPGroup'.map _
  have hmax : ∀ V : Subgroup G, V ≤ normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) →
      IsPGroup 2 V → S ≤ V → V = S := by
    intro V hVN hpV hSV
    have hpV' : IsPGroup 2 (V.subgroupOf (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))) :=
      hpV.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
    obtain ⟨Q', hQ'⟩ := hpV'.exists_le_sylow
    have hS₀V : (S₀ : Subgroup _) ≤ V.subgroupOf (normalizer ((Q ⊔ zpowers t : Subgroup G) :
        Set G)) := fun z hz => hSV ((hmemS z z.2).2 hz)
    have hEq : S₀.toSubgroup = Q'.toSubgroup := by
      apply Subgroup.eq_of_le_of_card_ge (hS₀V.trans hQ')
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    refine le_antisymm (fun y hy => (hmemS y (hVN hy)).2 ?_) hSV
    change _ ∈ S₀.toSubgroup
    rw [hEq]
    exact hQ' hy
  refine ⟨S, ⟨hTH, hE, hSN, hpS, hmax, ?_⟩⟩
  let e₀ : S ≃* SModel :=
    (((S₀ : Subgroup (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))).equivMapOfInjective
      _ (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)).subtype_injective).symm.trans
      (MulEquiv.subgroupCongr hS₀P)).trans
      ((Subgroup.equivSMul (MulAut.conj n) hB.jHom.range).symm.trans
        (MonoidHom.ofInjective hB.jHom_injective).symm)
  have key : ∀ d : SModel, ((e₀.symm d : S) : G) = (n : G) * (hB.jHom d : G) * (n : G)⁻¹ :=
    fun d => rfl
  have key' : ∀ s : S, ((hB.jHom (e₀ s) : _) : G) = (n : G)⁻¹ * s * n := by
    intro s
    have h := key (e₀ s)
    rw [MulEquiv.symm_apply_apply] at h
    rw [h]
    group
  have ht : t ∈ S := hTH hB.t_mem_TH
  let t' : S := ⟨t, ht⟩
  set c₀ := e₀ t' with hc₀def
  have hc₀E : c₀ ∈ SModel.EM := by
    rw [← hB.jHom_mem_E_iff, key']
    have hn' := (mem_normalizer_iff.1 (inv_mem n.2) t).1 t_mem_E
    simpa using hn'
  have hc₀lt : c₀.code < 128 := hc₀E
  obtain ⟨w, hw, hwt⟩ := hB.conj_t_form n
  have hjc : ((hB.jHom c₀ : _) : G) = ιG t ψ (kV ε c₀.code) := by
    change ((hB.ι (kV ε (eP c₀.code)) * hB.sec (phiN ε (gP c₀.code)) : _) : G) = _
    rw [eP_of_lt hc₀lt, gP_of_lt hc₀lt, phiN, dite_eq_left (by norm_num : 0 < 512), phiG_zero,
      map_one, mul_one]
    rfl
  have hkV : kV ε c₀.code = mk7 w 1 := by
    apply hB.ι_inj
    apply Subtype.ext
    rw [ι_coe, ι_coe, ← hjc, key']
    rw [hwt]
    simp [ιG, vOf_mk7, mk7_last, tPow]
  have hcode := code_of_kV hc₀lt hkV
  have hcent : Nat.card (centralizer ({t'} : Set S)) = 2 ^ 14 := by
    rw [← hB.card_TH]
    have hCS : ∀ s : S, s ∈ centralizer ({t'} : Set S) ↔ (s : G) ∈ TH := by
      intro s
      rw [mem_centralizer_singleton_iff]
      constructor
      · intro h
        have h' : (s : G) * t = t * s := by
          have := congrArg Subtype.val h
          simpa [t'] using this
        have hle : S ⊓ centralizer ({t} : Set G) = TH := by
          apply hB.TH_max
          · exact inf_le_right
          · exact hpS.to_le inf_le_left
          · exact le_inf hTH hB.TH_le
        rw [← hle]
        exact ⟨s.2, mem_centralizer_singleton_iff.2 h'⟩
      · intro h
        apply Subtype.ext
        have := mem_centralizer_singleton_iff.1 (hB.TH_le h)
        simpa [t'] using this
    have hsub : centralizer ({t'} : Set S) = TH.subgroupOf S := by
      ext s
      rw [hCS]
      rfl
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hcent' : Nat.card (centralizer ({c₀} : Set SModel)) = 2 ^ 14 := by
    rw [hc₀def, card_centralizer_map e₀ t', hcent]
  have : Finite SModel := SModel.codeIso.finite
  have horb := card_conj_orbit c₀
  rw [hcent', SModel.codeIso.card_univ] at horb
  have h4 : Nat.card (MulAction.orbit (ConjAct SModel) c₀) = 4 := by omega
  rw [card_orbit_eq c₀ hc₀lt, hcode] at h4
  have hmemO := (dictFacts ε).2 (vecBits w) (vecBits_lt w)
    ((qfV_eq_zero_iff ε w).1 hw) h4
  rw [← hcode] at hmemO
  simp only [p9Orbit, List.mem_dedup, List.mem_map, List.mem_range] at hmemO
  obtain ⟨g, hg, hgc⟩ := hmemO
  let x := pElt g hg
  refine ⟨e₀.trans (MulAut.conj x), fun s => ?_⟩
  have hes : ∀ s : S, (e₀.trans (MulAut.conj x)) s = x * e₀ s * x⁻¹ := fun s => rfl
  have het : (e₀.trans (MulAut.conj x)) t' = SModel.tM ε := by
    rw [hes]
    apply SModel.ext
    rw [conj_code _ _ hc₀lt, gP_pElt, hgc]
    cases ε <;> rfl
  constructor
  · constructor
    · intro hs
      have : s = t' := Subtype.ext hs
      rw [this, het]
    · intro hs
      rw [← het] at hs
      exact congrArg Subtype.val ((e₀.trans (MulAut.conj x)).injective hs)
  · rw [hes]
    have hconjE : ∀ c : SModel, c ∈ SModel.EM ↔ x * c * x⁻¹ ∈ SModel.EM := by
      intro c
      constructor
      · intro hc
        change (x * c * x⁻¹).code < 128
        rw [conj_code _ _ hc]
        exact sA_lt (gP_lt _) hc
      · intro hc
        have h1 : c = x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ := by group
        change c.code < 128
        rw [h1, conj_code _ _ hc]
        exact sA_lt (gP_lt _) hc
    rw [← hconjE, ← hB.jHom_mem_E_iff, key']
    constructor
    · intro hs
      have h1 := (mem_normalizer_iff.1 (inv_mem n.2) (s : G)).1 hs
      rwa [inv_inv] at h1
    · intro hs
      have h1 := (mem_normalizer_iff.1 n.2 _).1 hs
      have h2 : (n : G) * ((n : G)⁻¹ * s * n) * (n : G)⁻¹ = s := by group
      rwa [h2] at h1

end Branch

end CFSG.EvenSmallLie.OmegaEight.NSplit

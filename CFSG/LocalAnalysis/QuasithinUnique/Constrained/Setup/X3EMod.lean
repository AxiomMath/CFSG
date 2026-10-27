module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3ECheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.X3E

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.X3

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem isInvariant_of_gens (σ : S6 →* (W ≃ₗ[ZMod 2] W)) {U : Submodule (ZMod 2) W}
    (h : ∀ b, ∀ u ∈ U, σ (gen b) u ∈ U) : Offender.IsInvariant σ ⊤ U := by
  let T : Subgroup S6 :=
    { carrier := {g | ∀ u ∈ U, σ g u ∈ U}
      mul_mem' := fun {a b} ha hb u hu => by rw [map_mul, LinearEquiv.mul_apply]; exact ha _ (hb u hu)
      one_mem' := fun u hu => by simpa using hu
      inv_mem' := fun {a} ha u hu => by
        let f : U → U := fun u => ⟨σ a u, ha u u.2⟩
        have hf : Function.Injective f := by
          intro u u' huu
          exact Subtype.ext ((σ a).injective (congrArg Subtype.val huu))
        obtain ⟨u', hu'⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
        have h1 : σ a u' = u := congrArg Subtype.val hu'
        have h2 : σ a⁻¹ u = u' := by rw [← h1]; exact ρ_inv_apply σ a u'
        rw [h2]
        exact u'.2 }
  have hT : (⊤ : Subgroup S6) ≤ T := by
    rw [← closure_xy, Subgroup.closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · exact h false
    · exact h true
  intro g _ u hu
  exact hT (Subgroup.mem_top g) u hu

theorem exists_fixed_vector (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (hW : (⊤ : Submodule (ZMod 2) W) ≠ ⊥) :
    ∃ v : W, v ≠ 0 ∧ ∀ r ∈ R0, σ r v = v := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsPGroup 2 R0 := IsPGroup.of_card (n := 3) (by rw [card_R0]; norm_num)
  let _ : MulAction R0 W := MulAction.compHom W (σ.comp R0.subtype)
  have hmod := hG.card_modEq_card_fixedPoints W
  have hne : ∃ w : W, w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hW
    rw [eq_bot_iff]
    intro w _
    rw [Submodule.mem_bot]
    exact hcon w
  have hcard : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)]
    simp
  have hpos : 0 < Module.finrank (ZMod 2) W := by
    rw [Module.finrank_pos_iff]
    obtain ⟨w, hw⟩ := hne
    exact ⟨⟨w, 0, fun h => hw (by simpa using h)⟩⟩
  have heven : Nat.card W % 2 = 0 := by
    rw [hcard]
    obtain ⟨k, hk⟩ : ∃ k, Module.finrank (ZMod 2) W = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hk, pow_succ]
    simp
  by_contra hcon
  push Not at hcon
  have hfix : MulAction.fixedPoints R0 W = {0} := by
    ext w
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hw
      by_contra hw0
      obtain ⟨r, hr, hne'⟩ := hcon w hw0
      exact hne' (hw ⟨r, hr⟩)
    · rintro rfl m
      exact map_zero (σ m.1)
  have hone : Nat.card (MulAction.fixedPoints R0 W) = 1 := by
    rw [hfix]; simp
  rw [hone] at hmod
  have := hmod
  unfold Nat.ModEq at this
  omega

@[expose] noncomputable def phiMap (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (v : W) : Vec 45 →ₗ[ZMod 2] W :=
  Fintype.linearCombination (ZMod 2) (fun i : Fin 45 => σ (rep i.val) v)

omit [Finite W] in
theorem phiMap_single (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (v : W) (i : Fin 45) :
    phiMap σ v (Pi.single i 1) = σ (rep i.val) v := by
  unfold phiMap
  rw [Fintype.linearCombination_apply_single, one_smul]

theorem piCols_single (b : Bool) (i : Fin 45) :
    lin 45 (piColsOf b) (Pi.single i 1) = Pi.single ⟨tauOf b i.val, tau_lt i b⟩ (1 : ZMod 2) := by
  rw [lin_single, ← toVec_one_shiftLeft 45 (tauOf b i.val) (tau_lt i b)]
  congr 1
  unfold piColsOf piCols tauOf
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
  simp

omit [Finite W] in
theorem phiMap_equivariant (σ : S6 →* (W ≃ₗ[ZMod 2] W)) {v : W} (hv : ∀ r ∈ R0, σ r v = v)
    (b : Bool) (u : Vec 45) :
    phiMap σ v (lin 45 (piColsOf b) u) = σ (gen b) (phiMap σ v u) := by
  have key : (phiMap σ v).comp (lin 45 (piColsOf b)) =
      ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W).comp (phiMap σ v) := by
    apply linearMap_ext_basis
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [piCols_single, phiMap_single, phiMap_single]
    have hr := coset_rel i.val i.isLt b
    have h1 := hv _ hr
    calc σ (rep (tauOf b i.val)) v
        = σ (rep (tauOf b i.val)) (σ ((rep (tauOf b i.val))⁻¹ * gen b * rep i.val) v) := by rw [h1]
      _ = σ (rep (tauOf b i.val) * ((rep (tauOf b i.val))⁻¹ * gen b * rep i.val)) v :=
          (ρ_mul_apply σ _ _ _).symm
      _ = σ (gen b * rep i.val) v := by
          congr 2
          group
      _ = σ (gen b) (σ (rep i.val) v) := ρ_mul_apply σ _ _ _
  exact LinearMap.congr_fun key u

theorem phiMap_surjective (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (hS : IsLSimple σ ⊤ ⊤) {v : W} (hv0 : v ≠ 0)
    (hv : ∀ r ∈ R0, σ r v = v) : Function.Surjective (phiMap σ v) := by
  let U : Submodule (ZMod 2) W := LinearMap.range (phiMap σ v)
  have hUinv : Offender.IsInvariant σ ⊤ U := by
    apply isInvariant_of_gens
    rintro b u ⟨u', rfl⟩
    exact ⟨lin 45 (piColsOf b) u', phiMap_equivariant σ hv b u'⟩
  have hUne : U ≠ ⊥ := by
    intro h
    have hmem : v ∈ U := ⟨Pi.single ⟨0, by norm_num⟩ 1, by
      rw [phiMap_single]
      show σ (rep 0) v = v
      rw [rep_zero, map_one]; rfl⟩
    rw [h, Submodule.mem_bot] at hmem
    exact hv0 hmem
  rcases hS.2.2 U hUinv le_top with h | h
  · exact absurd h hUne
  · exact LinearMap.range_eq_top.mp h

theorem baseOK_facts :
    (∀ i : Fin 45, papply 45 eB (eT.getD i.val 0) = 1 <<< i.val) ∧
    (∀ b : Bool, ∀ j : Fin 45,
      papply 45 eB ((colsOf b).getD j.val 0) = papply 45 (piColsOf b) (eB.getD j.val 0)) := by
  have h := baseOK_true
  unfold baseOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, h1⟩, h2⟩, h3⟩ := h
  refine ⟨fun i => h1 i i.isLt, ?_⟩
  intro b j
  cases b
  · exact h2 j j.isLt
  · exact h3 j j.isLt

theorem lin_eB_eT (u : Vec 45) : lin 45 eB (lin 45 eT u) = u := by
  have : (lin 45 eB).comp (lin 45 eT) = LinearMap.id := by
    apply linearMap_ext_basis
    intro i
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [lin_single, ← toVec_papply, (baseOK_facts).1 i, toVec_one_shiftLeft 45 i.val i.isLt]
  exact LinearMap.congr_fun this u

theorem lin_eB_cols (b : Bool) (u : Vec 45) :
    lin 45 eB (lin 45 (colsOf b) u) = lin 45 (piColsOf b) (lin 45 eB u) := by
  have : (lin 45 eB).comp (lin 45 (colsOf b)) = (lin 45 (piColsOf b)).comp (lin 45 eB) := by
    apply linearMap_ext_basis
    intro j
    simp only [LinearMap.comp_apply]
    rw [lin_single, lin_single, ← toVec_papply, ← toVec_papply, (baseOK_facts).2 b j]
  exact LinearMap.congr_fun this u

theorem lin_eB_surjective : Function.Surjective (lin 45 eB) :=
  fun u => ⟨lin 45 eT u, lin_eB_eT u⟩

theorem flagOK_facts :
    eNs.getD 0 0 = 0 ∧ eNs.getD 12 0 = 45 ∧ (∀ i < 12, eNs.getD i 0 < eNs.getD (i + 1) 0) ∧
    (∀ i ≤ 12, ∀ j < eNs.getD i 0, eMx.getD j 0 < 2 ^ eNs.getD i 0 ∧
      eMy.getD j 0 < 2 ^ eNs.getD i 0) := by
  have h := flagOK_true
  unfold flagOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, decide_eq_true_eq]
    at h
  obtain ⟨⟨⟨⟨-, h0⟩, h12⟩, hmono⟩, hfl⟩ := h
  refine ⟨h0, h12, hmono, fun i hi j hj => ?_⟩
  have := hfl i (by omega) j hj
  exact this

theorem blocksOK_facts : ∀ i < 12,
    nortonOK (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i) (eAW.getD i []) (eKers.getD i [])
      (ePsi.getD i 0) (eDw.getD i []) (eRc.getD i []) (eMinv.getD i []) = true := by
  have h := blocksOK_true
  unfold blocksOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.2

theorem exists_block_iso (σ : S6 →* (W ≃ₗ[ZMod 2] W)) (hS : IsLSimple σ ⊤ ⊤) :
    ∃ i < 12, ∃ Ψ : Vec (eNs.getD (i + 1) 0 - eNs.getD i 0) ≃ₗ[ZMod 2] W,
      ∀ b s, Ψ (lin (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i b) s) = σ (gen b) (Ψ s) := by
  have hWne : (⊤ : Submodule (ZMod 2) W) ≠ ⊥ := hS.2.1
  obtain ⟨v, hv0, hv⟩ := exists_fixed_vector σ hWne
  obtain ⟨hns0, hnsN, hmono, hfl⟩ := flagOK_facts
  have hWirr : IrredPair (fun b => ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) := by
    intro U hU
    have hinv : Offender.IsInvariant σ ⊤ U := isInvariant_of_gens σ fun b u hu => hU b u hu
    exact hS.2.2 U hinv le_top
  have hφ : Function.Surjective ((phiMap σ v).comp (lin 45 eB)) := by
    rw [LinearMap.coe_comp]
    exact (phiMap_surjective σ hS hv0 hv).comp lin_eB_surjective
  have hφeq : ∀ b u, ((phiMap σ v).comp (lin 45 eB)) (lin 45 (colsOf b) u) =
      ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) (((phiMap σ v).comp (lin 45 eB)) u) := by
    intro b u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [lin_eB_cols, phiMap_equivariant σ hv]
  have hinv : ∀ i ≤ 12, ∀ b, ∀ w ∈ Fl 45 (eNs.getD i 0), lin 45 (colsOf b) w ∈ Fl 45 (eNs.getD i 0) := by
    intro i hi b w hw
    apply lin_mem_Fl _ hw
    intro j hj
    have := hfl i hi j hj
    cases b
    · exact this.1
    · exact this.2
  have hirr : ∀ i < 12, IrredPair (fun b => blockMap 45 (eNs.getD i 0)
      (eNs.getD (i + 1) 0 - eNs.getD i 0) (lin 45 (colsOf b))) := by
    intro i hi
    have hwin : eNs.getD i 0 + (eNs.getD (i + 1) 0 - eNs.getD i 0) ≤ 45 := by
      have h1 := hmono i hi
      have h2 : eNs.getD (i + 1) 0 ≤ eNs.getD 12 0 :=
        ns_mono (ns := fun i => eNs.getD i 0) (nSteps := 12) hmono (i + 1) 12 (by omega) le_rfl
      omega
    have : (fun b => blockMap 45 (eNs.getD i 0) (eNs.getD (i + 1) 0 - eNs.getD i 0)
        (lin 45 (colsOf b))) = fun b => lin (eNs.getD (i + 1) 0 - eNs.getD i 0) (blkOf i b) := by
      funext b
      exact blockMap_lin hwin (colsOf b)
    rw [this]
    exact nortonOK_sound (blocksOK_facts i hi)
  obtain ⟨i, hi, Ψ, hΨ⟩ := chain_jh (N := 45) (fun i => eNs.getD i 0) 12 hns0 hnsN hmono
    (fun b => lin 45 (colsOf b)) hinv hirr
    (fun b => ((σ (gen b) : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) hWirr hWne
    ((phiMap σ v).comp (lin 45 eB)) hφ hφeq
  refine ⟨i, hi, Ψ, fun b s => ?_⟩
  have hwin : eNs.getD i 0 + (eNs.getD (i + 1) 0 - eNs.getD i 0) ≤ 45 := by
    have h1 := hmono i hi
    have h2 : eNs.getD (i + 1) 0 ≤ eNs.getD 12 0 :=
      ns_mono (ns := fun i => eNs.getD i 0) (nSteps := 12) hmono (i + 1) 12 (by omega) le_rfl
    omega
  have := hΨ b s
  rw [blockMap_lin hwin] at this
  exact this

end CFSG.QuasithinUnique.Setup.X3E

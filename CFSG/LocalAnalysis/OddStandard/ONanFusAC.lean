module

public import CFSG.LocalAnalysis.OddStandard.ONanFusDE
public import CFSG.LocalAnalysis.OddStandard.ONanFusD
public import CFSG.LocalAnalysis.OddStandard.ONanFusExt

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def xF1E : AlpE := ⟨4, 0, 0, 0⟩
@[expose] def xF2E : AlpE := ⟨4, 1, 0, 1⟩
@[expose] def xG1E : AlpE := ⟨6, 0, 0, 3⟩
@[expose] def xG2E : AlpE := ⟨6, 1, 0, 0⟩

theorem xFG_facts : xF1E * invE 3 = invE 3 * xF1E ∧ xF2E * invE 3 = invE 3 * xF2E ∧
    xG1E * invE 3 = invE 3 * xG1E ∧ xG2E * invE 3 = invE 3 * xG2E ∧
    xF1E * xF2E ≠ xF2E * xF1E ∧ xG1E * xG2E ≠ xG2E * xG1E := by
  decide

set_option maxRecDepth 100000 in
theorem xFG_class : (∃ c : AlpE, c⁻¹ * invE 5 * c = xF1E) ∧ (∃ c : AlpE, c⁻¹ * invE 5 * c = xF2E) ∧
    (∃ c : AlpE, c⁻¹ * invE 6 * c = xG1E) ∧ (∃ c : AlpE, c⁻¹ * invE 6 * c = xG2E) := by
  decide +kernel

@[expose] def F4E : List AlpE := [⟨4, 0, 0, 0⟩, ⟨4, 0, 2, 0⟩, ⟨4, 2, 0, 2⟩, ⟨4, 2, 2, 2⟩]
@[expose] def G4E : List AlpE := [⟨4, 0, 1, 0⟩, ⟨4, 0, 3, 0⟩, ⟨4, 2, 1, 2⟩, ⟨4, 2, 3, 2⟩]

@[expose] def FG4E (k : Fin 3) : List AlpE := if k = 1 then F4E else G4E

set_option maxRecDepth 100000 in
theorem FG4E_facts : ∀ k : Fin 3, k ≠ 0 → (FG4E k).Nodup ∧ (FG4E k).length = 4 ∧
    ∀ x ∈ FG4E k, x * invE (repDFG k) = invE (repDFG k) * x ∧
      ∃ c : AlpE, c⁻¹ * invE (repDFG k) * c = x := by
  decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem mem_K4_of_fus (hAC : ¬ D.Fus 0 2) {w : G} (hw : w ∈ alpW v1 v2 v3) {j : Fin 7}
    (hj : D.InClass j w) (hfus : D.Fus 0 j) :
    w = invRep v1 v2 v3 s t 0 ∨ w = invRep v1 v2 v3 s t 1 ∨
      w = invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1 := by
  have hj2 := D.le_two_of_inClass_mem_V hj (D.W_le_V hw)
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · obtain ⟨c, hc, hcx⟩ := hj
    rw [D.z_central hc] at hcx
    exact Or.inl hcx.symm
  · obtain ⟨c, hc, hcx⟩ := hj
    obtain ⟨c', rfl⟩ := (AlpEmb.mem_alpP_iff D.E).1 hc
    rw [D.invRep_eq 1, invE_one, ← map_inv, ← map_mul, ← map_mul] at hcx
    rcases conj_bE c' with h | h
    · rw [h, ← invE_one, ← D.invRep_eq 1] at hcx
      exact Or.inr (Or.inl hcx.symm)
    · rw [h, map_mul, ← invE_zero, ← invE_one, ← D.invRep_eq 0, ← D.invRep_eq 1] at hcx
      exact Or.inr (Or.inr hcx.symm)
  · exact absurd hfus hAC

theorem inClass_E_of_H5 {x : G} (hxH : x ∈ D.H5) (hxV : x ∉ alpV v1 v2 v3) (hx2 : x * x = 1) :
    D.InClass 4 x := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hxH
  have hyd : y.d = 5 := by
    rcases mem_H5E.1 hy with h | h
    · exact absurd (by rw [AlpEmb.alpV_eq_map D.E]; exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 h))
        hxV
    · exact h
  have hy2 : y * y = 1 := D.E.inj (by rw [map_mul, hx2, map_one])
  exact D.inClass_of_model (inv_57_classE y (Or.inl hyd) hy2)

theorem fus_of_cent {k : Fin 3} {x : G}
    (hx : x ∈ alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t (repDFG k)} : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : ∃ j : Fin 7, D.InClass j x ∧ centCount k j ≠ 0 := by
  obtain ⟨j, hj⟩ := D.exists_inClass hx.1 hx2 hx1
  exact ⟨j, hj, D.centCount_ne_zero hx hx2 hx1 hj⟩

theorem fus_CD (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) : D.Fus 2 3 := by
  classical
  by_contra hCD
  obtain ⟨hD, -, -⟩ := D.fusABC_DFG hAB hAC
  have hDA : D.Fus 3 0 := by
    rcases hD with h | h | h
    · exact h
    · exact h.trans D (Fus.symm D hAB)
    · exact absurd (Fus.symm D h) hCD
  have hDE := D.fus_DE hAB hAC
  have hEA : D.Fus 4 0 := (Fus.symm D hDE).trans D hDA
  obtain ⟨g, hg1, hg2, hgH, hgW⟩ := D.ext_conj 0 hDA
  set r := invRep v1 v2 v3 s t (repDFG 0) with hr
  have hmemCr : ∀ {y : AlpE}, y * invE 3 = invE 3 * y →
      D.E.φ y ∈ alpP v1 v2 v3 s t ⊓ centralizer ({r} : Set G) := by
    intro y hy
    refine ⟨AlpEmb.φ_mem D.E y, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hr, show repDFG 0 = 3 from rfl, D.invRep_eq 3, ← map_mul, ← map_mul, hy]
  obtain ⟨hF1, hF2, hG1, hG2, hFnc, hGnc⟩ := xFG_facts
  obtain ⟨cF1, cF2, cG1, cG2⟩ := xFG_class
  have key : ∀ {x1 x2 : AlpE} {i : Fin 7}, x1 * invE 3 = invE 3 * x1 → x2 * invE 3 = invE 3 * x2 →
      x1 * x2 ≠ x2 * x1 → D.InClass i (D.E.φ x1) → D.InClass i (D.E.φ x2) → D.Fus i 4 := by
    intro x1 x2 i h1 h2 hnc hi1 hi2
    have hV : ¬ (g⁻¹ * D.E.φ x1 * g ∈ alpV v1 v2 v3 ∧ g⁻¹ * D.E.φ x2 * g ∈ alpV v1 v2 v3) := by
      rintro ⟨hV1, hV2⟩
      apply hnc
      apply D.E.inj
      have hc := mem_centralizer_iff.1 (D.V_le_centralizer_V hV2) _ hV1
      rw [map_mul, map_mul]
      calc D.E.φ x1 * D.E.φ x2 = g * ((g⁻¹ * D.E.φ x1 * g) * (g⁻¹ * D.E.φ x2 * g)) * g⁻¹ := by
            group
        _ = g * ((g⁻¹ * D.E.φ x2 * g) * (g⁻¹ * D.E.φ x1 * g)) * g⁻¹ := by rw [hc]
        _ = D.E.φ x2 * D.E.φ x1 := by group
    have hE : ∀ {x : AlpE}, x * invE 3 = invE 3 * x → D.InClass i (D.E.φ x) →
        g⁻¹ * D.E.φ x * g ∉ alpV v1 v2 v3 → D.Fus i 4 := by
      intro x hx hix hxV
      have hx2 : g⁻¹ * D.E.φ x * g * (g⁻¹ * D.E.φ x * g) = 1 := by
        calc g⁻¹ * D.E.φ x * g * (g⁻¹ * D.E.φ x * g) = g⁻¹ * (D.E.φ x * D.E.φ x) * g := by group
          _ = 1 := by rw [hix.sq]; group
      exact D.inClass_fus hix (D.inClass_E_of_H5 (hgH _ (hmemCr hx)) hxV hx2) g rfl
    by_cases hV1 : g⁻¹ * D.E.φ x1 * g ∈ alpV v1 v2 v3
    · exact hE h2 hi2 fun hV2 => hV ⟨hV1, hV2⟩
    · exact hE h1 hi1 hV1
  have hFE := key hF1 hF2 hFnc (D.inClass_of_model cF1) (D.inClass_of_model cF2)
  have hGE := key hG1 hG2 hGnc (D.inClass_of_model cG1) (D.inClass_of_model cG2)
  have hv2W : invRep v1 v2 v3 s t 2 ∈ alpW v1 v2 v3 := by
    show v2 ^ 2 ∈ alpW v1 v2 v3
    exact subset_closure (by simp)
  obtain ⟨x, hx, hxv⟩ := hgW hv2W
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxv
  have hx2 : x * x = 1 := by
    have := (D.mem_W_iff.1 hv2W).2
    rw [← hxv] at this
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [this]; group
  have hx1 : x ≠ 1 := by
    intro h
    apply D.rep_ne_one 2
    rw [← hxv, h]
    group
  obtain ⟨j, hj, hcc⟩ := D.fus_of_cent (k := 0) hx hx2 hx1
  have hfusj : D.Fus j 2 := D.inClass_fus hj (D.inClass_rep 2) g hxv
  have hj0 : D.Fus j 0 := by
    have key2 : ∀ j : Fin 7, centCount 0 j ≠ 0 → j = 0 ∨ j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 6 := by
      decide
    rcases key2 j hcc with rfl | rfl | rfl | rfl | rfl
    · exact Fus.refl D 0
    · exact Fus.symm D hAB
    · exact hDA
    · exact hFE.trans D hEA
    · exact hGE.trans D hEA
  exact hAC ((Fus.symm D hj0).trans D hfusj)

theorem fus_C_FG (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) (k : Fin 3) (hk : k ≠ 0) :
    D.Fus 2 (repDFG k) := by
  classical
  by_contra hC
  obtain ⟨-, hF, hG⟩ := D.fusABC_DFG hAB hAC
  have hABC : D.FusABC (repDFG k) := by
    have : k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl
    · exact hF
    · exact hG
  have hrA : D.Fus (repDFG k) 0 := by
    rcases hABC with h | h | h
    · exact h
    · exact h.trans D (Fus.symm D hAB)
    · exact absurd (Fus.symm D h) hC
  have hCE : D.Fus 2 4 := (D.fus_CD hAB hAC).trans D (D.fus_DE hAB hAC)
  have hnotE : ¬ D.Fus (repDFG k) 4 := fun h => hC (hCE.trans D (Fus.symm D h))
  obtain ⟨g, -, -, hgH, -⟩ := D.ext_conj k hrA
  obtain ⟨hnd, hlen, hmem⟩ := FG4E_facts k hk
  have himg : ∀ x ∈ FG4E k, g⁻¹ * D.E.φ x * g ∈ [invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1,
      invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1] := by
    intro x hx
    obtain ⟨hxr, hxcls⟩ := hmem x hx
    have hxC : D.E.φ x ∈ alpP v1 v2 v3 s t ⊓
        centralizer ({invRep v1 v2 v3 s t (repDFG k)} : Set G) :=
      ⟨AlpEmb.φ_mem D.E x, mem_centralizer_singleton_iff.2 (by
        rw [D.invRep_eq, ← map_mul, ← map_mul, hxr])⟩
    have hxi : D.InClass (repDFG k) (D.E.φ x) := D.inClass_of_model hxcls
    set y := g⁻¹ * D.E.φ x * g with hy
    have hy2 : y * y = 1 := by
      calc y * y = g⁻¹ * (D.E.φ x * D.E.φ x) * g := by rw [hy]; group
        _ = 1 := by rw [hxi.sq]; group
    have hy1 : y ≠ 1 := by
      intro h
      apply hxi.ne_one
      calc D.E.φ x = g * y * g⁻¹ := by rw [hy]; group
        _ = 1 := by rw [h]; group
    have hyV : y ∈ alpV v1 v2 v3 := by
      by_contra hyV
      exact hnotE (D.inClass_fus hxi (D.inClass_E_of_H5 (hgH _ hxC) hyV hy2) g rfl)
    have hyW : y ∈ alpW v1 v2 v3 := D.mem_W_iff.2 ⟨hyV, hy2⟩
    obtain ⟨j, hj⟩ := D.exists_inClass (D.V_le_P hyV) hy2 hy1
    have hfus : D.Fus 0 j := (Fus.symm D hrA).trans D (D.inClass_fus hxi hj g rfl)
    rcases D.mem_K4_of_fus hAC hyW hj hfus with h | h | h <;> simp [h]
  have hnd' : ((FG4E k).map fun x => g⁻¹ * D.E.φ x * g).Nodup := by
    refine hnd.map fun a b hab => D.E.inj ?_
    simpa using hab
  have hsub : ((FG4E k).map fun x => g⁻¹ * D.E.φ x * g) ⊆ [invRep v1 v2 v3 s t 0,
      invRep v1 v2 v3 s t 1, invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1] := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact himg x hx
  have hle := (hnd'.subperm hsub).length_le
  rw [List.length_map, hlen] at hle
  simp at hle

theorem fus_AC (hAB : D.Fus 0 1) : D.Fus 0 2 := by
  classical
  by_contra hAC
  have hCD := D.fus_CD hAB hAC
  have hDE := D.fus_DE hAB hAC
  have hCF := D.fus_C_FG hAB hAC 1 (by decide)
  have hCG := D.fus_C_FG hAB hAC 2 (by decide)
  have hnotAB : ∀ j : Fin 7, D.Fus 2 j → 2 ≤ j.val := by
    intro j hj
    by_contra hlt
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · exact hAC (Fus.symm D hj)
    · exact hAC (hAB.trans D (Fus.symm D hj))
  have hext := D.isSylowOf_rep 2 fun j hj => by
    have h2 := hnotAB j hj
    have key : ∀ j : Fin 7, 2 ≤ j.val →
        (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) j ≤ ![512, 256, 128, 32, 16, 32, 32] 2 := by
      decide
    exact key j h2
  obtain ⟨h, hh⟩ := id hCF
  obtain ⟨g, hg1, hg2⟩ := exists_conj_extremal D.isPGroup_P hext (u := invRep v1 v2 v3 s t 5) hh
  set z := invRep v1 v2 v3 s t 0
  set b := invRep v1 v2 v3 s t 1
  set Ct := alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 5} : Set G) with hCt
  set Cv := alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 2} : Set G) with hCv
  set Y := Ct.map (MulAut.conj g⁻¹).toMonoidHom with hY
  have hYCv : Y ≤ Cv := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply] using hg2 c hc
  have hcardY : Nat.card Y = 32 := by
    rw [hY, card_map_of_injective (MulAut.conj g⁻¹).injective, hCt,
      AlpEmb.card_centralizer_invRep D.E D.hF 5]
    rfl
  have hVCv : alpV v1 v2 v3 ≤ Cv := fun v hv => ⟨D.V_le_P hv, mem_centralizer_singleton_iff.2
    (mem_centralizer_iff.1 (D.V_le_centralizer_V hv) _ (D.rep_mem_V (i := 2) (by decide))).symm⟩
  have hrelCv : (alpV v1 v2 v3).relIndex Cv = 2 := by
    have h1 := relIndex_mul_card (H := alpV v1 v2 v3) (K := Cv)
    have hc : Nat.card Cv = 128 := by
      rw [hCv, AlpEmb.card_centralizer_invRep D.E D.hF 2]
      rfl
    rw [inf_of_le_left hVCv, AlpEmb.card_alpV D.E, hc] at h1
    omega
  have hYV : 16 ≤ Nat.card (alpV v1 v2 v3 ⊓ Y : Subgroup G) := by
    have h1 := relIndex_mul_card (H := alpV v1 v2 v3) (K := Y)
    have h2 : (alpV v1 v2 v3).relIndex Y ≤ 2 := by
      rw [← hrelCv]
      exact relIndex_le_of_le_right hYCv (by rw [hrelCv]; norm_num)
    rw [hcardY] at h1
    nlinarith
  have hz2 : z * z = 1 := D.rep_sq 0
  have hzg2 : g⁻¹ * z * g * (g⁻¹ * z * g) = 1 := by
    calc g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
      _ = 1 := by rw [hz2]; group
  have hWY : alpW v1 v2 v3 ≤ Y := by
    refine D.W_le_of_sq hzg2 hYV fun y hy => ?_
    obtain ⟨c, hc, rfl⟩ := hy
    have hc' := hc
    rw [hCt, D.invRep_eq 5, AlpEmb.inf_centralizer_eq_map D.E] at hc'
    obtain ⟨c', hc'C, rfl⟩ := Subgroup.mem_map.1 hc'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have e : g⁻¹ * D.E.φ c' * g * (g⁻¹ * D.E.φ c' * g) = g⁻¹ * D.E.φ (c' * c') * g := by
      rw [map_mul]
      group
    rw [e]
    rcases cent_sq_E 1 c' (mem_centralizer_singleton_iff.1 hc'C) with h1 | h1
    · left
      rw [h1, map_one, mul_one, inv_mul_cancel]
    · right
      rw [h1, AlpEmb.φ_zc D.E]
      rfl
  obtain ⟨w, i, hwi, hi1, hwW, hwne⟩ : ∃ w : G, ∃ i : Fin 7, D.InClass i w ∧ i.val ≤ 1 ∧
      w ∈ alpW v1 v2 v3 ∧ w ≠ g⁻¹ * z * g := by
    by_cases hz : z = g⁻¹ * z * g
    · refine ⟨b, 1, D.inClass_rep 1, by decide, ?_, fun hb => ?_⟩
      · show v1 ^ 2 * v2 ^ 2 ∈ alpW v1 v2 v3
        exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · rw [← hz] at hb
        have hb' : invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 0 := hb
        exact absurd (InClass.unique D (hb' ▸ D.inClass_rep 1) (D.inClass_rep 0)) (by decide)
    · exact ⟨z, 0, D.inClass_rep 0, by decide, sq_mul_sq_mem_alpW v1 v2 v3, hz⟩
  obtain ⟨x, hx, hxw⟩ := hWY hwW
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hxw
  have hw2 := (D.mem_W_iff.1 hwW).2
  have hx2 : x * x = 1 := by
    rw [← hxw] at hw2
    calc x * x = g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  have hx1 : x ≠ 1 := by
    intro h1
    apply hwi.ne_one
    rw [← hxw, h1]
    group
  have hxz : x ≠ z := fun h1 => hwne (by rw [← hxw, h1])
  obtain ⟨j, hj, hcc⟩ := D.fus_of_cent (k := 1) hx hx2 hx1
  have hfus : D.Fus j i := D.inClass_fus hj hwi g hxw
  have key : ∀ j : Fin 7, centCount 1 j ≠ 0 → j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 := by decide
  have hj2 : D.Fus j 2 := by
    rcases key j hcc with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨c, hc, hcx⟩ := hj
      rw [D.z_central hc] at hcx
      exact absurd hcx.symm hxz
    · exact Fus.refl D 2
    · exact Fus.symm D hCD
    · exact Fus.symm D hCF
    · exact Fus.symm D hCG
  have hi0 : D.Fus 0 i := by
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · exact Fus.refl D 0
    · exact hAB
  exact hAC (hi0.trans D ((Fus.symm D hfus).trans D hj2))

end FusCtx

end CFSG.OddStandard.ONanRec

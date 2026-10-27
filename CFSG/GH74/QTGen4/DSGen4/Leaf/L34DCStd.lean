module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdIso
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdK
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdGen
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCStdNu
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCFrattini
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCWitnessDefs

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.Quasithin.H13.F431.L3.P3
open CFSG.GH74.KGroups (GF4)

section Membership

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem mem_inf_of_Ln {θ : MulAut ↥(Ln F)}
    (hθ : ∀ m : ↥(Ln F), (m : projectiveSL 3 F) ∈ Pt F ↔ ((θ m : ↥(Ln F)) : projectiveSL 3 F) ∈ Pt F)
    (m : ↥(Ln F)) :
    (m : projectiveSL 3 F) ∈ Ln F ⊓ Pt F ↔ ((θ m : ↥(Ln F)) : projectiveSL 3 F) ∈ Ln F ⊓ Pt F := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(θ m).2, (hθ m).mp h.2⟩, fun h => ⟨m.2, (hθ m).mpr h.2⟩⟩

theorem mem_inf_of_Pt {θ : MulAut ↥(Pt F)}
    (hθ : ∀ m : ↥(Pt F), (m : projectiveSL 3 F) ∈ Ln F ↔ ((θ m : ↥(Pt F)) : projectiveSL 3 F) ∈ Ln F)
    (m : ↥(Pt F)) :
    (m : projectiveSL 3 F) ∈ Ln F ⊓ Pt F ↔ ((θ m : ↥(Pt F)) : projectiveSL 3 F) ∈ Ln F ⊓ Pt F := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨(hθ m).mp h.1, (θ m).2⟩, fun h => ⟨(hθ m).mpr h.1, m.2⟩⟩

theorem mem_conj_Ln (b : projectiveSL 3 F) (hb : b ∈ Ln F) (x : projectiveSL 3 F) :
    b * x * b⁻¹ ∈ Ln F ↔ x ∈ Ln F := by
  constructor
  · intro h
    have h2 := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h) hb
    have e : b⁻¹ * (b * x * b⁻¹) * b = x := by group
    rw [← e]
    exact h2
  · intro h
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb h) (Subgroup.inv_mem _ hb)

end Membership

section Transport

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def dTorus (ψ : F ≃+* KF) : ↥(torus3 F) :=
  ⟨proj 3 F (dMat (Units.map ψ.symm.toMonoidHom (tU 1)) 1),
    mem_torus3.mpr ⟨Units.map ψ.symm.toMonoidHom (tU 1), 1, rfl⟩⟩

@[expose] noncomputable def dSgen (ψ : F ≃+* KF) : ↥(Ln F ⊓ Pt F) := nuNFEquiv F (0, 0, 0, dTorus ψ)

@[expose] noncomputable def xSgen : ↥(Ln F ⊓ Pt F) := nuNFEquiv F (1, 0, 0, 1)

@[expose] noncomputable def ySgen : ↥(Ln F ⊓ Pt F) := nuNFEquiv F (0, 1, 0, 1)

@[expose] noncomputable def EBmap (ψ : F ≃+* KF) : ↥(Ln F ⊓ Pt F) ≃* ↥B0 :=
  (MulEquiv.subgroupMap (projIso ψ) (Ln F ⊓ Pt F)).trans
    (MulEquiv.subgroupCongr (map_B0_projIso ψ))

theorem EBmap_coe (ψ : F ≃+* KF) (x : ↥(Ln F ⊓ Pt F)) :
    ((EBmap ψ x : ↥B0) : projectiveSL 3 KF) = projIso ψ (x : projectiveSL 3 F) :=
  rfl

theorem dS_val (ψ : F ≃+* KF) :
    (dSgen ψ : projectiveSL 3 F) = proj 3 F (dMat (Units.map ψ.symm.toMonoidHom (tU 1)) 1) := by
  unfold dSgen
  rw [nuNF_dd]
  rfl

theorem units_map_symm_map (ψ : F ≃+* KF) (u : Units KF) :
    Units.map ψ.toMonoidHom (Units.map ψ.symm.toMonoidHom u) = u := by
  ext
  simp

theorem EBmap_dSgen (ψ : F ≃+* KF) : EBmap ψ (dSgen ψ) = dB := by
  apply Subtype.ext
  rw [EBmap_coe, dS_val, projIso_dMat, units_map_symm_map, dB_val]
  have h1 : Units.map ψ.toMonoidHom (1 : Fˣ) = 1 := by
    ext
    simp
  rw [h1]
  rfl

theorem EBmap_xSgen (ψ : F ≃+* KF) : EBmap ψ xSgen = eB 16 := by
  apply Subtype.ext
  rw [EBmap_coe, eB16_val]
  unfold xSgen
  rw [nuNF_xS, projIso_xP, map_one]

theorem EBmap_ySgen (ψ : F ≃+* KF) : EBmap ψ ySgen = eB 4 := by
  apply Subtype.ext
  rw [EBmap_coe, eB4_val]
  unfold ySgen
  rw [nuNF_yS, projIso_yP, map_one]

@[expose] noncomputable def nKof (ψ : F ≃+* KF) (n : MulAut ↥(Ln F ⊓ Pt F)) : MulAut ↥B0 :=
  (EBmap ψ).symm.trans (n.trans (EBmap ψ))

theorem nKof_apply (ψ : F ≃+* KF) (n : MulAut ↥(Ln F ⊓ Pt F)) (x : ↥(Ln F ⊓ Pt F)) :
    nKof ψ n (EBmap ψ x) = EBmap ψ (n x) := by
  simp [nKof]

theorem nKof_coe (ψ : F ≃+* KF) (n : MulAut ↥(Ln F ⊓ Pt F)) (x : ↥(Ln F ⊓ Pt F)) :
    ((nKof ψ n (EBmap ψ x) : ↥B0) : projectiveSL 3 KF) =
      projIso ψ ((n x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
  rw [nKof_apply, EBmap_coe]

theorem classify_F (ψ : F ≃+* KF) (n : MulAut ↥(Ln F ⊓ Pt F))
    (hnd : n (dSgen ψ) = dSgen ψ ∨ n (dSgen ψ) = (dSgen ψ)⁻¹)
    (hnV : ∀ x : ↥(Ln F ⊓ Pt F), (x : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) ↔
      ((n x : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F))) :
    ∃ (ε : Bool) (sF tF κ₁ κ₂ : F), sF ≠ 0 ∧ tF ≠ 0 ∧
      n (dSgen ψ) = (if ε then (dSgen ψ)⁻¹ else dSgen ψ) ∧
      n xSgen = nuNFEquiv F (sF, 0, κ₁, 1) ∧
      n ySgen = nuNFEquiv F (0, tF, κ₂, 1) := by
  have hnK_d : nKof ψ n dB = dB ∨ nKof ψ n dB = dB⁻¹ := by
    rw [← EBmap_dSgen ψ, nKof_apply]
    rcases hnd with h | h
    · left
      rw [h]
    · right
      rw [h, map_inv]
  have hnK_V : ∀ b : ↥B0, (b : projectiveSL 3 KF) ∈ (V2' : Subgroup (projectiveSL 3 KF)) →
      ((nKof ψ n b : ↥B0) : projectiveSL 3 KF) ∈ (V2' : Subgroup (projectiveSL 3 KF)) := by
    intro b hb
    obtain ⟨x, rfl⟩ := (EBmap ψ).surjective b
    rw [nKof_coe]
    rw [EBmap_coe, projIso_mem_V2] at hb
    rw [projIso_mem_V2]
    exact (hnV x).mp hb
  obtain ⟨ε, A, B, C, C', hA, hB, hd, hx, hy⟩ := kClass (nKof ψ n) hnK_d hnK_V
  have hnz : ∀ X : GF4, X ≠ 0 → ψ.symm (psi X) ≠ 0 := by
    intro X hX h
    apply hX
    apply psi.injective
    rw [map_zero]
    have := congrArg ψ h
    rwa [map_zero, RingEquiv.apply_symm_apply] at this
  have hdS_val : projIso ψ ((dSgen ψ : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) = dB.1 := by
    rw [← EBmap_coe, EBmap_dSgen]
  refine ⟨ε, ψ.symm (psi A), ψ.symm (psi B), ψ.symm (psi C), ψ.symm (psi C'), hnz A hA,
    hnz B hB, ?_, ?_, ?_⟩
  · apply Subtype.ext
    apply (projIso ψ).injective
    have key1 : projIso ψ ((n (dSgen ψ) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        ((nKof ψ n dB : ↥B0) : projectiveSL 3 KF) := by
      rw [← EBmap_dSgen ψ, nKof_coe]
    rw [key1, hd]
    cases ε
    · simp [hdS_val]
    · simp [hdS_val, map_inv]
  · apply Subtype.ext
    rw [nuNF_sxw]
    apply (projIso ψ).injective
    have key2 : ((nKof ψ n (eB 16) : ↥B0) : projectiveSL 3 KF) =
        projIso ψ ((n xSgen : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
      rw [← EBmap_xSgen ψ, nKof_coe]
    rw [← key2, hx, map_mul, projIso_xP, projIso_wP, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]
  · apply Subtype.ext
    rw [nuNF_tyw]
    apply (projIso ψ).injective
    have key3 : ((nKof ψ n (eB 4) : ↥B0) : projectiveSL 3 KF) =
        projIso ψ ((n ySgen : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) := by
      rw [← EBmap_ySgen ψ, nKof_coe]
    rw [← key3, hy, map_mul, projIso_yP, projIso_wP, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]

theorem symm_gY (ψ : F ≃+* KF) :
    (fun l => (EBmap ψ).symm (gY l)) = ![dSgen ψ, xSgen, ySgen] := by
  funext l
  fin_cases l
  · show (EBmap ψ).symm dB = dSgen ψ
    rw [← EBmap_dSgen ψ, MulEquiv.symm_apply_apply]
  · show (EBmap ψ).symm (eB 16) = xSgen
    rw [← EBmap_xSgen ψ, MulEquiv.symm_apply_apply]
  · show (EBmap ψ).symm (eB 4) = ySgen
    rw [← EBmap_ySgen ψ, MulEquiv.symm_apply_apply]

theorem words_S (ψ : F ≃+* KF) (x : ↥(Ln F ⊓ Pt F)) :
    ∃ w : List (Fin 3), x = wordEval w ![dSgen ψ, xSgen, ySgen] := by
  obtain ⟨w, hw⟩ := B0_words (EBmap ψ x)
  refine ⟨w, ?_⟩
  have h1 : (EBmap ψ).symm (EBmap ψ x) = x := MulEquiv.symm_apply_apply _ x
  rw [← h1, hw]
  rw [show (EBmap ψ).symm (evalB w gY) = wordEval w (fun l => (EBmap ψ).symm (gY l)) from
    map_wordEval ((EBmap ψ).symm : ↥B0 →* ↥(Ln F ⊓ Pt F)) gY w, symm_gY]

theorem dcStd_of_witnesses {F : Type} [Field F] [Finite F] [CharP F 2]
    (hq : Nat.card F = 4) (hLn : ∀ κ : F, WitnessLn F κ) (hPt : ∀ κ : F, WitnessPt F κ) :
    DCStd F := by
  unfold DCStd DCProp
  intro σ hσ
  obtain ⟨ψ⟩ : Nonempty (F ≃+* KF) :=
    ⟨CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) (by rw [hq]; norm_num)⟩
  have hcore : CFSG.Open.pCoreOf 2 (Ln F) = (V2 : Subgroup (projectiveSL 3 F)) := core_V2
  have hσ' : ∀ b : ↥(Ln F ⊓ Pt F), (b : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) ↔
      ((σ b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) ∈ (V2 : Subgroup (projectiveSL 3 F)) := by
    intro b
    have h := hσ b
    rw [hcore] at h
    exact h
  have hBV : Ln F ⊓ Pt F ≤ Subgroup.normalizer ((V2 : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := inf_le_left
  have hB : Nat.card ↥(Ln F ⊓ Pt F) = 192 := (Nat.card_congr (EBmap ψ).toEquiv).trans natCard_B0K
  have hdord : Nat.card (Subgroup.zpowers (dSgen ψ)) = 3 := by
    rw [Nat.card_zpowers, ← MulEquiv.orderOf_eq (EBmap ψ) (dSgen ψ), EBmap_dSgen, orderOf_dB]
  obtain ⟨b₀, n, hσeq, hnd, hnV⟩ := frattini_reduction hBV hB hdord σ hσ'
  obtain ⟨ε, sF, tF, κ₁, κ₂, hsF, htF, hnd_val, hnxS, hnyS⟩ := classify_F ψ n hnd hnV
  let sU : Fˣ := Units.mk0 sF hsF
  let tU' : Fˣ := Units.mk0 tF htF
  obtain ⟨θT, hθT1, hθT2⟩ := leaf_T13 hq sU tU' ε
  obtain ⟨θL, hθL1, hθL2⟩ := hLn (κ₁ * (sF ^ 2)⁻¹)
  obtain ⟨θP, hθP1, hθP2⟩ := hPt (κ₂ * (tF ^ 2)⁻¹)
  have hSLn : Ln F ⊓ Pt F ≤ Ln F := inf_le_left
  have hSPt : Ln F ⊓ Pt F ≤ Pt F := inf_le_right
  let rT : ↥(Ln F ⊓ Pt F) →* ↥(Ln F ⊓ Pt F) := restrictHom hSLn θT (fun m => mem_inf_of_Ln hθT1 m)
  let rL : ↥(Ln F ⊓ Pt F) →* ↥(Ln F ⊓ Pt F) := restrictHom hSLn θL (fun m => mem_inf_of_Ln hθL1 m)
  let rP : ↥(Ln F ⊓ Pt F) →* ↥(Ln F ⊓ Pt F) := restrictHom hSPt θP (fun m => mem_inf_of_Pt hθP1 m)
  let c : ↥(Ln F ⊓ Pt F) →* ↥(Ln F ⊓ Pt F) := rP.comp (rL.comp rT)
  have e1 : ∀ y : ↥(Ln F ⊓ Pt F), rT y = nuMap sU tU' 0 0 ε y := fun y =>
    restrictHom_eq_of hSLn θT _ (fun y' => nuMap sU tU' 0 0 ε y') (fun b m hm => hθT2 b m hm) y
  have e2 : ∀ y : ↥(Ln F ⊓ Pt F), rL y = nuMap 1 1 (κ₁ * (sF ^ 2)⁻¹) 0 false y := fun y =>
    restrictHom_eq_of hSLn θL _ (fun y' => nuMap 1 1 (κ₁ * (sF ^ 2)⁻¹) 0 false y')
      (fun b m hm => hθL2 b m hm) y
  have e3 : ∀ y : ↥(Ln F ⊓ Pt F), rP y = nuMap 1 1 0 (κ₂ * (tF ^ 2)⁻¹) false y := fun y =>
    restrictHom_eq_of hSPt θP _ (fun y' => nuMap 1 1 0 (κ₂ * (tF ^ 2)⁻¹) false y')
      (fun b m hm => hθP2 b m hm) y
  have hc : ∀ x : ↥(Ln F ⊓ Pt F), c x = nuMap 1 1 0 (κ₂ * (tF ^ 2)⁻¹) false
      (nuMap 1 1 (κ₁ * (sF ^ 2)⁻¹) 0 false (nuMap sU tU' 0 0 ε x)) := by
    intro x
    show rP (rL (rT x)) = _
    rw [e1 x, e2, e3]
  have hcd : c (dSgen ψ) = if ε = true then (dSgen ψ)⁻¹ else dSgen ψ := by
    rw [hc]
    have hd' : dSgen ψ = nuNFEquiv F (0, 0, 0, dTorus ψ) := rfl
    rw [hd', phi_dd]
    cases ε
    · simp
    · simp only [if_true]
      rw [nuNF_dd_inv]
  have hcx : c xSgen = nuNFEquiv F (sF, 0, κ₁, 1) := by
    rw [hc]
    have hx' : xSgen = nuNFEquiv F (1, 0, 0, 1) := rfl
    rw [hx', phi_xS]
    have hκ : κ₁ * (sF ^ 2)⁻¹ * sF ^ 2 = κ₁ := by
      field_simp
    show nuNFEquiv F (sF, 0, κ₁ * (sF ^ 2)⁻¹ * sF ^ 2, 1) = _
    rw [hκ]
  have hcy : c ySgen = nuNFEquiv F (0, tF, κ₂, 1) := by
    rw [hc]
    have hy' : ySgen = nuNFEquiv F (0, 1, 0, 1) := rfl
    rw [hy', phi_yS]
    have hκ : κ₂ * (tF ^ 2)⁻¹ * tF ^ 2 = κ₂ := by
      field_simp
    show nuNFEquiv F (0, tF, κ₂ * (tF ^ 2)⁻¹ * tF ^ 2, 1) = _
    rw [hκ]
  have hnc : (n : ↥(Ln F ⊓ Pt F) →* ↥(Ln F ⊓ Pt F)) = c := by
    apply eq_of_words _ _ ![dSgen ψ, xSgen, ySgen] (words_S ψ)
    intro l
    fin_cases l
    · show n (dSgen ψ) = c (dSgen ψ)
      rw [hcd, hnd_val]
    · show n xSgen = c xSgen
      rw [hcx, hnxS]
    · show n ySgen = c ySgen
      rw [hcy, hnyS]
  have hb₀L : (b₀ : projectiveSL 3 F) ∈ Ln F := (Subgroup.mem_inf.mp b₀.2).1
  have hb₀P : (b₀ : projectiveSL 3 F) ∈ Pt F := (Subgroup.mem_inf.mp b₀.2).2
  let gP : ↥(Pt F) := ⟨(b₀ : projectiveSL 3 F), hb₀P⟩
  have hkey : ∀ m₂ : ↥(Pt F), (((MulAut.conj gP * θP) m₂ : ↥(Pt F)) : projectiveSL 3 F) =
      (b₀ : projectiveSL 3 F) * ((θP m₂ : ↥(Pt F)) : projectiveSL 3 F) * (b₀ : projectiveSL 3 F)⁻¹ := by
    intro m₂
    simp [MulAut.mul_apply, MulAut.conj_apply, gP]
  refine ⟨θL * θT, MulAut.conj gP * θP, ?_, ?_, ?_⟩
  · intro m
    exact (hθT1 m).trans (hθL1 (θT m))
  · intro m
    rw [hkey m, mem_conj_Ln _ hb₀L]
    exact hθP1 m
  · intro b m₁ m₂ h1 h2
    have s1 : ((rT b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        ((θT m₁ : ↥(Ln F)) : projectiveSL 3 F) :=
      restrictHom_coe_of hSLn θT (fun m => mem_inf_of_Ln hθT1 m) b m₁ h1
    have s2 : ((rL (rT b) : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        ((θL (θT m₁) : ↥(Ln F)) : projectiveSL 3 F) :=
      restrictHom_coe_of hSLn θL (fun m => mem_inf_of_Ln hθL1 m) (rT b) (θT m₁) s1.symm
    have s3 : ((c b : ↥(Ln F ⊓ Pt F)) : projectiveSL 3 F) =
        ((θP m₂ : ↥(Pt F)) : projectiveSL 3 F) :=
      restrictHom_coe_of hSPt θP (fun m => mem_inf_of_Pt hθP1 m) (rL (rT b)) m₂
        (by rw [s2]; exact h2.symm)
    have hcb : c b = n b := (DFunLike.congr_fun hnc b).symm
    rw [hkey m₂, ← s3, hcb, hσeq]
    simp [MulAut.mul_apply, MulAut.conj_apply]

end Transport

end CFSG.GH74.QTGen4.DSGen4.L34

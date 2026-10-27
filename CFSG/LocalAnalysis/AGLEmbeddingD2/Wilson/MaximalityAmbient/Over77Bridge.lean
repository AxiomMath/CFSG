module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.EncBridge
public import Certificates.Certificate12631
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen
public import CFSG.Sporadic.Schreier.J4SElevenBase1


public section

set_option linter.unusedSectionVars false

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc CFSG.Quasithin.J4Rad

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem subgroupOf_closure_eq {G : Type*} [Group G] (H : Subgroup G) (S : Set G) (hS : S ⊆ H) :
    (Subgroup.closure S).subgroupOf H = Subgroup.closure (H.subtype ⁻¹' S) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have key : ∀ y (hy : y ∈ Subgroup.closure S), ∃ h : y ∈ H,
        (⟨y, h⟩ : H) ∈ Subgroup.closure (H.subtype ⁻¹' S) := by
      intro y hy
      induction hy using Subgroup.closure_induction with
      | mem y hy => exact ⟨hS hy, Subgroup.subset_closure hy⟩
      | one => exact ⟨H.one_mem, Subgroup.one_mem _⟩
      | mul y z _ _ hy hz =>
        obtain ⟨h1, h2⟩ := hy
        obtain ⟨h3, h4⟩ := hz
        exact ⟨H.mul_mem h1 h3, Subgroup.mul_mem _ h2 h4⟩
      | inv y _ hy =>
        obtain ⟨h1, h2⟩ := hy
        exact ⟨H.inv_mem h1, Subgroup.inv_mem _ h2⟩
    obtain ⟨h, h'⟩ := key x hx
    exact h'
  · rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (Subgroup.subset_closure hx)

section Act


theorem rho_apply_of_actOK (hF : J4Facts) {g : J} (hg : g ∈ M2) {X : Array Nat}
    (hX : Mx g = CFSG.Sporadic.SmallF2.rowsMatrix 112 X) {π : Array Nat} (h : actOK X π = true)
    (i : Fin 77) : (rho hF ⟨g, hg⟩ i : ℕ) = π.getD i 0 := by
  unfold actOK at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlt, hfr⟩ := h i i.2
  have h1 : g • pt i = pt (π.getD i 0) := by
    apply rowOf_injective hF
    rw [rowOf_smul hF.mat, rowOf_pt hF.mat i.2, rowOf_pt hF.mat hlt]
    refine smul_toRow_of_frApply (X := X.map CFSG.Quasithin.J4M2.natToV2) ?_ ?_
    · rw [EncBridge.rowsMatrix_map_natToV2]; exact hX
    · exact hfr
  have h2 := (rho_spec hF ⟨g, hg⟩ i ⟨π.getD i 0, hlt⟩).2 h1
  rw [h2]

end Act


section Reps

open CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native
open CFSG.AGLEmbeddingD2.Wilson.Coordinator

theorem mx_eq_of_rep {g : J} {P : Pair} (h : Rep Sp φ g P) :
    Mx g = CFSG.Sporadic.SmallF2.rowsMatrix 112 P.1 := h.2.2.1.symm

variable
  (hM : MatFacts)
include hM

omit hM in
theorem bridge_parts :
    zM.size = 112 ∧ O.eq (O.mul zRowsN zRowsN) O.one = true ∧
    actOK cAP.1 dataA = true ∧ actOK cBP.1 dataB = true ∧ actOK cZP.1 dataZ = true ∧
    commOK cAP.1 = true ∧ commOK cBP.1 = true ∧ commOK cZP.1 = true := by
  have hz : bridgeCheck = true := Certificates.certificate12631
  unfold bridgeCheck at hz
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hz
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem rep_z0 : Rep Sp φ z0 zPN := by
  obtain ⟨hs, hsq, -⟩ := bridge_parts
  have hWF : Sp.WF zRowsN := by
    show zRowsN.size = 112
    simp [zRowsN, hs]
  have hmat : Sp.toMat zRowsN = φ z0 := by
    show CFSG.Sporadic.SmallF2.rowsMatrix 112 zRowsN = φ z0
    rw [zRowsN, EncBridge.rowsMatrix_map_toNat, rowsMatrix_zM hM]
    rfl
  have h1 := Sp.toMat_eq (Sp.mul_wf hWF hWF) Sp.one_wf hsq
  rw [Sp.toMat_mul hWF hWF, Sp.toMat_one, hmat, ← map_mul] at h1
  have hsq' : z0 * z0 = 1 := φ_injective (by rw [h1, map_one])
  refine rep_of hWF hWF hmat ?_
  have hinv : z0⁻¹ = z0 := inv_eq_of_mul_eq_one_right hsq'
  rw [hinv]
  exact hmat

omit
  hM in
theorem hW_eq : hW = signedWord a b hWordN := by
  unfold hW wordProd signedWord
  congr 1

theorem rep_hW : Rep Sp φ hW hWP := by
  rw [hW_eq]
  exact rep_wordP (rep_a hM) (rep_b hM) hWordN

theorem rep_gam : Rep Sp φ gam gamP :=
  rep_mulP (rep_powP (rep_mulP (rep_z0 hM) (rep_mulP (rep_mulP (rep_hW hM) (rep_powP rep_nrm₂ 20))
    (rep_invP (rep_hW hM)))) 6) (rep_hW hM)

theorem rep_cA : Rep Sp φ cA cAP :=
  rep_mulP (rep_mulP (rep_gam hM) (rep_mulP (rep_powP rep_qy 10) rep_nrm₁)) (rep_invP (rep_gam hM))

theorem rep_cB : Rep Sp φ cB cBP :=
  rep_mulP (rep_mulP (rep_gam hM) rep_nrm₂) (rep_invP (rep_gam hM))

theorem rep_cZ : Rep Sp φ cZ cZP :=
  rep_mulP (rep_mulP (rep_gam hM) rep_qz) (rep_invP (rep_gam hM))


theorem mem_M2_of_rep {g : J} {P : Pair}
    (hP : Rep Sp φ g P) (h : commOK P.1 = true) : g ∈ M2 := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have hz := rep_z0 hM
  have h1 := Sp.toMat_eq (Sp.mul_wf hP.1 hz.1) (Sp.mul_wf hz.1 hP.1) h
  rw [Sp.toMat_mul hP.1 hz.1, Sp.toMat_mul hz.1 hP.1, hP.2.2.1, hz.2.2.1, ← map_mul, ← map_mul] at h1
  exact (φ_injective h1).symm

theorem cA_mem : cA ∈ M2 := mem_M2_of_rep hM (rep_cA hM) (bridge_parts.2.2.2.2.2.1)
theorem cB_mem : cB ∈ M2 := mem_M2_of_rep hM (rep_cB hM) (bridge_parts.2.2.2.2.2.2.1)
theorem cZ_mem : cZ ∈ M2 := mem_M2_of_rep hM (rep_cZ hM) (bridge_parts.2.2.2.2.2.2.2)

end Reps


theorem encP_eq_of_apply (g : Equiv.Perm (Fin 77)) (d : Array Nat) (hd : d.size = 77)
    (h : ∀ i : Fin 77, (g i : Nat) = d.getD i 0) : encP g = d := by
  apply Array.ext
  · simp [encP, hd]
  · intro i h1 h2
    have hi : i < 77 := by simpa [encP] using h1
    have := h ⟨i, hi⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h2] at this
    simpa [encP] using this

theorem sigData_length : ∀ n < 32, (sigData[n]!).length = 77 := by decide +kernel

section Final

open CFSG.AGLEmbeddingD2.Wilson.Coordinator

variable
  (hF : J4Facts)

theorem rho_cA (i : Fin 77) : (rho hF ⟨cA, cA_mem hF.mat⟩ i : ℕ) = dataA.getD i 0 :=
  rho_apply_of_actOK hF (cA_mem hF.mat) (X := cAP.1) (mx_eq_of_rep (rep_cA hF.mat))
    bridge_parts.2.2.1 i

theorem rho_cB (i : Fin 77) : (rho hF ⟨cB, cB_mem hF.mat⟩ i : ℕ) = dataB.getD i 0 :=
  rho_apply_of_actOK hF (cB_mem hF.mat) (X := cBP.1) (mx_eq_of_rep (rep_cB hF.mat))
    bridge_parts.2.2.2.1 i

theorem rho_cZ (i : Fin 77) : (rho hF ⟨cZ, cZ_mem hF.mat⟩ i : ℕ) = dataZ.getD i 0 :=
  rho_apply_of_actOK hF (cZ_mem hF.mat) (X := cZP.1) (mx_eq_of_rep (rep_cZ hF.mat))
    bridge_parts.2.2.2.2.1 i

theorem encP_sigPerm {n : Nat} (hn : n < 32) : encP (sigPerm n) = (sigData[n]!).toArray :=
  encP_eq_of_apply _ _ (by rw [List.size_toArray]; exact sigData_length n hn) fun i => by
    rw [sigPerm_val hn i]
    simp [Array.getD_eq_getD_getElem?, List.getElem!_eq_getElem?_getD]

@[expose] def nIdx : Fin 9 → Nat := ![12, 13, 14, 15, 16, 28, 29, 30, 17]

@[expose] def sPerm (k : Fin 9) : Equiv.Perm (Fin 77) := sigPerm (nIdx k)

theorem nIdx_lt : ∀ k, nIdx k < 32 := by decide

theorem Mbar_le_closure_sPerm : Mbar ≤ Subgroup.closure (Set.range sPerm) := by
  rw [Mbar, Subgroup.closure_le]
  intro x hx
  simp only [oddPerms, tPerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, or_assoc] at hx
  apply Subgroup.subset_closure
  rcases hx with h | h | h | h | h | h | h | h | h
  · refine Set.mem_range.2 ⟨(0 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(1 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(2 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(3 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(4 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(5 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(6 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(7 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]
  · refine Set.mem_range.2 ⟨(8 : Fin 9), ?_⟩
    simp [sPerm, nIdx, h]

theorem sigData_dataS : ∀ k : Fin 9, (sigData[nIdx k]!).toArray = dataS.getD k idA := by
  decide +kernel

theorem encP_sPerm (k : Fin 9) : encP (sPerm k) = dataS.getD k idA := by
  rw [sPerm, encP_sigPerm (nIdx_lt k)]
  exact sigData_dataS k

theorem encP_sigma : encP (sigPerm 15 * sigPerm 29) = dataSigma := by
  rw [encP_mul, encP_sigPerm (by norm_num), encP_sigPerm (by norm_num)]
  decide +kernel

include hF

theorem mElt_mem_M2 : mElt ∈ M2 := by
  have g : ∀ n < 32, gE n ∈ M2 := fun n hn => gE_mem_M2 hF.mat hn
  unfold mElt
  exact M2.mul_mem (M2.mul_mem (M2.mul_mem (M2.mul_mem (M2.mul_mem (g 15 (by norm_num))
    (g 29 (by norm_num))) (g 1 (by norm_num))) (g 7 (by norm_num))) (g 9 (by norm_num)))
    (g 11 (by norm_num))

theorem rho_mElt : rho hF ⟨mElt, mElt_mem_M2 hF⟩ = sigPerm 15 * sigPerm 29 := by
  have g : ∀ n < 32, gE n ∈ M2 := fun n hn => gE_mem_M2 hF.mat hn
  have e : (⟨mElt, mElt_mem_M2 hF⟩ : ↥M2) = ⟨gE 15, g 15 (by norm_num)⟩ *
      ⟨gE 29, g 29 (by norm_num)⟩ * ⟨gE 1, g 1 (by norm_num)⟩ * ⟨gE 7, g 7 (by norm_num)⟩ *
      ⟨gE 9, g 9 (by norm_num)⟩ * ⟨gE 11, g 11 (by norm_num)⟩ := rfl
  rw [e, map_mul, map_mul, map_mul, map_mul, map_mul, rho_gE_perm hF (by norm_num : 15 < 32),
    rho_gE_perm hF (by norm_num : 29 < 32), rho_gE_perm hF (by norm_num : 1 < 32),
    rho_gE_perm hF (by norm_num : 7 < 32), rho_gE_perm hF (by norm_num : 9 < 32),
    rho_gE_perm hF (by norm_num : 11 < 32), sigPerm_q (by norm_num : 1 < 12),
    sigPerm_q (by norm_num : 7 < 12), sigPerm_q (by norm_num : 9 < 12),
    sigPerm_q (by norm_num : 11 < 12)]
  simp

theorem map_rho_C0p : (C0p.subgroupOf M2).map (rho hF) =
    Subgroup.closure {rho hF ⟨cA, cA_mem hF.mat⟩, rho hF ⟨cB, cB_mem hF.mat⟩,
      rho hF ⟨cZ, cZ_mem hF.mat⟩} := by
  have hS : ({cA, cB, cZ} : Set J) ⊆ M2 := by
    rintro x (rfl | rfl | rfl)
    · exact cA_mem hF.mat
    · exact cB_mem hF.mat
    · exact cZ_mem hF.mat
  rw [C0p, subgroupOf_closure_eq M2 _ hS, MonoidHom.map_closure]
  congr 1
  ext p
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with h | h | h
    · have hx' : x = ⟨cA, cA_mem hF.mat⟩ := Subtype.ext h
      rw [hx']; exact Or.inl rfl
    · have hx' : x = ⟨cB, cB_mem hF.mat⟩ := Subtype.ext h
      rw [hx']; exact Or.inr (Or.inl rfl)
    · have hx' : x = ⟨cZ, cZ_mem hF.mat⟩ := Subtype.ext h
      rw [hx']; exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨⟨cA, cA_mem hF.mat⟩, Or.inl rfl, rfl⟩
    · exact ⟨⟨cB, cB_mem hF.mat⟩, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨⟨cZ, cZ_mem hF.mat⟩, Or.inr (Or.inr rfl), rfl⟩

theorem over77 (L : Subgroup (Equiv.Perm (Fin 77)))
    (hPL : (C0p.subgroupOf M2).map (rho hF) ≤ L) (hL : L ≤ (rho hF).range)
    (hnot : ¬ L ≤ (C0p.subgroupOf M2).map (rho hF)) :
    rho hF ⟨mElt, mElt_mem_M2 hF⟩ ∈ L := by
  rw [rho_mElt]
  rw [map_rho_C0p hF] at hPL hnot
  have hL' : L ≤ Subgroup.closure (Set.range sPerm) :=
    hL.trans ((range_rho_eq hF).le.trans Mbar_le_closure_sPerm)
  exact over77_of_certificate _ _ _ _ sPerm
    (encP_eq_of_apply _ _ (by decide) (rho_cA hF)) (encP_eq_of_apply _ _ (by decide) (rho_cB hF))
    (encP_eq_of_apply _ _ (by decide) (rho_cZ hF)) encP_sigma encP_sPerm L hPL hL' hnot

end Final

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Over77

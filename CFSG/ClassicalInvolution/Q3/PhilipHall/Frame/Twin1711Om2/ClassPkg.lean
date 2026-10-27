module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.SetOrbit
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om1.ClassPkg
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Om2.Relations

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Check
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Check (reflTab wA wordOK eA keyF)
open CFSG.ClassicalInvolution.Generic
open scoped Pointwise

set_option linter.unusedSectionVars false


@[expose] noncomputable def negSetY (q : HY) : Finset (Fin 480) :=
  Finset.univ.filter fun r => phi q r = phi (cK 2) r

private theorem cp2_mem_negSetY {q : HY} {r : Fin 480} :
    r ∈ negSetY q ↔ phi q r = phi (cK 2) r := by
  simp [negSetY]

private theorem cp2_mem_smul_finset {g : Equiv.Perm (Fin 480)} {S : Finset (Fin 480)}
    {r : Fin 480} : r ∈ g • S ↔ g⁻¹ r ∈ S := by
  conv_lhs => rw [← inv_inv g]
  exact Finset.mem_inv_smul_finset_iff

private theorem cp2_phi_cK_comm (x : HY) (s : Fin 480) :
    phi (cK 2) (phi x s) = phi x (phi (cK 2) s) := by
  have h := congrArg (fun u => phi u s) (cK_comm 2 x)
  simpa using h.symm

theorem negSetY_conj (x q : HY) : negSetY (x * q * x⁻¹) = x • negSetY q := by
  ext r
  rw [smul_def, cp2_mem_negSetY, cp2_mem_smul_finset, cp2_mem_negSetY]
  obtain ⟨s, rfl⟩ : ∃ s, r = phi x s := ⟨(phi x)⁻¹ r, by simp⟩
  have e : phi (x * q * x⁻¹) (phi x s) = phi x (phi q s) := by simp
  have e' : (phi x)⁻¹ (phi x s) = s := by simp
  rw [e, e', cp2_phi_cK_comm x s]
  exact (phi x).injective.eq_iff

theorem centralizer_le_stabilizerY (q : HY) :
    Subgroup.centralizer {q} ≤ MulAction.stabilizer HY (negSetY q) := by
  intro x hx
  rw [MulAction.mem_stabilizer_iff, ← negSetY_conj]
  have h : x * q = q * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  rw [h, mul_inv_cancel_right]

@[expose] noncomputable def closureG : Subgroup HY := Subgroup.closure (genE '' {k | k < 8})

private theorem cp2_enum_parts :
    enumSizeY (lettersY (reflTab ())) wS0 4096 = true ∧
      enumSizeY (lettersY (reflTab ())) wP3 27 = true ∧
      enumSizeY (lettersY (reflTab ())) wSc 1024 = true ∧
      enumSizeY (lettersY (reflTab ())) wPc 3 = true := by
  have h := om2A_parts.2.2.2.1
  simp only [enumCheckY, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  exact ⟨h1, h2, h3, h4⟩

private theorem cp2_card_S0 : Nat.card (closureY wS0) = 4096 :=
  (enumSizeY_spec (wordYOK_of_sub wS0_sub) cp2_enum_parts.1).1

private theorem cp2_card_P3 : Nat.card (closureY wP3) = 27 :=
  (enumSizeY_spec (wordYOK_of_sub wP3_sub) cp2_enum_parts.2.1).1

private theorem cp2_card_Sc : Nat.card (closureY wSc) = 1024 :=
  (enumSizeY_spec (wordYOK_of_sub wSc_sub) cp2_enum_parts.2.2.1).1

private theorem cp2_card_Pc : Nat.card (closureY wPc) = 3 :=
  (enumSizeY_spec (wordYOK_of_sub wPc_sub) cp2_enum_parts.2.2.2).1

private theorem cp2_orbit_part :
    orbSizeY (genY (reflTab ())) (fCodeY (wY (lettersY (reflTab ())) wT0)) 6300 = true := by
  have h := om2A_parts.2.2.2.2.1
  simp only [orbitCheckY, Bool.and_eq_true] at h
  exact h.2

private theorem cp2_ncard_orbit {F : Array ℕ} {sz : ℕ}
    (h : orbSizeY (genY (reflTab ())) F sz = true) :
    (MulAction.orbit closureG (decFY F)).ncard = sz := by
  have h' := (orbSizeY_spec (gens := genE) (fun k hk => rep_genY hk) h).2.1
  have hsz : (genY (reflTab ())).size = 8 := by simp [genY]
  rw [hsz] at h'
  exact h'

private theorem cp2_wordYOK_wT0 : wordYOK wT0 = true :=
  (wordsCheckY_spec (by simp [allWordsY] : wT0 ∈ allWordsY)).1

private theorem cp2_decFY_wT0 :
    decFY (fCodeY (wY (lettersY (reflTab ())) wT0)) = negSetY t0Y := by
  rw [decFY_fCodeY (rep_wordE cp2_wordYOK_wT0)]
  rfl

private theorem cp2_closureY_mono {ws ws' : List (List ℕ)} (h : ∀ w ∈ ws, w ∈ ws') :
    closureY ws ≤ closureY ws' :=
  Subgroup.closure_mono (Set.image_mono fun w hw => h w hw)

private theorem cp2_closureY_le {ws : List (List ℕ)} {K : Subgroup HY}
    (h : ∀ w ∈ ws, wordE w ∈ K) : closureY ws ≤ K := by
  rw [closureY, Subgroup.closure_le]
  rintro _ ⟨w, hw, rfl⟩
  exact h w hw

private theorem cp2_pkg {C : Subgroup HY} {t : HY} {c o : ℕ} {F : Array ℕ}
    (hdec : decFY F = negSetY t) (horb : orbSizeY (genY (reflTab ())) F o = true)
    (hC : C ≤ Subgroup.centralizer {t}) (hc : c ≤ Nat.card C) (hco : c * o = 696729600) :
    C = MulAction.stabilizer HY (negSetY t) ∧
      MulAction.orbit closureG (negSetY t) = MulAction.orbit HY (negSetY t) ∧
      Nat.card C = c ∧ (MulAction.orbit HY (negSetY t)).ncard = o := by
  have ho : o ≤ (MulAction.orbit closureG (negSetY t)).ncard := by
    rw [← hdec, cp2_ncard_orbit horb]
  refine OmGen.stab_eq_of_card (negSetY t) C closureG
    (hC.trans (centralizer_le_stabilizerY t)) hc ho ?_
  rw [hco]
  exact card_YP.le

theorem classPkg0Y :
    closureY wT = T0Y ∧ T0Y = MulAction.stabilizer HY (negSetY t0Y) ∧ Nat.card T0Y = 110592 ∧
      Nat.card (closureY wS0) = 4096 ∧ Nat.card (closureY wP3) = 27 ∧
      closureY wS0 ≤ T0Y ∧ closureY wP3 ≤ T0Y ∧
      MulAction.orbit closureG (negSetY t0Y) = MulAction.orbit HY (negSetY t0Y) ∧
      (MulAction.orbit HY (negSetY t0Y)).ncard = 6300 := by
  have hCT : closureY wT ≤ T0Y := cp2_closureY_le fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_t0Y_of_mem hw)
  have hS0C : closureY wS0 ≤ closureY wT :=
    cp2_closureY_mono fun w hw => List.mem_append_left _ hw
  have hP3C : closureY wP3 ≤ closureY wT :=
    cp2_closureY_mono fun w hw => List.mem_append_right _ hw
  have hdvd : 110592 ∣ Nat.card (closureY wT) := by
    have d1 : 4096 ∣ Nat.card (closureY wT) := cp2_card_S0 ▸ Subgroup.card_dvd_of_le hS0C
    have d2 : 27 ∣ Nat.card (closureY wT) := cp2_card_P3 ▸ Subgroup.card_dvd_of_le hP3C
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) d1 d2
  have hc : 110592 ≤ Nat.card (closureY wT) := Nat.le_of_dvd Nat.card_pos hdvd
  obtain ⟨hCeq, horb, hcard, hncard⟩ := cp2_pkg (F := fCodeY (wY (lettersY (reflTab ())) wT0))
    (o := 6300) (c := 110592) cp2_decFY_wT0 cp2_orbit_part hCT hc (by norm_num)
  have hTeq : T0Y = MulAction.stabilizer HY (negSetY t0Y) :=
    le_antisymm (centralizer_le_stabilizerY t0Y) (hCeq.ge.trans hCT)
  have hCT' : closureY wT = T0Y := hCeq.trans hTeq.symm
  refine ⟨hCT', hTeq, ?_, cp2_card_S0, cp2_card_P3, hS0C.trans hCT, hP3C.trans hCT, horb, hncard⟩
  rw [← hCT']
  exact hcard

private noncomputable def cp2_fst : HY →* WP := (MonoidHom.fst WP WP).comp YP.subtype

private theorem cp2_fst_surjective : Function.Surjective cp2_fst := by
  intro x
  obtain ⟨y, hy⟩ := pHat_surjective (sigmaO (pHat x))
  exact ⟨⟨(x, y), mem_YP.2 hy.symm⟩, rfl⟩

private theorem cp2_fst_tcY : cp2_fst tcY = Om1.tc := fst_tcY

private theorem cp2_fst_cK1 : cp2_fst (cK 1) = 1 := by
  simp [cp2_fst, cK]

theorem classPkgCY :
    Nat.card (Subgroup.centralizer {tcY}) ∣ 2 ^ 10 * 3 ∧ Nat.card (closureY wSc) = 2 ^ 10 ∧
      closureY wSc ≤ Subgroup.centralizer {tcY} ∧ closureY wCc ≤ Subgroup.centralizer {tcY} := by
  have hScCc : closureY wSc ≤ closureY wCc :=
    cp2_closureY_mono fun w hw => List.mem_append_left _ hw
  have hPcCc : closureY wPc ≤ closureY wCc :=
    cp2_closureY_mono fun w hw => List.mem_append_right _ hw
  have hCc : closureY wCc ≤ Subgroup.centralizer {tcY} := cp2_closureY_le fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_tcY_of_mem hw)
  have hlow : 3072 ∣ Nat.card (Subgroup.centralizer {tcY}) := by
    have d1 : 1024 ∣ Nat.card (Subgroup.centralizer {tcY}) :=
      cp2_card_Sc ▸ Subgroup.card_dvd_of_le (hScCc.trans hCc)
    have d2 : 3 ∣ Nat.card (Subgroup.centralizer {tcY}) :=
      cp2_card_Pc ▸ Subgroup.card_dvd_of_le (hPcCc.trans hCc)
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 1024 3) d1 d2
  have hD : Nat.card (Subgroup.centralizer {Om1.tc}) = 3072 := by
    have := (Om1.classPkgC).2.1
    simpa using this
  have hM : Nat.card ((Subgroup.centralizer {Om1.tc}).comap cp2_fst) = 6144 := by
    have h1 := Subgroup.card_mul_index ((Subgroup.centralizer {Om1.tc}).comap cp2_fst)
    have h2 := Subgroup.card_mul_index (Subgroup.centralizer {Om1.tc})
    have hY : Nat.card HY = 696729600 := card_YP
    have hW : Nat.card WP = 348364800 := card_wPlus
    rw [Subgroup.index_comap_of_surjective _ cp2_fst_surjective, hY] at h1
    rw [hD, hW] at h2
    have hidx : (Subgroup.centralizer {Om1.tc}).index = 113400 := by omega
    rw [hidx] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 113400) (h1.trans (by norm_num))
  have hCM : Subgroup.centralizer {tcY} ≤ (Subgroup.centralizer {Om1.tc}).comap cp2_fst := by
    intro c hc
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h : c * tcY = tcY * c := Subgroup.mem_centralizer_singleton_iff.1 hc
    have h' := congrArg cp2_fst h
    rw [map_mul, map_mul, cp2_fst_tcY] at h'
    exact h'
  have hfM : fuseC ∈ (Subgroup.centralizer {Om1.tc}).comap cp2_fst := by
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    have h' := congrArg cp2_fst fuseC_conj
    simp only [map_mul, map_inv, cp2_fst_tcY, cp2_fst_cK1, mul_one] at h'
    exact mul_inv_eq_iff_eq_mul.1 h'
  have hfC : fuseC ∉ Subgroup.centralizer {tcY} := by
    intro h
    have h1 : fuseC * tcY = tcY * fuseC := Subgroup.mem_centralizer_singleton_iff.1 h
    have h2 : fuseC * tcY * fuseC⁻¹ = tcY := by rw [h1, mul_inv_cancel_right]
    rw [fuseC_conj] at h2
    exact cK_ne_one (k := 1) (by norm_num) (mul_left_cancel (h2.trans (mul_one tcY).symm))
  have hdvd : Nat.card (Subgroup.centralizer {tcY}) ∣ 6144 :=
    hM ▸ Subgroup.card_dvd_of_le hCM
  have hne : Nat.card (Subgroup.centralizer {tcY}) ≠ 6144 := by
    intro h
    have heq := Subgroup.eq_of_le_of_card_ge hCM (by rw [hM, h])
    exact hfC (heq ▸ hfM)
  have hle : Nat.card (Subgroup.centralizer {tcY}) ≤ 6144 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card (Subgroup.centralizer {tcY}) := Nat.card_pos
  obtain ⟨a, ha⟩ := hlow
  have hcard : Nat.card (Subgroup.centralizer {tcY}) = 3072 := by omega
  refine ⟨by rw [hcard]; norm_num, by rw [cp2_card_Sc]; norm_num, hScCc.trans hCc, hCc⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2

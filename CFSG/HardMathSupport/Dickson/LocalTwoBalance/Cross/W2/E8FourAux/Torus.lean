module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Data
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.HardMathSupport.Lang.TwE6Step3.LangTorusMonomial
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyTorus
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyCover

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.LangTorus


namespace E8TorusAux

set_option linter.unusedSectionVars false

noncomputable def diagHom (L : Type) [Field L] : (Fin Tag.E8.rank → Lˣ) →* ModGL Tag.E8 L where
  toFun := rootDiagUnit Tag.E8
  map_one' := rootDiagUnit_one
  map_mul' a b := rootDiagUnit_mul a b

theorem dotE_neg (e v : Fin Tag.E8.rank → ℤ) : dotE e (-v) = - dotE e v := by
  simp [dotE, Finset.sum_neg_distrib]

theorem comm_Hel {L : Type} [Field L] [IsAlgClosed L] (D : StarData) {z : ModGL Tag.E8 L}
    (hcomm : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ → (5 : ℤ) ∣ dotE D.e γ →
      ∀ c : L, z * pinnedX Tag.E8 L γ c = pinnedX Tag.E8 L γ c * z)
    {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) (h5 : (5 : ℤ) ∣ dotE D.e γ) (t : Lˣ) :
    z * Hel γ t = Hel γ t * z := by
  have hle : rootSpan Tag.E8 L {γ, -γ} ≤ Subgroup.centralizer {z} := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rcases hα with rfl | hα
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ hγ h5 c).symm
    · rw [Set.mem_singleton_iff] at hα
      subst hα
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hcomm _ (IsRoot.neg hγ) (by rw [dotE_neg]; exact (dvd_neg).2 h5) c).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1
    (hle (Hel_root_mem_rootSpan (Or.inr (Or.inr (Or.inr rfl))) hγ t))).symm

theorem det_exps_ne_zero (D : StarData) (hD : D.Valid) :
    (Matrix.of fun (l j : Fin Tag.E8.rank) =>
      CFSG.LieType.Steinberg.Adjoint.iform (D.g j) (Pi.single l 1 : Fin Tag.E8.rank → ℤ)).det
        ≠ 0 := by
  classical
  have hB : Tag.E8.symmetrizedCartan.det ≠ 0 := by
    have h := (posDef_symmetrizedCartan Tag.E8).det_pos
    have e : ((Tag.E8.symmetrizedCartan.det : ℤ) : ℝ) =
        (Tag.E8.symmetrizedCartan.map (Int.cast : ℤ → ℝ)).det := Int.cast_det _
    intro h0
    rw [← e, h0] at h
    simp at h
  have hG : (Matrix.of D.g).det ≠ 0 := by
    have h : (Matrix.of D.m) * (Matrix.of D.g) =
        (5 : ℤ) • (1 : Matrix (Fin Tag.E8.rank) (Fin Tag.E8.rank) ℤ) := by
      ext i k
      rw [Matrix.mul_apply]
      simp only [Matrix.of_apply]
      rw [hD.mg i k]
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one] at h2
    intro h0
    rw [h0, mul_zero] at h2
    simp only [Fintype.card_fin, mul_one] at h2
    exact pow_ne_zero _ (by norm_num : (5 : ℤ) ≠ 0) h2.symm
  have hAeq : (Matrix.of fun (l j : Fin Tag.E8.rank) =>
      CFSG.LieType.Steinberg.Adjoint.iform (D.g j) (Pi.single l 1 : Fin Tag.E8.rank → ℤ)) =
        Tag.E8.symmetrizedCartan * (Matrix.of D.g).transpose := by
    ext l j
    rw [Matrix.mul_apply, Matrix.of_apply, CFSG.LieType.Steinberg.Adjoint.iform_comm]
    simp [CFSG.LieType.Steinberg.Adjoint.iform, Pi.single_apply]
  rw [hAeq, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero hB hG

theorem comm_rootDiagUnit {L : Type} [Field L] [IsAlgClosed L] (D : StarData) (hD : D.Valid)
    {z : ModGL Tag.E8 L}
    (hcomm : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ → (5 : ℤ) ∣ dotE D.e γ →
      ∀ c : L, z * pinnedX Tag.E8 L γ c = pinnedX Tag.E8 L γ c * z)
    (b : Fin Tag.E8.rank → Lˣ) : z * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * z := by
  classical
  let H : Subgroup (Fin Tag.E8.rank → Lˣ) := (Subgroup.centralizer {z}).comap (diagHom L)
  have hH : ∀ (j : Fin Tag.E8.rank) (t : Lˣ), Hchar (D.g j) t ∈ H := by
    intro j t
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    exact (comm_Hel D hcomm (mem_rootsV_iff.1 (hD.g_mem j).1) (hD.g_mem j).2 t).symm
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Lang.TwE6Step3.monoHom_surjective_of_det_ne_zero (L := L)
    _ (det_exps_ne_zero D hD) b
  have hb : b = ∏ j, Hchar (D.g j) (c j) := by
    funext l
    rw [Finset.prod_apply, ← congrFun hc l, CFSG.HardMathSupport.Lang.TwE6Step3.monoHom_apply]
    exact Finset.prod_congr rfl fun j _ => rfl
  have hbH : b ∈ H := by
    rw [hb]
    exact Subgroup.prod_mem H fun j _ => hH j (c j)
  exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hbH)).symm

theorem mem_torusGroup_of_comm_rootDiagUnit {L : Type} [Field L] (D : StarData) (hD : D.Valid)
    {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) {z : ModGL Tag.E8 L} (hz : z ∈ adjointGroup Tag.E8 L)
    (hc : ∀ b : Fin Tag.E8.rank → Lˣ, z * rootDiagUnit Tag.E8 b = rootDiagUnit Tag.E8 b * z) :
    z ∈ torusGroup Tag.E8 L := by
  classical
  set a : Fin 4 → (Fin Tag.E8.rank → Lˣ) := fun s => tupE ζ (D.b s) with ha
  have hzF : z ∈ familyCentralizer Tag.E8 L a := by
    rw [mem_familyCentralizer]
    refine ⟨hz, fun s => ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact (hc _).symm
  obtain ⟨w, hw, m, hm, hzm⟩ := familyCentralizer_le_mul Tag.E8 L a hzF
  have hker : familyKernel a = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun α hα => ?_
    obtain ⟨s, hs⟩ := hD.b_ne α (mem_rootsV_iff.2 hα.1)
    exact hs ((rootChar_tupE_eq_one_iff hζ (D.b s) α).1 (hα.2 s))
  have hmT : m ∈ torusGroup Tag.E8 L := by
    have : familyGroup (K := L) a = torusGroup Tag.E8 L := by
      rw [familyGroup, hker]
      simp [rootSpan]
    rwa [this] at hm
  have hw1 : w = 1 := by
    refine ext_single fun j => ?_
    rw [one_smul]
    have hv : IsRoot Tag.E8 (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := IsRoot.basis j
    have hwv : IsRoot Tag.E8 (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) := IsRoot.smul hv w
    refine hD.b_inj _ (mem_rootsV_iff.2 hwv) _ (mem_rootsV_iff.2 hv) fun s => ?_
    have h := hw s (Pi.single j 1)
    rw [rootChar_tupE, rootChar_tupE] at h
    have h1 : ζ ^ (dotE (D.b s) (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) -
        dotE (D.b s) (Pi.single j 1)) = 1 := by
      rw [zpow_sub, h, mul_inv_cancel]
    exact (hζ.zpow_eq_one_iff_dvd _).1 h1
  rw [hzm, hw1, canonicalRep_one, mul_one]
  exact hmT

theorem diagHom_pow {L : Type} [Field L] (c : Fin Tag.E8.rank → Lˣ) (n : ℕ) :
    (rootDiagUnit Tag.E8 c) ^ n = rootDiagUnit Tag.E8 (c ^ n) :=
  (map_pow (diagHom L) c n).symm

end E8TorusAux

theorem pow_five_eq_one_of_commute_kernel (D : StarData) (hD : D.Valid) {L : Type} [Field L]
    [IsAlgClosed L] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ 5) {z : ModGL Tag.E8 L}
    (hz : z ∈ adjointGroup Tag.E8 L)
    (hcomm : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ → (5 : ℤ) ∣ dotE D.e γ →
      ∀ c : L, z * pinnedX Tag.E8 L γ c = pinnedX Tag.E8 L γ c * z) : z ^ 5 = 1 := by
  have hT : z ∈ torusGroup Tag.E8 L :=
    E8TorusAux.mem_torusGroup_of_comm_rootDiagUnit D hD hζ hz
      (E8TorusAux.comm_rootDiagUnit D hD hcomm)
  obtain ⟨c, hcz⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hchar : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 γ → (5 : ℤ) ∣ dotE D.e γ →
      rootChar c γ = 1 := by
    intro γ hγ h5
    have h1 := rootDiagUnit_conj_pinnedX c hγ (1 : L)
    have h2 := hcomm γ hγ h5 1
    rw [hcz] at h2
    rw [h2, mul_inv_cancel_right] at h1
    have h3 := pinnedX_injective Tag.E8 L γ h1
    exact Units.ext (by simpa using h3.symm)
  have hci : ∀ i, c i ^ 5 = 1 := by
    intro i
    have e1 : (5 : ℕ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ) = ∑ j, D.m i j • D.g j := by
      funext k
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
      rw [hD.mg i k]
      by_cases h : i = k
      · subst h
        simp
      · simp [Pi.single_apply, h, Ne.symm h]
    calc c i ^ 5 = rootChar c ((5 : ℕ) • (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) :=
          (rootChar_nsmul_single c i 5).symm
      _ = rootChar c (∑ j, D.m i j • D.g j) := by rw [e1]
      _ = ∏ j, rootChar c (D.m i j • D.g j) := rootChar_sum _ _ _
      _ = 1 := Finset.prod_eq_one fun j _ => by
          rw [rootChar_zsmul, hchar _ (mem_rootsV_iff.1 (hD.g_mem j).1) (hD.g_mem j).2, one_zpow]
  have hc5 : c ^ 5 = 1 := funext fun i => by simpa using hci i
  rw [hcz, E8TorusAux.diagHom_pow, hc5, rootDiagUnit_one]

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

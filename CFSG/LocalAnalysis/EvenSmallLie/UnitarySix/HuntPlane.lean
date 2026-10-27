module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.MathieuExtPlane
public import CFSG.Fischer.Polar.Basic
public import Certificates.Certificate3004
import all CFSG.Fischer.F4
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open CFSG.Fischer CFSG.Monster.B.Classical.Plane CFSG.EvenSmallLie.UnitarySix.MathieuExt
  CFSG.Sporadic.Schreier CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native CFSG.Fischer.Native
open scoped MatrixGroups Matrix

@[expose] def lab (i : Fin 21) : Fin 42 := Fin.castLE (by norm_num) i

@[expose] def uβ (i : Fin 21) : Fin 693 := betaF (lab i)

theorem uβ_injective :
    Function.Injective uβ := fun _ _ h =>
  Fin.castLE_injective _ (betaF_injective h)

theorem tvP_uβ_injective :
    Function.Injective fun i => tvP
    (uβ i) := fun _ _ h =>
  uβ_injective (tvP_injective h)

theorem rho_val_lt (A : GL (Fin 3) CFSG.ComponentClassification.PSL3Four.F4) (i : Fin 21) :
    (CFSG.ComponentClassification.PSL3Four.rho A (lab i)).val < 21 := by
  rw [CFSG.ComponentClassification.PSL3Four.rho_apply]
  unfold CFSG.ComponentClassification.PSL3Four.rhoFun
  split_ifs with h
  · exact CFSG.ComponentClassification.PSL3Four.vIdx_lt _
  · exact absurd (by simp [lab]) h

theorem S_val_lt {σ : Equiv.Perm (Fin 42)} (hσ : σ ∈ CFSG.ComponentClassification.PSL3Four.S)
    (i : Fin 21) : (σ (lab i)).val < 21 := by
  have hle : CFSG.ComponentClassification.PSL3Four.S ≤
      (CFSG.ComponentClassification.PSL3Four.rho).range := by
    rw [CFSG.ComponentClassification.PSL3Four.S, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  obtain ⟨A, rfl⟩ := hle hσ
  exact rho_val_lt A i

@[expose] def restrFun (σ : CFSG.ComponentClassification.PSL3Four.S) (i : Fin 21) : Fin 21 :=
  ⟨((σ : Equiv.Perm (Fin 42)) (lab i)).val, S_val_lt σ.2 i⟩

theorem lab_restrFun (σ : CFSG.ComponentClassification.PSL3Four.S) (i : Fin 21) :
    lab (restrFun σ i) = (σ : Equiv.Perm (Fin 42)) (lab i) := Fin.ext rfl

@[expose] def restrS : CFSG.ComponentClassification.PSL3Four.S →* Equiv.Perm (Fin 21) where
  toFun σ :=
    { toFun := restrFun σ
      invFun := restrFun σ⁻¹
      left_inv := fun i => Fin.castLE_injective (by norm_num : 21 ≤ 42) (by
        change lab (restrFun σ⁻¹ (restrFun σ i)) = lab i
        rw [lab_restrFun, lab_restrFun, Subgroup.coe_inv]
        exact perm_inv_apply_self _ _)
      right_inv := fun i => Fin.castLE_injective (by norm_num : 21 ≤ 42) (by
        change lab (restrFun σ (restrFun σ⁻¹ i)) = lab i
        rw [lab_restrFun, lab_restrFun, Subgroup.coe_inv]
        exact perm_apply_inv_self _ _) }
  map_one' := Equiv.ext fun i => Fin.castLE_injective (by norm_num : 21 ≤ 42) (by
    change lab (restrFun 1 i) = lab i
    rw [lab_restrFun]
    rfl)
  map_mul' σ τ := Equiv.ext fun i => Fin.castLE_injective (by norm_num : 21 ≤ 42) (by
    change lab (restrFun (σ * τ) i) = lab (restrFun σ (restrFun τ i))
    rw [lab_restrFun, lab_restrFun, lab_restrFun]
    rfl)

theorem phi42_mem_S
    (k : uK) : phi42 k ∈ CFSG.ComponentClassification.PSL3Four.S :=
  range_phi42.1 ▸ ⟨k, rfl⟩

@[expose] noncomputable def phiS :
    uK →* CFSG.ComponentClassification.PSL3Four.S :=
  phi42.codRestrict _ phi42_mem_S

@[expose] noncomputable def kappa :
    uK →* Equiv.Perm (Fin 21) := restrS.comp phiS

theorem uβ_kappa
    (k : uK) (i : Fin 21) : uβ (kappa k i) =
    (k : Equiv.Perm (Fin 693)) (uβ i) := by
  change betaF (lab (restrFun (phiS k) i)) = _
  rw [lab_restrFun]
  exact betaF_phi42 k (lab i)

@[expose] def aM : Matrix (Fin 3) (Fin 3) F4 := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def bM : Matrix (Fin 3) (Fin 3) F4 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def cM : Matrix (Fin 3) (Fin 3) F4 := !![1, F4.ω, 0; 0, 1, 0; 0, 0, 1]

@[expose] def kM : Fin 3 → Matrix (Fin 3) (Fin 3) F4 := ![aM, bM, cM]

theorem kM_det (m : Fin 3) : (kM m).det = 1 := by
  rw [Matrix.det_fin_three]
  revert m
  decide +kernel

@[expose] def kSL (m : Fin 3) : Matrix.SpecialLinearGroup (Fin 3) F4 := ⟨kM m, kM_det m⟩

open CFSG.ComponentClassification.PSL3Four in
theorem kGen_check : ∀ m : Fin 3, ∀ i : Fin 21,
    (([g₁, g₂, g₃].getD m 1) (lab i)).val = (normIdx (kM m *ᵥ Ω i)).val := by
  decide +kernel

theorem kappa_kGen
    (m : Fin 3) :
    kappa ⟨kGens.getD m 1, kGens_getD_mem m.2⟩ = pslPerm (kSL m : PSL(3, F4)) := by
  ext i
  rw [pslPerm_mk_apply]
  change (restrFun (phiS _) i).val = _
  have h := congrArg Fin.val (lab_restrFun (phiS ⟨kGens.getD m 1, kGens_getD_mem m.2⟩) i)
  change (restrFun (phiS _) i).val = ((phi42 _) (lab i)).val at h
  rw [h, phi42_kGen m.2]
  exact kGen_check m i

theorem kappa_mem_range
    (k : uK) : kappa k ∈ pslPerm.range := by
  obtain ⟨k, hk⟩ := k
  have hk' := hk
  rw [uK_eq] at hk'
  induction hk' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hx
    have hm3 : m < 3 := by simpa [kGens, kWords] using hm
    have e : (⟨kGens[m], hk⟩ : uK) = ⟨kGens.getD m 1, kGens_getD_mem hm3⟩ :=
      Subtype.ext (List.getD_eq_getElem _ _ hm).symm
    have h1 : kappa ⟨kGens[m], hk⟩ = pslPerm (kSL ⟨m, hm3⟩ : PSL(3, F4)) :=
      (congrArg kappa e).trans (kappa_kGen ⟨m, hm3⟩)
    exact h1 ▸ ⟨_, rfl⟩
  | one => exact (map_one kappa).symm ▸ one_mem _
  | mul x y hx hy ihx ihy =>
    have e : (⟨x * y, hk⟩ : uK) = ⟨x, uK_eq ▸ hx⟩ * ⟨y, uK_eq ▸ hy⟩ := rfl
    rw [e, map_mul]
    exact mul_mem (ihx _) (ihy _)
  | inv x hx ihx =>
    have e : (⟨x⁻¹, hk⟩ : uK) = (⟨x, uK_eq ▸ hx⟩ : uK)⁻¹ := rfl
    rw [e, map_inv]
    exact inv_mem (ihx _)

theorem tvP_check :
    aGens.all (fun g => (List.range 21).any fun i =>
      tblEq 693 (toTable g) tvTabs[beta[i]!]!) = true ∧
    tblEq 693 (toTable j1) tvTabs[beta[5]!]! = true :=
  Certificates.certificate3004

theorem uβ_val (i : Fin 21) :
    (uβ i).val = beta[i.val]! := betaF_val (lab i)

theorem eq_tvP_of_tblEq
    {g : Equiv.Perm (Fin 693)} {i : Fin 21}
    (h : tblEq 693 (toTable g) tvTabs[beta[i.val]!]! = true) : g = tvP (uβ i) := by
  have hrep := rep_tvP (uβ i)
  rw [uβ_val] at hrep
  exact (tblEq_true_iff (rep_toTable hn693 g) hrep).1 h

theorem aGens_tvP :
    ∀ g ∈ aGens, ∃ i : Fin 21, g = tvP (uβ i) := by
  intro g hg
  obtain ⟨i, hi, h⟩ := List.any_eq_true.1 (List.all_eq_true.1 tvP_check.1 g hg)
  have hi21 : i < 21 := List.mem_range.1 hi
  exact ⟨⟨i, hi21⟩, eq_tvP_of_tblEq h⟩

theorem j1_eq_tvP :
    j1 = tvP (uβ 5) := eq_tvP_of_tblEq (i := 5) tvP_check.2

theorem conj_tvP
    {g : Equiv.Perm (Fin 693)}
    (hg : g ∈ T46) (q : Fin 693) :
    g * tvP q * g⁻¹ = tvP (g q) :=
  (isPolarAut_of_mem hg).mul_tvP_mul_inv q

theorem kappa_injective :
    Function.Injective kappa := by
  rw [injective_iff_map_eq_one]
  intro k hk
  have hfix : ∀ i, (k : Equiv.Perm (Fin 693)) (uβ i) = uβ i := fun i => by
    rw [← uβ_kappa, hk, Equiv.Perm.one_apply]
  refine Subtype.ext (eq_one_of_comm_aGens k.2 fun a ha => ?_)
  obtain ⟨i, rfl⟩ := aGens_tvP a ha
  have h := conj_tvP (uK_le_T46 k.2) (uβ i)
  rw [hfix] at h
  calc (k : Equiv.Perm (Fin 693)) * tvP (uβ i)
      = (k : Equiv.Perm (Fin 693)) * tvP (uβ i) * (k : Equiv.Perm (Fin 693))⁻¹ * k := by group
    _ = tvP (uβ i) * k := by rw [h]

theorem range_kappa :
    kappa.range = pslPerm.range := by
  refine Subgroup.eq_of_le_of_card_ge (fun _ ⟨k, hk⟩ => hk ▸ kappa_mem_range k) ?_
  rw [card_range_pslPerm, ← card_uK]
  exact (Nat.card_congr (MonoidHom.ofInjective kappa_injective).toEquiv).le

theorem conj_j1
    (k : uK) :
    (k : Equiv.Perm (Fin 693)) * j1 * (k : Equiv.Perm (Fin 693))⁻¹ = tvP (uβ (kappa k 5)) := by
  rw [j1_eq_tvP, conj_tvP (uK_le_T46 k.2), uβ_kappa]

theorem mem_conjClass_j1_iff
    {x : Equiv.Perm (Fin 693)} :
    x ∈ conjClass uK j1 ↔ ∃ i, tvP (uβ i) = x := by
  have hsub : conjClass uK j1 ⊆ Set.range fun i => tvP (uβ i) := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, (conj_j1 ⟨c, hc⟩).symm⟩
  have hcard : (Set.range fun i => tvP (uβ i)).ncard ≤ (conjClass uK j1).ncard := by
    rw [Set.ncard_range_of_injective tvP_uβ_injective, Nat.card_fin]
    have h := ToddOrbit.card_cls.1
    rw [ToddOrbit.cls, ← Set.ncard_eq_toFinset_card] at h
    rw [h]
  rw [Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)]
  rfl

end CFSG.EvenSmallLie.UnitarySix.Hunt

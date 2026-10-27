module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshBaseData
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshSwap

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp

@[expose] noncomputable def kapM : Multiplicative (ZMod 2) × G12 →* Equiv.Perm (Fin 14) :=
  kapP.comp ((MonoidHom.id (Multiplicative (ZMod 2))).prodMap (NativeSporadic.M12).subtype)

theorem kapM_apply (a : Multiplicative (ZMod 2)) (σ : G12) :
    kapM (a, σ) = kapP (a, (σ : Equiv.Perm (Fin 12))) := rfl

theorem kapM_injective : Function.Injective kapM := by
  intro p q h
  have h1 := kapP_injective h
  have hf := congrArg (fun z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 12) => z.1) h1
  have hs := congrArg (fun z : Multiplicative (ZMod 2) × Equiv.Perm (Fin 12) => z.2) h1
  exact Prod.ext hf (Subtype.ext hs)

theorem ap_of_rep {T : Table} {z : Equiv.Perm (Fin 14)} (h : Rep 14 T z) {i : ℕ} (hi : i < 14) :
    (T[i]!).toNat = ((z ⟨i, hi⟩ : Fin 14) : ℕ) := by
  have h1 := h i hi
  rw [idx_of_lt _ hi] at h1
  exact h1

theorem tbl_apply_of_rep {T : Table} {a : Multiplicative (ZMod 2)} {σ : Equiv.Perm (Fin 12)}
    (h : Rep 14 T (kapP (a, σ))) {i : ℕ} (hi : i < 12) : (T[i]!).toNat = pv σ i := by
  rw [ap_of_rep h (by omega), kapP_apply, Equiv.Perm.coe_mul, Function.comp_apply]
  have h1 : (extHom σ ⟨i, by omega⟩).val = (σ ⟨i, hi⟩).val :=
    extHom_apply_lt σ ⟨i, by omega⟩ hi
  have h2 : (extHom σ ⟨i, by omega⟩ : Fin 14).val < 12 := by rw [h1]; exact (σ _).2
  rw [tauPow_apply_lt a _ h2, h1]
  simp [pv, hi]

theorem epsT_eq {T : Table} {a : Multiplicative (ZMod 2)} {σ : Equiv.Perm (Fin 12)}
    (h : Rep 14 T (kapP (a, σ))) : epsT T = (Multiplicative.toAdd a).val := by
  have h1 := ap_of_rep h (i := 12) (by norm_num)
  rw [kapP_apply, Equiv.Perm.coe_mul, Function.comp_apply,
    extHom_apply_ge σ ⟨12, by omega⟩ (by simp), tauPow_apply_twelve] at h1
  have hv : (Multiplicative.toAdd a).val = 0 ∨ (Multiplicative.toAdd a).val = 1 := by
    rcases zmod_two_cases (Multiplicative.toAdd a) with h | h
    · left; rw [h]; rfl
    · right; rw [h]; rfl
  unfold epsT
  have h2 : (T[12]!).toNat = 12 + (Multiplicative.toAdd a).val := h1
  rw [h2]
  rcases hv with hv | hv <;> simp [hv]

theorem lamT_eq {T : Table} {a : Multiplicative (ZMod 2)} {σ : Equiv.Perm (Fin 12)}
    (h : Rep 14 T (kapP (a, σ))) : lamT T = lamP σ := by
  unfold lamT lamP
  have hp : ∀ j, j < 4 → (T[j]!).toNat = pv σ j := fun j hj => tbl_apply_of_rep h (by omega)
  refine congrArg (fun l : List ℕ => l.length % 2) ?_
  apply List.flatMap_congr
  intro i hi
  apply List.filter_congr
  intro j hj
  have hi' := List.mem_range.1 hi
  have hj' := List.mem_range.1 hj
  simp only [hp i hi', hp j hj']

section Tables

set_option linter.unusedSectionVars false

@[expose] def baseM : Fin 5 → Multiplicative (ZMod 2) × G12
  | 0 => (Multiplicative.ofAdd 1, 1)
  | 1 => (1, ⟨bfE, bfE_mem_M12⟩)
  | 2 => (1, ⟨bfN, bfN_mem_M12⟩)
  | 3 => (1, ⟨bfF, bfF_mem_M12⟩)
  | 4 => (1, ⟨pB, pB_mem⟩)

theorem rep_baseM (i : Fin 5) : Rep 14 (baseT i) (kapM (baseM i)) := by
  fin_cases i
  · have h : kapM (baseM 0) = tauP := by
      show kapP (Multiplicative.ofAdd 1, (1 : Equiv.Perm (Fin 12))) = tauP
      rw [kapP_apply, tauPow_ofAdd_one, map_one, mul_one]
    show Rep 14 tauT (kapM (baseM 0))
    rw [h]
    exact rep_tauT
  · have h : kapM (baseM 1) = extHom bfE := by
      show kapP (1, bfE) = extHom bfE
      rw [kapP_apply, tauPow_one, one_mul]
    show Rep 14 (tbl14 bfE) (kapM (baseM 1))
    rw [h]
    exact rep_tbl14 bfE
  · have h : kapM (baseM 2) = extHom bfN := by
      show kapP (1, bfN) = extHom bfN
      rw [kapP_apply, tauPow_one, one_mul]
    show Rep 14 (tbl14 bfN) (kapM (baseM 2))
    rw [h]
    exact rep_tbl14 bfN
  · have h : kapM (baseM 3) = extHom bfF := by
      show kapP (1, bfF) = extHom bfF
      rw [kapP_apply, tauPow_one, one_mul]
    show Rep 14 (tbl14 bfF) (kapM (baseM 3))
    rw [h]
    exact rep_tbl14 bfF
  · have h : kapM (baseM 4) = extHom pB := by
      show kapP (1, pB) = extHom pB
      rw [kapP_apply, tauPow_one, one_mul]
    show Rep 14 (tbl14 pB) (kapM (baseM 4))
    rw [h]
    exact rep_tbl14 pB

theorem rep_baseMi (i : Fin 5) : Rep 14 (baseTi i) (kapM (baseM i))⁻¹ := by
  fin_cases i
  · have h : (kapM (baseM 0))⁻¹ = tauP := by
      have h0 : kapM (baseM 0) = tauP := by
        show kapP (Multiplicative.ofAdd 1, (1 : Equiv.Perm (Fin 12))) = tauP
        rw [kapP_apply, tauPow_ofAdd_one, map_one, mul_one]
      rw [h0]
      exact inv_eq_of_mul_eq_one_right tauP_sq
    show Rep 14 tauT (kapM (baseM 0))⁻¹
    rw [h]
    exact rep_tauT
  · have h : (kapM (baseM 1))⁻¹ = extHom bfE⁻¹ := by
      have h0 : kapM (baseM 1) = extHom bfE := by
        show kapP (1, bfE) = extHom bfE
        rw [kapP_apply, tauPow_one, one_mul]
      rw [h0, map_inv]
    show Rep 14 (tbl14 bfE⁻¹) (kapM (baseM 1))⁻¹
    rw [h]
    exact rep_tbl14 bfE⁻¹
  · have h : (kapM (baseM 2))⁻¹ = extHom bfN⁻¹ := by
      have h0 : kapM (baseM 2) = extHom bfN := by
        show kapP (1, bfN) = extHom bfN
        rw [kapP_apply, tauPow_one, one_mul]
      rw [h0, map_inv]
    show Rep 14 (tbl14 bfN⁻¹) (kapM (baseM 2))⁻¹
    rw [h]
    exact rep_tbl14 bfN⁻¹
  · have h : (kapM (baseM 3))⁻¹ = extHom bfF⁻¹ := by
      have h0 : kapM (baseM 3) = extHom bfF := by
        show kapP (1, bfF) = extHom bfF
        rw [kapP_apply, tauPow_one, one_mul]
      rw [h0, map_inv]
    show Rep 14 (tbl14 bfF⁻¹) (kapM (baseM 3))⁻¹
    rw [h]
    exact rep_tbl14 bfF⁻¹
  · have h : (kapM (baseM 4))⁻¹ = extHom pB⁻¹ := by
      have h0 : kapM (baseM 4) = extHom pB := by
        show kapP (1, pB) = extHom pB
        rw [kapP_apply, tauPow_one, one_mul]
      rw [h0, map_inv]
    show Rep 14 (tbl14 pB⁻¹) (kapM (baseM 4))⁻¹
    rw [h]
    exact rep_tbl14 pB⁻¹

@[expose, irreducible] noncomputable def wordVal (w : List (Fin 5 × Bool)) :
    Multiplicative (ZMod 2) × G12 :=
  FreeGroup.lift baseM (FreeGroup.mk w)

theorem wordVal_def (w : List (Fin 5 × Bool)) :
    wordVal w = FreeGroup.lift baseM (FreeGroup.mk w) := by
  unfold wordVal
  rfl

theorem kapM_wordVal (w : List (Fin 5 × Bool)) :
    kapM (wordVal w) = FreeGroup.lift (fun i => kapM (baseM i)) (FreeGroup.mk w) := by
  have : (kapM.comp (FreeGroup.lift baseM)) = FreeGroup.lift (fun i => kapM (baseM i)) := by
    apply FreeGroup.ext_hom
    intro i
    simp
  unfold wordVal
  exact congrArg (fun f => f (FreeGroup.mk w)) this

theorem rep_tblW (w : List (Fin 5 × Bool)) : Rep 14 (tblW w) (kapM (wordVal w)) := by
  rw [kapM_wordVal]
  exact rep_evalT (by norm_num) (fun i => kapM (baseM i)) rep_baseM rep_baseMi w

theorem wordVal_eq_of_tblEq {w w' : List (Fin 5 × Bool)}
    (h : tblEq 14 (tblW w) (tblW w') = true) : wordVal w = wordVal w' :=
  kapM_injective ((tblEq_iff_eq (rep_tblW w) (rep_tblW w')).1 h)

theorem wordVal_eq_one_of_tblEq {w : List (Fin 5 × Bool)}
    (h : tblEq 14 (tblW w) (idT 14) = true) : wordVal w = 1 := by
  have h1 := (tblEq_iff_eq (rep_tblW w) (Rep.idT (G := Equiv.Perm (Fin 14)) (by norm_num))).1 h
  exact kapM_injective (by rw [h1, map_one])

theorem wordVal_append (w₁ w₂ : List (Fin 5 × Bool)) :
    wordVal (w₁ ++ w₂) = wordVal w₁ * wordVal w₂ := by
  unfold wordVal
  rw [show FreeGroup.mk (w₁ ++ w₂) = FreeGroup.mk w₁ * FreeGroup.mk w₂ from rfl, map_mul]

theorem wordVal_invW (w : List (Fin 5 × Bool)) : wordVal (invW w) = (wordVal w)⁻¹ := by
  unfold wordVal
  exact lift_mk_invW baseM w

theorem wordVal_powW (w : List (Fin 5 × Bool)) (k : ℕ) :
    wordVal (powW w k) = (wordVal w) ^ k := by
  unfold wordVal
  exact lift_mk_powW baseM w k

theorem wordVal_nil : wordVal [] = 1 := by simp [wordVal]

theorem wordVal_letter (i : Fin 5) : wordVal [(i, true)] = baseM i := by
  simp [wordVal]

theorem wordVal_wJ : wordVal wJ = (1, Jelt) := by
  have h : wJ = powW [((3 : Fin 5), true)] 4 := rfl
  rw [h, wordVal_powW, wordVal_letter]
  refine Prod.ext (by simp [baseM]) (Subtype.ext ?_)
  show ((⟨bfF, bfF_mem_M12⟩ : G12) ^ 4 : G12).1 = bfJ
  simp [bfJ]

theorem commJ_of_commT {T : Table} {a : Multiplicative (ZMod 2)} {τ : G12}
    (hrep : Rep 14 T (kapP (a, (τ : Equiv.Perm (Fin 12)))))
    (hc : commT T (tblW wJ) = true) : τ * Jelt = Jelt * τ := by
  unfold commT at hc
  have h1 := Rep.compT hrep (rep_tblW wJ)
  have h2 := Rep.compT (rep_tblW wJ) hrep
  have h3 := (tblEq_iff_eq h1 h2).1 hc
  rw [wordVal_wJ] at h3
  have h4 : kapM ((a, τ) * (1, Jelt)) = kapM ((1, Jelt) * (a, τ)) := by
    rw [map_mul, map_mul]
    exact h3
  have h5 := congrArg Prod.snd (kapM_injective h4)
  simpa using h5

theorem epsT_tblW (w : List (Fin 5 × Bool)) :
    epsT (tblW w) = (Multiplicative.toAdd (wordVal w).1).val :=
  epsT_eq (a := (wordVal w).1) (σ := ((wordVal w).2 : Equiv.Perm (Fin 12))) (rep_tblW w)

theorem fst_eq_one_of_epsT {w : List (Fin 5 × Bool)} (h : epsT (tblW w) = 0) :
    (wordVal w).1 = 1 := by
  rw [epsT_tblW] at h
  have h1 : Multiplicative.toAdd (wordVal w).1 = 0 := (ZMod.val_eq_zero _).1 h
  exact Multiplicative.toAdd.injective (by simpa using h1)

section Words

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)

@[expose] noncomputable def valG (w : List (Fin 5 × Bool)) : G := jH e₀ (wordVal w)

theorem valG_append (w₁ w₂ : List (Fin 5 × Bool)) :
    valG e₀ (w₁ ++ w₂) = valG e₀ w₁ * valG e₀ w₂ := by
  unfold valG
  rw [wordVal_append, map_mul]

theorem valG_invW (w : List (Fin 5 × Bool)) : valG e₀ (invW w) = (valG e₀ w)⁻¹ := by
  unfold valG
  rw [wordVal_invW]
  exact map_inv (jH e₀) (wordVal w)

theorem valG_powW (w : List (Fin 5 × Bool)) (k : ℕ) : valG e₀ (powW w k) = valG e₀ w ^ k := by
  unfold valG
  rw [wordVal_powW, map_pow]

theorem valG_eq_of_tblEq {w w' : List (Fin 5 × Bool)}
    (h : tblEq 14 (tblW w) (tblW w') = true) : valG e₀ w = valG e₀ w' := by
  unfold valG
  rw [wordVal_eq_of_tblEq h]

theorem valG_wJ : valG e₀ wJ = cG e₀ := by
  unfold valG
  rw [wordVal_wJ, cG_def]
  rfl

theorem valG_tau (he2 : orderOf e = 2) : valG e₀ [((0 : Fin 5), true)] = e := by
  unfold valG
  rw [wordVal_letter]
  exact (e_eq_jH e₀ he2).symm

end Words

end Tables

end CFSG.EvenSporadicStandard.M12Std.Yosh

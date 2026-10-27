module

public import CFSG.Fischer.Classification.PartIII.Beta.Points
public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.Fischer.Classification.Uniqueness.Abstract

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace Beta

open CFSG.Fischer CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary F3
open CFSG.Blueprint.Fischer (K)

@[expose] noncomputable def vecK (x : Fin 4 → F4) : Fin 4 → K := fun i => eF4 (x i)

theorem vecK_apply (x : Fin 4 → F4) (i : Fin 4) : vecK x i = eF4 (x i) :=
  rfl

theorem vecK_injective : Function.Injective vecK := fun _ _ h =>
  funext fun i => eF4.injective (congrFun h i)

theorem vecK_surjective : Function.Surjective vecK := fun v =>
  ⟨fun i => eF4.symm (v i), funext fun _ => eF4.apply_symm_apply _⟩

theorem vecK_zero : vecK 0 = 0 :=
  funext fun _ => map_zero eF4

theorem vecK_add (x y : Fin 4 → F4) : vecK (x + y) = vecK x + vecK y :=
  funext fun _ => map_add eF4 _ _

theorem vecK_smul (t : F4) (x : Fin 4 → F4) : vecK (t • x) = eF4 t • vecK x :=
  funext fun _ => map_mul eF4 _ _

theorem vecK_ne_zero {x : Fin 4 → F4} (hx : x ≠ 0) : vecK x ≠ 0 := fun h =>
  hx (vecK_injective (h.trans vecK_zero.symm))

theorem herm_vecK (x y : Fin 4 → F4) : herm frob (vecK x) (vecK y) = eF4 (hU x y) := by
  rw [herm_def, Fin.sum_univ_four, hU]
  simp only [vecK_apply, frob_eF4, map_add, map_mul, sq]

theorem tvU_smul_vecK {a : Fin 4 → F4} (ha : hU a a = 0) (b : Fin 4 → F4) :
    tvU (vecK a) • vecK b = vecK (tU a b) := by
  rw [tvU_smul (by rw [herm_vecK, ha, map_zero]), herm_vecK, tU, vecK_add, vecK_smul]

theorem vec4_eq (x : Fin 4 → F4) : x = ![x 0, x 1, x 2, x 3] := by
  ext i
  fin_cases i <;> rfl

theorem exists_eq_smul_uPt_uIdx {x : Fin 4 → F4} (hx0 : x ≠ 0) (hx : hU x x = 0) :
    ∃ t : F4, x = t • uPt (uIdx x) := by
  rw [vec4_eq x] at hx0 hx ⊢
  exact exists_eq_smul_uPt _ _ _ _ hx0 hx

theorem uIdx_uPt (i : Fin 45) : uIdx (uPt i) = i := by
  simpa using uIdx_smul_uPt i 1 one_ne_zero

theorem herm_vecK_uPt (i : Fin 45) : herm frob (vecK (uPt i)) (vecK (uPt i)) = 0 := by
  rw [herm_vecK, (uPt_spec i).2, map_zero]

@[expose] noncomputable def uElt (i : Fin 45) : DU 4 :=
  ⟨tqU (vecK (uPt i)), tqU_mem_DU (vecK_ne_zero (uPt_spec i).1) (herm_vecK_uPt i)⟩

theorem coe_uElt (i : Fin 45) : (uElt i : U2 4) = tqU (vecK (uPt i)) :=
  rfl

theorem tqU_vecK_eq {x : Fin 4 → F4} (hx0 : x ≠ 0) (hx : hU x x = 0) :
    tqU (vecK x) = tqU (vecK (uPt (uIdx x))) := by
  obtain ⟨t, ht⟩ := exists_eq_smul_uPt_uIdx hx0 hx
  refine ((tqU_eq_tqU_iff (by norm_num) (vecK_ne_zero (uPt_spec _).1) (herm_vecK_uPt _)
    (vecK_ne_zero hx0) (by rw [herm_vecK, hx, map_zero])).2 ⟨eF4 t, ?_⟩).symm
  rw [← vecK_smul, ← ht]

theorem uElt_bijective : Function.Bijective uElt := by
  refine ⟨fun i j hij => ?_, fun q => ?_⟩
  · obtain ⟨c, hc⟩ := (tqU_eq_tqU_iff (by norm_num) (vecK_ne_zero (uPt_spec i).1)
      (herm_vecK_uPt i) (vecK_ne_zero (uPt_spec j).1) (herm_vecK_uPt j)).1
      (congrArg Subtype.val hij)
    obtain ⟨t, rfl⟩ := eF4.surjective c
    rw [← vecK_smul] at hc
    have hji := vecK_injective hc
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hji
      exact (uPt_spec j).1 hji
    rw [← uIdx_uPt j, hji, uIdx_smul_uPt i t ht]
  · obtain ⟨v, hv0, hv, hq⟩ := mem_DU_iff.1 q.2
    obtain ⟨x, rfl⟩ := vecK_surjective v
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hv0 vecK_zero
    have hx : hU x x = 0 := eF4.injective (by rw [← herm_vecK, hv, map_zero])
    exact ⟨uIdx x, Subtype.ext (by rw [coe_uElt, ← tqU_vecK_eq hx0 hx, hq])⟩

theorem uElt_tau (i j : Fin 45) :
    tauE (pair_DU le_rfl) (uElt i) (uElt j) = uElt (uIdx (tU (uPt i) (uPt j))) := by
  apply Subtype.ext
  have hx : vecK (tU (uPt i) (uPt j)) = tvU (vecK (uPt i)) • vecK (uPt j) :=
    (tvU_smul_vecK (uPt_spec i).2 _).symm
  have hx0 : tU (uPt i) (uPt j) ≠ 0 := fun h => by
    rw [h, vecK_zero] at hx
    exact vecK_ne_zero (uPt_spec j).1 ((smul_eq_zero_iff_eq _).1 hx.symm)
  have hxx : hU (tU (uPt i) (uPt j)) (tU (uPt i) (uPt j)) = 0 :=
    eF4.injective (by rw [← herm_vecK, hx, herm_smul_smul, herm_vecK_uPt, map_zero])
  show tqU (vecK (uPt i)) * tqU (vecK (uPt j)) * tqU (vecK (uPt i)) = _
  rw [tqU_mul_tqU_mul_tqU (herm_vecK_uPt i) (herm_vecK_uPt j), ← hx, tqU_vecK_eq hx0 hxx,
    coe_uElt]

theorem oIdx_neg_oPt (i : Fin 45) : oIdx (-oPt i) = i :=
  (oIdx_oPt i).2

theorem oElt_tau (i j : Fin 45) :
    tauE (pair_R3 isF3Form_I5Form (by norm_num)) (oElt i) (oElt j) =
      oElt (uIdx (tU (uPt i) (uPt j))) := by
  apply Subtype.ext
  show reflBar I5Form (oPt i) * reflBar I5Form (oPt j) * reflBar I5Form (oPt i) = _
  rw [reflBar_conj isF3Form_I5Form, act_refl_I5Form (by rw [I5Form_eq_dot5]; exact dot5_oPt i),
    coe_oElt]
  rcases oPt_uIdx_tU i j with h | h <;> rw [h]
  exact (reflBar_neg _).symm

@[expose] noncomputable def betaEquiv : DU 4 ≃ D3 I5Form :=
  (Equiv.ofBijective uElt uElt_bijective).symm.trans (Equiv.ofBijective oElt oElt_bijective)

theorem betaEquiv_uElt (i : Fin 45) : betaEquiv (uElt i) = oElt i := by
  rw [betaEquiv, Equiv.trans_apply, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]

theorem betaEquiv_tau (e f : DU 4) :
    betaEquiv (tauE (pair_DU le_rfl) e f) =
      tauE (pair_R3 isF3Form_I5Form (by norm_num)) (betaEquiv e) (betaEquiv f) := by
  obtain ⟨i, rfl⟩ := uElt_bijective.2 e
  obtain ⟨j, rfl⟩ := uElt_bijective.2 f
  rw [uElt_tau, betaEquiv_uElt, betaEquiv_uElt, betaEquiv_uElt, oElt_tau]

end Beta

open Beta

theorem exists_mulEquiv_U2_four_R3_I5_eq :
    ∃ ψ : Unitary.U2 4 ≃* R3 I5Form, ∀ e : Unitary.DU 4, ψ e = betaEquiv e :=
  exists_mulEquiv_of_tau_eq (pair_DU le_rfl) (pair_R3 isF3Form_I5Form (by norm_num))
    (center_U2 le_rfl) (center_R3_eq_bot isF3Form_I5Form (by norm_num)) betaEquiv betaEquiv_tau

theorem exists_mulEquiv_U2_four_R3_I5 :
    ∃ ψ : Unitary.U2 4 ≃* R3 I5Form, ψ '' Unitary.DU 4 = D3 I5Form := by
  obtain ⟨ψ, hψ⟩ := exists_mulEquiv_U2_four_R3_I5_eq
  exact ⟨ψ, image_eq_of_forall_eq betaEquiv hψ⟩

theorem exists_mulEquiv_U2_four_of_ncard
    {f : LinearMap.BilinForm (ZMod 3) (Fin 5 → ZMod 3)} (hf : IsF3Form f)
    (h45 : (D3 f).ncard = 45) : ∃ ψ : R3 f ≃* Unitary.U2 4, ψ '' D3 f = Unitary.DU 4 := by
  rcases R3_five_cases hf with ⟨-, ψ, hψ⟩ | ⟨h36, -⟩
  · obtain ⟨β, hβ⟩ := exists_mulEquiv_U2_four_R3_I5
    refine ⟨ψ.trans β.symm, ?_⟩
    rw [MulEquiv.coe_trans, Set.image_comp, hψ, ← hβ]
    exact image_symm_image β _
  · omega

end CFSG.Fischer.Classification

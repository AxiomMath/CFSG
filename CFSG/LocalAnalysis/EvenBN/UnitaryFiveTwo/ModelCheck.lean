module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelGlobalRank
public import Certificates.Certificate27030
public import Certificates.Certificate27031
public import Certificates.Certificate27032
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Matrix Subgroup CFSG.Fischer Certificates.U52Yamada
open scoped commutatorElement

theorem one_omega_rel : (1 : F4) * bar 1 = F4.ω + bar F4.ω := by
  rw [bar_apply, bar_apply]
  decide

@[expose] def genSU : Fin 10 → SU52 :=
  ![uSU, vSU, e₁SU, e₂SU, x₂SU 1, x₂SU F4.ω, x₁SU 0 1 zero_one_rel, x₁SU 1 F4.ω one_omega_rel,
    x₃SU 1, x₄SU 1 F4.ω one_omega_rel]

theorem mat_genSU (i : Fin 10) : mat (genSU i) = genMat i := by
  fin_cases i <;> rfl

@[expose] def wordSU (w : List (Fin 10)) : SU52 := (w.map genSU).prod

theorem mat_wordSU (w : List (Fin 10)) : mat (wordSU w) = wordMat w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change mat (((i :: w).map genSU).prod) = ((i :: w).map genMat).prod
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mat_mul, mat_genSU]
    exact congrArg _ ih

theorem mat_inv_eq_invMat (g : SU52) : mat g⁻¹ = invMat (mat g) := mat_inv g

theorem mem_Fsub_of_isFShape {g : SU52} (h : IsFShape (mat g)) : g ∈ Fsub := by
  obtain ⟨hrow, hdiag, h21, h10, h20⟩ := h
  exact mem_Fsub.2 ⟨mem_Ssub.2 ⟨fun i j hij => hrow i j hij, hdiag⟩, h21, h10, h20⟩

@[expose] def nfSU (a₁ b₁ a₂ a₃ a₄ b₄ : F4) (h₁ : ValidPair a₁ b₁) (h₄ : ValidPair a₄ b₄) :
    SU52 :=
  x₁SU a₁ b₁ h₁ * x₂SU a₂ * x₃SU a₃ * x₄SU a₄ b₄ h₄

theorem mat_nfSU (a₁ b₁ a₂ a₃ a₄ b₄ : F4) (h₁ : ValidPair a₁ b₁) (h₄ : ValidPair a₄ b₄) :
    mat (nfSU a₁ b₁ a₂ a₃ a₄ b₄ h₁ h₄) = nfMat a₁ b₁ a₂ a₃ a₄ b₄ :=
  rfl

theorem nfSU_mem (a₁ b₁ a₂ a₃ a₄ b₄ : F4) (h₁ : ValidPair a₁ b₁) (h₄ : ValidPair a₄ b₄) :
    nfSU a₁ b₁ a₂ a₃ a₄ b₄ h₁ h₄ ∈ Ssub :=
  mul_mem (mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_sup_left (x₁SU_mem _ _ _))))
    (mem_sup_left (mem_sup_left (mem_sup_right (x₂SU_mem _)))))
    (mem_sup_left (mem_sup_right (x₃SU_mem _)))) (mem_sup_right (x₄SU_mem _ _ _))

theorem exists_nfMat {s : SU52} (hs : s ∈ Ssub) :
    ∃ a₁ b₁ a₂ a₃ a₄ b₄ : F4, ValidPair a₁ b₁ ∧ ValidPair a₄ b₄ ∧
      mat s = nfMat a₁ b₁ a₂ a₃ a₄ b₄ := by
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, -, -, -, -⟩ :=
    exists_eq_nf_coord hs
  exact ⟨a₁, b₁, a₂, a₃, a₄, b₄, x₁_coord_rel e₁, x₄_coord_rel e₄,
    by rw [mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄]; rfl⟩

theorem check3101_eq_true : check3101 () = true :=
  Certificates.certificate27030

theorem check39_eq_true : check39 () = true :=
  Certificates.certificate27031

theorem checkIdent_eq_true : checkIdent () = true :=
  Certificates.certificate27032

theorem exists_mul_eq_fld {s : SU52} (hs : s ∈ Ssub)
    (h : s * fld s = 1) : ∃ m ∈ Ssub, m * s = fld m := by
  have hc : Check3101 := of_check3101 check3101_eq_true
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, h₁, h₄, hm⟩ := exists_nfMat hs
  have h1 : nfMat a₁ b₁ a₂ a₃ a₄ b₄ * (nfMat a₁ b₁ a₂ a₃ a₄ b₄).map bar = 1 := by
    rw [← hm, ← mat_fld, ← mat_mul, h, mat_one]
  obtain ⟨c₁, d₁, c₂, c₃, c₄, d₄, k₁, k₄, hk⟩ := hc a₁ b₁ a₂ a₃ a₄ b₄ h₁ h₄ h1
  refine ⟨nfSU c₁ d₁ c₂ c₃ c₄ d₄ k₁ k₄, nfSU_mem _ _ _ _ _ _ _ _, ext_mat ?_⟩
  rw [mat_mul, mat_nfSU, hm, hk, mat_fld, mat_nfSU]

theorem exists_conj_mem_Fsub_of_mem_Ssub {s : SU52}
    (hs : s ∈ Ssub) (h : s * s = 1) : ∃ g : SU52, g * s * g⁻¹ ∈ Fsub := by
  have hc : Check39 := of_check39 check39_eq_true
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, h₁, h₄, hm⟩ := exists_nfMat hs
  have h1 : nfMat a₁ b₁ a₂ a₃ a₄ b₄ * nfMat a₁ b₁ a₂ a₃ a₄ b₄ = 1 := by
    rw [← hm, ← mat_mul, h, mat_one]
  rcases hc a₁ b₁ a₂ a₃ a₄ b₄ h₁ h₄ h1 with hF | ⟨k, hk⟩
  · refine ⟨1, ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact mem_Fsub_of_isFShape (hm ▸ hF)
  · refine ⟨wordSU (conjWord k), mem_Fsub_of_isFShape ?_⟩
    rw [mat_mul, mat_mul, mat_inv_eq_invMat, mat_wordSU, hm]
    exact hk

theorem exists_conj_mem_Fsub {x : SU52} (hx : x * x = 1) :
    ∃ g : SU52, g * x * g⁻¹ ∈ Fsub := by
  have hz : IsPGroup 2 (zpowers x) := isPGroup_two_of_sq fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, zpow_two, hx, _root_.one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_le_Ssub hz
  have hxS : g * x * g⁻¹ ∈ Ssub := hg ⟨x, mem_zpowers x, rfl⟩
  obtain ⟨g', hg'⟩ := exists_conj_mem_Fsub_of_mem_Ssub hxS (by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx, mul_one, mul_inv_cancel])
  exact ⟨g' * g, by simpa [mul_assoc] using hg'⟩

@[expose] def genFSU : Fin 4 → SU52 :=
  ![x₁SU 0 1 zero_one_rel, x₃SU 1, x₃SU F4.ω, x₄SU 0 1 zero_one_rel]

theorem mat_genFSU (j : Fin 4) : mat (genFSU j) = genF j := by
  fin_cases j <;> rfl

theorem genFSU_mem (j : Fin 4) : genFSU j ∈ Fsub := by
  fin_cases j
  · exact mem_sup_left (mem_sup_left ⟨0, 1, rfl, rfl⟩)
  · exact x₃SU_mem_Fsub 1
  · exact x₃SU_mem_Fsub F4.ω
  · exact x₄SU_zero_one_mem_Fsub zero_one_rel

theorem eq_zero_or_one_of_valid : ∀ b : F4, ValidPair 0 b → b = 0 ∨ b = 1 := by
  unfold ValidPair
  simp only [bar_apply]
  decide

theorem F4_cases : ∀ a : F4, a = 0 ∨ a = 1 ∨ a = F4.ω ∨ a = F4.ω + 1 := by decide

theorem closure_genFSU : closure (Set.range genFSU) = Fsub := by
  refine le_antisymm ((closure_le _).2 (by rintro _ ⟨j, rfl⟩; exact genFSU_mem j)) ?_
  have hmem : ∀ j, genFSU j ∈ closure (Set.range genFSU) := fun j => subset_closure ⟨j, rfl⟩
  refine sup_le (sup_le ?_ ?_) ?_ <;> intro g hg
  · obtain ⟨a, b, ha, hg⟩ := mem_x₁Sub.1 hg
    subst ha
    rcases eq_zero_or_one_of_valid b (x₁_coord_rel hg) with rfl | rfl
    · rw [eq_one_of_x₁ hg]
      exact one_mem _
    · rw [show g = genFSU 0 from ext_mat hg]
      exact hmem 0
  · obtain ⟨a, hg⟩ := mem_X₃sub.1 hg
    rcases F4_cases a with rfl | rfl | rfl | rfl
    · rw [show g = 1 from ext_mat (by rw [hg, x₃Mat_zero, mat_one])]
      exact one_mem _
    · rw [show g = genFSU 1 from ext_mat hg]
      exact hmem 1
    · rw [show g = genFSU 2 from ext_mat hg]
      exact hmem 2
    · rw [show g = genFSU 1 * genFSU 2 from ext_mat (by
        rw [hg, mat_mul, mat_genFSU, mat_genFSU]
        change x₃Mat (F4.ω + 1) = x₃Mat 1 * x₃Mat F4.ω
        rw [x₃Mat_mul, add_comm])]
      exact mul_mem (hmem 1) (hmem 2)
  · obtain ⟨a, b, ha, hg⟩ := mem_x₄Sub.1 hg
    subst ha
    rcases eq_zero_or_one_of_valid b (x₄_coord_rel hg) with rfl | rfl
    · rw [show g = 1 from ext_mat (by rw [hg, x₄Mat_zero, mat_one])]
      exact one_mem _
    · rw [show g = genFSU 3 from ext_mat hg]
      exact hmem 3

@[expose] def N0sub : Subgroup SU52 := closure (Set.range fun i : Fin 5 => genSU (genN0 i))

theorem genN0_conj_mem_Fsub (i : Fin 5) {y : SU52}
    (hy : y ∈ Fsub) : genSU (genN0 i) * y * (genSU (genN0 i))⁻¹ ∈ Fsub := by
  have hc : CheckIdent := of_checkIdent checkIdent_eq_true
  have hle : closure (Set.range genFSU) ≤
      Fsub.comap (MulAut.conj (genSU (genN0 i))).toMonoidHom := by
    refine (closure_le _).2 ?_
    rintro _ ⟨j, rfl⟩
    refine mem_Fsub_of_isFShape ?_
    change IsFShape (mat (genSU (genN0 i) * genFSU j * (genSU (genN0 i))⁻¹))
    rw [mat_mul, mat_mul, mat_inv_eq_invMat, mat_genSU, mat_genFSU]
    exact hc.1 i j
  rw [closure_genFSU] at hle
  exact hle hy

theorem N0sub_le_normalizer :
    N0sub ≤ normalizer (Fsub : Set SU52) :=
  (closure_le _).2 (by
    rintro _ ⟨i, rfl⟩
    exact mem_normalizer_fintype fun y hy => genN0_conj_mem_Fsub i hy)

theorem wordSU_mem_N0sub {w : List (Fin 10)} (hw : ∀ i ∈ w, ∃ k : Fin 5, genN0 k = i) :
    wordSU w ∈ N0sub := by
  induction w with
  | nil => exact one_mem _
  | cons i w ih =>
    change ((i :: w).map genSU).prod ∈ N0sub
    rw [List.map_cons, List.prod_cons]
    obtain ⟨k, hk⟩ := hw i List.mem_cons_self
    exact mul_mem (subset_closure ⟨k, congrArg genSU hk⟩)
      (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))

@[expose] def fSU (p : F4 × F4 × F4) (h₁ : ValidPair 0 p.1) (h₄ : ValidPair 0 p.2.2) : SU52 :=
  nfSU 0 p.1 0 p.2.1 0 p.2.2 h₁ h₄

theorem mat_fSU (p : F4 × F4 × F4) (h₁ : ValidPair 0 p.1) (h₄ : ValidPair 0 p.2.2) :
    mat (fSU p h₁ h₄) = fMat p :=
  rfl

theorem fMat_injective {p q : F4 × F4 × F4} (h : fMat p = fMat q) : p = q := by
  obtain ⟨p₁, p₂, p₃⟩ := p
  obtain ⟨q₁, q₂, q₃⟩ := q
  have e1 := congrFun (congrFun h 3) 1
  have e2 := congrFun (congrFun h 3) 0
  have e3 := congrFun (congrFun h 4) 0
  simp [fMat, nfMat, x₁Mat, x₂Mat, x₃Mat, x₄Mat, Matrix.mul_apply, Fin.sum_univ_five] at e1 e2 e3
  rw [e1, e2, e3]

theorem exists_fMat_of_mem_Fsub {y : SU52} (hy : y ∈ Fsub) :
    ∃ p : F4 × F4 × F4, ValidPair 0 p.1 ∧ ValidPair 0 p.2.2 ∧ mat y = fMat p := by
  obtain ⟨hyS, h21, h10, h20⟩ := mem_Fsub.1 hy
  obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, k₁, -, k₄⟩ :=
    exists_eq_nf_coord hyS
  rw [h10] at k₂
  rw [h21] at k₁
  rw [← k₁, ← k₂, h20, mul_zero, zero_add] at k₄
  subst k₁ k₂ k₄
  exact ⟨(b₁, a₃, b₄), x₁_coord_rel e₁, x₄_coord_rel e₄,
    by rw [mat_mul, mat_mul, mat_mul, e₁, e₂, e₃, e₄]; rfl⟩

@[expose] def orb5L : Fin 5 → F4 × F4 × F4 := Fin.cons (0, 0, 1) orb5

@[expose] def orb10L : Fin 10 → F4 × F4 × F4 := Fin.cons (0, 1, 0) orb10

theorem orb5L_valid : ∀ k : Fin 5, ValidPair 0 (orb5L k).1 ∧ ValidPair 0 (orb5L k).2.2 := by
  unfold ValidPair
  simp only [bar_apply]
  decide

theorem orb10L_valid : ∀ k : Fin 10, ValidPair 0 (orb10L k).1 ∧ ValidPair 0 (orb10L k).2.2 := by
  unfold ValidPair
  simp only [bar_apply]
  decide

@[expose] def orb5SU (k : Fin 5) : SU52 := fSU (orb5L k) (orb5L_valid k).1 (orb5L_valid k).2

@[expose] def orb10SU (k : Fin 10) : SU52 := fSU (orb10L k) (orb10L_valid k).1 (orb10L_valid k).2

theorem mat_orb5SU (k : Fin 5) : mat (orb5SU k) = fMat (orb5L k) := rfl

theorem mat_orb10SU (k : Fin 10) : mat (orb10SU k) = fMat (orb10L k) := rfl

theorem fMat_zero : fMat (0, 0, 0) = 1 := by
  simp only [fMat, nfMat, x₁Mat_zero, x₂Mat_zero, x₃Mat_zero, x₄Mat_zero, Matrix.one_mul]

theorem fMat_x₄ : fMat (0, 0, 1) = x₄Mat 0 1 := by
  simp only [fMat, nfMat, x₁Mat_zero, x₂Mat_zero, x₃Mat_zero, Matrix.one_mul]

theorem fMat_x₃ : fMat (0, 1, 0) = x₃Mat 1 := by
  simp only [fMat, nfMat, x₁Mat_zero, x₂Mat_zero, x₄Mat_zero, Matrix.one_mul, Matrix.mul_one]

theorem orb5SU_zero : orb5SU 0 = x₄SU 0 1 zero_one_rel :=
  ext_mat (by rw [mat_orb5SU]; exact fMat_x₄)

theorem orb10SU_zero : orb10SU 0 = x₃SU 1 :=
  ext_mat (by rw [mat_orb10SU]; exact fMat_x₃)

theorem orb5SU_mem (k : Fin 5) : orb5SU k ∈ Fsub := mem_Fsub_of_isFShape (by
  rw [mat_orb5SU]
  revert k
  decide)

theorem orb10SU_mem (k : Fin 10) : orb10SU k ∈ Fsub := mem_Fsub_of_isFShape (by
  rw [mat_orb10SU]
  revert k
  decide)

theorem orbL_facts : (∀ k l : Fin 5, orb5L k = orb5L l → k = l) ∧
    (∀ k l : Fin 10, orb10L k = orb10L l → k = l) ∧
    (∀ k l, orb5L k ≠ orb10L l) ∧ (∀ k, orb5L k ≠ (0, 0, 0)) ∧ ∀ k, orb10L k ≠ (0, 0, 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem orb5SU_injective : Function.Injective orb5SU := fun _ _ h =>
  orbL_facts.1 _ _ (fMat_injective (congrArg mat h))

theorem orb10SU_injective : Function.Injective orb10SU := fun _ _ h =>
  orbL_facts.2.1 _ _ (fMat_injective (congrArg mat h))

theorem orb5SU_ne_orb10SU (k : Fin 5) (l : Fin 10) : orb5SU k ≠ orb10SU l := fun h =>
  orbL_facts.2.2.1 k l (fMat_injective (congrArg mat h))

theorem orb5SU_ne_one (k : Fin 5) : orb5SU k ≠ 1 := fun h =>
  orbL_facts.2.2.2.1 k (fMat_injective (by rw [← mat_orb5SU, h, mat_one, fMat_zero]))

theorem orb10SU_ne_one (k : Fin 10) : orb10SU k ≠ 1 := fun h =>
  orbL_facts.2.2.2.2 k (fMat_injective (by rw [← mat_orb10SU, h, mat_one, fMat_zero]))

theorem mem_orb5_or_mem_orb10 {y : SU52} (hy : y ∈ Fsub) (hy1 : y ≠ 1) :
    (∃ k, y = orb5SU k) ∨ ∃ k, y = orb10SU k := by
  obtain ⟨p, h₁, h₄, hp⟩ := exists_fMat_of_mem_Fsub hy
  have hp0 : p ≠ (0, 0, 0) := by
    rintro rfl
    exact hy1 (ext_mat (by rw [hp, mat_one, fMat_zero]))
  have key : ∀ p : F4 × F4 × F4, ValidPair 0 p.1 → ValidPair 0 p.2.2 → p ≠ (0, 0, 0) →
      (∃ k, p = orb5L k) ∨ ∃ k, p = orb10L k := by
    unfold ValidPair
    simp only [bar_apply]
    decide
  rcases key p h₁ h₄ hp0 with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · exact Or.inl ⟨k, ext_mat hp⟩
  · exact Or.inr ⟨k, ext_mat hp⟩

@[expose] def orbWord5L : Fin 5 → List (Fin 10) := Fin.cons [] orbWord5

@[expose] def orbWord10L : Fin 10 → List (Fin 10) := Fin.cons [] orbWord10

theorem exists_N0_conj_orb5 (k : Fin 5) :
    ∃ n ∈ N0sub, n * orb5SU 0 * n⁻¹ = orb5SU k := by
  have hc : CheckIdent := of_checkIdent checkIdent_eq_true
  refine ⟨wordSU (orbWord5L k), wordSU_mem_N0sub ?_, ?_⟩
  · revert k
    decide
  · have e : mat (wordSU (orbWord5L k) * orb5SU 0) = mat (orb5SU k * wordSU (orbWord5L k)) := by
      rw [mat_mul, mat_mul, mat_wordSU, mat_orb5SU, mat_orb5SU]
      refine Fin.cases ?_ (fun l => ?_) k
      · simp [orbWord5L, wordMat]
      · simp only [orbWord5L, orb5L, Fin.cons_succ, Fin.cons_zero]
        rw [fMat_x₄]
        exact hc.2.1 l
    rw [ext_mat e, mul_inv_cancel_right]

theorem exists_N0_conj_orb10 (k : Fin 10) :
    ∃ n ∈ N0sub, n * orb10SU 0 * n⁻¹ = orb10SU k := by
  have hc : CheckIdent := of_checkIdent checkIdent_eq_true
  refine ⟨wordSU (orbWord10L k), wordSU_mem_N0sub ?_, ?_⟩
  · revert k
    decide
  · have e : mat (wordSU (orbWord10L k) * orb10SU 0) =
        mat (orb10SU k * wordSU (orbWord10L k)) := by
      rw [mat_mul, mat_mul, mat_wordSU, mat_orb10SU, mat_orb10SU]
      refine Fin.cases ?_ (fun l => ?_) k
      · simp [orbWord10L, wordMat]
      · simp only [orbWord10L, orb10L, Fin.cons_succ, Fin.cons_zero]
        rw [fMat_x₃]
        exact hc.2.2.1 l
    rw [ext_mat e, mul_inv_cancel_right]

theorem exists_commutator_conj {X : Type*} [Group X] {z a b : X} (ha : a * z = z * a)
    (hb : b * z = z * b) (hz : ⁅a, b⁆ = z) (m : X) :
    ∃ a' b' : X, a' * (m * z * m⁻¹) = m * z * m⁻¹ * a' ∧
      b' * (m * z * m⁻¹) = m * z * m⁻¹ * b' ∧ ⁅a', b'⁆ = m * z * m⁻¹ := by
  refine ⟨m * a * m⁻¹, m * b * m⁻¹, ?_, ?_, ?_⟩
  · calc m * a * m⁻¹ * (m * z * m⁻¹) = m * (a * z) * m⁻¹ := by group
      _ = m * (z * a) * m⁻¹ := by rw [ha]
      _ = m * z * m⁻¹ * (m * a * m⁻¹) := by group
  · calc m * b * m⁻¹ * (m * z * m⁻¹) = m * (b * z) * m⁻¹ := by group
      _ = m * (z * b) * m⁻¹ := by rw [hb]
      _ = m * z * m⁻¹ * (m * b * m⁻¹) := by group
  · rw [← hz, commutatorElement_def, commutatorElement_def]
    group

theorem one_bar_omega : (1 : F4) * bar F4.ω + bar 1 * F4.ω = 1 := by
  rw [bar_apply, bar_apply]
  decide

theorem commutator_x₂_x₃_eq :
    ⁅x₂SU 1, x₃SU F4.ω⁆ = x₄SU 0 1 zero_one_rel := by
  refine ext_mat ?_
  have h := commutator_x₂_x₃ (mat_inv_of_x₂ (mat_x₂SU 1)) (mat_inv_of_x₃ (mat_x₃SU F4.ω))
  rw [inv_inv, inv_inv, one_bar_omega] at h
  rw [commutatorElement_def, h, mat_x₄SU]

theorem commutator_x₁_x₄_eq :
    ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₄SU 1 F4.ω one_omega_rel)⁻¹⁆ = x₃SU 1 := by
  refine ext_mat ?_
  have h := commutator_x₁_x₄ (mat_x₁SU 1 F4.ω one_omega_rel) (mat_x₄SU 1 F4.ω one_omega_rel)
  rw [show bar (1 : F4) * 1 = 1 by rw [map_one, one_mul]] at h
  rw [commutatorElement_def, inv_inv, inv_inv, h, mat_x₃SU]

theorem exists_commutator_eq_of_sq
    {x : SU52} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ a b : SU52, a * x = x * a ∧ b * x = x * b ∧ ⁅a, b⁆ = x := by
  obtain ⟨g, hg⟩ := exists_conj_mem_Fsub hx
  have hy1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
    have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [this, h]
    group)
  have key : ∃ (m z a b : SU52), a * z = z * a ∧ b * z = z * b ∧ ⁅a, b⁆ = z ∧
      x = m * z * m⁻¹ := by
    rcases mem_orb5_or_mem_orb10 hg hy1 with ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨n, -, hn⟩ := exists_N0_conj_orb5 k
      refine ⟨g⁻¹ * n, orb5SU 0, x₂SU 1, x₃SU F4.ω, ?_, ?_, ?_, ?_⟩
      · rw [orb5SU_zero]
        exact (commute_X₂_X₄ (x₂SU_mem 1) (x₄SU_mem 0 1 zero_one_rel))
      · rw [orb5SU_zero]
        exact (commute_X₃_X₄ (x₃SU_mem F4.ω) (x₄SU_mem 0 1 zero_one_rel))
      · rw [orb5SU_zero]
        exact commutator_x₂_x₃_eq
      · rw [_root_.mul_inv_rev, inv_inv, show g⁻¹ * n * orb5SU 0 * (n⁻¹ * g) =
          g⁻¹ * (n * orb5SU 0 * n⁻¹) * g by group, hn, ← hk]
        group
    · obtain ⟨n, -, hn⟩ := exists_N0_conj_orb10 k
      refine ⟨g⁻¹ * n, orb10SU 0, (x₁SU 1 F4.ω one_omega_rel)⁻¹,
        (x₄SU 1 F4.ω one_omega_rel)⁻¹, ?_, ?_, ?_, ?_⟩
      · rw [orb10SU_zero]
        exact commute_X₁_X₃ (inv_mem (x₁SU_mem _ _ _)) (x₃SU_mem 1)
      · rw [orb10SU_zero]
        exact (commute_X₃_X₄ (x₃SU_mem 1) (inv_mem (x₄SU_mem _ _ _))).symm
      · rw [orb10SU_zero]
        exact commutator_x₁_x₄_eq
      · rw [_root_.mul_inv_rev, inv_inv, show g⁻¹ * n * orb10SU 0 * (n⁻¹ * g) =
          g⁻¹ * (n * orb10SU 0 * n⁻¹) * g by group, hn, ← hk]
        group
  obtain ⟨m, z, a, b, ha, hb, hz, rfl⟩ := key
  exact exists_commutator_conj ha hb hz m

@[expose] def cSU : SU52 := x₃SU 1 * x₄SU 0 1 zero_one_rel

@[expose] def bSU : SU52 :=
  x₁SU 0 1 zero_one_rel * x₄SU 0 1 zero_one_rel * uSU * vSU * uSU * vSU

theorem mat_cSU : mat cSU = cA5 := by
  rw [cSU, mat_mul, mat_x₃SU, mat_x₄SU]
  unfold cA5
  rfl

theorem mat_bSU : mat bSU = bA5 := by
  rw [bSU, mat_mul, mat_mul, mat_mul, mat_mul, mat_mul, mat_x₁SU, mat_x₄SU, mat_uSU, mat_vSU]
  unfold bA5
  rfl

@[expose] def cbSU (w : List Bool) : SU52 := (w.map fun x => if x then bSU else cSU).prod

theorem mat_cbSU (w : List Bool) : mat (cbSU w) = cbMat w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    change mat (((x :: w).map fun x => if x then bSU else cSU).prod) =
      ((x :: w).map fun x => if x then bA5 else cA5).prod
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, mat_mul]
    refine congrArg₂ _ ?_ ih
    cases x
    · exact mat_cSU
    · exact mat_bSU

@[expose] def P0sub : Subgroup SU52 := closure {cSU, bSU}

theorem cbSU_mem (w : List Bool) : cbSU w ∈ P0sub := by
  have hc : cSU ∈ P0sub := subset_closure (Set.mem_insert _ _)
  have hb : bSU ∈ P0sub := subset_closure (Set.mem_insert_of_mem _ rfl)
  refine list_prod_mem fun y hy => ?_
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
  cases x
  · simpa using hc
  · simpa using hb

theorem commutator_P0sub : ⁅P0sub, P0sub⁆ = P0sub := by
  have hc : CheckIdent := of_checkIdent checkIdent_eq_true
  obtain ⟨-, -, -, h1, h2⟩ := hc
  have e1 : cSU = ⁅cbSU (a5Word 0), cbSU (a5Word 1)⁆ := by
    have e : cSU * cbSU (a5Word 1) * cbSU (a5Word 0) = cbSU (a5Word 0) * cbSU (a5Word 1) :=
      ext_mat (by rw [mat_mul, mat_mul, mat_mul, mat_cbSU, mat_cbSU, mat_cSU]; exact h1)
    rw [commutatorElement_def, ← e]
    group
  have e2 : bSU = ⁅cbSU (a5Word 2), cbSU (a5Word 3)⁆ := by
    have e : bSU * cbSU (a5Word 3) * cbSU (a5Word 2) = cbSU (a5Word 2) * cbSU (a5Word 3) :=
      ext_mat (by rw [mat_mul, mat_mul, mat_mul, mat_cbSU, mat_cbSU, mat_bSU]; exact h2)
    rw [commutatorElement_def, ← e]
    group
  refine le_antisymm ?_ ((closure_le _).2 ?_)
  · rw [commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  · rintro _ (rfl | rfl)
    · rw [e1]
      exact commutator_mem_commutator (cbSU_mem _) (cbSU_mem _)
    · rw [e2]
      exact commutator_mem_commutator (cbSU_mem _) (cbSU_mem _)

theorem fld_x₁SU_zero_one : fld (x₁SU 0 1 zero_one_rel) = x₁SU 0 1 zero_one_rel :=
  ext_mat (by rw [mat_fld, mat_x₁SU, x₁Mat_map_bar, map_zero, map_one])

theorem fld_x₄SU_zero_one : fld (x₄SU 0 1 zero_one_rel) = x₄SU 0 1 zero_one_rel :=
  ext_mat (by rw [mat_fld, mat_x₄SU, x₄Mat_map_bar, map_zero, map_one])

theorem fld_x₃SU_one : fld (x₃SU 1) = x₃SU 1 :=
  ext_mat (by rw [mat_fld, mat_x₃SU, x₃Mat_map_bar, map_one])

theorem P0sub_le_CfldSub : P0sub ≤ CfldSub := by
  refine (closure_le _).2 ?_
  rintro _ (rfl | rfl)
  · change fld cSU = cSU
    rw [cSU, map_mul, fld_x₃SU_one, fld_x₄SU_zero_one]
  · change fld bSU = bSU
    simp only [bSU, map_mul, fld_x₁SU_zero_one, fld_x₄SU_zero_one, fld_uSU, fld_vSU]

@[expose] def yωSU : SU52 := x₃SU F4.ω * x₄SU 1 F4.ω one_omega_rel

theorem fld_yω_inv_mul : (fld yωSU)⁻¹ * yωSU = cSU := by
  rw [inv_mul_eq_iff_eq_mul]
  refine ext_mat ?_
  rw [mat_mul, mat_fld, yωSU, cSU, mat_mul, mat_mul, mat_x₃SU, mat_x₄SU, mat_x₃SU, mat_x₄SU,
    Matrix.map_mul, x₃Mat_map_bar, x₄Mat_map_bar, Matrix.mul_assoc (x₃Mat (bar F4.ω)),
    ← Matrix.mul_assoc (x₄Mat _ _) (x₃Mat 1), ← x₃Mat_x₄Mat_comm, Matrix.mul_assoc,
    ← Matrix.mul_assoc (x₃Mat (bar F4.ω)), x₃Mat_mul, x₄Mat_mul]
  have e1 : bar F4.ω + 1 = F4.ω := by rw [bar_apply]; decide
  rw [mul_zero, add_zero, add_zero, map_one, e1]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

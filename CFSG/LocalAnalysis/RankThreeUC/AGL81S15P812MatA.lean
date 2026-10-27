module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812MatDefs
public import CFSG.RankThree.PartTwo.Toolkit.Bloom

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.P812

open CFSG.RankThree.SubgroupLists CFSG.RankThree.PartTwo
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem caseA_ev_ne_zero (i : Fin 3) : ev i ≠ 0 := by
  intro h
  have h1 := congrFun h i
  simp [ev] at h1

theorem caseA_ev_mem_cline (i : Fin 3) : ev i ∈ cline i :=
  Submodule.mem_span_singleton_self _

theorem caseA_finrank_cline (i : Fin 3) : Module.finrank (ZMod 3) (cline i) = 1 :=
  finrank_span_singleton (caseA_ev_ne_zero i)

theorem caseA_mem_cplane {v : Fin 3 → ZMod 3} {a : Fin 3} (h : v a = 0) : v ∈ cplane a := by
  have hv : v = ∑ b, v b • ev b := by
    ext c
    simp [ev, Finset.sum_apply, Pi.single_apply]
  rw [hv]
  refine Submodule.sum_mem _ fun b _ => ?_
  by_cases hb : b = a
  · rw [hb, h, zero_smul]
    exact Submodule.zero_mem _
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)

theorem caseA_smul_ev_mem {P : Submodule (ZMod 3) (Fin 3 → ZMod 3)} {v : Fin 3 → ZMod 3}
    (hv : v ∈ P) (hA : (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ P)
    (hB : (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ P) (b : Fin 3) : v b • ev b ∈ P := by
  have h3 : ∀ x : ZMod 3, -x - x = x := by decide
  have h1 : v 1 • ev 1 = (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v - v := by
    rw [dA_mulVec]
    ext i
    fin_cases i <;> simp [ev, h3]
  have h2 : v 2 • ev 2 = (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v - v := by
    rw [dB_mulVec]
    ext i
    fin_cases i <;> simp [ev, h3]
  have h1' : v 1 • ev 1 ∈ P := by
    rw [h1]
    exact P.sub_mem hA hv
  have h2' : v 2 • ev 2 ∈ P := by
    rw [h2]
    exact P.sub_mem hB hv
  have h0 : v 0 • ev 0 = v - v 1 • ev 1 - v 2 • ev 2 := by
    ext i
    fin_cases i <;> simp [ev]
  have h0' : v 0 • ev 0 ∈ P := by
    rw [h0]
    exact P.sub_mem (P.sub_mem hv h1') h2'
  fin_cases b
  · exact h0'
  · exact h1'
  · exact h2'

theorem caseA_exists_cline_eq {ℓ : Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hrank : Module.finrank (ZMod 3) ℓ = 1)
    (hA : ∀ w ∈ ℓ, (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ ℓ)
    (hB : ∀ w ∈ ℓ, (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ ℓ) : ∃ a : Fin 3, ℓ = cline a := by
  have hne : ℓ ≠ ⊥ := by
    rintro rfl
    simp at hrank
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have h1 : v a • ev a ∈ ℓ := caseA_smul_ev_mem hv (hA v hv) (hB v hv) a
  have h2 : ev a ∈ ℓ := by
    have := ℓ.smul_mem (v a)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
  refine ⟨a, (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 h2
  · rw [hrank, caseA_finrank_cline]

theorem caseA_dA_mul_dA : dA * dA = 1 := by
  ext1
  rw [Units.val_mul, Units.val_one]
  exact dA.val_inv

theorem caseA_dB_mul_dB : dB * dB = 1 := by
  ext1
  rw [Units.val_mul, Units.val_one]
  exact dB.val_inv

theorem caseA_dA_mul_dB : dA * dB = dB * dA := by
  ext1
  rw [Units.val_mul, Units.val_mul]
  show Matrix.diagonal ![(1 : ZMod 3), -1, 1] * Matrix.diagonal ![1, 1, -1] =
    Matrix.diagonal ![1, 1, -1] * Matrix.diagonal ![1, -1, 1]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  fin_cases i <;> simp

theorem caseA_dA_ne_one : dA ≠ 1 := by decide

theorem caseA_dB_ne_one : dB ≠ 1 := by decide

theorem caseA_dA_ne_dB : dA ≠ dB := by decide

theorem caseA_common_fixed_point : ∀ f g : Fin 3 → Fin 3, (∀ i, f (f i) = i) → (∀ i, g (g i) = i) →
    (∀ i, f (g i) = g (f i)) → ∃ j, f j = j ∧ g j = j := by
  decide

theorem caseA_lines_injective {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hint : DirectSum.IsInternal L) (hrank : ∀ i, Module.finrank (ZMod 3) (L i) = 1) :
    Function.Injective L :=
  hint.submodule_iSupIndep.injective fun i h => by
    have h1 := hrank i
    rw [h] at h1
    simp at h1

theorem caseA_exists_common_fixed {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hinj : Function.Injective L) (hAperm : ∀ i, ∃ j, translate dA (L i) = L j)
    (hBperm : ∀ i, ∃ j, translate dB (L i) = L j) :
    ∃ j, translate dA (L j) = L j ∧ translate dB (L j) = L j := by
  choose πA hπA using hAperm
  choose πB hπB using hBperm
  have hAA : ∀ i, πA (πA i) = i := fun i => hinj (by
    calc L (πA (πA i)) = translate dA (L (πA i)) := (hπA _).symm
      _ = translate dA (translate dA (L i)) := by rw [hπA i]
      _ = translate (dA * dA) (L i) := (translate_mul _ _ _).symm
      _ = L i := by rw [caseA_dA_mul_dA, translate_one])
  have hBB : ∀ i, πB (πB i) = i := fun i => hinj (by
    calc L (πB (πB i)) = translate dB (L (πB i)) := (hπB _).symm
      _ = translate dB (translate dB (L i)) := by rw [hπB i]
      _ = translate (dB * dB) (L i) := (translate_mul _ _ _).symm
      _ = L i := by rw [caseA_dB_mul_dB, translate_one])
  have hAB : ∀ i, πA (πB i) = πB (πA i) := fun i => hinj (by
    calc L (πA (πB i)) = translate dA (L (πB i)) := (hπA _).symm
      _ = translate dA (translate dB (L i)) := by rw [hπB i]
      _ = translate (dA * dB) (L i) := (translate_mul _ _ _).symm
      _ = translate (dB * dA) (L i) := by rw [caseA_dA_mul_dB]
      _ = translate dB (translate dA (L i)) := translate_mul _ _ _
      _ = translate dB (L (πA i)) := by rw [hπA i]
      _ = L (πB (πA i)) := hπB _)
  obtain ⟨j, hjA, hjB⟩ := caseA_common_fixed_point πA πB hAA hBB hAB
  exact ⟨j, by rw [hπA, hjA], by rw [hπB, hjB]⟩

theorem caseA_le_cplane {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)}
    (hint : DirectSum.IsInternal L) (hinj : Function.Injective L) {j a : Fin 3}
    (hja : L j = cline a) (hjA : translate dA (L j) = L j) (hjB : translate dB (L j) = L j)
    (hAperm : ∀ i, ∃ k, translate dA (L i) = L k) (hBperm : ∀ i, ∃ k, translate dB (L i) = L k)
    {i : Fin 3} (hij : i ≠ j) : L i ≤ cplane a := by
  set P : Submodule (ZMod 3) (Fin 3 → ZMod 3) := ⨆ k, ⨆ (_ : k ≠ j), L k
  have hLP : ∀ k, k ≠ j → L k ≤ P := fun k hk => le_iSup₂_of_le k hk le_rfl
  have hmove : ∀ g : GL (Fin 3) (ZMod 3), translate g (L j) = L j →
      (∀ i, ∃ k, translate g (L i) = L k) → ∀ i, i ≠ j → ∃ k, k ≠ j ∧ translate g (L i) = L k := by
    intro g hg hperm i hi
    obtain ⟨k, hk⟩ := hperm i
    refine ⟨k, fun hkj => hi ?_, hk⟩
    apply hinj
    calc L i = translate g⁻¹ (translate g (L i)) := (translate_inv_translate g _).symm
      _ = translate g⁻¹ (L j) := by rw [hk, hkj]
      _ = translate g⁻¹ (translate g (L j)) := by rw [hg]
      _ = L j := translate_inv_translate g _
  intro v hv
  have hvP : v ∈ P := hLP i hij hv
  obtain ⟨k, hk, hk'⟩ := hmove dA hjA hAperm i hij
  obtain ⟨m, hm, hm'⟩ := hmove dB hjB hBperm i hij
  have hdA : (dA : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ P :=
    hLP k hk (by rw [← hk']; exact mulVec_mem_translate hv)
  have hdB : (dB : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ v ∈ P :=
    hLP m hm (by rw [← hm']; exact mulVec_mem_translate hv)
  have h1 : v a • ev a ∈ P := caseA_smul_ev_mem hvP hdA hdB a
  have h2 : v a • ev a ∈ L j := by
    rw [hja]
    exact Submodule.smul_mem _ _ (caseA_ev_mem_cline a)
  have hdisj : Disjoint (L j) P := iSupIndep_def.1 hint.submodule_iSupIndep j
  have h3 : v a • ev a = 0 := Submodule.disjoint_def.1 hdisj _ h2 h1
  have h4 : v a = 0 := by
    have := congrFun h3 a
    simpa [ev] using this
  exact caseA_mem_cplane h4

theorem caseA_caseC {H : Subgroup (GL (Fin 3) (ZMod 3))} (hA : dA ∈ H) (hB : dB ∈ H)
    {L : Fin 3 → Submodule (ZMod 3) (Fin 3 → ZMod 3)} (hint : DirectSum.IsInternal L)
    (hrank : ∀ i, Module.finrank (ZMod 3) (L i) = 1)
    (hperm : ∀ g ∈ H, ∀ i, ∃ j, translate g (L i) = L j) :
    ∃ a : Fin 3, ∀ g ∈ H,
      (∀ w ∈ cline a, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline a) ∨
      (∀ w ∈ cline a, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cplane a) := by
  have hinj := caseA_lines_injective hint hrank
  obtain ⟨j, hjA, hjB⟩ := caseA_exists_common_fixed hinj (hperm dA hA) (hperm dB hB)
  obtain ⟨a, ha⟩ := caseA_exists_cline_eq (hrank j)
    (fun w hw => by rw [← hjA]; exact mulVec_mem_translate hw)
    (fun w hw => by rw [← hjB]; exact mulVec_mem_translate hw)
  refine ⟨a, fun g hg => ?_⟩
  obtain ⟨i, hi⟩ := hperm g hg j
  by_cases hij : i = j
  · left
    intro w hw
    rw [← ha] at hw ⊢
    have := mulVec_mem_translate (g := g) hw
    rwa [hi, hij] at this
  · right
    intro w hw
    rw [← ha] at hw
    have := mulVec_mem_translate (g := g) hw
    rw [hi] at this
    exact caseA_le_cplane hint hinj ha hjA hjB (hperm dA hA) (hperm dB hB) hij this

theorem caseA_four_dvd_card {G : Type*} [Group G] {H : Subgroup G} {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y)
    (hc : x * y = y * x) (hxH : x ∈ H) (hyH : y ∈ H) : 4 ∣ Nat.card H := by
  have hc' : y * x = x * y := hc.symm
  have hlx : ∀ z : G, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hcz : ∀ z : G, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hc', mul_assoc]
  have hix : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hiy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  let V : Subgroup G :=
    { carrier := {1, x, y, x * y}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [mul_assoc, hx, hy, hlx, hc', hcz]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> simp [hix, hiy, hc'] }
  have hVH : V ≤ H := by
    intro a ha
    change a ∈ ({1, x, y, x * y} : Set G) at ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact H.one_mem
    · exact hxH
    · exact hyH
    · exact H.mul_mem hxH hyH
  have hV : Nat.card V = 4 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    change ({1, x, y, x * y} : Set G).ncard = 4
    have h12 : y ≠ x * y := fun h => hx1 (by simpa using congrArg (· * y⁻¹) h.symm)
    have h1 : x ∉ ({y, x * y} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hxy, fun h => hy1 (by simpa using congrArg (x⁻¹ * ·) h.symm)⟩
    have h0 : (1 : G) ∉ ({x, y, x * y} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨Ne.symm hx1, Ne.symm hy1, fun h => hxy ?_⟩
      rw [eq_inv_of_mul_eq_one_left h.symm, hiy]
    rw [Set.ncard_insert_of_notMem h0, Set.ncard_insert_of_notMem h1, Set.ncard_pair h12]
  exact hV ▸ Subgroup.card_dvd_of_le hVH

theorem caseA_dvd_card_statedSL : 27 ∣ Nat.card (CFSG.Open.StatedSL 3 (ZMod 3)) := by
  rw [CFSG.Open.StatedAPI.card_statedSL_three, Nat.card_zmod]
  norm_num

theorem caseA_exists_det_one {v : Fin 3 → ZMod 3} (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) (ZMod 3), (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 = v := by
  by_cases h0 : v 0 ≠ 0
  · let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1]
    have hM : M.det = 1 := by simp [M, Matrix.det_fin_three, h0]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
    ext i
    fin_cases i <;> simp [M, ev, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push Not at h0
  by_cases h1 : v 1 ≠ 0
  · let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![v 0, -1, 0; v 1, 0, 0; v 2, 0, (v 1)⁻¹]
    have hM : M.det = 1 := by simp [M, Matrix.det_fin_three, h1]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
    ext i
    fin_cases i <;> simp [M, ev, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push Not at h1
  have h2 : v 2 ≠ 0 := by
    intro h2
    apply hv
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![v 0, (v 2)⁻¹, 0; v 1, 0, 1; v 2, 0, 0]
  have hM : M.det = 1 := by simp [M, Matrix.det_fin_three, h2]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
  ext i
  fin_cases i <;> simp [M, ev, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem caseA_matrix
    (H : Subgroup (GL (Fin 3) (ZMod 3))) (hirr : CFSG.RankThree.SubgroupLists.IsIrreducibleOn H)
    (hA : dA ∈ H) (hB : dB ∈ H) :
    (∃ a : Fin 3, ∀ g ∈ H,
        (∀ w ∈ cline a, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cline a) ∨
        (∀ w ∈ cline a, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ w ∈ cplane a)) ∨
    (27 ∣ Nat.card H ∧ ∀ v : Fin 3 → ZMod 3, v ≠ 0 →
        ∃ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) *ᵥ ev 0 = v) := by
  by_cases h13 : 13 ∣ Nat.card H
  · rcases Toolkit.caseAB_of_dvd h13 with hcase | hcase
    · exfalso
      have h4 : 4 ∣ Nat.card H :=
        caseA_four_dvd_card caseA_dA_mul_dA caseA_dB_mul_dB caseA_dA_ne_one caseA_dB_ne_one
          caseA_dA_ne_dB caseA_dA_mul_dB hA hB
      have h78 := h4.trans (Toolkit.card_dvd_78_of_caseA hcase)
      omega
    · right
      have hle := Toolkit.statedSL_le_of_caseB hcase
      refine ⟨caseA_dvd_card_statedSL.trans (Subgroup.card_dvd_of_le hle), fun v hv => ?_⟩
      obtain ⟨g, hdet, hg⟩ := caseA_exists_det_one hv
      exact ⟨g, hle (CFSG.Open.StatedAPI.mem_statedSL_of_det hdet), hg⟩
  · left
    rcases irreducible_prime_degree_reduction (K := ZMod 3) Nat.prime_three
        (isIrreducibleOn_iff.1 hirr) with
      ⟨N, hNH, -, -, -, hdvd, hndvd⟩ | ⟨L, hint, hrank, hperm, -⟩ | ⟨-, -, hab⟩
    · exfalso
      rw [Nat.card_zmod] at hdvd hndvd
      apply h13
      have h13N : 13 ∣ Nat.card N := by
        by_contra h
        apply hndvd
        have hcop : Nat.Coprime (Nat.card N) 13 :=
          ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h).symm
        exact hcop.dvd_of_dvd_mul_right (show Nat.card N ∣ 2 * 13 by simpa using hdvd)
      exact h13N.trans (Subgroup.card_dvd_of_le hNH)
    · exact caseA_caseC hA hB hint hrank hperm
    · exact absurd (Toolkit.le_scalar_of_solvable (Toolkit.isSolvable_of_not_dvd h13) hab)
        (Toolkit.not_forall_scalar hirr)

end CFSG.LocalAnalysis.RankThreeUC.S15.P812

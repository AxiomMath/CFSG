module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
import CFSG.Assembly.GL83StatedBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open scoped MatrixGroups

private theorem charP_two_of_linArith {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) : CharP F 2 := by
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card F = 2 ^ n := h.2.2.2.2.1
  have hn : 2 ≤ n := h.2.2.2.2.2.1
  have hring : ringChar F = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hcard]
    exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
  rw [← hring]
  exact ringChar.charP F

private def permGL {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) : GL (Fin d) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp] private theorem coe_permGL {d : ℕ} {F : Type} [Field F]
    (σ : Equiv.Perm (Fin d)) :
    ((permGL σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl

private theorem inv_permGL {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    ((permGL σ : GL (Fin d) F))⁻¹ = permGL σ.symm := by
  apply Units.ext
  rfl

private theorem det_permGL {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (σ : Equiv.Perm (Fin d)) : (σ.permMatrix F).det = 1 := by
  haveI : CharP F 2 := charP_two_of_linArith h
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simp [h1]
  · simp only [h1, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    exact CharTwo.neg_eq 1

private theorem permGL_mem {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (σ : Equiv.Perm (Fin d)) : permGL σ ∈ LinSL d F := by
  rw [show LinSL d F = StatedSL d F from largeEvenSLGroup_eq_statedSL d]
  exact StatedAPI.mem_statedSL_of_det (by rw [coe_permGL]; exact det_permGL h σ)

private theorem permMatrix_mul_mul {d : ℕ} {F : Type} [Field F] (τ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) F) :
    τ.permMatrix F * M * (τ⁻¹).permMatrix F = M.submatrix τ τ := by
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rfl

private abbrev LinBlockClosure (d : ℕ) (F : Type) [Field F] (I : Finset (Fin d)) :
    Subgroup (LinPSL d F) :=
  Subgroup.closure (⋃ σ : Equiv.Perm (Fin d), LinBlockImage d F (I.map σ.toEmbedding))

private def IsTwoByTwo {d : ℕ} {F : Type} [Field F] (i j : Fin d)
    (M : Matrix (Fin d) (Fin d) F) : Prop :=
  ∀ a b : Fin d, (a ≠ i ∧ a ≠ j) ∨ (b ≠ i ∧ b ≠ j) →
    M a b = if a = b then 1 else 0

private theorem isTwoByTwo_transvection {d : ℕ} {F : Type} [Field F] {i j : Fin d}
    (hij : i ≠ j) (c : F) : IsTwoByTwo i j (Matrix.transvection i j c) := by
  intro a b hab
  have hsingle : Matrix.single i j c a b = 0 := by
    rw [Matrix.single_apply]
    rcases hab with ⟨ha, -⟩ | ⟨-, hb⟩
    · exact if_neg (fun hc => ha hc.1.symm)
    · exact if_neg (fun hc => hb hc.2.symm)
  rw [Matrix.transvection, Matrix.add_apply, hsingle, add_zero, Matrix.one_apply]

private theorem isTwoByTwo_diag2n {d : ℕ} {F : Type} [Field F] {i j : Fin d}
    (hij : i ≠ j) (c : F) (hc : c ≠ 0) :
    IsTwoByTwo i j
      ((Matrix.SpecialLinearGroup.diag2n hij c hc : Matrix (Fin d) (Fin d) F)) := by
  intro a b hab
  rw [Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply]
  by_cases h : a = b
  · rw [if_pos h, if_pos h]
    rcases hab with ⟨ha1, ha2⟩ | ⟨hb1, hb2⟩
    · rw [if_neg ha1, if_neg ha2]
    · rw [if_neg (fun hh => hb1 (h ▸ hh)), if_neg (fun hh => hb2 (h ▸ hh))]
  · rw [if_neg h, if_neg h]

private theorem exists_perm_maps_mem {d : ℕ} {I : Finset (Fin d)} (hI : 2 ≤ I.card)
    {i j : Fin d} (hij : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin d), i ∈ I.map σ.toEmbedding ∧ j ∈ I.map σ.toEmbedding := by
  obtain ⟨a, haI, b, hbI, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < I.card)
  have hia : i ≠ Equiv.swap a i b := by
    intro h
    apply hab
    apply (Equiv.swap a i).injective
    rw [Equiv.swap_apply_left]
    exact h
  refine ⟨(Equiv.swap a i).trans (Equiv.swap (Equiv.swap a i b) j), ?_, ?_⟩
  · refine Finset.mem_map.2 ⟨a, haI, ?_⟩
    change ((Equiv.swap a i).trans (Equiv.swap (Equiv.swap a i b) j)) a = i
    rw [Equiv.trans_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hia hij
  · refine Finset.mem_map.2 ⟨b, hbI, ?_⟩
    change ((Equiv.swap a i).trans (Equiv.swap (Equiv.swap a i b) j)) b = j
    rw [Equiv.trans_apply, Equiv.swap_apply_left]

private theorem mem_linBlockClosure_of_isTwoByTwo {d : ℕ} {F : Type} [Field F]
    {I : Finset (Fin d)} (hI : 2 ≤ I.card) {i j : Fin d} (hij : i ≠ j)
    {u : ↥(LinSL d F)}
    (h2 : IsTwoByTwo i j (((u : GL (Fin d) F) : Matrix (Fin d) (Fin d) F))) :
    LinMk d F u ∈ LinBlockClosure d F I := by
  obtain ⟨σ, hiJ, hjJ⟩ := exists_perm_maps_mem hI hij
  have hsub : ({i, j} : Finset (Fin d)) ⊆ I.map σ.toEmbedding := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hiJ
    · exact hjJ
  have mem_i : ∀ {x : Fin d}, x = i → x ∈ ({i, j} : Finset (Fin d)) := by
    intro x h; rw [h]; exact Finset.mem_insert_self i {j}
  have mem_j : ∀ {x : Fin d}, x = j → x ∈ ({i, j} : Finset (Fin d)) := by
    intro x h; rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
  have hblock : (u : GL (Fin d) F) ∈ LinBlockSet d F (I.map σ.toEmbedding) := by
    refine ⟨u.2, fun a b hab => h2 a b ?_⟩
    rcases hab with ha | hb
    · left
      exact ⟨fun h => ha (hsub (mem_i h)), fun h => ha (hsub (mem_j h))⟩
    · right
      exact ⟨fun h => hb (hsub (mem_i h)), fun h => hb (hsub (mem_j h))⟩
  exact Subgroup.subset_closure
    (Set.mem_iUnion.2 ⟨σ, Set.mem_image_of_mem (LinMk d F) hblock⟩)

private theorem permGL_conj_mem_diagSet {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) {x : GL (Fin d) F}
    (hxSL : x ∈ LinSL d F) (hxp : x ^ p = 1)
    (hxd : ∀ i j : Fin d, i ≠ j → (x : Matrix (Fin d) (Fin d) F) i j = 0) :
    permGL τ * x * (permGL τ)⁻¹ ∈ LinSL d F ∧
      (permGL τ * x * (permGL τ)⁻¹) ^ p = 1 ∧
      (∀ i j : Fin d, i ≠ j →
        (((permGL τ * x * (permGL τ)⁻¹ : GL (Fin d) F)) :
          Matrix (Fin d) (Fin d) F) i j = 0) := by
  have hτ : permGL τ ∈ LinSL d F := permGL_mem h τ
  refine ⟨?_, ?_, ?_⟩
  · exact (LinSL d F).mul_mem ((LinSL d F).mul_mem hτ hxSL) ((LinSL d F).inv_mem hτ)
  · have hconj : permGL τ * x * (permGL τ)⁻¹ = MulAut.conj (permGL τ) x := by
      rw [MulAut.conj_apply]
    rw [hconj, ← map_pow, hxp, map_one]
  · intro i j hij
    have hmat : (((permGL τ * x * (permGL τ)⁻¹ : GL (Fin d) F)) :
        Matrix (Fin d) (Fin d) F) = (x : Matrix (Fin d) (Fin d) F).submatrix τ τ := by
      rw [Units.val_mul, Units.val_mul, coe_permGL, show
        (((permGL τ)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = (τ⁻¹).permMatrix F
        from rfl, permMatrix_mul_mul]
    rw [hmat, Matrix.submatrix_apply]
    exact hxd (τ i) (τ j) (τ.injective.ne hij)

private theorem permGL_conj_mem_diagTorsion {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) {x : GL (Fin d) F}
    (hx : x ∈ LinDiagTorsion p d F) :
    permGL τ * x * (permGL τ)⁻¹ ∈ LinDiagTorsion p d F := by
  have hsub : (LinDiagTorsion p d F).map (MulAut.conj (permGL τ)).toMonoidHom ≤
      LinDiagTorsion p d F := by
    rw [LinDiagTorsion, MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro a ⟨b, hb, rfl⟩
    refine Subgroup.subset_closure ?_
    simp only [Set.mem_setOf_eq] at hb ⊢
    obtain ⟨hbSL, hbp, hbd⟩ := hb
    have := permGL_conj_mem_diagSet h τ hbSL hbp hbd
    simpa [MulAut.conj_apply] using this
  have hxmap : MulAut.conj (permGL τ) x ∈
      (LinDiagTorsion p d F).map (MulAut.conj (permGL τ)).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  have := hsub hxmap
  simpa [MulAut.conj_apply] using this

private theorem permGL_conj_mem_torsionImage {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) {y : LinPSL d F}
    (hy : y ∈ LinTorsionImage p d F) :
    LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * y *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹ ∈ LinTorsionImage p d F := by
  obtain ⟨s, hs, rfl⟩ := hy
  have hconj : (⟨permGL τ, permGL_mem h τ⟩ : ↥(LinSL d F)) * s *
      (⟨permGL τ, permGL_mem h τ⟩ : ↥(LinSL d F))⁻¹ ∈
      (LinDiagTorsion p d F).subgroupOf (LinSL d F) := by
    change (s : GL (Fin d) F) ∈ LinDiagTorsion p d F at hs
    change permGL τ * (s : GL (Fin d) F) * (permGL τ)⁻¹ ∈ LinDiagTorsion p d F
    exact permGL_conj_mem_diagTorsion h τ hs
  refine Subgroup.mem_map.2 ⟨_, hconj, ?_⟩
  simp only [map_mul, map_inv]

private theorem permGL_conj_mem_blockSet {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) {J : Finset (Fin d)} {M : GL (Fin d) F}
    (hM : M ∈ LinBlockSet d F J) :
    permGL τ * M * (permGL τ)⁻¹ ∈ LinBlockSet d F (J.map τ.symm.toEmbedding) := by
  have hτ : permGL τ ∈ LinSL d F := permGL_mem h τ
  have hSL : permGL τ * M * (permGL τ)⁻¹ ∈ LinSL d F :=
    (LinSL d F).mul_mem ((LinSL d F).mul_mem hτ hM.1) ((LinSL d F).inv_mem hτ)
  refine ⟨hSL, fun i j hij => ?_⟩
  have hmat : (((permGL τ * M * (permGL τ)⁻¹ : GL (Fin d) F)) :
      Matrix (Fin d) (Fin d) F) = (M : Matrix (Fin d) (Fin d) F).submatrix τ τ := by
    rw [Units.val_mul, Units.val_mul, coe_permGL, show
      (((permGL τ)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = (τ⁻¹).permMatrix F
      from rfl, permMatrix_mul_mul]
  rw [hmat, Matrix.submatrix_apply]
  have hnot : τ i ∉ J ∨ τ j ∉ J := by
    rcases hij with hi | hj
    · left
      intro hmem
      exact hi (Finset.mem_map.2 ⟨τ i, hmem, by simp⟩)
    · right
      intro hmem
      exact hj (Finset.mem_map.2 ⟨τ j, hmem, by simp⟩)
  rw [hM.2 (τ i) (τ j) hnot]
  by_cases hij' : i = j
  · subst hij'; simp
  · rw [if_neg hij', if_neg (fun hh => hij' (τ.injective hh))]

private theorem conj_image_blockImage_subset {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) (J : Finset (Fin d)) :
    (fun b => LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * b *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹) '' (LinBlockImage d F J) ⊆
      LinBlockImage d F (J.map τ.symm.toEmbedding) := by
  rintro x ⟨b, hb, rfl⟩
  obtain ⟨v, hv, rfl⟩ := hb
  change LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * LinMk d F v *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹ ∈
      LinBlockImage d F (J.map τ.symm.toEmbedding)
  have heq : LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * LinMk d F v *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹ =
      LinMk d F (⟨permGL τ, permGL_mem h τ⟩ * v * ⟨permGL τ, permGL_mem h τ⟩⁻¹) := by
    simp only [map_mul, map_inv]
  rw [heq]
  refine Set.mem_image_of_mem (LinMk d F) ?_
  change permGL τ * (v : GL (Fin d) F) * (permGL τ)⁻¹ ∈
    LinBlockSet d F (J.map τ.symm.toEmbedding)
  exact permGL_conj_mem_blockSet h τ hv

private theorem conj_image_blockImage {p n d : ℕ} {F : Type} [Field F] [Finite F]
    (h : LinArith p n d F) (τ : Equiv.Perm (Fin d)) (I : Finset (Fin d)) :
    (fun b => LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * b *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹) '' (LinBlockImage d F I) =
      LinBlockImage d F (I.map τ.symm.toEmbedding) := by
  refine Set.Subset.antisymm (conj_image_blockImage_subset h τ I) ?_
  intro x hx
  have hJ : (I.map τ.symm.toEmbedding).map (τ.symm).symm.toEmbedding = I := by
    rw [Finset.map_map, Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,
      Finset.map_refl]
  have hx' : LinMk d F ⟨permGL τ.symm, permGL_mem h τ.symm⟩ * x *
      (LinMk d F ⟨permGL τ.symm, permGL_mem h τ.symm⟩)⁻¹ ∈
      LinBlockImage d F I := by
    have hmem := Set.mem_image_of_mem
      (fun b => LinMk d F ⟨permGL τ.symm, permGL_mem h τ.symm⟩ * b *
        (LinMk d F ⟨permGL τ.symm, permGL_mem h τ.symm⟩)⁻¹) hx
    have := conj_image_blockImage_subset h τ.symm (I.map τ.symm.toEmbedding) hmem
    rwa [hJ] at this
  have hg' : LinMk d F ⟨permGL τ.symm, permGL_mem h τ.symm⟩ =
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹ := by
    rw [← map_inv]
    congr 1
  have hy : (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹ * x *
      LinMk d F ⟨permGL τ, permGL_mem h τ⟩ ∈ LinBlockImage d F I := by
    rw [hg'] at hx'
    simpa using hx'
  convert Set.mem_image_of_mem
    (fun b => LinMk d F ⟨permGL τ, permGL_mem h τ⟩ * b *
      (LinMk d F ⟨permGL τ, permGL_mem h τ⟩)⁻¹) hy using 1
  group

theorem lin_perm_data {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    (σ : Equiv.Perm (Fin d)) (I : Finset (Fin d)) :
    ∃ g : LinPSL d F, g ∈ Subgroup.normalizer (LinTorsionImage p d F : Set (LinPSL d F)) ∧
      (fun b => g * b * g⁻¹) '' (LinBlockImage d F I) =
        LinBlockImage d F (I.map σ.toEmbedding) := by
  refine ⟨LinMk d F ⟨permGL σ.symm, permGL_mem h σ.symm⟩, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact permGL_conj_mem_torsionImage h σ.symm
    · intro hy
      have hg_inv : (LinMk d F ⟨permGL σ.symm, permGL_mem h σ.symm⟩)⁻¹ =
          LinMk d F ⟨permGL σ, permGL_mem h σ⟩ := by
        rw [← map_inv]
        apply congrArg (LinMk d F)
        apply Subtype.ext
        show (permGL σ.symm)⁻¹ = permGL σ
        rw [inv_permGL, Equiv.symm_symm]
      have hgen := permGL_conj_mem_torsionImage h σ hy
      rw [← hg_inv] at hgen
      convert hgen using 1
      group
  · simpa using conj_image_blockImage h σ.symm I

private noncomputable def linSLEquiv (d : ℕ) (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin d) F ≃* ↥(LinSL d F) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL d F).trans
    (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL d).symm)

private theorem linSLEquiv_apply_coe {d : ℕ} {F : Type} [Field F]
    (t : Matrix.SpecialLinearGroup (Fin d) F) :
    ((linSLEquiv d F t : ↥(LinSL d F)) : GL (Fin d) F) =
      Matrix.SpecialLinearGroup.toGL t := rfl

private theorem linSLEquiv_coe {d : ℕ} {F : Type} [Field F]
    (t : Matrix.SpecialLinearGroup (Fin d) F) :
    (((linSLEquiv d F t : ↥(LinSL d F)) : GL (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = (t : Matrix (Fin d) (Fin d) F) := by
  rw [linSLEquiv_apply_coe]
  rfl

theorem lin_blocks_generate {d : ℕ} {F : Type} [Field F] [Finite F] {I : Finset (Fin d)}
    (hI : 2 ≤ I.card) :
    Subgroup.closure (⋃ σ : Equiv.Perm (Fin d), LinBlockImage d F (I.map σ.toEmbedding)) =
      (⊤ : Subgroup (LinPSL d F)) := by
  change LinBlockClosure d F I = ⊤
  have hd : 2 ≤ d := by
    have := Finset.card_le_univ I
    rw [Fintype.card_fin] at this
    omega
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  let K : Subgroup ↥(LinSL d F) := (LinBlockClosure d F I).comap (LinMk d F)
  let K' : Subgroup (Matrix.SpecialLinearGroup (Fin d) F) :=
    K.comap (linSLEquiv d F).toMonoidHom
  have htrans : ∀ (i j : Fin d) (hij : i ≠ j) (a : F),
      Matrix.SpecialLinearGroup.transvection hij a ∈ K' := by
    intro i j hij a
    change LinMk d F (linSLEquiv d F (Matrix.SpecialLinearGroup.transvection hij a)) ∈
      LinBlockClosure d F I
    exact mem_linBlockClosure_of_isTwoByTwo hI hij (by
      rw [linSLEquiv_coe, Matrix.SpecialLinearGroup.transvection_coe]
      exact isTwoByTwo_transvection hij a)
  have hdiag : ∀ (i j : Fin d) (hij : i ≠ j) {c : F} (hc : c ≠ 0),
      Matrix.SpecialLinearGroup.diag2n hij c hc ∈ K' := by
    intro i j hij c hc
    change LinMk d F (linSLEquiv d F (Matrix.SpecialLinearGroup.diag2n hij c hc)) ∈
      LinBlockClosure d F I
    exact mem_linBlockClosure_of_isTwoByTwo hI hij (by
      rw [linSLEquiv_coe]
      exact isTwoByTwo_diag2n hij c hc)
  have hK'top : K' = ⊤ := by
    apply top_unique
    intro M _
    exact Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun M => M ∈ K') M
      hdiag htrans (fun A B hA hB => K'.mul_mem hA hB)
  have hKtop : K = ⊤ := by
    apply top_unique
    intro x _
    have hx : (linSLEquiv d F).symm x ∈ K' := by rw [hK'top]; exact Subgroup.mem_top _
    have hx' : linSLEquiv d F ((linSLEquiv d F).symm x) ∈ K := hx
    simpa only [MulEquiv.apply_symm_apply] using hx'
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin d) F).subgroupOf (LinSL d F)) y
  have hxK : x ∈ K := by rw [hKtop]; exact Subgroup.mem_top x
  exact hxK

theorem lin_quot_gen {p n d : ℕ} {F : Type} [Field F] [Finite F] (h : LinArith p n d F)
    {Q : Type} [Group Q] {ψ : Q ≃* LinPSL d F} {Bbar Kbar : Subgroup Q}
    (hB : Bbar.map ψ.toMonoidHom = LinTorsionImage p d F) {I : Finset (Fin d)}
    (hI : 2 ≤ I.card)
    (hK : (Kbar.map ψ.toMonoidHom : Set (LinPSL d F)) = LinBlockImage d F I) :
    (⨆ g ∈ Subgroup.normalizer (Bbar : Set Q), Kbar.map (MulAut.conj g).toMonoidHom) = ⊤ := by
  set H : Subgroup Q :=
    ⨆ g ∈ Subgroup.normalizer (Bbar : Set Q), Kbar.map (MulAut.conj g).toMonoidHom with hH
  have hmem : ∀ b' : Q, b' ∈ Bbar ↔ ψ b' ∈ LinTorsionImage p d F := by
    intro b'
    rw [← hB]
    constructor
    · intro hb'
      exact ⟨b', hb', rfl⟩
    · rintro ⟨c, hc, hcc⟩
      have hcb : c = b' := ψ.injective hcc
      exact hcb ▸ hc
  have hblock : ∀ σ : Equiv.Perm (Fin d),
      LinBlockImage d F (I.map σ.toEmbedding) ⊆ (H.map ψ.toMonoidHom : Set (LinPSL d F)) := by
    intro σ u hu
    obtain ⟨g, hgN, himg⟩ := lin_perm_data h σ I
    rw [← himg] at hu
    obtain ⟨b, hb, rfl⟩ := hu
    rw [← hK] at hb
    obtain ⟨k, hk, rfl⟩ := hb
    have hq : ψ.symm g ∈ Subgroup.normalizer (Bbar : Set Q) := by
      rw [Subgroup.mem_normalizer_iff] at hgN ⊢
      intro b'
      rw [hmem, hmem]
      have := hgN (ψ b')
      simpa using this
    refine ⟨ψ.symm g * k * (ψ.symm g)⁻¹, ?_, ?_⟩
    · have hle := le_iSup₂ (f := fun (g : Q) (_ : g ∈ Subgroup.normalizer (Bbar : Set Q)) =>
        Kbar.map (MulAut.conj g).toMonoidHom) (ψ.symm g) hq
      exact hle ⟨k, hk, rfl⟩
    · simp
  have hle : (⊤ : Subgroup (LinPSL d F)) ≤ H.map ψ.toMonoidHom := by
    rw [← lin_blocks_generate (F := F) hI]
    exact (Subgroup.closure_le _).2 (Set.iUnion_subset hblock)
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨q', hq', hqq⟩ := hle (Subgroup.mem_top (ψ q))
  have hq'q : q' = q := ψ.injective hqq
  exact hq'q ▸ hq'

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

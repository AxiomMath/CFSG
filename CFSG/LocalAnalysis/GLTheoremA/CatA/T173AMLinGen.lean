module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ALinDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173
open scoped commutatorElement MatrixGroups

private theorem mem_largeEvenSL_iff {d : ℕ} {F : Type} [Field F] {A : GL (Fin d) F} :
    A ∈ LargeEvenSLGroup (Fin d) F ↔ (A : Matrix (Fin d) (Fin d) F).det = 1 := by
  change A ∈ (Matrix.GeneralLinearGroup.det : GL (Fin d) F →* Fˣ).ker ↔
    (A : Matrix (Fin d) (Fin d) F).det = 1
  rw [MonoidHom.mem_ker, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
    Units.val_one]

private theorem largeEvenSLGroup_normal {d : ℕ} {F : Type} [Field F] :
    (LargeEvenSLGroup (Fin d) F).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_largeEvenSL_iff] at hn ⊢
  have hg : (g : Matrix (Fin d) (Fin d) F).det *
      ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  calc ((g * n * g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det
      = (g : Matrix (Fin d) (Fin d) F).det * (n : Matrix (Fin d) (Fin d) F).det *
          ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det := by
        rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    _ = (g : Matrix (Fin d) (Fin d) F).det * 1 *
          ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det := by rw [hn]
    _ = (g : Matrix (Fin d) (Fin d) F).det *
          ((g⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F).det := by ring
    _ = 1 := hg

private noncomputable def conjSL {d : ℕ} {F : Type} [Field F] (P : GL (Fin d) F) :
    ↥(LargeEvenSLGroup (Fin d) F) ≃* ↥(LargeEvenSLGroup (Fin d) F) where
  toFun u := ⟨P * (u : GL (Fin d) F) * P⁻¹,
    (largeEvenSLGroup_normal (d := d) (F := F)).conj_mem _ u.2 P⟩
  invFun u := ⟨P⁻¹ * (u : GL (Fin d) F) * P,
    (largeEvenSLGroup_normal (d := d) (F := F)).conj_mem _ u.2 P⁻¹⟩
  left_inv u := by apply Subtype.ext; group
  right_inv u := by apply Subtype.ext; group
  map_mul' u v := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    group

@[simp] private theorem conjSL_apply_coe {d : ℕ} {F : Type} [Field F] (P : GL (Fin d) F)
    (u : ↥(LargeEvenSLGroup (Fin d) F)) :
    ((conjSL P u : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) =
      P * (u : GL (Fin d) F) * P⁻¹ := rfl

private noncomputable def toSL {d : ℕ} {F : Type} [Field F] :
    Matrix.SpecialLinearGroup (Fin d) F ≃* ↥(LargeEvenSLGroup (Fin d) F) :=
  Matrix.SpecialLinearGroup.toGLKerEquiv

@[simp] private theorem toSL_apply_coe {d : ℕ} {F : Type} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin d) F) :
    ((toSL A : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) =
      Matrix.SpecialLinearGroup.toGL A := rfl

@[simp] private theorem toSL_apply_matrix {d : ℕ} {F : Type} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin d) F) :
    (((toSL A : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) :
        Matrix (Fin d) (Fin d) F) = (A : Matrix (Fin d) (Fin d) F) := rfl


private theorem exists_card_eq_superset_pair {d m : ℕ} (hm : 2 ≤ m) (hmd : m ≤ d)
    (i j : Fin d) :
    ∃ J : Finset (Fin d), J.card = m ∧ i ∈ J ∧ j ∈ J := by
  have hcard : ({i, j} : Finset (Fin d)).card ≤ m := by
    have : ({i, j} : Finset (Fin d)).card ≤ 2 := Finset.card_le_two
    omega
  have hmle : m ≤ Fintype.card (Fin d) := by simpa using hmd
  obtain ⟨J, hsub, hJ⟩ := Finset.exists_superset_card_eq hcard hmle
  exact ⟨J, hJ, hsub (by simp), hsub (by simp)⟩

private noncomputable def permGL {d : ℕ} {F : Type} [Field F]
    (σ : Equiv.Perm (Fin d)) : GL (Fin d) F :=
  ⟨σ.permMatrix F, (σ⁻¹).permMatrix F,
    by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one],
    by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]⟩

@[simp] private theorem coe_permGL {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    ((permGL σ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = σ.permMatrix F := rfl

@[simp] private theorem coe_permGL_inv {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d)) :
    (((permGL σ)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = (σ⁻¹).permMatrix F := rfl

private theorem permMatrix_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (i j : Fin d) : σ.permMatrix F i j = if σ i = j then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]

private theorem permGL_mem_SL {d : ℕ} {F : Type} [Field F] [CharP F 2]
    (σ : Equiv.Perm (Fin d)) : permGL σ ∈ LargeEvenSLGroup (Fin d) F := by
  rw [mem_largeEvenSL_iff, coe_permGL, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]; norm_num
  · rw [h, show (((-1 : ℤˣ) : F)) = (-1 : F) by norm_num]
    exact CharTwo.neg_eq 1

private theorem permMatrix_mul_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) F) (a b : Fin d) :
    (σ.permMatrix F * M) a b = M (σ a) b := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_mul_apply]
  simp

private theorem mul_permMatrix_apply' {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (M : Matrix (Fin d) (Fin d) F) (a b : Fin d) :
    (M * σ.permMatrix F) a b = M a (σ⁻¹ b) := by
  rw [Equiv.Perm.permMatrix, PEquiv.mul_toMatrix_apply, ← Equiv.toPEquiv_symm,
    Equiv.toPEquiv_apply]
  rfl

private theorem permGL_conj_apply {d : ℕ} {F : Type} [Field F] (σ : Equiv.Perm (Fin d))
    (g : GL (Fin d) F) (a b : Fin d) :
    ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) a b =
      (g : Matrix (Fin d) (Fin d) F) (σ a) (σ b) := by
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv,
    mul_permMatrix_apply', permMatrix_mul_apply']
  simp

private theorem permGL_conj_mem_LinBlockSet {d : ℕ} {F : Type} [Field F] [CharP F 2]
    {I J : Finset (Fin d)} (σ : Equiv.Perm (Fin d)) (hσ : I.map σ.toEmbedding = J)
    {g : GL (Fin d) F} (hg : g ∈ LinBlockSet d F J) :
    permGL σ * g * (permGL σ)⁻¹ ∈ LinBlockSet d F I := by
  refine ⟨largeEvenSLGroup_normal.conj_mem g hg.1 (permGL σ), ?_⟩
  have hmemI : ∀ x, σ x ∈ J ↔ x ∈ I := by
    intro x
    rw [← hσ, Finset.mem_map]
    exact ⟨fun ⟨y, hy, hyx⟩ => σ.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  intro a b hab
  rw [permGL_conj_apply]
  have hJ : σ a ∉ J ∨ σ b ∉ J := by
    rcases hab with h | h
    · exact Or.inl (fun hh => h ((hmemI a).mp hh))
    · exact Or.inr (fun hh => h ((hmemI b).mp hh))
  rw [hg.2 (σ a) (σ b) hJ]
  by_cases hab' : a = b
  · subst hab'; rw [if_pos rfl, if_pos rfl]
  · rw [if_neg hab', if_neg (fun h => hab' (σ.injective h))]

private theorem closureIn_conj_mem {G : Type} [Group G] (K N : Subgroup G) {b : G}
    (hb : b ∈ N) {k : G} (hk : k ∈ K) :
    b * k * b⁻¹ ∈ closureIn (G := G) K N := by
  rw [closureIn]
  refine le_iSup (fun a => ⨆ (_ : a ∈ N), K.map (MulAut.conj a).toMonoidHom) b ?_
  refine le_iSup (fun _ : b ∈ N => K.map (MulAut.conj b).toMonoidHom) hb ?_
  simpa using Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hk

private theorem transvection_toSL_mem_LinBlockSet {d : ℕ} {F : Type} [Field F]
    {J : Finset (Fin d)} {i j : Fin d} (hij : i ≠ j) (hi : i ∈ J) (hj : j ∈ J) (c : F) :
    ((toSL (Matrix.SpecialLinearGroup.transvection hij c) :
      ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) ∈ LinBlockSet d F J := by
  refine ⟨(toSL _).2, ?_⟩
  intro a b hab
  rw [toSL_apply_matrix, Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases h : a = b
  · subst h
    have haJ : a ∉ J := hab.elim id id
    have hai : a ≠ i := fun hh => haJ (hh ▸ hi)
    rw [if_pos rfl, if_neg (fun hh => hai hh.1.symm)]
    simp
  · have hnot : ¬(i = a ∧ j = b) := by
      rintro ⟨hia, hjb⟩
      rcases hab with ha | hb
      · exact ha (hia ▸ hi)
      · exact hb (hjb ▸ hj)
    rw [if_neg h, if_neg hnot]
    simp

private theorem diag2n_toSL_mem_LinBlockSet {d : ℕ} {F : Type} [Field F]
    {J : Finset (Fin d)} {i j : Fin d} (hij : i ≠ j) {c : F} (hc : c ≠ 0)
    (hi : i ∈ J) (hj : j ∈ J) :
    ((toSL (Matrix.SpecialLinearGroup.diag2n hij c hc) :
      ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) ∈ LinBlockSet d F J := by
  refine ⟨(toSL _).2, ?_⟩
  intro a b hab
  rw [toSL_apply_matrix, Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h
    have haJ : a ∉ J := hab.elim id id
    have hai : a ≠ i := fun hh => haJ (hh ▸ hi)
    have haj : a ≠ j := fun hh => haJ (hh ▸ hj)
    rw [if_pos rfl, if_pos rfl, if_neg hai, if_neg haj]
  · rw [if_neg h, if_neg h]

private theorem eq_top_of_LinBlockSet_le {d : ℕ} {F : Type} [Field F] {m : ℕ}
    (hm : 2 ≤ m) (hmd : m ≤ d) (H : Subgroup ↥(LargeEvenSLGroup (Fin d) F))
    (hH : ∀ J : Finset (Fin d), J.card = m → ∀ g : ↥(LargeEvenSLGroup (Fin d) F),
      (g : GL (Fin d) F) ∈ LinBlockSet d F J → g ∈ H) :
    H = ⊤ := by
  haveI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (le_trans hm hmd)
  have hmem : ∀ A : Matrix.SpecialLinearGroup (Fin d) F, toSL A ∈ H := by
    intro A
    refine Matrix.SpecialLinearGroup.diagonal_transvection_induction'
      (fun A => toSL A ∈ H) A ?_ ?_ ?_
    · intro i j hij c hc
      obtain ⟨J, hJ, hiJ, hjJ⟩ := exists_card_eq_superset_pair hm hmd i j
      exact hH J hJ _ (diag2n_toSL_mem_LinBlockSet hij hc hiJ hjJ)
    · intro i j hij c
      obtain ⟨J, hJ, hiJ, hjJ⟩ := exists_card_eq_superset_pair hm hmd i j
      exact hH J hJ _ (transvection_toSL_mem_LinBlockSet hij hiJ hjJ c)
    · intro A B hA hB
      rw [map_mul]
      exact H.mul_mem hA hB
  rw [eq_top_iff]
  intro u _
  obtain ⟨A, rfl⟩ : ∃ A, toSL A = u := ⟨toSL.symm u, toSL.apply_symm_apply u⟩
  exact hmem A

theorem lin_gen {d : ℕ} {F : Type} [Field F] {m : ℕ} (hm : 2 ≤ m) (hmd : m ≤ d)
    (P : GL (Fin d) F) (H : Subgroup ↥(LargeEvenSLGroup (Fin d) F))
    (hH : ∀ J : Finset (Fin d), J.card = m → ∀ u : ↥(LargeEvenSLGroup (Fin d) F),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ LinBlockSet d F J → u ∈ H) :
    H = ⊤ := by
  have htop : H.comap (conjSL P⁻¹).toMonoidHom = ⊤ := by
    refine eq_top_of_LinBlockSet_le hm hmd _ (fun J hJ g hg => ?_)
    rw [Subgroup.mem_comap]
    refine hH J hJ (conjSL P⁻¹ g) ?_
    have hcoe : (P * ((conjSL P⁻¹ g : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F) *
        P⁻¹) = (g : GL (Fin d) F) := by
      rw [conjSL_apply_coe]; group
    rw [hcoe]; exact hg
  rw [eq_top_iff]
  intro u _
  have hmem : (conjSL P⁻¹).symm u ∈ H.comap (conjSL P⁻¹).toMonoidHom := by
    rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hmem
  change (conjSL P⁻¹) ((conjSL P⁻¹).symm u) ∈ H at hmem
  rwa [(conjSL P⁻¹).apply_symm_apply u] at hmem

theorem lin_closure_top {d : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S N K : Subgroup Ω}
    {F : Type} [Field F] [Finite F] [CharP F 2] (hd : 3 ≤ d)
    (ψ : ↥(LargeEvenSLGroup (Fin d) F) →* ↥S) (hψ : Function.Surjective ψ) (P : GL (Fin d) F)
    (I : Finset (Fin d)) (hI : 2 ≤ I.card)
    (hK : ∀ k : Ω, k ∈ K ↔ ∃ u : ↥(LargeEvenSLGroup (Fin d) F),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ LinBlockSet d F I ∧ (ψ u : Ω) = k)
    (hN : ∀ (σ : Equiv.Perm (Fin d)) (Pσ : GL (Fin d) F) (u : ↥(LargeEvenSLGroup (Fin d) F)),
      (Pσ : Matrix (Fin d) (Fin d) F) = σ.permMatrix F → (u : GL (Fin d) F) = P⁻¹ * Pσ * P →
        (ψ u : Ω) ∈ N) :
    S ≤ closureIn K N := by
  have hId : I.card ≤ d := by
    have := Finset.card_le_univ I
    simpa using this
  have hblock : ∀ J : Finset (Fin d), J.card = I.card →
      ∀ u : ↥(LargeEvenSLGroup (Fin d) F),
      (P * (u : GL (Fin d) F) * P⁻¹) ∈ LinBlockSet d F J →
        (ψ u : Ω) ∈ closureIn K N := by
    intro J hJ u hu
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq I J hJ.symm
    let R : GL (Fin d) F := (permGL σ)⁻¹
    let w : ↥(LargeEvenSLGroup (Fin d) F) :=
      ⟨P⁻¹ * R * P,
        largeEvenSLGroup_normal.conj_mem R (Subgroup.inv_mem _ (permGL_mem_SL σ)) P⁻¹⟩
    have hwN : (ψ w : Ω) ∈ N := hN σ⁻¹ (permGL σ⁻¹) w rfl rfl
    have hhere : (ψ (w⁻¹ * u * w) : Ω) ∈ K := by
      rw [hK]
      refine ⟨w⁻¹ * u * w, ?_, rfl⟩
      have heq : P * (((w⁻¹ * u * w : ↥(LargeEvenSLGroup (Fin d) F)) : GL (Fin d) F)) *
          P⁻¹ = permGL σ * (P * (u : GL (Fin d) F) * P⁻¹) * (permGL σ)⁻¹ := by
        dsimp only [w, R]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact permGL_conj_mem_LinBlockSet σ hσ hu
    have hmem : (ψ w : Ω) * (ψ (w⁻¹ * u * w) : Ω) * (ψ w : Ω)⁻¹ ∈ closureIn K N :=
      closureIn_conj_mem K N hwN hhere
    have hwu : (ψ w : Ω) * (ψ (w⁻¹ * u * w) : Ω) * (ψ w : Ω)⁻¹ = (ψ u : Ω) := by
      rw [map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [hwu] at hmem
  have hgen : Subgroup.comap ψ ((closureIn K N).comap S.subtype) = ⊤ :=
    lin_gen hI hId P _ (fun J hJ u hu => hblock J hJ u hu)
  intro s hs
  obtain ⟨u, hu⟩ := hψ (⟨s, hs⟩ : ↥S)
  have humem : u ∈ Subgroup.comap ψ ((closureIn K N).comap S.subtype) := by
    rw [hgen]; trivial
  rw [Subgroup.mem_comap, Subgroup.mem_comap] at humem
  rwa [hu] at humem

private theorem le_center_of_normal_isPGroup_two {Q : Type*} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple Q) {N : Subgroup Q} (hNn : N.Normal) (hN2 : IsPGroup 2 N) :
    N ≤ Subgroup.center Q := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' _
  have hMnorm : (N.map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  have hM2 : IsPGroup 2 (N.map π) := hN2.map π
  rcases Subgroup.Normal.eq_bot_or_eq_top (N.map π) with hM | hM
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hM
  · exfalso
    haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hQ.2.toNontrivial
    have hM2' : IsPGroup 2 (Q ⧸ Subgroup.center Q) := (hM ▸ hM2).of_equiv Subgroup.topEquiv
    have hcenter : Subgroup.center (Q ⧸ Subgroup.center Q) = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top
        (Subgroup.center (Q ⧸ Subgroup.center Q)) with h | h
      · exact absurd h (IsPGroup.bot_lt_center hM2').ne'
      · exact h
    haveI : IsMulCommutative (Q ⧸ Subgroup.center Q) :=
      Subgroup.center_eq_top_iff.mp hcenter
    have hcomm : commutator (Q ⧸ Subgroup.center Q) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
    have hcommtop : commutator (Q ⧸ Subgroup.center Q) = ⊤ := by
      have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup Q)) (H₂ := ⊤) π
      rw [show (⁅(⊤ : Subgroup Q), ⊤⁆ : Subgroup Q) = ⊤ from hQ.1, Subgroup.map_top,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)] at h
      exact h.symm
    rw [hcomm] at hcommtop
    exact bot_ne_top hcommtop

theorem cfg_hc_contra {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (hS : S ≤ closureIn K N) : False := by
  have hSn : S.Normal := hcfg.normal
  have hKS : K ≤ S := by
    have h := hcfg.std
    unfold GLAStdSubPre at h
    exact h.2.2.2.2.2.1.1.trans inf_le_left
  have hclS : closureIn K N ≤ S := by
    rw [closureIn]
    refine iSup_le (fun a => iSup_le (fun _ => ?_))
    rintro y ⟨k, hk, rfl⟩
    exact hSn.conj_mem k (hKS hk) a
  have hEq : closureIn K N = S := le_antisymm hclS hS
  obtain ⟨T, hTS, hT2, hNT, hne⟩ := hcfg.hc
  have hST : S ≤ Subgroup.normalizer (T : Set Ω) := by
    rw [← hEq]
    exact (le_sup_left : closureIn K N ≤ closureIn K N ⊔ B).trans hNT
  have hTnorm : (T.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr hST
  have hT2' : IsPGroup 2 (T.subgroupOf S) := hT2.comap_subtype
  have hcenter : T.subgroupOf S ≤ Subgroup.center ↥S :=
    le_center_of_normal_isPGroup_two hcfg.qs hTnorm hT2'
  have hcomm : ⁅S, T⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have hc : (⟨t, hTS ht⟩ : ↥S) ∈ Subgroup.center ↥S :=
      hcenter (Subgroup.mem_subgroupOf.mpr ht)
    simpa using (Subgroup.mem_center_iff.mp hc (⟨s, hs⟩ : ↥S)).symm
  rw [hEq] at hne
  exact hne hcomm

end CFSG.LocalAnalysis.GLTheoremA.T173A

end

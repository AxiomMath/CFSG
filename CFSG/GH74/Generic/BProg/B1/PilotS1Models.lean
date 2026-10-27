module

public import CFSG.GH74.Generic.BProg.B1.PilotS1Facts
public import CFSG.GH74.Generic.Front.DataLin
public import CFSG.GH74.Generic.Front.DataUni
public import CFSG.GH74.GLS.Stage2.Final.ModelRefl

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage2.Final.ModelBlock Matrix Subgroup
open scoped MatrixGroups commutatorElement

section Model

variable {F : Type} [Field F]

theorem diagGL_mul_self_eq_one {a b : GL (Fin 2) F} :
    diagGL a b * diagGL a b = 1 ↔ a * a = 1 ∧ b * b = 1 := by
  rw [diagGL_mul, ← diagGL_one]
  constructor
  · intro h; exact diagGL_inj h
  · rintro ⟨h1, h2⟩; rw [h1, h2]

theorem gl2_invol_of_det_one (h2 : (2 : F) ≠ 0) {a : GL (Fin 2) F} (ha : a * a = 1)
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det = 1) : a = 1 ∨ a = -1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, hd⟩ := refl_trace_det ha hcon.1 hcon.2
  rw [hdet] at hd
  apply h2
  linear_combination hd

theorem det_neg_one_gl2 : (((-1 : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [Matrix.det_neg]

theorem det_commutator_gl2 (a b : GL (Fin 2) F) :
    ((⁅a, b⁆ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  have h : Matrix.GeneralLinearGroup.det ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have := congrArg (fun u : Fˣ => (u : F)) h
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this
  exact this

theorem diagGL_commutator (a b a' b' : GL (Fin 2) F) :
    ⁅diagGL a b, diagGL a' b'⁆ = diagGL ⁅a, a'⁆ ⁅b, b'⁆ := by
  simp only [commutatorElement_def, diagGL_mul, diagGL_inv]

theorem sl2_not_comm (F : Type) [Field F] : ∃ s t : SL(2, F), s * t ≠ t * s := by
  refine ⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩, ?_⟩
  intro h
  have h' := congr_arg (fun m : SL(2, F) => (m : Matrix (Fin 2) (Fin 2) F)) h
  have h'' := congr_fun (congr_fun h' 0) 0
  change ((!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 =
    ((!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F)) 0 0 at h''
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h''

variable (M : ModelData F)

open ModelData

theorem commutator_mem_sup (h2 : (2 : F) ≠ 0) {a b : ↥M.K4} (ha : a * M.yK = M.yK * a)
    (hb : b * M.yK = M.yK * b) : ⁅a, b⁆ ∈ M.J2 ⊔ M.J4 := by
  obtain ⟨a1, a2, hae, ha1, ha2, -⟩ := M.exists_diagGL_of_comm h2 a.2 (congrArg Subtype.val ha)
  obtain ⟨b1, b2, hbe, hb1, hb2, -⟩ := M.exists_diagGL_of_comm h2 b.2 (congrArg Subtype.val hb)
  have hH : ∀ c1 c2 : GL (Fin 2) F, c1 ∈ M.U2 → c2 ∈ M.U2 → ⁅c1, c2⁆ ∈ M.H2 := by
    intro c1 c2 hc1 hc2
    refine (M.mem_H2 _).2 ⟨?_, det_commutator_gl2 _ _⟩
    rw [commutatorElement_def]
    exact M.U2.mul_mem (M.U2.mul_mem (M.U2.mul_mem hc1 hc2) (M.U2.inv_mem hc1)) (M.U2.inv_mem hc2)
  have hmem1 := hH a1 b1 ha1 hb1
  have hmem2 := hH a2 b2 ha2 hb2
  have hprod : (⁅a, b⁆ : ↥M.K4) = ⟨blkL F ⁅a1, b1⁆, M.blkL_mem_K4 hmem1⟩ *
      ⟨blkR F ⁅a2, b2⁆, M.blkR_mem_K4 hmem2⟩ := by
    apply Subtype.ext
    have : ((⁅a, b⁆ : ↥M.K4) : GL (Fin 4) F) = ⁅(a : GL (Fin 4) F), (b : GL (Fin 4) F)⁆ := rfl
    rw [this, hae, hbe, diagGL_commutator]
    exact diagGL_eq_blkL_mul_blkR _ _
  rw [hprod]
  exact Subgroup.mul_mem_sup (ModelData.blkL_mem_J2 hmem1) (ModelData.blkR_mem_J4 hmem2)

theorem disjoint_J2_J4 : Disjoint M.J2 M.J4 := by
  rw [Subgroup.disjoint_def]
  intro g hg1 hg2
  obtain ⟨a, -, ha⟩ := mem_J2.1 hg1
  obtain ⟨b, -, hb⟩ := mem_J4.1 hg2
  have h1 : diagGL a 1 = diagGL 1 b := by
    rw [← blkL_apply, ← blkR_apply, ← ha, ← hb]
  have h := diagGL_inj h1
  apply Subtype.ext
  rw [ha, h.1, blkL_apply, diagGL_one]
  rfl

theorem invol_of_centralizes_J2 (h2 : (2 : F) ≠ 0) {F' : Type} [Field F'] (e2 : SL(2, F') ≃* ↥M.H2)
    {d : ↥M.K4} (hdd : d * d = 1) (hdj : ∀ j ∈ M.J2, d * j = j * d) :
    d = 1 ∨ d = M.xK ∨ d = M.yK ∨ d = M.xK * M.yK := by
  have hdy : (d : GL (Fin 4) F) * yGL F = yGL F * d := congrArg Subtype.val (hdj M.yK M.yK_mem_J2)
  obtain ⟨a, b, hde, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 d.2 hdy
  have hdd' : diagGL a b * diagGL a b = 1 := by
    rw [← hde]
    exact congrArg Subtype.val hdd
  obtain ⟨haa, hbb⟩ := diagGL_mul_self_eq_one.1 hdd'
  have hcomm : ∀ h ∈ M.H2, (a : Matrix (Fin 2) (Fin 2) F) * (h : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * (a : Matrix (Fin 2) (Fin 2) F) := by
    intro h hh
    have hj : (⟨blkL F h, M.blkL_mem_K4 hh⟩ : ↥M.K4) ∈ M.J2 := ModelData.blkL_mem_J2 hh
    have h3 : diagGL a b * diagGL h 1 = diagGL h 1 * diagGL a b := by
      have h3' : (d : GL (Fin 4) F) * blkL F h = blkL F h * (d : GL (Fin 4) F) :=
        congrArg Subtype.val (hdj _ hj)
      rw [hde, blkL_apply] at h3'
      exact h3'

    rw [diagGL_mul, diagGL_mul] at h3
    have h4 := (diagGL_inj h3).1
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) h4
    simpa using this
  have ha_pm : a = 1 ∨ a = -1 := by
    by_cases hsc : ∃ c : F, (a : Matrix (Fin 2) (Fin 2) F) = c • 1
    · obtain ⟨c, hc⟩ := hsc
      have hcc : c * c = 1 := by
        have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) haa
        simpa [Units.val_mul, hc, Matrix.mul_apply, Fin.sum_univ_two] using this
      rcases mul_self_eq_one_iff.1 hcc with rfl | rfl
      · left
        exact Units.ext (by simpa using hc)
      · right
        exact Units.ext (by simpa using hc)
    · exfalso
      obtain ⟨s, t, hst⟩ := sl2_not_comm F'
      apply hst
      apply e2.injective
      have hs := hcomm ((e2 s : ↥M.H2) : GL (Fin 2) F) (e2 s).2
      have ht := hcomm ((e2 t : ↥M.H2) : GL (Fin 2) F) (e2 t).2
      have h5 := CFSG.SectionRank.Ccomm.commute_of_commute_nonscalar hsc hs ht
      apply Subtype.ext
      apply Units.ext
      simpa using h5
  have hdeta : (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rcases ha_pm with rfl | rfl
    · simp
    · exact det_neg_one_gl2
  have hdetb : (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [hdeta, one_mul] at hdet
    exact hdet
  have hb_pm := gl2_invol_of_det_one h2 hbb hdetb
  have hxy : (M.xK * M.yK : ↥M.K4) = M.xyK := M.xK_mul_yK
  rcases ha_pm with rfl | rfl <;> rcases hb_pm with rfl | rfl
  · left
    apply Subtype.ext
    rw [hde, diagGL_one]
    rfl
  · right; right; right
    rw [hxy]
    apply Subtype.ext
    rw [hde]
    rfl
  · right; right; left
    apply Subtype.ext
    rw [hde]
    rfl
  · right; left
    apply Subtype.ext
    rw [hde]
    rfl

theorem splitAt_yK (h2 : (2 : F) ≠ 0) {F' : Type} [Field F'] [Finite F'] (e2 : SL(2, F') ≃* ↥M.H2)
    (hsq : Nat.card F' < 4 → ∀ c : F, c ≠ 0 → c * c = 1) :
    SplitAt F' (⊤ : Subgroup ↥M.K4) M.xK M.yK M.J2 M.J4 where
  ord := M.orderOf_yK h2
  le₁ := le_inf M.J2_le_centralizer le_top
  le₂ := le_inf M.J4_le_centralizer le_top
  comm := fun a _ b _ ha hb => commutator_mem_sup M h2 ha hb
  norm₁ := fun a _ ha j hj => by
    have hn := M.centralizer_yK_le_normalizer_J2 h2 (Subgroup.mem_centralizer_singleton_iff.2 ha)
    exact (Subgroup.mem_set_normalizer_iff.1 hn j).1 hj
  norm₂ := fun a _ ha j hj => by
    have hn := M.centralizer_yK_le_normalizer_J4 h2 (Subgroup.mem_centralizer_singleton_iff.2 ha)
    exact (Subgroup.mem_set_normalizer_iff.1 hn j).1 hj
  commute := fun a ha b hb => M.J2_comm_J4 ha hb
  disj := disjoint_J2_J4 M
  u_mem := M.yK_mem_J2
  zu_mem := by rw [M.xK_mul_yK]; exact M.xyK_mem_J4
  equiv₁ := ⟨M.J2EquivH2.trans e2.symm⟩
  equiv₂ := ⟨M.J4EquivH2.trans e2.symm⟩
  invol := fun d _ hdd hdj => invol_of_centralizes_J2 M h2 e2 hdd hdj
  sq_mem := fun hF a _ ha => by
    obtain ⟨a1, a2, hae, ha1, ha2, -⟩ := M.exists_diagGL_of_comm h2 a.2 (congrArg Subtype.val ha)
    have hsqdet : ∀ c : GL (Fin 2) F,
        ((c * c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      intro c
      rw [Units.val_mul, Matrix.det_mul]
      have hne : (c : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
        have := (Matrix.GeneralLinearGroup.det c).ne_zero
        rwa [Matrix.GeneralLinearGroup.val_det_apply] at this
      exact hsq hF _ hne
    have hm1 : a1 * a1 ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem ha1 ha1, hsqdet a1⟩
    have hm2 : a2 * a2 ∈ M.H2 := (M.mem_H2 _).2 ⟨M.U2.mul_mem ha2 ha2, hsqdet a2⟩
    have hprod : a * a = ⟨blkL F (a1 * a1), M.blkL_mem_K4 hm1⟩ *
        ⟨blkR F (a2 * a2), M.blkR_mem_K4 hm2⟩ := by
      apply Subtype.ext
      have : ((a * a : ↥M.K4) : GL (Fin 4) F) = (a : GL (Fin 4) F) * (a : GL (Fin 4) F) := rfl
      rw [this, hae, diagGL_mul]
      exact diagGL_eq_blkL_mul_blkR _ _
    rw [hprod]
    exact Subgroup.mul_mem_sup (ModelData.blkL_mem_J2 hm1) (ModelData.blkR_mem_J4 hm2)

theorem splitLike_top (h2 : (2 : F) ≠ 0) {F' : Type} [Field F'] [Finite F'] (e2 : SL(2, F') ≃* ↥M.H2)
    (hsq : Nat.card F' < 4 → ∀ c : F, c ≠ 0 → c * c = 1)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK) :
    Split1Like F' (⊤ : Subgroup ↥M.K4) M.xK := by
  refine ⟨trivial, M.orderOf_xK h2, fun g _ => Subgroup.mem_center_iff.1 M.xK_mem_center g, ?_⟩
  intro u _ hu2 huz
  have huu : u * u = 1 := by rw [← pow_two]; exact hu2 ▸ pow_orderOf_eq_one u
  have hu1 : u ≠ 1 := fun h => by simp [h] at hu2
  have hucen : u ∉ Subgroup.center ↥M.K4 := by
    intro hc
    rcases (hcenter u).1 hc with h | h
    · exact hu1 (Subtype.ext (by simpa using h))
    · exact huz (Subtype.ext h)
  obtain ⟨k, hk⟩ := hone u huu hu1 hucen
  let σ : ↥M.K4 →* ↥M.K4 := (MulAut.conj k⁻¹).toMonoidHom
  have hσ : Function.Injective σ := (MulAut.conj k⁻¹).injective
  have hσy : σ M.yK = u := by
    have : u = k⁻¹ * M.yK * k := by rw [← hk]; group
    simp [σ, this]
  have hσx : σ M.xK = M.xK := by
    have h1 := Subgroup.mem_center_iff.1 M.xK_mem_center k⁻¹
    simp [σ]
    rw [h1]
    group
  have hσtop : (⊤ : Subgroup ↥M.K4).map σ = ⊤ := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top]
    exact (MulAut.conj k⁻¹).surjective
  have := (splitAt_yK M h2 e2 hsq).map σ hσ
  rw [hσtop, hσx, hσy] at this
  exact ⟨_, _, this⟩

@[expose] def V4 (F : Type) [Field F] : Set (GL (Fin 4) F) := {1, yGL F, xyGL F, xGL F}

theorem V4_ncard_le : (V4 F).ncard ≤ 4 := by
  classical
  have h1 := Set.ncard_insert_le (1 : GL (Fin 4) F) ({yGL F, xyGL F, xGL F} : Set (GL (Fin 4) F))
  have h2 := Set.ncard_insert_le (yGL F) ({xyGL F, xGL F} : Set (GL (Fin 4) F))
  have h3 := Set.ncard_insert_le (xyGL F) ({xGL F} : Set (GL (Fin 4) F))
  have h4 := Set.ncard_singleton (xGL F)
  unfold V4
  omega

theorem diagGL_mem_V4 (h2 : (2 : F) ≠ 0) {a b : GL (Fin 2) F}
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1)
    (hbb : b * b = 1) (ha : a = 1 ∨ a = -1) : diagGL a b ∈ V4 F := by
  have hda : (a : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rcases ha with rfl | rfl
    · simp
    · exact det_neg_one_gl2
  rw [hda, one_mul] at hdet
  rcases ha with rfl | rfl
  · rcases gl2_invol_of_det_one h2 hbb hdet with rfl | rfl
    · left; exact diagGL_one
    · right; right; left; rfl
  · rcases gl2_invol_of_det_one h2 hbb hdet with rfl | rfl
    · right; left; rfl
    · right; right; right; rfl

theorem exists_diagGL_invol (h2 : (2 : F) ≠ 0) {g : GL (Fin 4) F} (hg : g ∈ M.K4) (hgg : g * g = 1)
    (hgy : g * yGL F = yGL F * g) :
    ∃ a b : GL (Fin 2) F, g = diagGL a b ∧ a * a = 1 ∧ b * b = 1 ∧
      (a : Matrix (Fin 2) (Fin 2) F).det * (b : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  obtain ⟨a, b, hab, -, -, hdet⟩ := M.exists_diagGL_of_comm h2 hg hgy
  have h1 : diagGL a b * diagGL a b = 1 := by rw [← hab]; exact hgg
  obtain ⟨haa, hbb⟩ := diagGL_mul_self_eq_one.1 h1
  exact ⟨a, b, hab, haa, hbb, hdet⟩

theorem xGL_mem_of_card_eight (h2 : (2 : F) ≠ 0) (E : Subgroup (GL (Fin 4) F)) (hEK : E ≤ M.K4)
    (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hy : yGL F ∈ E) (hcard : Nat.card ↥E = 8) :
    xGL F ∈ E := by
  classical
  have hfin : Finite ↥E := Nat.finite_of_card_ne_zero (by omega)
  have hEsq : ∀ g ∈ E, g * g = 1 := fun g hg => by
    rw [← pow_two]; exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) g hg
  have hEcomm : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g := fun g hg g' hg' =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥E)).comm ⟨g, hg⟩ ⟨g', hg'⟩)
  have hV4E : V4 F ∩ (E : Set (GL (Fin 4) F)) ⊆ V4 F := Set.inter_subset_left
  have hclaim : ∀ g ∈ E, g ∉ V4 F → ∀ g' ∈ E, g' ∉ V4 F → g * g' ∈ V4 F := by
    intro g hg hgV g' hg' hg'V
    obtain ⟨a, b, hgab, haa, hbb, hdet⟩ := exists_diagGL_invol M h2 (hEK hg) (hEsq g hg)
      (hEcomm g hg _ hy)
    obtain ⟨a', b', hgab', haa', hbb', hdet'⟩ := exists_diagGL_invol M h2 (hEK hg') (hEsq g' hg')
      (hEcomm g' hg' _ hy)
    have hna : ¬ (a = 1 ∨ a = -1) := fun h => hgV (hgab ▸ diagGL_mem_V4 h2 hdet hbb h)
    have hna' : ¬ (a' = 1 ∨ a' = -1) := fun h => hg'V (hgab' ▸ diagGL_mem_V4 h2 hdet' hbb' h)
    push Not at hna hna'
    have hda := (refl_trace_det haa hna.1 hna.2).2
    have hda' := (refl_trace_det haa' hna'.1 hna'.2).2
    have hdb : (b : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      rw [hda] at hdet; linear_combination -hdet
    have hdb' : (b' : Matrix (Fin 2) (Fin 2) F).det = -1 := by
      rw [hda'] at hdet'; linear_combination -hdet'
    have hcomm : diagGL a b * diagGL a' b' = diagGL a' b' * diagGL a b := by
      rw [← hgab, ← hgab']; exact hEcomm g hg g' hg'
    rw [diagGL_mul, diagGL_mul] at hcomm
    obtain ⟨hcomm1, hcomm2⟩ := diagGL_inj hcomm
    have haa2 : (a * a') * (a * a') = 1 := by
      calc (a * a') * (a * a') = a * (a' * a) * a' := by group
        _ = a * (a * a') * a' := by rw [← hcomm1]
        _ = (a * a) * (a' * a') := by group
        _ = 1 := by rw [haa, haa', one_mul]
    have hbb2 : (b * b') * (b * b') = 1 := by
      calc (b * b') * (b * b') = b * (b' * b) * b' := by group
        _ = b * (b * b') * b' := by rw [← hcomm2]
        _ = (b * b) * (b' * b') := by group
        _ = 1 := by rw [hbb, hbb', one_mul]
    have hdaa : ((a * a' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, hda, hda']; norm_num
    have hdbb : ((b * b' : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
      rw [Units.val_mul, Matrix.det_mul, hdb, hdb']; norm_num
    have hprod : g * g' = diagGL (a * a') (b * b') := by rw [hgab, hgab', diagGL_mul]
    rw [hprod]
    exact diagGL_mem_V4 h2 (by rw [hdaa, hdbb, one_mul]) hbb2 (gl2_invol_of_det_one h2 haa2 hdaa)
  set P : Set (GL (Fin 4) F) := (E : Set (GL (Fin 4) F)) ∩ V4 F with hP
  set Q : Set (GL (Fin 4) F) := (E : Set (GL (Fin 4) F)) \ V4 F with hQ
  have hEc : (E : Set (GL (Fin 4) F)).ncard = 8 := by
    rw [← Nat.card_coe_set_eq]; exact hcard
  have hEfin : (E : Set (GL (Fin 4) F)).Finite := Set.toFinite _
  have hsum : P.ncard + Q.ncard = 8 := by
    rw [← hEc, hP, hQ]
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard _ _ hEfin
  have hPfin : P.Finite := hEfin.subset Set.inter_subset_left
  have hPV : P ⊆ V4 F := Set.inter_subset_right
  have hVfin : (V4 F).Finite := by unfold V4; exact Set.toFinite _
  have hQP : Q.ncard ≤ P.ncard := by
    by_cases hQe : Q = ∅
    · rw [hQe]; simp
    · obtain ⟨e₀, he₀E, he₀V⟩ := Set.nonempty_iff_ne_empty.2 hQe
      refine Set.ncard_le_ncard_of_injOn (fun g => e₀ * g) ?_ ?_ hPfin
      · intro g hg
        obtain ⟨hgE, hgV⟩ := hg
        exact ⟨E.mul_mem he₀E hgE, hclaim e₀ he₀E he₀V g hgE hgV⟩
      · intro g _ g' _ h
        exact mul_left_cancel h
  have hP4 : 4 ≤ P.ncard := by omega
  have hPeq : P = V4 F := Set.eq_of_subset_of_ncard_le hPV (le_trans V4_ncard_le hP4) hVfin
  have hxV : xGL F ∈ V4 F := by right; right; right; rfl
  rw [← hPeq] at hxV
  exact hxV.1

theorem e8_mem_xK [Finite F] (h2 : (2 : F) ≠ 0)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK)
    (E : Subgroup ↥M.K4) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hcard : Nat.card ↥E = 8) :
    M.xK ∈ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hex : ∃ u ∈ E, u ≠ 1 ∧ u ≠ M.xK := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ Subgroup.zpowers M.xK := by
      intro u hu
      by_cases h1 : u = 1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [hcon u hu h1]; exact Subgroup.mem_zpowers _
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, M.orderOf_xK h2] at this
    omega
  obtain ⟨u, huE, hu1, hux⟩ := hex
  have huu : u * u = 1 := by
    rw [← pow_two]
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) u huE
  have hucen : u ∉ Subgroup.center ↥M.K4 := by
    intro hc
    rcases (hcenter u).1 hc with h | h
    · exact hu1 (Subtype.ext (by simpa using h))
    · exact hux (Subtype.ext h)
  obtain ⟨k, hk⟩ := hone u huu hu1 hucen
  set E' : Subgroup ↥M.K4 := E.map (MulAut.conj k).toMonoidHom with hE'
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := IsElementaryAbelian.map _
  have hE'card : Nat.card ↥E' = 8 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj k).injective]
    exact hcard
  have hyE' : M.yK ∈ E' := ⟨u, huE, by simpa [MulAut.conj_apply] using hk⟩
  set E'' : Subgroup (GL (Fin 4) F) := E'.map M.K4.subtype with hE''
  have hE''el : CFSG.IsElementaryAbelian 2 ↥E'' := IsElementaryAbelian.map_subtype
  have hE''card : Nat.card ↥E'' = 8 := by
    rw [hE'', Subgroup.card_map_of_injective M.K4.subtype_injective]
    exact hE'card
  have hx'' := xGL_mem_of_card_eight M h2 E'' (Subgroup.map_subtype_le _) hE''el ⟨M.yK, hyE', rfl⟩
    hE''card
  obtain ⟨g, hg, hgx⟩ := hx''
  have hgxK : g = M.xK := Subtype.ext hgx
  rw [hgxK] at hg
  obtain ⟨e, heE, hex'⟩ := hg
  have h1 := Subgroup.mem_center_iff.1 M.xK_mem_center k
  have : e = M.xK := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hex'
    calc e = k⁻¹ * (k * e * k⁻¹) * k := by group
      _ = k⁻¹ * M.xK * k := by rw [hex']
      _ = k⁻¹ * (k * M.xK) := by rw [mul_assoc, ← h1]
      _ = M.xK := by group
  rw [← this]
  exact heE

theorem e4_symm_zero : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
theorem e4_symm_one : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
theorem e4_symm_two : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
theorem e4_symm_three : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide

theorem diagGL_matrix (a b : GL (Fin 2) F) (p q r s : F)
    (ha : (a : Matrix (Fin 2) (Fin 2) F) = !![p, 0; 0, q])
    (hb : (b : Matrix (Fin 2) (Fin 2) F) = !![r, 0; 0, s]) :
    ((diagGL a b : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal ![p, q, r, s] := by
  rw [coe_diagGL, ha, hb]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock, Matrix.reindex_apply,
      Matrix.submatrix_apply, e4_symm_zero, e4_symm_one, e4_symm_two, e4_symm_three]

@[expose] def negRefl (F : Type) [Field F] : GL (Fin 2) F := (-1 : GL (Fin 2) F) * dRefl F

theorem coe_negRefl : ((negRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![-1, 0; 0, 1] := by
  simp [negRefl, coe_dRefl]

theorem det_negRefl : ((negRefl F : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  simp [coe_negRefl, Matrix.det_fin_two]

theorem mul_self_eq_one_of_diag {g : GL (Fin 4) F} {v : Fin 4 → F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal v) (hv : ∀ j, v j * v j = 1) :
    g * g = 1 := by
  apply Units.ext
  rw [Units.val_mul, hg, Matrix.diagonal_mul_diagonal, Units.val_one, ← Matrix.diagonal_one]
  congr 1
  ext j
  exact hv j

theorem mul_comm_of_diag {g g' : GL (Fin 4) F} {v v' : Fin 4 → F}
    (hg : (g : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal v)
    (hg' : (g' : Matrix (Fin 4) (Fin 4) F) = Matrix.diagonal v') : g * g' = g' * g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hg, hg', Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  ext j
  exact mul_comm _ _

theorem exists_e8_model [Finite F] (h2 : (2 : F) ≠ 0) (hr : dRefl F ∈ M.U2) :
    ∃ E : Subgroup ↥M.K4, CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn1 : (-1 : F) ≠ 1 := by
    intro h
    apply h2
    linear_combination (-1 : F) * h
  have hnr : negRefl F ∈ M.U2 := M.U2.mul_mem M.neg_mem hr
  let u0 : ↥M.K4 := M.yK
  let u1 : ↥M.K4 := ⟨diagGL (negRefl F) (negRefl F),
    (M.diagGL_mem_K4_iff).2 ⟨hnr, hnr, by rw [det_negRefl]; norm_num⟩⟩
  let u2 : ↥M.K4 := ⟨diagGL (negRefl F) (dRefl F),
    (M.diagGL_mem_K4_iff).2 ⟨hnr, hr, by rw [det_negRefl, det_dRefl]; norm_num⟩⟩
  let u : Fin 3 → ↥M.K4 := ![u0, u1, u2]
  have hM0 : ((u0 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → F) := yGL_matrix
  have hM1 : ((u1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![-1, 1, -1, 1] : Fin 4 → F) :=
    diagGL_matrix _ _ _ _ _ _ coe_negRefl coe_negRefl
  have hM2 : ((u2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![-1, 1, 1, -1] : Fin 4 → F) :=
    diagGL_matrix _ _ _ _ _ _ coe_negRefl coe_dRefl
  have hM : ∀ i, ((u i : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      Matrix.diagonal (![![-1, -1, 1, 1], ![-1, 1, -1, 1], ![-1, 1, 1, -1]] i : Fin 4 → F) := by
    intro i
    fin_cases i
    · exact hM0
    · exact hM1
    · exact hM2
  have hsq : ∀ i, u i ^ 2 = 1 := by
    intro i
    rw [pow_two]
    apply Subtype.ext
    apply mul_self_eq_one_of_diag (hM i)
    intro j
    fin_cases i <;> fin_cases j <;> simp
  have hcomm : ∀ i j, Commute (u i) (u j) := by
    intro i j
    apply Subtype.ext
    exact mul_comm_of_diag (hM i) (hM j)
  have hker : ∀ a : Fin 3 → Fin 2, a ≠ 0 →
      (List.ofFn fun i => u i ^ (a i : ℕ)).prod ≠ 1 := by
    intro a ha hprod
    apply ha
    simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at hprod
    have hmat := congrArg (fun g : ↥M.K4 => ((g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) hprod
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val, hM,
      Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, OneMemClass.coe_one, Units.val_one] at hmat
    have e1 := congrFun (congrFun hmat 1) 1
    have e2 := congrFun (congrFun hmat 2) 2
    have e3 := congrFun (congrFun hmat 3) 3
    simp [Matrix.diagonal_apply_eq, Pi.pow_apply] at e1 e2 e3
    have hev : ∀ k : Fin 2, (-1 : F) ^ (k : ℕ) = 1 → k = 0 := by
      intro k hk
      fin_cases k
      · rfl
      · exfalso
        simp at hk
        exact hn1 hk
    funext i
    fin_cases i
    · simpa using hev _ e1
    · simpa using hev _ e2
    · simpa using hev _ e3
  obtain ⟨f, hf⟩ := CFSG.GH74.Filter.exists_injective_of_commuting_involutions u hsq hcomm hker
  have hel : CFSG.IsElementaryAbelian 2 ↥(⊤ : Subgroup (Fin 3 → Multiplicative (ZMod 2))) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => by
        apply Subtype.ext
        funext i
        change (a.1 i) ^ 2 = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one]
        generalize Multiplicative.toAdd (a.1 i) = z
        revert z
        decide +revert }
  refine ⟨f.range, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map]
    exact IsElementaryAbelian.map f
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, CFSG.GH74.Filter.card_pi_zmod_two]
    norm_num

theorem grpS1_of_model [Finite F] (h2 : (2 : F) ≠ 0) (hr : dRefl F ∈ M.U2) {F' : Type} [Field F']
    [Finite F'] (e2 : SL(2, F') ≃* ↥M.H2) (hsq : Nat.card F' < 4 → ∀ c : F, c ≠ 0 → c * c = 1)
    (hcenter : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔
      (g : GL (Fin 4) F) = 1 ∨ (g : GL (Fin 4) F) = xGL F)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK) : GrpS1 F' ↥M.K4 M.xK := by
  have hc' : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔ g = 1 ∨ g = M.xK := by
    intro g
    rw [hcenter]
    constructor
    · rintro (h | h)
      · left; exact Subtype.ext h
      · right; exact Subtype.ext h
    · rintro (rfl | rfl)
      · left; rfl
      · right; rfl
  exact ⟨hc', splitLike_top M h2 e2 hsq hcenter hone, fun E hE hc => e8_mem_xK M h2 hcenter hone E hE hc,
    exists_e8_model M h2 hr⟩

end Model

theorem grpS1_lin {F : Type} [Field F] [Finite F] (hF : Nat.card F % 4 = 3) :
    ∃ z : ↥(StatedSL 4 F), GrpS1 F ↥(StatedSL 4 F) z := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.2 (by omega)
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  have hsq : Nat.card F < 4 → ∀ c : F, c ≠ 0 → c * c = 1 := by
    intro hlt c hc
    have h3 : Nat.card F = 3 := by omega
    have : Fintype F := Fintype.ofFinite F
    have h4 := FiniteField.pow_card_sub_one_eq_one c hc
    rw [← Nat.card_eq_fintype_card, h3] at h4
    simpa [pow_two] using h4
  exact ⟨(ModelData.lin F).xK, grpS1_of_model (ModelData.lin F) h2 (Subgroup.mem_top _)
    (lin_sl2_equiv_H2 F) hsq (mem_center_lin_iff hF)
    (hone_of_model _ (mem_center_lin_iff hF) (fun t hT h1 hm1 => hmat_lin h2 t hT h1 hm1))⟩

theorem grpS1_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) :
    ∃ (F' : Type) (_ : Field F') (_ : Finite F'), Nat.card F' = q ∧
      ∃ z : ↥(StatedSU 4 q F), GrpS1 F' ↥(StatedSU 4 q F) z := by
  obtain ⟨p, f, hp, hchar, rfl⟩ := exists_prime_pow_of_card_eq_sq hF
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (Nat.odd_iff.2 (by omega : p ^ f % 2 = 1)).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.L5U5.two_ne_zero_of_odd_card hodd
  obtain ⟨e2⟩ := nonempty_sl2_equiv_uni_H2 hF
  have hcard1 : 1 < Nat.card F := Finite.one_lt_card
  have hr2 : 2 ≤ p ^ f := by
    by_contra hlt
    have h' : p ^ f ≤ 1 := by omega
    have : (p ^ f) ^ 2 ≤ 1 := by
      calc (p ^ f) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left h' 2
        _ = 1 := by norm_num
    omega
  have hsq : Nat.card ↥(CFSG.LieType.Steinberg.fixedSubfield F p f) < 4 →
      ∀ c : F, c ≠ 0 → c * c = 1 := fun hlt => by
    rw [CFSG.LieType.Steinberg.card_fixedSubfield hF] at hlt
    omega
  exact ⟨↥(CFSG.LieType.Steinberg.fixedSubfield F p f), inferInstance, inferInstance,
    CFSG.LieType.Steinberg.card_fixedSubfield hF,
    (ModelData.uni hF).xK, grpS1_of_model (ModelData.uni hF) h2 dRefl_mem_uni e2 hsq
      (mem_center_uni_iff hF hq)
      (hone_of_model _ (mem_center_uni_iff hF hq) (fun t hT h1 hm1 => hmat_uni hF h2 t hT h1 hm1))⟩

@[expose] def QShape1Big (Kt : Type) [Group Kt] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F % 4 = 3 ∧ 4 ≤ Nat.card F ∧
      Nonempty (Kt ≃* StatedSL 4 F)) ∨
    (∃ (q : ℕ) (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ^ 2 ∧ q % 4 = 1 ∧
      Nonempty (Kt ≃* StatedSU 4 q F))

@[expose] def QShape1Three (Kt : Type) [Group Kt] : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 3 ∧ Nonempty (Kt ≃* StatedSL 4 F)

theorem qShape1_split {Kt : Type} [Group Kt] (h : QShape1 Kt) : QShape1Big Kt ∨ QShape1Three Kt := by
  rcases h with ⟨F, _, _, hF, e⟩ | ⟨q, F, _, _, hF, hq, e⟩
  · by_cases h3 : Nat.card F = 3
    · exact Or.inr ⟨F, inferInstance, inferInstance, h3, e⟩
    · refine Or.inl (Or.inl ⟨F, inferInstance, inferInstance, hF, by omega, e⟩)
  · exact Or.inl (Or.inr ⟨q, F, inferInstance, inferInstance, hF, hq, e⟩)

theorem exists_grpS1_of_big {Kt : Type} [Group Kt] (h : QShape1Big Kt) :
    ∃ (P : Type) (_ : Group P) (F' : Type) (_ : Field F') (_ : Finite F') (z : P),
      Nonempty (Kt ≃* P) ∧ Odd (Nat.card F') ∧ 4 ≤ Nat.card F' ∧ GrpS1 F' P z := by
  rcases h with ⟨F, _, _, hF, h4, ⟨e⟩⟩ | ⟨q, F, _, _, hF, hq, ⟨e⟩⟩
  · obtain ⟨z, hz⟩ := grpS1_lin hF
    exact ⟨_, inferInstance, F, inferInstance, inferInstance, z, ⟨e⟩, Nat.odd_iff.2 (by omega),
      h4, hz⟩
  · obtain ⟨F', _, _, hF', z, hz⟩ := grpS1_uni hF hq
    refine ⟨_, inferInstance, F', inferInstance, inferInstance, z, ⟨e⟩, ?_, ?_, hz⟩
    · rw [hF']; exact Nat.odd_iff.2 (by omega)
    · have : 2 ≤ q := by
        by_contra hlt
        have : q ≤ 1 := by omega
        have : q ^ 2 ≤ 1 := by
          calc q ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left this 2
            _ = 1 := by norm_num
        have h1 : 1 < Nat.card F := Finite.one_lt_card
        omega
      rw [hF']; omega

end CFSG.GH74.Generic.BProg.B1.PilotS1

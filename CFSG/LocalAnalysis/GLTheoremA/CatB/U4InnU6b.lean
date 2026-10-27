module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnU6a
public import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily
import all CFSG.Fischer.F4

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Fischer CFSG.StandardType CFSG.Assembly
open CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo CFSG.LocalAnalysis.GLTheoremA.CatB.U52Layer
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU (reindexGL reindexGL_val mem_statedSU_of reindex_unitary)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped commutatorElement

namespace U4InnU6

variable {D : GL (Fin 6) F4} {d : Fin 6 → F4}
  (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)

@[expose] noncomputable def blkDet (c : F4) : ↥(CenD D) →* F4ˣ :=
  (Matrix.GeneralLinearGroup.det).comp (blkHom hD c)

theorem blkDet_val (c : F4) (x : ↥(CenD D)) :
    ((blkDet hD c x : F4ˣ) : F4) = (blkM d c (mM6 x.1)).det := by
  simp [blkDet, Matrix.GeneralLinearGroup.val_det_apply, blkHom_val]

@[expose] noncomputable def allDet : ↥(CenD D) →* (F4 → F4ˣ) := MonoidHom.pi (fun c => blkDet hD c)

@[expose] noncomputable def K1 : Subgroup M6 := (allDet hD).ker.map (CenD D).subtype

theorem mem_K1 {g : M6} :
    g ∈ K1 hD ↔ ∃ h : g ∈ CenD D, ∀ c : F4, (blkM d c (mM6 g)).det = 1 := by
  unfold K1
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun c => ?_⟩
    have h1 : allDet hD x = 1 := hx
    have h2 := congrFun h1 c
    have h3 := congrArg Units.val h2
    show (blkM d c (mM6 x.1)).det = 1
    rw [← blkDet_val hD c x]
    exact h3
  · rintro ⟨h, hdet⟩
    refine ⟨⟨g, h⟩, ?_, rfl⟩
    show allDet hD ⟨g, h⟩ = 1
    funext c
    apply Units.ext
    rw [show ((allDet hD ⟨g, h⟩ c : F4ˣ) : F4) = ((blkDet hD c ⟨g, h⟩ : F4ˣ) : F4) from rfl,
      blkDet_val]
    exact hdet c

theorem K1_le_CenD : K1 hD ≤ CenD D := fun g hg => ((mem_K1 hD).1 hg).1

theorem pPrimeCore_CenD_of_K1 (h : CFSG.pPrimeCore 3 ↥(K1 hD) = ⊥) :
    CFSG.pPrimeCore 3 ↥(CenD D) = ⊥ := by
  refine pPrimeCore_eq_bot_of_ker_range (allDet hD) ?_ ?_
  · exact pPrimeCore_eq_bot_of_mulEquiv
      (Subgroup.equivMapOfInjective _ (CenD D).subtype (CenD D).subtype_injective) h
  · apply pPrimeCore_eq_bot_of_exponent
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    funext c
    show (g.1 c) ^ 3 = 1
    exact F4unit_pow_three _

section Emb

variable (d) (c : F4)

theorem exists_embSU_block {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) {g : M6} (hg : g ∈ CenD D)
    (hdet : (blkM d c (mM6 g)).det = 1) :
    ∃ A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4),
      blkM d c (mM6 (embSU d c A)) = blkM d c (mM6 g) := by
  have hmem : reindexGL (Fintype.equivFin (Blk d c)) (blkHom hD c ⟨g, hg⟩) ∈
      StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4 := by
    apply mem_statedSU_of
    · rw [reindexGL_val, Matrix.det_reindex_self]
      exact hdet
    · rw [reindexGL_val]
      exact reindex_unitary _ _ (blkM_unitary d c
        (fun i j hij => CenD_zero hD ⟨g, hg⟩ hij) (M6_unitary g))
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [mM6_embSU, blkM_extMat]
  rw [reindexGL_val]
  ext i j
  simp [Matrix.reindex_apply, blkHom_val]

theorem blkM_embSU_ne {c' : F4} (hc' : c' ≠ c)
    (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) :
    blkM d c' (mM6 (embSU d c A)) = 1 := by
  ext i j
  rw [blkM, mM6_embSU, extMat_apply, dif_neg (fun h => hc' (i.2.symm.trans h.1))]
  simp [Matrix.one_apply, Subtype.ext_iff]

theorem det_blkM_embSU (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) :
    (blkM d c (mM6 (embSU d c A))).det = 1 := by
  rw [mM6_embSU, blkM_extMat, Matrix.det_reindex_self]
  exact det_eq_one_of_mem_statedSU' _ A.2

theorem embSU_mem_K1 {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) : embSU d c A ∈ K1 hD := by
  rw [mem_K1]
  refine ⟨embSU_mem_CenD d c hD A, fun c' => ?_⟩
  by_cases h : c' = c
  · subst h
    exact det_blkM_embSU d c' A
  · rw [blkM_embSU_ne d c h A, Matrix.det_one]

theorem embSU_mem_K1_of_mem_range {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) {g : M6}
    (hg : g ∈ (embSU d c).range) : g ∈ K1 hD := by
  obtain ⟨A, rfl⟩ := hg
  exact embSU_mem_K1 d c hD A

theorem embSU_comm_of_blk_one {D : GL (Fin 6) F4}
    (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d)
    (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) {r : M6} (hr : r ∈ CenD D)
    (hrc : blkM d c (mM6 r) = 1) : embSU d c A * r = r * embSU d c A := by
  have hu := embSU_mem_CenD d c hD A
  have hrc' : blkHom hD c ⟨r, hr⟩ = 1 := Units.ext (by rw [blkHom_val]; exact hrc)
  have key : (⟨embSU d c A, hu⟩ : ↥(CenD D)) * ⟨r, hr⟩ = ⟨r, hr⟩ * ⟨embSU d c A, hu⟩ := by
    apply blkPi_injective hD
    funext c'
    simp only [MonoidHom.pi_apply, map_mul]
    by_cases h : c' = c
    · subst h
      rw [hrc', mul_one, one_mul]
    · have h1 : blkHom hD c' ⟨embSU d c A, hu⟩ = 1 :=
        Units.ext (by rw [blkHom_val]; exact blkM_embSU_ne d c h A)
      rw [h1, mul_one, one_mul]
  exact congrArg Subtype.val key

end Emb

section Rc

variable {D : GL (Fin 6) F4} {d : Fin 6 → F4}
  (hD : (D : Matrix (Fin 6) (Fin 6) F4) = Matrix.diagonal d) (c : F4)

@[expose] noncomputable def Rc : Subgroup M6 :=
  K1 hD ⊓ (blkHom hD c).ker.map (CenD D).subtype

theorem mem_Rc {g : M6} :
    g ∈ Rc hD c ↔ g ∈ K1 hD ∧ ∃ h : g ∈ CenD D, blkM d c (mM6 g) = 1 := by
  unfold Rc
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨h1, x, hx, rfl⟩
    refine ⟨h1, x.2, ?_⟩
    have h2 : blkHom hD c x = 1 := hx
    have h3 := congrArg Units.val h2
    rw [blkHom_val] at h3
    simpa using h3
  · rintro ⟨h1, h, hb⟩
    refine ⟨h1, ⟨g, h⟩, ?_, rfl⟩
    show blkHom hD c ⟨g, h⟩ = 1
    exact Units.ext (by rw [blkHom_val]; simpa using hb)

theorem Rc_le_K1 : Rc hD c ≤ K1 hD := inf_le_left

theorem Rc_normal {x : M6} (hx : x ∈ K1 hD) {r : M6} (hr : r ∈ Rc hD c) :
    x * r * x⁻¹ ∈ Rc hD c := by
  obtain ⟨hr1, hrC, hrb⟩ := (mem_Rc hD c).1 hr
  have hxC := K1_le_CenD hD hx
  rw [mem_Rc]
  refine ⟨mul_mem (mul_mem hx hr1) (inv_mem hx), mul_mem (mul_mem hxC hrC) (inv_mem hxC), ?_⟩
  have hrb' : blkHom hD c ⟨r, hrC⟩ = 1 := Units.ext (by rw [blkHom_val]; simpa using hrb)
  have h1 : blkHom hD c ⟨x * r * x⁻¹, mul_mem (mul_mem hxC hrC) (inv_mem hxC)⟩ = 1 := by
    have : (⟨x * r * x⁻¹, mul_mem (mul_mem hxC hrC) (inv_mem hxC)⟩ : ↥(CenD D)) =
        ⟨x, hxC⟩ * ⟨r, hrC⟩ * ⟨x, hxC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, hrb', mul_one, mul_inv_cancel]
  have h2 := congrArg Units.val h1
  rw [blkHom_val] at h2
  simpa using h2

theorem K1_eq_mul {g : M6} (hg : g ∈ K1 hD) :
    ∃ k ∈ (embSU d c).range, ∃ r ∈ Rc hD c, g = k * r := by
  obtain ⟨hgC, hdets⟩ := (mem_K1 hD).1 hg
  obtain ⟨A, hA⟩ := exists_embSU_block d c hD hgC (hdets c)
  have hkC : embSU d c A ∈ CenD D := embSU_mem_CenD d c hD A
  have hk1 : blkHom hD c ⟨embSU d c A, hkC⟩ = blkHom hD c ⟨g, hgC⟩ :=
    Units.ext (by rw [blkHom_val, blkHom_val]; exact hA)
  have hrC : (embSU d c A)⁻¹ * g ∈ CenD D := mul_mem (inv_mem hkC) hgC
  refine ⟨embSU d c A, ⟨A, rfl⟩, (embSU d c A)⁻¹ * g, ?_, by group⟩
  rw [mem_Rc]
  refine ⟨mul_mem (inv_mem (embSU_mem_K1 d c hD A)) hg, hrC, ?_⟩
  have hr : blkHom hD c ⟨(embSU d c A)⁻¹ * g, hrC⟩ = 1 := by
    have : (⟨(embSU d c A)⁻¹ * g, hrC⟩ : ↥(CenD D)) = ⟨embSU d c A, hkC⟩⁻¹ * ⟨g, hgC⟩ := rfl
    rw [this, map_mul, map_inv, hk1, inv_mul_cancel]
  have h2 := congrArg Units.val hr
  rw [blkHom_val] at h2
  simpa using h2

theorem eq_one_of_det_eq_one_of_card_le_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι ≤ 1) {M : Matrix ι ι F4} (h : M.det = 1) : M = 1 := by
  haveI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 hι
  rcases isEmpty_or_nonempty ι with hE | ⟨⟨i₀⟩⟩
  · exact Subsingleton.elim _ _
  · haveI : Unique ι := ⟨⟨i₀⟩, fun i => Subsingleton.elim _ _⟩
    rw [Matrix.det_unique] at h
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, h, Matrix.one_apply_eq]

theorem Rc_eq_bot (hsmall : ∀ c' : F4, c' ≠ c → Fintype.card (Blk d c') ≤ 1) : Rc hD c = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  obtain ⟨hg1, hgC, hgb⟩ := (mem_Rc hD c).1 hg
  obtain ⟨-, hdets⟩ := (mem_K1 hD).1 hg1
  have : (⟨g, hgC⟩ : ↥(CenD D)) = 1 := by
    apply blkPi_injective hD
    funext c'
    simp only [MonoidHom.pi_apply, map_one, Pi.one_apply]
    apply Units.ext
    rw [blkHom_val]
    by_cases h : c' = c
    · subst h
      simpa using hgb
    · simpa using eq_one_of_det_eq_one_of_card_le_one (hsmall c' h) (hdets c')
  exact congrArg Subtype.val this

end Rc

@[expose] def sw2 : Matrix (Fin 2) (Fin 2) F4 := !![0, 1; 1, 0]

@[expose] def tw2 : Matrix (Fin 2) (Fin 2) F4 := !![F4.ω, 0; 0, F4.ω + 1]

@[expose] def tw2' : Matrix (Fin 2) (Fin 2) F4 := !![F4.ω + 1, 0; 0, F4.ω]

theorem sw2_mul : sw2 * sw2 = 1 := by decide
theorem tw2_mul : tw2 * tw2' = 1 := by decide
theorem tw2_mul' : tw2' * tw2 = 1 := by decide
theorem sw2_unitary : (sw2.map bar).transpose * sw2 = 1 := by decide
theorem tw2_unitary : (tw2.map bar).transpose * tw2 = 1 := by decide
theorem sw2_det : sw2.det = 1 := by
  rw [Matrix.det_fin_two]
  decide
theorem tw2_det : tw2.det = 1 := by
  rw [Matrix.det_fin_two]
  decide
theorem sw2_tw2_ne : sw2 * tw2 ≠ tw2 * sw2 := by decide

theorem not_comm_statedSU (n : ℕ) (hn : n = 2) :
    ¬ ∀ a b : ↥(StatedSU n (2 ^ 1) F4), a * b = b * a := by
  subst hn
  intro h
  let S : GL (Fin 2) F4 := ⟨sw2, sw2, sw2_mul, sw2_mul⟩
  let T : GL (Fin 2) F4 := ⟨tw2, tw2', tw2_mul, tw2_mul'⟩
  have hS : S ∈ StatedSU 2 (2 ^ 1) F4 := mem_statedSU_of 2 S sw2_det sw2_unitary
  have hT : T ∈ StatedSU 2 (2 ^ 1) F4 := mem_statedSU_of 2 T tw2_det tw2_unitary
  have h1 := congrArg (fun x : ↥(StatedSU 2 (2 ^ 1) F4) =>
    ((x : GL (Fin 2) F4) : Matrix (Fin 2) (Fin 2) F4)) (h ⟨S, hS⟩ ⟨T, hT⟩)
  exact sw2_tw2_ne h1

theorem card_statedSU_six (n : ℕ) (hn : n = 2) : Nat.card (StatedSU n (2 ^ 1) F4) = 6 := by
  subst hn
  have := CFSG.RankThree.SubgroupLists.card_statedSU_two (K := F4) (r := 2) (f := 1) hF4card
  rw [this]
  norm_num

theorem cover_of_card (c c₂ : F4) (hne : c ≠ c₂)
    (h6 : Fintype.card (Blk d c) + Fintype.card (Blk d c₂) = 6) :
    ∀ i : Fin 6, d i = c ∨ d i = c₂ := by
  have hinj : Function.Injective
      (Sum.elim (fun i : Blk d c => i.1) (fun i : Blk d c₂ => i.1)) := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exact absurd (a.2.symm.trans ((congrArg d hab).trans b.2)) hne
    · exact absurd (b.2.symm.trans ((congrArg d hab.symm).trans a.2)) hne
    · exact congrArg Sum.inr (Subtype.ext hab)
  have hbij : Function.Bijective
      (Sum.elim (fun i : Blk d c => i.1) (fun i : Blk d c₂ => i.1)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [Fintype.card_sum, h6]⟩
  intro i
  obtain ⟨x, hx⟩ := hbij.2 i
  rcases x with a | a
  · left
    have : a.1 = i := hx
    rw [← this]; exact a.2
  · right
    have : a.1 = i := hx
    rw [← this]; exact a.2

section Char

variable (c : F4)

theorem hid_embSU (A : ↥(StatedSU (Fintype.card (Blk d c)) (2 ^ 1) F4)) :
    ∀ i j : Fin 6, ¬ (d i = c ∧ d j = c) →
      mM6 (embSU d c A) i j = (1 : Matrix (Fin 6) (Fin 6) F4) i j := by
  intro i j h
  rw [mM6_embSU, extMat_apply, dif_neg h]

include hD in
theorem mem_range_embSU_of_id {g : M6} (hgC : g ∈ CenD D) (hdet : (blkM d c (mM6 g)).det = 1)
    (hid : ∀ i j : Fin 6, ¬ (d i = c ∧ d j = c) →
      mM6 g i j = (1 : Matrix (Fin 6) (Fin 6) F4) i j) : g ∈ (embSU d c).range := by
  obtain ⟨A, hA⟩ := exists_embSU_block d c hD hgC hdet
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply Units.ext
  show mM6 (embSU d c A) = mM6 g
  calc mM6 (embSU d c A) = extMat d c (blkM d c (mM6 (embSU d c A))) :=
        (extMat_blkM d c (hid_embSU c A)).symm
    _ = extMat d c (blkM d c (mM6 g)) := by rw [hA]
    _ = mM6 g := extMat_blkM d c hid

theorem Rc_eq_range (c₂ : F4) (hne : c ≠ c₂) (hcover : ∀ i : Fin 6, d i = c ∨ d i = c₂) :
    Rc hD c = (embSU d c₂).range := by
  ext g
  constructor
  · intro hg
    obtain ⟨hg1, hgC, hgb⟩ := (mem_Rc hD c).1 hg
    obtain ⟨-, hdets⟩ := (mem_K1 hD).1 hg1
    refine mem_range_embSU_of_id hD c₂ hgC (hdets c₂) ?_
    intro i j hij
    rcases hcover i with hi | hi <;> rcases hcover j with hj | hj
    · have := congrFun (congrFun hgb ⟨i, hi⟩) ⟨j, hj⟩
      simpa [blkM, Matrix.one_apply, Subtype.ext_iff] using this
    · have hij' : i ≠ j := fun h => hne (by rw [← hi, ← hj, h])
      rw [CenD_zero hD ⟨g, hgC⟩ (by rw [hi, hj]; exact hne), Matrix.one_apply_ne hij']
    · have hij' : i ≠ j := fun h => hne (by rw [← hi, ← hj, h]) |>.elim
      rw [CenD_zero hD ⟨g, hgC⟩ (by rw [hi, hj]; exact Ne.symm hne), Matrix.one_apply_ne hij']
    · exact absurd ⟨hi, hj⟩ hij
  · rintro ⟨A, rfl⟩
    rw [mem_Rc]
    exact ⟨embSU_mem_K1 d c₂ hD A, embSU_mem_CenD d c₂ hD A, blkM_embSU_ne d c₂ hne A⟩

end Char

end U4InnU6

end CFSG.LocalAnalysis.GLTheoremA.CatB

end

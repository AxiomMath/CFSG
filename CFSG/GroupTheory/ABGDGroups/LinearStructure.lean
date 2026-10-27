module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs
public import CFSG.CharacterTheory.Semidihedral.SemilinearOuterQuotient
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData

public noncomputable section

namespace CFSG.ABGDGroups

open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (PGammaL2 PSL2 PGL2 IsOddPrimePower pgl2FieldAut psl2FieldAut
  pGammaL2PSLRange pGammaL2PGLRange psl2FieldAut_toPGL mem_pGammaL2PSLRange_iff)
open CFSG.Semidihedral.SemilinearOuterQuotient (SquareClass pglDet pglDet_ker pglDet_field
  squareClass_card_two)
open scoped commutatorElement

section FiniteField

variable (F : Type) [Field F] [Finite F]

instance finite_ringEquiv : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) fun _ _ h => RingEquiv.ext (congrFun h)

theorem isCyclic_ringEquiv : IsCyclic (F ≃+* F) := by
  let p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  let : Algebra (ZMod p) F := ZMod.algebra F p
  exact (CFSG.Semidihedral.FixedFieldData.primeFieldAutEquiv p F).isCyclic.mpr inferInstance

variable {F}

theorem ringEquiv_mul_comm (σ τ : F ≃+* F) : σ * τ = τ * σ := by
  have := isCyclic_ringEquiv F
  exact (IsCyclic.isMulCommutative (α := F ≃+* F)).is_comm.comm σ τ

theorem ringEquiv_eq_of_sq_eq_one {σ τ : F ≃+* F} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1)
    (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  have := isCyclic_ringEquiv F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) (by norm_num)
  by_contra hne
  have hsub : ({1, σ, τ} : Finset (F ≃+* F)) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hσ
    · exact hτ
  have hcard : ({1, σ, τ} : Finset (F ≃+* F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hσ1, Ne.symm hτ1⟩
  have := Finset.card_le_card hsub
  omega

instance finite_pGL2 : Finite (PGL2 F) :=
  Finite.of_surjective _ Matrix.ProjGenLinGroup.mk_surjective

instance finite_pGammaL2 : Finite (PGammaL2 F) :=
  Finite.of_injective (fun x : PGammaL2 F => (x.left, x.right)) fun _ _ h =>
    SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

end FiniteField

section Layers

variable {F : Type} [Field F]

theorem pgl2FieldAut_mem_range_iff (σ : F ≃+* F) (g : PGL2 F) :
    pgl2FieldAut F σ g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨psl2FieldAut F σ⁻¹ y, ?_⟩
    rw [psl2FieldAut_toPGL, hy, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply]
  · rintro ⟨y, rfl⟩
    exact ⟨psl2FieldAut F σ y, psl2FieldAut_toPGL σ y⟩

theorem mul_mem_range_toPGL_iff [Finite F] (g h : PGL2 F) :
    g * h ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      (g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
        h ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) := by
  by_cases hF : IsOddPrimePower (Nat.card F)
  · exact Subgroup.mul_mem_iff_of_index_two
      (CFSG.GorensteinWalter.pgl2_psl2Range_index_eq_two F hF)
  ·
    have hchar : ringChar F = 2 := by
      by_contra hne
      apply hF
      have : Fintype F := Fintype.ofFinite F
      obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
      refine ⟨ringChar F, n, hp, hp.odd_of_ne_two hne, n.pos, ?_⟩
      rw [Nat.card_eq_fintype_card, hcard]
    have hall : ∀ x : PGL2 F,
        x ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
      intro x
      obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
      exact (CFSG.GorensteinWalter.pgl2_mk_mem_psl2_range_iff_det_isSquare A).mpr
        (FiniteField.isSquare_of_char_two hchar _)
    simp only [hall]

end Layers

@[expose] def pGammaL2FieldRange (F : Type) [Field F] : Subgroup (PGammaL2 F) :=
  (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F).range

@[expose] def pGammaL2PGLStar (F : Type) [Field F] [Finite F] : Subgroup (PGammaL2 F) where
  carrier := {x | x.right ^ 2 = 1 ∧
    (x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      x.right = 1)}
  mul_mem' := by
    rintro x y ⟨hx2, hx⟩ ⟨hy2, hy⟩
    have hcomm : Commute x.right y.right := ringEquiv_mul_comm _ _
    refine ⟨?_, ?_⟩
    · rw [SemidirectProduct.mul_right, hcomm.mul_pow, hx2, hy2, one_mul]
    · rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right, mul_mem_range_toPGL_iff,
        pgl2FieldAut_mem_range_iff, hx, hy]
      by_cases ha : x.right = 1 <;> by_cases hb : y.right = 1
      · simp [ha, hb]
      · simp [ha, hb]
      · simp [ha, hb]
      · rw [ringEquiv_eq_of_sq_eq_one hx2 hy2 ha hb, ← pow_two, hy2]
        simp
  one_mem' := ⟨one_pow 2, by simp⟩
  inv_mem' := by
    rintro x ⟨hx2, hx⟩
    refine ⟨by rw [SemidirectProduct.inv_right, inv_pow, hx2, inv_one], ?_⟩
    rw [SemidirectProduct.inv_left, SemidirectProduct.inv_right, pgl2FieldAut_mem_range_iff,
      inv_mem_iff, inv_eq_one]
    exact hx

@[expose] def linearCore {H : Type} [Group H] {F : Type} [Field F] (ι : H →* PGammaL2 F) :
    Subgroup H :=
  (pGammaL2PSLRange F).comap ι

section DetClass

def pGammaL2DetClass (F : Type) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F)) :
    PGammaL2 F →* SquareClass F :=
  SemidirectProduct.lift (pglDet F) 1 fun σ => by
    ext g
    simp [pglDet_field F hF σ g]

variable {F : Type} [Field F]

theorem mem_range_toPGL_iff_pglDet (g : PGL2 F) :
    g ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      pglDet F g = 1 := by
  rw [← pglDet_ker, MonoidHom.mem_ker]

theorem squareClass_sq (a : SquareClass F) : a ^ 2 = 1 := by
  induction a using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_square]
    exact ⟨u, sq u⟩

variable [Finite F]

theorem pGammaL2DetClass_apply (hF : IsOddPrimePower (Nat.card F)) (x : PGammaL2 F) :
    pGammaL2DetClass F hF x = pglDet F x.left := by
  change pglDet F x.left * (1 : (F ≃+* F) →* SquareClass F) x.right = _
  rw [MonoidHom.one_apply, mul_one]

theorem squareClass_eq_of_ne_one (hF : IsOddPrimePower (Nat.card F)) {a b : SquareClass F}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b :=
  CFSG.Semidihedral.SemilinearOuterQuotient.eq_of_nonone_of_card_two
    (squareClass_card_two F hF) ha hb

theorem left_mem_range_toPGL_iff (hF : IsOddPrimePower (Nat.card F)) (x : PGammaL2 F) :
    x.left ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ↔
      pGammaL2DetClass F hF x = 1 := by
  rw [pGammaL2DetClass_apply, mem_range_toPGL_iff_pglDet]

theorem pGammaL2PSLRange_eq_inf_ker (hF : IsOddPrimePower (Nat.card F)) :
    pGammaL2PSLRange F = pGammaL2PGLRange F ⊓ (pGammaL2DetClass F hF).ker := by
  ext x
  rw [Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · intro hx
    rw [mem_pGammaL2PSLRange_iff] at hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [← left_mem_range_toPGL_iff hF]
    exact ⟨y, rfl⟩
  · rintro ⟨⟨g, rfl⟩, hker⟩
    rw [← left_mem_range_toPGL_iff hF] at hker
    obtain ⟨y, hy⟩ := hker
    rw [mem_pGammaL2PSLRange_iff]
    exact ⟨y, by rw [hy]; rfl⟩

theorem pGammaL2PSLRange_normal (hF : IsOddPrimePower (Nat.card F)) :
    (pGammaL2PSLRange F).Normal := by
  rw [pGammaL2PSLRange_eq_inf_ker hF]
  infer_instance

theorem pGammaL2PGLStar_normal (hF : IsOddPrimePower (Nat.card F)) :
    (pGammaL2PGLStar F).Normal := by
  constructor
  rintro x ⟨hx2, hx⟩ g
  have hright : (g * x * g⁻¹).right = x.right := by
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [ringEquiv_mul_comm g.right x.right, mul_inv_cancel_right]
  refine ⟨by rw [hright]; exact hx2, ?_⟩
  rw [hright, left_mem_range_toPGL_iff hF, map_mul, map_mul, map_inv, mul_inv_cancel_comm,
    ← left_mem_range_toPGL_iff hF]
  exact hx

theorem commutator_mem_pGammaL2PSLRange (hF : IsOddPrimePower (Nat.card F))
    (x y : PGammaL2 F) : x * y * x⁻¹ * y⁻¹ ∈ pGammaL2PSLRange F := by
  rw [pGammaL2PSLRange_eq_inf_ker hF, Subgroup.mem_inf, MonoidHom.mem_ker]
  refine ⟨?_, ?_⟩
  · rw [pGammaL2PGLRange, SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
      map_mul, map_mul, map_mul, map_inv, map_inv, SemidirectProduct.rightHom_eq_right,
      ringEquiv_mul_comm x.right y.right]
    group
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (pGammaL2DetClass F hF x) (pGammaL2DetClass F hF y)]
    group

end DetClass

section StandardLayers

variable {F : Type} [Field F]

theorem pGammaL2PSLRange_le_pGLRange : pGammaL2PSLRange F ≤ pGammaL2PGLRange F := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

theorem pGLRange_inf_fieldRange : pGammaL2PGLRange F ⊓ pGammaL2FieldRange F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨g, hg⟩, ⟨σ, rfl⟩⟩
  have hσ : σ = 1 := by
    have h := congrArg SemidirectProduct.right hg
    simpa using h.symm
  rw [hσ, map_one]
  exact Subgroup.one_mem _

variable [Finite F]

theorem pGammaL2PSLRange_le_pGLStar : pGammaL2PSLRange F ≤ pGammaL2PGLStar F := by
  intro x hx
  rw [mem_pGammaL2PSLRange_iff] at hx
  obtain ⟨y, rfl⟩ := hx
  refine ⟨by simp, ?_⟩
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, iff_true]
  exact ⟨y, rfl⟩

theorem pGLStar_inf_pGLRange :
    pGammaL2PGLStar F ⊓ pGammaL2PGLRange F = pGammaL2PSLRange F := by
  apply le_antisymm
  · rintro x ⟨⟨-, hx⟩, ⟨g, rfl⟩⟩
    simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, iff_true] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨y, rfl⟩
  · exact le_inf pGammaL2PSLRange_le_pGLStar pGammaL2PSLRange_le_pGLRange

theorem pGLStar_inf_fieldRange : pGammaL2PGLStar F ⊓ pGammaL2FieldRange F = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨-, hx⟩, ⟨σ, rfl⟩⟩
  have hσ : σ = 1 := by
    simp only [SemidirectProduct.left_inr, SemidirectProduct.right_inr] at hx
    exact hx.mp (Subgroup.one_mem _)
  rw [hσ, map_one]
  exact Subgroup.one_mem _

@[expose] def IsStandardLayer (M : Subgroup (PGammaL2 F)) : Prop :=
  M = pGammaL2PSLRange F ∨ M = pGammaL2PGLRange F ∨ M = pGammaL2PGLStar F

theorem IsStandardLayer.pGammaL2PSLRange_le {M : Subgroup (PGammaL2 F)}
    (hM : IsStandardLayer M) : pGammaL2PSLRange F ≤ M := by
  rcases hM with rfl | rfl | rfl
  · exact le_rfl
  · exact pGammaL2PSLRange_le_pGLRange
  · exact pGammaL2PSLRange_le_pGLStar

theorem IsStandardLayer.normal (hF : IsOddPrimePower (Nat.card F)) {M : Subgroup (PGammaL2 F)}
    (hM : IsStandardLayer M) : M.Normal := by
  rcases hM with rfl | rfl | rfl
  · exact pGammaL2PSLRange_normal hF
  · infer_instance
  · exact pGammaL2PGLStar_normal hF

theorem IsStandardLayer.inf_fieldRange {M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M) :
    M ⊓ pGammaL2FieldRange F = ⊥ := by
  rcases hM with rfl | rfl | rfl
  · exact eq_bot_iff.mpr ((inf_le_inf_right _ pGammaL2PSLRange_le_pGLRange).trans
      pGLRange_inf_fieldRange.le)
  · exact pGLRange_inf_fieldRange
  · exact pGLStar_inf_fieldRange

theorem IsStandardLayer.eq_pGLRange_or_inf {M : Subgroup (PGammaL2 F)} (hM : IsStandardLayer M) :
    M = pGammaL2PGLRange F ∨ M ⊓ pGammaL2PGLRange F = pGammaL2PSLRange F := by
  rcases hM with rfl | rfl | rfl
  · exact Or.inr (inf_eq_left.mpr pGammaL2PSLRange_le_pGLRange)
  · exact Or.inl rfl
  · exact Or.inr pGLStar_inf_pGLRange

end StandardLayers

structure IsLinearDecomposition {H : Type} [Group H] {F : Type} [Field F] [Finite F]
    (ι : H →* PGammaL2 F) (L E : Subgroup H) (S : Sylow 2 H) : Prop where
  isOddPrimePower_card : IsOddPrimePower (Nat.card F)
  injective : Function.Injective ι
  normal : L.Normal
  map_eq : L.map ι = pGammaL2PSLRange F ∨ L.map ι = pGammaL2PGLRange F ∨
    L.map ι = pGammaL2PGLStar F
  isCyclic : IsCyclic E
  odd_card : Odd (Nat.card E)
  inf_eq_bot : L ⊓ E = ⊥
  sup_eq_top : L ⊔ E = ⊤
  map_le_fieldRange : E.map ι ≤ pGammaL2FieldRange F
  le_centralizer : E ≤ Subgroup.centralizer ((S : Subgroup H) : Set H)

namespace IsLinearDecomposition

variable {H : Type} [Group H] {F : Type} [Field F] [Finite F] {ι : H →* PGammaL2 F}
  {L E : Subgroup H} {S : Sylow 2 H}

theorem isStandardLayer (hd : IsLinearDecomposition ι L E S) : IsStandardLayer (L.map ι) :=
  hd.map_eq

theorem pGammaL2PSLRange_le_map (hd : IsLinearDecomposition ι L E S) :
    pGammaL2PSLRange F ≤ L.map ι :=
  hd.isStandardLayer.pGammaL2PSLRange_le

theorem pGammaL2PSLRange_le_range (hd : IsLinearDecomposition ι L E S) :
    pGammaL2PSLRange F ≤ ι.range :=
  hd.pGammaL2PSLRange_le_map.trans (Subgroup.map_le_range ι L)

theorem map_linearCore (hd : IsLinearDecomposition ι L E S) :
    (linearCore ι).map ι = pGammaL2PSLRange F := by
  rw [linearCore, Subgroup.map_comap_eq, inf_eq_right.mpr hd.pGammaL2PSLRange_le_range]

theorem linearCore_le (hd : IsLinearDecomposition ι L E S) : linearCore ι ≤ L := by
  intro x hx
  obtain ⟨l, hl, hlx⟩ := hd.pGammaL2PSLRange_le_map hx
  rwa [← hd.injective hlx]

theorem linearCore_normal (hd : IsLinearDecomposition ι L E S) : (linearCore ι).Normal := by
  have := pGammaL2PSLRange_normal hd.isOddPrimePower_card
  exact Subgroup.Normal.comap inferInstance ι

theorem nonempty_linearCore_mulEquiv (hd : IsLinearDecomposition ι L E S) :
    Nonempty (linearCore ι ≃* PSL2 F) :=
  ⟨((linearCore ι).equivMapOfInjective ι hd.injective).trans
    ((MulEquiv.subgroupCongr hd.map_linearCore).trans
      (CFSG.GorensteinWalter.pGammaL2PSLRangeEquiv F).symm)⟩

theorem isComplement' (hd : IsLinearDecomposition ι L E S) : L.IsComplement' E := by
  have := hd.normal
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (disjoint_iff.mpr hd.inf_eq_bot) ?_
  rw [← Subgroup.normal_mul, hd.sup_eq_top, Subgroup.coe_top]

theorem index_eq_card (hd : IsLinearDecomposition ι L E S) : L.index = Nat.card E :=
  hd.isComplement'.symm.index_eq_card

theorem odd_index (hd : IsLinearDecomposition ι L E S) : Odd L.index := by
  rw [hd.index_eq_card]
  exact hd.odd_card

theorem sylow_le [Finite H] (hd : IsLinearDecomposition ι L E S) (P : Sylow 2 H) :
    (P : Subgroup H) ≤ L := by
  have := hd.normal
  have h2 : IsPGroup 2 ((P : Subgroup H).map (QuotientGroup.mk' L)) :=
    P.isPGroup'.map (QuotientGroup.mk' L)
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd : Nat.card ((P : Subgroup H).map (QuotientGroup.mk' L)) ∣ L.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ L.index :=
      (dvd_pow_self 2 hk0).trans hdvd
    exact (Nat.not_even_iff_odd.mpr hd.odd_index) (even_iff_two_dvd.mpr h2dvd)
  rw [hk0, pow_zero, Subgroup.card_eq_one, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hk
  exact hk

theorem commutator_le_linearCore (hd : IsLinearDecomposition ι L E S) :
    commutator H ≤ linearCore ι := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  change ι ⁅x, y⁆ ∈ pGammaL2PSLRange F
  rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact commutator_mem_pGammaL2PSLRange hd.isOddPrimePower_card _ _

end IsLinearDecomposition

end CFSG.ABGDGroups

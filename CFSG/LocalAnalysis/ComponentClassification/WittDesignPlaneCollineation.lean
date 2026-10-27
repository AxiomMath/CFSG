module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneGeometry
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open CFSG.Fischer CFSG.Monster.B.Classical.Plane Module Matrix Equiv

universe u

@[expose] def frobF4 : F4 ≃+* F4 where
  toFun x := x * x
  invFun x := x * x
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide
  map_add' := by decide

theorem frobF4_apply (x : F4) : frobF4 x = x * x := rfl

theorem ringEquiv_F4 (σ : F4 ≃+* F4) : σ = RingEquiv.refl F4 ∨ σ = frobF4 := by
  have hq : σ F4.ω * σ F4.ω + σ F4.ω + 1 = 0 := by
    rw [← map_mul, ← map_add, ← map_one σ, ← map_add, show F4.ω * F4.ω + F4.ω + 1 = 0 by decide,
      map_zero]
  have hroots : ∀ x : F4, x * x + x + 1 = 0 → x = F4.ω ∨ x = F4.ω * F4.ω := by decide
  have hall : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω * F4.ω := by decide
  rcases hroots _ hq with h | h
  · left
    refine RingEquiv.ext fun x => ?_
    rcases hall x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simp [h]
    · simp [map_mul, h]
  · right
    refine RingEquiv.ext fun x => ?_
    rw [frobF4_apply]
    rcases hall x with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exact h
    · rw [map_mul, h]

theorem frobF4_ne_refl : frobF4 ≠ RingEquiv.refl F4 := by
  intro h
  have h1 : frobF4 F4.ω = F4.ω := by rw [h]; rfl
  rw [frobF4_apply] at h1
  revert h1
  decide

theorem card_ringEquiv_F4 : Nat.card (F4 ≃+* F4) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨RingEquiv.refl F4, frobF4, frobF4_ne_refl.symm, Set.eq_univ_of_forall fun σ => ?_⟩
  rcases ringEquiv_F4 σ with rfl | rfl
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

theorem pow_three_F4 : ∀ x : F4, x ≠ 0 → x ^ 3 = 1 := by decide

@[expose] def slin (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) : Vec3 :=
  (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ (σ ∘ v)

theorem comp_mulVec (σ : F4 ≃+* F4) (M : Matrix (Fin 3) (Fin 3) F4) (v : Vec3) :
    σ ∘ (M *ᵥ v) = M.map σ *ᵥ (σ ∘ v) := by
  funext i
  exact RingHom.map_mulVec (σ : F4 →+* F4) M v i

theorem slin_slin (A B : GL (Fin 3) F4) (σ τ : F4 ≃+* F4) (v : Vec3) :
    slin A σ (slin B τ v) =
      slin (A * GeneralLinearGroup.map (σ : F4 →+* F4) B) (τ.trans σ) v := by
  simp only [slin]
  rw [comp_mulVec, Units.val_mul, ← mulVec_mulVec]
  rfl

theorem slin_refl (A : GL (Fin 3) F4) (v : Vec3) :
    slin A (RingEquiv.refl F4) v = (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ v := rfl

theorem slin_one (v : Vec3) : slin 1 (RingEquiv.refl F4) v = v := by
  rw [slin_refl, Units.val_one, one_mulVec]

theorem slin_add (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v w : Vec3) :
    slin A σ (v + w) = slin A σ v + slin A σ w := by
  have : σ ∘ (v + w) = σ ∘ v + σ ∘ w := by
    funext i
    simp
  rw [slin, slin, slin, this, mulVec_add]

theorem slin_smul (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (c : F4) (v : Vec3) :
    slin A σ (c • v) = σ c • slin A σ v := by
  have : σ ∘ (c • v) = σ c • (σ ∘ v) := by
    funext i
    simp
  rw [slin, slin, this, mulVec_smul]

theorem slin_zero (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) : slin A σ 0 = 0 := by
  have := slin_smul A σ 0 0
  rwa [zero_smul, map_zero, zero_smul] at this

@[expose] def slinInvMat (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) : GL (Fin 3) F4 :=
  GeneralLinearGroup.map (σ.symm : F4 →+* F4) A⁻¹

theorem slin_inv_left (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) :
    slin (slinInvMat A σ) σ.symm (slin A σ v) = v := by
  have hA : slinInvMat A σ * GeneralLinearGroup.map (σ.symm : F4 →+* F4) A = 1 := by
    rw [slinInvMat, ← map_mul, inv_mul_cancel, map_one]
  rw [slin_slin, hA, RingEquiv.self_trans_symm, slin_one]

theorem slin_inv_right (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) :
    slin A σ (slin (slinInvMat A σ) σ.symm v) = v := by
  have hmap : GeneralLinearGroup.map (σ : F4 →+* F4) (slinInvMat A σ) = A⁻¹ := by
    ext i j
    simp only [slinInvMat, GeneralLinearGroup.map_apply, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
  rw [slin_slin, hmap, mul_inv_cancel, RingEquiv.symm_trans_self, slin_one]

@[expose] def slinPerm (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) : Perm Vec3 where
  toFun := slin A σ
  invFun := slin (slinInvMat A σ) σ.symm
  left_inv := slin_inv_left A σ
  right_inv := slin_inv_right A σ

theorem slinPerm_apply (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) (v : Vec3) :
    slinPerm A σ v = slin A σ v := rfl

@[expose] def GammaL3 : Subgroup (Perm Vec3) where
  carrier := {g | ∃ (A : GL (Fin 3) F4) (σ : F4 ≃+* F4), ∀ v, g v = slin A σ v}
  one_mem' := ⟨1, RingEquiv.refl F4, fun v => (slin_one v).symm⟩
  mul_mem' := by
    rintro g h ⟨A, σ, hA⟩ ⟨B, τ, hB⟩
    exact ⟨_, _, fun v => by rw [Perm.mul_apply, hB, hA, slin_slin]⟩
  inv_mem' := by
    rintro g ⟨A, σ, hA⟩
    refine ⟨slinInvMat A σ, σ.symm, fun v => ?_⟩
    have hg : g = slinPerm A σ := Equiv.ext hA
    rw [hg]
    rfl

theorem mem_GammaL3 {g : Perm Vec3} :
    g ∈ GammaL3 ↔ ∃ (A : GL (Fin 3) F4) (σ : F4 ≃+* F4), ∀ v, g v = slin A σ v := Iff.rfl

theorem slinPerm_mem (A : GL (Fin 3) F4) (σ : F4 ≃+* F4) : slinPerm A σ ∈ GammaL3 :=
  ⟨A, σ, fun _ => rfl⟩

theorem mulVec_apply_three (M : Matrix (Fin 3) (Fin 3) F4) (v : Vec3) (i : Fin 3) :
    (M *ᵥ v) i = M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 := by
  simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem slin_injective {A B : GL (Fin 3) F4} {σ τ : F4 ≃+* F4}
    (h : ∀ v, slin A σ v = slin B τ v) : A = B ∧ σ = τ := by
  have hAB : A = B := by
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    have hs : ∀ ρ : F4 ≃+* F4, ρ ∘ (Pi.single j 1 : Vec3) = Pi.single j 1 := fun ρ => by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    rw [slin, slin, hs, hs, mulVec_single_one, mulVec_single_one] at this
    exact this
  subst hAB
  refine ⟨rfl, RingEquiv.ext fun x => ?_⟩
  have hv := h (Pi.single 0 x)
  rw [slin, slin] at hv
  have hinj := congrArg (fun w => ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) hv
  simp only [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at hinj
  simpa using congrFun hinj 0

@[expose] def imgSub (g : GammaL3) (W : Submodule F4 Vec3) : Submodule F4 Vec3 where
  carrier := (g : Perm Vec3) '' W
  add_mem' := by
    obtain ⟨A, σ, hA⟩ := g.2
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, W.add_mem hx hy, by rw [hA, hA, hA, slin_add]⟩
  zero_mem' := by
    obtain ⟨A, σ, hA⟩ := g.2
    exact ⟨0, W.zero_mem, by rw [hA, slin_zero]⟩
  smul_mem' := by
    obtain ⟨A, σ, hA⟩ := g.2
    rintro c _ ⟨x, hx, rfl⟩
    exact ⟨σ.symm c • x, W.smul_mem _ hx, by rw [hA, hA, slin_smul, RingEquiv.apply_symm_apply]⟩

theorem mem_imgSub {g : GammaL3} {W : Submodule F4 Vec3} {v : Vec3} :
    v ∈ imgSub g W ↔ ∃ x ∈ W, (g : Perm Vec3) x = v := Iff.rfl

theorem imgSub_mul (g h : GammaL3) (W : Submodule F4 Vec3) :
    imgSub (g * h) W = imgSub g (imgSub h W) := by
  ext v
  simp only [mem_imgSub]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(h : Perm Vec3) x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem imgSub_one (W : Submodule F4 Vec3) : imgSub 1 W = W := by
  ext v
  simp only [mem_imgSub]
  exact ⟨fun ⟨x, hx, e⟩ => e ▸ hx, fun hv => ⟨v, hv, rfl⟩⟩

theorem imgSub_le_imgSub_iff (g : GammaL3) (W W' : Submodule F4 Vec3) :
    imgSub g W ≤ imgSub g W' ↔ W ≤ W' := by
  change (g : Perm Vec3) '' W ⊆ (g : Perm Vec3) '' W' ↔ W ≤ W'
  rw [Set.image_subset_image_iff (g : Perm Vec3).injective, SetLike.coe_subset_coe]

theorem natCard_submodule (W : Submodule F4 Vec3) : Nat.card W = 4 ^ finrank F4 W := by
  rw [Module.natCard_eq_pow_finrank (K := F4), Nat.card_eq_fintype_card, F4.card]

theorem finrank_imgSub (g : GammaL3) (W : Submodule F4 Vec3) :
    finrank F4 (imgSub g W) = finrank F4 W := by
  have h : Nat.card (imgSub g W) = Nat.card W :=
    Nat.card_image_of_injective (g : Perm Vec3).injective (W : Set Vec3)
  rw [natCard_submodule, natCard_submodule] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 4) h

@[expose] def rhoFun (g : GammaL3) (p : PG24Point) : PG24Point :=
  ⟨imgSub g p, (finrank_imgSub g p).trans p.2⟩

theorem rhoFun_inv_rhoFun (g : GammaL3) (p : PG24Point) : rhoFun g⁻¹ (rhoFun g p) = p :=
  Subtype.ext (show imgSub g⁻¹ (imgSub g p) = p by
    rw [← imgSub_mul, inv_mul_cancel, imgSub_one])

@[expose] def rhoGL : GammaL3 →* Perm PG24Point where
  toFun g :=
    { toFun := rhoFun g
      invFun := rhoFun g⁻¹
      left_inv := rhoFun_inv_rhoFun g
      right_inv := fun p => by simpa using rhoFun_inv_rhoFun g⁻¹ p }
  map_one' := Equiv.ext fun p => Subtype.ext (imgSub_one p)
  map_mul' g h := Equiv.ext fun p => Subtype.ext (imgSub_mul g h p)

theorem coe_rhoGL_apply (g : GammaL3) (p : PG24Point) :
    ((rhoGL g p : PG24Point) : Submodule F4 Vec3) = imgSub g p := rfl

theorem coe_rhoGL_symm_apply (g : GammaL3) (p : PG24Point) :
    (((rhoGL g).symm p : PG24Point) : Submodule F4 Vec3) = imgSub g⁻¹ p := rfl

theorem map_rhoGL_line (g : GammaL3) (W : Submodule F4 Vec3) :
    (Finset.univ.filter fun p : PG24Point => (p : Submodule F4 Vec3) ≤ W).map
        (rhoGL g).toEmbedding =
      Finset.univ.filter fun p : PG24Point => (p : Submodule F4 Vec3) ≤ imgSub g W := by
  ext q
  rw [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_filter, coe_rhoGL_symm_apply,
    ← imgSub_le_imgSub_iff g, ← imgSub_mul, mul_inv_cancel, imgSub_one]
  simp

theorem map_rhoGL_mem {g : GammaL3} {B : Finset PG24Point} (hB : B ∈ PG24Lines) :
    B.map (rhoGL g).toEmbedding ∈ PG24Lines := by
  obtain ⟨W, -, rfl⟩ := Finset.mem_image.1 hB
  rw [map_rhoGL_line]
  exact Finset.mem_image.2 ⟨⟨imgSub g W, (finrank_imgSub g W).trans W.2⟩, Finset.mem_univ _, rfl⟩

theorem rhoGL_mem_blockAut (g : GammaL3) : rhoGL g ∈ blockAut PG24Lines := by
  intro B
  refine ⟨fun hB => ?_, map_rhoGL_mem⟩
  have h := map_rhoGL_mem (g := g⁻¹) hB
  rwa [← map_perm_mul', ← map_mul, inv_mul_cancel, map_one,
    show (1 : Perm PG24Point).toEmbedding = Function.Embedding.refl _ from rfl,
    Finset.map_refl] at h

theorem range_rhoGL_le : rhoGL.range ≤ blockAut PG24Lines := by
  rintro _ ⟨g, rfl⟩
  exact rhoGL_mem_blockAut g

theorem conj_mem_lineAut {σ : Perm PG24Point} (hσ : σ ∈ blockAut PG24Lines) :
    ptEquiv.trans (σ.trans ptEquiv.symm) ∈ lineAut := by
  intro a
  have h1 : (projLine a).map ptEquiv.toEmbedding ∈ PG24Lines := by
    rw [← image_ptEquiv_lines]
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  have h2 := (hσ _).2 h1
  rw [← image_ptEquiv_lines] at h2
  obtain ⟨_, hL, e⟩ := Finset.mem_image.1 h2
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hL
  refine ⟨b, ?_⟩
  rw [Equiv.trans_toEmbedding, Equiv.trans_toEmbedding, ← Finset.map_map, ← Finset.map_map, ← e,
    Finset.map_map, ← Equiv.trans_toEmbedding, Equiv.self_trans_symm]
  exact Finset.map_refl

theorem card_blockAut_le : Nat.card (blockAut PG24Lines) ≤ 120960 := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun σ => (⟨ptEquiv.trans (σ.1.trans ptEquiv.symm), conj_mem_lineAut σ.2⟩ : lineAut)) ?_)
    card_lineAut_le
  intro σ τ h
  have h' := congrArg (fun x : lineAut => (x : Perm (Fin 21))) h
  refine Subtype.ext (Equiv.ext fun p => ?_)
  have := congrArg (fun f : Perm (Fin 21) => ptEquiv (f (ptEquiv.symm p))) h'
  simpa using this

theorem card_GL : Nat.card (GL (Fin 3) F4) = 181440 := by
  rw [card_GL_field, F4.card]
  decide

@[expose] def slinGamma (x : GL (Fin 3) F4 × (F4 ≃+* F4)) : GammaL3 :=
  ⟨slinPerm x.1 x.2, slinPerm_mem x.1 x.2⟩

theorem slinGamma_bijective : Function.Bijective slinGamma := by
  refine ⟨fun x y h => ?_, fun g => ?_⟩
  · have h' := slin_injective (A := x.1) (B := y.1) (σ := x.2) (τ := y.2) fun v =>
      congrArg (fun g : GammaL3 => (g : Perm Vec3) v) h
    exact Prod.ext h'.1 h'.2
  · obtain ⟨A, σ, hA⟩ := g.2
    exact ⟨(A, σ), Subtype.ext (Equiv.ext fun v => (hA v).symm)⟩

theorem card_GammaL3 : Nat.card GammaL3 = Nat.card (GL (Fin 3) F4) * 2 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ slinGamma_bijective), Nat.card_prod,
    card_ringEquiv_F4]

theorem exists_smul_of_mem_ker {g : GammaL3} (hg : g ∈ rhoGL.ker) {v : Vec3} (hv : v ≠ 0) :
    ∃ c : F4, (g : Perm Vec3) v = c • v := by
  have hp : finrank F4 (Submodule.span F4 {v}) = 1 := finrank_span_singleton hv
  have h : imgSub g (Submodule.span F4 {v}) = Submodule.span F4 {v} :=
    congrArg (fun σ : Perm PG24Point => ((σ ⟨_, hp⟩ : PG24Point) : Submodule F4 Vec3))
      (MonoidHom.mem_ker.1 hg)
  have hmem : (g : Perm Vec3) v ∈ imgSub g (Submodule.span F4 {v}) :=
    ⟨v, Submodule.mem_span_singleton_self v, rfl⟩
  rw [h, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

theorem mem_ker_rhoGL (g : GammaL3) :
    g ∈ rhoGL.ker ↔ ∃ c : F4ˣ, ∀ v, (g : Perm Vec3) v = (c : F4) • v := by
  constructor
  · intro hg
    obtain ⟨A, σ, hA⟩ := g.2
    set M : Matrix (Fin 3) (Fin 3) F4 := A.val with hM
    have key : ∀ v : Vec3, v ≠ 0 → ∃ c : F4, M *ᵥ (σ ∘ v) = c • v := fun v hv => by
      obtain ⟨c, hc⟩ := exists_smul_of_mem_ker hg hv
      exact ⟨c, (hA v).symm.trans hc⟩
    have hσ0 : σ 0 = 0 := map_zero σ
    have hσ1 : σ 1 = 1 := map_one σ
    have comp3 : ∀ a b c : F4, σ ∘ ![a, b, c] = ![σ a, σ b, σ c] := fun a b c => by
      funext i
      fin_cases i <;> rfl
    have ev : ∀ a b c : F4, ![a, b, c] ≠ 0 → ∃ t : F4,
        M 0 0 * σ a + M 0 1 * σ b + M 0 2 * σ c = t * a ∧
        M 1 0 * σ a + M 1 1 * σ b + M 1 2 * σ c = t * b ∧
        M 2 0 * σ a + M 2 1 * σ b + M 2 2 * σ c = t * c := fun a b c hv => by
      obtain ⟨t, ht⟩ := key _ hv
      rw [comp3] at ht
      refine ⟨t, ?_, ?_, ?_⟩
      · simpa [mulVec_apply_three] using congrFun ht 0
      · simpa [mulVec_apply_three] using congrFun ht 1
      · simpa [mulVec_apply_three] using congrFun ht 2
    have ne : ∀ a b c : F4, a ≠ 0 → ![a, b, c] ≠ 0 := fun a b c ha e =>
      ha (by simpa using congrFun e 0)
    have ne' : ∀ b c : F4, b ≠ 0 → ![0, b, c] ≠ 0 := fun b c hb e =>
      hb (by simpa using congrFun e 1)
    have ne'' : ∀ c : F4, c ≠ 0 → ![0, 0, c] ≠ 0 := fun c hc e =>
      hc (by simpa using congrFun e 2)
    have one_ne : (1 : F4) ≠ 0 := one_ne_zero
    obtain ⟨t₀, h00, h10, h20⟩ := ev 1 0 0 (ne _ _ _ one_ne)
    obtain ⟨t₁, h01, h11, h21⟩ := ev 0 1 0 (ne' _ _ one_ne)
    obtain ⟨t₂, h02, h12, h22⟩ := ev 0 0 1 (ne'' _ one_ne)
    obtain ⟨t₃, h03, h13, -⟩ := ev 1 1 0 (ne _ _ _ one_ne)
    obtain ⟨t₄, h04, -, h24⟩ := ev 1 0 1 (ne _ _ _ one_ne)
    obtain ⟨t₅, h05, h15, -⟩ := ev 1 F4.ω 0 (ne _ _ _ one_ne)
    simp only [hσ0, hσ1, mul_zero, mul_one, add_zero, zero_add] at h00 h10 h20 h01 h11 h21
    simp only [hσ0, hσ1, mul_zero, mul_one, add_zero, zero_add] at h02 h12 h22 h03 h13 h04
    simp only [hσ0, hσ1, mul_zero, mul_one, add_zero] at h24 h05 h15
    have e11 : M 1 1 = M 0 0 := by linear_combination h13 - h03 - h10 + h01
    have e22 : M 2 2 = M 0 0 := by linear_combination h24 - h04 - h20 + h02
    have hne : M 0 0 ≠ 0 := by
      intro h0
      have hz : M = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h10, h20, h01, h21, h02, h12, e11, e22, h0]
      have h1 := A.mul_inv
      change M * _ = 1 at h1
      rw [hz, zero_mul] at h1
      have := congrFun (congrFun h1 0) 0
      simp at this
    have hω : σ F4.ω = F4.ω := by
      have h5 : M 0 0 * σ F4.ω = M 0 0 * F4.ω := by
        linear_combination h15 - h10 - σ F4.ω * e11 - F4.ω * h05 + F4.ω * σ F4.ω * h01
      exact mul_left_cancel₀ hne h5
    have hσ : σ = RingEquiv.refl F4 := by
      rcases ringEquiv_F4 σ with h | h
      · exact h
      · exfalso
        rw [h, frobF4_apply] at hω
        revert hω
        decide
    refine ⟨Units.mk0 (M 0 0) hne, fun v => ?_⟩
    rw [hA, hσ, slin_refl]
    change M *ᵥ v = _
    funext i
    simp only [Units.val_mk0, Pi.smul_apply, smul_eq_mul, mulVec_apply_three]
    fin_cases i <;> simp [h10, h20, h01, h21, h02, h12, e11, e22]
  · rintro ⟨c, hc⟩
    refine MonoidHom.mem_ker.2 (Equiv.ext fun p => Subtype.ext ?_)
    change imgSub g p = p
    ext v
    rw [mem_imgSub]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hc]
      exact p.1.smul_mem _ hx
    · intro hv
      refine ⟨((c⁻¹ : F4ˣ) : F4) • v, p.1.smul_mem _ hv, ?_⟩
      rw [hc, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

@[expose] def scalarGamma (c : F4ˣ) : GammaL3 :=
  ⟨slinPerm (GeneralLinearGroup.scalar (Fin 3) c) (RingEquiv.refl F4), slinPerm_mem _ _⟩

theorem scalarGamma_apply (c : F4ˣ) (v : Vec3) :
    ((scalarGamma c : GammaL3) : Perm Vec3) v = (c : F4) • v := by
  change slin _ _ v = _
  rw [slin_refl, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem card_ker_rhoGL : Nat.card rhoGL.ker = 3 := by
  have hbij : Function.Bijective fun c : F4ˣ =>
      (⟨scalarGamma c, (mem_ker_rhoGL _).2 ⟨c, scalarGamma_apply c⟩⟩ : rhoGL.ker) := by
    refine ⟨fun c d h => ?_, fun g => ?_⟩
    · have h1 := congrArg (fun g : rhoGL.ker => ((g : GammaL3) : Perm Vec3) (Pi.single 0 1)) h
      simp only [scalarGamma_apply] at h1
      have h2 := congrFun h1 0
      simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
      exact Units.ext h2
    · obtain ⟨c, hc⟩ := (mem_ker_rhoGL g.1).1 g.2
      exact ⟨c, Subtype.ext (Subtype.ext (Equiv.ext fun v => by rw [scalarGamma_apply, hc]))⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_units, Nat.card_eq_fintype_card,
    F4.card]

theorem card_range_rhoGL : Nat.card rhoGL.range = 120960 := by
  have h := Subgroup.card_mul_index rhoGL.ker
  rw [Subgroup.index_ker, card_ker_rhoGL, card_GammaL3, card_GL] at h
  omega

theorem blockAut_eq_range_rhoGL : blockAut PG24Lines = rhoGL.range :=
  (Subgroup.eq_of_le_of_card_ge range_rhoGL_le
    (by rw [card_range_rhoGL]; exact card_blockAut_le)).symm

theorem card_blockAut : Nat.card (blockAut PG24Lines) = 120960 := by
  rw [blockAut_eq_range_rhoGL, card_range_rhoGL]

@[expose] def slHom : Matrix.SpecialLinearGroup (Fin 3) F4 →* GammaL3 where
  toFun A := ⟨slinPerm (Matrix.SpecialLinearGroup.toGL A) (RingEquiv.refl F4), slinPerm_mem _ _⟩
  map_one' := Subtype.ext (Equiv.ext fun v => by
    change slin _ _ v = v
    rw [map_one, slin_one])
  map_mul' A B := Subtype.ext (Equiv.ext fun v => by
    change slin _ _ v = slin _ _ (slin _ _ v)
    rw [slin_refl, slin_refl, slin_refl, map_mul, Units.val_mul, mulVec_mulVec])

theorem slHom_apply (A : Matrix.SpecialLinearGroup (Fin 3) F4) (v : Vec3) :
    ((slHom A : GammaL3) : Perm Vec3) v = (A : Matrix (Fin 3) (Fin 3) F4) *ᵥ v := rfl

theorem ker_rhoGL_comp_slHom :
    (rhoGL.comp slHom).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F4) := by
  ext A
  rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
  change slHom A ∈ rhoGL.ker ↔ _
  rw [mem_ker_rhoGL]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, pow_three_F4 _ c.ne_zero, ?_⟩
    ext i j
    have h := congrFun (hc (Pi.single j 1)) i
    rw [slHom_apply, mulVec_single_one, col_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at h
    rw [h, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  · rintro ⟨r, hr, hA⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      norm_num at hr
    refine ⟨Units.mk0 r hr0, fun v => ?_⟩
    rw [slHom_apply, ← hA, Units.val_mk0, Matrix.scalar_apply]
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl

theorem card_SL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F4) = 60480 := by
  rw [card_SL_field, F4.card, Fin.prod_univ_three]
  norm_num

@[expose] def scalarSL (c : F4ˣ) : Matrix.SpecialLinearGroup (Fin 3) F4 :=
  ⟨Matrix.scalar (Fin 3) (c : F4), by
    rw [Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_three_F4 _ c.ne_zero⟩

theorem card_ker_rhoGL_comp_slHom : Nat.card (rhoGL.comp slHom).ker = 3 := by
  have hmem : ∀ c : F4ˣ, scalarSL c ∈ (rhoGL.comp slHom).ker := fun c => by
    rw [ker_rhoGL_comp_slHom, Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
    exact ⟨c, pow_three_F4 _ c.ne_zero, rfl⟩
  have hbij : Function.Bijective fun c : F4ˣ =>
      (⟨scalarSL c, hmem c⟩ : (rhoGL.comp slHom).ker) := by
    refine ⟨fun c d h => ?_, fun A => ?_⟩
    · have h1 := congrArg (fun A : (rhoGL.comp slHom).ker =>
        ((A : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) 0 0) h
      simp only [scalarSL, Matrix.scalar_apply, diagonal_apply_eq] at h1
      exact Units.ext h1
    · have hA : (A : Matrix.SpecialLinearGroup (Fin 3) F4) ∈ Subgroup.center _ := by
        rw [← ker_rhoGL_comp_slHom]
        exact A.2
      rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin] at hA
      obtain ⟨r, hr, hrA⟩ := hA
      have hr0 : r ≠ 0 := by
        rintro rfl
        norm_num at hr
      exact ⟨Units.mk0 r hr0, Subtype.ext (Subtype.ext hrA)⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_units, Nat.card_eq_fintype_card,
    F4.card]

theorem card_range_rhoGL_comp_slHom : Nat.card (rhoGL.comp slHom).range = 20160 := by
  have h := Subgroup.card_mul_index (rhoGL.comp slHom).ker
  rw [Subgroup.index_ker, card_ker_rhoGL_comp_slHom, card_SL] at h
  omega

@[expose] def rangeSLEquivPSL :
    (rhoGL.comp slHom).range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4 :=
  (QuotientGroup.quotientKerEquivRange (rhoGL.comp slHom)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq ker_rhoGL_comp_slHom)

theorem slHom_conj (h : GammaL3) (a : Matrix.SpecialLinearGroup (Fin 3) F4) :
    ∃ b : Matrix.SpecialLinearGroup (Fin 3) F4, h * slHom a * h⁻¹ = slHom b := by
  obtain ⟨C, σ, hC⟩ := h.2
  set X : GL (Fin 3) F4 :=
    GeneralLinearGroup.map (σ : F4 →+* F4) (Matrix.SpecialLinearGroup.toGL a) with hX
  set B : GL (Fin 3) F4 := C * X * C⁻¹ with hB
  have hdetX : (X : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    change ((σ : F4 →+* F4).mapMatrix (a : Matrix (Fin 3) (Fin 3) F4)).det = 1
    rw [← RingHom.map_det, a.2, map_one]
  have hdet : (B : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    rw [hB, Units.val_mul, Units.val_mul, det_mul, det_mul, hdetX, mul_one, ← det_mul,
      Units.mul_inv, det_one]
  refine ⟨⟨B, hdet⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  have hBC : (B : Matrix (Fin 3) (Fin 3) F4) * C = C * X := by
    rw [← Units.val_mul, ← Units.val_mul, hB, inv_mul_cancel_right]
  refine Subtype.ext (Equiv.ext fun w => ?_)
  change (h : Perm Vec3) ((a : Matrix (Fin 3) (Fin 3) F4) *ᵥ w) =
    (B : Matrix (Fin 3) (Fin 3) F4) *ᵥ ((h : Perm Vec3) w)
  rw [hC, hC, slin, slin, comp_mulVec, mulVec_mulVec, mulVec_mulVec, hBC]
  rfl

theorem range_rhoGL_comp_slHom_le : (rhoGL.comp slHom).range ≤ blockAut PG24Lines := by
  rintro _ ⟨a, rfl⟩
  exact rhoGL_mem_blockAut _

theorem range_rhoGL_comp_slHom_normal :
    ((rhoGL.comp slHom).range.subgroupOf (blockAut PG24Lines)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨a, ha⟩ := hn
  have hg : (g : Perm PG24Point) ∈ rhoGL.range := blockAut_eq_range_rhoGL ▸ g.2
  obtain ⟨h, hh⟩ := hg
  obtain ⟨b, hb⟩ := slHom_conj h a
  refine ⟨b, ?_⟩
  change rhoGL (slHom b) = _
  rw [← hb, map_mul, map_mul, map_inv, hh]
  change _ = (g : Perm PG24Point) * (n : Perm PG24Point) * (g : Perm PG24Point)⁻¹
  rw [← ha]
  rfl

theorem relIndex_range_rhoGL_comp_slHom :
    (rhoGL.comp slHom).range.relIndex (blockAut PG24Lines) = 6 := by
  have h := Subgroup.card_mul_index ((rhoGL.comp slHom).range.subgroupOf (blockAut PG24Lines))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe range_rhoGL_comp_slHom_le).toEquiv,
    card_range_rhoGL_comp_slHom, card_blockAut] at h
  rw [Subgroup.relIndex]
  omega

theorem IsSteinerPlane.card_inter {P : Type*} [Fintype P] [DecidableEq P]
    {𝓛 : Finset (Finset P)} (h : IsSteinerPlane 𝓛) {L M : Finset P} (hL : L ∈ 𝓛) (hM : M ∈ 𝓛)
    (hLM : L ≠ M) : (L ∩ M).card = 1 := by
  obtain ⟨x, hxL, hxM⟩ := h.exists_mem_inter hL hM
  rw [Finset.card_eq_one]
  refine ⟨x, Finset.eq_singleton_iff_unique_mem.2 ⟨Finset.mem_inter.2 ⟨hxL, hxM⟩, fun y hy => ?_⟩⟩
  rw [Finset.mem_inter] at hy
  by_contra hyx
  exact hLM (h.eq_of_mem_of_mem hL hM hyx hy.1 hxL hy.2 hxM)

theorem pg24_unique_and_collineation_group :
    (∀ {P : Type u} [Fintype P] [DecidableEq P] (𝓛 : Finset (Finset P)), IsSteinerPlane 𝓛 →
      𝓛.card = 21 ∧ (∀ p, (linesThru 𝓛 p).card = 5) ∧
        ∀ L ∈ 𝓛, ∀ M ∈ 𝓛, L ≠ M → (L ∩ M).card = 1) ∧
    IsSteinerPlane PG24Lines ∧
    (∀ σ : F4 ≃+* F4, σ = RingEquiv.refl F4 ∨ σ = frobF4) ∧
    (∀ {P : Type u} [Fintype P] [DecidableEq P] (𝓛 : Finset (Finset P)), IsSteinerPlane 𝓛 →
      ∃ e : P ≃ PG24Point, ∀ L : Finset P, L ∈ 𝓛 ↔ L.map e.toEmbedding ∈ PG24Lines) ∧
    blockAut PG24Lines = rhoGL.range ∧
    (∀ g : GammaL3, g ∈ rhoGL.ker ↔ ∃ c : F4ˣ, ∀ v, (g : Perm Vec3) v = (c : F4) • v) ∧
    Nat.card rhoGL.ker = 3 ∧
    Nat.card GammaL3 = Nat.card (GL (Fin 3) F4) * 2 ∧ Nat.card (GL (Fin 3) F4) = 181440 ∧
    Nat.card (blockAut PG24Lines) = 120960 ∧
    Nonempty ((rhoGL.comp slHom).range ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F4) ∧
    Nat.card (rhoGL.comp slHom).range = 20160 ∧
    (rhoGL.comp slHom).range ≤ blockAut PG24Lines ∧
    ((rhoGL.comp slHom).range.subgroupOf (blockAut PG24Lines)).Normal ∧
    (rhoGL.comp slHom).range.relIndex (blockAut PG24Lines) = 6 :=
  ⟨fun _ h => ⟨h.card_lines, h.card_linesThru, fun _ hL _ hM hLM => h.card_inter hL hM hLM⟩,
    isSteinerPlane_PG24, ringEquiv_F4, fun _ h => iso_PG24 h, blockAut_eq_range_rhoGL,
    mem_ker_rhoGL, card_ker_rhoGL, card_GammaL3, card_GL, card_blockAut, ⟨rangeSLEquivPSL⟩,
    card_range_rhoGL_comp_slHom, range_rhoGL_comp_slHom_le, range_rhoGL_comp_slHom_normal,
    relIndex_range_rhoGL_comp_slHom⟩

end CFSG.ComponentClassification.WittDesign

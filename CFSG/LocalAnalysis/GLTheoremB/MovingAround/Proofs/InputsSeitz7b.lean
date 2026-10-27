module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsSeitz7
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1310r2

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz7

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (Seitz2313Even seitz2313Even_holds
  seitzHyperGamma_eq_top_of_seitz2313Even)
open GL83.CompFam
open scoped Pointwise

set_option linter.unusedSectionVars false

section HyperInvDef

@[expose] def HyperInv (G : Type*) [Group G] : Prop :=
  ∀ (E : Subgroup G) (k : ℕ), IsElemAbelian 3 E → Nat.card E = 3 ^ k → 1 ≤ k →
    ∃ H : Subgroup G, H ≤ E ∧ Nat.card E = 3 * Nat.card H ∧
      ∃ t : G, t ≠ 1 ∧ t * t = 1 ∧ ∀ x ∈ H, x * t = t * x

theorem HyperInv.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (h : HyperInv G') :
    HyperInv G := by
  intro E k hE hEc hk
  obtain ⟨H, hHE, hHc, t, ht1, ht2, htH⟩ := h (E.map e.toMonoidHom) k
    (CFSG.SectionRank.isElemAbelian_map hE _)
    (by rw [Subgroup.card_map_of_injective e.injective, hEc]) hk
  have hHr : (H.comap e.toMonoidHom).map e.toMonoidHom = H :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective H
  refine ⟨H.comap e.toMonoidHom, ?_, ?_, e.symm t, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hHE hx
    rw [← e.injective hyx]
    exact hy
  · have h1 : Nat.card (E.map e.toMonoidHom) = Nat.card E := Subgroup.card_map_of_injective e.injective
    have h2 : Nat.card ((H.comap e.toMonoidHom).map e.toMonoidHom) = Nat.card (H.comap e.toMonoidHom) :=
      Subgroup.card_map_of_injective e.injective
    rw [← h1, hHc, ← h2, hHr]
  · intro h1
    apply ht1
    rw [← e.apply_symm_apply t, h1, map_one]
  · rw [← map_mul, ht2, map_one]
  · intro x hx
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact htH _ hx

theorem mem_range_conj_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') {α : MulAut G}
    (h : MulAut.congr e α ∈ (MulAut.conj : G' →* MulAut G').range) :
    α ∈ (MulAut.conj : G →* MulAut G).range := by
  obtain ⟨g, hg⟩ := h
  refine ⟨e.symm g, MulEquiv.ext fun x => ?_⟩
  have h1 := congrArg (fun φ : MulAut G' => φ (e x)) hg
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, e.apply_symm_apply, h1]

theorem card_le_three_mul_inner_of_mulEquiv {G G' : Type*} [Group G] [Group G'] [Finite G'] (e : G ≃* G')
    (h : ∀ D : Subgroup (MulAut G'), IsElemAbelian 3 D →
      Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : G' →* MulAut G').range))
    (D : Subgroup (MulAut G)) (hD : IsElemAbelian 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : G →* MulAut G).range) := by
  haveI : Finite (MulAut G') := MulEquiv.finite_left
  have hD' := h (D.map (MulAut.congr e).toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hD _)
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective] at hD'
  refine hD'.trans (Nat.mul_le_mul_left 3 ?_)
  have hle : D.map (MulAut.congr e).toMonoidHom ⊓ (MulAut.conj : G' →* MulAut G').range ≤
      (D ⊓ (MulAut.conj : G →* MulAut G).range).map (MulAut.congr e).toMonoidHom := by
    rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, mem_range_conj_of_mulEquiv e hy⟩, rfl⟩
  calc Nat.card ↥(D.map (MulAut.congr e).toMonoidHom ⊓ (MulAut.conj : G' →* MulAut G').range)
      ≤ Nat.card ↥((D ⊓ (MulAut.conj : G →* MulAut G).range).map (MulAut.congr e).toMonoidHom) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card ↥(D ⊓ (MulAut.conj : G →* MulAut G).range) :=
        Subgroup.card_map_of_injective (MulAut.congr e).injective

theorem isElemAbelian_comap_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ} {f : G →* H}
    (hf : Function.Injective f) {A : Subgroup H} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.comap f) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (hf ?_)⟩⟩, fun x hx => hf ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨_, a.2⟩ ⟨_, b.2⟩)
  · rw [map_pow, map_one]
    exact hA.2 _ hx

@[expose] def HyperInvOut (G : Type*) [Group G] : Prop :=
  ∀ D : Subgroup (MulAut G), IsElemAbelian 3 D → ¬ D ≤ (MulAut.conj : G →* MulAut G).range →
    ∃ E : Subgroup (MulAut G), E ≤ D ∧ Nat.card D ≤ 3 * Nat.card E ∧
      ∃ t : G, t ≠ 1 ∧ t * t = 1 ∧ ∀ φ ∈ E, φ t = t

theorem HyperInvOut.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G') (h : HyperInvOut G') :
    HyperInvOut G := by
  intro D hD hDout
  set c := MulAut.congr e with hcdef
  have hD'out : ¬ D.map c.toMonoidHom ≤ (MulAut.conj : G' →* MulAut G').range := by
    intro hle
    apply hDout
    intro x hx
    exact mem_range_conj_of_mulEquiv e (hle ⟨x, hx, rfl⟩)
  obtain ⟨E', hE'D, hE'c, t, ht1, ht2, htE⟩ := h (D.map c.toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hD _) hD'out
  have hE'r : (E'.comap c.toMonoidHom).map c.toMonoidHom = E' :=
    Subgroup.map_comap_eq_self_of_surjective c.surjective E'
  refine ⟨E'.comap c.toMonoidHom, fun x hx => ?_, ?_, e.symm t, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hE'D hx
    rw [← c.injective hyx]
    exact hy
  · have h1 : Nat.card (D.map c.toMonoidHom) = Nat.card D := Subgroup.card_map_of_injective c.injective
    have h2 : Nat.card ((E'.comap c.toMonoidHom).map c.toMonoidHom) = Nat.card (E'.comap c.toMonoidHom) :=
      Subgroup.card_map_of_injective c.injective
    rw [← h1, ← h2, hE'r]
    exact hE'c
  · intro h1
    apply ht1
    rw [← e.apply_symm_apply t, h1, map_one]
  · rw [← map_mul, ht2, map_one]
  · intro φ hφ
    have h1 : c φ t = t := htE _ hφ
    have h2 : c φ t = e (φ (e.symm t)) := rfl
    rw [h2] at h1
    have h3 := congrArg e.symm h1
    rwa [MulEquiv.symm_apply_apply] at h3

end HyperInvDef

section SpLinear

open CFSG.Open (StatedSp StatedScalars StatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped Matrix

variable {n : ℕ} {F : Type} [Field F]

theorem statedScalars_subgroupOf_sp [CharP F 2] (hn : 1 ≤ n) :
    (StatedScalars (Fin n ⊕ Fin n) F).subgroupOf (StatedSp n F) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hx
  obtain ⟨u, hu⟩ := hx
  have hx2 := SymplecticTorusWeyl.mem_statedSp_iff.1 x.2
  rw [← hu, Matrix.GeneralLinearGroup.coe_scalar] at hx2
  have hJ := congrFun (congrFun hx2 (Sum.inl ⟨0, by omega⟩)) (Sum.inr ⟨0, by omega⟩)
  simp [Matrix.scalar_apply, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.fromBlocks] at hJ
  have hu1 : (u : F) = 1 := by
    have h2 : ((u : F) - 1) ^ 2 = 0 := by
      have h3 : ((u : F) - 1) ^ 2 = (u : F) * u - 1 - 2 * (u : F) + 2 := by ring
      rw [h3, hJ, CharTwo.two_eq_zero]
      ring
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h2)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hu, show u = 1 from Units.ext hu1, map_one, OneMemClass.coe_one]

noncomputable def projEquivSp [CharP F 2] (hn : 1 ≤ n) :
    StatedProj (StatedSp n F) ≃* ↥(StatedSp n F) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_sp hn)).trans QuotientGroup.quotientBot

variable (n F) in
abbrev spJ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 0 1 (-1) 0

variable (n F) in
noncomputable abbrev spForm : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) :=
  Matrix.toBilin' (spJ n F)

theorem spJ_mulVec (x : Fin n ⊕ Fin n → F) :
    spJ n F *ᵥ x = Sum.elim (x ∘ Sum.inr) (-(x ∘ Sum.inl)) := by
  rw [spJ, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, Matrix.one_mulVec, Matrix.neg_mulVec, zero_add, add_zero]

theorem spForm_self (x : Fin n ⊕ Fin n → F) : spForm n F x x = 0 := by
  rw [Matrix.toBilin'_apply', spJ_mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Function.comp_apply, Pi.neg_apply, mul_neg]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i _ => ?_
  ring

theorem spJ_mul_self : spJ n F * spJ n F = -1 := by
  rw [spJ, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg, neg_zero]

theorem spForm_isometry {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F)
    (x y : Fin n ⊕ Fin n → F) :
    spForm n F ((g : Matrix _ _ F) *ᵥ x) ((g : Matrix _ _ F) *ᵥ y) = spForm n F x y := by
  have h := Matrix.toBilin'_comp (spJ n F) (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  rw [SymplecticTorusWeyl.mem_statedSp_iff.1 hg] at h
  have h2 := congrArg (fun b : LinearMap.BilinForm F (Fin n ⊕ Fin n → F) => b x y) h
  simpa [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using h2

theorem mem_statedSp_of_isometry {g : GL (Fin n ⊕ Fin n) F}
    (h : ∀ x y, spForm n F ((g : Matrix _ _ F) *ᵥ x) ((g : Matrix _ _ F) *ᵥ y) = spForm n F x y) :
    g ∈ StatedSp n F := by
  rw [SymplecticTorusWeyl.mem_statedSp_iff]
  apply Matrix.toBilin'.injective
  rw [← Matrix.toBilin'_comp]
  refine LinearMap.ext₂ fun x y => ?_
  simpa [LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply] using h x y

noncomputable def spTransv (v : Fin n ⊕ Fin n → F) : GL (Fin n ⊕ Fin n) F :=
  Matrix.GeneralLinearGroup.toLin.symm
    (CFSG.ClassicalGroups.Alternating.symplecticTransvection (spForm n F) spForm_self v 1)

theorem spTransv_mulVec (v x : Fin n ⊕ Fin n → F) :
    ((spTransv v : GL _ F) : Matrix _ _ F) *ᵥ x = x + spForm n F x v • v := by
  have h : Matrix.GeneralLinearGroup.toLin (spTransv v) =
      CFSG.ClassicalGroups.Alternating.symplecticTransvection (spForm n F) spForm_self v 1 :=
    MulEquiv.apply_symm_apply _ _
  have h2 := congrArg (fun g : LinearMap.GeneralLinearGroup F (Fin n ⊕ Fin n → F) =>
    (g : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F)) x) h
  have h3 := h2.trans (CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply
    (B := spForm n F) spForm_self v 1 x)
  rw [one_mul] at h3
  simpa [Matrix.GeneralLinearGroup.coe_toLin] using h3

theorem spTransv_mem (v : Fin n ⊕ Fin n → F) : spTransv v ∈ StatedSp n F := by
  refine mem_statedSp_of_isometry fun x y => ?_
  rw [spTransv_mulVec, spTransv_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, spForm_self, smul_eq_mul,
    mul_zero, add_zero]
  have hyx : spForm n F y v = -spForm n F v y := by
    have h := spForm_self (n := n) (F := F) (y + v)
    simp only [map_add, LinearMap.add_apply, spForm_self, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  rw [hyx]
  ring

theorem spTransv_mul_self [CharP F 2] (v : Fin n ⊕ Fin n → F) : spTransv v * spTransv v = 1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Units.val_mul, Units.val_one, Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
    spTransv_mulVec, spTransv_mulVec, Matrix.one_mulVec]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, spForm_self, smul_eq_mul,
    mul_zero, add_zero]
  rw [add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem spTransv_ne_one {v : Fin n ⊕ Fin n → F} (hv : v ≠ 0) : spTransv v ≠ 1 := by
  intro h
  apply hv
  have hB : ∀ x, spForm n F x v = 0 := by
    intro x
    have h1 := spTransv_mulVec v x
    rw [h, Units.val_one, Matrix.one_mulVec, left_eq_add, smul_eq_zero] at h1
    exact h1.resolve_right hv
  have hJv : spJ n F *ᵥ v = 0 := by
    funext k
    have h1 := hB (Pi.single k 1)
    rw [Matrix.toBilin'_apply', single_dotProduct, one_mul] at h1
    exact h1
  have h2 : spJ n F *ᵥ (spJ n F *ᵥ v) = -v := by
    rw [Matrix.mulVec_mulVec, spJ_mul_self, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hJv, Matrix.mulVec_zero] at h2
  exact neg_eq_zero.1 h2.symm

theorem comm_spTransv {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F)
    {v : Fin n ⊕ Fin n → F} (hgv : (g : Matrix _ _ F) *ᵥ v = v) :
    g * spTransv v = spTransv v * g := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, spTransv_mulVec, spTransv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hgv]
  have h := spForm_isometry hg x v
  rw [hgv] at h
  rw [h]

@[expose] noncomputable def vecAct (ι K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] :
    GL ι K →* MulAut (Multiplicative (ι → K)) where
  toFun g :=
    { toFun := fun v => Multiplicative.ofAdd ((g : Matrix ι ι K) *ᵥ Multiplicative.toAdd v)
      invFun := fun v => Multiplicative.ofAdd ((↑g⁻¹ : Matrix ι ι K) *ᵥ Multiplicative.toAdd v)
      left_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, ofAdd_toAdd]
      right_inv := fun v => by
        simp only [toAdd_ofAdd, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec, ofAdd_toAdd]
      map_mul' := fun v w => by
        simp only [toAdd_mul, Matrix.mulVec_add, ofAdd_add] }
  map_one' := by
    ext v
    simp
  map_mul' := fun g h => by
    ext v
    simp [Matrix.mulVec_mulVec]

theorem exists_hyperplane_fix [Finite F] (hF3 : ¬ 3 ∣ Nat.card F) {ι : Type} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {E : Subgroup (GL ι F)} (hE : IsElemAbelian 3 E) (hE1 : E ≠ ⊥) :
    ∃ H : Subgroup (GL ι F), H ≤ E ∧ Nat.card E = 3 * Nat.card H ∧
      ∃ v : ι → F, v ≠ 0 ∧ ∀ h ∈ H, (h : Matrix ι ι F) *ᵥ v = v := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsElementaryAbelian 3 ↥E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
  haveI : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hE1
  letI : MulDistribMulAction ↥E (Multiplicative (ι → F)) :=
    MulDistribMulAction.compHom _ ((vecAct ι F).comp E.subtype)
  have hcop : ¬ 3 ∣ Nat.card (Multiplicative (ι → F)) := by
    rw [show Nat.card (Multiplicative (ι → F)) = Nat.card (ι → F) from rfl, Nat.card_fun]
    exact fun h => hF3 (Nat.prime_three.dvd_of_dvd_pow h)
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := 3) (A := ↥E)
    (H := Multiplicative (ι → F)) hcop
  obtain ⟨B, hBi, hBne⟩ : ∃ B : Subgroup ↥E, B.index = 3 ∧
      CFSG.fixedPointSubgroup B (Multiplicative (ι → F)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Subgroup (Multiplicative (ι → F))) = ⊥ := by
      rw [← hgen]
      exact iSup₂_eq_bot.2 fun B hB => hcon B hB
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hne : (Multiplicative.ofAdd (Pi.single i 1 : ι → F)) ≠ 1 := by
      intro h
      have := congrFun (congrArg Multiplicative.toAdd h) i
      simp at this
    exact hne (Subgroup.eq_bot_iff_forall _ |>.1 htop _ (Subgroup.mem_top _))
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  refine ⟨B.map E.subtype, Subgroup.map_subtype_le B, ?_, Multiplicative.toAdd (w : Multiplicative _), ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective, ← hBi, Subgroup.index_mul_card]
  · intro h0
    apply hw1
    apply Subtype.ext
    show (w : Multiplicative (ι → F)) = 1
    rw [← ofAdd_toAdd (w : Multiplicative (ι → F)), h0, ofAdd_zero]
  · rintro _ ⟨b, hb, rfl⟩
    have h1 := (FixedPoints.mem_subgroup ↥B (Multiplicative (ι → F))
      (w : Multiplicative (ι → F))).1 w.2 ⟨b, hb⟩
    have h3 := congrArg Multiplicative.toAdd h1
    exact h3

theorem hyperInv_statedSp [Finite F] [CharP F 2] (hn : 1 ≤ n) : HyperInv ↥(StatedSp n F) := by
  classical
  intro E k hE hEc hk
  have hF3 : ¬ 3 ∣ Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hm]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  let f := (StatedSp n F).subtype
  have hf : Function.Injective f := Subgroup.subtype_injective _
  have hE'el : IsElemAbelian 3 (E.map f) := CFSG.SectionRank.isElemAbelian_map hE f
  have hE'c : Nat.card (E.map f) = 3 ^ k := by rw [Subgroup.card_map_of_injective hf, hEc]
  have hE'ne : E.map f ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hE'c
    have := Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 3)
    omega
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨H, hHE, hHc, v, hv0, hHv⟩ := exists_hyperplane_fix hF3 hE'el hE'ne
  have hHr : H ≤ f.range := hHE.trans (Subgroup.map_le_range f E)
  have hHc' : Nat.card (H.comap f) = Nat.card H := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hHr]
    rw [Subgroup.card_map_of_injective hf]
  refine ⟨H.comap f, fun x hx => ?_, ?_, ⟨spTransv v, spTransv_mem v⟩, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hHE hx
    exact hf hyx ▸ hy
  · rw [hHc', ← hHc, Subgroup.card_map_of_injective hf]
  · intro h1
    exact spTransv_ne_one hv0 (congrArg Subtype.val h1)
  · exact Subtype.ext (spTransv_mul_self v)
  · intro x hx
    exact Subtype.ext (comm_spTransv x.2 (hHv _ hx))

theorem card_le_three_mul_inf {G : Type*} [Group G] {N : Subgroup G} [N.Normal] (hN : ¬ 9 ∣ N.index)
    (hN0 : N.index ≠ 0) {D : Subgroup G} [Finite D] (hD : IsPGroup 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ N) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := Subgroup.relIndex_mul_card N D
  obtain ⟨k, hk⟩ := hD.exists_card_eq
  have hdvd : N.relIndex D ∣ 3 ^ k := hk ▸ Subgroup.relIndex_dvd_card N D
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hj1 : j ≤ 1 := by
    by_contra hj1
    apply hN
    have h9 : 3 ^ 2 ∣ 3 ^ j := Nat.pow_dvd_pow 3 (by omega)
    exact h9.trans (hj ▸ Subgroup.relIndex_dvd_index_of_normal N D)
  have h2 : N.relIndex D ≤ 3 := by
    rw [hj]
    calc 3 ^ j ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 3 := pow_one 3
  rw [inf_comm] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ h2

theorem card_le_three_mul_inner_sp [Finite F] (hF : Nat.card F = 2 ^ 3) (hn : 2 ≤ n)
    (D : Subgroup (MulAut (StatedProj (StatedSp n F)))) (hD : IsElemAbelian 3 D) :
    Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : StatedProj (StatedSp n F) →* _).range) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (outer_card_dvd Nat.prime_two (by norm_num) hF hn).1
  rw [show 2 * 3 * Nat.gcd 2 (2 ^ 3 - 1) = 6 by norm_num] at h
  haveI : (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  have hidx : (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range.index ∣ 6 := h
  haveI : Finite (MulAut (StatedProj (StatedSp n F))) := MulEquiv.finite_left
  refine card_le_three_mul_inf (fun h9 => ?_) (fun h0 => by rw [h0] at hidx; norm_num at hidx) hD.isPGroup
  have := Nat.le_of_dvd (by norm_num) (h9.trans hidx)
  omega

theorem nonempty_typeBGroupEquiv_spTwo {n : ℕ} (hn : 3 ≤ n) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid) (hp : q.p = 2) (he : q.exponent = 1) :
    Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.B n q, hv⟩ ≃* ↥(StatedSp n (ZMod 2))) := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B n q, hv⟩
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) = 2 ^ 1 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic ⟨.B n q, hv⟩ = q.p from
        TauCeti.LieTypeIndex.characteristic_B n q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B n q, hv⟩ = q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_B n q, hp, he]
  let φ : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) ≃+* ZMod 2 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField _ 2 1 one_pos hcard).trans
      (GaloisField.equivZmodP 2).toRingEquiv
  exact ⟨(CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hp hn).trans
    ((CFSG.Adapters.RankTwoModelTransports.statedProjCongr
      (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
      (CFSG.ClassicalInvolution.Upgrade.glCongr_statedSp φ n)
      (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)).trans (projEquivSp (by omega)))⟩

theorem all_inner_spTwo {n : ℕ} (hn : 3 ≤ n) (α : MulAut ↥(StatedSp n (ZMod 2))) :
    ∃ g : ↥(StatedSp n (ZMod 2)), α = MulAut.conj g := by
  have key : ∀ β : MulAut (StatedProj (StatedSp n (ZMod 2))),
      ∃ g : StatedProj (StatedSp n (ZMod 2)), β = MulAut.conj g := by
    intro β
    obtain ⟨-, hform⟩ := automorphism_generation (K := ZMod 2) (r := n) hn
    obtain ⟨A, σ, hβ⟩ := hform β
    have hσ : fieldAut n (ZMod 2) σ = 1 := by
      rw [show σ = 1 from Subsingleton.elim _ _, map_one]
    have hA : (A : GL (Fin n ⊕ Fin n) (ZMod 2)) ∈ StatedSp n (ZMod 2) := by
      obtain ⟨μ, hμ⟩ := A.2
      have hμ1 : μ = 1 := Subsingleton.elim _ _
      subst hμ1
      rw [Units.val_one, one_smul] at hμ
      exact SymplecticTorusWeyl.mem_statedSp_iff.2 hμ
    refine ⟨SymplecticFlag.proj n (ZMod 2) ⟨A, hA⟩, ?_⟩
    rw [hβ, hσ, mul_one, ← conjAut_statedSp]
  have hn1 : 1 ≤ n := by omega
  obtain ⟨g, hg⟩ := key (MulAut.congr (projEquivSp (F := ZMod 2) hn1).symm α)
  refine ⟨projEquivSp hn1 g, ?_⟩
  have h1 : MulAut.congr (projEquivSp (F := ZMod 2) hn1)
      (MulAut.congr (projEquivSp (F := ZMod 2) hn1).symm α) = α := by
    ext x
    simp [MulAut.congr_apply]
  rw [← h1, hg, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj]

theorem exists_typeBGroupEquiv_sp {n : ℕ} (hn : 2 ≤ n) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.B n q).Valid) (hp : q.p = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ q.exponent ∧
      Nonempty (TauCeti.ValidLieTypeIndex.Group ⟨.B n q, hv⟩ ≃* ↥(StatedSp n F)) := by
  have hfin := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B n q, hv⟩
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) = 2 ^ q.exponent := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
      show TauCeti.ValidLieTypeIndex.characteristic ⟨.B n q, hv⟩ = q.p from
        TauCeti.LieTypeIndex.characteristic_B n q,
      show TauCeti.ValidLieTypeIndex.fieldExponent ⟨.B n q, hv⟩ = q.exponent from
        TauCeti.LieTypeIndex.fieldExponent_B n q, hp]
  haveI : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩) 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      q.exponent_pos hcard
  have e : TauCeti.ValidLieTypeIndex.Group ⟨.B n q, hv⟩ ≃*
      StatedProj (StatedSp n ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B n q, hv⟩)) := by
    by_cases h2 : n = 2
    · subst h2
      exact CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv
    · exact CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj n q hv hp (by omega)
  exact ⟨_, inferInstance, hfin, inferInstance, hcard, ⟨e.trans (projEquivSp (by omega))⟩⟩

@[expose] def IsSpTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), 3 ≤ n ∧ q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B n q

@[expose] def IsSpEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (n : ℕ) (q : TauCeti.PrimePower), 2 ≤ n ∧ q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B n q

end SpLinear

section SpField

open CFSG.Open (StatedSp StatedScalars StatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open scoped Matrix

variable {n : ℕ} {F : Type} [Field F]

theorem vecAct_apply (ι : Type) [Fintype ι] [DecidableEq ι] (g : GL ι F) (v : Multiplicative (ι → F)) :
    Multiplicative.toAdd (vecAct ι F g v) = (g : Matrix ι ι F) *ᵥ Multiplicative.toAdd v :=
  rfl

@[expose] noncomputable def fieldVecAct (ι F : Type) [Field F] : (F ≃+* F) →* MulAut (Multiplicative (ι → F)) where
  toFun σ :=
    { toFun := fun v => Multiplicative.ofAdd fun i => σ (Multiplicative.toAdd v i)
      invFun := fun v => Multiplicative.ofAdd fun i => σ.symm (Multiplicative.toAdd v i)
      left_inv := fun v => by simp
      right_inv := fun v => by simp
      map_mul' := fun v w => by
        simp only [toAdd_mul, Pi.add_apply, map_add]
        rfl }
  map_one' := by
    ext v
    rfl
  map_mul' := fun σ τ => by
    ext v
    rfl

theorem fieldVecAct_apply (ι : Type) (σ : F ≃+* F) (v : Multiplicative (ι → F)) :
    Multiplicative.toAdd (fieldVecAct ι F σ v) = fun i => σ (Multiplicative.toAdd v i) :=
  rfl

theorem map_mulVec_apply {ι : Type} [Fintype ι] (σ : F ≃+* F) (M : Matrix ι ι F) (v : ι → F) (i : ι) :
    σ ((M *ᵥ v) i) = (M.map σ *ᵥ fun j => σ (v j)) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem fieldVecAct_commute {ι : Type} [Fintype ι] [DecidableEq ι] {σ : F ≃+* F} {g : GL ι F}
    (hg : (g : Matrix ι ι F).map σ = g) :
    Commute (fieldVecAct ι F σ) (vecAct ι F g) := by
  apply MulEquiv.ext
  intro v
  apply Multiplicative.toAdd.injective
  rw [MulAut.mul_apply, MulAut.mul_apply, fieldVecAct_apply, vecAct_apply, vecAct_apply, fieldVecAct_apply]
  funext i
  rw [map_mulVec_apply, hg]

@[expose] def matFix {ι : Type} (M : Matrix ι ι F) : Subgroup (F ≃+* F) where
  carrier := {τ | M.map τ = M}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [Matrix.map_apply] at h1 h2 ⊢
    show a (b (M i j)) = M i j
    rw [h2, h1]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    ext i j
    rfl
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [Matrix.map_apply] at h1 ⊢
    show a.symm (M i j) = M i j
    conv_lhs => rw [← h1]
    exact a.symm_apply_apply _

theorem spForm_map (σ : F ≃+* F) (x y : Fin n ⊕ Fin n → F) :
    spForm n F (fun i => σ (x i)) (fun i => σ (y i)) = σ (spForm n F x y) := by
  rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', spJ_mulVec, spJ_mulVec, dotProduct, dotProduct,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases i with i | i <;> simp [map_mul, map_neg]

theorem map_spTransv (σ : F ≃+* F) (v : Fin n ⊕ Fin n → F) :
    ((spTransv v : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map σ =
      ((spTransv (fun i => σ (v i)) : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, spTransv_mulVec]
  funext i
  have h1 := map_mulVec_apply σ ((spTransv v : GL (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (fun j => σ.symm (x j)) i
  simp only [RingEquiv.apply_symm_apply] at h1
  rw [← h1, spTransv_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingEquiv.apply_symm_apply]
  rw [← spForm_map σ (fun j => σ.symm (x j)) v]
  simp only [RingEquiv.apply_symm_apply]

theorem conj_spTransv {g : GL (Fin n ⊕ Fin n) F} (hg : g ∈ StatedSp n F) (v : Fin n ⊕ Fin n → F) :
    g * spTransv v * g⁻¹ = spTransv ((g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v) := by
  apply Units.ext
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, spTransv_mulVec, spTransv_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hgg : (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
      (((g⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hgg]
  have h := spForm_isometry hg (((g⁻¹ : GL (Fin n ⊕ Fin n) F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ x) v
  rw [hgg] at h
  rw [h]

theorem mem_matFix {ι : Type} {M : Matrix ι ι F} {τ : F ≃+* F} : τ ∈ matFix M ↔ M.map τ = M :=
  Iff.rfl

theorem proj_injective_sp [CharP F 2] (hn : 1 ≤ n) : Function.Injective (proj n F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  show (QuotientGroup.mk' _).ker = ⊥
  rw [QuotientGroup.ker_mk']
  exact statedScalars_subgroupOf_sp hn

theorem exists_fixInv_of_fieldAut_mem [Finite F] [CharP F 2] (hn : 1 ≤ n)
    (hconj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))))
    {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (hσout : fieldAut n F σ ∉
      (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range)
    {D : Subgroup (MulAut (StatedProj (StatedSp n F)))} (hD : IsElemAbelian 3 D)
    (hσD : fieldAut n F σ ∈ D)
    (hD3 : Nat.card D ≤ 3 * Nat.card ↥(D ⊓
      (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range)) :
    ∃ E : Subgroup (MulAut (StatedProj (StatedSp n F))), E ≤ D ∧ Nat.card D ≤ 3 * Nat.card E ∧
      ∃ t : StatedProj (StatedSp n F), t ≠ 1 ∧ t * t = 1 ∧ ∀ φ ∈ E, φ t = t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hπ := proj_injective_sp (F := F) hn
  let c : ↥(StatedSp n F) →* MulAut (StatedProj (StatedSp n F)) := MulAut.conj.comp (proj n F)
  have hc : Function.Injective c := hconj.comp hπ
  set E₀ : Subgroup ↥(StatedSp n F) := (D ⊓ (MulAut.conj : StatedProj (StatedSp n F) →*
    MulAut (StatedProj (StatedSp n F))).range).comap c with hE₀
  have hmap : E₀.map c = D ⊓ (MulAut.conj : StatedProj (StatedSp n F) →*
      MulAut (StatedProj (StatedSp n F))).range := by
    refine Subgroup.map_comap_eq_self fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx.2
    obtain ⟨s, rfl⟩ := proj_surjective (r := n) (K := F) y
    exact ⟨s, rfl⟩
  have hE₀c : Nat.card E₀ = Nat.card ↥(D ⊓ (MulAut.conj : StatedProj (StatedSp n F) →*
      MulAut (StatedProj (StatedSp n F))).range) := by
    rw [← hmap, Subgroup.card_map_of_injective hc]
  have hE₀el : IsElemAbelian 3 E₀ := isElemAbelian_comap_of_injective hc (elem_mono hD inf_le_left)
  have hcomm : ∀ φ ∈ D, Commute (fieldAut n F σ) φ := fun φ hφ =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hσD⟩ ⟨φ, hφ⟩)
  have hfix : ∀ a ∈ E₀, σ ∈ matFix ((a : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    intro a ha
    have h1 : MulAut.conj (fieldAut n F σ (proj n F a)) = MulAut.conj (proj n F a) := by
      have h2 : MulAut.conj (fieldAut n F σ (proj n F a)) =
          fieldAut n F σ * MulAut.conj (proj n F a) * (fieldAut n F σ)⁻¹ := by
        ext x
        simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
          MulEquiv.apply_symm_apply]
      rw [h2]
      have h3 : MulAut.conj (proj n F a) = c a := rfl
      rw [h3, (hcomm _ ha.1).eq, mul_inv_cancel_right]
    have h4 : proj n F (fieldSp n F σ a) = proj n F a := by
      rw [← fieldAut_proj]
      exact hconj h1
    have h5 := congrArg (fun g : ↥(StatedSp n F) => ((g : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) (hπ h4)
    simp only [coe_fieldSp] at h5
    exact mem_matFix.2 h5
  have hfixz : ∀ a ∈ E₀, ∀ x ∈ Subgroup.zpowers σ, ((a : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F).map x = (a : GL (Fin n ⊕ Fin n) F) :=
    fun a ha x hx => mem_matFix.1 ((Subgroup.zpowers_le.2 (hfix a ha)) hx)
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hx1 : ∀ x ∈ Subgroup.zpowers σ, fieldAut n F x ∈ (MulAut.conj : StatedProj (StatedSp n F) →*
      MulAut (StatedProj (StatedSp n F))).range → x = 1 := by
    intro x hx hxin
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_mod_orderOf, hσ] at hxin ⊢
    have h0 : 0 ≤ k % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h3 : k % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨r, hr⟩ : ∃ r : ℕ, k % ((3 : ℕ) : ℤ) = r := ⟨(k % ((3 : ℕ) : ℤ)).toNat, by omega⟩
    rw [hr, zpow_natCast] at hxin ⊢
    have hr3 : r < 3 := by omega
    interval_cases r
    · rfl
    · rw [pow_one] at hxin
      exact absurd hxin hσout
    · exfalso
      apply hσout
      have h4 : fieldAut n F σ = (fieldAut n F (σ ^ 2)) ^ 2 := by
        rw [← map_pow, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hσ3, one_mul]
      rw [h4]
      exact pow_mem hxin 2
  have hcommV : ∀ (x : ↥(Subgroup.zpowers σ)) (a : ↥E₀),
      Commute (((fieldVecAct (Fin n ⊕ Fin n) F).comp (Subgroup.zpowers σ).subtype) x)
        (((vecAct (Fin n ⊕ Fin n) F).comp ((StatedSp n F).subtype.comp E₀.subtype)) a) := fun x a =>
    fieldVecAct_commute (hfixz a a.2 x x.2)
  let Θ := MonoidHom.noncommCoprod _ _ hcommV
  have hcommP : ∀ (x : ↥(Subgroup.zpowers σ)) (a : ↥E₀),
      Commute (((fieldAut n F).comp (Subgroup.zpowers σ).subtype) x) ((c.comp E₀.subtype) a) := by
    rintro ⟨x, hx⟩ a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    show Commute (fieldAut n F (σ ^ k)) (c a)
    rw [map_zpow]
    exact (hcomm _ a.2.1).zpow_left k
  let Θ' := MonoidHom.noncommCoprod _ _ hcommP
  have hzc : Nat.card (Subgroup.zpowers σ) = 3 := by rw [Nat.card_zpowers, hσ]
  haveI : IsElementaryAbelian 3 (↥(Subgroup.zpowers σ) × ↥E₀) :=
    { is_comm := ⟨fun x y => by
        refine Prod.ext (Subtype.ext ?_) (hE₀el.1.is_comm.comm x.2 y.2)
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.1.2
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.1 y.1.2
        show (x.1 : F ≃+* F) * y.1 = y.1 * x.1
        rw [← hk, ← hl]
        exact (Commute.refl σ).zpow_zpow k l⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => by
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext (hE₀el.2 _ g.2.2))
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 g.1.2
        show (g.1 : F ≃+* F) ^ 3 = 1
        rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3, one_zpow] }
  have hσ1 : σ ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hσ; omega
  haveI : Nontrivial (↥(Subgroup.zpowers σ) × ↥E₀) :=
    ⟨⟨(⟨σ, Subgroup.mem_zpowers σ⟩, 1), 1, fun h =>
      hσ1 (congrArg Subtype.val (congrArg Prod.fst h))⟩⟩
  letI : MulDistribMulAction (↥(Subgroup.zpowers σ) × ↥E₀) (Multiplicative (Fin n ⊕ Fin n → F)) :=
    MulDistribMulAction.compHom _ Θ
  have hcop : ¬ 3 ∣ Nat.card (Multiplicative (Fin n ⊕ Fin n → F)) := by
    rw [show Nat.card (Multiplicative (Fin n ⊕ Fin n → F)) = Nat.card (Fin n ⊕ Fin n → F) from rfl,
      Nat.card_fun]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, -, hm⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hm, ← pow_mul]
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  have hgen := CFSG.SolvableHall.abelian_hyperplane_generation (p := 3)
    (A := ↥(Subgroup.zpowers σ) × ↥E₀) (H := Multiplicative (Fin n ⊕ Fin n → F)) hcop
  obtain ⟨B, hBi, hBne⟩ : ∃ B : Subgroup (↥(Subgroup.zpowers σ) × ↥E₀), B.index = 3 ∧
      CFSG.fixedPointSubgroup B (Multiplicative (Fin n ⊕ Fin n → F)) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have htop : (⊤ : Subgroup (Multiplicative (Fin n ⊕ Fin n → F))) = ⊥ := by
      rw [← hgen]
      exact iSup₂_eq_bot.2 fun B hB => hcon B hB
    have hne : (Multiplicative.ofAdd (Pi.single (Sum.inl ⟨0, by omega⟩) 1 : Fin n ⊕ Fin n → F)) ≠ 1 := by
      intro h
      have := congrFun (congrArg Multiplicative.toAdd h) (Sum.inl ⟨0, by omega⟩)
      simp at this
    exact hne (Subgroup.eq_bot_iff_forall _ |>.1 htop _ (Subgroup.mem_top _))
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hBne
  set v : Fin n ⊕ Fin n → F := Multiplicative.toAdd (w : Multiplicative (Fin n ⊕ Fin n → F)) with hvdef
  have hv0 : v ≠ 0 := by
    intro h0
    apply hw1
    apply Subtype.ext
    show (w : Multiplicative (Fin n ⊕ Fin n → F)) = 1
    rw [← ofAdd_toAdd (w : Multiplicative (Fin n ⊕ Fin n → F)), ← hvdef, h0, ofAdd_zero]
  have hBv : ∀ b ∈ B, Θ b (w : Multiplicative (Fin n ⊕ Fin n → F)) = w := fun b hb =>
    (FixedPoints.mem_subgroup ↥B (Multiplicative (Fin n ⊕ Fin n → F))
      (w : Multiplicative (Fin n ⊕ Fin n → F))).1 w.2 ⟨b, hb⟩
  have hΘ'inj : Function.Injective Θ' := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, a⟩ hxa
    rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hxa
    have hxin : fieldAut n F (x : F ≃+* F) ∈ (MulAut.conj : StatedProj (StatedSp n F) →*
        MulAut (StatedProj (StatedSp n F))).range := by
      have h1 : fieldAut n F (x : F ≃+* F) = (c a)⁻¹ := eq_inv_of_mul_eq_one_left hxa
      rw [h1]
      exact inv_mem ⟨proj n F a, rfl⟩
    have hx : x = 1 := Subtype.ext (hx1 x x.2 hxin)
    subst hx
    have ha : c a = 1 := by
      simpa using hxa
    have ha1 : a = 1 := Subtype.ext (hc (ha.trans (map_one c).symm))
    rw [Subgroup.mem_bot, ha1]
    rfl
  set tS : ↥(StatedSp n F) := ⟨spTransv v, spTransv_mem v⟩ with htS
  refine ⟨B.map Θ', ?_, ?_, proj n F tS, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨x, a⟩, -, rfl⟩
    rw [MonoidHom.noncommCoprod_apply]
    refine mul_mem ?_ a.2.1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 x.2
    show fieldAut n F (x : F ≃+* F) ∈ D
    rw [← hk, map_zpow]
    exact zpow_mem hσD k
  · rw [Subgroup.card_map_of_injective hΘ'inj]
    have h1 : Nat.card (↥(Subgroup.zpowers σ) × ↥E₀) = 3 * Nat.card E₀ := by
      rw [Nat.card_prod, hzc]
    have h2 := Subgroup.index_mul_card B
    rw [hBi, h1] at h2
    have h3 : Nat.card B = Nat.card E₀ := by omega
    rw [h3, hE₀c]
    exact hD3
  · intro h1
    apply spTransv_ne_one hv0
    have h2 := hπ (h1.trans (map_one (proj n F)).symm)
    exact congrArg Subtype.val h2
  · rw [← map_mul]
    have h2 : tS * tS = 1 := Subtype.ext (spTransv_mul_self v)
    rw [h2, map_one]
  · rintro _ ⟨⟨x, a⟩, hb, rfl⟩
    have hfx := hBv _ hb
    rw [MonoidHom.noncommCoprod_apply, MulAut.mul_apply] at hfx
    have hfx' := congrArg Multiplicative.toAdd hfx
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype, fieldVecAct_apply,
      vecAct_apply] at hfx'
    rw [MonoidHom.noncommCoprod_apply, MulAut.mul_apply]
    show fieldAut n F (x : F ≃+* F) (MulAut.conj (proj n F (a : ↥(StatedSp n F))) (proj n F tS)) =
      proj n F tS
    rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, fieldAut_proj]
    congr 1
    apply Subtype.ext
    apply Units.ext
    rw [coe_fieldSp]
    have h1 : ((((a : ↥(StatedSp n F)) * tS * (a : ↥(StatedSp n F))⁻¹ : ↥(StatedSp n F)) :
        GL (Fin n ⊕ Fin n) F)) = spTransv (((a : ↥(StatedSp n F)) : GL (Fin n ⊕ Fin n) F) *ᵥ v) :=
      conj_spTransv (a : ↥(StatedSp n F)).2 v
    rw [h1, map_spTransv, htS]
    congr 2

theorem hyperInvOut_sp [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ 3) (hn : 2 ≤ n)
    (hconj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F)))) :
    HyperInvOut (StatedProj (StatedSp n F)) := by
  classical
  intro D hD hDout
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fintype F := Fintype.ofFinite F
  haveI : (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  obtain ⟨α, hαD, hαout⟩ := Set.not_subset.1 hDout
  have hα3 : α ^ 3 = 1 := hD.2 α hαD
  have hαlin : α ∉ (conjAut n F).range := by
    rintro ⟨A, rfl⟩
    exact hαout (conjAut_mem_inner_of_isSquare (FiniteField.isSquare_of_char_two (ringChar.eq F 2) _))
  obtain ⟨σ, hσ, H, hH⟩ : ∃ σ : F ≃+* F, orderOf σ = 3 ∧ ∃ H : gsp n F,
      α = conjAut n F H * fieldAut n F σ * (conjAut n F H)⁻¹ := by
    by_cases h2 : n = 2
    · subst h2
      exact CFSG.RankThree.PartTwo.KFacts.sp4_even_order_three_field_descent α hα3 hαlin
    · exact CFSG.RankThree.PartTwo.KFacts.symplectic_order_three_field_descent (by omega) α hα3 hαlin
  set γ := conjAut n F H with hγ
  set D' := D.map (MulAut.conj γ⁻¹).toMonoidHom with hD'
  have hσD' : fieldAut n F σ ∈ D' :=
    ⟨α, hαD, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hH]; group⟩
  have hD'el : IsElemAbelian 3 D' := CFSG.SectionRank.isElemAbelian_map hD _
  have hσout : fieldAut n F σ ∉
      (MulAut.conj : StatedProj (StatedSp n F) →* MulAut (StatedProj (StatedSp n F))).range := by
    intro hin
    apply hαout
    rw [hH]
    exact Subgroup.Normal.conj_mem inferInstance _ hin γ
  obtain ⟨E', hE'D', hE'c, t, ht1, ht2, htE'⟩ :=
    exists_fixInv_of_fieldAut_mem (by omega) hconj hσ hσout hD'el hσD'
      (card_le_three_mul_inner_sp hF hn D' hD'el)
  refine ⟨E'.map (MulAut.conj γ).toMonoidHom, ?_, ?_, γ t, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hE'D' hx
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply]
    have : γ * (γ⁻¹ * y * γ⁻¹⁻¹) * γ⁻¹ = y := by group
    rw [this]
    exact hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    have h1 : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective (MulAut.conj γ⁻¹).injective
    rw [← h1]
    exact hE'c
  · intro h1
    apply ht1
    have h2 := congrArg γ.symm h1
    rwa [MulEquiv.symm_apply_apply, map_one] at h2
  · rw [← map_mul, ht2, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, htE' x hx]

end SpField

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

variable {ℓ f : ℕ} {L : Type} [Field L]

theorem hyperInv_gramSU [CharP L 2] (h : UnitaryFieldData ℓ f L) (hq3 : 3 ∣ ℓ ^ f + 1) {n : ℕ}
    (hn : 2 ≤ n) : HyperInv ↥(gramSU h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  classical
  intro E k hE hEc hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite L := h.finite
  have hSU : gramSU h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ≤
      primeFormUnitary h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    fun g hg => ((mem_gramSU_iff_unitary h).1 hg).1
  let ι := Subgroup.inclusion hSU
  let G := E.map ι
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg ι (congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hGpow : ∀ x ∈ G, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_three hq3 G
    hGcomm hGpow
  let M : ↥E → Matrix (Fin n) (Fin n) L := fun x =>
    (((P⁻¹ * ι x * P : ↥(primeFormUnitary h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) :
      GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  have hMd : ∀ x : ↥E, (M x).IsDiag := fun x => hP (ι x) ⟨x, x.2, rfl⟩
  have hMmul : ∀ x y : ↥E, M (x * y) = M x * M y := by
    intro x y
    simp only [M, Subgroup.coe_mul, map_mul]
    rw [← Units.val_mul]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hM1 : M 1 = 1 := by
    simp only [M, OneMemClass.coe_one, map_one, mul_one, inv_mul_cancel, Units.val_one]
  have hMdiag : ∀ (x y : ↥E) (i : Fin n), (M x * M y) i i = M x i i * M y i i := by
    intro x y i
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro j _ hj
      rw [hMd x hj.symm, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hMne : ∀ (x : ↥E) (i : Fin n), M x i i ≠ 0 := by
    intro x i h0
    have h1 : M x * M x⁻¹ = 1 := by rw [← hMmul, mul_inv_cancel, hM1]
    have h2 := congrFun (congrFun h1 i) i
    rw [hMdiag, h0, zero_mul, Matrix.one_apply_eq] at h2
    exact zero_ne_one h2
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin n := ⟨1, by omega⟩ with hi₁
  let r : ↥E →* L :=
    { toFun := fun x => M x i₀ i₀ * (M x i₁ i₁)⁻¹
      map_one' := by
        simp only [hM1, Matrix.one_apply_eq, inv_one, mul_one]
      map_mul' := fun x y => by
        simp only [hMmul, hMdiag, mul_inv]
        ring }
  let r' : ↥E →* Lˣ := r.toHomUnits
  have hrange : r'.range ≤ rootsOfUnity 3 L := by
    rintro _ ⟨x, rfl⟩
    rw [mem_rootsOfUnity, ← map_pow]
    have hx3 : x ^ 3 = 1 := Subtype.ext (hE.2 _ x.2)
    rw [hx3, map_one]
  have hidx : r'.ker.index ≤ 3 := by
    rw [Subgroup.index_ker]
    exact (Subgroup.card_le_of_le hrange).trans (card_rootsOfUnity L 3)
  have hker : ∀ x ∈ r'.ker, M x i₀ i₀ = M x i₁ i₁ := by
    intro x hx
    have h1 : r x = 1 := by
      have h0 : ((r' x : Lˣ) : L) = ((1 : Lˣ) : L) := congrArg Units.val (MonoidHom.mem_ker.1 hx)
      exact h0.trans Units.val_one
    have h2 : M x i₀ i₀ * (M x i₁ i₁)⁻¹ = 1 := h1
    exact (mul_inv_eq_one₀ (hMne x i₁)).1 h2
  obtain ⟨H₁, hH₁k, hH₁c⟩ : ∃ H₁ : Subgroup ↥E, H₁ ≤ r'.ker ∧ Nat.card ↥E = 3 * Nat.card H₁ := by
    have hEc' : Nat.card ↥E = 3 ^ k := hEc
    have hdvd : r'.ker.index ∣ 3 ^ k := hEc' ▸ Subgroup.index_dvd_card _
    obtain ⟨j, hjk, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj1 : j ≤ 1 := by
      by_contra hj1
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj1 with hj0 | hj1'
    · obtain ⟨H₁, hH₁⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := k - 1)
        (G := ↥E) (by rw [hEc']; exact pow_dvd_pow 3 (Nat.sub_le k 1))
      refine ⟨H₁, ?_, ?_⟩
      · rw [hj0, pow_zero, Subgroup.index_eq_one] at hj
        rw [hj]
        exact le_top
      · rw [hH₁, hEc', ← pow_succ']
        congr 1
        omega
    · refine ⟨r'.ker, le_rfl, ?_⟩
      rw [← Subgroup.index_mul_card r'.ker, hj, hj1', pow_one]
  obtain ⟨t, htSU, ht2, htns, htc⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.exists_swap_involution h hn
      (P : GL (Fin n) L) P.2
  refine ⟨H₁.map E.subtype, Subgroup.map_subtype_le _, ?_, ⟨t, htSU⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact hH₁c
  · intro h1
    apply htns 1
    rw [map_one]
    exact congrArg Subtype.val h1
  · apply Subtype.ext
    rw [Subgroup.coe_mul, ← sq, ht2, OneMemClass.coe_one]
  · rintro _ ⟨x, hx, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact htc _ (hMd x) (hker x (hH₁k hx))

noncomputable def primeFormPEquivGramSU (h : UnitaryFieldData ℓ f L) {n : ℕ} (hn : 1 ≤ n)
    (hg : Nat.gcd n (ℓ ^ f + 1) = 1) :
    primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) ≃*
      ↥(gramSU h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.eq_bot_of_card_eq _
    ((CFSG.RankThree.Classical.card_normOneScalars_one h hn).trans hg))).trans QuotientGroup.quotientBot

theorem mem_innU_two (h : UnitaryFieldData ℓ f L) (hℓ : ℓ = 2) (hf : f = 1) {n : ℕ} (hn : 4 ≤ n)
    (hn3 : ¬ 3 ∣ n) (β : MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))
    (hβ : β ^ 3 = 1) : β ∈ CFSG.RankThree.PartOne.innU h n := by
  subst hℓ hf
  haveI : Finite L := h.finite
  have hn3' : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 1 = 2) := by omega
  refine CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn3' hq Nat.prime_three ?_ ?_ hβ
  · intro hdvd
    exact hn3 (hdvd.trans (Nat.gcd_dvd_left _ _))
  · rw [← ker_primeFormFieldFactor h isPrimeFormGram_one hn3' hq, MonoidHom.mem_ker]
    set θ := primeFormFieldFactor h isPrimeFormGram_one hn3' hq β
    have hcard : Nat.card (RingAut L) = 2 :=
      (card_ringAut_and_isCyclic Nat.prime_two L (h.card.trans (by norm_num))).1
    haveI : Finite (RingAut L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
    have h2 : θ ^ 2 = 1 := by
      have := pow_card_eq_one' (G := RingAut L) (x := θ)
      rwa [hcard] at this
    have h3 : θ ^ 3 = 1 := by rw [← map_pow, hβ, map_one]
    calc θ = θ ^ 3 * (θ ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2, one_mul, inv_one]

@[expose] def IsUnitaryTwoIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ ¬ 3 ∣ r + 1 ∧ q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .twistedA r q

theorem unitaryTwo_model {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hr : 3 ≤ r) (hr3 : ¬ 3 ∣ r + 1) (hqp : q.p = 2) (hqe : q.exponent = 1) {S : Type} [Group S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    HyperInv S ∧ ∀ α : MulAut S, α ^ 3 = 1 → α ∈ (MulAut.conj : S →* MulAut S).range := by
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) L) : Matrix (Fin (r + 1)) (Fin (r + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  haveI : CharP L q.p := h.charP
  haveI : CharP L 2 := hqp ▸ h.charP
  have hg : Nat.gcd (r + 1) (q.p ^ q.exponent + 1) = 1 := by
    rw [hqp, hqe, show (2 : ℕ) ^ 1 + 1 = 3 by norm_num]
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hr3)
  refine ⟨HyperInv.of_mulEquiv (e.trans (primeFormPEquivGramSU h (by omega) hg))
    (hyperInv_gramSU h (by rw [hqp, hqe]; norm_num) (by omega)),
    fun α hα => mem_range_conj_of_mulEquiv e ?_⟩
  exact mem_innU_two h hqp hqe (by omega) hr3 _ (by rw [← map_pow, hα, map_one])

theorem card_le_three_mul_innU_eight (h : UnitaryFieldData ℓ f L) (hℓ : ℓ = 2) (hf : f = 3) {n : ℕ}
    (hn : 4 ≤ n) (hn3 : ¬ 3 ∣ n)
    (D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))))
    (hD : IsElemAbelian 3 D) : Nat.card D ≤ 3 * Nat.card ↥(D ⊓ CFSG.RankThree.PartOne.innU h n) := by
  subst hℓ hf
  classical
  haveI : Finite L := h.finite
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) :=
    MulEquiv.finite_left
  have hn3' : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 3 = 2) := by omega
  have hker := ker_primeFormFieldFactor h isPrimeFormGram_one hn3' hq
  have hcard : Nat.card (RingAut L) = 6 :=
    (card_ringAut_and_isCyclic Nat.prime_two L (h.card.trans (by norm_num))).1
  haveI : Finite (RingAut L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let πD := (primeFormFieldFactor h isPrimeFormGram_one hn3' hq).comp D.subtype
  have hkerD : πD.ker.map D.subtype ≤ D ⊓ CFSG.RankThree.PartOne.innU h n := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn3' hq Nat.prime_three
      ?_ ?_ (hD.2 x x.2)⟩
    · intro hdvd
      exact hn3 (hdvd.trans (Nat.gcd_dvd_left _ _))
    · rw [← hker, MonoidHom.mem_ker]
      exact hx
  have hrange : Nat.card πD.range ≤ 3 := by
    have hp3 : IsPGroup 3 πD.range := by
      rintro ⟨_, x, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      have hx3 : x ^ 3 = 1 := Subtype.ext (hD.2 _ x.2)
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hx3, map_one]
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card πD.range ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> norm_num at hlt
    have := Nat.le_of_dvd (by norm_num) ((Nat.pow_dvd_pow 3 hk2).trans hdvd)
    norm_num at this
  have h1 := Subgroup.card_mul_index πD.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card πD.ker ≤ Nat.card ↥(D ⊓ CFSG.RankThree.PartOne.innU h n) := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact Subgroup.card_le_of_le hkerD
  calc Nat.card D = Nat.card πD.ker * Nat.card πD.range := h1.symm
    _ ≤ Nat.card ↥(D ⊓ CFSG.RankThree.PartOne.innU h n) * 3 := Nat.mul_le_mul h2 hrange
    _ = 3 * Nat.card ↥(D ⊓ CFSG.RankThree.PartOne.innU h n) := mul_comm _ _

@[expose] def IsUnitaryEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ (r : ℕ) (q : TauCeti.PrimePower), 3 ≤ r ∧ ¬ 3 ∣ r + 1 ∧ q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA r q

theorem unitaryEight_model {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hr : 3 ≤ r) (hr3 : ¬ 3 ∣ r + 1) (hqp : q.p = 2) (hqe : q.exponent = 3) {S : Type} [Group S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    HyperInv S ∧ ∀ D : Subgroup (MulAut S), IsElemAbelian 3 D →
      Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : S →* MulAut S).range) := by
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) L) : Matrix (Fin (r + 1)) (Fin (r + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  haveI : CharP L 2 := hqp ▸ h.charP
  haveI : Finite L := h.finite
  haveI : Finite (primeFormP h ((1 : GL (Fin (r + 1)) L) : Matrix (Fin (r + 1)) (Fin (r + 1)) L)) :=
    inferInstance
  have hg : Nat.gcd (r + 1) (q.p ^ q.exponent + 1) = 1 := by
    rw [hqp, hqe, show (2 : ℕ) ^ 3 + 1 = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hr3))
  exact ⟨HyperInv.of_mulEquiv (e.trans (primeFormPEquivGramSU h (by omega) hg))
    (hyperInv_gramSU h (by rw [hqp, hqe]; norm_num) (by omega)),
    card_le_three_mul_inner_of_mulEquiv e fun D hD =>
      card_le_three_mul_innU_eight h hqp hqe (by omega) hr3 D hD⟩

end Unitary

section UnitaryOuter

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Chevalley

variable {L : Type} [Field L]

theorem exists_fixInv_of_fieldHom_mem (h : UnitaryFieldData 2 3 L) {n : ℕ} (hn : 4 ≤ n)
    (hg : Nat.gcd n (2 ^ 3 + 1) = 1)
    (hconj : Function.Injective (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
      MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))))
    {σ : L ≃+* L} (hσ : orderOf σ = 3)
    (hσout : primeFormFieldHom h isPrimeFormGram_one σ ∉
      (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
        MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))).range)
    {D : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))}
    (hD : IsElemAbelian 3 D) (hσD : primeFormFieldHom h isPrimeFormGram_one σ ∈ D)
    (hD3 : Nat.card D ≤ 3 * Nat.card ↥(D ⊓
      (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
        MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))).range)) :
    ∃ E : Subgroup (MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))), E ≤ D ∧
      Nat.card D ≤ 3 * Nat.card E ∧
      ∃ t : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), t ≠ 1 ∧ t * t = 1 ∧
        ∀ φ ∈ E, φ t = t := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : CharP L 2 := h.charP
  haveI : Finite L := h.finite
  have hn1 : 1 ≤ n := by omega
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))) :=
    MulEquiv.finite_left
  set P := primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hPdef
  set SU := gramSU h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hSUdef
  set fσ := primeFormFieldHom h isPrimeFormGram_one σ with hfσ
  have hbot : normOneScalars h SU n = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ ((CFSG.RankThree.Classical.card_normOneScalars_one h hn1).trans hg)
  let π : ↥SU →* P := QuotientGroup.mk' _
  have hπ : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hbot
  let c : ↥SU →* MulAut P := MulAut.conj.comp π
  have hc : Function.Injective c := hconj.comp hπ
  set E₀ : Subgroup ↥SU := (D ⊓ (MulAut.conj : P →* MulAut P).range).comap c with hE₀
  have hmap : E₀.map c = D ⊓ (MulAut.conj : P →* MulAut P).range := by
    refine Subgroup.map_comap_eq_self fun x hx => ?_
    obtain ⟨y, rfl⟩ := hx.2
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨s, rfl⟩
  have hE₀c : Nat.card E₀ = Nat.card ↥(D ⊓ (MulAut.conj : P →* MulAut P).range) := by
    rw [← hmap, Subgroup.card_map_of_injective hc]
  have hE₀el : IsElemAbelian 3 E₀ := isElemAbelian_comap_of_injective hc (elem_mono hD inf_le_left)
  have hcomm : ∀ φ ∈ D, Commute fσ φ := fun φ hφ =>
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hσD⟩ ⟨φ, hφ⟩)
  have hfix : ∀ a ∈ E₀, glAut σ (a : GL (Fin n) L) = a := by
    intro a ha
    have h1 : MulAut.conj (fσ (π a)) = MulAut.conj (π a) := by
      have h2 : MulAut.conj (fσ (π a)) = fσ * MulAut.conj (π a) * fσ⁻¹ := by
        ext x
        simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, map_mul, map_inv,
          MulEquiv.apply_symm_apply]
      rw [h2]
      have h3 : MulAut.conj (π a) = c a := rfl
      rw [h3, (hcomm _ ha.1).eq, mul_inv_cancel_right]
    have h4 : π (primeFormFieldSU h isPrimeFormGram_one σ a) = π a := by
      have h5 : fσ (π a) = π (primeFormFieldSU h isPrimeFormGram_one σ a) :=
        primeFormFieldAut_mk h isPrimeFormGram_one σ a
      rw [← h5]
      exact hconj h1
    exact congrArg Subtype.val (hπ h4)
  have h₀ : UnitaryFieldData 2 (3 / 3) ↥(fixSubfield σ) :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three (by norm_num) hσ
  have hbar : ∀ x : ↥(fixSubfield σ), (h₀.bar x : L) = h.bar x :=
    CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h Nat.prime_three (by norm_num) hσ
  haveI : CharP ↥(fixSubfield σ) 2 := h₀.charP
  let ιS := CFSG.RankThree.Classical.subfieldSU h h₀ hbar n
  have hιS : Function.Injective ιS := CFSG.RankThree.Classical.subfieldSU_injective h h₀ hbar n
  have hE₀ι : E₀ ≤ ιS.range := by
    intro a ha
    obtain ⟨g₀, hg₀⟩ := CFSG.RankThree.Classical.exists_subfieldGL_eq_of_fixed n (hfix a ha)
    have hg₀SU : g₀ ∈ gramSU h₀ ((1 : GL (Fin n) ↥(fixSubfield σ)) :
        Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) :=
      CFSG.RankThree.Classical.mem_gramSU_of_subfieldGL h n h₀ hbar (by rw [hg₀]; exact a.2)
    exact ⟨⟨g₀, hg₀SU⟩, Subtype.ext hg₀⟩
  set E₀' := E₀.comap ιS with hE₀'
  have hE₀'c : Nat.card E₀' = Nat.card E₀ := by
    rw [← Subgroup.card_map_of_injective hιS, Subgroup.map_comap_eq_self hE₀ι]
  have hE₀'el : IsElemAbelian 3 E₀' := isElemAbelian_comap_of_injective hιS hE₀el
  obtain ⟨H', hH'E, hH'c, t₀, ht₀1, ht₀2, ht₀H⟩ : ∃ H' : Subgroup ↥(gramSU h₀ ((1 : GL (Fin n)
      ↥(fixSubfield σ)) : Matrix (Fin n) (Fin n) ↥(fixSubfield σ))), H' ≤ E₀' ∧
      Nat.card E₀' ≤ 3 * Nat.card H' ∧ ∃ t₀ : ↥(gramSU h₀ ((1 : GL (Fin n) ↥(fixSubfield σ)) :
        Matrix (Fin n) (Fin n) ↥(fixSubfield σ))), t₀ ≠ 1 ∧ t₀ * t₀ = 1 ∧
        ∀ x ∈ H', x * t₀ = t₀ * x := by
    obtain ⟨k, hk⟩ := GL83.CompFam.exists_card_eq_pow hE₀'el
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · obtain ⟨t, htSU, ht2, htns, -⟩ :=
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.exists_swap_involution h₀
          (n := n) (by omega) 1 (one_mem _)
      refine ⟨⊥, bot_le, ?_, ⟨t, htSU⟩, ?_, ?_, ?_⟩
      · rw [hk, hk0, Subgroup.card_bot]
        norm_num
      · intro h1
        apply htns 1
        rw [map_one]
        exact congrArg Subtype.val h1
      · apply Subtype.ext
        rw [Subgroup.coe_mul, ← sq, ht2, OneMemClass.coe_one]
      · intro x hx
        rw [Subgroup.mem_bot] at hx
        rw [hx, one_mul, mul_one]
    · obtain ⟨H', hH'E, hH'c, t₀, ht₀1, ht₀2, ht₀H⟩ :=
        hyperInv_gramSU h₀ (by norm_num) (by omega) E₀' k hE₀'el hk hk0
      exact ⟨H', hH'E, hH'c.le, t₀, ht₀1, ht₀2, ht₀H⟩
  have hfixι : ∀ g : ↥(gramSU h₀ ((1 : GL (Fin n) ↥(fixSubfield σ)) :
      Matrix (Fin n) (Fin n) ↥(fixSubfield σ))), fσ (π (ιS g)) = π (ιS g) := by
    intro g
    have h5 : fσ (π (ιS g)) = π (primeFormFieldSU h isPrimeFormGram_one σ (ιS g)) :=
      primeFormFieldAut_mk h isPrimeFormGram_one σ (ιS g)
    rw [h5]
    congr 1
    apply Subtype.ext
    apply Units.ext
    show ((ιS g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σ = (ιS g : GL (Fin n) L)
    rw [CFSG.RankThree.Classical.coe_subfieldSU, CFSG.RankThree.Classical.coe_subfieldGL]
    ext i j
    simp only [Matrix.map_apply]
    exact (mem_fixSubfield σ).1 (((g : GL (Fin n) ↥(fixSubfield σ)) :
      Matrix (Fin n) (Fin n) ↥(fixSubfield σ)) i j).2
  let ψ := c.comp ιS
  have hψ : Function.Injective ψ := hc.comp hιS
  set H'' := H'.map ψ with hH''
  have hH''D : H'' ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hH'E hx).1
  have hH''inn : H'' ≤ (MulAut.conj : P →* MulAut P).range := by
    rintro _ ⟨x, -, rfl⟩
    exact ⟨π (ιS x), rfl⟩
  set E := Subgroup.zpowers fσ ⊔ H'' with hEdef
  have hED : E ≤ D := sup_le (Subgroup.zpowers_le.2 hσD) hH''D
  set t : P := π (ιS t₀) with htdef
  refine ⟨E, hED, ?_, t, ?_, ?_, ?_⟩
  ·
    have hH''c : Nat.card H'' = Nat.card H' := Subgroup.card_map_of_injective hψ
    have hidx3 : 3 ≤ H''.relIndex E := by
      have hdvd : H''.relIndex E ∣ Nat.card E := Subgroup.relIndex_dvd_card _ _
      have hEp : IsPGroup 3 E := (elem_mono hD hED).isPGroup
      obtain ⟨m, hm⟩ := hEp.exists_card_eq
      rw [hm] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
      have hne : H''.relIndex E ≠ 1 := by
        intro h1
        have hle := (Subgroup.relIndex_eq_one).1 h1
        exact hσout (hH''inn (hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers fσ))))
      rw [hj] at hne ⊢
      have : j ≠ 0 := by
        rintro rfl
        exact hne (pow_zero 3)
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.2 this)
    have hcardE : 3 * Nat.card H'' ≤ Nat.card E := by
      have h := Subgroup.relIndex_mul_card H'' E
      rw [inf_of_le_left (le_sup_right : H'' ≤ E)] at h
      rw [← h]
      exact Nat.mul_le_mul_right _ hidx3
    rw [hH''c] at hcardE
    rw [← hE₀c, ← hE₀'c] at hD3
    omega
  · intro h1
    apply ht₀1
    exact hιS (hπ (h1.trans (map_one π).symm) |>.trans (map_one ιS).symm)
  · rw [← map_mul, ← map_mul, ht₀2, map_one, map_one]
  ·
    have hstab : E ≤ MulAction.stabilizer (MulAut P) t := by
      refine sup_le (Subgroup.zpowers_le.2 ?_) ?_
      · exact hfixι t₀
      · rintro _ ⟨x, hx, rfl⟩
        show MulAut.conj (π (ιS x)) t = t
        rw [MulAut.conj_apply, htdef, ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul,
          ht₀H x hx, mul_inv_cancel_right]
    intro φ hφ
    exact hstab hφ

theorem hyperInvOut_unitaryEight {ℓ f : ℕ} (h : UnitaryFieldData ℓ f L) (hℓ : ℓ = 2) (hf : f = 3) {n : ℕ}
    (hn : 4 ≤ n) (hn3 : ¬ 3 ∣ n)
    (hconj : Function.Injective (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
      MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)))) :
    HyperInvOut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
  subst hℓ hf
  classical
  intro D hD hDout
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite L := h.finite
  have hn3' : 3 ≤ n := by omega
  have hq : ¬(n = 3 ∧ 2 ^ 3 = 2) := by omega
  have hg : Nat.gcd n (2 ^ 3 + 1) = 1 := by
    rw [show (2 : ℕ) ^ 3 + 1 = 3 ^ 2 by norm_num]
    exact Nat.Coprime.pow_right 2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hn3))
  haveI : (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
      MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  set Θ := primeFormFieldFactor h isPrimeFormGram_one hn3' hq with hΘ
  have hkerΘ := ker_primeFormFieldFactor h isPrimeFormGram_one hn3' hq
  obtain ⟨a, haD, hain⟩ := Set.not_subset.1 hDout
  have ha3 : a ^ 3 = 1 := hD.2 a haD
  have haout : a ∉ primeFormD h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := fun hD' =>
    hain (CFSG.RankThree.PartOne.pElement_mem_inner_of_not_dvd_gcd h hn3' hq Nat.prime_three
      (fun hdvd => hn3 (hdvd.trans (Nat.gcd_dvd_left _ _))) hD' ha3)
  set σ := Θ a with hσdef
  have hσ1 : σ ≠ 1 := fun h1 => haout (by rw [← hkerΘ]; exact h1)
  have hσ3 : σ ^ 3 = 1 := by rw [hσdef, ← map_pow, ha3, map_one]
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have ha1 : a ≠ 1 := fun h1 => hσ1 (by rw [hσdef, h1, map_one])
  have haord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3' hq Nat.prime_three
      (by norm_num) (by norm_num) a haord σ rfl hσord
  set γ := primeFormConjHom h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) M with hγ
  set D' := D.map (MulAut.conj γ⁻¹).toMonoidHom with hD'
  have hσD' : primeFormFieldHom h isPrimeFormGram_one σ ∈ D' :=
    ⟨a, haD, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hM]⟩
  have hD'el : IsElemAbelian 3 D' := CFSG.SectionRank.isElemAbelian_map hD _
  have hσout : primeFormFieldHom h isPrimeFormGram_one σ ∉
      (MulAut.conj : primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) →*
        MulAut (primeFormP h ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))).range := by
    intro hin
    apply hain
    have : a = γ * primeFormFieldHom h isPrimeFormGram_one σ * γ⁻¹ := by
      rw [← hM]
      group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance _ hin γ
  obtain ⟨E', hE'D', hE'c, t, ht1, ht2, htE'⟩ :=
    exists_fixInv_of_fieldHom_mem h hn hg hconj hσord hσout hD'el hσD'
      (card_le_three_mul_innU_eight h rfl rfl hn hn3 D' hD'el)
  refine ⟨E'.map (MulAut.conj γ).toMonoidHom, ?_, ?_, γ t, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hE'D' hx
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.conj_apply]
    have : γ * (γ⁻¹ * y * γ⁻¹⁻¹) * γ⁻¹ = y := by group
    rw [this]
    exact hy
  · rw [Subgroup.card_map_of_injective (MulAut.conj γ).injective]
    have h1 : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective (MulAut.conj γ⁻¹).injective
    rw [← h1]
    exact hE'c
  · intro h1
    apply ht1
    have h2 := congrArg γ.symm h1
    rwa [MulEquiv.symm_apply_apply, map_one] at h2
  · rw [← map_mul, ht2, map_one]
  · rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, htE' x hx]

theorem unitaryEight_hyperInvOut {r : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hr : 3 ≤ r) (hr3 : ¬ 3 ∣ r + 1) (hqp : q.p = 2)
    (hqe : q.exponent = 3) {S : Type} [Group S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group)
    (hconjS : Function.Injective (MulAut.conj : S →* MulAut S)) : HyperInvOut S := by
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := r + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (r + 1)) L) : Matrix (Fin (r + 1)) (Fin (r + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  have hconjP : Function.Injective (MulAut.conj : primeFormP h ((1 : GL (Fin (r + 1)) L) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) L) →* MulAut (primeFormP h ((1 : GL (Fin (r + 1)) L) :
        Matrix (Fin (r + 1)) (Fin (r + 1)) L))) := by
    intro x y hxy
    have h1 := congrArg (MulAut.congr e.symm) hxy
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at h1
    exact e.symm.injective (hconjS h1)
  exact HyperInvOut.of_mulEquiv e (hyperInvOut_unitaryEight h hqp hqe (by omega) hr3 hconjP)

end UnitaryOuter

section Hyper

variable {X : Type} [Group X] [Finite X]

theorem exists_le_centGenI_of_inv {E K : Subgroup X} (hEel : IsElemAbelian 3 E)
    {d : TauCeti.ValidLieTypeIndex} (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hFA : F ≤ InputsSeitz3.autIm E K) {k : ℕ} (hFk : Nat.card F = 3 ^ k)
    (hk : 1 ≤ k) {t : ↥K} (ht1 : t ≠ 1) (ht2 : t * t = 1) (htF : ∀ φ ∈ F, φ t = t) :
    ∃ E₂ : Subgroup X, E₂ ≤ E ∧ Nat.card E₂ = 3 ^ k ∧
      E₂ ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧ K ≤ centGenI 3 E₂ K := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E₂ : Subgroup X := InputsSeitz3.autPre E K F with hE₂
  have hE₂E : E₂ ≤ E := InputsSeitz3.autPre_le E K F
  have hE₂N : E₂ ≤ Subgroup.normalizer (K : Set X) := by
    rintro _ ⟨n, -, rfl⟩
    exact n.2
  have hE₂C : E₂ ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf_right _ hE₂E).trans hEC.le)
  have hE₂card : Nat.card E₂ = 3 ^ k := (InputsSeitz3.card_autPre hEC hFA).trans hFk
  have hAF : InputsSeitz3.autIm E₂ K = F := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨n, hn, rfl⟩
      have hn' : (n : X) ∈ InputsSeitz3.autPre E K F := Subgroup.mem_subgroupOf.1 hn
      unfold InputsSeitz3.autPre at hn'
      obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.1 hn'
      have hmn' : m = n := Subtype.ext hmn
      rw [← hmn']
      exact (Subgroup.mem_inf.1 hm).2
    · rw [InputsSeitz3.card_autIm hE₂N hE₂C, hE₂card, hFk]
  have hFel : IsElemAbelian 3 F := hAF ▸ InputsSeitz3.isElemAbelian_autIm (elem_mono hEel hE₂E) K
  have hF0 : F ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hFk
    have := Nat.one_lt_pow (by omega : k ≠ 0) (by norm_num : 1 < 3)
    omega
  have hU : ∃ U : Subgroup ↥K, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ F, ∀ u ∈ U, φ u ∈ U := by
    refine ⟨Subgroup.zpowers t, ?_, ?_, ?_⟩
    · rwa [Ne, Subgroup.zpowers_eq_bot]
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1, pow_one]
    · intro φ hφ u hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      rw [map_zpow, htF φ hφ]
      exact Subgroup.zpow_mem_zpowers t j
  have hgen := seitzHyperGamma_eq_top_of_seitz2313Even seitz2313Even_holds Nat.prime_three
    (by norm_num) d ⟨eK⟩ hs hFel hF0 hU
  exact ⟨E₂, hE₂E, hE₂card, hE₂C,
    InputsSeitz3.le_centGenI_of_autIm hE₂N hE₂C (by rw [hAF]; exact hgen)⟩

theorem le_glbCore_of_e9_inv {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    {d : TauCeti.ValidLieTypeIndex} (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥)
    {E : Subgroup X} (hEB : E ≤ B) (hEC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hFA : F ≤ InputsSeitz3.autIm E K) (hF9 : Nat.card F = 3 ^ 2)
    {t : ↥K} (ht1 : t ≠ 1) (ht2 : t * t = 1) (htF : ∀ φ ∈ F, φ t = t) :
    K ≤ GLBCore 3 2 B := by
  obtain ⟨E₂, hE₂E, hE₂card, hE₂C, hcg⟩ :=
    exists_le_centGenI_of_inv (elem_mono hB hEB) hs eK hEC hFA hF9 (by norm_num) ht1 ht2 htF
  exact InputsSeitz3.le_glbCore_of_centGenI_central Nat.prime_three hB (hE₂E.trans hEB) inf_le_left
    inf_le_right (le_bot_iff.1 ((inf_le_inf_left _ inf_le_right).trans hE₂C.le)) hC
    (by rw [hE₂card]) hcg

theorem le_glbCore_of_e27_inv {B K : Subgroup X} (hB : IsElemAbelian 3 B)
    {d : TauCeti.ValidLieTypeIndex} (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    {E : Subgroup X} (hEB : E ≤ B) (hEC : E ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    {F : Subgroup (MulAut ↥K)} (hFA : F ≤ InputsSeitz3.autIm E K) (hF27 : Nat.card F = 3 ^ 3)
    {t : ↥K} (ht1 : t ≠ 1) (ht2 : t * t = 1) (htF : ∀ φ ∈ F, φ t = t) :
    K ≤ GLBCore 3 2 B := by
  obtain ⟨E₂, hE₂E, hE₂card, -, hcg⟩ :=
    exists_le_centGenI_of_inv (elem_mono hB hEB) hs eK hEC hFA hF27 (by norm_num) ht1 ht2 htF
  exact InputsSeitz3.le_glbCore_of_centGenI Nat.prime_three (hE₂E.trans hEB)
    (elem_mono (elem_mono hB hEB) hE₂E) (by rw [hE₂card]) hcg

theorem le_glbCore_of_hyperInv {B : Subgroup X} (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center ↥K = ⊥)
    (hinn : ∀ α : MulAut ↥K, α ^ 3 = 1 → α ∈ (MulAut.conj : ↥K →* MulAut ↥K).range)
    (hhyp : HyperInv ↥K) : K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hconj := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  have hE' : ∀ {E : Subgroup X} {k : ℕ}, E ≤ B → E ≤ Subgroup.normalizer (K : Set X) →
      E ⊓ Subgroup.centralizer (K : Set X) = ⊥ → Nat.card E = 3 ^ k →
      Nat.card ((InputsSeitz3.autIm E K).comap (MulAut.conj : ↥K →* MulAut ↥K)) = 3 ^ k ∧
        IsElemAbelian 3 ((InputsSeitz3.autIm E K).comap (MulAut.conj : ↥K →* MulAut ↥K)) ∧
        ((InputsSeitz3.autIm E K).comap MulAut.conj).map MulAut.conj = InputsSeitz3.autIm E K := by
    intro E k hEB hEN hEC hEc
    have hAel := InputsSeitz3.isElemAbelian_autIm (elem_mono hB hEB) K
    have hmap : ((InputsSeitz3.autIm E K).comap MulAut.conj).map MulAut.conj = InputsSeitz3.autIm E K :=
      Subgroup.map_comap_eq_self fun α hα => hinn α (hAel.2 α hα)
    refine ⟨?_, isElemAbelian_comap_of_injective hconj hAel, hmap⟩
    rw [← (InputsSeitz3.card_autIm hEN hEC).trans hEc]
    conv_rhs => rw [← hmap]
    rw [Subgroup.card_map_of_injective hconj]
  have hcore' : ∀ {E : Subgroup X} {k : ℕ}, E ≤ B → E ≤ Subgroup.normalizer (K : Set X) →
      E ⊓ Subgroup.centralizer (K : Set X) = ⊥ → Nat.card E = 3 ^ k → 1 ≤ k →
      ∃ F : Subgroup (MulAut ↥K), F ≤ InputsSeitz3.autIm E K ∧ Nat.card F = 3 ^ (k - 1) ∧
        ∃ t : ↥K, t ≠ 1 ∧ t * t = 1 ∧ ∀ φ ∈ F, φ t = t := by
    intro E k hEB hEN hEC hEc hk
    obtain ⟨hE'c, hE'el, hmap⟩ := hE' hEB hEN hEC hEc
    obtain ⟨H, hHE, hHc, t, ht1, ht2, htH⟩ := hhyp _ k hE'el hE'c hk
    refine ⟨H.map MulAut.conj, hmap ▸ Subgroup.map_mono hHE, ?_, t, ht1, ht2, ?_⟩
    · rw [Subgroup.card_map_of_injective hconj]
      rw [hE'c] at hHc
      have h3 : 3 ^ k = 3 * 3 ^ (k - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3] at hHc
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num) hHc).symm
    · rintro _ ⟨x, hx, rfl⟩
      show MulAut.conj x t = t
      rw [MulAut.conj_apply, htH x hx, mul_inv_cancel_right]
  have hCel : IsElemAbelian 3 (cen B K) := elem_mono hB inf_le_left
  have hSel : IsElemAbelian 3 (stab B K) := elem_mono hB inf_le_left
  obtain ⟨c, hc⟩ := GL83.CompFam.exists_card_eq_pow hCel
  obtain ⟨s, hs'⟩ := GL83.CompFam.exists_card_eq_pow hSel
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hsmall' : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card (cen B K) < Nat.card (stab B K) := hsmall
  rw [hc, hs', ← pow_add] at hsmall'
  have hsm : CFSG.Open.pRank 3 B - 2 + c < s := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hsmall'
  have hsB : s ≤ CFSG.Open.pRank 3 B := by
    have h1 : Nat.card (stab B K) ≤ Nat.card B := Subgroup.card_le_of_le inf_le_left
    rw [hs', hBc] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  by_cases hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥
  · have hc0 : c = 0 := by
      have h1 : Nat.card (cen B K) = 1 := by
        show Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) = 1
        rw [hC, Subgroup.card_bot]
      rw [hc] at h1
      exact (Nat.pow_eq_one.1 h1).resolve_left (by norm_num)
    have hs4 : 4 ≤ s := by
      by_contra hs3
      obtain ⟨E, hEN, hEC, hEc⟩ := InputsSeitz3.exists_faithful hp hB (k := 3)
        (by rw [hc, hs', hc0, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
      obtain ⟨hE'c, hE'el, -⟩ := hE' (hEN.trans inf_le_left) (hEN.trans inf_le_right) hEC hEc
      have hK3 : 3 ≤ CFSG.Open.pRank 3 K := by
        refine CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.map_subtype_le _)
          (CFSG.SectionRank.isElemAbelian_map hE'el K.subtype) ?_
        rw [Subgroup.card_map_of_injective K.subtype_injective, hE'c]
      obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) := by
        by_contra hall
        push Not at hall
        have h1 : stab B K = B := inf_eq_left.2 hall
        have h2 := hs'
        rw [h1, hBc] at h2
        have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h2
        omega
      have hb3 : b ^ 3 = 1 := hB.2 b hbB
      have hbb : b * b ∉ Subgroup.normalizer (K : Set X) := by
        intro h
        apply hbN
        have h2 : b * b * (b * b) = b := by
          have h4 : b * b * (b * b) = b ^ 3 * b := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
          rw [h4, hb3, one_mul]
        rw [← h2]
        exact Subgroup.mul_mem _ h h
      have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥K) := by
        rw [hZ, Subgroup.card_bot]
        norm_num
      have h3 := InputsSeitz6.three_mul_pRank_le_of_not_mem hp hK hZ3 hbN hbb
      omega
    obtain ⟨E, hEN, hEC, hEc⟩ := InputsSeitz3.exists_faithful hp hB (k := 4)
      (by rw [hc, hs', hc0, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨F, hFA, hFc, t, ht1, ht2, htF⟩ :=
      hcore' (hEN.trans inf_le_left) (hEN.trans inf_le_right) hEC hEc (by norm_num)
    exact le_glbCore_of_e27_inv hB hs eK (hEN.trans inf_le_left) hEC hFA hFc ht1 ht2 htF
  · obtain ⟨E, hEN, hEC, hEc⟩ := InputsSeitz3.exists_faithful hp hB (k := 3)
      (by rw [hc, hs', ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega))
    obtain ⟨F, hFA, hFc, t, ht1, ht2, htF⟩ :=
      hcore' (hEN.trans inf_le_left) (hEN.trans inf_le_right) hEC hEc (by norm_num)
    exact le_glbCore_of_e9_inv hB hs eK hC (hEN.trans inf_le_left) hEC hFA hFc ht1 ht2 htF

theorem le_glbCore_of_spTwo (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsSpTwoIndex d) : K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨n, q, hn, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    have hZp := Inputs245b.isPGroup_center_of_component hp hcore hK
    have hdvd := InputsSeitz6.dvd_card_of_isPGroup hZp hZ
    have hpd : 3 ≠ (TauCeti.LieTypeIndex.B n q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_B, hqp]
      decide
    exact CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp (by norm_num)
      hK.2.2 ⟨.B n q, hv⟩ e hpd hdvd
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨e₂⟩ := nonempty_typeBGroupEquiv_spTwo hn q hv hqp hqe
  let ψ : ↥K ≃* ↥(CFSG.Open.StatedSp n (ZMod 2)) := eK.trans e₂
  refine le_glbCore_of_hyperInv hB hB4 hrk hK hsmall (d := ⟨.B n q, hv⟩) hqp eK hZ
    (fun α _ => mem_range_conj_of_mulEquiv ψ ?_) (HyperInv.of_mulEquiv ψ (hyperInv_statedSp (F := ZMod 2) (by omega)))
  obtain ⟨g, hg⟩ := all_inner_spTwo hn (MulAut.congr ψ α)
  exact ⟨g, hg.symm⟩

theorem le_glbCore_of_unitaryTwo (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsUnitaryTwoIndex d) : K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨r, q, hr, hr3, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    have hZp := Inputs245b.isPGroup_center_of_component hp hcore hK
    have hdvd := InputsSeitz6.dvd_card_of_isPGroup hZp hZ
    have hpd : 3 ≠ (TauCeti.LieTypeIndex.twistedA r q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedA, hqp]
      decide
    exact hr3 (CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp (by norm_num)
      hK.2.2 ⟨.twistedA r q, hv⟩ e hpd hdvd).1
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group :=
    (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨hhyp, hinn⟩ := unitaryTwo_model hv hr hr3 hqp hqe eK
  exact le_glbCore_of_hyperInv hB hB4 hrk hK hsmall (d := ⟨.twistedA r q, hv⟩) ⟨hqp, hr⟩ eK hZ hinn hhyp

theorem le_glbCore_of_hyperInvOut {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X} {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hout : ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) (hHO : HyperInvOut ↥K) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hAel := InputsSeitz3.isElemAbelian_autIm hB K
  have hAc : Nat.card (InputsSeitz3.autIm B K) = 3 ^ CFSG.Open.pRank 3 B :=
    (InputsSeitz3.card_autIm hBN hC).trans (GL83.PiGen.card_eq_pow_pRank hB)
  obtain ⟨E, hEA, hEc, t, ht1, ht2, htE⟩ := hHO _ hAel hout
  obtain ⟨j, hj⟩ := CFSG.Open.IsElemAbelian.isPGroup (elem_mono hAel hEA) |>.exists_card_eq
  have hj3 : 3 ≤ j := by
    rw [hAc, hj, ← pow_succ'] at hEc
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hEc
    omega
  obtain ⟨F, hFc, -, hFE⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp (n := 3) (H := ⊥) (L := E)
    (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hj]; exact Nat.pow_dvd_pow 3 hj3) bot_le
  obtain ⟨E₂, hE₂B, hE₂c, -, hcg⟩ := exists_le_centGenI_of_inv hB hs eK hC (hFE.trans hEA) hFc
    (by norm_num) ht1 ht2 fun φ hφ => htE φ (hFE hφ)
  exact InputsSeitz3.le_glbCore_of_centGenI hp hE₂B (elem_mono hB hE₂B) (by rw [hE₂c]) hcg

theorem le_glbCore_of_hyperInv_outer {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (eK : ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) (hZ : Subgroup.center ↥K = ⊥)
    (hout : ∀ D : Subgroup (MulAut ↥K), IsElemAbelian 3 D →
      Nat.card D ≤ 3 * Nat.card ↥(D ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range))
    (hhyp : HyperInv ↥K) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥)
    (hfour : CFSG.Open.pRank 3 B = 4 → B ≤ Subgroup.normalizer (K : Set X) →
      InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hconj := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  have hinner : ∀ {E : Subgroup X} {k : ℕ}, E ≤ B → E ≤ Subgroup.normalizer (K : Set X) →
      E ⊓ Subgroup.centralizer (K : Set X) = ⊥ → Nat.card E = 3 ^ k →
      ∃ ρ : ℕ, k ≤ ρ + 1 ∧ ∃ E' : Subgroup ↥K, IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ ρ ∧
        E'.map MulAut.conj ≤ InputsSeitz3.autIm E K ∧
        (InputsSeitz3.autIm E K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range → ρ = k) := by
    intro E k hEB hEN hEC hEc
    have hDel := InputsSeitz3.isElemAbelian_autIm (elem_mono hB hEB) K
    have hDc : Nat.card (InputsSeitz3.autIm E K) = 3 ^ k := (InputsSeitz3.card_autIm hEN hEC).trans hEc
    have hD₀el : IsElemAbelian 3 (InputsSeitz3.autIm E K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range) :=
      elem_mono hDel inf_le_left
    obtain ⟨ρ, hρ⟩ := GL83.CompFam.exists_card_eq_pow hD₀el
    have hmap : ((InputsSeitz3.autIm E K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range).comap MulAut.conj).map
        MulAut.conj = InputsSeitz3.autIm E K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range :=
      Subgroup.map_comap_eq_self inf_le_right
    have hE'c : Nat.card ((InputsSeitz3.autIm E K ⊓ (MulAut.conj : ↥K →* MulAut ↥K).range).comap
        (MulAut.conj : ↥K →* MulAut ↥K)) = 3 ^ ρ := by
      rw [← hρ, ← hmap, Subgroup.card_map_of_injective hconj, hmap]
    refine ⟨ρ, ?_, _, isElemAbelian_comap_of_injective hconj hD₀el, hE'c, hmap.le.trans inf_le_left,
      fun hin => ?_⟩
    · have h1 := hout _ hDel
      rw [hDc, hρ, ← pow_succ'] at h1
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    · rw [inf_eq_left.2 hin, hDc] at hρ
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hρ).symm
  have hSel : IsElemAbelian 3 (stab B K) := elem_mono hB inf_le_left
  obtain ⟨s, hs'⟩ := GL83.CompFam.exists_card_eq_pow hSel
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hcen1 : Nat.card (cen B K) = 1 := by
    show Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) = 1
    rw [hC, Subgroup.card_bot]
  have hsmall' : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card (cen B K) < Nat.card (stab B K) := hsmall
  rw [hcen1, mul_one, hs'] at hsmall'
  have hsm : CFSG.Open.pRank 3 B - 2 < s := (Nat.pow_lt_pow_iff_right (by norm_num)).1 hsmall'
  have hsB : s ≤ CFSG.Open.pRank 3 B := by
    have h1 : Nat.card (stab B K) ≤ Nat.card B := Subgroup.card_le_of_le inf_le_left
    rw [hs', hBc] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  by_cases hBN : B ≤ Subgroup.normalizer (K : Set X)
  · obtain ⟨ρ, hρk, E', hE'el, hE'c, hE'A, hρin⟩ := hinner le_rfl hBN hC hBc
    have hρ4 : 4 ≤ ρ := by
      by_cases hm4 : CFSG.Open.pRank 3 B = 4
      · rw [hρin (hfour hm4 hBN)]
        omega
      · omega
    obtain ⟨H, hHE, hHc, t, ht1, ht2, htH⟩ := hhyp E' ρ hE'el hE'c (by omega)
    have hHc' : Nat.card H = 3 ^ (ρ - 1) := by
      rw [hE'c, show ρ = ρ - 1 + 1 by omega, pow_succ'] at hHc
      exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) hHc).symm
    have hFA : H.map MulAut.conj ≤ InputsSeitz3.autIm B K := (Subgroup.map_mono hHE).trans hE'A
    have hFc : Nat.card (H.map (MulAut.conj : ↥K →* MulAut ↥K)) = 3 ^ (ρ - 1) := by
      rw [Subgroup.card_map_of_injective hconj, hHc']
    have htF : ∀ φ ∈ H.map (MulAut.conj : ↥K →* MulAut ↥K), φ t = t := by
      rintro _ ⟨x, hx, rfl⟩
      show MulAut.conj x t = t
      rw [MulAut.conj_apply, htH x hx, mul_inv_cancel_right]
    obtain ⟨E₂, hE₂B, hE₂c, -, hcg⟩ :=
      exists_le_centGenI_of_inv hB hs eK hC hFA hFc (by omega) ht1 ht2 htF
    exact InputsSeitz3.le_glbCore_of_centGenI hp hE₂B (elem_mono hB hE₂B)
      (by rw [hE₂c]; exact Nat.pow_le_pow_right (by norm_num) (by omega)) hcg
  ·
    exfalso
    have hs1 : s + 1 = CFSG.Open.pRank 3 B := by
      have hlt : s < CFSG.Open.pRank 3 B := by
        rcases hsB.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hBN
          have h1 : stab B K = B :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hs', hBc, h])
          rw [← h1]
          exact inf_le_right
      omega
    obtain ⟨E, hEN, hEC, hEc⟩ := InputsSeitz3.exists_faithful hp hB (k := s)
      (by rw [hcen1, mul_one, hs'])
    obtain ⟨ρ, hρk, E', hE'el, hE'c, -, -⟩ :=
      hinner (hEN.trans inf_le_left) (hEN.trans inf_le_right) hEC hEc
    obtain ⟨b, hbB, hbN⟩ : ∃ b ∈ B, b ∉ Subgroup.normalizer (K : Set X) := by
      by_contra hall
      push Not at hall
      exact hBN hall
    have hb3 : b ^ 3 = 1 := hB.2 b hbB
    have hbb : b * b ∉ Subgroup.normalizer (K : Set X) := by
      intro h
      apply hbN
      have h2 : b * b * (b * b) = b := by
        have h4 : b * b * (b * b) = b ^ 3 * b := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        rw [h4, hb3, one_mul]
      rw [← h2]
      exact Subgroup.mul_mem _ h h
    have hEZ : ∀ x ∈ E'.map K.subtype, (∀ y ∈ K, x * y = y * x) → x = 1 := by
      rintro _ ⟨x, -, rfl⟩ hxc
      have hx : x ∈ Subgroup.center ↥K :=
        Subgroup.mem_center_iff.2 fun y => Subtype.ext (hxc y y.2).symm
      rw [hZ, Subgroup.mem_bot] at hx
      rw [hx, map_one]
    have h3 := three_mul_le_of_not_mem hp hK (Subgroup.map_subtype_le E')
      (CFSG.SectionRank.isElemAbelian_map hE'el K.subtype) hEZ
      (by rw [Subgroup.card_map_of_injective K.subtype_injective, hE'c]) hbN hbb
    rw [← hrk] at h3
    omega

theorem not_coverIndex_of_eight {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSpEightIndex d ∨ IsUnitaryEightIndex d) :
    ¬ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 := by
  rcases hd with ⟨n, q, -, -, -, hdq⟩ | ⟨r, q, -, hr3, -, -, hdq⟩
  · rw [hdq]
    exact id
  · rw [hdq]
    exact fun h => hr3 h.1

theorem le_glbCore_of_spEight (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsSpEightIndex d) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hd' := hd
  obtain ⟨n, q, hn, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    have hZp := Inputs245b.isPGroup_center_of_component hp hcore hK
    have hdvd := InputsSeitz6.dvd_card_of_isPGroup hZp hZ
    have hpd : 3 ≠ (TauCeti.LieTypeIndex.B n q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_B, hqp]
      decide
    exact not_coverIndex_of_eight (Or.inl hd')
      (CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp (by norm_num)
        hK.2.2 ⟨.B n q, hv⟩ e hpd hdvd)
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.B n q, hv⟩).Group := (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨F, _, _, _, hF, ⟨e₂⟩⟩ := exists_typeBGroupEquiv_sp hn q hv hqp
  rw [hqe] at hF
  let ψ : ↥K ≃* ↥(CFSG.Open.StatedSp n F) := eK.trans e₂
  let ψ' : ↥K ≃* CFSG.Open.StatedProj (CFSG.Open.StatedSp n F) := ψ.trans (projEquivSp (by omega)).symm
  haveI : Finite (CFSG.Open.StatedProj (CFSG.Open.StatedSp n F)) := inferInstance
  have hconjK := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  have hconjP : Function.Injective (MulAut.conj : CFSG.Open.StatedProj (CFSG.Open.StatedSp n F) →*
      MulAut (CFSG.Open.StatedProj (CFSG.Open.StatedSp n F))) := by
    intro x y hxy
    have h1 := congrArg (MulAut.congr ψ'.symm) hxy
    rw [CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj, CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj] at h1
    exact ψ'.symm.injective (hconjK h1)
  by_cases hcfg : CFSG.Open.pRank 3 B = 4 ∧ B ≤ Subgroup.normalizer (K : Set X) ∧
      ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range
  · exact le_glbCore_of_hyperInvOut hB hB4 (d := ⟨.B n q, hv⟩) hqp eK hC hcfg.2.1 hcfg.2.2
      (HyperInvOut.of_mulEquiv ψ' (hyperInvOut_sp hF hn hconjP))
  · exact le_glbCore_of_hyperInv_outer hB hB4 hrk hK hsmall (d := ⟨.B n q, hv⟩) hqp eK hZ
      (card_le_three_mul_inner_of_mulEquiv ψ' fun D hD => card_le_three_mul_inner_sp hF hn D hD)
      (HyperInv.of_mulEquiv ψ (hyperInv_statedSp (by omega))) hC
      fun h4 hBN => by_contra fun hn' => hcfg ⟨h4, hBN, hn'⟩

theorem le_glbCore_of_unitaryEight (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsUnitaryEightIndex d) (hC : B ⊓ Subgroup.centralizer (K : Set X) = ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hd' := hd
  obtain ⟨r, q, hr, hr3, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hZ : Subgroup.center ↥K = ⊥ := by
    by_contra hZ
    have hZp := Inputs245b.isPGroup_center_of_component hp hcore hK
    have hdvd := InputsSeitz6.dvd_card_of_isPGroup hZp hZ
    have hpd : 3 ≠ (TauCeti.LieTypeIndex.twistedA r q).characteristic := by
      rw [TauCeti.LieTypeIndex.characteristic_twistedA, hqp]
      decide
    exact not_coverIndex_of_eight (Or.inr hd')
      (CFSG.LieType.SeitzGeneration.QuasiHigh.coverIndex_of_dvd_card_center hGM hp (by norm_num)
        hK.2.2 ⟨.twistedA r q, hv⟩ e hpd hdvd)
  let eK : ↥K ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group :=
    (InputsSeitz3.equivCenterQuot hZ).trans e
  obtain ⟨hhyp, hout⟩ := unitaryEight_model hv hr hr3 hqp hqe eK
  have hconjK := CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318E68Aux.conj_injective_of_center_eq_bot hZ
  by_cases hcfg : CFSG.Open.pRank 3 B = 4 ∧ B ≤ Subgroup.normalizer (K : Set X) ∧
      ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range
  · exact le_glbCore_of_hyperInvOut hB hB4 (d := ⟨.twistedA r q, hv⟩) ⟨hqp, hr⟩ eK hC hcfg.2.1 hcfg.2.2
      (unitaryEight_hyperInvOut hv hr hr3 hqp hqe eK hconjK)
  · exact le_glbCore_of_hyperInv_outer hB hB4 hrk hK hsmall (d := ⟨.twistedA r q, hv⟩) ⟨hqp, hr⟩ eK hZ
      hout hhyp hC fun h4 hBN => by_contra fun hn' => hcfg ⟨h4, hBN, hn'⟩

section Covers

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (isElemAbelian_autImage)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313InAux (StarConcl starConcl_of_congr)
open CFSG.HardMathSupport.Dickson.I271 (autImage)
open CFSG.HardMathSupport.Solomon.Coordinator (i271_exists_card_eq i271_isElemAbelian_of_le)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

theorem odd_card_center_of_core (hcore : GLAPPrimeCore 3 X = ⊥) {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    Odd (Nat.card (Subgroup.center ↥K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (Inputs245b.isPGroup_center_of_component Nat.prime_three hcore hK).exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem le_glbCore_of_star3 (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hstar : ∀ D : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), IsElemAbelian 3 D →
      Claims1310r.Star3Concl D)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hodd := odd_card_center_of_core hcore hK
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  obtain ⟨r, hr⟩ := i271_exists_card_eq hp hAel
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hB inf_le_left
  have hCc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) =
      3 ^ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    GL83.PiGen.card_eq_pow_pRank hCel
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hstab := card_stab_eq (B := B) hperf
  rw [inf_eq_left.2 hBN, hr, hCc, hBc, ← pow_add] at hstab
  have hm : CFSG.Open.pRank 3 B = r + CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) hstab
  have hc1 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 1 := by
    have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) ≠ 0 := by
      intro h0
      apply hC
      apply Subgroup.eq_bot_of_card_eq
      rw [hCc, h0, pow_zero]
    rw [hCc, inf_eq_left.2 hBN, hBc, ← pow_add] at hsmall
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hsmall
    omega
  obtain ⟨E, hEA, hEc, U, hU0, hU2, hUinv⟩ := hstar _ hAel
  have hEel : IsElemAbelian 3 E := i271_isElemAbelian_of_le hAel hEA
  obtain ⟨m₀, hm₀⟩ := i271_exists_card_eq hp hEel
  have hm₀2 : 2 ≤ m₀ := by
    rcases hEc with h | h
    · rw [hr, hm₀, ← pow_succ'] at h
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
      omega
    · rw [hm₀] at h
      by_contra hlt
      have : 3 ^ m₀ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  exact (le_gammaPrime_of_seitz_rank seitz2313Even_holds (k := 2) hperf hB hodd hs e hEA hEel hm₀
    (by omega) (by rw [hc1]; omega) ⟨U, hU0, hU2, hUinv⟩).trans (gammaPrimeIn_le_glbCore le_rfl B K)

theorem le_glbCore_of_starConcl {B K : Subgroup X} (hB : IsElemAbelian 3 B) (hK : IsComponentOf K ⊤)
    (hodd : Odd (Nat.card (Subgroup.center ↥K))) {d : TauCeti.ValidLieTypeIndex}
    (hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope d.1)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hstar : ∀ D : Subgroup (MulAut (↥K ⧸ Subgroup.center ↥K)), IsElemAbelian 3 D → StarConcl D) {r : ℕ}
    (hr : Nat.card (autImage B K) = 3 ^ r) (hr3 : 3 ≤ r)
    (h5 : 5 ≤ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) + r) :
    K ≤ GLBCore 3 2 B := by
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  obtain ⟨E₀, hE₀A, hrel, U, hU0, hU2, hUinv⟩ := hstar (autImage B K) hAel
  have hE₀el : IsElemAbelian 3 E₀ := i271_isElemAbelian_of_le hAel hE₀A
  obtain ⟨m₀, hm₀⟩ := i271_exists_card_eq Nat.prime_three hE₀el
  have h1 := Subgroup.relIndex_mul_card E₀ (autImage B K)
  rw [inf_of_le_left hE₀A, hm₀, hr] at h1
  have h3 : 3 ^ r ≤ 3 ^ (m₀ + 2) := by
    calc 3 ^ r = E₀.relIndex (autImage B K) * 3 ^ m₀ := h1.symm
      _ ≤ 9 * 3 ^ m₀ := Nat.mul_le_mul_right _ hrel
      _ = 3 ^ (m₀ + 2) := by ring
  have h4 : r ≤ m₀ + 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h3
  exact (le_gammaPrime_of_seitz_rank seitz2313Even_holds (k := 2) hperf hB hodd hs e hE₀A hE₀el hm₀
    (by omega) (by omega) ⟨U, hU0, hU2, hUinv⟩).trans (gammaPrimeIn_le_glbCore le_rfl B K)

@[expose] def IsUSixIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ (q.exponent = 1 ∨ q.exponent = 3) ∧ d.1 = .twistedA 5 q

@[expose] def IsUThreeEightIndex (d : TauCeti.ValidLieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .twistedA 2 q

theorem unitarySix_star {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid)
    (hqp : q.p = 2) (hqe : q.exponent = 1 ∨ q.exponent = 3) {S : Type} [Group S] [Finite S]
    (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 5 q, hv⟩).Group) :
    (∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → StarConcl D) ∧
      (∀ D : Subgroup (MulAut S), IsElemAbelian 3 D → Claims1310r.Star3Concl D) := by
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 5 q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 5 + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (5 + 1)) L) : Matrix (Fin (5 + 1)) (Fin (5 + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  refine ⟨fun D hD => starConcl_of_congr e D ?_, fun D hD => Claims1310r.star3Concl_of_congr e D ?_⟩
  · rcases hqe with he | he
    · exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.starConcl_two h hqp he
        (by norm_num) _ (hD.map _)
    · exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Star2313UnitaryProof.starConcl_eight h hqp he
        (by norm_num) _ (hD.map _)
  · rcases hqe with he | he
    · exact Claims1310r.star3Concl_two h hqp he (by norm_num) _ (hD.map _)
    · exact Claims1310r.star3Concl_eight h hqp he (by norm_num) _ (hD.map _)

theorem le_glbCore_of_unitarySix (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X}
    (hB : IsElemAbelian 3 B) (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsUSixIndex d)
    (hcase : (B ≤ Subgroup.normalizer (K : Set X) ∧ B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨
      (B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧
        ((5 ≤ CFSG.Open.pRank 3 B ∧ B ≤ Subgroup.normalizer (K : Set X)) ∨ 6 ≤ CFSG.Open.pRank 3 B))) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨hstar, hstar3⟩ := unitarySix_star hv hqp hqe e
  have hs : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Seitz2313Cover.EvenScope (.twistedA 5 q) :=
    ⟨hqp, by norm_num⟩
  rcases hcase with ⟨hBN, hC⟩ | ⟨hC, hcase⟩
  · exact le_glbCore_of_star3 hcore hB hB4 hK hsmall hs e hstar3 hBN hC
  · have hperf : commutator ↥K = ⊤ := hK.2.2.1
    have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
    obtain ⟨r, hr⟩ := i271_exists_card_eq hp hAel
    have hc0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
      rw [hC]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.pRank_bot_eq_zero' hp
    have hstab := card_stab_eq (B := B) hperf
    rw [hr, hC, Subgroup.card_bot, mul_one] at hstab
    have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
    have hr1 : CFSG.Open.pRank 3 B - 1 ≤ r := by
      rw [hC, Subgroup.card_bot, mul_one, hstab] at hsmall
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hsmall
      omega
    have hr5 : 5 ≤ r := by
      rcases hcase with ⟨h5, hBN⟩ | h6
      · rw [inf_eq_left.2 hBN, hBc] at hstab
        have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hstab
        omega
      · omega
    exact le_glbCore_of_starConcl hB hK (odd_card_center_of_core hcore hK) hs e hstar hr (by omega)
      (by omega)

theorem card_le_27_of_unitaryThreeEight {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hqp : q.p = 2) (hqe : q.exponent = 3) {S : Type}
    [Group S] [Finite S] (eS : S ≃* (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)
    (D : Subgroup (MulAut S)) (hD : IsElemAbelian 3 D) : Nat.card D ≤ 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hℓ, hf, -, -⟩, L, _, _, hL, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv eS
  have h : UnitaryFieldData q.p q.exponent L := ⟨hℓ, hf, by rw [hL, ← pow_mul, mul_comm]⟩
  obtain ⟨eP⟩ := nonempty_primeFormP_mulEquiv h (isPrimeFormGram_one (n := 2 + 1) (K := L))
  let e : S ≃* primeFormP h ((1 : GL (Fin (2 + 1)) L) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) L) :=
    (eT.trans (unitaryPSUEquiv h (by omega)).symm).trans eP.symm
  haveI : Finite L := h.finite
  haveI : Finite (MulAut (primeFormP h ((1 : GL (Fin (2 + 1)) L) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) L))) :=
    MulEquiv.finite_left
  have hq : ¬(2 + 1 = 3 ∧ q.p ^ q.exponent = 2) := by
    rw [hqp, hqe]
    norm_num
  set D' := D.map (MulAut.congr e).toMonoidHom with hD'
  have hD'el : IsElemAbelian 3 D' := hD.map _
  have hD'c : Nat.card D' = Nat.card D := Subgroup.card_map_of_injective (MulAut.congr e).injective
  have hker := ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num : 3 ≤ 2 + 1) hq
  have hLc : Nat.card L = 2 ^ 6 := by rw [h.card, hqp, hqe]
  have h3 : 3 ∣ Nat.card Lˣ := by
    rw [Nat.card_units, hLc]
    norm_num
  have h9 := Claims1310r.card_le_nine_of_le_primeFormD_three h h3
    (D' ⊓ primeFormD h ((1 : GL (Fin (2 + 1)) L) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) L))
    (elem_mono hD'el inf_le_left) inf_le_right
  have hcard : Nat.card (RingAut L) = 6 :=
    (card_ringAut_and_isCyclic Nat.prime_two L (by rw [hLc])).1
  haveI : Finite (RingAut L) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  let πD := (primeFormFieldFactor h isPrimeFormGram_one (by norm_num : 3 ≤ 2 + 1) hq).comp D'.subtype
  have hrange : Nat.card πD.range ≤ 3 := by
    have hp3 : IsPGroup 3 πD.range := by
      rintro ⟨_, x, rfl⟩
      refine ⟨1, Subtype.ext ?_⟩
      have hx3 : x ^ 3 = 1 := Subtype.ext (hD'el.2 _ x.2)
      simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
      rw [← map_pow, hx3, map_one]
    obtain ⟨k, hk⟩ := hp3.exists_card_eq
    have hdvd : Nat.card πD.range ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card _
    rw [hk] at hdvd ⊢
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> norm_num at hlt
    have := Nat.le_of_dvd (by norm_num) ((Nat.pow_dvd_pow 3 hk2).trans hdvd)
    norm_num at this
  have hkerD : πD.ker.map D'.subtype ≤
      D' ⊓ primeFormD h ((1 : GL (Fin (2 + 1)) L) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) L) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    rw [← hker]
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hx)
  have h1 := Subgroup.card_mul_index πD.ker
  rw [Subgroup.index_ker] at h1
  have h2 : Nat.card πD.ker ≤ Nat.card ↥(D' ⊓
      primeFormD h ((1 : GL (Fin (2 + 1)) L) : Matrix (Fin (2 + 1)) (Fin (2 + 1)) L)) := by
    rw [← Subgroup.card_map_of_injective D'.subtype_injective]
    exact Subgroup.card_le_of_le hkerD
  rw [← hD'c, ← h1]
  calc Nat.card πD.ker * Nat.card πD.range ≤ 9 * 3 := Nat.mul_le_mul (h2.trans h9) hrange
    _ = 27 := by norm_num

end Covers

section U38

open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (isElemAbelian_autImage)
open CFSG.HardMathSupport.Dickson.I271 (autImage)
open CFSG.HardMathSupport.Solomon.Coordinator (i271_exists_card_eq i271_isElemAbelian_of_le)

theorem le_glbCore_of_unitaryThreeEight {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hB4 : 4 ≤ CFSG.Open.pRank 3 B) {K : Subgroup X} (hK : IsComponentOf K ⊤)
    (hsmall : 3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
      Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)))
    (d : TauCeti.ValidLieTypeIndex) (e : ↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : IsUThreeEightIndex d) (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    K ≤ GLBCore 3 2 B := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨q, hqp, hqe, hdq⟩ := hd
  obtain ⟨d0, hv⟩ := d
  simp only at hdq
  subst hdq
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hAel : IsElemAbelian 3 (autImage B K) := isElemAbelian_autImage hB
  obtain ⟨r, hr⟩ := i271_exists_card_eq hp hAel
  have hCel : IsElemAbelian 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    i271_isElemAbelian_of_le hB inf_le_left
  have hCc : Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) =
      3 ^ CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    GL83.PiGen.card_eq_pow_pRank hCel
  have hBc : Nat.card B = 3 ^ CFSG.Open.pRank 3 B := GL83.PiGen.card_eq_pow_pRank hB
  have hstab := card_stab_eq (B := B) hperf
  rw [inf_eq_left.2 hBN, hr, hCc, hBc, ← pow_add] at hstab
  have hm : CFSG.Open.pRank 3 B = r + CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) hstab
  have hc1 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) ≤ 1 := by
    rw [hCc, inf_eq_left.2 hBN, hBc, ← pow_add] at hsmall
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).1 hsmall
    omega
  have h27 := card_le_27_of_unitaryThreeEight hv hqp hqe e (autImage B K) hAel
  rw [hr] at h27
  have hr3 : r ≤ 3 := by
    by_contra hlt
    have : 3 ^ 4 ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hC : B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := by
    intro hC
    have h0 : CFSG.Open.pRank 3 (B ⊓ Subgroup.centralizer (K : Set X)) = 0 := by
      rw [hC]
      exact CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.pRank_bot_eq_zero' hp
    omega
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hC
  have hz1' : z ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hA27 : 27 ≤ Nat.card (autImage B K) := by
    rw [hr]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨⟨hℓ, hf, -, -⟩, F, _, _, hF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
  have hFd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData q.p q.exponent F :=
    ⟨hℓ, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hgam := Claims1310r.le_gammaPrime_of_u38 hK.2.2 hB hBN hz.1 hz1' hz.2 hA27 hFd hqp hqe
    (eT.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hFd (by norm_num)).symm)
  exact hgam.trans (gammaPrimeIn_le_glbCore le_rfl B K)

end U38

end Hyper

section Cover

variable {X : Type} [Group X] [Finite X]

theorem cen_ne_bot_of_center_ne_bot (hcore : GLAPPrimeCore 3 X = ⊥) {B K : Subgroup X}
    (hB : IsElemAbelian 3 B) (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X))
    (hK : IsComponentOf K ⊤) (hZ : Subgroup.center ↥K ≠ ⊥)
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  set Z : Subgroup X := (Subgroup.center ↥K).map K.subtype with hZdef
  have hZp : IsPGroup 3 Z := (Inputs245b.isPGroup_center_of_component hp hcore hK).map K.subtype
  have hZne : Z ≠ ⊥ := fun h =>
    hZ ((Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h)
  have hZC : Z ≤ Subgroup.centralizer (K : Set X) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨k, hk⟩)
  have hBZ : B ≤ Subgroup.normalizer (Z : Set X) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨hbz, hbzc⟩ := InputsSeitz.conj_mem_center (hBN hb) hz
      exact ⟨_, hbzc, rfl⟩
    · rintro ⟨w, hw, hwx⟩
      obtain ⟨hbw, hbwc⟩ := InputsSeitz.conj_mem_center (Subgroup.inv_mem _ (hBN hb)) hw
      refine ⟨_, hbwc, ?_⟩
      have hwx' : (w : X) = b * x * b⁻¹ := hwx
      show b⁻¹ * (w : X) * b⁻¹⁻¹ = x
      rw [hwx']
      group
  have hPp : IsPGroup 3 (B ⊔ Z : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' (CFSG.Open.IsElemAbelian.isPGroup hB) hZp hBZ
  obtain ⟨x, hxZ, hxB, hx1⟩ : ∃ x ∈ Z, x ∈ Subgroup.centralizer (B : Set X) ∧ x ≠ 1 := by
    haveI : Group.IsNilpotent ↥(B ⊔ Z : Subgroup X) := hPp.isNilpotent
    have hPN : B ⊔ Z ≤ Subgroup.normalizer (Z : Set X) := sup_le hBZ Subgroup.le_normalizer
    haveI : (Z.subgroupOf (B ⊔ Z)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2 hPN
    have hZP : Z.subgroupOf (B ⊔ Z) ≠ ⊥ := by
      intro h
      apply hZne
      rw [eq_bot_iff]
      intro z hz
      have h1 : (⟨z, Subgroup.mem_sup_right hz⟩ : ↥(B ⊔ Z : Subgroup X)) ∈ Z.subgroupOf (B ⊔ Z) := hz
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (congrArg Subtype.val h1)
    have h := Group.IsNilpotent.inf_center_ne_bot_of_normal hZP
    obtain ⟨⟨⟨x, hxP⟩, hxin⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 h
    obtain ⟨hxZ, hxc⟩ := Subgroup.mem_inf.1 hxin
    refine ⟨x, hxZ, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have := Subgroup.mem_center_iff.1 hxc ⟨b, Subgroup.mem_sup_left hb⟩
      exact congrArg Subtype.val this
    · intro h1
      apply hx1
      apply Subtype.ext
      apply Subtype.ext
      exact h1
  have hW : Z ⊓ Subgroup.centralizer (B : Set X) ≠ ⊥ := by
    intro h
    have : x ∈ Z ⊓ Subgroup.centralizer (B : Set X) := ⟨hxZ, hxB⟩
    rw [h, Subgroup.mem_bot] at this
    exact hx1 this
  have hWp : IsPGroup 3 (Z ⊓ Subgroup.centralizer (B : Set X) : Subgroup X) := hZp.to_le inf_le_left
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 (InputsSeitz6.dvd_card_of_isPGroup hWp hW)
  have hyZ : (y : X) ∈ Z := y.2.1
  have hyB' : (y : X) ∈ Subgroup.centralizer (B : Set X) := y.2.2
  have hy3 : orderOf (y : X) = 3 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyB : (y : X) ∈ B := by
    by_contra hyB
    have hYc : Nat.card (Subgroup.zpowers (y : X)) = 3 ^ 1 := by rw [Nat.card_zpowers, hy3, pow_one]
    have hYel : IsElemAbelian 3 (Subgroup.zpowers (y : X)) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
      · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
        apply Subtype.ext
        show (a : X) * b = b * a
        rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy3, pow_orderOf_eq_one,
          one_zpow]
    have hcomm : ∀ g ∈ Subgroup.zpowers (y : X), ∀ b ∈ B, g * b = b * g := by
      intro g hg b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_iff.1 hyB' b hb).symm i)).eq
    have hd : Subgroup.zpowers (y : X) ⊓ B = ⊥ := by
      have hdvd : Nat.card ↥(Subgroup.zpowers (y : X) ⊓ B) ∣ 3 := by
        rw [← pow_one 3, ← hYc]
        exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).1 hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        have hle : Subgroup.zpowers (y : X) ≤ B := by
          have heq : Subgroup.zpowers (y : X) ⊓ B = Subgroup.zpowers (y : X) :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hYc, h3, pow_one])
          rw [← heq]
          exact inf_le_right
        exact hyB (hle (Subgroup.mem_zpowers _))
    have h1 := InputsSeitz.add_le_pRank_of_commute hp hYel hB hcomm hd hYc
      (GL83.PiGen.card_eq_pow_pRank hB)
    omega
  intro h
  have hyc : (y : X) ∈ B ⊓ Subgroup.centralizer (K : Set X) := ⟨hyB, hZC hyZ⟩
  rw [h, Subgroup.mem_bot] at hyc
  rw [hyc, orderOf_one] at hy3
  omega

end Cover

section Normalizes

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_of_i112 (T : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (TL : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2)
    (TT : CFSG.HardMathSupport.Solomon.Coordinator.Tables112Types) (hKX : CFSG.Open.IsKGroup X)
    (hcore : GLAPPrimeCore 3 X = ⊥) {B : Subgroup X} (hB : IsElemAbelian 3 B)
    (hrk : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X)) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (haut : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K))) :
    B ≤ Subgroup.normalizer (K : Set X) := by
  by_contra hnK
  have hr : GLATwoLocalRank 3 X ≤ CFSG.Open.pRank 3 B := by
    rw [hrk]
    show sSup {k | ∃ H : Subgroup X, CFSG.Open.IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} ≤ _
    refine csSup_le' ?_
    rintro k ⟨H, -, rfl⟩
    exact CFSG.SectionRank.pRank_mono (by norm_num) le_top
  obtain ⟨-, -, h2, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.i112f_core T TL TT hKX Nat.prime_three
    (by norm_num) hcore hB hr
    (CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112b_glaPComponent_of_isComponentOf hcore hK) hnK
  omega

end Normalizes

@[expose] def Input23_19ExcThreeRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → GLAPPrimeCore 3 X = ⊥ →
    ∀ B : Subgroup X, IsElemAbelian 3 B → 4 ≤ CFSG.Open.pRank 3 B →
      CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 (⊤ : Subgroup X) →
    ∀ K : Subgroup X, IsComponentOf K ⊤ →
      3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥K)) →
      3 ^ (CFSG.Open.pRank 3 B - 2) * Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set X)) <
        Nat.card ↥(B ⊓ Subgroup.normalizer (K : Set X)) →
      B ≤ Subgroup.normalizer (K : Set X) →
      ∀ d : TauCeti.ValidLieTypeIndex,
        Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group) →
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.ExcIndex 3 d.1 → d.1 ≠ .tits →
        ¬ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsL2EightIndex d.1 →
        ¬ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Index d.1 →
        ¬ IsSpTwoIndex d → ¬ IsUnitaryTwoIndex d →
        ¬ IsSpEightIndex d → ¬ IsUnitaryEightIndex d → ¬ IsUThreeEightIndex d →
        (IsUSixIndex d → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧ CFSG.Open.pRank 3 B = 4) →
        (CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsSixIndex d.1 →
          ¬ InputsSeitz3.autIm B K ≤ (MulAut.conj : ↥K →* MulAut ↥K).range) →
        ((Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 ∧
            B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨
          B ⊓ Subgroup.centralizer (K : Set X) = ⊥) →
        K ≤ GLBCore 3 2 B

theorem spTwo_or_unitaryTwo_of_d2Exc {d : TauCeti.ValidLieTypeIndex}
    (h : CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1)
    (hexc : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.ExcIndex 3 d.1) (htits : d.1 ≠ .tits)
    (hl28 : ¬ CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsL2EightIndex d.1) :
    IsSpTwoIndex d ∨ IsUnitaryTwoIndex d := by
  rcases h with ⟨-, ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ | ⟨q, hq2, hq3, hd⟩ |
      ⟨q, hq2, hq3, hd | hd⟩ | hd⟩ | ⟨h5, -⟩
  · exact absurd (by rw [hd]; exact ⟨rfl, hq2, hq3⟩) hl28
  · exfalso
    rw [hd] at hexc
    rcases hexc with h | ⟨-, h⟩
    · exact h
    · simp only [CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsL2EightIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Index,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Bal209TwoIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsTwistedE6FourIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsSixIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsF4EightIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.IsD4FourIndex,
        CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.FourIndex, or_false] at h
      rcases h with ⟨h1, -⟩ | ⟨-, n, hn, h3⟩
      · omega
      · have : 3 ^ 2 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
        omega
  · exact Or.inr ⟨3, q, le_rfl, by norm_num, hq2, hq3, hd⟩
  · exact Or.inl ⟨3, q, le_rfl, hq2, hq3, hd⟩
  · exact Or.inl ⟨4, q, by norm_num, hq2, hq3, hd⟩
  · exact absurd hd htits
  · omega

section Assemble

theorem input23_19ExcThree_of_rest (hGA : CFSG.Open.GriessAllModelsStatement)
    (hGM : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (T : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112)
    (TL : CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableL2)
    (TT : CFSG.HardMathSupport.Solomon.Coordinator.Tables112Types)
    (h : Input23_19ExcThreeRest) : InputsSeitz6.Input23_19ExcThree := by
  intro X _ _ hKX hcore B hB hB4 hrk K hK haut hsmall d hd hexc htits hl28 hsix hrest
  obtain ⟨e⟩ := hd
  have hBN : B ≤ Subgroup.normalizer (K : Set X) := le_normalizer_of_i112 T TL TT hKX hcore hB hrk hK haut
  by_cases hg : CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318Index d.1
  · exact le_glbCore_of_gen2318 hGA hKX hB hB4 hrk hK hsmall d e hg
  by_cases hs6 : IsSpTwoIndex d
  · exact le_glbCore_of_spTwo hGM hcore hB hB4 hrk hK hsmall d e hs6
  by_cases hu4 : IsUnitaryTwoIndex d
  · exact le_glbCore_of_unitaryTwo hGM hcore hB hB4 hrk hK hsmall d e hu4
  have hrest' : (Subgroup.center ↥K ≠ ⊥ ∧ CFSG.LieType.SeitzGeneration.QuasiHigh.CoverIndex 3 d.1 ∧
      B ⊓ Subgroup.centralizer (K : Set X) ≠ ⊥) ∨ B ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
    rcases hrest with ⟨hZ, hcov⟩ | hC | hD
    · exact Or.inl ⟨hZ, hcov, cen_ne_bot_of_center_ne_bot hcore hB hrk hK hZ hBN⟩
    · exact Or.inr hC
    · exact ((spTwo_or_unitaryTwo_of_d2Exc hD hexc htits hl28).elim hs6 hu4).elim
  have hC8 : IsSpEightIndex d ∨ IsUnitaryEightIndex d → B ⊓ Subgroup.centralizer (K : Set X) = ⊥ :=
    fun h8 => hrest'.resolve_left fun hc => not_coverIndex_of_eight h8 hc.2.1
  by_cases hS8 : IsSpEightIndex d
  · exact le_glbCore_of_spEight hGM hcore hB hB4 hrk hK hsmall d e hS8 (hC8 (Or.inl hS8))
  by_cases hU8 : IsUnitaryEightIndex d
  · exact le_glbCore_of_unitaryEight hGM hcore hB hB4 hrk hK hsmall d e hU8 (hC8 (Or.inr hU8))
  by_cases hU38 : IsUThreeEightIndex d
  · exact le_glbCore_of_unitaryThreeEight hB hB4 hK hsmall d e hU38 hBN
  by_cases hU6 : IsUSixIndex d ∧ ¬ (B ⊓ Subgroup.centralizer (K : Set X) = ⊥ ∧ CFSG.Open.pRank 3 B = 4)
  · refine le_glbCore_of_unitarySix hcore hB hB4 hK hsmall d e hU6.1 ?_
    rcases hrest' with ⟨-, -, hC⟩ | hC
    · exact Or.inl ⟨hBN, hC⟩
    · have h4 : CFSG.Open.pRank 3 B ≠ 4 := fun h4 => hU6.2 ⟨hC, h4⟩
      exact Or.inr ⟨hC, Or.inl ⟨by omega, hBN⟩⟩
  · exact h X hKX hcore B hB hB4 hrk K hK haut hsmall hBN d ⟨e⟩ hexc htits hl28 hg hs6 hu4 hS8 hU8 hU38
      (fun h6 => by_contra fun hn => hU6 ⟨h6, hn⟩) hsix hrest'

end Assemble

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz7

end

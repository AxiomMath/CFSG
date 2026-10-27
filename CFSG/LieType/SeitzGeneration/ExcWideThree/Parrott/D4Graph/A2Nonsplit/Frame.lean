module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Split.SplitPair
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix5

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

section Hom

variable {K : Type} [Field K] {H : Type*} [Group H]

theorem commute_of_gens_right (f' : SL2 K →* H) {x : H} (hu : ∀ c, Commute x (f' (uSL c)))
    (hv : ∀ c, Commute x (f' (vSL c))) (A' : SL2 K) : Commute x (f' A') := by
  set S := (Subgroup.centralizer ({x} : Set H)).comap f'
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← sl2_closure_upper_lower, Subgroup.closure_le]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · show f' (uSL t) ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hu t).symm.eq
    · show f' (vSL t) ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hv t).symm.eq
  have hA : A' ∈ S := by rw [hS]; trivial
  exact (Subgroup.mem_centralizer_singleton_iff.1 hA).symm

theorem commute_of_gens (f f' : SL2 K →* H)
    (huu : ∀ c c', Commute (f (uSL c)) (f' (uSL c')))
    (huv : ∀ c c', Commute (f (uSL c)) (f' (vSL c')))
    (hvu : ∀ c c', Commute (f (vSL c)) (f' (uSL c')))
    (hvv : ∀ c c', Commute (f (vSL c)) (f' (vSL c'))) (A A' : SL2 K) :
    Commute (f A) (f' A') := by
  refine (commute_of_gens_right f (x := f' A') (fun c => ?_) (fun c => ?_) A).symm
  · exact (commute_of_gens_right f' (huu c) (huv c) A').symm
  · exact (commute_of_gens_right f' (hvu c) (hvv c) A').symm

end Hom

section D4


variable {K : Type} [Field K]

local notation "𝕩" => xPar (rootOperatorFamily Tag.D4)

@[expose] def IsFrameHom (f : SL2 K →* ↥(adjointGroup Tag.D4 K)) (β : Fin Tag.D4.rank → ℤ) :
    Prop :=
  (∃ ε : K, ε * ε = 1 ∧ ∀ c, f (uSL c) = 𝕩 β (ε * c)) ∧
    ∃ ε : K, ε * ε = 1 ∧ ∀ c, f (vSL c) = 𝕩 (-β) (ε * c)

@[expose] def fβ₁ : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 0]

@[expose] def fβ₂ : Fin Tag.D4.rank → ℤ := ![1, 0, 1, 1]

@[expose] def fβ₃ : Fin Tag.D4.rank → ℤ := ![0, 1, 1, 1]

@[expose] noncomputable def nW (i : Fin Tag.D4.rank) : ↥(adjointGroup Tag.D4 K) :=
  CFSG.LieType.Steinberg.weylElement 𝕩 i (1 : Kˣ)

variable (K) in
@[expose] noncomputable def frameK₁ : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
  (MulAut.conj (nW (K := K) ⟨0, by decide⟩ * nW ⟨1, by decide⟩)).toMonoidHom.comp
    (sl2At K ⟨2, by decide⟩)

variable (K) in
@[expose] noncomputable def frameK₃ : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
  (d4Graph K 1).toMonoidHom.comp (frameK₁ K)

variable (K) in
@[expose] noncomputable def frameK₂ : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
  (d4Graph K 1).toMonoidHom.comp (frameK₃ K)

theorem frameK₁_apply (A : SL2 K) :
    frameK₁ K A = nW ⟨0, by decide⟩ * nW ⟨1, by decide⟩ * sl2At K ⟨2, by decide⟩ A *
      (nW ⟨0, by decide⟩ * nW ⟨1, by decide⟩)⁻¹ :=
  rfl

theorem frameK₃_apply (A : SL2 K) : frameK₃ K A = d4Graph K 1 (frameK₁ K A) := rfl

theorem frameK₂_apply (A : SL2 K) : frameK₂ K A = d4Graph K 1 (frameK₃ K A) := rfl

theorem d4Graph_one_pow_three : d4Graph K 1 ^ 3 = 1 := by
  rw [pow_succ, pow_two, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]

theorem d4Graph_one_three (x : ↥(adjointGroup Tag.D4 K)) :
    d4Graph K 1 (d4Graph K 1 (d4Graph K 1 x)) = x := by
  have h := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ x)
    (d4Graph_one_pow_three (K := K))
  simpa [pow_succ, MulAut.mul_apply] using h

theorem d4Graph_one_frameK₂ (A : SL2 K) : d4Graph K 1 (frameK₂ K A) = frameK₁ K A :=
  d4Graph_one_three _

theorem rhoL_neg (v : Fin Tag.D4.rank → ℤ) : rhoL (-v) = -rhoL v := by
  funext i
  simp [rhoL, permLattice]

theorem IsFrameHom.d4Graph {f : SL2 K →* ↥(adjointGroup Tag.D4 K)} {β : Fin Tag.D4.rank → ℤ}
    (hβ : IsRoot Tag.D4 β) (hf : IsFrameHom f β) :
    IsFrameHom ((d4Graph K 1).toMonoidHom.comp f) (rhoL β) := by
  obtain ⟨⟨ε, hε, hu⟩, ⟨ε', hε', hv⟩⟩ := hf
  obtain ⟨δ, hδ, hγ⟩ := d4Graph_one_xPar (K := K) hβ
  obtain ⟨δ', hδ', hγ'⟩ := d4Graph_one_xPar (K := K) (IsRoot.neg hβ)
  refine ⟨⟨δ * ε, ?_, fun c => ?_⟩, ⟨δ' * ε', ?_, fun c => ?_⟩⟩
  · calc δ * ε * (δ * ε) = (δ * δ) * (ε * ε) := by ring
      _ = 1 := by rw [hδ, hε, one_mul]
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hu, hγ]
    rw [mul_assoc]
  · calc δ' * ε' * (δ' * ε') = (δ' * δ') * (ε' * ε') := by ring
      _ = 1 := by rw [hδ', hε', one_mul]
  · simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, hv, hγ',
      rhoL_neg]
    rw [mul_assoc]

theorem isFrameHom_frameK₁ : IsFrameHom (frameK₁ K) fβ₁ := by
  have he2 := isRoot_single Tag.D4 (⟨2, by decide⟩ : Fin Tag.D4.rank)
  have he2' := isRoot_neg_single Tag.D4 (⟨2, by decide⟩ : Fin Tag.D4.rank)
  obtain ⟨e1, he1, h1⟩ := exists_weyl_conj (K := K) ⟨1, by decide⟩ he2
  obtain ⟨e0, he0, h0⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ (he2.reflect ⟨1, by decide⟩)
  obtain ⟨f1, hf1, g1⟩ := exists_weyl_conj (K := K) ⟨1, by decide⟩ he2'
  obtain ⟨f0, hf0, g0⟩ := exists_weyl_conj (K := K) ⟨0, by decide⟩ (he2'.reflect ⟨1, by decide⟩)
  have r1 : reflect Tag.D4 ⟨0, by decide⟩ (reflect Tag.D4 ⟨1, by decide⟩
      (Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1)) = fβ₁ := by decide
  have r2 : reflect Tag.D4 ⟨0, by decide⟩ (reflect Tag.D4 ⟨1, by decide⟩
      (-Pi.single (⟨2, by decide⟩ : Fin Tag.D4.rank) 1)) = -fβ₁ := by decide
  refine ⟨⟨e0 * e1, ?_, fun c => ?_⟩, ⟨f0 * f1, ?_, fun c => ?_⟩⟩
  · calc e0 * e1 * (e0 * e1) = (e0 * e0) * (e1 * e1) := by ring
      _ = 1 := by rw [he0, he1, one_mul]
  · rw [frameK₁_apply, ← xPar_single_eq_sl2At, mul_inv_rev,
      show nW ⟨0, by decide⟩ * nW ⟨1, by decide⟩ * 𝕩 (Pi.single ⟨2, by decide⟩ 1) c *
          ((nW ⟨1, by decide⟩)⁻¹ * (nW ⟨0, by decide⟩)⁻¹) =
        nW ⟨0, by decide⟩ * (nW ⟨1, by decide⟩ * 𝕩 (Pi.single ⟨2, by decide⟩ 1) c *
          (nW ⟨1, by decide⟩)⁻¹) * (nW (K := K) ⟨0, by decide⟩)⁻¹ by group]
    unfold nW
    rw [h1, h0, r1, ← mul_assoc]
  · calc f0 * f1 * (f0 * f1) = (f0 * f0) * (f1 * f1) := by ring
      _ = 1 := by rw [hf0, hf1, one_mul]
  · rw [frameK₁_apply, ← xPar_neg_single_eq_sl2At, mul_inv_rev,
      show nW ⟨0, by decide⟩ * nW ⟨1, by decide⟩ * 𝕩 (-Pi.single ⟨2, by decide⟩ 1) c *
          ((nW ⟨1, by decide⟩)⁻¹ * (nW ⟨0, by decide⟩)⁻¹) =
        nW ⟨0, by decide⟩ * (nW ⟨1, by decide⟩ * 𝕩 (-Pi.single ⟨2, by decide⟩ 1) c *
          (nW ⟨1, by decide⟩)⁻¹) * (nW (K := K) ⟨0, by decide⟩)⁻¹ by group]
    unfold nW
    rw [g1, g0, r2, ← mul_assoc]

theorem isFrameHom_frameK₃ : IsFrameHom (frameK₃ K) fβ₃ := by
  have hr : IsRoot Tag.D4 fβ₁ := by rw [isRoot_iff_mem_artifactRoots]; decide
  have e : rhoL fβ₁ = fβ₃ := by decide
  have := (isFrameHom_frameK₁ (K := K)).d4Graph hr
  rwa [e] at this

theorem isFrameHom_frameK₂ : IsFrameHom (frameK₂ K) fβ₂ := by
  have hr : IsRoot Tag.D4 fβ₃ := by rw [isRoot_iff_mem_artifactRoots]; decide
  have e : rhoL fβ₃ = fβ₂ := by decide
  have := (isFrameHom_frameK₃ (K := K)).d4Graph hr
  rwa [e] at this

theorem IsFrameHom.commute {f f' : SL2 K →* ↥(adjointGroup Tag.D4 K)}
    {β β' : Fin Tag.D4.rank → ℤ} (hf : IsFrameHom f β) (hf' : IsFrameHom f' β')
    (hβ : IsRoot Tag.D4 β) (hβ' : IsRoot Tag.D4 β') (h1 : β ≠ β') (h2 : β ≠ -β')
    (hpp : ¬IsRoot Tag.D4 (β + β')) (hpm : ¬IsRoot Tag.D4 (β + -β'))
    (hmp : ¬IsRoot Tag.D4 (-β + β')) (hmm : ¬IsRoot Tag.D4 (-β + -β')) (A A' : SL2 K) :
    Commute (f A) (f' A') := by
  obtain ⟨⟨ε, -, hu⟩, ⟨ε', -, hv⟩⟩ := hf
  obtain ⟨⟨δ, -, hu'⟩, ⟨δ', -, hv'⟩⟩ := hf'
  refine commute_of_gens f f' (fun c c' => ?_) (fun c c' => ?_) (fun c c' => ?_)
    (fun c c' => ?_) A A'
  · rw [hu, hu']
    exact CFSG.LieType.Steinberg.TwistedD4.commute_xPar hβ hβ' h1 h2 hpp _ _
  · rw [hu, hv']
    exact CFSG.LieType.Steinberg.TwistedD4.commute_xPar hβ (IsRoot.neg hβ') h2
      (fun h => h1 (h.trans (neg_neg β'))) hpm _ _
  · rw [hv, hu']
    exact CFSG.LieType.Steinberg.TwistedD4.commute_xPar (IsRoot.neg hβ) hβ'
      (fun h => h2 (neg_eq_iff_eq_neg.1 h)) (fun h => h1 (neg_inj.1 h)) hmp _ _
  · rw [hv, hv']
    exact CFSG.LieType.Steinberg.TwistedD4.commute_xPar (IsRoot.neg hβ) (IsRoot.neg hβ')
      (fun h => h1 (neg_inj.1 h)) (fun h => h2 (neg_inj.1 h)) hmm _ _

theorem frame_facts :
    IsRoot Tag.D4 fβ₁ ∧ IsRoot Tag.D4 fβ₂ ∧ IsRoot Tag.D4 fβ₃ ∧
    (∀ β ∈ ([fβ₁, fβ₂, fβ₃] : List (Fin Tag.D4.rank → ℤ)),
      ∀ β' ∈ ([fβ₁, fβ₂, fβ₃] : List (Fin Tag.D4.rank → ℤ)),
      β ≠ β' → β ≠ -β' ∧ ¬IsRoot Tag.D4 (β + β') ∧ ¬IsRoot Tag.D4 (β + -β') ∧
        ¬IsRoot Tag.D4 (-β + β') ∧ ¬IsRoot Tag.D4 (-β + -β')) := by
  simp only [isRoot_iff_mem_artifactRoots]
  decide

theorem longOrthRoots_eq : longOrthRoots = [fβ₁, fβ₂, fβ₃] := rfl

theorem frameK_commute (A A' : SL2 K) :
    Commute (frameK₁ K A) (frameK₃ K A') ∧ Commute (frameK₁ K A) (frameK₂ K A') ∧
      Commute (frameK₃ K A) (frameK₂ K A') := by
  obtain ⟨h1, h2, h3, h⟩ := frame_facts
  have c13 := h fβ₁ (by simp) fβ₃ (by simp) (by decide)
  have c12 := h fβ₁ (by simp) fβ₂ (by simp) (by decide)
  have c32 := h fβ₃ (by simp) fβ₂ (by simp) (by decide)
  exact ⟨isFrameHom_frameK₁.commute isFrameHom_frameK₃ h1 h3 (by decide) c13.1 c13.2.1
      c13.2.2.1 c13.2.2.2.1 c13.2.2.2.2 A A',
    isFrameHom_frameK₁.commute isFrameHom_frameK₂ h1 h2 (by decide) c12.1 c12.2.1
      c12.2.2.1 c12.2.2.2.1 c12.2.2.2.2 A A',
    isFrameHom_frameK₃.commute isFrameHom_frameK₂ h3 h2 (by decide) c32.1 c32.2.1
      c32.2.2.1 c32.2.2.2.1 c32.2.2.2.2 A A'⟩

theorem IsFrameHom.commute_sl2Two {f : SL2 K →* ↥(adjointGroup Tag.D4 K)}
    {β : Fin Tag.D4.rank → ℤ} (hf : IsFrameHom f β) (hβ : β ∈ longOrthRoots) (A A' : SL2 K) :
    Commute (f A) (sl2At K ⟨2, by decide⟩ A') := by
  obtain ⟨⟨ε, -, hu⟩, ⟨ε', -, hv⟩⟩ := hf
  obtain ⟨hβr, hβr', hp, hm, hp', hm', h1, h2, h1', h2'⟩ := longOrth_facts β hβ
  refine (commute_of_gens_right f (x := sl2At K ⟨2, by decide⟩ A') (fun c => ?_)
    (fun c => ?_) A).symm
  · rw [hu]
    exact (Parrott.D4Graph.commute_sl2Two hβr hp hm h1 h2 _ A').symm
  · rw [hv]
    exact (Parrott.D4Graph.commute_sl2Two hβr' hp' hm' h1' h2' _ A').symm

theorem frameK_commute_sl2Two (A A' : SL2 K) :
    Commute (frameK₁ K A) (sl2At K ⟨2, by decide⟩ A') ∧
      Commute (frameK₃ K A) (sl2At K ⟨2, by decide⟩ A') ∧
        Commute (frameK₂ K A) (sl2At K ⟨2, by decide⟩ A') :=
  ⟨isFrameHom_frameK₁.commute_sl2Two (by rw [longOrthRoots_eq]; simp) A A',
    isFrameHom_frameK₃.commute_sl2Two (by rw [longOrthRoots_eq]; simp) A A',
    isFrameHom_frameK₂.commute_sl2Two (by rw [longOrthRoots_eq]; simp) A A'⟩

theorem gammaP_apply_of_commute (B : SL2 K) {x : ↥(adjointGroup Tag.D4 K)}
    (hx : Commute (d4Graph K 1 x) (sl2At K ⟨2, by decide⟩ B)) :
    gammaP K B x = d4Graph K 1 x := by
  rw [gammaP, MulAut.mul_apply, MulAut.conj_apply, hx.symm.eq, mul_inv_cancel_right]

theorem gammaP_frameK₁ (B A : SL2 K) : gammaP K B (frameK₁ K A) = frameK₃ K A :=
  gammaP_apply_of_commute B (frameK_commute_sl2Two A B).2.1

theorem gammaP_frameK₃ (B A : SL2 K) : gammaP K B (frameK₃ K A) = frameK₂ K A :=
  gammaP_apply_of_commute B (frameK_commute_sl2Two A B).2.2

theorem gammaP_frameK₂ (B A : SL2 K) : gammaP K B (frameK₂ K A) = frameK₁ K A := by
  rw [gammaP_apply_of_commute B (by rw [d4Graph_one_frameK₂]; exact
    (frameK_commute_sl2Two A B).1), d4Graph_one_frameK₂]

@[expose] noncomputable def frameDiag (A : SL2 K) : ↥(adjointGroup Tag.D4 K) :=
  frameK₁ K A * frameK₃ K A * frameK₂ K A

theorem gammaP_frameDiag (B A : SL2 K) : gammaP K B (frameDiag A) = frameDiag A := by
  obtain ⟨c13, c12, -⟩ := frameK_commute (K := K) A A
  rw [frameDiag, map_mul, map_mul, gammaP_frameK₁, gammaP_frameK₃, gammaP_frameK₂, mul_assoc,
    ← c12.eq, ← mul_assoc, ← c13.eq]

variable (K) in
@[expose] noncomputable def frameDiagHom : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
  ((frameK₁ K).noncommCoprod ((frameK₃ K).noncommCoprod (frameK₂ K)
      (fun X Y => (frameK_commute X Y).2.2))
    (fun X p => ((frameK_commute X p.1).1).mul_right ((frameK_commute X p.2).2.1))).comp
    ((MonoidHom.id (SL2 K)).prod ((MonoidHom.id (SL2 K)).prod (MonoidHom.id (SL2 K))))

theorem frameDiagHom_apply (A : SL2 K) : frameDiagHom K A = frameDiag A := by
  change frameK₁ K A * (frameK₃ K A * frameK₂ K A) = frameDiag A
  rw [frameDiag, mul_assoc]

theorem frameDiag_mul (A A' : SL2 K) : frameDiag (A * A') = frameDiag A * frameDiag A' := by
  rw [← frameDiagHom_apply, ← frameDiagHom_apply, ← frameDiagHom_apply, map_mul]

theorem frameDiag_inv (A : SL2 K) : frameDiag A⁻¹ = (frameDiag A)⁻¹ := by
  rw [← frameDiagHom_apply, ← frameDiagHom_apply, map_inv]

theorem gammaP_one : gammaP K 1 = d4Graph K 1 := by
  rw [gammaP, map_one, map_one, one_mul]

theorem d4Graph_frameDiag (A : SL2 K) : d4Graph K 1 (frameDiag A) = frameDiag A := by
  rw [← gammaP_one]
  exact gammaP_frameDiag 1 A

theorem frameDiag_commute_sl2Two (A A' : SL2 K) :
    Commute (frameDiag A) (sl2At K ⟨2, by decide⟩ A') := by
  obtain ⟨h1, h3, h2⟩ := frameK_commute_sl2Two (K := K) A A'
  exact (h1.mul_left h3).mul_left h2

theorem d4Graph_nW (i : Fin Tag.D4.rank) : d4Graph K 1 (nW i) = nW ((d4Rho ^ 1) i) := by
  unfold nW
  rw [weylElement_eq_sl2At, weylElement_eq_sl2At, d4Graph_sl2At]

theorem frameK₃_eq (A : SL2 K) :
    frameK₃ K A = nW ⟨1, by decide⟩ * nW ⟨3, by decide⟩ * sl2At K ⟨2, by decide⟩ A *
      (nW ⟨1, by decide⟩ * nW ⟨3, by decide⟩)⁻¹ := by
  rw [frameK₃_apply, frameK₁_apply]
  simp only [map_mul, map_inv]
  rw [d4Graph_nW, d4Graph_nW, d4Graph_one_sl2Two]
  rfl

theorem frameK₂_eq (A : SL2 K) :
    frameK₂ K A = nW ⟨3, by decide⟩ * nW ⟨0, by decide⟩ * sl2At K ⟨2, by decide⟩ A *
      (nW ⟨3, by decide⟩ * nW ⟨0, by decide⟩)⁻¹ := by
  rw [frameK₂_apply, frameK₃_eq]
  simp only [map_mul, map_inv]
  rw [d4Graph_nW, d4Graph_nW, d4Graph_one_sl2Two]
  rfl

variable (K) in
@[expose] noncomputable def frameD (B : SL2 K) : ↥(adjointGroup Tag.D4 K) :=
  frameK₂ K B * (frameK₃ K B)⁻¹

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

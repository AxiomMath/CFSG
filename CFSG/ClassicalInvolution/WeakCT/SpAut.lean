module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.WeakCT.SpModel

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.Timmesfeld.LevisExtras
open CFSG.LieType.Universal.Symplectic (rootDatum cartanC)
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Steinberg (relA relB chevEval chevOf CommOrder CommutatorFormula)
open scoped commutatorElement MatrixGroups

section Hom

variable {F : Type} [Field F]

theorem exists_sp_hom [Finite F] {G : Type} [Group G] (y : (Fin 2 → ℤ) → F → G)
    (O' : CommOrder (Steinberg.Sp.Φ 2 F)) (C' : (Fin 2 → ℤ) → (Fin 2 → ℤ) → ℕ × ℕ → ℤ)
    (hC' : CommutatorFormula (Steinberg.Sp.x 2 F) O' C')
    (hrel : ∀ r ∈ relA (Steinberg.Sp.Φ 2 F) F ∪ relB (Steinberg.Sp.Φ 2 F) F O' C',
      FreeGroup.lift (chevEval y) r = 1) :
    ∃ φ : StatedSp 2 F →* G, ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      φ (Steinberg.Sp.x 2 F γ c) = y γ c := by
  obtain ⟨⟨C₀, -, hC₀⟩, hpres⟩ := Steinberg.Sp.presentationB (F := F) (n := 2) le_rfl O'
  obtain ⟨hrelS, hbij⟩ := hpres C' hC'
  refine ⟨(PresentedGroup.toGroup hrel).comp
    (MulEquiv.ofBijective (PresentedGroup.toGroup hrelS) hbij).symm.toMonoidHom, fun γ hγ c => ?_⟩
  have h1 : (PresentedGroup.toGroup hrelS) (PresentedGroup.of (⟨γ, hγ⟩, c)) =
      Steinberg.Sp.x 2 F γ c := by
    rw [PresentedGroup.toGroup.of]
    rfl
  have h2 : (MulEquiv.ofBijective (PresentedGroup.toGroup hrelS) hbij).symm
      (Steinberg.Sp.x 2 F γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
    rw [MulEquiv.symm_apply_eq]
    exact h1.symm
  show (PresentedGroup.toGroup hrel) ((MulEquiv.ofBijective (PresentedGroup.toGroup hrelS)
    hbij).symm (Steinberg.Sp.x 2 F γ c)) = _
  rw [h2, PresentedGroup.toGroup.of]
  rfl

end Hom

section Twist

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : Steinberg.RootSystem ι} {F F₀ : Type} [Field F]
  [Field F₀] {G : Type} [Group G]

theorem twist_relations {O : CommOrder Φ} {C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ}
    {x : (ι → ℤ) → F₀ → G} (hadd : ∀ γ ∈ Φ.roots, ∀ c d : F₀, x γ (c + d) = x γ c * x γ d)
    (hcomm : CommutatorFormula x O C) (ψ : F →+* F₀) (χ : (ι → ℤ) → F₀)
    (hχ : ∀ α ∈ Φ.roots, ∀ β ∈ Φ.roots, α + β ≠ 0 → ∀ p ∈ O.list α β,
      χ (p.1 • α + p.2 • β) = χ α ^ p.1 * χ β ^ p.2) :
    ∀ r ∈ relA Φ F ∪ relB Φ F O C,
      FreeGroup.lift (chevEval (fun γ c => x γ (χ γ * ψ c))) r = 1 := by
  rintro r (⟨γ, hγ, c, d, rfl⟩ | ⟨α, hα, β, hβ, hαβ, c, d, rfl⟩)
  · simp only [map_mul, map_inv, lift_chevOf _ hγ]
    rw [map_add, mul_add, hadd γ hγ, mul_inv_cancel]
  · have hp : ∀ p ∈ O.list α β, p.1 • α + p.2 • β ∈ Φ.roots := fun p hp =>
      ((O.mem_iff α hα β hβ hαβ p).1 hp).2.2
    simp only [map_mul, map_inv, map_commutatorElement, lift_chevOf _ hα, lift_chevOf _ hβ,
      map_list_prod, List.map_map]
    rw [mul_inv_eq_one, hcomm α hα β hβ hαβ]
    have hterm : ∀ p ∈ O.list α β, (⇑(FreeGroup.lift (chevEval (fun γ c =>
        x γ (χ γ * ψ c)))) ∘ fun p => chevOf (Φ := Φ)
          (p.1 • α + p.2 • β) (((C α β p : ℤ) : F) * c ^ p.1 * d ^ p.2)) p =
        x (p.1 • α + p.2 • β) (((C α β p : ℤ) : F₀) * (χ α * ψ c) ^ p.1 *
          (χ β * ψ d) ^ p.2) := by
      intro p hpl
      simp only [Function.comp]
      rw [lift_chevOf _ (hp p hpl), hχ α hα β hβ hαβ p hpl]
      congr 1
      simp only [map_mul, map_pow, map_intCast]
      ring
    rw [List.map_congr_left hterm]

end Twist

section Aut

variable {F : Type} [Field F] [Finite F]

theorem exists_sp_aut (ψ : F ≃+* F) (r : Fˣ) :
    ∃ β : StatedSp 2 F ≃* StatedSp 2 F, ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      β (Steinberg.Sp.x 2 F γ c) = Steinberg.Sp.x 2 F γ (((r ^ (coords γ).2 : Fˣ) : F) * ψ c) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have hχ : ∀ α ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ β ∈ (Steinberg.Sp.Φ 2 F).roots, α + β ≠ 0 →
      ∀ p ∈ O.list α β, ((r ^ (coords (p.1 • α + p.2 • β)).2 : Fˣ) : F) =
        ((r ^ (coords α).2 : Fˣ) : F) ^ p.1 * ((r ^ (coords β).2 : Fˣ) : F) ^ p.2 := by
    intro α hα β hβ hαβ p hp
    have hz : (coords (p.1 • α + p.2 • β)).2 =
        (coords α).2 * (p.1 : ℤ) + (coords β).2 * (p.2 : ℤ) := by
      simp [coords, mul_comm]
    rw [hz, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  obtain ⟨φ, hφ⟩ := exists_sp_hom (fun γ c => Steinberg.Sp.x 2 F γ
    (((r ^ (coords γ).2 : Fˣ) : F) * (ψ : F →+* F) c)) O Steinberg.Sp.commC hE.comm
    (twist_relations (fun γ hγ c d => x_add' hE hγ c d) hE.comm (ψ : F →+* F)
      (fun γ => ((r ^ (coords γ).2 : Fˣ) : F)) hχ)
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    rw [eq_top_iff, ← show (⨆ γ ∈ (rootDatum 2 F).roots, (rootDatum 2 F).rootGroup γ) = ⊤ from
      (Symplectic.isCTGroupDatum 2 F).iSup_eq_top]
    refine iSup₂_le fun γ hγ g hg => ?_
    obtain ⟨c', rfl⟩ := ((hE.param γ hγ).1 g).1 hg
    refine ⟨Steinberg.Sp.x 2 F γ (ψ.symm (((r ^ (coords γ).2)⁻¹ : Fˣ) * c')), ?_⟩
    have hψ : ∀ v : F, ((ψ : F →+* F) (ψ.symm v)) = v := fun v => ψ.apply_symm_apply v
    rw [hφ γ hγ, hψ, Units.val_inv_eq_inv_val, mul_inv_cancel_left₀ (Units.ne_zero _)]
  exact ⟨MulEquiv.ofBijective φ ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩, hφ⟩

end Aut

section Transport

variable {F F₀ : Type} [Field F] [Finite F] [Field F₀]

theorem exists_spMap (ψ : F →+* F₀) :
    ∃ Φ : StatedSp 2 F →* StatedSp 2 F₀, ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      Φ (Steinberg.Sp.x 2 F γ c) = Steinberg.Sp.x 2 F₀ γ (ψ c) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have hE₀ : Steinberg.ChevalleyExtras (rootDatum 2 F₀) F₀ (Steinberg.Sp.x 2 F₀)
      Steinberg.Sp.commC (O : CommOrder (Steinberg.Sp.Φ 2 F₀)) :=
    Steinberg.Sp.chevalleyExtras (F := F₀) le_rfl O _
      (Steinberg.Sp.commutatorFormula (F := F₀) O)
  have hrel : ∀ r ∈ relA (Steinberg.Sp.Φ 2 F) F ∪ relB (Steinberg.Sp.Φ 2 F) F O
      Steinberg.Sp.commC, FreeGroup.lift (chevEval (fun γ c => Steinberg.Sp.x 2 F₀ γ
        ((fun _ => (1 : F₀)) γ * ψ c))) r = 1 :=
    twist_relations (Φ := Steinberg.Sp.Φ 2 F) (O := O) (x := Steinberg.Sp.x 2 F₀)
      (fun γ hγ c d => x_add' hE₀ hγ c d) hE₀.comm ψ (fun _ => (1 : F₀))
      (fun _ _ _ _ _ _ => by simp)
  obtain ⟨φ, hφ⟩ := exists_sp_hom (fun γ c => Steinberg.Sp.x 2 F₀ γ (ψ c)) O Steinberg.Sp.commC
    hE.comm (by simpa only [one_mul] using hrel)
  exact ⟨φ, hφ⟩

omit [Finite F] in
theorem map_tv01 (ψ : F →+* F₀) (c : F) :
    Matrix.SpecialLinearGroup.map ψ (tv 0 1 c : SL(2, F)) = (tv 0 1 (ψ c) : SL(2, F₀)) := by
  rw [tv01_eq_sl2Upper, tv01_eq_sl2Upper]
  refine Subtype.ext ?_
  show ψ.mapMatrix ((Steinberg.sl2Upper c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    ((Steinberg.sl2Upper (ψ c) : SL(2, F₀)) : Matrix (Fin 2) (Fin 2) F₀)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Upper]

omit [Finite F] in
theorem map_tv10 (ψ : F →+* F₀) (c : F) :
    Matrix.SpecialLinearGroup.map ψ (tv 1 0 c : SL(2, F)) = (tv 1 0 (ψ c) : SL(2, F₀)) := by
  rw [tv10_eq_sl2Lower, tv10_eq_sl2Lower]
  refine Subtype.ext ?_
  show ψ.mapMatrix ((Steinberg.sl2Lower c : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
    ((Steinberg.sl2Lower (ψ c) : SL(2, F₀)) : Matrix (Fin 2) (Fin 2) F₀)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Lower]

omit [Finite F] in
theorem spMap_comp_spBlock (ψ : F →+* F₀) {Φ : StatedSp 2 F →* StatedSp 2 F₀}
    (hΦ : ∀ γ ∈ (Steinberg.Sp.Φ 2 F).roots, ∀ c : F,
      Φ (Steinberg.Sp.x 2 F γ c) = Steinberg.Sp.x 2 F₀ γ (ψ c)) (i : Fin 2) :
    Φ.comp (spBlock F i) = (spBlock F₀ i).comp (Matrix.SpecialLinearGroup.map ψ) := by
  have h1 : (Pi.single i 1 : Fin 2 → ℤ) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    (Steinberg.Sp.Φ 2 F).single_mem i
  have h2 : (-Pi.single i 1 : Fin 2 → ℤ) ∈ (Steinberg.Sp.Φ 2 F).roots :=
    (Steinberg.Sp.Φ 2 F).neg_mem _ h1
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · simp only [MonoidHom.comp_apply, map_tv01, spBlock_upper]
    exact hΦ _ h1 c
  · simp only [MonoidHom.comp_apply, map_tv10, spBlock_lower]
    exact hΦ _ h2 c

end Transport

section SL2Gen

variable {F : Type} [Field F]

theorem fieldAutSL_tv01 (ψ : F ≃+* F) (c : F) :
    fieldAutSL ψ 2 (tv 0 1 c) = tv 0 1 (ψ c) := by
  rw [tv01_eq_sl2Upper, tv01_eq_sl2Upper]
  refine Subtype.ext ?_
  rw [coe_fieldAutSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Upper]

theorem fieldAutSL_tv10 (ψ : F ≃+* F) (c : F) :
    fieldAutSL ψ 2 (tv 1 0 c) = tv 1 0 (ψ c) := by
  rw [tv10_eq_sl2Lower, tv10_eq_sl2Lower]
  refine Subtype.ext ?_
  rw [coe_fieldAutSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Lower]

theorem invTransposeSL_tv01 (c : F) : invTransposeSL 2 (tv 0 1 c) = tv 1 0 (-c) := by
  rw [tv01_eq_sl2Upper, tv10_eq_sl2Lower]
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Steinberg.sl2Upper, Steinberg.sl2Lower]

theorem invTransposeSL_tv10 (c : F) : invTransposeSL 2 (tv 1 0 c) = tv 0 1 (-c) := by
  rw [tv01_eq_sl2Upper, tv10_eq_sl2Lower]
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Steinberg.sl2Upper, Steinberg.sl2Lower]

theorem diagConj2_tv01 (a b : Fˣ) (c : F) :
    diagConj2 a b (tv 0 1 c) = tv 0 1 ((a : F) * c * ((b⁻¹ : Fˣ) : F)) := by
  rw [tv01_eq_sl2Upper, tv01_eq_sl2Upper]
  refine Subtype.ext ?_
  rw [coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Upper, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem diagConj2_tv10 (a b : Fˣ) (c : F) :
    diagConj2 a b (tv 1 0 c) = tv 1 0 ((b : F) * c * ((a⁻¹ : Fˣ) : F)) := by
  rw [tv10_eq_sl2Lower, tv10_eq_sl2Lower]
  refine Subtype.ext ?_
  rw [coe_diagConj2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Steinberg.sl2Lower, Matrix.mul_apply,
    Matrix.diagonal_apply]

theorem aut_sl2_shape [Finite F] (hK : 4 ≤ Nat.card F) (α : SL(2, F) ≃* SL(2, F))
    (hα : (diagTorus2 F).map α.toMonoidHom ≤ diagTorus2 F) :
    ∃ (ψ : F ≃+* F) (a b : Fˣ),
      (∀ A, α A = diagConj2 a b (fieldAutSL ψ 2 A)) ∨
        (∀ A, α A = diagConj2 a b (invTransposeSL 2 (fieldAutSL ψ 2 A))) := by
  obtain ⟨G, ψ, hG⟩ := CFSG.ClassicalInvolution.Phan.exists_toGL_eq_conj_map α
  obtain ⟨s₀, hs₀⟩ := exists_unit_sq_ne_one hK
  obtain ⟨t, ht⟩ : α (torusHom F s₀) ∈ diagTorus2 F := hα ⟨_, ⟨s₀, rfl⟩, rfl⟩
  have hGd := hG (torusHom F s₀)
  rw [← ht, map_torusHom] at hGd
  have hmat : ((torusHom F t : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      (G : Matrix (Fin 2) (Fin 2) F) = (G : Matrix (Fin 2) (Fin 2) F) *
        ((torusHom F (Units.map (ψ : F →* F) s₀) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : Matrix.SpecialLinearGroup.toGL (torusHom F t) * G =
        G * Matrix.SpecialLinearGroup.toGL (torusHom F (Units.map (ψ : F →* F) s₀)) := by
      calc Matrix.SpecialLinearGroup.toGL (torusHom F t) * G
          = G * Matrix.SpecialLinearGroup.toGL (torusHom F (Units.map (ψ : F →* F) s₀)) * G⁻¹ * G :=
            by rw [← hGd]
        _ = _ := by group
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) h1
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  have hσ : (Units.map (ψ : F →* F) s₀) ^ 2 ≠ 1 := by
    intro h
    apply hs₀
    apply Units.map_injective (f := (ψ : F →* F)) ψ.injective
    rw [map_pow, h, map_one]
  have hcoe : ∀ A : SL(2, F), ((α A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (G : Matrix (Fin 2) (Fin 2) F) *
        ((Matrix.SpecialLinearGroup.map (ψ : F →+* F) A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
          ((G⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    intro A
    have h2 := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) (hG A)
    simpa only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using h2
  rcases monomial_shape hσ G hmat with ⟨h01, h10⟩ | ⟨h00, h11⟩
  · obtain ⟨a, b, hGa, hGi⟩ := exists_diagonal_of_offDiag_zero G h01 h10
    exact ⟨ψ, a, b, Or.inl fun A => Subtype.ext (by rw [hcoe A, hGa, hGi]; rfl)⟩
  · obtain ⟨a, b, hab⟩ := exists_diagonal_of_diag_zero G h00 h11
    exact ⟨ψ, a, b, Or.inr fun A => Subtype.ext ((hcoe A).trans (hab _))⟩

end SL2Gen

section W0Sp

variable (F : Type) [Field F]

noncomputable def spW0 : StatedSp 2 F :=
  Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 *
    Steinberg.weylElement (Steinberg.Sp.x 2 F) (1 : Fin 2) 1 *
    Steinberg.weylElement (Steinberg.Sp.x 2 F) (0 : Fin 2) 1 *
    Steinberg.weylElement (Steinberg.Sp.x 2 F) (1 : Fin 2) 1

variable {F}

theorem spW0_conj_upper (i : Fin 2) (c : F) :
    spW0 F * Steinberg.Sp.x 2 F (Pi.single i 1) c * (spW0 F)⁻¹ =
      Steinberg.Sp.x 2 F (-Pi.single i 1) (-c) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h := w0_conj_simple hE (s := spS) (l := spL) rfl sp_cartan_01 sp_cartan_10 c
  rw [pair_one_zero, pair_neg_one_zero, pair_zero_one, pair_zero_neg_one] at h
  fin_cases i
  · exact h.1
  · exact h.2.2.1

theorem spW0_conj_lower (i : Fin 2) (c : F) :
    spW0 F * Steinberg.Sp.x 2 F (-Pi.single i 1) c * (spW0 F)⁻¹ =
      Steinberg.Sp.x 2 F (Pi.single i 1) (-c) := by
  obtain ⟨O, hE⟩ := exists_sp_chevalleyExtras F
  have h := w0_conj_simple hE (s := spS) (l := spL) rfl sp_cartan_01 sp_cartan_10 c
  rw [pair_one_zero, pair_neg_one_zero, pair_zero_one, pair_zero_neg_one] at h
  fin_cases i
  · exact h.2.1
  · exact h.2.2.2

theorem spW0_block (i : Fin 2) :
    (MulAut.conj (spW0 F)).toMonoidHom.comp (spBlock F i) =
      (spBlock F i).comp (invTransposeSL 2).toMonoidHom := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      spBlock_upper, invTransposeSL_tv01, spBlock_lower, spW0_conj_upper]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      spBlock_lower, invTransposeSL_tv10, spBlock_upper, spW0_conj_lower]

end W0Sp

section ExtendAux

variable {F : Type} [Field F]

theorem invTransposeSL_torusHom (s : Fˣ) : invTransposeSL 2 (torusHom F s) = torusHom F s⁻¹ := by
  refine Subtype.ext ?_
  rw [coe_invTransposeSL, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two, coe_torusHom]

theorem fieldAutSL_torusHom (ψ : F ≃+* F) (s : Fˣ) :
    fieldAutSL ψ 2 (torusHom F s) = torusHom F (Units.map (ψ : F →* F) s) :=
  map_torusHom ψ s

end ExtendAux

section Extend

variable {F : Type} [Field F] [Finite F]

theorem exists_extend_sp (hF : 4 ≤ Nat.card F) (α : SL(2, F) ≃* SL(2, F))
    (hα : (diagTorus2 F).map α.toMonoidHom ≤ diagTorus2 F) :
    ∃ (β : StatedSp 2 F ≃* StatedSp 2 F) (α' : SL(2, F) ≃* SL(2, F)),
      (∀ A, β (spBlock F 1 A) = spBlock F 1 (α A)) ∧
        (∀ A, β (spBlock F 0 A) = spBlock F 0 (α' A)) ∧
        (diagTorus2 F).map α'.toMonoidHom ≤ diagTorus2 F := by
  obtain ⟨ψ, a, b, hα'⟩ := aut_sl2_shape hF α hα
  rcases hα' with hα' | hα'
  · obtain ⟨β, hβ⟩ := exists_sp_aut ψ (a * b⁻¹)
    refine ⟨β, fieldAutSL ψ 2, fun A => ?_, fun A => ?_, ?_⟩
    · have h : β.toMonoidHom.comp (spBlock F 1) = (spBlock F 1).comp α.toMonoidHom := by
        refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_upper, hα',
            fieldAutSL_tv01, diagConj2_tv01]
          rw [hβ _ (single_mem_sp_roots 1), coords_single_one]
          congr 1
          simp only [zpow_one, Units.val_mul]
          ring
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_lower, hα',
            fieldAutSL_tv10, diagConj2_tv10]
          rw [hβ _ (neg_single_mem_sp_roots 1), coords_neg_single_one]
          congr 1
          simp only [zpow_neg, zpow_one, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev,
            inv_inv]
          ring
      exact DFunLike.congr_fun h A
    · have h : β.toMonoidHom.comp (spBlock F 0) =
          (spBlock F 0).comp (fieldAutSL ψ 2).toMonoidHom := by
        refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_upper,
            fieldAutSL_tv01]
          rw [hβ _ (single_mem_sp_roots 0), coords_single_zero]
          simp
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_lower,
            fieldAutSL_tv10]
          rw [hβ _ (neg_single_mem_sp_roots 0), coords_neg_single_zero]
          simp
      exact DFunLike.congr_fun h A
    · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      exact ⟨Units.map (ψ : F →* F) s, (fieldAutSL_torusHom ψ s).symm⟩
  · obtain ⟨β₀, hβ₀⟩ := exists_sp_aut ψ (a⁻¹ * b)
    refine ⟨β₀.trans (MulAut.conj (spW0 F)), (fieldAutSL ψ 2).trans (invTransposeSL 2),
      fun A => ?_, fun A => ?_, ?_⟩
    · have h : ((MulAut.conj (spW0 F)).toMonoidHom.comp β₀.toMonoidHom).comp (spBlock F 1) =
          (spBlock F 1).comp α.toMonoidHom := by
        refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            spBlock_upper, hα', fieldAutSL_tv01, invTransposeSL_tv01, diagConj2_tv10]
          rw [hβ₀ _ (single_mem_sp_roots 1), coords_single_one, spW0_conj_upper]
          simp only [spBlock_lower]
          congr 1
          simp only [zpow_one, Units.val_mul, Units.val_inv_eq_inv_val]
          ring
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            spBlock_lower, hα', fieldAutSL_tv10, invTransposeSL_tv10, diagConj2_tv01]
          rw [hβ₀ _ (neg_single_mem_sp_roots 1), coords_neg_single_one, spW0_conj_lower]
          simp only [spBlock_upper]
          congr 1
          simp only [zpow_neg, zpow_one, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_rev,
            inv_inv]
          ring
      exact DFunLike.congr_fun h A
    · have h : ((MulAut.conj (spW0 F)).toMonoidHom.comp β₀.toMonoidHom).comp (spBlock F 0) =
          (spBlock F 0).comp ((invTransposeSL 2).toMonoidHom.comp
            (fieldAutSL ψ 2).toMonoidHom) := by
        refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            spBlock_upper, fieldAutSL_tv01, invTransposeSL_tv01]
          rw [hβ₀ _ (single_mem_sp_roots 0), coords_single_zero, spW0_conj_upper]
          simp [spBlock_lower]
        · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            spBlock_lower, fieldAutSL_tv10, invTransposeSL_tv10]
          rw [hβ₀ _ (neg_single_mem_sp_roots 0), coords_neg_single_zero, spW0_conj_lower]
          simp [spBlock_upper]
      exact DFunLike.congr_fun h A
    · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      refine ⟨(Units.map (ψ : F →* F) s)⁻¹, ?_⟩
      show torusHom F _ = invTransposeSL 2 (fieldAutSL ψ 2 (torusHom F s))
      rw [fieldAutSL_torusHom, invTransposeSL_torusHom]

end Extend

end CFSG.ClassicalInvolution.WeakCT

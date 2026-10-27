module

public import CFSG.LieType.Chevalley.C2E6FourthResidueSpace
public import CFSG.LieType.Chevalley.C2E6D4Twist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std.FourthResidue

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LieType.Universal.Spin
  CFSG.ClassicalGroups.Orthogonal QuadraticMap Module Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def fourthJ : Set (Fin 4) := {0, 1, 2}

theorem two_mem_fourthJ : (2 : Fin 4) ∈ fourthJ := by
  simp [fourthJ]

theorem nativeUnion_fourthJ : nativeUnion fourthJ = setD := by
  have key1 : ∀ i : Fin 4, (i = 0 ∨ i = 1 ∨ i = 2) → ∀ x : Fin 6, x ∈ nativeOrbit i →
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
    decide
  have key2 : ∀ x : Fin 6, (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) →
      ∃ i : Fin 4, (i = 0 ∨ i = 1 ∨ i = 2) ∧ x ∈ nativeOrbit i := by
    decide
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact key1 i hi x hxi
  · intro hx
    obtain ⟨i, hi, hxi⟩ := key2 x hx
    exact Set.mem_iUnion₂.mpr ⟨i, hi, hxi⟩

theorem stdLevi_fourthJ
    : stdLevi fourthJ = groupD ⊓ stdFixedGroup := by
  rw [stdLevi, nativeUnion_fourthJ]

theorem stdLeviUnipotent_fourthJ
    : stdLeviUnipotent fourthJ = unipotentD ⊓ stdFixedGroup := by
  rw [stdLeviUnipotent, nativeUnion_fourthJ]

theorem stdLevi_fourthJ_le_groupD
    : stdLevi fourthJ ≤ groupD := by
  rw [stdLevi_fourthJ]
  exact inf_le_left

@[expose] def psiL
    : stdLevi fourthJ →* ((Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)) :=
  psiD.comp (Subgroup.inclusion stdLevi_fourthJ_le_groupD)

theorem psiL_apply
    (l : stdLevi fourthJ) :
    psiL l = psiD ⟨l, stdLevi_fourthJ_le_groupD l.2⟩ :=
  rfl

theorem psiD_betaD_apply
    (g : groupD) (w : Fin 4 ⊕ Fin 4 → K) :
    psiD (betaD g) w = frob8 (psiD g (frob8 w)) := by
  have h1 : psiD (betaD g) w = LinearMap.toMatrix'
      (psiD (betaD g) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *ᵥ w :=
    (LinearMap.toMatrix'_mulVec _ w).symm
  have h2 : psiD g (frob8 w) = LinearMap.toMatrix'
      (psiD g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) *ᵥ frob8 w :=
    (LinearMap.toMatrix'_mulVec _ _).symm
  rw [h1, h2, psiD_betaD g]
  set M := LinearMap.toMatrix' (psiD g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K))
  funext i
  change _ = barHom ((M *ᵥ frob8 w) i)
  rw [RingHom.map_mulVec]
  congr 1
  funext j
  exact (bar_bar (w j)).symm

theorem conjD_betaD_eq
    (l : stdLevi fourthJ) :
    conjD (betaD ⟨l, stdLevi_fourthJ_le_groupD l.2⟩) = ⟨l, stdLevi_fourthJ_le_groupD l.2⟩ := by
  have hΓ : (l : ModGL Tag.E6 K) ∈ stdFixedGroup := (stdLevi_fourthJ.le l.2).2
  have hfix := ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).mp hΓ).2
  apply Subtype.ext
  rw [coe_conjD, coe_betaD, ← twistHom_eq_conj]
  exact hfix

theorem psiL_swapE4F4_frob8
    (l : stdLevi fourthJ) (w : Fin 4 ⊕ Fin 4 → K) :
    psiL l (swapE4F4 (frob8 w)) = swapE4F4 (frob8 (psiL l w)) := by
  have h := psiD_conjD (betaD ⟨l, stdLevi_fourthJ_le_groupD l.2⟩)
  rw [conjD_betaD_eq] at h
  conv_lhs => rw [psiL_apply, h]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv,
    LinearEquiv.symm_apply_apply, psiD_betaD_apply, frob8_frob8]
  rfl

theorem psiL_embed_fixed
    (l : stdLevi fourthJ) (v : V0) :
    swapE4F4 (frob8 (psiL l (embed v))) = psiL l (embed v) := by
  rw [← psiL_swapE4F4_frob8, swapE4F4_frob8_embed]

@[expose] def rhoLin
    (l : stdLevi fourthJ) : V0 →ₗ[ZMod 2] V0 :=
  coords ∘ₗ ((psiL l : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)).restrictScalars (ZMod 2)) ∘ₗ
    embed

theorem embed_rhoLin
    (l : stdLevi fourthJ) (v : V0) : embed (rhoLin l v) = psiL l (embed v) :=
  embed_coords (psiL_embed_fixed l v)

theorem rhoLin_mul
    (l l' : stdLevi fourthJ) (v : V0) :
    rhoLin (l * l') v = rhoLin l (rhoLin l' v) := by
  apply embed_injective
  rw [embed_rhoLin, embed_rhoLin, embed_rhoLin, map_mul, LinearEquiv.mul_apply]

theorem rhoLin_one
    (v : V0) : rhoLin 1 v = v := by
  apply embed_injective
  rw [embed_rhoLin, map_one]
  rfl

@[expose] def rhoEquiv
    (l : stdLevi fourthJ) : V0 ≃ₗ[ZMod 2] V0 :=
  LinearEquiv.ofLinearMap (rhoLin l) (rhoLin l⁻¹)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← rhoLin_mul, mul_inv_cancel, rhoLin_one]
      rfl)
    (LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, ← rhoLin_mul, inv_mul_cancel, rhoLin_one]
      rfl)

theorem rhoEquiv_apply
    (l : stdLevi fourthJ) (v : V0) : rhoEquiv l v = rhoLin l v :=
  rfl

@[expose] def rhoMinus :
    stdLevi fourthJ →* (V0 ≃ₗ[ZMod 2] V0) where
  toFun := rhoEquiv
  map_one' := LinearEquiv.ext fun v => by
    rw [rhoEquiv_apply, rhoLin_one]
    rfl
  map_mul' l l' := LinearEquiv.ext fun v => by
    rw [rhoEquiv_apply, rhoLin_mul, LinearEquiv.mul_apply, rhoEquiv_apply, rhoEquiv_apply]

theorem embed_rhoMinus
    (l : stdLevi fourthJ) (v : V0) :
    embed (rhoMinus l v) = psiL l (embed v) :=
  embed_rhoLin l v

theorem rhoMinus_injective :
    Function.Injective rhoMinus := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have h : (psiL l : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = LinearMap.id :=
    linearMap_ext_embed fun v => by
      rw [LinearEquiv.coe_coe, ← embed_rhoMinus, hl]
      rfl
  have h1 : psiL l = 1 := LinearEquiv.toLinearMap_injective h
  have h2 : (⟨l, stdLevi_fourthJ_le_groupD l.2⟩ : groupD) = 1 :=
    psiD_injective (by rw [← psiL_apply, h1, map_one])
  have h3 : (l : ModGL Tag.E6 K) = 1 := congrArg Subtype.val h2
  exact Subtype.ext h3

theorem psiL_mem_orthogonalGroup
    (l : stdLevi fourthJ) :
    psiL l ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) :=
  orthElementaryGroup_le _ (psiD_range_le ⟨_, rfl⟩)

theorem rhoMinus_mem_orthogonalGroup
    (l : stdLevi fourthJ) :
    rhoMinus l ∈ TauCeti.QuadraticMap.orthogonalGroup Qminus := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  apply (algebraMap (ZMod 2) K).injective
  rw [← quadPlus_embed, ← quadPlus_embed, embed_rhoMinus, map_of_mem (psiL_mem_orthogonalGroup l)]

theorem rhoMinus_betaGL
    (l : stdLevi fourthJ) :
    rhoMinus ⟨betaGL l, betaGL_mem_stdLevi l.2⟩ = sMinus * rhoMinus l * sMinus := by
  refine LinearEquiv.ext fun v => embed_injective ?_
  rw [embed_rhoMinus, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← frob8_embed, embed_rhoMinus,
    ← frob8_embed]
  exact psiD_betaD_apply ⟨l, stdLevi_fourthJ_le_groupD l.2⟩ (embed v)

theorem map_eq_of_forall_mem {g : V0 ≃ₗ[ZMod 2] V0} {W : Submodule (ZMod 2) V0}
    (h1 : ∀ v ∈ W, g v ∈ W) (h2 : ∀ v ∈ W, g.symm v ∈ W) :
    W.map (g : V0 →ₗ[ZMod 2] V0) = W := by
  refine le_antisymm ?_ fun v hv => ⟨g.symm v, h2 v hv, g.apply_symm_apply v⟩
  rintro _ ⟨v, hv, rfl⟩
  exact h1 v hv

theorem rhoMinus_mem_tailFlag
    {l : stdLevi fourthJ} {k : ℕ} (hk : k ≤ 3)
    (hl : ∀ w ∈ flag 4 K k, psiL l w ∈ flag 4 K k) {v : V0}
    (hv : v ∈ tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k) :
    rhoMinus l v ∈ tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
  rw [← embed_mem_flag_iff hk, embed_rhoMinus]
  exact hl _ ((embed_mem_flag_iff hk v).mpr hv)

theorem map_tailFlag_rhoMinus
    {l : stdLevi fourthJ} (hl : psiL l ∈ borel 4 K) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ 3) :
    (tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k).map (rhoMinus l : V0 →ₗ[ZMod 2] V0) =
      tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k := by
  have hmaps : ∀ g ∈ borel 4 K, ∀ w ∈ flag 4 K k, g w ∈ flag 4 K k := fun g hg w hw => by
    rw [← (mem_borel.1 hg).2 k hk1 (by omega)]
    exact Submodule.mem_map_of_mem hw
  have hinv : psiL l⁻¹ ∈ borel 4 K := by
    rw [map_inv]
    exact inv_mem hl
  refine map_eq_of_forall_mem (fun v hv => rhoMinus_mem_tailFlag hk (hmaps _ hl) hv)
    fun v hv => ?_
  have e : (rhoMinus l).symm v = rhoMinus l⁻¹ v := by
    rw [map_inv, LinearEquiv.coe_inv]
  rw [e]
  exact rhoMinus_mem_tailFlag hk (hmaps _ hinv) hv

theorem psiD_mem_borel
    {g : ModGL Tag.E6 K} (hg : g ∈ stdLeviBorel fourthJ) (hD : g ∈ groupD) :
    psiD ⟨g, hD⟩ ∈ borel 4 K := by
  let S : Subgroup (ModGL Tag.E6 K) := ((borel 4 K).comap psiD).map groupD.subtype
  have hT : stdTorus ≤ S := by
    intro h hh
    rw [← stdTorus0_eq_stdTorus, stdTorus0_eq_zpowers] at hh
    have hTD : h ∈ torusD := (Subgroup.zpowers_le.mpr
      (fixedTorusGen_mem_subsystemTorus (Or.inr (Or.inl rfl))
        (Or.inr (Or.inr (Or.inr rfl))))) hh
    have hhD := torusD_le_groupD hTD
    have hmem : psiD ⟨h, hhD⟩ ∈ (torusD.subgroupOf groupD).map psiD := ⟨⟨h, hhD⟩, hTD, rfl⟩
    rw [map_psiD_torusD] at hmem
    obtain ⟨a, ha⟩ := hmem
    exact ⟨⟨h, hhD⟩, torus_le_borel ⟨psiD_range_le ⟨_, rfl⟩, a, ha⟩, rfl⟩
  have hU : stdLeviUnipotent fourthJ ≤ S := by
    intro u hu
    rw [stdLeviUnipotent_fourthJ] at hu
    have huD := unipotentD_le_groupD hu.1
    have hmem : psiD ⟨u, huD⟩ ∈ (unipotentD.subgroupOf groupD).map psiD := ⟨⟨u, huD⟩, hu.1, rfl⟩
    rw [map_psiD_unipotentD] at hmem
    exact ⟨⟨u, huD⟩, unipotent_le_borel hmem, rfl⟩
  obtain ⟨g', hg', hgg'⟩ := (sup_le hT hU : stdLeviBorel fourthJ ≤ S) hg
  have e : g' = ⟨g, hD⟩ := Subtype.ext hgg'
  rw [← e]
  exact hg'

theorem map_tailFlag_rhoMinus_of_mem
    {l : stdLevi fourthJ}
    (hl : (l : ModGL Tag.E6 K) ∈ stdLeviBorel fourthJ) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ 3) :
    (tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k).map (rhoMinus l : V0 →ₗ[ZMod 2] V0) =
      tailFlag (ZMod 2) (Fin 2 → ZMod 2) 3 k :=
  map_tailFlag_rhoMinus (psiD_mem_borel hl _) hk1 hk

end CFSG.LieType.Chevalley.C2E6Std.FourthResidue

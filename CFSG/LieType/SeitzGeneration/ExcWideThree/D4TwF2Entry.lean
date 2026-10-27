module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Inv
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxTwo

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Entry

open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.HardMathSupport.Lang.D4Three
  CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Chain
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Form
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Span
  CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Inv


section Entry


variable {K : Type} [Field K]

theorem posLabel_27_eq (hp : 27 < dim Tag.D4) :
    posLabel 27 hp = negLabel isMaxHeightRoot_d4Root_22.1 := by
  have hroot : (Tag.rootCertificate Tag.D4).root (27 - Tag.D4.rank) = -(d4Root 22) := by
    funext i
    fin_cases i <;> rfl
  unfold posLabel
  rw [dif_neg (by decide +kernel)]
  show Sum.inr _ = Sum.inr _
  congr 1
  exact Subtype.ext hroot

theorem pcoord_eq_negLabel (w : RootModule Tag.D4 K) :
    pcoord K w 27 = w (negLabel isMaxHeightRoot_d4Root_22.1) := by
  have hp : 27 < dim Tag.D4 := by decide +kernel
  unfold pcoord posCoord
  rw [dif_pos hp, Finsupp.lapply_apply, posLabel_27_eq hp]

theorem gram_row_theta : ∀ b < 28, gramZ 26 b = if b = 27 then 1 else 0 := by
  decide +kernel

theorem Bf_vTheta [CharP K 2] (w : RootModule Tag.D4 K) : Bf K (vTheta K) w = pcoord K w 27 := by
  have h1 : Bf K (vTheta K) w = Bzk (fun a : ℕ => if a = 26 then (1 : K) else 0)
      (fun b => pcoord K w b) := by
    unfold Bf
    congr 1
    funext a
    exact pcoord_vTheta K a
  rw [h1]
  unfold Bzk
  rw [Finset.sum_eq_single 26]
  · simp only [if_true, one_mul]
    rw [Finset.sum_eq_single 27]
    · rw [gram_row_theta 27 (by norm_num)]
      simp
    · intro b hb hb27
      rw [gram_row_theta b (Finset.mem_range.1 hb), if_neg hb27]
      simp
    · intro h
      exact absurd (Finset.mem_range.2 (by norm_num)) h
  · intro a _ ha26
    simp [ha26]
  · intro h
    exact absurd (Finset.mem_range.2 (by norm_num)) h


theorem vanish_top {σ : K ≃+* K} [CharP K 2]
    (hspan : Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ), x = endHom K r (vTheta K)} = ⊤)
    (z : RootModule Tag.D4 K)
    (hz : z ∈ vanishSub (fixedSubgroup (d4Twist 1 σ)) (negLabel isMaxHeightRoot_d4Root_22.1))
    (x : adjointGroup Tag.D4 K) :
    (endHom K x z) (negLabel isMaxHeightRoot_d4Root_22.1) = 0 := by
  have hBz : ∀ u, Bf K u z = 0 := by
    intro u
    have hu : u ∈ Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ),
        x = endHom K r (vTheta K)} := by
      rw [hspan]
      exact Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have e1 := Bf_inv_all r (vTheta K) (endHom K r⁻¹ z)
      have e2 : endHom K r (endHom K r⁻¹ z) = z := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      rw [e2] at e1
      rw [e1, Bf_vTheta, pcoord_eq_negLabel]
      exact mem_vanishSub.1 hz r⁻¹ (inv_mem hr)
    | zero => simp [Bf, Bzk, pcoord]
    | add y y' _ _ h1 h2 => rw [Bf_add_left, h1, h2, add_zero]
    | smul c y _ h => rw [Bf_smul_left, h, mul_zero]
  have e3 : Bf K (vTheta K) (endHom K x z) = Bf K (endHom K x⁻¹ (vTheta K)) z := by
    have := Bf_inv_all x (endHom K x⁻¹ (vTheta K)) z
    have e : endHom K x (endHom K x⁻¹ (vTheta K)) = vTheta K := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rwa [e] at this
  rw [← pcoord_eq_negLabel, ← Bf_vTheta, e3]
  exact hBz _

theorem mem_fixedSubgroup_of_entries_F2 [CharP K 2] {θ : Fin Tag.D4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.D4 θ)
    (hθ22 : θ = d4Root 22) {σ : K ≃+* K} [Finite K]
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (hK3top : 3 ≤ Nat.card (⊤ : Subfield K))
    (hspan : Submodule.span K {x | ∃ r ∈ fixedSubgroup (d4Twist 1 σ), x = endHom K r (vTheta K)} = ⊤)
    {g : adjointGroup Tag.D4 K}
    (hall : ∀ r ∈ fixedSubgroup (d4Twist 1 σ), ∀ r' ∈ fixedSubgroup (d4Twist 1 σ),
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ fixedSubgroup (d4Twist 1 σ) := by
  classical
  subst hθ22
  have hvθ' : rootVec Tag.D4 K (d4Root 22) = Finsupp.single (rootLabel hθ.1) 1 :=
    rootVec_of_isRoot' hθ.1
  let Z : Submodule K (RootModule Tag.D4 K) :=
    vanishSub (fixedSubgroup (d4Twist 1 σ)) (negLabel hθ.1)
  let W : Submodule K (RootModule Tag.D4 K) :=
    Submodule.span K
      {x | ∃ r ∈ (fixedSubgroup (d4Twist 1 σ)), x = endHom K r (rootVec Tag.D4 K (d4Root 22))}
  have hZtop : ∀ z ∈ Z, ∀ x : adjointGroup Tag.D4 K, (endHom K x z) (negLabel hθ.1) = 0 :=
    fun z hz x => vanish_top hspan z hz x
  have hWtop : W = ⊤ := hspan
  have e1 : ∀ r ∈ (fixedSubgroup (d4Twist 1 σ)), ∀ r' ∈ (fixedSubgroup (d4Twist 1 σ)),
      ∀ x : adjointGroup Tag.D4 K,
      (endHom K r (endHom K x (endHom K r' (rootVec Tag.D4 K (d4Root 22))))) (negLabel hθ.1) =
        entry (r * x * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r _ r' _ x
    rw [hvθ', entry, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
      mul_assoc]
  have hD0 : ∀ r' ∈ (fixedSubgroup (d4Twist 1 σ)), ∀ r ∈ (fixedSubgroup (d4Twist 1 σ)),
      entry (r * d4Twist 1 σ g * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r' hr' r hr
    have e : r * d4Twist 1 σ g * r' = d4Twist 1 σ (r * g * r') := by
      rw [map_mul, map_mul, mem_fixedSubgroup.1 hr, mem_fixedSubgroup.1 hr']
    rw [e]
    refine (entry_d4Twist_fixed (K := K) σ (r * g * r') d4_labelPerm_negTheta
      d4_labelPerm_theta).trans ?_
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  have hD : ∀ r' ∈ (fixedSubgroup (d4Twist 1 σ)), (endHom K (d4Twist 1 σ g) - endHom K g)
      (endHom K r' (rootVec Tag.D4 K (d4Root 22))) ∈ Z := by
    intro r' hr'
    refine mem_vanishSub.2 (fun r hr => ?_)
    rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, e1 r hr r' hr' (d4Twist 1 σ g),
      e1 r hr r' hr' g, hD0 r' hr' r hr, sub_self]
  have hDW : ∀ v, (endHom K (d4Twist 1 σ g) - endHom K g) v ∈ Z := by
    have hle : W ≤ Z.comap (endHom K (d4Twist 1 σ g) - endHom K g) :=
      Submodule.span_le.2 (fun x hx => by
        obtain ⟨r', hr', rfl⟩ := hx
        exact (Submodule.mem_comap).2 (hD r' hr'))
    rw [hWtop] at hle
    exact fun v => (Submodule.mem_comap).1 (hle (Submodule.mem_top (x := v)))
  have hx : ∀ v, endHom K (d4Twist 1 σ g * g⁻¹) v - v ∈ Z := by
    intro v
    have hgv : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have e : endHom K (d4Twist 1 σ g * g⁻¹) v - v =
        (endHom K (d4Twist 1 σ g) - endHom K g) (endHom K g⁻¹ v) := by
      rw [map_mul, Module.End.mul_apply, LinearMap.sub_apply, hgv]
    rw [e]
    exact hDW _
  have hx1 : d4Twist 1 σ g * g⁻¹ = 1 :=
    eq_one_of_sub_mem_vanishSub_sl (K := K) d4SimplyLaced hK3top (R := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _) hθ _ (fun v => mem_vanishSub.2 (fun r _ =>
        hZtop _ (hx v) r))
  exact mem_fixedSubgroup.2 (mul_inv_eq_one.1 hx1)


theorem D4TwF2EntryProp_holds : D4TwF2EntryProp := by
  intro K _ _ σ hσ hk g hg
  by_contra h
  push Not at h
  have hσ3 := sigma_cube_of_orderOf hσ
  have h2 : (2 : K) = 0 := by
    have h11 : (1 : K) + 1 ∈ fixSubfield σ :=
      (fixSubfield σ).add_mem (fixSubfield σ).one_mem (fixSubfield σ).one_mem
    rcases zero_or_one_of_mem_card_two hk h11 with h' | h'
    · rw [one_add_one_eq_two] at h'
      exact h'
    · exfalso
      have : (1 : K) = 0 := by
        have := congrArg (fun x => x - 1) h'
        simpa using this
      exact one_ne_zero this
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have h8 : Nat.card K = 8 := by
    have hKcard : Nat.card K = Nat.card (fixSubfield σ) ^ 3 :=
      (CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ).trans (by rw [hσ])
    rw [hKcard, hk]
    norm_num
  have hspan := span_top_K hσ3 h8 hσ
  have h3top : 3 ≤ Nat.card (⊤ : Subfield K) := by
    rw [Nat.card_congr (Subfield.topEquiv : (⊤ : Subfield K) ≃+* K).toEquiv]
    omega
  exact hg (mem_fixedSubgroup_of_entries_F2 d4F2_theta_isMax d4Root_22_eq.symm hσ3 h3top hspan h)

end Entry

end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Entry

end

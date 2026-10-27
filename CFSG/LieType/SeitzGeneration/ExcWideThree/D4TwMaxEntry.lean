module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwMaxSpan
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4MaxEntry

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne.CTP
open scoped commutatorElement

section TwEntry


variable {K : Type} [Field K]

theorem eq_top_of_simple_mem {S : Subgroup (adjointGroup Tag.D4 K)}
    (h : ∀ i : Fin Tag.D4.rank, ∀ c : K,
      xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c ∈ S ∧
        xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c ∈ S) : S = ⊤ := by
  have hw : ∀ i : Fin Tag.D4.rank, CFSG.LieType.Steinberg.weylElement
      (xPar (rootOperatorFamily Tag.D4)) i (1 : Kˣ) ∈ S := by
    intro i
    unfold CFSG.LieType.Steinberg.weylElement
    exact S.mul_mem (S.mul_mem ((h i _).1) ((h i _).2)) ((h i _).1)
  exact eq_top_of_forall_xPar_mem S fun γ hγ c =>
    (xPar_mem_iff_of_roots S hw cartanD4_connected hγ (isRoot_single Tag.D4 (nd 0)) c).2
      ((h (nd 0) c).1)

theorem gInv_of_gamma {σ : K ≃+* K} (hσ3 : ∀ c : K, σ (σ (σ c)) = c)
    (hσ1 : ∃ x : K, σ x ≠ x) (hk3 : 3 ≤ Nat.card (fixSubfield σ))
    {U : Submodule K (RootModule Tag.D4 K)}
    (hU : ∀ r ∈ fixedSubgroup (d4Twist 1 σ), ∀ u ∈ U, endHom K r u ∈ U)
    (g : adjointGroup Tag.D4 K) : ∀ u ∈ U, endHom K g u ∈ U := by
  classical
  let S : Subgroup (adjointGroup Tag.D4 K) :=
    { carrier := {x | ∀ v ∈ U, endHom K x v ∈ U ∧ endHom K x⁻¹ v ∈ U}
      one_mem' := fun v hv => by
        simp only [inv_one, map_one, Module.End.one_apply]
        exact ⟨hv, hv⟩
      mul_mem' := fun {x y} hx hy v hv => by
        refine ⟨?_, ?_⟩
        · rw [map_mul, Module.End.mul_apply]
          exact (hx _ (hy v hv).1).1
        · rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact (hy _ (hx v hv).2).2
      inv_mem' := fun {x} hx v hv => ⟨(hx v hv).2, by rw [inv_inv]; exact (hx v hv).1⟩ }
  have hΓS : ∀ x ∈ fixedSubgroup (d4Twist 1 σ), x ∈ S := fun x hx v hv =>
    ⟨hU x hx v hv, hU x⁻¹ ((fixedSubgroup (d4Twist 1 σ)).inv_mem hx) v hv⟩
  obtain ⟨⟨X₁, X₂, hX⟩, ⟨Y₁, Y₂, hY⟩⟩ := endHom_xPar_simple_poly_sl (K := K) d4SimplyLaced (nd 2)
  have hF : ∀ c ∈ fixSubfield σ, σ c = c := fun c hc => (mem_fixSubfield σ).1 hc
  have hpX : ∀ c : K, ∀ v ∈ U, v + c • X₁ v + c ^ 2 • X₂ v ∈ U := by
    intro c v hv
    refine poly_invariant U X₁ X₂ hk3 (fun c₀ hc₀ z hz => ?_) c hv
    have h1 := hU _ (xPar_e2_mem_fixed hσ3 (hF c₀ hc₀)) z hz
    erw [hX c₀] at h1
    have e : ((1 + c₀ • X₁ + c₀ ^ 2 • X₂ : Module.End K (RootModule Tag.D4 K))) z =
        z + c₀ • X₁ z + c₀ ^ 2 • X₂ z := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← e]
    exact h1
  have hpY : ∀ c : K, ∀ v ∈ U, v + c • Y₁ v + c ^ 2 • Y₂ v ∈ U := by
    intro c v hv
    refine poly_invariant U Y₁ Y₂ hk3 (fun c₀ hc₀ z hz => ?_) c hv
    have h1 := hU _ (xPar_neg_e2_mem_fixed hσ3 (hF c₀ hc₀)) z hz
    erw [hY c₀] at h1
    have e : ((1 + c₀ • Y₁ + c₀ ^ 2 • Y₂ : Module.End K (RootModule Tag.D4 K))) z =
        z + c₀ • Y₁ z + c₀ ^ 2 • Y₂ z := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [← e]
    exact h1
  have hE : ∀ c : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 2) 1) c ∈ S ∧
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 2) 1) c ∈ S := by
    intro c
    constructor
    · intro v hv
      constructor
      · erw [hX c]
        have e : ((1 + c • X₁ + c ^ 2 • X₂ : Module.End K (RootModule Tag.D4 K))) v =
            v + c • X₁ v + c ^ 2 • X₂ v := by
          simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        rw [e]
        exact hpX c v hv
      · erw [xPar_neg, hX (-c)]
        have e : ((1 + (-c) • X₁ + (-c) ^ 2 • X₂ : Module.End K (RootModule Tag.D4 K))) v =
            v + (-c) • X₁ v + (-c) ^ 2 • X₂ v := by
          simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        rw [e]
        exact hpX (-c) v hv
    · intro v hv
      constructor
      · erw [hY c]
        have e : ((1 + c • Y₁ + c ^ 2 • Y₂ : Module.End K (RootModule Tag.D4 K))) v =
            v + c • Y₁ v + c ^ 2 • Y₂ v := by
          simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        rw [e]
        exact hpY c v hv
      · erw [xPar_neg, hY (-c)]
        have e : ((1 + (-c) • Y₁ + (-c) ^ 2 • Y₂ : Module.End K (RootModule Tag.D4 K))) v =
            v + (-c) • Y₁ v + (-c) ^ 2 • Y₂ v := by
          simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
        rw [e]
        exact hpY (-c) v hv
  have hT : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (Pi.single (nd 3) 1) (σ (σ s)) ∈ S :=
    fun s => hΓS _ (triple_pos_mem hσ3 s)
  have hTm : ∀ s : K, xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 0) 1) s *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 1) 1) (σ s) *
      xPar (rootOperatorFamily Tag.D4) (-Pi.single (nd 3) 1) (σ (σ s)) ∈ S :=
    fun s => hΓS _ (triple_neg_mem hσ3 s)
  obtain ⟨o0, o1, o3⟩ := outer_root_mem_of_triples hσ3 hσ1 hE hT hTm
  have hST : S = ⊤ := by
    refine eq_top_of_simple_mem fun i c => ?_
    fin_cases i
    · exact o0 c
    · exact o1 c
    · exact hE c
    · exact o3 c
  have hg : g ∈ S := by
    rw [hST]
    exact Subgroup.mem_top g
  exact fun u hu => (hg u hu).1

section EntryTwist

theorem d4P_single_fixed {b : Label TwistTag.D4.tag}
    (hb : labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm b = b) :
    (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K))
      (Finsupp.single b 1) = Finsupp.single b 1 := by
  rw [show (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K))
      (Finsupp.single b 1) = Finsupp.single (labelPerm TwistTag.D4.perm
        TwistTag.D4.cartan_perm b) 1 from
    Finsupp.domLCongr_single (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm) b 1, hb]

theorem d4P_apply_fixed (w : RootModule TwistTag.D4.tag K) {a : Label TwistTag.D4.tag}
    (ha : labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm a = a) :
    (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K)) w a = w a := by
  have h : (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K)) w
      (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm a) = w a := by
    change Finsupp.equivMapDomain (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm) w
      (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm a) = w a
    rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  rw [ha] at h
  exact h

theorem d4Pinv_single_fixed {b : Label TwistTag.D4.tag}
    (hb : labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm b = b) :
    (((diagramMap TwistTag.D4 K)⁻¹ : ModGL TwistTag.D4.tag K) :
        Module.End K (RootModule TwistTag.D4.tag K)) (Finsupp.single b 1) =
      Finsupp.single b 1 := by
  have hinv : (((diagramMap TwistTag.D4 K)⁻¹ : ModGL TwistTag.D4.tag K) :
      Module.End K (RootModule TwistTag.D4.tag K)) *
      (diagramMap TwistTag.D4 K : Module.End K (RootModule TwistTag.D4.tag K)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  conv_lhs => rw [← d4P_single_fixed (K := K) hb]
  rw [← Module.End.mul_apply, hinv, Module.End.one_apply]

theorem endHom_d4Twist_apply (σ : K ≃+* K) (y : adjointGroup Tag.D4 K) (v : RootModule Tag.D4 K) :
    endHom K (d4Twist 1 σ y) v =
      ((diagramMap TwistTag.D4 K : ModGL TwistTag.D4.tag K) :
          Module.End K (RootModule TwistTag.D4.tag K))
        (entrywise σ.toRingHom (endHom K y)
          ((((diagramMap TwistTag.D4 K)⁻¹ : ModGL TwistTag.D4.tag K) :
            Module.End K (RootModule TwistTag.D4.tag K)) v)) := by
  show (((d4Twist 1 σ y : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) :
      Module.End K (RootModule Tag.D4 K)) v = _
  rw [d4Twist_one_eq_twistC]
  erw [coe_twistC]
  erw [coe_twistHom]
  rfl

theorem entry_d4Twist_fixed (σ : K ≃+* K) (y : adjointGroup Tag.D4 K)
    {a b : Label TwistTag.D4.tag}
    (ha : labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm a = a)
    (hb : labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm b = b) :
    entry (d4Twist 1 σ y) a b = σ (entry y a b) := by
  unfold entry
  erw [endHom_d4Twist_apply, d4Pinv_single_fixed (K := K) hb, entrywise_single,
    d4P_apply_fixed _ ha,
    Finsupp.mapRange_apply]

theorem d4_labelPerm_theta :
    labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm
      (rootLabel isMaxHeightRoot_d4Root_22.1) = rootLabel isMaxHeightRoot_d4Root_22.1 := by
  change Sum.inr _ = Sum.inr _
  congr 1
  apply Subtype.ext
  exact rho_d4Root_22

theorem d4_labelPerm_negTheta :
    labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm
      (negLabel isMaxHeightRoot_d4Root_22.1) = negLabel isMaxHeightRoot_d4Root_22.1 := by
  change Sum.inr _ = Sum.inr _
  congr 1
  apply Subtype.ext
  show permLattice TwistTag.D4.perm (-(d4Root 22)) = -(d4Root 22)
  rw [permLattice_neg]
  exact congrArg Neg.neg rho_d4Root_22

end EntryTwist

theorem mem_fixedSubgroup_of_entries_twD4 {σ : K ≃+* K} [Finite K]
    (hσ3 : ∀ c : K, σ (σ (σ c)) = c) (hσ1 : ∃ x : K, σ x ≠ x)
    (hk3 : 3 ≤ Nat.card (fixSubfield σ)) {g : adjointGroup Tag.D4 K}
    (hall : ∀ r ∈ fixedSubgroup (d4Twist 1 σ), ∀ r' ∈ fixedSubgroup (d4Twist 1 σ),
      entry (r * g * r') (negLabel isMaxHeightRoot_d4Root_22.1)
        (rootLabel isMaxHeightRoot_d4Root_22.1) ∈ fixSubfield σ) :
    g ∈ fixedSubgroup (d4Twist 1 σ) := by
  classical
  have hθ := isMaxHeightRoot_d4Root_22
  have hvθ' : rootVec Tag.D4 K (d4Root 22) = Finsupp.single (rootLabel hθ.1) 1 :=
    rootVec_of_isRoot' hθ.1
  let Z : Submodule K (RootModule Tag.D4 K) :=
    vanishSub (fixedSubgroup (d4Twist 1 σ)) (negLabel hθ.1)
  let W : Submodule K (RootModule Tag.D4 K) :=
    Submodule.span K
      {x | ∃ r ∈ (fixedSubgroup (d4Twist 1 σ)), x = endHom K r (rootVec Tag.D4 K (d4Root 22))}
  have hZΓ : ∀ r ∈ (fixedSubgroup (d4Twist 1 σ)), ∀ z ∈ Z, endHom K r z ∈ Z := by
    intro r hr z hz
    refine mem_vanishSub.2 (fun r' hr' => ?_)
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem_vanishSub.1 hz (r' * r) ((fixedSubgroup (d4Twist 1 σ)).mul_mem hr' hr)
  have hZG : ∀ x : adjointGroup Tag.D4 K, ∀ z ∈ Z, endHom K x z ∈ Z :=
    fun x z hz => gInv_of_gamma hσ3 hσ1 hk3 hZΓ x z hz
  have hZtop : ∀ z ∈ Z, ∀ x : adjointGroup Tag.D4 K, (endHom K x z) (negLabel hθ.1) = 0 := by
    intro z hz x
    have h1 := mem_vanishSub.1 (hZG x z hz) 1 (fixedSubgroup (d4Twist 1 σ)).one_mem
    rwa [map_one, Module.End.one_apply] at h1
  have hWΓ : ∀ r ∈ (fixedSubgroup (d4Twist 1 σ)), ∀ w ∈ W, endHom K r w ∈ W := by
    intro r hr w hw
    refine Submodule.span_induction (p := fun w _ => endHom K r w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', (fixedSubgroup (d4Twist 1 σ)).mul_mem hr hr', by
        rw [map_mul, Module.End.mul_apply]⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact W.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact W.smul_mem a hx
  have hvW : rootVec Tag.D4 K (d4Root 22) ∈ W :=
    Submodule.subset_span
      ⟨1, (fixedSubgroup (d4Twist 1 σ)).one_mem, by rw [map_one, Module.End.one_apply]⟩
  have hWG : ∀ x : adjointGroup Tag.D4 K, ∀ w ∈ W, endHom K x w ∈ W :=
    fun x w hw => gInv_of_gamma hσ3 hσ1 hk3 hWΓ x w hw
  have hWtop : W = ⊤ := by
    have hsp := span_orbit_eq_top_sl (K := K) d4SimplyLaced (k := ⊥) (R := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _) hθ
    have hle : Submodule.span K {x | ∃ r ∈ (⊤ : Subgroup (adjointGroup Tag.D4 K)),
        x = endHom K r (rootVec Tag.D4 K (d4Root 22))} ≤ W :=
      Submodule.span_le.2 (fun x hx => by
        obtain ⟨r, -, rfl⟩ := hx
        exact hWG r _ hvW)
    rw [hsp] at hle
    exact eq_top_iff.2 hle
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
    eq_one_of_sub_mem_vanishSub_sl (K := K) d4SimplyLaced hk3 (R := ⊤)
      (fun _ _ _ _ => Subgroup.mem_top _) hθ _ (fun v => mem_vanishSub.2 (fun r _ =>
        hZtop _ (hx v) r))
  exact mem_fixedSubgroup.2 (mul_inv_eq_one.1 hx1)

end TwEntry

end CFSG.LieType.SeitzGeneration.ExcWideThree

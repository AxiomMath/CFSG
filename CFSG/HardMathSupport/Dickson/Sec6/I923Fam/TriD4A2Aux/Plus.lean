module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Fold
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Final
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Main

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}

theorem hexPos_one_eq : hexPos 1 = (Pi.single (ng 1) 1 : Fin Tag.G2.rank → ℤ) := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 400000 in
theorem a2_slShort_upper_mem_hex (h : A2Std σ d q) (c : K) :
    slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper c) ∈
      hexGroup (twistedX σ.toRingHom) 1 := by
  have hx := xOuter_mem σ.toRingHom (s := 1) (Or.inl rfl) (c := c) (a2sl_sigma_three h c)
  rw [one_smul] at hx
  refine (mem_twistedRootGroup (σ := σ.toRingHom) (β := hexPos 1)).2 ?_
  rw [hexPos_one_eq, slShort_upper]
  exact hx

@[expose] def a2SlHom (h : A2Std σ d q) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) →* twistedGroup σ.toRingHom :=
  (slShort σ.toRingHom (a2sl_sigma_three h)).comp
    (Matrix.SpecialLinearGroup.map (fixedField σ.toRingHom).subtype)

theorem a2SlHom_upper (h : A2Std σ d q) (c : fixedField σ.toRingHom) :
    a2SlHom h (sl2Upper c) = slShort σ.toRingHom (a2sl_sigma_three h) (sl2Upper (c : K)) := by
  simp only [a2SlHom, MonoidHom.comp_apply, a2sl_map_upper]

theorem a2SlHom_lower (h : A2Std σ d q) (c : fixedField σ.toRingHom) :
    a2SlHom h (sl2Lower c) = slShort σ.toRingHom (a2sl_sigma_three h) (sl2Lower (c : K)) := by
  simp only [a2SlHom, MonoidHom.comp_apply, a2sl_map_lower]

theorem a2SlHom_fixed (h : A2Std σ d q) (y : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :
    a2Conj σ d (((a2SlHom h y : twistedGroup σ.toRingHom) : adjointGroup d4 K) :
      ModGL TwistTag.D4.tag K) =
      (((a2SlHom h y : twistedGroup σ.toRingHom) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
  let ι : twistedGroup σ.toRingHom →* ModGL TwistTag.D4.tag K :=
    (adjointGroup d4 K).subtype.comp (twistedGroup σ.toRingHom).subtype
  have hu : ∀ c : fixedField σ.toRingHom, ι (a2SlHom h (sl2Upper c)) ∈ a2slFix σ d := fun c => by
    rw [a2SlHom_upper]
    exact a2sl_mem_fix.2 (a2sl_upper_fixed h c.2)
  have hl : ∀ c : fixedField σ.toRingHom, ι (a2SlHom h (sl2Lower c)) ∈ a2slFix σ d := fun c => by
    rw [a2SlHom_lower]
    exact a2sl_mem_fix.2 (a2sl_lower_fixed h c.2)
  obtain ⟨e, a, b, c, rfl⟩ := sl2_eq_prod y
  have : ι (a2SlHom h (sl2Lower e * sl2Upper a * sl2Lower b * sl2Upper c)) ∈ a2slFix σ d := by
    simp only [map_mul]
    exact mul_mem (mul_mem (mul_mem (hl e) (hu a)) (hl b)) (hu c)
  exact a2sl_mem_fix.1 this

theorem a2_finite (h : A2Std σ d q) : Finite (twistedGroup σ.toRingHom) :=
  Finite.of_equiv _ (a2Equiv h).symm.toEquiv

theorem card_fixedField_a2 (h : A2Std σ d q) : Nat.card (fixedField σ.toRingHom) = q :=
  card_fixedField_of_cube σ.toRingHom h.two_le h.card h.frob

theorem four_le_a2 (h : A2Std σ d q) : 4 ≤ q := by
  have := h.two_le
  have := h.mod3
  omega

variable (h : A2Std σ d q)
  (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

@[expose] def a2SlFixHom :
    Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom) →* ↥(foldFix (a2Phi h φ)) :=
  (a2SlHom h).codRestrict (foldFix (a2Phi h φ))
    (fun y => (a2Phi_eq_iff h φ hφ _).2 (a2SlHom_fixed h y))

theorem a2SlFixHom_coe (y : Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :
    ((a2SlFixHom h φ hφ y : ↥(foldFix (a2Phi h φ))) : twistedGroup σ.toRingHom) = a2SlHom h y :=
  rfl

theorem a2SlFixHom_range_perfect :
    ⁅(a2SlFixHom h φ hφ).range, (a2SlFixHom h φ hφ).range⁆ = (a2SlFixHom h φ hφ).range := by
  have h4 : 4 ≤ Nat.card (fixedField σ.toRingHom) := by
    rw [card_fixedField_a2 h]
    exact four_le_a2 h
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (fixedField σ.toRingHom)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect
      (CFSG.LinearGroups.exists_finset_card_eq_four h4)
  haveI : Group.IsPerfect (a2SlFixHom h φ hφ).range := Group.IsPerfect.range _
  exact Subgroup.isPerfect_iff.1 inferInstance

set_option maxHeartbeats 400000 in
theorem a2_root_one_le_range :
    ∀ x ∈ foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) 1,
      ∃ hx : x ∈ foldFix (a2Phi h φ),
        (⟨x, hx⟩ : ↥(foldFix (a2Phi h φ))) ∈ (a2SlFixHom h φ hφ).range := by
  haveI := a2_finite h
  set G := ↥(foldFix (a2Phi h φ)) with hG
  set E : Subgroup G := (a2SlFixHom h φ hφ).range with hE
  have hle1 : foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) 1 ≤
      foldFix (a2Phi h φ) := inf_le_right
  set F1 : Subgroup G :=
    (foldRoot (a2Phi h φ) (hexGroup (twistedX σ.toRingHom)) 1).subgroupOf (foldFix (a2Phi h φ))
    with hF1
  have hroot1 : CFSG.GH74.BNPair.IsRoot 3 1 := ⟨by norm_num, by norm_num⟩
  have hcardF1 : Nat.card F1 = q := by
    rw [hF1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle1).toEquiv]
    exact a2_card_foldRoot h φ hφ hroot1
  have hF1mem : ∀ c : fixedField σ.toRingHom, a2SlFixHom h φ hφ (sl2Upper c) ∈ F1 := by
    intro c
    rw [hF1, Subgroup.mem_subgroupOf]
    refine ⟨?_, (a2SlFixHom h φ hφ (sl2Upper c)).2⟩
    show _ ∈ hexGroup (twistedX σ.toRingHom) (foldIdx 1)
    have : foldIdx 1 = 1 := by simp [foldIdx]
    rw [this, a2SlFixHom_coe, a2SlHom_upper]
    exact a2_slShort_upper_mem_hex h _
  have hmem : ∀ c : fixedField σ.toRingHom,
      a2SlFixHom h φ hφ (sl2Upper c) ∈ E ⊓ F1 := fun c =>
    Subgroup.mem_inf.2 ⟨⟨_, rfl⟩, hF1mem c⟩
  let f : fixedField σ.toRingHom → ↥(E ⊓ F1) := fun c => ⟨_, hmem c⟩
  have hf : Function.Injective f := by
    intro c c' hcc'
    have h1 := congrArg (fun z : ↥(E ⊓ F1) => ((z : G) : twistedGroup σ.toRingHom)) hcc'
    simp only [f, a2SlFixHom_coe, a2SlHom_upper] at h1
    have h2 := slShort_injective (a2sl_sigma_three h) h1
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) K =>
      (M : Matrix (Fin 2) (Fin 2) K) 0 1) h2
    simp [CFSG.LieType.Steinberg.coe_sl2Upper] at h3
    exact h3
  have hle : E ⊓ F1 ≤ F1 := inf_le_right
  have hcard : Nat.card F1 ≤ Nat.card ↥(E ⊓ F1) := by
    calc Nat.card F1 = q := hcardF1
      _ = Nat.card (fixedField σ.toRingHom) := (card_fixedField_a2 h).symm
      _ ≤ Nat.card ↥(E ⊓ F1) := Nat.card_le_card_of_injective f hf
  have heq : E ⊓ F1 = F1 := Subgroup.eq_of_le_of_card_ge hle hcard
  intro x hx
  have hxG : x ∈ foldFix (a2Phi h φ) := hx.2
  refine ⟨hxG, ?_⟩
  have hxF1 : (⟨x, hxG⟩ : G) ∈ F1 := by
    rw [hF1, Subgroup.mem_subgroupOf]
    exact hx
  rw [← heq] at hxF1
  exact (Subgroup.mem_inf.1 hxF1).1

theorem cofactor_plus_le {q : ℕ} (hq : 1 ≤ q) :
    (q - 1) ^ 2 * ((q + 1) * (q ^ 2 + q + 1)) ≤ q ^ 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  nlinarith [Nat.zero_le m, pow_nonneg (Nat.zero_le m) 2, pow_nonneg (Nat.zero_le m) 3,
    pow_nonneg (Nat.zero_le m) 4, pow_nonneg (Nat.zero_le m) 5]

theorem exists_noncomm_of_perfect {G : Type*} [Group G] (S : Subgroup G) (hS : S ≠ ⊥)
    (hperf : ⁅S, S⁆ = S) : ∃ a b : ↥S, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  apply hS
  rw [← hperf, eq_bot_iff]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have := hcon ⟨a, ha⟩ ⟨b, hb⟩
  have h1 : a * b = b * a := congrArg Subtype.val this
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 h1

set_option maxHeartbeats 400000 in
theorem noL2Layer_a2_plus {p f : ℕ} (hp : p.Prime) (h : A2Std σ d (p ^ f)) (hq5 : 5 ≤ p ^ f)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, d, 1]) :
    NoL2Layer (MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ) := by
  set φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφdef
  have hφ := a2_hφ_of_class (σ := σ) (d := d) hs
  haveI := a2_finite h
  haveI : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    Finite.of_equiv _ (a2Equiv h).toEquiv
  have hFD := a2_foldData h φ hφ
  have hgen : ((⨆ i, hHat σ.toRingHom i) ⊔ posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊔
      (d4RGD2 σ.toRingHom h.cube_apply).N = ⊤ :=
    hexRGD2_gen (twistedData σ.toRingHom h.cube_apply)
  obtain ⟨S, hSn, hsol, hperf, hsimple, hUS⟩ := fold_residual_simple hFD hgen
    (fun g _ hcomm => a2_hZ h hcomm) (fun x hx => a2_hz h φ hφ x hx) (a2_hC h φ hφ)
    (a2SlFixHom h φ hφ).range (a2SlFixHom_range_perfect h φ hφ) (a2_root_one_le_range h φ hφ)
  let e0 : ↥(foldFix (a2Phi h φ)) ≃* ↥(fixSub φ) :=
    (MulEquiv.subgroupMap (a2Equiv h) (foldFix (a2Phi h φ))).trans
      (MulEquiv.subgroupCongr (a2_foldFix_map h φ hφ))
  let ef : ↥(fixSubgroup φ) ≃* ↥(fixSub φ) := MulEquiv.subgroupCongr (by
    ext x
    rfl)
  let e : ↥(fixSubgroup φ) ≃* ↥(foldFix (a2Phi h φ)) := ef.trans e0.symm
  have hcardG : Nat.card ↥(foldFix (a2Phi h φ)) =
      (p ^ f) ^ 3 * ((p ^ f - 1) ^ 2 * ((p ^ f + 1) * ((p ^ f) ^ 2 + p ^ f + 1))) := by
    rw [Nat.card_congr e0.toEquiv, a2_card_fixSub h φ hφ]
    ring
  have hSne : S ≠ ⊥ := by
    haveI := hsimple
    exact (Subgroup.nontrivial_iff_ne_bot S).1 IsSimpleGroup.toNontrivial
  have hnab := exists_noncomm_of_perfect S hSne hperf
  obtain ⟨r₁', r₂', -, -, -, -, R'⟩ := hFD.exists_rgd2
  have hcardU := a2_card_U_fix h φ hφ R'
  have hxS : (p ^ f) ^ 3 ∣ Nat.card ↥S := by
    have hle : ((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓ foldFix (a2Phi h φ)).subgroupOf
        (foldFix (a2Phi h φ)) ≤ S := by
      intro g hg
      obtain ⟨hu, hgS⟩ := hUS g.1 hg
      exact hgS
    have hc : Nat.card ↥(((posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
        foldFix (a2Phi h φ)).subgroupOf (foldFix (a2Phi h φ))) = (p ^ f) ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : (posUnipotent (g2Shape (twistedX σ.toRingHom))) ⊓
          foldFix (a2Phi h φ) ≤ foldFix (a2Phi h φ))).toEquiv]
      exact hcardU
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  have hSC : Nat.card ↥S ≤ (p ^ f) ^ 3 *
      ((p ^ f - 1) ^ 2 * ((p ^ f + 1) * ((p ^ f) ^ 2 + p ^ f + 1))) := by
    rw [← hcardG]
    exact Subgroup.card_le_card_group S
  have hkey := key_of_le_pow_five (q := p ^ f) (by omega) (cofactor_plus_le (by omega))
  have hxpp : (p ^ f) ^ 3 = 1 ∨ IsPrimePow ((p ^ f) ^ 3) := by
    rw [← pow_mul]
    exact isPrimePow_or_one hp
  exact noL2Layer_of_simple_normal φ e S hsol hsimple hnab hxpp hxS hSC hkey

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

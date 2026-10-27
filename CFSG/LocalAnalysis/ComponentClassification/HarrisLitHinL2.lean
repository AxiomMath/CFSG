module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinBasic
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterDiag
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.GH74.KGroups.PSLN
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield

public section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup GorensteinWalter AutL2Facts CatalogueSchreierLinearTwo

theorem commutator_self_eq_of_isPerfect' {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) : ⁅H, H⁆ = H := by
  have h := congrArg (Subgroup.map H.subtype) hH.commutator_eq_top
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact h

theorem le_perfectResidual_of_isPerfect {G : Type*} [Group G] {H : Subgroup G}
    (hH : Group.IsPerfect H) : H ≤ perfectResidual G := by
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact le_top
  | succ n ih =>
    rw [derivedSeries_succ, ← commutator_self_eq_of_isPerfect' hH]
    exact Subgroup.commutator_mono ih ih

section Odd

variable {F : Type} [Field F] [Finite F]

theorem eq_one_of_commute_psl2
    (hodd : IsOddPrimePower (Nat.card F)) {L : Subgroup (PSL2 F)}
    {p m : ℕ} (hp2 : p ≠ 2) (hL : Blueprint.LieModel ↥L .PSL 2 p m) {c : PGL2 F}
    (hc : ∀ l ∈ L, Matrix.ProjectiveSpecialLinearGroup.toPGL l * c =
      c * Matrix.ProjectiveSpecialLinearGroup.toPGL l) : c = 1 := by
  classical
  have := isSimpleGroup_of_lieModel_psl2 hL
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  obtain ⟨k, hk, ⟨eS⟩⟩ := hasDihedralSylowTwo_of_lieModel_psl2 hp2 hL S
  obtain ⟨W, -, hW⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv (S : Subgroup ↥L) hk eS
  let ψ : ↥L →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL.comp L.subtype
  have hψ : Function.Injective ψ :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp Subtype.val_injective
  set V : Subgroup (PGL2 F) := W.map ψ
  let eW : ↥W ≃* ↥V := W.equivMapOfInjective ψ hψ
  have hV : IsKleinFour ↥V :=
    ⟨(Nat.card_congr eW.toEquiv).symm.trans hW.card_four,
      (Monoid.exponent_eq_of_mulEquiv eW).symm.trans hW.exponent_two⟩
  have hcent := pgl2_kleinFour_centralizer_eq_self F hodd V hV
  have hcV : c ∈ V := by
    rw [← hcent, mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    exact hc w.1 w.2
  obtain ⟨w, -, hwc⟩ := hcV
  have hwz : w ∈ center ↥L := by
    rw [mem_center_iff]
    intro z
    apply hψ
    rw [map_mul, map_mul, hwc]
    exact hc z.1 z.2
  rw [(LocalCores.isQuasisimple_of_isSimpleGroup (nonabelian_of_lieModel_psl2 hL)).2,
    mem_bot] at hwz
  rw [← hwc, hwz, map_one]

theorem right_ne_one_of_fixes
    {Y : Type} [Group Y] [Finite Y] (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F)
    {τ : MulAut Y} (hτ : τ ≠ 1) {L : Subgroup Y} (hLτ : ∀ y ∈ L, τ y = y) {p m : ℕ}
    (hp2 : p ≠ 2) (hL : Blueprint.LieModel ↥L .PSL 2 p m) : (autEquiv e τ).right ≠ 1 := by
  intro hr
  set g := autEquiv e τ with hgdef
  have hg : g = SemidirectProduct.inl g.left := by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
    rw [hr, map_one, mul_one]
  have hL' : Blueprint.LieModel ↥(L.map e.toMonoidHom) .PSL 2 p m :=
    lieModel_psl2_of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective).symm hL
  have hc : g.left = 1 := by
    refine eq_one_of_commute_psl2 hodd hp2 hL' fun l hl => ?_
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hl
    have h1 := semilinearAction_autEquiv_apply e τ y
    rw [hLτ y hy, ← hgdef, hg, semilinearAction_inl] at h1
    have h3 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h1
    rw [toPGL_pglAction] at h3
    change Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) * g.left =
      g.left * Matrix.ProjectiveSpecialLinearGroup.toPGL (e y)
    calc Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) * g.left
        = (g.left * Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) * g.left⁻¹) * g.left := by
          rw [h3]
      _ = g.left * Matrix.ProjectiveSpecialLinearGroup.toPGL (e y) := by group
  apply hτ
  apply (autEquiv e).injective
  rw [map_one, ← hgdef, hg, hc, map_one]

theorem card_eq_of_field {Y : Type} [Group Y] [Finite Y]
    (hodd : IsOddPrimePower (Nat.card F)) (e : Y ≃* PSL2 F) {τ : MulAut Y}
    (hτ : orderOf τ = 2) (hr : (autEquiv e τ).right ≠ 1) {p m : ℕ} (hp2 : p ≠ 2)
    (h16 : 16 ∣ p ^ (2 * m) - 1)
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn (fixedPoints τ)) .PSL 2 p m) :
    Nat.card F = p ^ (2 * m) := by
  classical
  set g := autEquiv e τ with hgdef
  have hg2 : orderOf g = 2 := by rw [hgdef, MulEquiv.orderOf_eq]; exact hτ
  set σ := g.right with hσdef
  have hσ2 : orderOf σ = 2 := by
    have hsq : g ^ orderOf g = 1 := pow_orderOf_eq_one g
    rw [hg2] at hsq
    have h1 := congrArg SemidirectProduct.right hsq
    rw [pow_two, SemidirectProduct.mul_right, ← pow_two, SemidirectProduct.one_right] at h1
    exact orderOf_eq_prime h1 hr
  obtain ⟨C₁, hC₁⟩ := exists_conj_inr_of_involution hodd g hg2 hr
  set h : PGammaL2 F := SemidirectProduct.inl C₁
  let E : Y ≃* PSL2 F := e.trans (semilinearAction F h⁻¹)
  have hE : ∀ y, E (τ y) = psl2FieldAut F σ (E y) := by
    intro y
    have h1 := semilinearAction_autEquiv_apply e τ y
    change semilinearAction F h⁻¹ (e (τ y)) = psl2FieldAut F σ (semilinearAction F h⁻¹ (e y))
    rw [← h1, ← semilinearAction_inr, ← hC₁, ← hgdef]
    simp only [map_mul, map_inv, MulAut.mul_apply]
    congr 2
    exact ((semilinearAction F h).apply_symm_apply (e y)).symm
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ2
  have hσσ : ∀ z, σ (σ z) = z := fun z => by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ2, pow_orderOf_eq_one]
    have := congrArg (fun ρ : F ≃+* F => ρ z) h1
    simpa using this
  have hFodd : Odd (Nat.card F) := by
    obtain ⟨p', n, -, hpodd, -, hc⟩ := hodd
    rw [hc]
    exact hpodd.pow
  have hK₀odd' : Odd (Nat.card K₀) := by
    rw [hcard] at hFodd
    exact Nat.Odd.of_mul_left (by rwa [← pow_two])
  have hK₀odd : IsOddPrimePower (Nat.card K₀) := isOddPrimePower_of_odd_card _ hK₀odd'
  set C := fixedPoints τ with hCdef
  have hmemC : ∀ y : Y, y ∈ C ↔ E y ∈ fieldCent σ := by
    intro y
    change τ y = y ↔ psl2FieldAut F σ (E y) = E y
    rw [← hE, E.injective.eq_iff]
  have hmap : C.map E.toMonoidHom = fieldCent σ := by
    ext z
    rw [Subgroup.mem_map_equiv, hmemC, MulEquiv.apply_symm_apply]
  have hCcard : Nat.card C = Nat.card (PGL2 K₀) := by
    rw [← card_fieldCent_eq hK₀ h90 hσσ hcard hodd, ← hmap,
      Subgroup.card_map_of_injective E.injective]
  have h168 := le_card_of_lieModel_psl2_sixteen hp2 h16 hL
  have hLC : Nat.card ↥(GSThmB.layerIn C) ≤ Nat.card C :=
    Subgroup.card_le_of_le (map_subtype_le _)
  have hK₀3 : 3 < Nat.card K₀ := by
    by_contra hle
    push Not at hle
    have h1 : 1 < Nat.card K₀ := Finite.one_lt_card
    obtain ⟨j, hj⟩ := hK₀odd'
    have h3 : Nat.card K₀ = 3 := by omega
    rw [hCcard, pgl2_card_formula, h3] at hLC
    omega
  have : Group.IsPerfect (PSL2 K₀) := psl2_isPerfect_of_card_gt_three K₀ hK₀3
  have hsK : IsSimpleGroup (PSL2 K₀) :=
    BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  let ψ : PSL2 K₀ →* C := (E.symm.toMonoidHom.comp (psl2Sub K₀)).codRestrict C fun x =>
    (hmemC _).mpr (by
      show E (E.symm (psl2Sub K₀ x)) ∈ fieldCent σ
      rw [MulEquiv.apply_symm_apply]
      exact psl2Sub_mem_fieldCent hK₀ x)
  have hψ : Function.Injective ψ := fun a b hab =>
    psl2Sub_injective K₀ (E.symm.injective (congrArg Subtype.val hab))
  have hPR : perfectResidual C = ψ.range := by
    refine perfectResidual_eq_of_two_mul (Group.IsPerfect.range ψ) ?_
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, hCcard, pgl2_card_eq_two_mul hK₀odd]
  have hq := isComponent_pLayer hL
  have hLP : pLayer ↥C 2 ≤ ψ.range := by
    rw [← hPR]
    exact le_perfectResidual_of_isPerfect hq.1.1
  have hPs : IsSimpleGroup ψ.range := (MonoidHom.ofInjective hψ).symm.isSimpleGroup
  have hnorm : ((pLayer ↥C 2).subgroupOf ψ.range).Normal :=
    (pLayer_two_normal C).subgroupOf _
  have hLeq : pLayer ↥C 2 = ψ.range := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((pLayer ↥C 2).subgroupOf ψ.range) with
      hb | ht
    · exfalso
      have hs := isSimpleGroup_pLayer hL
      obtain ⟨⟨x, hxL⟩, hx⟩ := exists_ne (1 : ↥(pLayer ↥C 2))
      have hxm : (⟨x, hLP hxL⟩ : ↥ψ.range) ∈ (pLayer ↥C 2).subgroupOf ψ.range := hxL
      rw [hb, mem_bot] at hxm
      have hx1 : x = 1 := congrArg Subtype.val hxm
      exact hx (Subtype.ext hx1)
    · exact le_antisymm hLP (subgroupOf_eq_top.mp ht)
  obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hF'odd : IsOddPrimePower (Nat.card F') := isOddPrimePower_of hpP hp2 hm1 hF'
  have hcards : Nat.card (PSL2 K₀) = Nat.card (PSL2 F') := by
    rw [Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, ← hLeq,
      ← Nat.card_congr (layerInEquiv C).toEquiv, Nat.card_congr eL.toEquiv]
  have hK₀card : Nat.card K₀ = p ^ m := by rw [card_eq_of_psl2_card_eq hK₀odd hF'odd hcards, hF']
  rw [hcard, hK₀card, ← pow_mul, mul_comm]

theorem hinFor_psl2_odd :
    HinFor fun Y _ => ∃ ℓ f : ℕ, ℓ ≠ 2 ∧ Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 ℓ f := by
  intro Y _ _ _ ⟨ℓ, f, hℓ2, hY⟩ _ p m hp hp2 hm h16 _ τ hτ hL
  obtain ⟨⟨hℓ, hf, -, -, -⟩, F, _, _, hF, ⟨e₀⟩⟩ := hY
  let e : Y ≃* PSL2 F :=
    e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  have hodd : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hℓ hℓ2 hf hF
  have hτ1 : τ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hτ
    norm_num at hτ
  have hr : (autEquiv e τ).right ≠ 1 :=
    right_ne_one_of_fixes hodd e hτ1 (fun y hy => (map_subtype_le _ hy : y ∈ fixedPoints τ))
      hp2 hL
  have hout : τ ∉ innAut Y := by
    rintro ⟨y, rfl⟩
    exact hr (by rw [autEquiv_conj, incl_apply, SemidirectProduct.right_inl])
  refine hinConcl_of_list hout (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))
  have hcard := card_eq_of_field hodd e hτ hr hp2 h16 hL
  have h9 : 9 ≤ p ^ (2 * m) := by
    have h3 : 3 ≤ p := by
      rcases hp.eq_two_or_odd' with h | h
      · exact (hp2 h).elim
      · obtain ⟨k, hk⟩ := h
        have := hp.two_le
        omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ p ^ (2 * m) := Nat.pow_le_pow_right (by omega) (by omega)
  refine Or.inl ⟨by simp [Blueprint.classicalTags], ⟨hp, by omega, le_rfl, ?_, ?_⟩, F,
    inferInstance, inferInstance, hcard, ⟨e₀⟩⟩
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega
  · intro h
    simp only [Prod.mk.injEq, true_and] at h
    omega

end Odd

theorem exists_orderOf_four_of_lieModel_psl2 {L : Type} [Group L] [Finite L] {p m : ℕ}
    (hp2 : p ≠ 2) (h16 : 16 ∣ p ^ (2 * m) - 1) (hL : Blueprint.LieModel L .PSL 2 p m) :
    ∃ x : L, orderOf x = 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 L) := inferInstance
  obtain ⟨k, hk, ⟨eS⟩⟩ := hasDihedralSylowTwo_of_lieModel_psl2 hp2 hL S
  have h8 : 2 ^ 3 ∣ Nat.card L := by
    obtain ⟨hpP, hm1, -, F', _, _, hF', ⟨e⟩⟩ := exists_psl2_of_lieModel hL
    rw [Nat.card_congr e.toEquiv, psl2_card_formula F' (isOddPrimePower_of hpP hp2 hm1 hF'), hF']
    have hq2 : p ^ (2 * m) = (p ^ m) ^ 2 := by rw [← pow_mul, mul_comm]
    rw [hq2] at h16
    obtain ⟨t, ht⟩ := h16
    rw [ht, show p ^ m * (16 * t) = 2 * (2 ^ 3 * (p ^ m * t)) by ring,
      Nat.mul_div_cancel_left _ (by norm_num)]
    exact Dvd.intro _ rfl
  have h8S := Sylow.pow_dvd_card_of_pow_dvd_card S h8
  rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card] at h8S
  have hk2 : 2 ≤ k := by
    by_contra hlt
    push Not at hlt
    interval_cases k
    norm_num at h8S
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  have hval : ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)).val = 2 ^ (k - 2) :=
    ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hord : orderOf (DihedralGroup.r ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k))) = 4 := by
    rw [DihedralGroup.orderOf_r, hval, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega)),
      Nat.pow_div (by omega) (by norm_num), show k - (k - 2) = 2 by omega]
  refine ⟨(eS.symm (DihedralGroup.r ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k))) : L), ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]

theorem orderOf_ne_four_psl2Model {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 1 ≤ n)
    (e : X ≃* Theory.Comparator.PSL2Model n) (g : X) : orderOf g ≠ 4 := by
  intro hg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have : Finite (Theory.Comparator.PSL2Model n) := Finite.of_equiv X e.toEquiv
  have hg' : orderOf (e g) = 4 := by rw [MulEquiv.orderOf_eq, hg]
  have hp : IsPGroup 2 (Subgroup.zpowers (e g)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hg']; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨f⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF Q
  have hgQ : e g ∈ (Q : Subgroup (Theory.Comparator.PSL2Model n)) := hQ (Subgroup.mem_zpowers _)
  obtain ⟨a, ha⟩ := f.surjective ⟨e g, hgQ⟩
  have ha2 : a ^ 2 = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul]
    exact CharTwo.add_self_eq_zero _
  have hsq : (⟨e g, hgQ⟩ : ↥Q) ^ 2 = 1 := by
    rw [← ha, ← map_pow, ha2, map_one]
  have h2 : (e g) ^ 2 = 1 := congrArg Subtype.val hsq
  have := orderOf_dvd_of_pow_eq_one h2
  rw [hg'] at this
  omega

theorem hinFor_psl2_even :
    HinFor fun Y _ => ∃ f : ℕ, Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 2 f := by
  intro Y _ _ _ ⟨f, hY⟩ _ p m _ hp2 _ h16 _ τ _ hL
  exfalso
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨-, hf, -⟩, -⟩ := id hY
  obtain ⟨e⟩ := GH74.KGroups.PSLN.psl_equiv_of_stated (F := GaloisField 2 f) 2 2 f (by omega)
    (GaloisField.card 2 f (by omega)) hY
  obtain ⟨x, hx⟩ := exists_orderOf_four_of_lieModel_psl2 hp2 h16 hL
  exact orderOf_ne_four_psl2Model hf e (x : Y) (by rw [Subgroup.orderOf_coe]; exact hx)

theorem hinFor_psl2 :
    HinFor fun Y _ => ∃ ℓ f : ℕ, Assembly.LowTwoRank.StatedClassicalModel Y .PSL 2 ℓ f := by
  intro Y _ _ _ ⟨ℓ, f, hY⟩
  by_cases hℓ : ℓ = 2
  · subst hℓ
    exact hinFor_psl2_even Y ⟨f, hY⟩
  · exact hinFor_psl2_odd Y ⟨ℓ, f, hℓ, hY⟩

end CFSG.ComponentClassification.HarrisLit.Hin

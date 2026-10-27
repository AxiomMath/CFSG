module

public import CFSG.LieType.Steinberg.TwistedE6.Clause0
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.HighestRoot.GenModels

public noncomputable section

namespace CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Minuscule.MinData.Valid
  CFSG.LieType.CurtisTits

section RankOne

variable {k : Type} [Field k] (θ : k →+* k)

theorem slRankOne_slLower (a : Fin (Tag.rank .E6)) (c : k) :
    (slRankOne k a (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c :=
  Subtype.ext (Units.ext (by
    change e6Data_valid.blockOp k a (slLower k c : Matrix (Fin 2) (Fin 2) k) = _
    rw [slLower_val, e6Data_valid.blockOp_lower]
    rfl))

abbrev fixedSubfield : Subfield k := RingHom.eqLocusField θ (RingHom.id k)

@[expose] def slFixedNodeE (a : Fin (Tag.rank .E6)) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield θ) →* e6Data_valid.minGroup k :=
  (rankOne (e6Data_valid.rootGroup k) a).subtype.comp
    ((slRankOne k a).comp (Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype))

theorem slFixedNodeE_upper (a : Fin (Tag.rank .E6)) (c : fixedSubfield θ) :
    slFixedNodeE θ a (sl2Upper c) = e6Data_valid.xm k (Pi.single a 1) c := by
  have e : Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype (sl2Upper c) =
      slUpper k (c : k) :=
    Subtype.ext (by
      ext x y
      fin_cases x <;> fin_cases y <;> simp [coe_sl2Upper, slUpper_val])
  change (slRankOne k a (Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype
    (sl2Upper c)) : e6Data_valid.minGroup k) = _
  rw [e, slRankOne_upper]

theorem slFixedNodeE_lower (a : Fin (Tag.rank .E6)) (c : fixedSubfield θ) :
    slFixedNodeE θ a (sl2Lower c) = e6Data_valid.xm k (-Pi.single a 1) c := by
  have e : Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype (sl2Lower c) =
      slLower k (c : k) :=
    Subtype.ext (by
      ext x y
      fin_cases x <;> fin_cases y <;> simp [coe_sl2Lower, slLower_val])
  change (slRankOne k a (Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype
    (sl2Lower c)) : e6Data_valid.minGroup k) = _
  rw [e, slRankOne_slLower]

theorem sigma_comp_slFixedNodeE {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    (sigma k θ).comp (slFixedNodeE θ a) = slFixedNodeE θ a := by
  refine MonoidHom.eq_of_eqOn_dense
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field ?_
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  have hc : θ (c : k) = c := c.2
  have key : ∀ M, M = sl2Upper c ∨ M = sl2Lower c →
      (sigma k θ).comp (slFixedNodeE θ a) M = slFixedNodeE θ a M := by
    rintro M (rfl | rfl)
    · rw [MonoidHom.comp_apply, slFixedNodeE_upper, sigma_xm_single, ha, hc]
    · rw [MonoidHom.comp_apply, slFixedNodeE_lower, sigma_xm_neg_single, ha, hc]
  refine key _ ?_
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · refine Or.inl (Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_)
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Upper]
  · refine Or.inr (Matrix.SpecialLinearGroup.ext _ _ fun x y => ?_)
    fin_cases x <;> fin_cases y <;>
      simp [Matrix.SpecialLinearGroup.transvection_coe, coe_sl2Lower]
  · exact absurd rfl hij

theorem slFixedNodeE_mem {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (M : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield θ)) :
    slFixedNodeE θ a M ∈ fixedGroup k θ :=
  DFunLike.congr_fun (sigma_comp_slFixedNodeE θ ha) M

@[expose] def slFixedNodeHom {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield θ) →* fixedGroup k θ :=
  (slFixedNodeE θ a).codRestrict _ (slFixedNodeE_mem θ ha)

theorem slFixedNodeHom_val {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (M : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield θ)) :
    (slFixedNodeHom θ ha M : e6Data_valid.minGroup k) = slFixedNodeE θ a M :=
  rfl

theorem slFixedNodeHom_injective {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    Function.Injective (slFixedNodeHom θ ha) := by
  intro M N h
  have h1 : e6Data_valid.blockOp k a
        (Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype M : Matrix (Fin 2) (Fin 2) k) =
      e6Data_valid.blockOp k a
        (Matrix.SpecialLinearGroup.map (fixedSubfield θ).subtype N : Matrix (Fin 2) (Fin 2) k) :=
    congrArg (fun g : fixedGroup k θ => e6Data_valid.endo k (g : e6Data_valid.minGroup k)) h
  have h2 := e6Data_valid.blockOp_injective k a h1
  exact Subtype.ext (Matrix.ext fun x y => Subtype.ext (congrFun (congrFun h2 x) y))

theorem rankOne_le_range_slFixedNodeHom {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i) :
    rankOne (twistedRootGroup k θ) i ≤ (slFixedNodeHom θ ha).range := by
  subst hi
  have h1 : rho (Pi.single a 1) = Pi.single a 1 := by rw [rho_single, ha]
  have h2 : rho (-Pi.single a 1) = -Pi.single a 1 := by rw [rho_neg_single, ha]
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · rw [← proj_single] at hx
    obtain ⟨c, hc, hxc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ (isRoot_single _ a) rfl h1 x).1 hx
    exact ⟨sl2Upper ⟨c, hc⟩, Subtype.ext ((slFixedNodeE_upper θ a _).trans hxc.symm)⟩
  · rw [← proj_neg_single] at hx
    obtain ⟨c, hc, hxc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed θ (isRoot_neg_single _ a) rfl h2 x).1 hx
    exact ⟨sl2Lower ⟨c, hc⟩, Subtype.ext ((slFixedNodeE_lower θ a _).trans hxc.symm)⟩

theorem slOrbitHom_slLower (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c * e6Data_valid.xm k (-Pi.single b 1) (θ c) := by
  change phiOrbit θ hab (slRankOne k a (slLower k c)) = _
  rw [phiOrbit_apply, slRankOne_slLower, sigma_xm_neg_single, rhoPerm_of_orbit hab]

theorem rankOne_le_range_slOrbitHom (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {i : Fin (Tag.rank .F4)}
    (hi : orbitMap a = i) :
    rankOne (twistedRootGroup k θ) i ≤ (slOrbitHom θ hθ hab).range := by
  subst hi
  have hρ := rhoPerm_of_orbit hab
  have hne1 : rho (Pi.single a 1) ≠ Pi.single a 1 := by
    rw [rho_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hne2 : rho (-Pi.single a 1) ≠ -Pi.single a 1 := by
    rw [rho_neg_single, hρ]
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  refine sup_le (fun x hx => ?_) (fun x hx => ?_)
  · rw [← proj_single] at hx
    obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_single _ a) rfl hne1 x).1 hx
    refine ⟨slUpper k c, Subtype.ext ?_⟩
    rw [slOrbitHom_upper, hc, rho_single, hρ, twistSign_single, Int.cast_one, one_mul]
  · rw [← proj_neg_single] at hx
    obtain ⟨c, hc⟩ :=
      (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne2 x).1 hx
    refine ⟨slLower k c, Subtype.ext ?_⟩
    rw [slOrbitHom_slLower, hc, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

theorem endo_slOrbitHom_single (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) {w : Fin e6Data.d}
    (hw : e6Data.wt w b = 0) (M : Matrix.SpecialLinearGroup (Fin 2) k) :
    e6Data_valid.endo k (slOrbitHom θ hθ hab M : e6Data_valid.minGroup k)
        (Finsupp.single w 1) =
      e6Data_valid.blockOp k a (M : Matrix (Fin 2) (Fin 2) k) (Finsupp.single w 1) := by
  have hσ : e6Data_valid.endo k (sigma k θ (slRankOne k a M : e6Data_valid.minGroup k))
      (Finsupp.single w 1) = Finsupp.single w 1 :=
    endo_single_of_mem_rankOne hw (rhoPerm_of_orbit hab ▸ sigma_mem_rankOne θ (slRankOne k a M).2)
  change e6Data_valid.endo k ((slRankOne k a M : e6Data_valid.minGroup k) *
    sigma k θ (slRankOne k a M : e6Data_valid.minGroup k)) (Finsupp.single w 1) = _
  rw [e6Data_valid.endo_mul, Module.End.mul_apply, hσ]
  rfl

theorem slOrbitHom_injective (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    Function.Injective (slOrbitHom θ hθ hab) := by
  intro M N h
  obtain ⟨w, hwa, hwb⟩ : ∃ w : Fin e6Data.d, e6Data.wt w a = 1 ∧ e6Data.wt w b = 0 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨1, by decide⟩, by decide, by decide⟩
    · exact ⟨⟨0, by decide⟩, by decide, by decide⟩
  obtain ⟨w', hwa', hwb'⟩ : ∃ w' : Fin e6Data.d, e6Data.wt w' a = -1 ∧ e6Data.wt w' b = 0 := by
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨2, by decide⟩, by decide, by decide⟩
    · exact ⟨⟨1, by decide⟩, by decide, by decide⟩
  have key : ∀ w₀ : Fin e6Data.d, e6Data.wt w₀ b = 0 →
      e6Data_valid.blockOp k a (M : Matrix (Fin 2) (Fin 2) k) (Finsupp.single w₀ 1) =
        e6Data_valid.blockOp k a (N : Matrix (Fin 2) (Fin 2) k) (Finsupp.single w₀ 1) :=
    fun w₀ hw₀ => by
      rw [← endo_slOrbitHom_single θ hθ hab hw₀, ← endo_slOrbitHom_single θ hθ hab hw₀, h]
  have e1 := key w hwb
  have e2 := key w' hwb'
  have hne : e6Data_valid.sRefl a w ≠ w := e6Data_valid.sRefl_ne_self (by omega)
  have hne' : e6Data_valid.sRefl a w' ≠ w' := e6Data_valid.sRefl_ne_self (by omega)
  simp only [e6Data_valid.blockOp_single_of_eq_one k hwa] at e1
  simp only [e6Data_valid.blockOp_single_of_eq_neg_one k hwa'] at e2
  have e1a := congrArg (fun v => v w) e1
  have e1b := congrArg (fun v => v (e6Data_valid.sRefl a w)) e1
  have e2a := congrArg (fun v => v w') e2
  have e2b := congrArg (fun v => v (e6Data_valid.sRefl a w')) e2
  simp [hne, hne.symm, hne', hne'.symm] at e1a e1b e2a e2b
  refine Subtype.ext (Matrix.ext fun x y => ?_)
  fin_cases x <;> fin_cases y <;> simp [e1a, e1b, e2a, e2b]

end RankOne

theorem twistedE6_exists_section_of_coprime {k : Type} [Field k] [Finite k] {θ : k →+* k}
    (hθ : ∀ c, θ (θ c) = c) {p : ℕ} [Fact p.Prime] [CharP k p] {E : Type*} [Group E] [Finite E]
    {π : E →* fixedGroup k θ} (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hC : p.Coprime (Nat.card π.ker)) :
    ∃ s : fixedGroup k θ →* E, ∀ g, π (s g) = g := by
  have hC' : ¬ p ∣ Nat.card π.ker := (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hC
  have : Finite (fixedSubfield θ) := Subtype.finite
  have hfix : ∀ {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)}
      (hi : orbitMap a = i), ∃ φ : ↥(rankOne (twistedRootGroup k θ) i) →* E,
        ∀ x, π (φ x) = x := fun ha _ hi => by
    obtain ⟨ρ', hρ', -⟩ :=
      SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' (slFixedNodeHom θ ha)
    exact exists_lift_of_injective (slFixedNodeHom_injective θ ha)
      (rankOne_le_range_slFixedNodeHom θ ha hi) fun g => DFunLike.congr_fun hρ' g
  have horb : ∀ {a b : Fin (Tag.rank .E6)} (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
      {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i),
      ∃ φ : ↥(rankOne (twistedRootGroup k θ) i) →* E, ∀ x, π (φ x) = x := fun hab _ hi => by
    obtain ⟨ρ', hρ', -⟩ :=
      SectionRank.EvenCover.sl2_existsUnique_lift hπ hcen hC' (slOrbitHom θ hθ hab)
    exact exists_lift_of_injective (slOrbitHom_injective θ hθ hab)
      (rankOne_le_range_slOrbitHom θ hθ hab hi) fun g => DFunLike.congr_fun hρ' g
  refine (existsUnique_section_of_rankOne_lift (p := p)
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ)
    (fun β hβ => HighestRoot.isPGroup_twistedE6_rootGroup θ
      (isRoot_of_mem_twistedDatum_roots θ hβ)) hπ hcen hC' fun i => ?_).exists
  match i with
  | ⟨0, _⟩ => exact hfix (a := nd 1) rfl rfl
  | ⟨1, _⟩ => exact hfix (a := nd 3) rfl rfl
  | ⟨2, _⟩ => exact horb (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) rfl
  | ⟨3, _⟩ => exact horb (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) rfl

end CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed

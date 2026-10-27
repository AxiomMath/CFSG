module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalReduce
public import CFSG.LieType.Steinberg.TwistedE6.Clause0

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Minuscule.MinData.Valid CFSG.LieType.CurtisTits CFSG.LieType.Universal
  CFSG.Blueprint.Chevalley CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic

section PGroup

variable {k : Type} [Field k]

theorem xm_pow_e6 (γ : Fin (Tag.rank .E6) → ℤ) (c : k) (n : ℕ) :
    (e6Data_valid.xm k γ c) ^ n = e6Data_valid.xm k γ (n • c) := by
  induction n with
  | zero => simp [e6Data_valid.xm_zero]
  | succ n ih => rw [pow_succ, ih, ← e6Data_valid.xm_add, succ_nsmul]

variable (θ : k →+* k) {p : ℕ} [Fact p.Prime] [CharP k p]

theorem isPGroup_twistedRootGroup_e6 {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    IsPGroup p (twistedRootGroup k θ β) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨x, hx⟩
  have hpc : ∀ c : k, p • c = 0 := fun c => by
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  have hxp : (⟨x, hx⟩ : twistedRootGroup k θ β) ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨α₀, hα₀, hproj⟩ := exists_proj_eq hβ
    show ((x : fixedGroup k θ) : e6Data_valid.minGroup k) ^ p = 1
    by_cases hfix : rho α₀ = α₀
    · obtain ⟨c, -, hc⟩ := (mem_twistedRootGroup_iff_of_fixed θ hα₀ hproj hfix _).1 hx
      rw [hc, xm_pow_e6, hpc, e6Data_valid.xm_zero]
    · obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ hα₀ hproj hfix _).1 hx
      rw [hc, ((commute_xm_rho hα₀ hfix) _ _).mul_pow, xm_pow_e6, xm_pow_e6, hpc, hpc,
        e6Data_valid.xm_zero, e6Data_valid.xm_zero, mul_one]
  have hdvd : orderOf (⟨x, hx⟩ : twistedRootGroup k θ β) ∣ p := orderOf_dvd_of_pow_eq_one hxp
  rcases (Nat.dvd_prime Fact.out).1 hdvd with h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩

end PGroup

section Fixed

variable {k : Type} [Field k] (θ : k →+* k)

abbrev fixedFieldE6 : Subfield k := RingHom.eqLocusField θ (RingHom.id k)

theorem mem_fixedFieldE6 {c : k} : c ∈ fixedFieldE6 θ ↔ θ c = c := Iff.rfl

variable (k) in
@[expose] noncomputable def slE (a : Fin (Tag.rank .E6)) :
    Matrix.SpecialLinearGroup (Fin 2) k →* e6Data_valid.minGroup k :=
  (e6Data_valid.slHom k a).codRestrict _ (e6Data_valid.slHom_mem k a)

theorem slE_upper (a : Fin (Tag.rank .E6)) (c : k) :
    slE k a (slUpper k c) = e6Data_valid.xm k (Pi.single a 1) c :=
  slRankOne_upper a c

theorem slE_lower (a : Fin (Tag.rank .E6)) (c : k) :
    slE k a (slLower k c) = e6Data_valid.xm k (-Pi.single a 1) c :=
  Subtype.ext (Units.ext (by
    change e6Data_valid.blockOp k a (slLower k c : Matrix (Fin 2) (Fin 2) k) = _
    rw [slLower_val, e6Data_valid.blockOp_lower]
    rfl))

theorem slE_injective (a : Fin (Tag.rank .E6)) : Function.Injective (slE k a) := by
  intro M N h
  have h' := congrArg (e6Data_valid.endo k) h
  exact Subtype.ext (e6Data_valid.blockOp_injective k a h')

theorem map_slUpper (c : k) :
    Matrix.SpecialLinearGroup.map θ (slUpper k c) = slUpper k (θ c) := by
  apply Subtype.ext
  ext x y
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases x <;> fin_cases y <;> simp [slUpper, RingHom.mapMatrix_apply]

theorem map_slLower (c : k) :
    Matrix.SpecialLinearGroup.map θ (slLower k c) = slLower k (θ c) := by
  apply Subtype.ext
  ext x y
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases x <;> fin_cases y <;> simp [slLower, RingHom.mapMatrix_apply]

theorem toSL_zero_one (c : k) (h : (0 : Fin 2) ≠ 1) :
    (Matrix.TransvectionStruct.mk (0 : Fin 2) 1 h c).toSpecialLinearGroup = slUpper k c := by
  apply Subtype.ext
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.TransvectionStruct.toSpecialLinearGroup, slUpper,
      Matrix.SpecialLinearGroup.transvection_coe]

theorem toSL_one_zero (c : k) (h : (1 : Fin 2) ≠ 0) :
    (Matrix.TransvectionStruct.mk (1 : Fin 2) 0 h c).toSpecialLinearGroup = slLower k c := by
  apply Subtype.ext
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [Matrix.TransvectionStruct.toSpecialLinearGroup, slLower,
      Matrix.SpecialLinearGroup.transvection_coe]

theorem sigma_comp_slE {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    (sigma k θ).comp (slE k a) = (slE k a).comp (Matrix.SpecialLinearGroup.map θ) := by
  apply MonoidHom.eq_of_eqOn_dense
    Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have e : (Matrix.TransvectionStruct.mk (0 : Fin 2) 1 hij c).toSpecialLinearGroup =
        slUpper k c := toSL_zero_one c hij
    show ((sigma k θ).comp (slE k a))
        (Matrix.TransvectionStruct.mk (0 : Fin 2) 1 hij c).toSpecialLinearGroup =
      ((slE k a).comp (Matrix.SpecialLinearGroup.map θ))
        (Matrix.TransvectionStruct.mk (0 : Fin 2) 1 hij c).toSpecialLinearGroup
    rw [e]
    simp only [MonoidHom.comp_apply, slE_upper, map_slUpper, sigma_xm_single, ha]
  · have e : (Matrix.TransvectionStruct.mk (1 : Fin 2) 0 hij c).toSpecialLinearGroup =
        slLower k c := toSL_one_zero c hij
    show ((sigma k θ).comp (slE k a))
        (Matrix.TransvectionStruct.mk (1 : Fin 2) 0 hij c).toSpecialLinearGroup =
      ((slE k a).comp (Matrix.SpecialLinearGroup.map θ))
        (Matrix.TransvectionStruct.mk (1 : Fin 2) 0 hij c).toSpecialLinearGroup
    rw [e]
    simp only [MonoidHom.comp_apply, slE_lower, map_slLower, sigma_xm_neg_single, ha]
  · exact absurd rfl hij

theorem map_subtype_fixed (M : Matrix.SpecialLinearGroup (Fin 2) (fixedFieldE6 θ)) :
    Matrix.SpecialLinearGroup.map θ (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M) =
      Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M := by
  apply Subtype.ext
  ext x y
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact (M x y).2

@[expose] noncomputable def slFixedHom {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    Matrix.SpecialLinearGroup (Fin 2) (fixedFieldE6 θ) →* fixedGroup k θ :=
  ((slE k a).comp (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype)).codRestrict _
    fun M => by
      rw [mem_fixedGroup]
      have h := DFunLike.congr_fun (sigma_comp_slE θ ha)
        (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M)
      simp only [MonoidHom.comp_apply, map_subtype_fixed] at h ⊢
      exact h

theorem slFixedHom_val {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a)
    (M : Matrix.SpecialLinearGroup (Fin 2) (fixedFieldE6 θ)) :
    (slFixedHom θ ha M : e6Data_valid.minGroup k) =
      slE k a (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M) := rfl

theorem slFixedHom_injective {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    Function.Injective (slFixedHom θ ha) := by
  intro M N h
  have h1 : slE k a (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M) =
      slE k a (Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype N) := congrArg Subtype.val h
  have h2 := slE_injective a h1
  apply Subtype.ext
  ext x y
  have h3 := congrFun (congrFun (congrArg Subtype.val h2) x) y
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    at h3
  exact h3

theorem rankOne_le_range_slFixedHom {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) :
    rankOne (twistedRootGroup k θ) (orbitMap a) ≤ (slFixedHom θ ha).range := by
  intro g hg
  obtain ⟨M, hM, hMg⟩ := exists_sl_of_mem_rankOne_fixed θ ha hg
  have hMfix := (mem_slFixed θ).1 hM
  let M₀ : Matrix (Fin 2) (Fin 2) (fixedFieldE6 θ) :=
    Matrix.of fun x y => ⟨(M : Matrix _ _ k) x y, hMfix x y⟩
  have hM₀ : (fixedFieldE6 θ).subtype.mapMatrix M₀ = (M : Matrix (Fin 2) (Fin 2) k) := by
    ext x y
    rfl
  have hdet : M₀.det = 1 := by
    apply (fixedFieldE6 θ).subtype.injective
    rw [RingHom.map_det, hM₀, M.det_coe, map_one]
  let M' : Matrix.SpecialLinearGroup (Fin 2) (fixedFieldE6 θ) := ⟨M₀, hdet⟩
  refine ⟨M', ?_⟩
  apply Subtype.ext
  apply e6Data_valid.endo_injective k
  rw [hMg]
  show e6Data_valid.blockOp k a ((Matrix.SpecialLinearGroup.map (fixedFieldE6 θ).subtype M' :
    Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) = _
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  exact congrArg (e6Data_valid.blockOp k a) hM₀

end Fixed

section Orbit

variable {k : Type} [Field k] (θ : k →+* k)

theorem slOrbitHom_lower (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) (c : k) :
    (slOrbitHom θ hθ hab (slLower k c) : e6Data_valid.minGroup k) =
      e6Data_valid.xm k (-Pi.single a 1) c * e6Data_valid.xm k (-Pi.single b 1) (θ c) := by
  change phiOrbit θ hab (slRankOne k a (slLower k c)) = _
  rw [phiOrbit_apply, show (slRankOne k a (slLower k c) : e6Data_valid.minGroup k) =
    e6Data_valid.xm k (-Pi.single a 1) c from slE_lower a c, sigma_xm_neg_single,
    rhoPerm_of_orbit hab]

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
    obtain ⟨c, hc⟩ := (mem_twistedRootGroup_iff_of_pair θ (isRoot_neg_single _ a) rfl hne2 x).1 hx
    refine ⟨slLower k c, Subtype.ext ?_⟩
    rw [slOrbitHom_lower, hc, rho_neg_single, hρ, twistSign_neg_single, Int.cast_one, one_mul]

theorem slOrbitHom_injective (hθ : ∀ c, θ (θ c) = c) {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    Function.Injective (slOrbitHom θ hθ hab) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have hρ := rhoPerm_of_orbit hab
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
        Finsupp.single w₀ 1 := by
    intro w₀ hw₀
    have h1 := congrArg (fun g : fixedGroup k θ =>
      e6Data_valid.endo k (g : e6Data_valid.minGroup k) (Finsupp.single w₀ 1)) hM
    have hσ : e6Data_valid.endo k (sigma k θ (slRankOne k a M : e6Data_valid.minGroup k))
        (Finsupp.single w₀ 1) = Finsupp.single w₀ 1 :=
      endo_single_of_mem_rankOne hw₀ (hρ ▸ sigma_mem_rankOne θ (slRankOne k a M).2)
    have h2 : e6Data_valid.endo k ((slOrbitHom θ hθ hab M : fixedGroup k θ) :
        e6Data_valid.minGroup k) (Finsupp.single w₀ 1) =
        e6Data_valid.blockOp k a (M : Matrix (Fin 2) (Fin 2) k) (Finsupp.single w₀ 1) := by
      change e6Data_valid.endo k ((slRankOne k a M : e6Data_valid.minGroup k) *
        sigma k θ (slRankOne k a M : e6Data_valid.minGroup k)) (Finsupp.single w₀ 1) = _
      rw [e6Data_valid.endo_mul, Module.End.mul_apply, hσ]
      rfl
    simp only [OneMemClass.coe_one, e6Data_valid.endo_one, Module.End.one_apply] at h1
    rw [← h2]
    exact h1
  have e1 := key w hwb
  have e2 := key w' hwb'
  have hne : e6Data_valid.sRefl a w ≠ w := e6Data_valid.sRefl_ne_self (by omega)
  have hne' : e6Data_valid.sRefl a w' ≠ w' := e6Data_valid.sRefl_ne_self (by omega)
  rw [e6Data_valid.blockOp_single_of_eq_one k hwa] at e1
  rw [e6Data_valid.blockOp_single_of_eq_neg_one k hwa'] at e2
  have e1a := congrArg (fun v => v w) e1
  have e1b := congrArg (fun v => v (e6Data_valid.sRefl a w)) e1
  have e2a := congrArg (fun v => v w') e2
  have e2b := congrArg (fun v => v (e6Data_valid.sRefl a w')) e2
  simp [hne, hne.symm, hne', hne'.symm] at e1a e1b e2a e2b
  apply Subtype.ext
  ext x y
  fin_cases x <;> fin_cases y <;> simp [e1a, e1b, e2a, e2b]

end Orbit

section Split

variable {k : Type} [Field k] [Finite k]

theorem centralTwoSplit_twistedE6 (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) (hk : ringChar k ≠ 2) :
    CentralTwoSplit (fixedGroup k θ) := by
  intro E _ _ π hπ hker h2
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have hX : ∀ γ ∈ (twistedDatum k θ).roots,
      IsPGroup (ringChar k) ((twistedDatum k θ).rootGroup γ) := fun γ hγ =>
    isPGroup_twistedRootGroup_e6 θ (isRoot_of_mem_twistedDatum_roots θ hγ)
  have hkF : ringChar (fixedFieldE6 θ) ≠ 2 := by
    rw [ringChar.eq (fixedFieldE6 θ) (ringChar k)]
    exact hk
  have hfix : ∀ {a : Fin (Tag.rank .E6)} (ha : rhoPerm a = a) {i : Fin (Tag.rank .F4)}
      (hi : orbitMap a = i), ∃ φ : ↥(rankOne (twistedDatum k θ).rootGroup i) →* E,
        ∀ x, π (φ x) = x := by
    intro a ha i hi
    subst hi
    obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hkF hπ hker h2 (slFixedHom θ ha)
    exact exists_lift_of_injective (slFixedHom_injective θ ha) (rankOne_le_range_slFixedHom θ ha)
      fun g => DFunLike.congr_fun hβ g
  have horb : ∀ {a b : Fin (Tag.rank .E6)} (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5))
      {i : Fin (Tag.rank .F4)} (hi : orbitMap a = i),
      ∃ φ : ↥(rankOne (twistedDatum k θ).rootGroup i) →* E, ∀ x, π (φ x) = x := by
    intro a b hab i hi
    obtain ⟨β, hβ⟩ := CFSG.LieType.CentralExt.exists_lift hk hπ hker h2 (slOrbitHom θ hθ hab)
    exact exists_lift_of_injective (slOrbitHom_injective θ hθ hab)
      (rankOne_le_range_slOrbitHom θ hθ hab hi) fun g => DFunLike.congr_fun hβ g
  have hrank : ∀ i, ∃ φ : ↥(rankOne (twistedDatum k θ).rootGroup i) →* E, ∀ x, π (φ x) = x := by
    intro i
    match i with
    | ⟨0, _⟩ => exact hfix (a := nd 1) rfl rfl
    | ⟨1, _⟩ => exact hfix (a := nd 3) rfl rfl
    | ⟨2, _⟩ => exact horb (a := nd 2) (b := nd 4) (Or.inl ⟨rfl, rfl⟩) rfl
    | ⟨3, _⟩ => exact horb (a := nd 0) (b := nd 5) (Or.inr ⟨rfl, rfl⟩) rfl
  obtain ⟨s, hs, -⟩ := existsUnique_section_of_rankOne_lift
    (twistedDatum_isCTGroupDatum θ hθ (iSup_twistedDatum_rootGroup θ hθ))
    (twistedDatum_steinbergExtras θ hθ) hX hπ hker (not_ringChar_dvd_card_ker hk h2) hrank
  exact ⟨s, hs⟩

end Split

theorem finite_and_centralTwoSplit_modelUniv_twistedE6 {p n e : ℕ} (hp2 : p ≠ 2) (hp : p.Prime)
    (hadm : StatedLieAdmissible .twistedE6 n p e) :
    Finite (modelUniv .twistedE6 n p e hp).K ∧
      CentralTwoSplit (modelUniv .twistedE6 n p e hp).K := by
  have : Fact p.Prime := ⟨hp⟩
  have he : 1 ≤ e := hadm.2.1
  have hk : ringChar (GaloisField p (2 * e)) ≠ 2 := ringChar_galoisField_ne_two hp2
  exact ⟨finite_modelUniv_twistedE6 hp,
    centralTwoSplit_twistedE6 (Exceptional.frobQ p e) (Exceptional.frobQ_frobQ p e he) hk⟩

theorem centralLift (p : ℕ) : CentralLift p :=
  centralLift_of_twisted
    (fun hp2 _ _ hp hadm => finite_and_centralTwoSplit_modelUniv_twistedE6 hp2 hp hadm)
    (fun hp2 _ _ hp hadm => finite_and_centralTwoSplit_modelUniv_twistedD4 hp2 hp hadm)

end CFSG.ClassicalInvolution.ModelFacts

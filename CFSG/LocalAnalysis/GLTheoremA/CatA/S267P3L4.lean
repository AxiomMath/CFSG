module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Orth
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3LinModel
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3.L4

open Matrix CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S267.P3
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Torus

variable {F : Type} [Field F]

@[expose] def torusDiag (v : Fˣ × (Fˣ × Fˣ)) : Fin 4 → F :=
  ![(v.1 : F), (v.2.1 : F) / v.1, (v.2.2 : F) / v.2.1, 1 / (v.2.2 : F)]

theorem prod_torusDiag (v : Fˣ × (Fˣ × Fˣ)) : ∏ i, torusDiag v i = 1 := by
  rw [Fin.prod_univ_four]
  change (v.1 : F) * ((v.2.1 : F) / v.1) * ((v.2.2 : F) / v.2.1) * (1 / (v.2.2 : F)) = 1
  have h1 := v.1.ne_zero
  have h2 := v.2.1.ne_zero
  have h3 := v.2.2.ne_zero
  field_simp

@[expose] noncomputable def torusHom : Fˣ × (Fˣ × Fˣ) →* SpecialLinearGroup (Fin 4) F where
  toFun v := ⟨diagonal (torusDiag v), by rw [det_diagonal]; exact prod_torusDiag v⟩
  map_one' := Subtype.ext (by
    change diagonal (torusDiag 1) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [torusDiag])
  map_mul' v w := Subtype.ext (by
    change diagonal (torusDiag (v * w)) = diagonal (torusDiag v) * diagonal (torusDiag w)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    have h1 := v.1.ne_zero
    have h2 := v.2.1.ne_zero
    have h3 := v.2.2.ne_zero
    have h1' := w.1.ne_zero
    have h2' := w.2.1.ne_zero
    have h3' := w.2.2.ne_zero
    fin_cases i <;> simp [torusDiag] <;> field_simp)

theorem coe_torusHom (v : Fˣ × (Fˣ × Fˣ)) :
    ((torusHom v : SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      diagonal (torusDiag v) := rfl

theorem torusHom_comm (v w : Fˣ × (Fˣ × Fˣ)) :
    torusHom v * torusHom w = torusHom w * (torusHom v : SpecialLinearGroup (Fin 4) F) := by
  rw [← map_mul, ← map_mul, mul_comm]

@[expose] noncomputable def ωU {ω : F} (hω0 : ω ≠ 0) : Fˣ := Units.mk0 ω hω0

@[expose] def torusDom (u : Fˣ) : Subgroup (Fˣ × (Fˣ × Fˣ)) :=
  (Subgroup.zpowers u).prod ((Subgroup.zpowers u).prod (Subgroup.zpowers u))

variable {ω : F} (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) (h2 : (2 : F) ≠ 0)

include hω3 in
theorem ω_ne_zero : ω ≠ 0 := by
  rintro rfl
  norm_num at hω3

include hω3 in
theorem ωU_pow_three : ωU (ω_ne_zero hω3) ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, ωU, Units.val_mk0, hω3, Units.val_one])

include hω hω3 in
theorem orderOf_ωU : orderOf (ωU (ω_ne_zero hω3)) = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime (ωU_pow_three hω3) fun h => hω (by
    have := congrArg Units.val h
    rwa [ωU, Units.val_mk0, Units.val_one] at this)

include hω3 in
theorem isElemAbelian_torusDom : IsElemAbelian 3 (torusDom (ωU (ω_ne_zero hω3))) :=
  Lin.isElemAbelian_prod (Lin.isElemAbelian_zpowers (ωU_pow_three hω3))
    (Lin.isElemAbelian_prod (Lin.isElemAbelian_zpowers (ωU_pow_three hω3))
      (Lin.isElemAbelian_zpowers (ωU_pow_three hω3)))

include hω hω3 in
theorem card_torusDom : Nat.card (torusDom (ωU (ω_ne_zero hω3))) = 3 ^ 3 := by
  rw [torusDom, Lin.card_prod_subgroup, Lin.card_prod_subgroup, Nat.card_zpowers,
    orderOf_ωU hω hω3]
  norm_num

include hω3 in
theorem ker_torus : ∀ v ∈ torusDom (ωU (ω_ne_zero hω3)),
    ((proj 4 F).comp torusHom) v = 1 → v = 1 := by
  intro v hv h1
  have hs : torusHom v ∈ scalars 4 F := by
    rw [← ker_proj]
    exact h1
  obtain ⟨c, hc4, hcv⟩ := mem_scalars.1 hs
  rw [coe_torusHom] at hcv
  have hv3 : v ^ 3 = 1 := (isElemAbelian_torusDom hω3).2 v hv
  have e : ∀ i, torusDiag v i = (c : F) := fun i => by
    have := congrFun (congrFun hcv i) i
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using this
  have h3 : (v.1 : F) ^ 3 = 1 := by
    have := congrArg (fun w : Fˣ × (Fˣ × Fˣ) => (w.1 : F)) hv3
    simpa using this
  have hc : (v.1 : F) = c := by simpa [torusDiag] using e 0
  have hc4' : (c : F) ^ 4 = 1 := by
    have := congrArg Units.val hc4
    simpa using this
  have hx1 : (v.1 : F) = 1 := by
    have h4 : (v.1 : F) ^ 4 = 1 := by rw [hc]; exact hc4'
    have : (v.1 : F) ^ 4 = (v.1 : F) ^ 3 * v.1 := pow_succ _ 3
    rw [h4, h3, one_mul] at this
    exact this.symm
  have hy1 : (v.2.1 : F) = 1 := by
    have := e 1
    change (v.2.1 : F) / v.1 = c at this
    rw [← hc, hx1, div_one] at this
    exact this
  have hz1 : (v.2.2 : F) = 1 := by
    have := e 2
    change (v.2.2 : F) / v.2.1 = c at this
    rw [← hc, hy1, hx1, div_one] at this
    exact this
  exact Prod.ext (Units.ext hx1) (Prod.ext (Units.ext hy1) (Units.ext hz1))

@[expose] noncomputable def tTorus : SpecialLinearGroup (Fin 4) F := torusHom (-1, (1, 1))

theorem tTorus_sq : tTorus (F := F) ^ 2 = 1 := by
  rw [tTorus, ← map_pow]
  have : ((-1 : Fˣ), ((1 : Fˣ), (1 : Fˣ))) ^ 2 = 1 := by ext <;> simp
  rw [this, map_one]

include h2 in
theorem proj_tTorus_ne_one : proj 4 F (tTorus (F := F)) ≠ 1 := by
  intro h
  have hs : tTorus (F := F) ∈ scalars 4 F := by
    rw [← ker_proj]
    exact h
  obtain ⟨c, -, hcv⟩ := mem_scalars.1 hs
  rw [tTorus, coe_torusHom] at hcv
  have e0 := congrFun (congrFun hcv 0) 0
  have e2 := congrFun (congrFun hcv 2) 2
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, torusDiag] at e0 e2
  apply h2
  linear_combination e2 - e0

include hω hω3 h2 in
theorem three_le_twoLocalRank [Finite F] : 3 ≤ GLATwoLocalRank 3 (projectiveSL 4 F) := by
  set E : Subgroup (projectiveSL 4 F) :=
    (torusDom (ωU (ω_ne_zero hω3))).map ((proj 4 F).comp torusHom) with hE
  set T : Subgroup (projectiveSL 4 F) := Subgroup.zpowers (proj 4 F tTorus) with hT
  have hEc : Nat.card E = 3 ^ 3 := by
    rw [hE, card_map_eq_of_ker _ _ (ker_torus hω3), card_torusDom hω hω3]
  have hEl : IsElemAbelian 3 E :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_torusDom hω3) _
  have ht2 : proj 4 F (tTorus (F := F)) ^ 2 = 1 := by rw [← map_pow, tTorus_sq, map_one]
  have hT1 : T ≠ ⊥ := fun h => proj_tTorus_ne_one h2 (by
    have := Subgroup.mem_zpowers (proj 4 F (tTorus (F := F)))
    rw [← hT, h, Subgroup.mem_bot] at this
    exact this)
  have hT2 : IsPGroup 2 T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine IsPGroup.of_card (n := 1) ?_
    rw [hT, Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime ht2 (proj_tTorus_ne_one h2)
  have hEN : E ≤ Subgroup.normalizer (T : Set (projectiveSL 4 F)) := by
    rintro _ ⟨v, -, rfl⟩
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 ?_)
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    refine (Commute.zpow_left ?_ k).eq
    change Commute (proj 4 F tTorus) (proj 4 F (torusHom v))
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, tTorus, torusHom_comm]
  exact CFSG.HardMathSupport.Timmesfeld.ComponentBalance.le_glaTwoLocalRank_of_le_normalizer
    (by norm_num : 1 < 3) hT1 hT2 hEl hEN hEc

end Torus

section Fixed

variable {K : Type} [Field K]

@[expose] def fixedSub (σ : K ≃+* K) : Subfield K := (σ : K →+* K).eqLocusField (RingHom.id K)

theorem mem_fixedSub {σ : K ≃+* K} {x : K} : x ∈ fixedSub σ ↔ σ x = x := Iff.rfl

theorem map_scalars_le (n : ℕ) (L : Subfield K) :
    scalars n ↥L ≤ (scalars n K).comap (SpecialLinearGroup.map L.subtype) := by
  intro A hA
  obtain ⟨c, hc, hcA⟩ := mem_scalars.1 hA
  refine mem_scalars.2 ⟨Units.map L.subtype.toMonoidHom c, ?_, ?_⟩
  · rw [← map_pow, hc, map_one]
  · change (A : Matrix (Fin n) (Fin n) ↥L).map L.subtype = _
    rw [hcA]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]

@[expose] noncomputable def incl (n : ℕ) (L : Subfield K) : projectiveSL n ↥L →* projectiveSL n K :=
  QuotientGroup.map (scalars n ↥L) (scalars n K) (SpecialLinearGroup.map L.subtype)
    (map_scalars_le n L)

theorem incl_proj (n : ℕ) (L : Subfield K) (g : SpecialLinearGroup (Fin n) ↥L) :
    incl n L (proj n ↥L g) = proj n K (SpecialLinearGroup.map L.subtype g) := rfl

theorem incl_injective (n : ℕ) [NeZero n] (L : Subfield K) : Function.Injective (incl n L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨A, rfl⟩ := proj_surjective n ↥L x
  rw [incl_proj] at hx
  have hs : SpecialLinearGroup.map L.subtype A ∈ scalars n K := by
    rw [← ker_proj]
    exact hx
  obtain ⟨c, hc, hcA⟩ := mem_scalars.1 hs
  have hentry : ∀ i j, ((A : Matrix (Fin n) (Fin n) ↥L) i j : K) =
      Matrix.scalar (Fin n) (c : K) i j := fun i j => congrFun (congrFun hcA i) j
  set a : ↥L := (A : Matrix (Fin n) (Fin n) ↥L) 0 0 with ha
  have hac : (a : K) = c := by simpa [Matrix.scalar_apply] using hentry 0 0
  have ha0 : a ≠ 0 := fun h => c.ne_zero (by rw [← hac, h]; rfl)
  have hA : (A : Matrix (Fin n) (Fin n) ↥L) = Matrix.scalar (Fin n) a := by
    ext i j
    rw [hentry]
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, hac]
  have hpow : (Units.mk0 a ha0) ^ n = 1 := Units.ext (by
    apply Subtype.ext
    have := congrArg Units.val hc
    simpa [hac] using this)
  rw [← ker_proj] at *
  exact (proj_eq_one_iff (n := n) (K := ↥L)).2 (mem_scalars.2 ⟨Units.mk0 a ha0, hpow, hA⟩)

theorem fieldAut_incl (n : ℕ) (σ : K ≃+* K) (m : projectiveSL n ↥(fixedSub σ)) :
    fieldAut n K σ (incl n (fixedSub σ) m) = incl n (fixedSub σ) m := by
  obtain ⟨A, rfl⟩ := proj_surjective n ↥(fixedSub σ) m
  rw [incl_proj, fieldAut_proj]
  congr 1
  ext i j
  simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact mem_fixedSub.1 ((A : Matrix (Fin n) (Fin n) ↥(fixedSub σ)) i j).2

end Fixed

theorem fix_cube_root {K : Type} [Field K] {σ : K ≃+* K} (hσ : orderOf σ = 3) {ω : K}
    (hω : ω ≠ 1) (hω3 : ω ^ 3 = 1) : σ ω = ω := by
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hω0 : ω ≠ 0 := ω_ne_zero hω3
  have h1ω : ω * ω + ω + 1 = 0 := by
    have : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hω)
  set y := σ ω with hy
  have hy3 : y ^ 3 = 1 := by rw [hy, ← map_pow, hω3, map_one]
  have hfac : (y - 1) * (y - ω) * (y - ω * ω) = 0 := by
    linear_combination hy3 - (y * y) * h1ω + (y : K) * (ω * h1ω) - hω3 + y * h1ω - y * h1ω
  have hy1 : y ≠ 1 := fun h => hω (σ.injective (by rw [← hy, h, map_one]))
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact absurd (sub_eq_zero.1 h') hy1
    · exact sub_eq_zero.1 h'
  · have hy2 : y = ω * ω := sub_eq_zero.1 h
    exfalso
    have h3 : (σ ^ 3) ω = ω := by rw [hσ3]; rfl
    have hω4 : ω * ω * (ω * ω) = ω := by linear_combination ω * hω3
    have : (σ ^ 3) ω = ω * ω := by
      rw [pow_succ, pow_succ, pow_one, RingAut.mul_apply, RingAut.mul_apply, ← hy, hy2, map_mul,
        ← hy, hy2, hω4, ← hy, hy2]
    rw [h3] at this
    have : ω * (ω - 1) = 0 := by linear_combination -this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact hω0 h0
    · exact hω (sub_eq_zero.1 h0)

theorem congr_conj {G G' : Type*} [Group G] [Group G'] (ε : G ≃* G') (g : G) :
    MulAut.congr ε (MulAut.conj g) = MulAut.conj (ε g) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem concC_of_A3
    {q : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}
    (H : P3Hyp q S B) {Q : TauCeti.PrimePower} (hQq : Q.p = q)
    (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.A 3 Q, hv⟩).Group) (h3 : 3 ∣ Q.card - 1) :
    S267ConcBCDE 3 q S B := by
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  set K := GaloisField Q.p Q.exponent with hKdef
  have hKcard : Nat.card K = Q.card := by
    rw [hKdef, GaloisField.card Q.p Q.exponent Q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hp2 : Q.p ≠ 2 := hQq ▸ H.two
  have hp3 : Q.p ≠ 3 := hQq ▸ H.three
  have hQ5 : 5 ≤ Q.p ^ Q.exponent :=
    (Q.prime_p.five_le_of_ne_two_of_ne_three hp2 hp3).trans
      (Nat.le_self_pow Q.exponent_pos.ne' _)
  have e₁ : PSimple 3 S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) K :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 Q hv)
  have hZ : Subgroup.center ↥S = ⊥ := by
    refine H.center_eq_bot_of_multiplier e₁ ?_
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.griess_psl_of_ne Q.p
      Q.exponent 4 Q.exponent_pos (by norm_num) (by norm_num) (by norm_num) (by omega)
    rw [Nat.card_congr eM.toEquiv]
    have hex : CFSG.Open.griessPSLExceptional 4 (Q.p ^ Q.exponent) = (1, 1) := by
      have : Q.p ^ Q.exponent ≠ 2 := by omega
      simp [CFSG.Open.griessPSLExceptional, this]
    rw [hex, Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod]
    simp only [Nat.card_zmod, mul_one]
    intro hd
    exact absurd ((hd.trans (Nat.gcd_dvd_left _ _) : 3 ∣ 4)) (by norm_num)
  let ε : ↥S ≃* projectiveSL 4 K := ((psimpleEquiv H hZ).symm.trans e₁).trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 4 K).symm)
  have h3K : 3 ∣ Nat.card Kˣ := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hKcard]
    exact h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3K
  have hω3 : (u : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one,
    Units.val_one]
  have hω : (u : K) ≠ 1 := fun h => by
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    norm_num at hu
  have h2K : (2 : K) ≠ 0 := by
    have h : ((2 : ℕ) : K) ≠ 0 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq Q.prime_p
      Nat.prime_two).1 ((CharP.cast_eq_zero_iff K Q.p 2).1 h))
    exact_mod_cast h
  have hW : 3 ≤ GLATwoLocalRank 3 ↥S := by
    have h := three_le_twoLocalRank hω hω3 h2K
    have hr := CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv ε Nat.prime_three
    change 3 ≤ CFSG.Assembly.RankThreeEven.localRank 3 ↥S
    rw [hr]
    exact h
  have hF : ∀ β : MulAut ↥S, CFSG.RankThree.PartOne.CTP.IsOuterOfOrder 3 β →
      ∃ (M : Type) (_ : Group M) (_ : Finite M), 3 ≤ GLATwoLocalRank 3 M ∧
        Subgroup.center M = ⊥ ∧ ∃ ψ : M →* ↥S, Function.Injective ψ ∧ ∀ m, β (ψ m) = ψ m := by
    rintro β ⟨hβo, hβout⟩
    set α := MulAut.congr ε β with hα
    have hα3 : α ^ 3 = 1 := by
      rw [hα, ← map_pow, ← hβo, pow_orderOf_eq_one, map_one]
    have hαD : α ∉ linearAutGroup 4 K := by
      intro hD
      obtain ⟨x, hx⟩ := mem_range_conj_of_mem_linearAutGroup_of_coprime hD
        (by norm_num : Nat.Coprime 3 4) hα3
      apply hβout (ε.symm x)
      apply (MulAut.congr ε).injective
      rw [congr_conj, MulEquiv.apply_symm_apply, hx]
    obtain ⟨σ, hσ, Hm, hαeq⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
      (by norm_num) α hα3 hαD
    have hσω : σ (u : K) = u := fix_cube_root hσ hω hω3
    set L := fixedSub σ with hL
    have hωL : ((⟨u, hσω⟩ : ↥L) : K) ^ 3 = 1 := hω3
    have hωL' : (⟨(u : K), hσω⟩ : ↥L) ^ 3 = 1 := Subtype.ext (by simpa using hω3)
    have hωL1 : (⟨(u : K), hσω⟩ : ↥L) ≠ 1 := fun h => hω (congrArg Subtype.val h)
    have h2L : (2 : ↥L) ≠ 0 := fun h => h2K (by rw [← map_ofNat L.subtype 2, h, map_zero])
    refine ⟨projectiveSL 4 ↥L, inferInstance, inferInstance,
      three_le_twoLocalRank hωL1 hωL' h2L,
      CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num),
      (ε.symm.toMonoidHom.comp (conjAut 4 K Hm).toMonoidHom).comp (incl 4 L), ?_, ?_⟩
    · exact ε.symm.injective.comp ((conjAut 4 K Hm).injective.comp (incl_injective 4 L))
    · intro m
      have key : ∀ z, β (ε.symm z) = ε.symm (α z) := fun z => by
        rw [hα, MulAut.congr_apply]
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [key, hαeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, fieldAut_incl]
  obtain ⟨hsup, hinf⟩ := H.eq_sup hZ hW hF
  exact Or.inr (Or.inl ⟨H.card, hsup, hinf, H.center_pQuot_eq_bot hZ, Q, hQq,
    Or.inl ⟨⟨.lie ⟨_, hv⟩, rfl, ⟨e⟩⟩, h3⟩⟩)

theorem p3At_A_three_of_dvd_sub_one
    {Q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 3 Q).Valid) (h3 : 3 ∣ Q.card - 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exact Or.inr (concC_of_A3 H (by simpa using hchar) hv e h3)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3.L4

end

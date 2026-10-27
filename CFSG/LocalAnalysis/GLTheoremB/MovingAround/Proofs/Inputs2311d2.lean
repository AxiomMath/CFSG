module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs2311d
public import CFSG.LieType.SeitzGeneration.UnitaryNonsplit
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.OrthManyBig
public import CFSG.LieType.SeitzGeneration.OrthManyThree
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagParabolicTw
public import CFSG.LieType.SeitzGeneration.OuterOrthCat
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeData
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerivedProof
import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.TwE6Fixed
import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderSmallReeDescent
public import CFSG.LieType.SeitzGeneration.OuterSUData
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega
public import CFSG.RankThree.PartTwo.Census.CommonUnipotent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c

section SuTwo

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
  CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem closure_pow_ringChar_su_two (hK : Nat.card K = (p ^ f) ^ 2) :
    Subgroup.closure {g : Su K p f 2 | g ^ ringChar K = 1} = ⊤ := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  let Θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f) ≃* Su K p f 2 :=
    (hypEquiv hζ0 hζ).trans (CFSG.LieType.Universal.Unitary.conjEquiv P hP)
  have hchar : ringChar (fixedSubfield K p f) = ringChar K := by
    rw [ringChar.eq (fixedSubfield K p f) p, ringChar.eq K p]
  rw [eq_top_iff]
  intro y _
  have hy : Θ.symm y ∈ Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
      TransvectionStruct (Fin 2) (fixedSubfield K p f) →
        Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f))) := by
    rw [Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field]
    exact Subgroup.mem_top _
  have hmap := Subgroup.mem_map_of_mem Θ.toMonoidHom hy
  rw [MonoidHom.map_closure] at hmap
  have hΘ : Θ.toMonoidHom (Θ.symm y) = y := by simp
  rw [hΘ] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
  show (Θ.toMonoidHom t.toSpecialLinearGroup) ^ ringChar K = 1
  rw [← map_pow, TransvectionStruct.toSpecialLinearGroup_def, ← hchar,
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c.transvection_pow_ringChar, map_one]

end SuTwo

section Toral

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.CTP

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem uniClosure_unitarySU_of_dvd_add_one
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (hq : ℓ ^ f ≠ 2) (E : Subgroup (unitarySU ℓ f K (n + 1)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  have hle : unitarySU ℓ f K (n + 1) ≤ primeFormUnitary h (idGram K (n + 1)) :=
    unitarySU_le_primeFormUnitary h
  let G : Subgroup (primeFormUnitary h (idGram K (n + 1))) := E.map (Subgroup.inclusion hle)
  have hGcomm : ∀ u ∈ G, ∀ v ∈ G, u * v = v * u := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hGexp : ∀ u ∈ G, u ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]
  obtain ⟨P, hP⟩ := exists_unitary_conj_diag h hp hpq G hGcomm hGexp
  let Pg : GL (Fin (n + 1)) K := (P : GL (Fin (n + 1)) K)
  let Dg : E → GL (Fin (n + 1)) K := fun x =>
    Pg⁻¹ * (((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg
  have hdiag : ∀ x : E,
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K).IsDiag :=
    fun x => hP (Subgroup.inclusion hle x) ⟨x, x.2, rfl⟩
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin (n + 1) → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiag x) c }
  have hnz : ∀ (x : E) (c : Fin (n + 1)),
      ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c ≠ 0 := by
    intro x c
    have h1 : (((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
        (((Dg x)⁻¹ : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiag x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hcommblock : ∀ i : Fin n, ∃ x : E, x ≠ 1 ∧ ∀ A : Matrix (Fin 2) (Fin 2) K,
      blockMat (n + 1) i A * ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) *
          blockMat (n + 1) i A := by
    intro i
    obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i.castSucc) (χ i.succ)
    refine ⟨x, hx1, fun A => ?_⟩
    have hD : ((Dg x : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) =
        Matrix.diagonal (fun c => ((Dg x : GL (Fin (n + 1)) K) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) c c) := ((hdiag x).diagonal_diag).symm
    rw [hD]
    exact blockMat_mul_diagonal_comm (by omega) _ (hnz x) i.castSucc i.succ (by simp) (by simp)
      hxeq A
  let φ := conjSU h P
  set S := Subgroup.closure {g : unitarySU ℓ f K (n + 1) |
    ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} with hS
  have hblock : ∀ (i : Fin n) (y : unitarySU ℓ f K (n + 1))
      (A : Matrix (Fin 2) (Fin 2) K),
      (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) = blockMat (n + 1) i A → y ^ ringChar K = 1 →
        φ y ∈ S := by
    intro i y A hA hyr
    obtain ⟨x, hx1, hxc⟩ := hcommblock i
    refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K (n + 1)), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_, by rw [← map_pow, hyr, map_one]⟩
    apply Subtype.ext
    have hYD : ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x =
        Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) := by
      apply Units.ext
      simp only [Units.val_mul]
      rw [hA]
      exact hxc A
    have hxeq : ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) = Pg * Dg x * Pg⁻¹ := by
      simp [Dg, mul_assoc]
    show Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
        ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) =
      ((x : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) *
        (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹)
    rw [hxeq]
    calc Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹ *
          (Pg * Dg x * Pg⁻¹)
        = Pg * (((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Dg x) * Pg⁻¹ := by group
      _ = Pg * (Dg x * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K)) * Pg⁻¹ := by
        rw [hYD]
      _ = Pg * Dg x * Pg⁻¹ *
          (Pg * ((y : unitarySU ℓ f K (n + 1)) : GL (Fin (n + 1)) K) * Pg⁻¹) := by group
  let ε : Su K ℓ f (n + 1) ≃* unitarySU ℓ f K (n + 1) :=
    MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1))
  let ι : Fin n → (Su K ℓ f 2 →* unitarySU ℓ f K (n + 1)) := fun i =>
    ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)
  have hgen : ⨆ i : Fin n, (ι i).range = ⊤ := by
    have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
    have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
    rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
    simpa [ι, MonoidHom.range_comp] using h2
  have hsu2 := closure_pow_ringChar_su_two (K := K) (p := ℓ) (f := f) h.card_eq_sq
  have hle' : (⨆ i : Fin n, (ι i).range).map φ.toMonoidHom ≤ S := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    rw [MonoidHom.range_eq_map, ← hsu2, MonoidHom.map_closure, MonoidHom.map_closure,
      Subgroup.closure_le]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    refine hblock i _ ((a : Su K ℓ f 2) : GL (Fin 2) K) rfl ?_
    rw [← map_pow, ha, map_one]
  rw [hgen, Subgroup.map_top_of_surjective _ φ.surjective] at hle'
  exact top_unique hle'

end Toral

section UnitaryCat

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.CTP

theorem uniClosure_statedProj_unitary_of_lift {ℓ f p : ℕ} {K : Type} [Field K] {m : ℕ}
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hm : 1 ≤ m)
    (hker : ¬ p ∣ Nat.gcd m (ℓ ^ f + 1))
    (E : Subgroup (StatedProj (StatedSU m (ℓ ^ f) K))) [CFSG.IsElementaryAbelian p E]
    (hcard : Nat.card E = p ^ 2)
    (hG : ∀ E' : Subgroup (unitarySU ℓ f K m), (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) →
      (∀ x ∈ E', x ^ p = 1) → Nat.card E' = p ^ 2 →
      Subgroup.closure {g : unitarySU ℓ f K m |
        ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤) :
    Subgroup.closure {k : StatedProj (StatedSU m (ℓ ^ f) K) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar K = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact p.Prime := ⟨hp⟩
  let π : unitarySU ℓ f K m →* StatedProj (StatedSU m (ℓ ^ f) K) :=
    QuotientGroup.mk' ((StatedScalars (Fin m) K).subgroupOf (unitarySU ℓ f K m))
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hkerπ : π.ker = unitaryScalars h m := by
    rw [QuotientGroup.ker_mk', unitaryScalars_eq h hm]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hkerπ, card_unitaryScalars h hm]
    exact hker
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact uniClosure_of_lift π hπ hker' E hcomm hexp fun E' hc he hcd => hG E' hc he (hcd.trans hcard)

theorem uniPlaneGen_inner_unitary {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime)
    (hlift : ¬ (p ∣ q.card + 1 ∧ p ∣ m + 1))
    (hSU : ∀ E : Subgroup (unitarySU (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
        (TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)
        (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
          (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)) (m + 1)),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
        Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar
          (GaloisField (TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩)
            (2 * TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩)) = 1} = ⊤)
    {E : Subgroup (MulAut (Cat ⟨.twistedA m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.twistedA m q, hv⟩ p E) : UniPlaneGen q.p E := by
  have : Fact p.Prime := ⟨hp⟩
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hfin := hU.finite
  let e := CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj m q hv
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSU (m + 1) (ℓ ^ f)
      (GaloisField ℓ (2 * f)))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU (GaloisField ℓ (2 * f)) ℓ f
      (by rw [hU.card, pow_mul']) (m + 1) (by omega) (by
        intro h32
        obtain ⟨h31, h2⟩ := Prod.mk.inj h32
        have h3 := hrange.2 (by omega)
        rw [hqcard] at h2
        omega)
  have : IsSimpleGroup (Cat ⟨.twistedA m q, hv⟩) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedA m q, hv⟩)
    (range_conj_ne_bot_of_inner hp hc hinner)
  have hchar : ringChar (GaloisField ℓ (2 * f)) = q.p := by
    rw [ringChar.eq (GaloisField ℓ (2 * f)) ℓ]
    simp [hℓ, TauCeti.ValidLieTypeIndex.characteristic]
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  exact uniClosure_statedProj_unitary_of_lift hU hp (by omega) (fun hd => hlift ⟨by
      rw [← hqcard]; exact (hd.trans (Nat.gcd_dvd_right _ _)), hd.trans (Nat.gcd_dvd_left _ _)⟩)
    E₁ hcard₁ hSU

end UnitaryCat

section Split

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.CTP

section Heis

variable {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ}

theorem heisenbergMatrix_pow {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k)
    (a b : F) (m : ℕ) :
    heisenbergMatrix σ i k a b ^ m =
      heisenbergMatrix σ i k ((m : F) * a) ((m : F) * b - (m.choose 2 : F) * (a * σ a)) := by
  induction m with
  | zero => simp [heisenbergMatrix_zero]
  | succ m ih =>
    rw [pow_succ, ih, heisenbergMatrix_mul σ hi hik hk, Nat.choose_succ_succ', Nat.choose_one_right]
    congr 1
    · push_cast
      ring
    · push_cast
      ring

end Heis

variable {ℓ f n p : ℕ} {K : Type} [Field K]

theorem rootHom_pow_ringChar [CharP K ℓ] {σ : K ≃+* K} (hσ : ∀ c, σ (σ c) = c) {i j : Fin n}
    (hij : i ≠ j) (hi : i ≠ Fin.rev i) (hj : j ≠ Fin.rev j) (c : Multiplicative K) :
    rootHom σ hσ hij hi hj c ^ ringChar K = 1 := by
  rw [← map_pow]
  have : c ^ ringChar K = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, ringChar.Nat.cast_ringChar, zero_mul]
  rw [this, map_one]

theorem longRootHom_pow_ringChar [CharP K ℓ] {σ : K ≃+* K} {i : Fin n} (hi : i ≠ Fin.rev i)
    (c : Multiplicative (traceZero σ)) : longRootHom σ hi c ^ ringChar K = 1 := by
  rw [← map_pow]
  have : c ^ ringChar K = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    apply Subtype.ext
    rw [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero, nsmul_eq_mul, ringChar.Nat.cast_ringChar,
      zero_mul]
  rw [this, map_one]

theorem heisenberg_pow_ringChar [Fact ℓ.Prime] [CharP K ℓ] (hℓ2 : ℓ ≠ 2) {σ : K ≃+* K}
    {i k : Fin n} (hi : i ≠ Fin.rev i) (hik : i ≠ k) (hk : Fin.rev k = k) {g : SU σ n} {a b : K}
    (hg : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = heisenbergMatrix σ i k a b) :
    g ^ ringChar K = 1 := by
  have hr : ringChar K = ℓ := ringChar.eq K ℓ
  have hℓ3 : 3 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    omega
  have hchoose : ((ℓ.choose 2 : ℕ) : K) = 0 := by
    rw [CharP.cast_eq_zero_iff K ℓ]
    exact (Fact.out : ℓ.Prime).dvd_choose_self (by norm_num) (by omega)
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hg, heisenbergMatrix_pow σ hi hik hk, hr,
    CharP.cast_eq_zero K ℓ, hchoose, zero_mul, zero_mul, zero_mul, sub_zero, heisenbergMatrix_zero]
  rfl

theorem uniClosure_unitarySU_of_frame [Finite K] [Fact ℓ.Prime] [CharP K ℓ] (hℓ2 : ℓ ≠ 2)
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1)
    (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n)) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (P : GL (Fin n) K)
    (hP : conjTr (unitaryInvolution K ℓ f) (P : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = antidiag n)
    (hdiag : ∀ x ∈ E, (((P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) * P : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K).IsDiag) :
    Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤ := by
  classical
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  let ε : Su K ℓ f n ≃* unitarySU ℓ f K n :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU h.card_eq_sq n)
  let Φ : SU σ n ≃* unitarySU ℓ f K n := (CFSG.LieType.Universal.Unitary.conjEquiv P hP).trans ε
  let Dg : E → GL (Fin n) K := fun x =>
    P⁻¹ * (((x : unitarySU ℓ f K n)) : GL (Fin n) K) * P
  have hDg : ∀ x : E, ((Φ.symm (x : unitarySU ℓ f K n) : SU σ n) : GL (Fin n) K) = Dg x :=
    fun x => rfl
  have hdiagE : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag :=
    fun x => hdiag x x.2
  have hDmul : ∀ x y : E, Dg (x * y) = Dg x * Dg y := by
    intro x y
    simp only [Dg, Subgroup.coe_mul]
    group
  have hD1 : Dg 1 = 1 := by simp [Dg]
  let χ : Fin n → E →* K := fun c =>
    { toFun := fun x => ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) c c
      map_one' := by simp [hD1]
      map_mul' := fun x y => by
        simp only [hDmul, Units.val_mul]
        exact mul_apply_diag_of_isDiag (hdiagE x) c }
  have hD : ∀ x : E, ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun c => χ c x) := fun x => ((hdiagE x).diagonal_diag).symm
  have hnz : ∀ (c : Fin n) (x : E), χ c x ≠ 0 := by
    intro c x
    have h1 : (((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((Dg x)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) c c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [mul_apply_diag_of_isDiag (hdiagE x)] at h1
    exact left_ne_zero_of_mul_eq_one h1
  have hexpE : ∀ x : E, x ^ p = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  have hχp : ∀ (c : Fin n) (x : E), (χ c x) ^ p = 1 := fun c x => by
    rw [← map_pow, hexpE, map_one]
  have hσχ : ∀ (c : Fin n) (x : E), σ (χ c x) = χ c x := by
    intro c x
    rw [hσdef, unitaryInvolution_apply]
    obtain ⟨k, hk⟩ := hpq
    have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ h.prime.pos
    have hq : ℓ ^ f = 1 + p * k := by omega
    rw [hq, pow_add, pow_one, pow_mul, hχp, one_pow, mul_one]
  have hrel : ∀ (c : Fin n) (x : E), χ c x * χ (Fin.rev c) x = 1 := by
    intro c x
    have hmem := (Φ.symm (x : unitarySU ℓ f K n)).2.2
    rw [hDg, hD x] at hmem
    have h1 := congrFun (congrFun hmem c) (Fin.rev c)
    have hconj : conjTr σ (Matrix.diagonal (fun c => χ c x)) =
        Matrix.diagonal (fun c => σ (χ c x)) := by
      rw [conjTr, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    rw [hconj, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    simp only [antidiag, Matrix.of_apply, ite_true, mul_one] at h1
    rw [hσχ] at h1
    exact h1
  set S := Subgroup.closure {g : unitarySU ℓ f K n |
    ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} with hS
  have hmemS : ∀ (a : SU σ n) (x : E), x ≠ 1 →
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((Dg x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → a ^ ringChar K = 1 → Φ a ∈ S := by
    intro a x hx1 hcomm har
    refine Subgroup.subset_closure ⟨(x : unitarySU ℓ f K n), x.2,
      fun h1 => hx1 (Subtype.ext h1), ?_, by rw [← map_pow, har, map_one]⟩
    apply Subtype.ext
    have hYD : (a : GL (Fin n) K) * Dg x = Dg x * (a : GL (Fin n) K) := by
      apply Units.ext
      simpa only [Units.val_mul] using hcomm
    have hxeq : ((x : unitarySU ℓ f K n) : GL (Fin n) K) = P * Dg x * P⁻¹ := by
      simp [Dg, mul_assoc]
    show P * (a : GL (Fin n) K) * P⁻¹ * ((x : unitarySU ℓ f K n) : GL (Fin n) K) =
      ((x : unitarySU ℓ f K n) : GL (Fin n) K) * (P * (a : GL (Fin n) K) * P⁻¹)
    rw [hxeq]
    calc P * (a : GL (Fin n) K) * P⁻¹ * (P * Dg x * P⁻¹)
        = P * ((a : GL (Fin n) K) * Dg x) * P⁻¹ := by group
      _ = P * (Dg x * (a : GL (Fin n) K)) * P⁻¹ := by rw [hYD]
      _ = P * Dg x * P⁻¹ * (P * (a : GL (Fin n) K) * P⁻¹) := by group
  have hrev : ∀ (i j : Fin n) (x : E), χ i x = χ j x → χ (Fin.rev j) x = χ (Fin.rev i) x := by
    intro i j x hij
    have h1 := hrel i x
    have h2 := hrel j x
    rw [hij] at h1
    exact mul_left_cancel₀ (hnz j x) (h2.trans h1.symm)
  have hR : Subgroup.comap Φ.toMonoidHom S = ⊤ := by
    refine eq_top_of_rootElements_le hσ.invol hσ.exists_traceZero hσ.trace_surj
      (fun x hx => hσ.exists_norm hx) hn _ ?_ ?_ ?_
    · intro i j hij hi hj hjr c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ j)
      refine hmemS _ x hx1 ?_ (rootHom_pow_ringChar hσ.invol hij hi hj c)
      rw [coe_rootHom, hD x]
      exact rootMatrix_comm_diag_of_eq σ (fun c => χ c x) i j _ hxeq (hrev i j x hxeq)
    · intro i hi c
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ (Fin.rev i))
      refine hmemS _ x hx1 ?_ (longRootHom_pow_ringChar hi c)
      rw [coe_longRootHom, hD x]
      exact longRootMatrix_comm_diag_of_eq (fun c => χ c x) i _ hxeq
    · intro i k hi hik hk g hg
      obtain ⟨a, b, -, hga⟩ := hg
      have hmid : ∀ x : E, χ k x = 1 := by
        intro x
        have hsq : (χ k x) ^ 2 = 1 := by
          have := hrel k x
          rw [hk] at this
          simpa [sq] using this
        obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
        have h3 : χ k x ^ p = χ k x := by
          rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul]
        rw [← h3]
        exact hχp k x
      obtain ⟨x, hx1, -, hxeq⟩ := exists_ne_one_hom_eq hp hexpE hcard (χ i) (χ k)
      refine hmemS g x hx1 ?_ (heisenberg_pow_ringChar hℓ2 hi hik hk hga)
      have h1i : χ i x = 1 := hxeq.trans (hmid x)
      have hr : χ (Fin.rev i) x = 1 := by
        have := hrel i x
        rwa [h1i, one_mul] at this
      rw [hga, hD x]
      exact heisenbergMatrix_comm_diag_of_eq σ (fun c => χ c x) i k a b hxeq
        ((hmid x).trans hr.symm)
  refine eq_top_iff.2 fun y _ => ?_
  have hy : Φ.symm y ∈ Subgroup.comap Φ.toMonoidHom S := by
    rw [hR]
    exact Subgroup.mem_top _
  simpa using hy

theorem uniClosure_unitarySU_split (h : UnitaryFieldData ℓ f K) (hℓ2 : ℓ ≠ 2) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f - 1) (hn : 2 ≤ n) (E : Subgroup (unitarySU ℓ f K n))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤ := by
  classical
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε :=
    ⟨n / 2, n - 2 * (n / 2), by omega, by omega⟩
  have hB : (stdB h (2 * r + ε)).IsSymm := gramForm_isSymm h (by simp)
  have hBl : (stdB h (2 * r + ε)).SeparatingLeft := gramForm_separatingLeft h (by simp)
  set ρ := unitaryRep (ℓ := ℓ) (f := f) (n := 2 * r + ε) (K := K) E with hρdef
  let S : E → Module.End K (Fin (2 * r + ε) → K) := fun x =>
    ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K))
  have hScomm : ∀ x y, Commute (S x) (S y) := fun x y => by
    have hxy : x * y = y * x := Subtype.ext (hcomm x x.2 y y.2)
    show S x * S y = S y * S x
    simp only [S, ← Units.val_mul, ← map_mul, hxy]
  have hSpow : ∀ x, S x ^ p = 1 := fun x => by
    have hx : x ^ p = 1 := Subtype.ext (hexp x x.2)
    show ((ρ x : LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
      Module.End K (Fin (2 * r + ε) → K)) ^ p = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hx, map_one, Units.val_one]
  have hSiso : ∀ x v w, stdB h (2 * r + ε) (S x v) (S x w) = stdB h (2 * r + ε) v w :=
    fun x v w => mem_sesqUnitaryGroup.mp (unitaryRep_mem h E x) v w
  obtain ⟨w, hw, hev⟩ := exists_adapted_hypFamily h hp hp2 hpq hε r
    (V := Fin (2 * r + ε) → K) hB hBl (by simp) S hScomm hSpow hSiso
  let e := hypEquivFin r ε
  obtain ⟨P, hPJ, hPdiag⟩ := exists_frame_of_family h E (fun c => w (e.symm c))
    (fun i j => by
      rw [hw, hypGram_apply]
      have : e.symm j = hypPartner (e.symm i) ↔ j = Fin.rev i := by
        rw [Equiv.symm_apply_eq, hypEquivFin_hypPartner hε, Equiv.apply_symm_apply]
      simp only [this])
    (fun x hx => by
      choose d hd using fun c => hev ⟨x, hx⟩ (e.symm c)
      exact ⟨d, hd⟩)
  exact uniClosure_unitarySU_of_frame hℓ2 h hp hp2 hpq hn E hexp hcard P hPJ hPdiag

end Split


section TransvectionPow

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

theorem ofLinearEquiv_transvection_pow_apply {f : Module.Dual R W} {v : W} (h : f v = 0) (m : ℕ)
    (y : W) :
    ((LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection h) ^ m :
      LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) y = y + ((m : R) * f y) • v := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Units.val_mul, Module.End.mul_apply, ih]
    change LinearEquiv.transvection h y + ((m : R) * f (LinearEquiv.transvection h y)) • v = _
    rw [LinearEquiv.transvection.apply, map_add, map_smul, h, smul_eq_mul, mul_zero, add_zero]
    push_cast
    module

theorem ofLinearEquiv_transvection_pow_eq_one {f : Module.Dual R W} {v : W} (h : f v = 0) {m : ℕ}
    (hm : (m : R) = 0) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection h) ^ m = 1 := by
  apply Units.ext
  apply LinearMap.ext
  intro y
  rw [ofLinearEquiv_transvection_pow_apply, hm, zero_mul, zero_smul, add_zero]
  rfl

end TransvectionPow

section MixingUni

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LieType.SeitzGeneration.Mixing

variable {ℓ f : ℕ} {K : Type*} [Field K] {hK : UnitaryFieldData ℓ f K} {V : Type*}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {B : V →ₛₗ[hK.bar] V →ₗ[K] K}
  {x : LinearMap.GeneralLinearGroup K V}

theorem exists_mixing_element_of_paired_uni (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)} (hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]))
    {u w : V} (hu : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hind : LinearIndependent (AdjoinRoot (a : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (x : Module.End K V) (a : K[X])), ⟨w, hw⟩]) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧
        (g : Module.End K V) w = w + u := by
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  obtain ⟨φ, -, hφ1, -, -, hdet⟩ := (pairedPrimaryBlock H a hne).factor
  set W := primaryComponent (x : Module.End K V) (a : K[X]) with hWdef
  set E := AdjoinRoot (a : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp h1.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set ψ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hψ
  have hψw : ψ w₀ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hψu : ψ u₀ = 0 := by
    have h1 : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hψ, LinearMap.smul_apply, h1, smul_zero]
  let γ₀ : blockGL (x : Module.End K V) (a : K[X]) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hψu)
  have hγdet : LinearMap.det ((γ₀ : blockGL (x : Module.End K V) (a : K[X])) :
      Module.End E W) = 1 := by
    have h1 := LinearEquiv.transvection.det_eq_one hψu
    rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at h1
    exact h1
  have hγr : γ₀ ^ ringChar K = 1 := by
    refine ofLinearEquiv_transvection_pow_eq_one hψu ?_
    rw [← map_natCast (algebraMap K E), ringChar.Nat.cast_ringChar, map_zero]
  refine ⟨(φ.symm γ₀ : LinearMap.GeneralLinearGroup K V), (φ.symm γ₀).2.1, ?_, ?_, ?_⟩
  · refine hdet (φ.symm γ₀) ?_
    rw [MulEquiv.apply_symm_apply]
    exact hγdet
  · rw [← SubgroupClass.coe_pow, ← map_pow, hγr, map_one, OneMemClass.coe_one]
  · have hg := hφ1 (φ.symm γ₀) w hw
    rw [MulEquiv.apply_symm_apply] at hg
    rw [← hg]
    have hγ : blockApply γ₀ w hw = w + ((ψ w₀ • u₀ : W) : V) := rfl
    rw [hγ, hψw, one_smul]

theorem exists_mixing_element_of_selfDual_uni (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)} (hself : dualPoly hK.bar (a : K[X]) = a)
    (hdeg : 2 ≤ (a : K[X]).natDegree) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ s ∈ S₁, (x : Module.End K V) s ∈ S₁) (hS₂ : ∀ s ∈ S₂, (x : Module.End K V) s ∈ S₂)
    (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0) (hnd₁ : (B.domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : (B.domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0)
    {u w : V} (hu : u ∈ S₁) (hua : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hu0 : u ≠ 0) (hw : w ∈ S₂) (hwa : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw0 : w ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (g : Module.End K V) w₀ = u'' + w'' := by
  classical
  have := hK.finite
  have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
  obtain ⟨hodd, hE, hbarE, hadj, Hf, hsymmF, hsep, htrace, -, φ, hφ1, hφdet⟩ :=
    selfDualPrimaryBlock H a hself
  have haX : (a : K[X]) ∈ primaryFactors (x : Module.End K V) := a.2
  have hsymm : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      hE.bar (Hf s t) = Hf t s := fun s t => hsymmF.eq s t
  have hbarne : ∃ s : AdjoinRoot (a : K[X]), hE.bar s ≠ s := hE.exists_bar_ne
  have hεa : primaryProjection (x : Module.End K V) (a : K[X]) =
      primaryProjection (x : Module.End K V) (dualPoly hK.bar (a : K[X])) := by
    rw [hself]
  have hεadj : ∀ v t : V, B (primaryProjection (x : Module.End K V) (a : K[X]) v) t =
      B v (primaryProjection (x : Module.End K V) (a : K[X]) t) := by
    intro v t
    rw [H.adj_spec, adj_primaryProjection H haX, ← hεa]
  have hBtr : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]),
      B (s : V) (t : V) = Algebra.trace K (AdjoinRoot (a : K[X])) (Hf s t) := fun s t => by
    simpa using (htrace s t 1).symm
  have hHorth : ∀ s t : primaryComponent (x : Module.End K V) (a : K[X]), (s : V) ∈ S₁ →
      (t : V) ∈ S₂ → Hf s t = 0 := by
    intro s t hs ht
    refine eq_zero_of_trace_mul_eq_zero (a : K[X]) (Hf s t) fun c => ?_
    rw [htrace s t c]
    exact horth _ hs _ (coe_smul_mem_of_stable hS₂ c t ht)
  have hex : ∀ S : Submodule K V, (∀ s ∈ S, (x : Module.End K V) s ∈ S) →
      (B.domRestrict₁₂ S S).SeparatingLeft →
      ∀ v : primaryComponent (x : Module.End K V) (a : K[X]), (v : V) ∈ S → v ≠ 0 →
        ∃ z : primaryComponent (x : Module.End K V) (a : K[X]), (z : V) ∈ S ∧ Hf z z ≠ 0 := by
    intro S hS hnd v hvS hv0
    obtain ⟨s, hs, hBs⟩ : ∃ s ∈ S, B (v : V) s ≠ 0 := by
      by_contra hcon
      push Not at hcon
      refine hv0 (Subtype.ext ?_)
      have := hnd ⟨(v : V), hvS⟩ (fun y => by
        rw [LinearMap.domRestrict₁₂_apply]
        exact hcon y y.2)
      have h0 : ((⟨(v : V), hvS⟩ : S) : V) = ((0 : S) : V) := congrArg Subtype.val this
      simpa using h0
    set y₁ : primaryComponent (x : Module.End K V) (a : K[X]) :=
      ⟨primaryProjection (x : Module.End K V) (a : K[X]) s,
        primaryProjection_mem hsq haX s⟩ with hy₁
    have hy₁S : (y₁ : V) ∈ S := KCUnitaryMixing.aeval_apply_mem hS _ hs
    have h1 : B (y₁ : V) (v : V) = B s (v : V) := by
      rw [hy₁]
      change B (primaryProjection (x : Module.End K V) (a : K[X]) s) (v : V) = _
      rw [hεadj, primaryProjection_of_mem hsq haX v.2]
    have h2 : B (v : V) (y₁ : V) = B (v : V) s := by
      rw [← hB.eq, h1, hB.eq]
    have hz : Hf v y₁ ≠ 0 := by
      intro h0
      apply hBs
      rw [← h2, hBtr, h0, map_zero]
    exact exists_anisotropic_of_pairing Hf hsymm hbarne
      { carrier := {z | (z : V) ∈ S}
        add_mem' := fun {a b} ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c z hz => coe_smul_mem_of_stable hS c z hz } hvS hy₁S hz
  obtain ⟨z₁, hz₁S, hz₁⟩ := hex S₁ hS₁ hnd₁ ⟨u, hua⟩ hu
    (fun h => hu0 (by simpa using congrArg Subtype.val h))
  obtain ⟨z₂, hz₂S, hz₂⟩ := hex S₂ hS₂ hnd₂ ⟨w, hwa⟩ hw
    (fun h => hw0 (by simpa using congrArg Subtype.val h))
  have hz₁0 : z₁ ≠ 0 := fun h => hz₁ (by rw [h]; simp)
  have hz₂0 : z₂ ≠ 0 := fun h => hz₂ (by rw [h]; simp)
  have ht₁ : hE.bar (Hf z₁ z₁) = Hf z₁ z₁ := hsymm z₁ z₁
  have ht₂ : hE.bar (Hf z₂ z₂) = Hf z₂ z₂ := hsymm z₂ z₂
  have hmem : (-(Hf z₂ z₂) / Hf z₁ z₁ : AdjoinRoot (a : K[X])) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_div₀, map_neg, ht₁, ht₂]
  obtain ⟨lam, hlam⟩ := hE.normHom_surjective ⟨_, hmem⟩
  have hlam' : lam * hE.bar lam = -(Hf z₂ z₂) / Hf z₁ z₁ := by
    have := congrArg Subtype.val hlam
    simpa [UnitaryFieldData.norm] using this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlam'
    exact (div_ne_zero (neg_ne_zero.mpr hz₂) hz₁) hlam'.symm
  have hnorm : Hf (lam • z₁) (lam • z₁) = -(Hf z₂ z₂) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc lam * (hE.bar lam * Hf z₁ z₁) = (lam * hE.bar lam) * Hf z₁ z₁ := by ring
      _ = -(Hf z₂ z₂) := by rw [hlam']; field_simp
  have hlz₁S : ((lam • z₁ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ :=
    coe_smul_mem_of_stable hS₁ lam z₁ hz₁S
  have hH12 : Hf (lam • z₁) z₂ = 0 := hHorth _ _ hlz₁S hz₂S
  have hH21 : Hf z₂ (lam • z₁) = 0 := by
    rw [← hsymm, hH12, map_zero]
  have hee : Hf (lam • z₁ + z₂) (lam • z₁ + z₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hnorm, hH12, hH21]
    ring
  have hz₂V : (z₂ : V) ≠ 0 := fun h => hz₂0 (Subtype.ext h)
  obtain ⟨w₀, hw₀S, hw₀i, hBw₀⟩ := hKI (z₂ : V) hz₂S hz₂V
  set ω : primaryComponent (x : Module.End K V) (a : K[X]) :=
    ⟨primaryProjection (x : Module.End K V) (a : K[X]) w₀, primaryProjection_mem hsq haX w₀⟩
    with hω
  have hωS : (ω : V) ∈ S₂ := KCUnitaryMixing.aeval_apply_mem hS₂ _ hw₀S
  have hBω : B (z₂ : V) (ω : V) = B (z₂ : V) w₀ := by
    rw [hω]
    change B (z₂ : V) (primaryProjection (x : Module.End K V) (a : K[X]) w₀) = _
    rw [← hεadj, primaryProjection_of_mem hsq haX z₂.2]
  have hh₀ : Hf z₂ ω ≠ 0 := by
    intro h0
    apply hBw₀
    rw [← hBω, hBtr, h0, map_zero]
  have hH1ω : Hf (lam • z₁) ω = 0 := hHorth _ _ hlz₁S hωS
  have hHeω : Hf (lam • z₁ + z₂) ω = Hf z₂ ω := by
    rw [map_add, LinearMap.add_apply, hH1ω, zero_add]
  have hc : ∃ c₁ c₂ : AdjoinRoot (a : K[X]), hE.bar c₁ = -c₁ ∧ hE.bar c₂ = -c₂ ∧ c₁ ≠ 0 ∧
      c₂ ≠ 0 ∧ c₁ ≠ c₂ := by
    have := hE.finite
    have hq : 3 ≤ ℓ ^ (f * (a : K[X]).natDegree) := by
      have hℓ2 := hK.prime.two_le
      have hf1 := hK.one_le
      calc 3 ≤ 2 ^ 2 := by norm_num
        _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ2 2
        _ ≤ ℓ ^ (f * (a : K[X]).natDegree) :=
          Nat.pow_le_pow_right (by omega) (by nlinarith)
    have hcard : 2 < (hE.traceZero : Set (AdjoinRoot (a : K[X]))).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 2 < Nat.card hE.traceZero
      rw [hE.card_traceZero]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
    have hbar : ∀ c ∈ hE.traceZero, hE.bar c = -c := fun c hc => by
      have := hE.mem_traceZero.mp hc
      rw [UnitaryFieldData.trace] at this
      linear_combination this
    by_cases h0₁ : c₁ = 0
    · exact ⟨c₂, c₃, hbar _ h₂, hbar _ h₃, fun h => h12 (h0₁.trans h.symm),
        fun h => h13 (h0₁.trans h.symm), h23⟩
    · by_cases h0₂ : c₂ = 0
      · exact ⟨c₁, c₃, hbar _ h₁, hbar _ h₃, h0₁, fun h => h23 (h0₂.trans h.symm), h13⟩
      · exact ⟨c₁, c₂, hbar _ h₁, hbar _ h₂, h0₁, h0₂, h12⟩
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hc12⟩ := hc
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    exact hBw₀ (by simp)
  have hmain : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → ∃ g : LinearMap.GeneralLinearGroup K V,
      g ∈ unitaryCentralizer B x ∧ LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧
        (g : Module.End K V) w₀ = w₀ +
          (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) :
            V) := by
    intro c hc
    have hfv : (c • Hf (lam • z₁ + z₂)) (lam • z₁ + z₂) = 0 := by
      rw [LinearMap.smul_apply, hee, smul_zero]
    let γ : primaryComponent (x : Module.End K V) (a : K[X]) ≃ₗ[AdjoinRoot (a : K[X])]
        primaryComponent (x : Module.End K V) (a : K[X]) := LinearEquiv.transvection hfv
    have hγapply : ∀ y, γ y = y + (c * Hf (lam • z₁ + z₂) y) • (lam • z₁ + z₂) := fun y => rfl
    have hγiso : ∀ y z, Hf (γ y) (γ z) = Hf y z := fun y z => by
      rw [hγapply, hγapply]
      exact transvection_isometry Hf hsymm hee hc y z
    let γg : blockGL (x : Module.End K V) (a : K[X]) :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv γ
    have hγmem : γg ∈ sesqUnitaryGroup Hf := fun y z => hγiso y z
    have hγdet : LinearMap.det ((γg : blockGL (x : Module.End K V) (a : K[X])) :
        Module.End (AdjoinRoot (a : K[X])) (primaryComponent (x : Module.End K V) (a : K[X]))) =
        1 := by
      have h1 := LinearEquiv.transvection.det_eq_one hfv
      rw [← Units.val_inj, LinearEquiv.coe_det, Units.val_one] at h1
      exact h1
    have hγspec : γg ∈ sesqSpecialUnitaryGroup Hf := mem_sesqSpecialUnitaryGroup.mpr ⟨hγmem, hγdet⟩
    set g := φ.symm ⟨γg, hγmem⟩ with hg
    refine ⟨(g : LinearMap.GeneralLinearGroup K V), g.2.1, hφdet g ?_, ?_, ?_⟩
    · rw [hg, MulEquiv.apply_symm_apply]
      exact hγspec
    · have hγr : (⟨γg, hγmem⟩ : sesqUnitaryGroup Hf) ^ ringChar K = 1 := by
        apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        refine ofLinearEquiv_transvection_pow_eq_one hfv ?_
        rw [← map_natCast (algebraMap K (AdjoinRoot (a : K[X]))), ringChar.Nat.cast_ringChar,
          map_zero]
      rw [← SubgroupClass.coe_pow, hg, ← map_pow, hγr, map_one, OneMemClass.coe_one]
    · have h1 := apply_of_supported hsq haX g.2 w₀
      have h3 := hφ1 g (primaryProjection (x : Module.End K V) (a : K[X]) w₀)
        (primaryProjection_mem hsq haX w₀)
      have h4 : φ g = ⟨γg, hγmem⟩ := by rw [hg, MulEquiv.apply_symm_apply]
      rw [h4] at h3
      have h5 : ((γ ω : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
          ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (primaryProjection (x : Module.End K V) (a : K[X]) w₀) := h3
      rw [h1, ← h5, hγapply, hHeω]
      change w₀ + (((ω + (c * Hf z₂ ω) • (lam • z₁ + z₂) :
        primaryComponent (x : Module.End K V) (a : K[X])) : V) - (ω : V)) = _
      rw [Submodule.coe_add]
      abel
  have hpart : ∀ c : AdjoinRoot (a : K[X]), c ≠ 0 →
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₁ ∧
      (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 ∧
      (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ∈ S₂ := by
    intro c hc0
    refine ⟨coe_smul_mem_of_stable hS₁ _ _ hlz₁S, fun h => ?_,
      coe_smul_mem_of_stable hS₂ _ _ hz₂S⟩
    exact smul_ne_zero (mul_ne_zero hc0 hh₀) (smul_ne_zero hlam0 hz₁0) (Subtype.ext h)
  have hsplit : ∀ c : AdjoinRoot (a : K[X]),
      (((c * Hf z₂ ω) • (lam • z₁ + z₂) : primaryComponent (x : Module.End K V) (a : K[X])) : V) =
        (((c * Hf z₂ ω) • (lam • z₁) : primaryComponent (x : Module.End K V) (a : K[X])) : V) +
        (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) := by
    intro c
    rw [smul_add, Submodule.coe_add]
  have hfin : ∀ c : AdjoinRoot (a : K[X]), hE.bar c = -c → c ≠ 0 →
      w₀ + (((c * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) : V) ≠ 0 →
      ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
        LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
          ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧
            (g : Module.End K V) w₀ = u'' + w'' := by
    intro c hc hc0 hne
    obtain ⟨g, hg1, hg2, hgr, hg3⟩ := hmain c hc
    obtain ⟨hp1, hp2, hp3⟩ := hpart c hc0
    refine ⟨g, hg1, hg2, hgr, w₀, hw₀S, hw₀0, hw₀i, _, hp1, w₀ + _, S₂.add_mem hw₀S hp3, hp2, hne, ?_⟩
    rw [hg3, hsplit]
    abel
  by_cases h1 : w₀ + (((c₁ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
      V) = 0
  · by_cases h2 : w₀ + (((c₂ * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) :
        V) = 0
    · exfalso
      have e1 := eq_neg_of_add_eq_zero_right h1
      have e2 := eq_neg_of_add_eq_zero_right h2
      have h0 : (((c₁ - c₂) * Hf z₂ ω) • z₂ : primaryComponent (x : Module.End K V) (a : K[X])) =
          0 := by
        apply Subtype.ext
        rw [sub_mul, sub_smul, Submodule.coe_sub, e1, e2, sub_self]
        rfl
      exact smul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hc12) hh₀) hz₂0 h0
    · exact hfin c₂ hc₂ hc₂0 h2
  · exact hfin c₁ hc₁ hc₁0 h1

theorem exists_mixing_element_uni (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hx : x ∈ sesqUnitaryGroup B) (hsq : Squarefree (minpoly K (x : Module.End K V)))
    {a : primaryFactors (x : Module.End K V)}
    (hdeg : dualPoly hK.bar (a : K[X]) = a → 2 ≤ (a : K[X]).natDegree) {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ s ∈ S₁, (x : Module.End K V) s ∈ S₁) (hS₂ : ∀ s ∈ S₂, (x : Module.End K V) s ∈ S₂)
    (hdisj : Disjoint S₁ S₂) (horth : ∀ s ∈ S₁, ∀ t ∈ S₂, B s t = 0)
    (hnd₁ : (B.domRestrict₁₂ S₁ S₁).SeparatingLeft)
    (hnd₂ : (B.domRestrict₁₂ S₂ S₂).SeparatingLeft)
    (hKI : ∀ w ∈ S₂, w ≠ 0 → ∃ w₀ ∈ S₂, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0)
    {u w : V} (hu : u ∈ S₁) (hua : u ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hu0 : u ≠ 0) (hw : w ∈ S₂) (hwa : w ∈ primaryComponent (x : Module.End K V) (a : K[X]))
    (hw0 : w ≠ 0) :
    ∃ g : LinearMap.GeneralLinearGroup K V, g ∈ unitaryCentralizer B x ∧
      LinearMap.det (g : Module.End K V) = 1 ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ S₂, w₀ ≠ 0 ∧ B w₀ w₀ = 0 ∧
        ∃ u'' ∈ S₁, ∃ w'' ∈ S₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (g : Module.End K V) w₀ = u'' + w'' := by
  by_cases hself : dualPoly hK.bar (a : K[X]) = a
  · exact exists_mixing_element_of_selfDual_uni hB hBl hx hsq hself (hdeg hself) hS₁ hS₂ horth hnd₁
      hnd₂ hKI hu hua hu0 hw hwa hw0
  · have H : UnitaryPrimaryData hK.bar B x := ⟨hK.bar_bar, hB, hBl, hx, hsq⟩
    have hne : (a : K[X]) ≠ dualPoly hK.bar (a : K[X]) := fun h => hself h.symm
    have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
    have hind := KCUnitaryMixing.linearIndependent_pair_of_disjoint (a := (a : K[X]))
      hS₁ hS₂ hdisj hu hw hua hwa hu0 hw0
    obtain ⟨g, hg1, hg2, hgr, hg3⟩ :=
      exists_mixing_element_of_paired_uni hB hBl hx hsq hne hua hwa hind
    have hwi : B w w = 0 := (pairedPrimaryBlock H a hne).isotropic_left w hwa w hwa
    exact ⟨g, hg1, hg2, hgr, w, hw, hw0, hwi, u, hu, w, hw, hu0, hw0, hg3.trans (add_comm w u)⟩

end MixingUni

section UnitaryMixingGeneric

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {ℓ f : ℕ} {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W]

theorem exists_unitary_transvection_mixing (hE : UnitaryFieldData ℓ f E) (hq : 3 ≤ ℓ ^ f)
    (Hf : W →ₛₗ[hE.bar] W →ₗ[E] E) (hsymm : ∀ a b, hE.bar (Hf a b) = Hf b a)
    {R₁ R₂ : Submodule E W} (horth : ∀ a ∈ R₁, ∀ b ∈ R₂, Hf a b = 0)
    {z₁ z₂ : W} (hz₁R : z₁ ∈ R₁) (hz₂R : z₂ ∈ R₂) (hz₁ : Hf z₁ z₁ ≠ 0) (hz₂ : Hf z₂ z₂ ≠ 0)
    {n : ℕ} (hn : (n : E) = 0) :
    ∃ γ : LinearMap.GeneralLinearGroup E W, γ ∈ sesqUnitaryGroup Hf ∧ γ ^ n = 1 ∧
      ∃ u'' ∈ R₁, ∃ w'' ∈ R₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (γ : W →ₗ[E] W) z₂ = u'' + w'' := by
  classical
  have := hE.finite
  have hz₁0 : z₁ ≠ 0 := fun h0 => hz₁ (by rw [h0]; simp)
  have hz₂0 : z₂ ≠ 0 := fun h0 => hz₂ (by rw [h0]; simp)
  have ht₁ : hE.bar (Hf z₁ z₁) = Hf z₁ z₁ := hsymm z₁ z₁
  have ht₂ : hE.bar (Hf z₂ z₂) = Hf z₂ z₂ := hsymm z₂ z₂
  have hmem : (-(Hf z₂ z₂) / Hf z₁ z₁ : E) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_div₀, map_neg, ht₁, ht₂]
  obtain ⟨lam, hlam⟩ := hE.normHom_surjective ⟨_, hmem⟩
  have hlam' : lam * hE.bar lam = -(Hf z₂ z₂) / Hf z₁ z₁ := by
    have := congrArg Subtype.val hlam
    simpa [UnitaryFieldData.norm] using this
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hlam'
    exact (div_ne_zero (neg_ne_zero.mpr hz₂) hz₁) hlam'.symm
  have hnorm : Hf (lam • z₁) (lam • z₁) = -(Hf z₂ z₂) := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc lam * (hE.bar lam * Hf z₁ z₁) = (lam * hE.bar lam) * Hf z₁ z₁ := by ring
      _ = -(Hf z₂ z₂) := by rw [hlam']; field_simp
  have hlz₁R : lam • z₁ ∈ R₁ := R₁.smul_mem lam hz₁R
  have hH12 : Hf (lam • z₁) z₂ = 0 := horth _ hlz₁R _ hz₂R
  have hH21 : Hf z₂ (lam • z₁) = 0 := by
    rw [← hsymm, hH12, map_zero]
  have hee : Hf (lam • z₁ + z₂) (lam • z₁ + z₂) = 0 := by
    simp only [map_add, LinearMap.add_apply, hnorm, hH12, hH21]
    ring
  have hHe2 : Hf (lam • z₁ + z₂) z₂ = Hf z₂ z₂ := by
    rw [map_add, LinearMap.add_apply, hH12, zero_add]
  obtain ⟨c₁, c₂, hc₁, hc₂, hc₁0, hc₂0, hc12⟩ : ∃ c₁ c₂ : E, hE.bar c₁ = -c₁ ∧ hE.bar c₂ = -c₂ ∧
      c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ c₁ ≠ c₂ := by
    have hcard : 2 < (hE.traceZero : Set E).ncard := by
      rw [← Nat.card_coe_set_eq]
      change 2 < Nat.card hE.traceZero
      rw [hE.card_traceZero]
      omega
    obtain ⟨c₁, c₂, c₃, h₁, h₂, h₃, h12, h13, h23⟩ :=
      (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
    have hbar' : ∀ c ∈ hE.traceZero, hE.bar c = -c := fun c hc => by
      have := hE.mem_traceZero.mp hc
      rw [UnitaryFieldData.trace] at this
      linear_combination this
    by_cases h0₁ : c₁ = 0
    · exact ⟨c₂, c₃, hbar' _ h₂, hbar' _ h₃, fun h => h12 (h0₁.trans h.symm),
        fun h => h13 (h0₁.trans h.symm), h23⟩
    · by_cases h0₂ : c₂ = 0
      · exact ⟨c₁, c₃, hbar' _ h₁, hbar' _ h₃, h0₁, fun h => h23 (h0₂.trans h.symm), h13⟩
      · exact ⟨c₁, c₂, hbar' _ h₁, hbar' _ h₂, h0₁, h0₂, h12⟩
  have hmain : ∀ c : E, hE.bar c = -c → c ≠ 0 → (1 + c * Hf z₂ z₂) • z₂ ≠ 0 →
      ∃ γ : LinearMap.GeneralLinearGroup E W, γ ∈ sesqUnitaryGroup Hf ∧ γ ^ n = 1 ∧
        ∃ u'' ∈ R₁, ∃ w'' ∈ R₂, u'' ≠ 0 ∧ w'' ≠ 0 ∧ (γ : W →ₗ[E] W) z₂ = u'' + w'' := by
    intro c hc hc0 hne
    have hfv : (c • Hf (lam • z₁ + z₂)) (lam • z₁ + z₂) = 0 := by
      rw [LinearMap.smul_apply, hee, smul_zero]
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hfv), ?_,
      ofLinearEquiv_transvection_pow_eq_one hfv hn, (c * Hf z₂ z₂) • (lam • z₁),
      R₁.smul_mem _ hlz₁R, (1 + c * Hf z₂ z₂) • z₂, R₂.smul_mem _ hz₂R,
      smul_ne_zero (mul_ne_zero hc0 hz₂) (smul_ne_zero hlam0 hz₁0), hne, ?_⟩
    · rw [mem_sesqUnitaryGroup]
      intro y z
      exact Mixing.transvection_isometry Hf hsymm hee hc y z
    · change z₂ + (c * Hf (lam • z₁ + z₂) z₂) • (lam • z₁ + z₂) = _
      rw [hHe2, smul_add, add_smul, one_smul]
      abel
  by_cases h1 : (1 + c₁ * Hf z₂ z₂) • z₂ = 0
  · by_cases h2 : (1 + c₂ * Hf z₂ z₂) • z₂ = 0
    · exfalso
      have e1 : 1 + c₁ * Hf z₂ z₂ = 0 := (smul_eq_zero.mp h1).resolve_right hz₂0
      have e2 : 1 + c₂ * Hf z₂ z₂ = 0 := (smul_eq_zero.mp h2).resolve_right hz₂0
      have e3 : (c₁ - c₂) * Hf z₂ z₂ = 0 := by linear_combination e1 - e2
      exact mul_ne_zero (sub_ne_zero.mpr hc12) hz₂ e3
    · exact hmain c₂ hc₂ hc₂0 h2
  · exact hmain c₁ hc₁ hc₁0 h1

end UnitaryMixingGeneric

section SpPlaneFive

open Polynomial CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)


variable {ℓ f p r : ℕ} {K : Type} [Field K] {Ahat : Subgroup (StatedSp r K)}

theorem exists_mixing_element_of_paired_sp_uni (S : SpPlaneSetup ℓ f p r K Ahat) {x : StatedSp r K}
    (hxA : x ∈ Ahat) (hx1 : x ≠ 1) {h : primaryFactors (spEnd x)}
    (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    {u w : Fin r ⊕ Fin r → K} (hu : u ∈ primaryComponent (spEnd x) (h : K[X]))
    (hw : w ∈ primaryComponent (spEnd x) (h : K[X]))
    (hind : LinearIndependent (AdjoinRoot (h : K[X]))
      ![(⟨u, hu⟩ : primaryComponent (spEnd x) (h : K[X])), ⟨w, hw⟩]) :
    ∃ g : StatedSp r K, g * x = x * g ∧ g ^ ringChar K = 1 ∧ spEnd g w = w + u := by
  obtain ⟨φ, hφ1, -⟩ := ((S.blocks hxA hx1).paired h hne).factor
  set W := primaryComponent (spEnd x) (h : K[X]) with hWdef
  set E := AdjoinRoot (h : K[X]) with hEdef
  set u₀ : W := ⟨u, hu⟩ with hu₀
  set w₀ : W := ⟨w, hw⟩ with hw₀
  have hwnot : w₀ ∉ Submodule.span E {u₀} := by
    intro hmem
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := (LinearIndependent.pair_iff.mp hind) e (-1) (by
      simp only [neg_smul, one_smul]
      rw [he]
      exact add_neg_cancel _)
    exact one_ne_zero (neg_eq_zero.mp h1.2)
  obtain ⟨φ₀, hφ₀w, hφ₀u⟩ := Submodule.exists_le_ker_of_notMem hwnot
  set ψ : Module.Dual E W := (φ₀ w₀)⁻¹ • φ₀ with hψ
  have hψw : ψ w₀ = 1 := by
    rw [hψ, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀w]
  have hψu : ψ u₀ = 0 := by
    have h1 : φ₀ u₀ = 0 := hφ₀u (Submodule.mem_span_singleton_self u₀)
    rw [hψ, LinearMap.smul_apply, h1, smul_zero]
  let γ₀ : blockGL (spEnd x) (h : K[X]) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (LinearEquiv.transvection hψu)
  have hγr : γ₀ ^ ringChar K = 1 := by
    refine ofLinearEquiv_transvection_pow_eq_one hψu ?_
    rw [← map_natCast (algebraMap K E), ringChar.Nat.cast_ringChar, map_zero]
  refine ⟨(φ.symm γ₀ : StatedSp r K), (mem_spSupported.mp (φ.symm γ₀).2).1, ?_, ?_⟩
  · rw [← SubgroupClass.coe_pow, ← map_pow, hγr, map_one, OneMemClass.coe_one]
  · have hg := hφ1 (φ.symm γ₀) w hw
    rw [MulEquiv.apply_symm_apply] at hg
    rw [← hg]
    have hγ : blockApply γ₀ w hw = w + ((ψ w₀ • u₀ : W) : Fin r ⊕ Fin r → K) := rfl
    rw [hγ, hψw, one_smul]

@[expose] def compSub {x : StatedSp r K} (a : K[X]) {M : Submodule K (Fin r ⊕ Fin r → K)}
    (hstab : ∀ s ∈ M, spEnd x s ∈ M) : Submodule (AdjoinRoot a) (primaryComponent (spEnd x) a) where
  carrier := {v | (v : Fin r ⊕ Fin r → K) ∈ M}
  add_mem' := fun {s t} hs ht => M.add_mem hs ht
  zero_mem' := M.zero_mem
  smul_mem' := fun c v hv => coe_smul_mem_of_stable hstab c v hv

theorem exists_anisotropic_compSub (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    {x : StatedSp r K} (hxA : x ∈ Ahat) {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h)
    {bar : AdjoinRoot (h : K[X]) →+* AdjoinRoot (h : K[X])}
    (Hf : primaryComponent (spEnd x) (h : K[X]) →ₛₗ[bar]
      primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])] AdjoinRoot (h : K[X]))
    (hsymm : ∀ a b, bar (Hf a b) = Hf b a) (hbarne : ∃ s, bar s ≠ s) {η : AdjoinRoot (h : K[X])}
    (hη0 : η ≠ 0)
    (htrace : ∀ (v w : primaryComponent (spEnd x) (h : K[X])) (c : AdjoinRoot (h : K[X])),
      Algebra.trace K (AdjoinRoot (h : K[X])) (c * Hf v w) =
        spForm r K (v : Fin r ⊕ Fin r → K)
          (((c * η) • w : primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K))
    {M : Subgroup ↥Ahat} (hM : Nat.card M = p) (hstabM : ∀ s ∈ spLineSpace M, spEnd x s ∈ spLineSpace M)
    {v : Fin r ⊕ Fin r → K} (hvM : v ∈ spLineSpace M)
    (hvh : v ∈ primaryComponent (spEnd x) (h : K[X])) (hv0 : v ≠ 0) :
    ∃ z ∈ compSub (h : K[X]) hstabM, Hf z z ≠ 0 := by
  set v₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨v, hvh⟩ with hv₁
  have hv₁R : v₁ ∈ compSub (h : K[X]) hstabM := hvM
  obtain ⟨y, hyM, hyh, hBy⟩ := exists_pairing_in_component
    (altPrimaryData_spLin S.p_cast_ne_zero (S.pow_eq_one hxA)) h.2 hself hstabM
    (D.nondeg (some ⟨M, hM⟩)) hvM hvh hv0
  set y₁ : primaryComponent (spEnd x) (h : K[X]) := ⟨y, hyh⟩ with hy₁
  have hy₁R : y₁ ∈ compSub (h : K[X]) hstabM := hyM
  have hz : Hf v₁ y₁ ≠ 0 := by
    intro h0
    apply hBy
    have h1 := htrace v₁ (η⁻¹ • y₁) 1
    have e1 : Hf v₁ (η⁻¹ • y₁) = 0 := by rw [map_smul, smul_eq_mul, h0, mul_zero]
    have e2 : ((1 * η) • (η⁻¹ • y₁) : primaryComponent (spEnd x) (h : K[X])) = y₁ := by
      rw [smul_smul, one_mul, mul_inv_cancel₀ hη0, one_smul]
    rw [e1, e2, mul_zero, map_zero] at h1
    exact h1.symm
  exact exists_anisotropic_of_pairing Hf hsymm hbarne _ hv₁R hy₁R hz

theorem exists_mixing_element_of_selfDual_sp_uni (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) (hℓ2 : ℓ ≠ 2) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {x : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1)
    {h : primaryFactors (spEnd x)} (hh1 : (h : K[X]) ≠ X - 1)
    (hself : reciprocalPolynomial (h : K[X]) = h) {u w : Fin r ⊕ Fin r → K}
    (hu : u ∈ spLineSpace L) (huh : u ∈ primaryComponent (spEnd x) (h : K[X])) (hu0 : u ≠ 0)
    (hw : w ∈ spLineSpace N) (hwh : w ∈ primaryComponent (spEnd x) (h : K[X])) (hw0 : w ≠ 0) :
    ∃ g : StatedSp r K, g * x = x * g ∧ g ^ ringChar K = 1 ∧ ∃ w₀ ∈ spLineSpace N, w₀ ≠ 0 ∧
      ∃ u' ∈ spLineSpace L, ∃ w' ∈ spLineSpace N, u' ≠ 0 ∧ w' ≠ 0 ∧
        spEnd g w₀ = u' + w' := by
  classical
  have := S.finite
  have blocks := S.blocks hxA hx1
  obtain ⟨d, hd2, hpd, σ, hσpow, hσne, hσσ, hσroot, hσadj, hE, hbar, Hf, hsymmF, hsep,
    ⟨η, hη0, hηbar, htrace⟩, -, φ, hφ⟩ := (blocks.selfDual h hh1 hself).exists_half
  have hsymm : ∀ a b : primaryComponent (spEnd x) (h : K[X]), hE.bar (Hf a b) = Hf b a :=
    fun a b => hsymmF.eq a b
  have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
    S.spLineSpace_stable ⟨x, hxA⟩ hs
  have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
  have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
    fun a ha b hb => D.orth _ _ hne a ha b hb
  have hHf : ∀ a ∈ compSub (h : K[X]) hstabL, ∀ b ∈ compSub (h : K[X]) hstabN, Hf a b = 0 := by
    intro a ha b hb
    refine eq_zero_of_trace_mul_eq_zero (h : K[X]) (Hf a b) fun c => ?_
    rw [htrace a b c]
    exact horth _ ha _ (coe_smul_mem_of_stable hstabN (c * η) b hb)
  have hbarne : ∃ s, hE.bar s ≠ s := by
    by_contra hcon
    push Not at hcon
    refine hσne (AlgEquiv.ext fun z => ?_)
    rw [AlgEquiv.one_apply, ← hbar z]
    exact hcon z
  obtain ⟨z₁, hz₁L, hz₁⟩ :=
    exists_anisotropic_compSub S D hxA hself Hf hsymm hbarne hη0 htrace hL hstabL hu huh hu0
  obtain ⟨z₂, hz₂N, hz₂⟩ :=
    exists_anisotropic_compSub S D hxA hself Hf hsymm hbarne hη0 htrace hN hstabN hw hwh hw0
  have hq : 3 ≤ ℓ ^ (f * d) := by
    have hℓ3 : 3 ≤ ℓ := by have := S.prime_ell.two_le; omega
    calc 3 ≤ ℓ := hℓ3
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ (f * d) := Nat.pow_le_pow_right S.prime_ell.pos hE.one_le
  have hn : ((ringChar K : ℕ) : AdjoinRoot (h : K[X])) = 0 := by
    rw [← map_natCast (algebraMap K (AdjoinRoot (h : K[X]))), ringChar.Nat.cast_ringChar, map_zero]
  obtain ⟨γ, hγmem, hγr, u'', hu''L, w'', hw''N, hu''0, hw''0, hγz⟩ :=
    exists_unitary_transvection_mixing hE hq Hf hsymm hHf hz₁L hz₂N hz₁ hz₂ hn
  have hz₂0 : (z₂ : Fin r ⊕ Fin r → K) ≠ 0 := fun h0 => hz₂ (by
    rw [show z₂ = 0 from Subtype.ext h0]
    simp)
  set g := φ.symm ⟨γ, hγmem⟩ with hg
  refine ⟨(g : StatedSp r K), (mem_spSupported.mp g.2).1, ?_, (z₂ : Fin r ⊕ Fin r → K), hz₂N, hz₂0,
    (u'' : Fin r ⊕ Fin r → K), hu''L, (w'' : Fin r ⊕ Fin r → K), hw''N,
    fun h0 => hu''0 (Subtype.ext h0), fun h0 => hw''0 (Subtype.ext h0), ?_⟩
  · have hγr' : (⟨γ, hγmem⟩ : sesqUnitaryGroup Hf) ^ ringChar K = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hγr)
    rw [← SubgroupClass.coe_pow, hg, ← map_pow, hγr', map_one, OneMemClass.coe_one]
  · have h3 := hφ g (z₂ : Fin r ⊕ Fin r → K) z₂.2
    have h4 : φ g = ⟨γ, hγmem⟩ := by rw [hg, MulEquiv.apply_symm_apply]
    rw [h4] at h3
    rw [← h3]
    have h5 : blockApply ((⟨γ, hγmem⟩ : sesqUnitaryGroup Hf) : blockGL (spEnd x) (h : K[X]))
        (z₂ : Fin r ⊕ Fin r → K) z₂.2 =
          (((γ : primaryComponent (spEnd x) (h : K[X]) →ₗ[AdjoinRoot (h : K[X])]
            primaryComponent (spEnd x) (h : K[X])) z₂ : primaryComponent (spEnd x) (h : K[X])) :
              Fin r ⊕ Fin r → K) := rfl
    rw [h5, hγz, Submodule.coe_add]

theorem mem_spUniSpan {x g : StatedSp r K} (hxA : x ∈ Ahat) (hx1 : x ≠ 1) (hg : g * x = x * g)
    (hgr : g ^ ringChar K = 1) : g ∈ spUniSpan Ahat :=
  Subgroup.subset_closure ⟨x, hxA, hx1, hg, hgr⟩

theorem transCenter_of_mem_summand_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (i : Option {M : Subgroup ↥Ahat // Nat.card M = p}) {c : Fin r ⊕ Fin r → K}
    (hc : c ∈ spInnerSummand p Ahat i) : TransCenter (spUniSpan Ahat) c := by
  rcases i with _ | ⟨M, hM⟩
  · obtain ⟨a, ha⟩ := spPlane_exists_ne_one S
    refine transCenter_uni_of_fixed a.2 (fun h => ha (Subtype.ext h)) ?_
    exact mem_fixSub.mp hc a (Subgroup.mem_top a)
  · obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
    have hker := (D.ker_eq M hM t htM ht1).1
    have hc' : c ∈ spLineFix M := (inf_le_left : spLineSpace M ≤ spLineFix M) hc
    rw [← hker] at hc'
    exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hc')

theorem transCenter_add_of_mem_summands_uni (S : SpPlaneSetup ℓ f p r K Ahat)
    (D : SpPlaneDecomp p Ahat) {M : Subgroup ↥Ahat} (hM : Nat.card M = p) {y y' : Fin r ⊕ Fin r → K}
    (hy : y ∈ spPlaneFix Ahat) (hy' : y' ∈ spLineSpace M) :
    TransCenter (spUniSpan Ahat) (y + y') := by
  obtain ⟨t, htM, ht1⟩ := spPlane_exists_ne_one_of_card S hM
  have hker := D.ker_eq M hM t htM ht1
  have hmem : y + y' ∈ spLineFix M := by
    rw [hker.2]
    exact Submodule.add_mem_sup hy hy'
  rw [← hker.1] at hmem
  exact transCenter_uni_of_fixed t.2 (fun h => ht1 (Subtype.ext h)) (mem_ker_sub_one_iff.mp hmem)

theorem exists_mixed_transCenter_five_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat)
    (hℓ2 : ℓ ≠ 2) {L N : Subgroup ↥Ahat} (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hVL : spLineSpace L ≠ ⊥) (hVN : spLineSpace N ≠ ⊥) :
    ∃ u ∈ spLineSpace L, ∃ w ∈ spLineSpace N, u ≠ 0 ∧ w ≠ 0 ∧
      TransCenter (spUniSpan Ahat) (u + w) := by
  classical
  obtain ⟨x, hxA, hx1, h, hmem, hh1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    S.exists_mixing_factor D hL hN hLN hVL hVN
  have hpureN : ∀ c ∈ spLineSpace N, TransCenter (spUniSpan Ahat) c := fun c hc =>
    transCenter_of_mem_summand_uni S D (some ⟨N, hN⟩) hc
  by_cases hself : reciprocalPolynomial h = h
  · obtain ⟨g, hg, hgr, w₀, hw₀N, hw₀0, u', hu'L, w', hw'N, hu'0, hw'0, hgw⟩ :=
      exists_mixing_element_of_selfDual_sp_uni S D hℓ2 hL hN hLN hxA hx1 (h := ⟨h, hmem⟩) hh1 hself
        hvL hvh hv0 hwN hwh hw0
    refine ⟨u', hu'L, w', hw'N, hu'0, hw'0, ?_⟩
    rw [← hgw]
    exact (hpureN w₀ hw₀N).map (mem_spUniSpan hxA hx1 hg hgr)
  · have hne : h ≠ reciprocalPolynomial h := fun h' => hself h'.symm
    have hstabL : ∀ s ∈ spLineSpace L, spEnd x s ∈ spLineSpace L := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have hstabN : ∀ s ∈ spLineSpace N, spEnd x s ∈ spLineSpace N := fun s hs =>
      S.spLineSpace_stable ⟨x, hxA⟩ hs
    have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hmem⟩
    have hind := CFSG.RankThree.PartOne.KCUnitaryMixing.linearIndependent_pair_of_disjoint hstabL
      hstabN (D.disjoint_lineSpace hL hN hLN) hvL hwN hvh hwh hv0 hw0
    obtain ⟨g, hg, hgr, hgw⟩ :=
      exists_mixing_element_of_paired_sp_uni S hxA hx1 (h := ⟨h, hmem⟩) hne hvh hwh hind
    refine ⟨v, hvL, w, hwN, hv0, hw0, ?_⟩
    rw [add_comm, ← hgw]
    exact (hpureN w hwN).map (mem_spUniSpan hxA hx1 hg hgr)

theorem transCenter_pair_uni (S : SpPlaneSetup ℓ f p r K Ahat) (D : SpPlaneDecomp p Ahat) (hℓ2 : ℓ ≠ 2)
    (i j : Option {M : Subgroup ↥Ahat // Nat.card M = p}) (hij : i ≠ j)
    {y y' : Fin r ⊕ Fin r → K} (hy : y ∈ spInnerSummand p Ahat i)
    (hy' : y' ∈ spInnerSummand p Ahat j) (hy0 : y ≠ 0) (hy'0 : y' ≠ 0) :
    TransCenter (spUniSpan Ahat) (y + y') := by
  rcases i with _ | ⟨L, hL⟩ <;> rcases j with _ | ⟨N, hN⟩
  · exact absurd rfl hij
  · exact transCenter_add_of_mem_summands_uni S D hN hy hy'
  · rw [add_comm]
    exact transCenter_add_of_mem_summands_uni S D hL hy' hy
  · have hLN : L ≠ N := fun h' => hij (by subst h'; rfl)
    have hVL : spLineSpace L ≠ ⊥ := fun h' => hy0 (by
      have : y ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy
      exact (Submodule.mem_bot K).mp this)
    have hVN : spLineSpace N ≠ ⊥ := fun h' => hy'0 (by
      have : y' ∈ (⊥ : Submodule K (Fin r ⊕ Fin r → K)) := h' ▸ hy'
      exact (Submodule.mem_bot K).mp this)
    obtain ⟨u₀, hu₀, w₀, hw₀, hu₀0, hw₀0, hmix⟩ :=
      exists_mixed_transCenter_five_uni S D hℓ2 hL hN hLN hVL hVN
    have hne : (some ⟨L, hL⟩ : Option {M : Subgroup ↥Ahat // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
      fun h' => hLN (congrArg Subtype.val (Option.some.inj h'))
    have horth : ∀ a ∈ spLineSpace L, ∀ b ∈ spLineSpace N, spForm r K a b = 0 :=
      fun a ha b hb => D.orth _ _ hne a ha b hb
    have horth' : ∀ b ∈ spLineSpace N, ∀ a ∈ spLineSpace L, spForm r K b a = 0 :=
      fun b hb a ha => by rw [← spForm_isAlt.neg_eq, horth a ha b hb, neg_zero]
    obtain ⟨g₁, hg₁, hg₁u, hg₁fix⟩ := exists_mem_fixing_eq (U := spLineSpace L)
      (D.nondeg (some ⟨L, hL⟩)) (fun c hc => transCenter_of_mem_summand_uni S D (some ⟨L, hL⟩) hc)
      hu₀ hy hu₀0 hy0
    obtain ⟨g₂, hg₂, hg₂w, hg₂fix⟩ := exists_mem_fixing_eq (U := spLineSpace N)
      (D.nondeg (some ⟨N, hN⟩)) (fun c hc => transCenter_of_mem_summand_uni S D (some ⟨N, hN⟩) hc)
      hw₀ hy' hw₀0 hy'0
    have h2 : spEnd g₂ u₀ = u₀ := hg₂fix u₀ (fun c hc => horth u₀ hu₀ c hc)
    have h1 : spEnd g₁ y' = y' := hg₁fix y' (fun c hc => horth' y' hy' c hc)
    have := hmix.map ((spUniSpan Ahat).mul_mem hg₁ hg₂)
    rwa [spEnd_mul, Module.End.mul_apply, map_add, h2, hg₂w, map_add, hg₁u, h1] at this

theorem uniClosure_spPlane_five (S : SpPlaneSetup ℓ f p r K Ahat) (hℓ2 : ℓ ≠ 2) :
    spUniSpan Ahat = ⊤ := by
  classical
  have D := S.decomp
  exact eq_top_of_transCenter (transCenter_of_pairs (Vs := spInnerSummand p Ahat)
    D.internal.submodule_iSup_eq_top D.orth D.nondeg
    (fun i c hc => transCenter_of_mem_summand_uni S D i hc)
    (fun i j hij y hy y' hy' hy0 hy'0 => transCenter_pair_uni S D hℓ2 i j hij hy hy' hy0 hy'0))

end SpPlaneFive

section SpCatFive

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCSpFull
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)


theorem uniPlaneGen_inner_sp_five {d : TauCeti.ValidLieTypeIndex} {r ℓ f p : ℕ} {K : Type}
    [Field K] (e : Cat d ≃* StatedProj (StatedSp r K)) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hr : 2 ≤ r)
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hinner : InnerPlane d p E) : UniPlaneGen ℓ E := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have hrq : ¬ (r = 2 ∧ ℓ ^ f = 2) := fun h => hℓ2 ((Nat.Prime.pow_eq_iff Nat.prime_two).1 h.2).1
  have hsimpleP : IsSimpleGroup (StatedProj (StatedSp r K)) :=
    isSimpleGroup_statedProj_statedSp_of_two_le hr fun h => hrq ⟨h.1, by rw [← hK]; exact h.2⟩
  have : IsSimpleGroup (Cat d) := MulEquiv.isSimpleGroup e
  have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat d)
    (range_conj_ne_bot_of_inner hp hc hinner)
  have hchar : ringChar K = ℓ := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hℓ hf hK
  rw [← hchar]
  refine uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  refine uniClosure_of_lift (proj r K)
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r) (K := K))
    ?_ E₁ (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := r) (K := K) (by omega) hp (by omega : p ≠ 2)
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl p))
  · intro E' hc' he' hcd'
    have : CFSG.IsElementaryAbelian p E' :=
      { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hc' a a.2 b b.2)⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (he' x x.2) }
    exact uniClosure_spPlane_five ⟨hℓ, hf, hK, hp, by omega, hpℓ, hr, hrq, this,
      hcd'.trans hcard₁⟩ hℓ2

theorem uniSeitzPlanes_symplectic_five :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ 5 ≤ p ∧ IsSymplecticIndex d.1 ∧
      d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, hsp, hch⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hsp with ⟨q, rfl⟩ | ⟨n, q, rfl, -, hq2⟩ | ⟨n, q, rfl⟩
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have h := uniPlaneGen_inner_sp_five (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      q.prime_p (by simpa using hch) q.exponent_pos
      (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hp hp5 hq le_rfl hE hc hinner
    simpa using h
  ·
    exact absurd (by simpa using hq2) hch
  ·
    have hq : p ≠ q.p := by simpa using hpd
    have hn3 : 3 ≤ n := hrange.1
    have h := uniPlaneGen_inner_sp_five (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj n q hv)
      q.prime_p (by simpa using hch) q.exponent_pos (card_fixedField_C n q hv) hp hp5 hq (by omega)
      hE hc hinner
    simpa using h

end SpCatFive

section TvUni

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem tv_pow_smul (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) (m : ℕ) (v : Fin n → K) :
    (tv hσ ha hc ^ m) • v = v + ((m : K) * c * herm σ a v) • a := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, mul_smul, tv_smul, ih]
    simp only [herm_add_right, herm_smul_right, ha, mul_zero, add_zero]
    push_cast
    module

theorem tv_pow_ringChar (hσ : ∀ c, σ (σ c) = c) {a : Fin n → K} (ha : herm σ a a = 0) {c : K}
    (hc : c + σ c = 0) : tv hσ ha hc ^ ringChar K = 1 := by
  apply ext_smul σ
  intro v
  rw [tv_pow_smul, ringChar.Nat.cast_ringChar, zero_mul, zero_mul, zero_smul, add_zero, one_smul]

theorem isCenter_of_fixed_uni (hσ : ∀ c, σ (σ c) = c) {H : Subgroup (SUid σ n)} {y : SUid σ n}
    (hH : ∀ g : SUid σ n, g * y = y * g → g ^ ringChar K = 1 → g ∈ H) {v : Fin n → K}
    (hv : herm σ v v = 0) (hyv : y • v = v) : CFSG.LieType.SeitzGeneration.Centers.IsCenter H v := by
  refine ⟨hv, fun c hc => ⟨tv hσ hv hc, hH _ ?_ (tv_pow_ringChar hσ hv hc), tv_smul hσ hv hc⟩⟩
  apply ext_smul σ
  intro u
  have h1 : herm σ v (y • u) = herm σ v u := by
    have := herm_smul_smul σ y v u
    rwa [hyv] at this
  rw [mul_smul, mul_smul, tv_smul, tv_smul, smul_add, smul_comm y (c * herm σ v u) v, hyv, h1]

end TvUni

section NonsplitCore

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.LieType.SeitzGeneration.Nonsplit
open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryExact CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryMixing CFSG.RankThree.PartOne.KCPrimary Polynomial

variable {ℓ f p n : ℕ} {K : Type} [Field K] [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem mem_closure_uni (hU : UnitaryFieldData ℓ f K) (hp5 : 5 ≤ p)
    (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    {Ahat : Subgroup (gramSU hU (idGram K n))} (S : PlaneSetup hU n p Ahat)
    (g : GL (Fin n) K) (hg : g ∈ gramSU hU (idGram K n)) :
    g ∈ Subgroup.closure {g : GL (Fin n) K | g ∈ gramSU hU (idGram K n) ∧
      (∃ x : gramSU hU (idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
        g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g) ∧ g ^ ringChar K = 1} := by
  classical
  have hℓ := hU.prime
  have hf := hU.one_le
  set σ := unitaryInvolution K ℓ f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution hU
  have hSG : SUid σ n = gramSU hU (idGram K n) := by
    rw [hσdef, SUid_eq_statedSU hU.card_eq_sq n]
    exact (unitarySU_eq_gramSU hU n)
  have he3 : 3 ≤ ordNegQ ℓ f p := three_le_ordNegQ S.prime hp5 hℓ S.ne_char hf hpq1 hpq
  have hdec := planeKernelDecomposition (h := hU) S.prime S.ne_char S.elem S.card
  have : Finite ↥Ahat := inferInstance
  have : Fintype ↥Ahat := Fintype.ofFinite _
  set ρ := planeRep hU n Ahat with hρdef
  set B := idForm hU n with hBdef
  set 𝒞 : Set (GL (Fin n) K) := {g | g ∈ gramSU hU (idGram K n) ∧
    (∃ x : gramSU hU (idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
      g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g) ∧ g ^ ringChar K = 1} with h𝒞
  set Hgl : Subgroup (GL (Fin n) K) := Subgroup.closure 𝒞 with hHgl
  let H : Subgroup (SUid σ n) := Hgl.comap (SUid σ n).subtype
  have hHmem : ∀ (gS : SUid σ n) (x : gramSU hU (idGram K n)), x ∈ Ahat → x ≠ 1 →
      (gS : GL (Fin n) K) * (x : GL (Fin n) K) = (x : GL (Fin n) K) * gS → gS ^ ringChar K = 1 →
        gS ∈ H := by
    intro gS x hx hx1 hcomm hgr
    have hgS : (gS : GL (Fin n) K) ∈ gramSU hU (idGram K n) := hSG ▸ gS.2
    exact Subgroup.subset_closure ⟨hgS, ⟨x, hx, hx1, hcomm⟩, by rw [← map_pow, hgr, map_one]⟩
  have hexL : ∀ L : Subgroup ↥Ahat, Nat.card L = p → ∃ t : ↥Ahat, t ∈ L ∧ t ≠ 1 := by
    intro N hN
    have h1 : Nontrivial ↥N :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hN]; exact S.prime.one_lt)
    obtain ⟨t, ht⟩ := exists_ne (1 : ↥N)
    exact ⟨t, t.2, fun h' => ht (Subtype.ext h')⟩
  let toS : ↥Ahat → SUid σ n := fun t =>
    ⟨((t.1 : gramSU hU (idGram K n)) : GL (Fin n) K), by rw [hSG]; exact t.1.2⟩
  have hact : ∀ (t : ↥Ahat) (v : Fin n → K), act ρ t v = toS t • v := fun t v => by
    rw [smul_def σ (toS t) v]
    simp [act, hρdef, planeRep, toLinU, toUnitary, toS]
    rfl
  have hAll : ∀ L : Subgroup ↥Ahat, Nat.card L = p →
      Centers.AllCenters H (fixedSpace ρ ⊤ ⊔ lineSpace ρ B L) := by
    intro L hL v hv hvi
    obtain ⟨t, htL, ht1⟩ := hexL L hL
    have hker := hdec.ker_eq L hL t htL ht1
    have hv' : v ∈ LinearMap.ker (act ρ t - 1) := hker ▸ hv
    have hfix : toS t • v = v := by
      rw [← hact]
      simpa [sub_eq_zero] using hv'
    refine isCenter_of_fixed_uni hσ.invol (fun g hg hgr => hHmem g t.1 t.2
      (fun h => ht1 (Subtype.ext h)) ?_ hgr) hvi hfix
    have := congrArg (fun z : SUid σ n => (z : GL (Fin n) K)) hg
    simpa [toS] using this
  have hfin : ∀ L : Subgroup ↥Ahat, Nat.card L = p → lineSpace ρ B L ≠ ⊥ →
      ordNegQ ℓ f p ≤ Module.finrank K (lineSpace ρ B L) := by
    intro L hL hV
    have hdvd := hdec.dvd_finrank L hL
    have hpos : 1 ≤ Module.finrank K (lineSpace ρ B L) := Submodule.one_le_finrank_iff.mpr hV
    exact Nat.le_of_dvd hpos hdvd
  have hdimOK : ∀ L : Subgroup ↥Ahat, Nat.card L = p → lineSpace ρ B L ≠ ⊥ →
      (4 ≤ Module.finrank K (lineSpace ρ B L) ∨ (3 ≤ Module.finrank K (lineSpace ρ B L) ∧
        ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1)) := by
    intro L hL hV
    have hle := hfin L hL hV
    by_cases hq : ℓ ^ f = 2
    · left
      have := four_le_ordNegQ_of_two S.prime (by omega : 3 < p) S.ne_char hℓ hq
      omega
    · right
      refine ⟨by omega, ?_⟩
      obtain ⟨s, hs0, hs⟩ := exists_norm_ne_one hU hq
      refine ⟨s, hs0, ?_⟩
      rw [hσdef, unitaryInvolution_eq_bar hU]
      exact hs
  have hBsymm : B.IsSymm := idForm_isSymm hU n
  obtain ⟨L₁, M₁, hL₁, hM₁, hL₁M₁, hVL₁, hVM₁⟩ := hdec.exists_two_active
  let ι := {L : Subgroup ↥Ahat // Nat.card L = p ∧ lineSpace ρ B L ≠ ⊥}
  let i₁ : ι := ⟨L₁, hL₁, hVL₁⟩
  let Z : ι → Submodule K (Fin n → K) := fun i => if i = i₁ then fixedSpace ρ ⊤ else ⊥
  let W : ι → Submodule K (Fin n → K) := fun i => lineSpace ρ B i.1 ⊔ Z i
  have hZV : ∀ i, Z i ≤ fixedSpace ρ ⊤ := fun i => by
    simp only [Z]
    split_ifs
    · exact le_rfl
    · exact bot_le
  have hZdisj : ∀ i j : ι, i ≠ j → Z i = ⊥ ∨ Z j = ⊥ := fun i j hij => by
    by_cases hi : i = i₁
    · right
      have hj : j ≠ i₁ := fun hj => hij (hi.trans hj.symm)
      simp [Z, hj]
    · left
      simp [Z, hi]
  have hWle : ∀ i : ι, W i ≤ fixedSpace ρ ⊤ ⊔ lineSpace ρ B i.1 := fun i =>
    sup_le le_sup_right (le_sup_of_le_left (hZV i))
  have hA : ∀ i : ι, Centers.AllCenters H (W i) := fun i v hv hvi =>
    hAll i.1 i.2.1 v (hWle i hv) hvi
  have hON : ∀ i : ι, Centers.HasONBasis σ (W i) := by
    intro i
    by_cases hi : i = i₁
    · have hZi : Z i = fixedSpace ρ ⊤ := by simp [Z, hi]
      have hsep : (B.domRestrict₁₂ (W i) (W i)).SeparatingLeft := by
        refine separatingLeft_sup hBsymm (hdec.nondegenerate_line i.1 i.2.1) ?_ ?_
        · rw [hZi]
          exact hdec.nondegenerate_fixed
        · intro u hu v hv
          rw [hZi] at hv
          rw [← hBsymm.eq v u, hdec.orthogonal_fixed_line i.1 i.2.1 v hv u hu, map_zero]
      have hle : Module.finrank K (lineSpace ρ B i.1) ≤ Module.finrank K (W i) :=
        Submodule.finrank_mono le_sup_left
      refine hasONBasis_of_separatingLeft hU (W i) hsep ?_
      rcases hdimOK i.1 i.2.1 i.2.2 with h | ⟨h, hs⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hs⟩
    · have hZi : Z i = ⊥ := by simp [Z, hi]
      have hWi : W i = lineSpace ρ B i.1 := by simp [W, hZi]
      rw [hWi]
      exact hasONBasis_of_separatingLeft hU _ (hdec.nondegenerate_line i.1 i.2.1)
        (hdimOK i.1 i.2.1 i.2.2)
  have horthB : ∀ i j : ι, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, B u v = 0 := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hVV := hdec.orthogonal_line_line i.1 j.1 i.2.1 j.2.1 hne
    refine forall_sup_sup hVV ?_ ?_ ?_
    · intro x hx y hy
      have hy' := hZV j hy
      rw [← hBsymm.eq y x, hdec.orthogonal_fixed_line i.1 i.2.1 y hy' x hx, map_zero]
    · intro x hx y hy
      exact hdec.orthogonal_fixed_line j.1 j.2.1 x (hZV i hx) y hy
    · intro x hx y hy
      rcases hZdisj i j hij with h | h
      · rw [h] at hx
        rw [(Submodule.mem_bot K).mp hx, map_zero, LinearMap.zero_apply]
      · rw [h] at hy
        rw [(Submodule.mem_bot K).mp hy, map_zero]
  have horth : ∀ i j : ι, i ≠ j → ∀ u ∈ W i, ∀ v ∈ W j, herm σ u v = 0 :=
    fun i j hij u hu v hv => by
      rw [← idForm_eq_herm hU]
      exact horthB i j hij u hu v hv
  have htop : ⨆ i : ι, W i = ⊤ := by
    refine top_unique ?_
    rw [← hdec.sup_eq_top]
    refine iSup_le fun k => ?_
    rcases k with _ | L
    · exact le_iSup_of_le i₁ (by
        change fixedSpace ρ ⊤ ≤ lineSpace ρ B L₁ ⊔ Z i₁
        have : Z i₁ = fixedSpace ρ ⊤ := by simp [Z]
        rw [this]
        exact le_sup_right)
    · by_cases hV : lineSpace ρ B L.1 = ⊥
      · change lineSpace ρ B L.1 ≤ _
        rw [hV]
        exact bot_le
      · exact le_iSup_of_le ⟨L.1, L.2, hV⟩ le_sup_left
  have hmix : ∀ i j : ι, i ≠ j → ∃ w₁ ∈ W i, ∃ w₂ ∈ W j, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧
      Centers.IsCenter H (w₁ + w₂) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    obtain ⟨x, hxA, hx1, a, ha1, ⟨v, hvL, hva, hv0⟩, ⟨w, hwM, hwa, hw0⟩⟩ :=
      exists_mixing_factor S hdec hpq1 i.2.1 j.2.1 hne i.2.2 j.2.2
    set xabs : LinearMap.GeneralLinearGroup K (Fin n → K) := toLinU hU n (liftUnitary x)
      with hxabs
    have hxmem : xabs ∈ sesqUnitaryGroup B := toLinU_mem _
    have hsq : Squarefree (minpoly K (xabs : Module.End K (Fin n → K))) :=
      (S.planeData hxA).squarefree_minpoly
    have hVMon : Centers.HasONBasis σ (lineSpace ρ B j.1) :=
      hasONBasis_of_separatingLeft hU _ (hdec.nondegenerate_line j.1 j.2.1)
        (hdimOK j.1 j.2.1 j.2.2)
    have hKI : ∀ w ∈ lineSpace ρ B j.1, w ≠ 0 →
        ∃ w₀ ∈ lineSpace ρ B j.1, B w₀ w₀ = 0 ∧ B w w₀ ≠ 0 := by
      intro w hw hw0
      obtain ⟨w₀, hw₀, h1, h2⟩ := exists_isotropic_pairing hσ hVMon hw hw0
      exact ⟨w₀, hw₀, by rw [hBdef, idForm_eq_herm]; exact h1,
        by rw [hBdef, idForm_eq_herm]; exact h2⟩
    have hdeg : dualPoly hU.bar (a.1 : K[X]) = a.1 → 2 ≤ (a.1 : K[X]).natDegree := by
      intro hself
      have hfd : (a.1 : K[X]) ∣ X ^ p - 1 := primaryFactor_dvd_pow_sub_one S ⟨x, hxA⟩ a.1.2
      have hfmon := monic_of_mem_primaryFactors a.1.2
      have hne1 := natDegree_ne_one_of_selfDual (h := hU) S.prime hpq1 hfmon hfd ha1 hself
      have hpos : 0 < (a.1 : K[X]).natDegree :=
        (irreducible_of_mem_primaryFactors a.1.2).natDegree_pos
      omega
    obtain ⟨g, hg, hgdet, hgr, w₀, hw₀, hw₀0, hw₀i, u'', hu'', w'', hw'', hu''0, hw''0, hgw⟩ :=
      exists_mixing_element_uni (a := a.1) hBsymm (idForm_separatingLeft hU n) hxmem hsq hdeg
        (fun s hs => lineSpace_stable S ⟨x, hxA⟩ hs) (fun s hs => lineSpace_stable S ⟨x, hxA⟩ hs)
        (disjoint_lineSpace hdec i.2.1 j.2.1 hne)
        (hdec.orthogonal_line_line i.1 j.1 i.2.1 j.2.1 hne) (hdec.nondegenerate_line i.1 i.2.1)
        (hdec.nondegenerate_line j.1 j.2.1) hKI hvL hva hv0 hwM hwa hw0
    have hgsesq := (mem_unitaryCentralizer.mp hg).1
    have hgcomm := (mem_unitaryCentralizer.mp hg).2
    obtain ⟨gS, hgS, hgSr⟩ : ∃ gS : SUid σ n, (∀ v, gS • v = (g : Module.End K (Fin n → K)) v) ∧
        gS ^ ringChar K = 1 := by
      let gm : GL (Fin n) K := Matrix.GeneralLinearGroup.toLin.symm g
      have hgm : ∀ v, (gm : Matrix (Fin n) (Fin n) K) *ᵥ v = (g : Module.End K (Fin n → K)) v := by
        intro v
        have h1 : (Matrix.GeneralLinearGroup.toLin gm : LinearMap.GeneralLinearGroup K (Fin n → K))
            = g := MulEquiv.apply_symm_apply _ g
        have h2 := congrArg (fun φ : LinearMap.GeneralLinearGroup K (Fin n → K) =>
          (φ : Module.End K (Fin n → K)) v) h1
        simpa [Matrix.GeneralLinearGroup.coe_toLin, Matrix.toLin'_apply] using h2
      have heq : (g : Module.End K (Fin n → K)) = Matrix.toLin' (gm : Matrix (Fin n) (Fin n) K) :=
        LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hgm]
      refine ⟨⟨gm, (mem_SUid_iff σ).mpr ⟨?_, fun v w => ?_⟩⟩, fun v => hgm v, ?_⟩
      · rw [← LinearMap.det_toLin', ← heq]
        exact hgdet
      · rw [hgm, hgm, ← idForm_eq_herm hU, ← idForm_eq_herm hU]
        exact hgsesq v w
      · apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        show (Matrix.GeneralLinearGroup.toLin.symm g) ^ ringChar K = 1
        rw [← map_pow, hgr, map_one]
    have hcommS : gS * toS ⟨x, hxA⟩ = toS ⟨x, hxA⟩ * gS := by
      refine ext_smul σ fun v => ?_
      rw [mul_smul, mul_smul, ← hact, ← hact, hgS, hgS]
      exact LinearMap.congr_fun hgcomm.eq v
    have hgH : gS ∈ H := hHmem gS x hxA hx1 (by
      have := congrArg (fun z : SUid σ n => (z : GL (Fin n) K)) hcommS
      simpa [toS] using this) hgSr
    have hCw₀ : Centers.IsCenter H w₀ := hAll j.1 j.2.1 w₀ (Submodule.mem_sup_right hw₀)
      (by rw [← idForm_eq_herm hU]; exact hw₀i)
    have hCg := hCw₀.map hgH
    rw [hgS, hgw] at hCg
    exact ⟨u'', (le_sup_left : lineSpace ρ B i.1 ≤ W i) hu'', w'',
      (le_sup_left : lineSpace ρ B j.1 ≤ W j) hw'', hu''0, hw''0, hCg⟩
  have hn4 : 4 ≤ n := by
    have hdisj := disjoint_lineSpace hdec hL₁ hM₁ hL₁M₁
    have h1 := hfin L₁ hL₁ hVL₁
    have h2 := hfin M₁ hM₁ hVM₁
    have h3 := Submodule.finrank_sup_add_finrank_inf_eq (lineSpace ρ B L₁) (lineSpace ρ B M₁)
    rw [hdisj.eq_bot, finrank_bot] at h3
    have h4 := Submodule.finrank_le (lineSpace ρ B L₁ ⊔ lineSpace ρ B M₁)
    rw [Module.finrank_fin_fun] at h4
    omega
  have : Finite ι := Subtype.finite
  have : Fintype ι := Fintype.ofFinite ι
  have : Nonempty ι := ⟨i₁⟩
  have hHtop : H = ⊤ := Centers.eq_top_of_blocks hσ hn4 W hON horth hA hmix htop
  have hmem : (⟨g, by rw [hSG]; exact hg⟩ : SUid σ n) ∈ H := hHtop ▸ Subgroup.mem_top _
  exact hmem



end NonsplitCore

section NonsplitWrap

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.LieType.SeitzGeneration.Nonsplit

theorem uniClosure_unitarySU_nonsplit {ℓ f p n : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hpq1 : ¬ p ∣ ℓ ^ f + 1) (hpq : ¬ p ∣ ℓ ^ f - 1)
    (hn : 3 ≤ n) (E : Subgroup (unitarySU ℓ f K n)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {g : unitarySU ℓ f K n |
      ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1} = ⊤ := by
  classical
  have := hU.finite
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have : CharP K ℓ := hU.charP
  have hGG : unitarySU ℓ f K n = CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) := unitarySU_eq_gramSU hU n
  have hinj : Function.Injective (Subgroup.inclusion hGG.le) := Subgroup.inclusion_injective hGG.le
  let Ahat : Subgroup (CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n)) := E.map (Subgroup.inclusion hGG.le)
  have hAmem : ∀ x : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n), x ∈ Ahat ↔
      ∃ e ∈ E, Subgroup.inclusion hGG.le e = x := fun x => Subgroup.mem_map
  have hAcard : Nat.card Ahat = p ^ 2 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective hinj
  have hAel : CFSG.IsElementaryAbelian p Ahat := by
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p Ahat).mpr
      ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨e₁, he₁, h₁⟩ := (hAmem a.1).mp a.2
      obtain ⟨e₂, he₂, h₂⟩ := (hAmem b.1).mp b.2
      refine Subtype.ext ?_
      change a.1 * b.1 = b.1 * a.1
      rw [← h₁, ← h₂, ← map_mul, ← map_mul, hcomm e₁ he₁ e₂ he₂]
    · obtain ⟨e, he, h1⟩ := (hAmem x).mp hx
      rw [← h1, ← map_pow, hexp e he, map_one]
  have h2e : 2 * ordNegQ ℓ f p ≤ n := CFSG.RankThree.PartOne.CTP.two_mul_ordNegQ_le hU hp hpℓ E
    hexp hcard
  have he3 : 3 ≤ ordNegQ ℓ f p := three_le_ordNegQ hp hp5 hU.prime hpℓ hU.one_le hpq1 hpq
  have hS : CFSG.RankThree.PartOne.KCUnitaryExact.PlaneSetup hU n p Ahat :=
    { three_le := hn
      ne := fun h => by omega
      prime := hp
      ne_char := hpℓ
      noTorsion := fun c hc _ hcp => by
        have h1 : (c : K) ^ (ℓ ^ f + 1) = 1 := by rw [← hU.norm_eq_pow]; exact hc
        have h2 : c ^ (ℓ ^ f + 1) = 1 := Units.ext (by simpa using h1)
        have hgcd : Nat.gcd p (ℓ ^ f + 1) = 1 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpq1
        have h3 : c ^ Nat.gcd p (ℓ ^ f + 1) = 1 := pow_gcd_eq_one.mpr ⟨hcp, h2⟩
        rwa [hgcd, pow_one] at h3
      elem := hAel
      card := hAcard }
  rw [eq_top_iff]
  intro g _
  have hgmem : (g : GL (Fin n) K) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) := hGG ▸ g.2
  have hmain := mem_closure_uni hU hp5 hpq1 hpq hS (g : GL (Fin n) K) hgmem
  let S₀ : Set (unitarySU ℓ f K n) := {g | ∃ x ∈ E, x ≠ 1 ∧ g * x = x * g ∧ g ^ ringChar K = 1}
  have himg : (unitarySU ℓ f K n).subtype '' S₀ = {g : GL (Fin n) K |
      g ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ∧
      (∃ x : CFSG.ClassicalGroups.UnitaryFlag.gramSU hU
        (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n), x ∈ Ahat ∧ x ≠ 1 ∧
        g * (x : GL (Fin n) K) = (x : GL (Fin n) K) * g) ∧ g ^ ringChar K = 1} := by
    ext g'
    constructor
    · rintro ⟨g₀, ⟨x, hx, hx1, hcomm', hg₀r⟩, rfl⟩
      refine ⟨hGG ▸ g₀.2, ⟨Subgroup.inclusion hGG.le x, (hAmem _).mpr ⟨x, hx, rfl⟩,
        fun h => hx1 (hinj (by rw [h, map_one])), ?_⟩, ?_⟩
      · have := congrArg (fun z : unitarySU ℓ f K n => (z : GL (Fin n) K)) hcomm'
        simpa using this
      · rw [Subgroup.coe_subtype, ← SubgroupClass.coe_pow, hg₀r, OneMemClass.coe_one]
    · rintro ⟨hg', ⟨x', hx', hx'1, hcomm'⟩, hg'r⟩
      obtain ⟨x, hx, rfl⟩ := (hAmem x').mp hx'
      refine ⟨⟨g', hGG ▸ hg'⟩, ⟨x, hx, fun h => hx'1 (by rw [h, map_one]), Subtype.ext ?_, ?_⟩,
        rfl⟩
      · simpa using hcomm'
      · apply Subtype.ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hg'r
  rw [← himg, ← MonoidHom.map_closure] at hmain
  obtain ⟨y, hy, hyg⟩ := hmain
  have hyg' : y = g := Subtype.ext hyg
  rw [← hyg']
  exact hy



end NonsplitWrap

section UnitaryInnerAll

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem uniSeitzPlanes_unitary_inner_all :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧
      d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hinner, ⟨m, q, hd⟩, hlift, hq2⟩
  subst hd
  have hq2' : q.p ≠ 2 := by simpa using hq2
  have hpq : p ≠ q.p := by simpa using hpd
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA m q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA m q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA m q, hv⟩)
  have hℓq : ℓ = q.p := by simp [hℓ, TauCeti.ValidLieTypeIndex.characteristic]
  have hqcard : ℓ ^ f = q.card := by
    simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent,
      TauCeti.PrimePower.card_def]
  have hq : ℓ ^ f ≠ 2 := by
    rw [hqcard]
    intro h2
    have hdvd : q.p ∣ q.card := by
      rw [TauCeti.PrimePower.card_def]
      exact dvd_pow_self _ q.exponent_pos.ne'
    rw [h2] at hdvd
    exact hq2' ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd)
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm2 : 2 ≤ m := hrange.1
  have hSU : ∀ E' : Subgroup (unitarySU ℓ f (GaloisField ℓ (2 * f)) (m + 1)),
      (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) → (∀ x ∈ E', x ^ p = 1) → Nat.card E' = p ^ 2 →
        Subgroup.closure {g | ∃ x ∈ E', x ≠ 1 ∧ g * x = x * g ∧
          g ^ ringChar (GaloisField ℓ (2 * f)) = 1} = ⊤ := by
    intro E' hcomm hexp hcard
    by_cases h1 : p ∣ ℓ ^ f + 1
    · exact uniClosure_unitarySU_of_dvd_add_one hU hp h1 hq E' hcomm hexp hcard
    by_cases h2 : p ∣ ℓ ^ f - 1
    · exact uniClosure_unitarySU_split hU (by rw [hℓq]; exact hq2') hp hp2 h2 (by omega) E' hcomm
        hexp hcard
    ·
      have hp5 : 5 ≤ p := by
        have hp3 : p ≠ 3 := by
          rintro rfl
          have hℓ3 : ¬ 3 ∣ ℓ ^ f := fun h => hpq (by
            rw [← hℓq]
            exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hU.prime).1
              (Nat.prime_three.dvd_of_dvd_pow h)))
          have hpos : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hU.prime.pos
          have : ℓ ^ f % 3 = 1 ∨ ℓ ^ f % 3 = 2 := by omega
          rcases this with h | h
          · exact h2 (by omega)
          · exact h1 (by omega)
        have := hp.two_le
        rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      exact uniClosure_unitarySU_nonsplit hU hp hp5 (by rw [hℓq]; exact hpq) h1 h2 (by omega) E'
        hcomm hexp hcard
  have h := uniPlaneGen_inner_unitary hv hp hlift hSU hE hc hinner
  simpa using h

end UnitaryInnerAll

section UnitaryOuter

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.ClassicalInvolution.Phan

theorem closure_pow_ringChar_gramSU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (hq : ℓ ^ f ≠ 2) (n : ℕ) :
    Subgroup.closure {g : gramSU h ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) |
      g ^ ringChar K = 1} = ⊤ := by
  have hfin := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have : CharP K ℓ := h.charP
  let ε : Su K ℓ f (n + 1) ≃*
      gramSU h ((1 : GL (Fin (n + 1)) K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :=
    MulEquiv.subgroupCongr ((CFSG.LieType.Universal.Unitary.SUid_eq_statedSU h.card_eq_sq (n + 1)).trans
      (unitarySU_eq_gramSU h (n + 1)))
  have h1 := iSup_range_blockEmb2 (K := K) (p := ℓ) (f := f) h.card_eq_sq hq n
  have hsu2 := closure_pow_ringChar_su_two (K := K) (p := ℓ) (f := f) h.card_eq_sq
  have h2 := congrArg (Subgroup.map ε.toMonoidHom) h1
  rw [Subgroup.map_iSup, Subgroup.map_top_of_surjective _ ε.surjective] at h2
  rw [eq_top_iff, ← h2]
  refine iSup_le fun i => ?_
  rw [MonoidHom.range_eq_map, ← hsu2, Subgroup.map_map, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Subgroup.subset_closure
  show (ε.toMonoidHom.comp (blockEmb2 K ℓ f n i)) a ^ ringChar K = 1
  rw [← map_pow]
  rw [show a ^ ringChar K = 1 from ha, map_one]

theorem fixedSubgroup_primeFormFieldHom_le_closure {ℓ f p n : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K} (hσ : orderOf σ = p)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n))
    (hq₀ : ℓ ^ (f / p) ≠ 2) :
    fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ) ≤
      Subgroup.closure {x | primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ x = x ∧
        x ^ ringChar K = 1} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, -, -, -, -, -, hrange, -⟩ :=
    prime_subfield_fixed_group_package h hp hp2 hσ (m + 1) hn hne hZ
  have h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  have hFeq : fixedSubgroup (primeFormFieldHom h (isPrimeFormGram_one (n := m + 1)) σ) =
      fieldFixedPSU h (m + 1) σ :=
    Subgroup.ext fun _ => Iff.rfl
  have hchar : ringChar (fixSubfield σ) = ringChar K := by
    have : CharP (fixSubfield σ) (ringChar K) := inferInstance
    exact ringChar.eq _ _
  let ψ := (QuotientGroup.mk' (normOneScalars h (gramSU h
    ((1 : GL (Fin (m + 1)) K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K)) (m + 1))).comp
      (subfieldSU h h₀ hbar (m + 1))
  have hψ : ψ.range = fieldFixedPSU h (m + 1) σ := by
    rw [← hrange, range_subfieldPSU_eq_map, MonoidHom.range_comp]
    rfl
  have hgen := closure_pow_ringChar_gramSU h₀ hq₀ m
  rw [hFeq, ← hψ]
  rintro _ ⟨g, rfl⟩
  have hg : g ∈ Subgroup.closure {g : gramSU h₀ ((1 : GL (Fin (m + 1)) (fixSubfield σ)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (fixSubfield σ)) | g ^ ringChar (fixSubfield σ) = 1} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have h1 := Subgroup.mem_map_of_mem ψ hg
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨s, hs, rfl⟩
  have hmem : ψ s ∈ fieldFixedPSU h (m + 1) σ := hψ ▸ ⟨s, rfl⟩
  refine ⟨hmem, ?_⟩
  rw [← map_pow, ← hchar]
  rw [show s ^ ringChar (fixSubfield σ) = 1 from hs, map_one]

theorem uniPlaneGen_outer_su_model {d : TauCeti.ValidLieTypeIndex}
    {n ℓ f p : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K)
    (e : Cat d ≃* primeFormP h (idGram K n)) (hn3 : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hg : ¬ p ∣ Nat.gcd n (ℓ ^ f + 1))
    {E : Subgroup (MulAut (Cat d))} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ InnerPlane d p E) : UniPlaneGen ℓ E := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hfin := h.finite
  have : CharP K ℓ := h.charP
  have : IsSimpleGroup (primeFormP h (idGram K n)) := isSimpleGroup_primeFormP_one h hn3 hne
  have hnab : ∃ a b : primeFormP h (idGram K n), a * b ≠ b * a := by
    have hnc := not_commute_primeFormP_one h hn3 hne
    push Not at hnc
    exact hnc
  have hd : FieldAutData (primeFormP h (idGram K n)) p :=
    fieldAutData_primeFormP_odd
      (subfieldPairSUOdd CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds)
      hn3 h hne hp hp2 hpℓ hg
  have hchar : ringChar K = ℓ := ringChar.eq K ℓ
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) n) := by
    rw [card_normOneScalars_one h (by omega)]
    exact hg
  have hℓodd : Odd ℓ := h.prime.odd_of_ne_two hℓ2
  have hq₀ : ℓ ^ (f / p) ≠ 2 := by
    intro h2
    have h3 : Odd (ℓ ^ (f / p)) := hℓodd.pow
    rw [h2] at h3
    exact (by decide : ¬ Odd 2) h3
  have hfix : ∀ α : MulAut (primeFormP h (idGram K n)), IsOuterOfOrder p α →
      fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ℓ = 1} := by
    intro α hα
    obtain ⟨hord, hout'⟩ := hα
    have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
    have hσ1 : primeFormFieldFactor h hC hn3 hne α ≠ 1 := by
      intro h1
      have hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
        rw [← ker_primeFormFieldFactor h hC hn3 hne]
        exact h1
      obtain ⟨g, hgk⟩ := pElement_mem_inner_of_not_dvd_gcd h hn3 hne hp hg hD hαp
      exact hout' g hgk.symm
    have hσp : (primeFormFieldFactor h hC hn3 hne α) ^ p = 1 := by
      rw [← map_pow, hαp, map_one]
    have hσord : orderOf (primeFormFieldFactor h hC hn3 hne α) = p := orderOf_eq_prime hσp hσ1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent h hn3 hne hp hp2 hpℓ
        α hord _ rfl hσord
    have key : fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} :=
      fixedSubgroup_le_closure_of_conj (c := (primeFormConjHom h _ M)⁻¹) (by rw [inv_inv]; exact hM)
        (fixedSubgroup_primeFormFieldHom_le_closure h hp hp2 hσord hn3 hne hZ hq₀)
    rw [hchar] at key
    exact key
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout'' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h'
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h' φ hφ).imp fun g hg => hg.symm
  exact (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_of_fieldAutData hnab hp hd hfix _ hc' hout'')

theorem uniSeitzPlanes_unitary_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧
      d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨m, q, hd⟩, hlift, hch⟩
  subst hd
  obtain ⟨hℓ, hf, hn3, hne, F, _, hU, ⟨θ⟩⟩ :=
    CFSG.RankThree.PartOne.exists_primeFormP_of_statedClassicalModel_PSU
      (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
        (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩)))
  have h := uniPlaneGen_outer_su_model hU θ hn3 hne (by simpa using hch) hp hp2
    (by simpa using hpd) (by
      intro hdv
      apply hlift
      rw [TauCeti.PrimePower.card_def]
      exact ⟨hdv.trans (Nat.gcd_dvd_right _ _), hdv.trans (Nat.gcd_dvd_left _ _)⟩) hE hc hout
  simpa using h

end UnitaryOuter

section OrthUni

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical CFSG.Open
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthNS
  CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)


section Span

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

variable (Q) in
@[expose] def orthUSpan (E : Subgroup (orthDerived Q)) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
    (∃ x ∈ E.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g) ∧ g ^ ringChar K = 1}

theorem orthUSpan_le_orthogonalGroup (E : Subgroup (orthDerived Q)) :
    orthUSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨hg, -⟩
  exact orthDerived_le_orthogonalGroup Q hg

theorem orthUSpan_eq_map (E : Subgroup (orthDerived Q)) :
    orthUSpan Q E =
      (Subgroup.closure {h : orthDerived Q |
        ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1}).map (orthDerived Q).subtype := by
  have hset : (orthDerived Q).subtype '' {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} =
      {g : V ≃ₗ[K] V | g ∈ orthDerived Q ∧
        (∃ x ∈ E.map (orthDerived Q).subtype, x ≠ 1 ∧ g * x = x * g) ∧ g ^ ringChar K = 1} := by
    ext g
    constructor
    · rintro ⟨h, ⟨x, hx, hx1, hhx, hr⟩, rfl⟩
      refine ⟨h.2, ⟨x.1, ⟨x, hx, rfl⟩, fun h' => hx1 (Subtype.ext h'), congrArg Subtype.val hhx⟩,
        ?_⟩
      have := congrArg Subtype.val hr
      simpa using this
    · rintro ⟨hg, ⟨_, ⟨x, hx, rfl⟩, hx1, hgx⟩, hr⟩
      refine ⟨⟨g, hg⟩, ⟨x, hx, fun h => hx1 (congrArg Subtype.val h), Subtype.ext hgx,
        Subtype.ext ?_⟩, rfl⟩
      simpa using hr
  rw [MonoidHom.map_closure, hset]
  rfl

theorem orthU_closure_eq_top_of_le (E : Subgroup (orthDerived Q))
    (h : orthDerived Q ≤ orthUSpan Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  rw [orthUSpan_eq_map] at h
  refine eq_top_iff.2 fun g _ => ?_
  obtain ⟨g', hg', hgg'⟩ := h g.2
  have : g' = g := Subtype.ext hgg'
  exact this ▸ hg'

theorem orthU_eichler_pow_nsmul {u w : V} (hu : Q u = 0) (huw : polar Q u w = 0) (n : ℕ) :
    eichler Q u w ^ n = eichler Q u (n • w) := by
  induction n with
  | zero => simp [eichler_zero_right]
  | succ n ih =>
    have hnw : polar Q u (n • w) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, polar_smul_right_eq, huw, mul_zero]
    rw [pow_succ, ih, succ_nsmul, eichler_mul hnw huw]

theorem orthU_eichler_pow_ringChar (u w : V) : eichler Q u w ^ ringChar K = 1 := by
  by_cases hc : Q u = 0 ∧ polar Q u w = 0
  · rw [orthU_eichler_pow_nsmul hc.1 hc.2]
    have : ringChar K • w = 0 := by
      rw [← Nat.cast_smul_eq_nsmul K, ringChar.Nat.cast_ringChar, zero_smul]
    rw [this, eichler_zero_right]
  · rw [eichler_of_not hc, one_pow]

variable {E : Subgroup (orthDerived Q)}

theorem orthU_mem_of_commute {g : V ≃ₗ[K] V} (hg : g ∈ orthDerived Q)
    {a : orthDerived Q} (ha : a ∈ E) (ha1 : a ≠ 1)
    (hc : g * (a : V ≃ₗ[K] V) = (a : V ≃ₗ[K] V) * g) (hr : g ^ ringChar K = 1) :
    g ∈ orthUSpan Q E :=
  Subgroup.subset_closure ⟨hg, ⟨(a : V ≃ₗ[K] V), ⟨a, ha, rfl⟩, fun h => ha1 (Subtype.ext h), hc⟩,
    hr⟩

theorem orthU_eichler_mem_of_fix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {e w : V} {x : orthDerived Q} (hxE : x ∈ E) (hx1 : x ≠ 1)
    (hxe : ((x : orthDerived Q) : V ≃ₗ[K] V) e = e)
    (hxw : ((x : orthDerived Q) : V ≃ₗ[K] V) w = w) :
    eichler Q e w ∈ orthUSpan Q E := by
  refine orthU_mem_of_commute (hEΩ (eichler_mem_elementaryGroup Q e w)) hxE hx1 ?_
    (orthU_eichler_pow_ringChar e w)
  have hconj := eichler_conj (Q := Q) (orthDerived_le_orthogonalGroup Q x.2) e w
  rw [hxe, hxw] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

theorem orthU_eichler_mem_of_lineFix (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    {M : Subgroup E} (hM : M ≠ ⊥) {e w : V} (he : e ∈ lineFixSpace M) (hw : w ∈ lineFixSpace M) :
    eichler Q e w ∈ orthUSpan Q E := by
  obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hM
  have hmem : ((t : E) : orthDerived Q) ∈ E := (t : E).2
  have hfix : ∀ v ∈ lineFixSpace M, (((t : E) : orthDerived Q) : V ≃ₗ[K] V) v = v := by
    intro v hv
    exact (mem_fixSpace.mp hv) _ ⟨((t : E) : orthDerived Q), ⟨(t : E), t.2, rfl⟩, rfl⟩
  refine orthU_eichler_mem_of_fix hEΩ (x := ((t : E) : orthDerived Q)) hmem ?_
    (hfix e he) (hfix w hw)
  intro h1
  exact ht1 (Subtype.ext (Subtype.ext h1))

theorem orthU_eichler_mem_of_mem_sup (hEΩ : elementaryGroup Q ≤ orthDerived Q) {M : Subgroup E}
    (hM : M ≠ ⊥) {e w : V} (he : e ∈ planeFixSpace E ⊔ lineSpace M)
    (hw : w ∈ planeFixSpace E ⊔ lineSpace M) : eichler Q e w ∈ orthUSpan Q E :=
  orthU_eichler_mem_of_lineFix hEΩ hM (sup_le_lineFixSpace M he) (sup_le_lineFixSpace M hw)

end Span

section Pivots

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}
  {E : Subgroup (orthDerived Q)}

open _root_.Classical in
theorem orthU_isRootCenter_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N : Subgroup E}
    (hN : Nat.card N = p) {s : V} (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0)
    (hsQ : Q s = 0)
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N →
      ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthUSpan Q E) s) :
    IsRootCenter Q (orthUSpan Q E) s := by
  refine ⟨hs0, hsQ, fun w hw => ?_⟩
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  set T : Submodule K V := ⨆ (M : {M : Subgroup E // Nat.card M = p}) (_ : M.1 ≠ N),
    lineSpace M.1 with hT
  have htop : (⊤ : Submodule K V) ≤ (planeFixSpace E ⊔ lineSpace N) ⊔ T := by
    rw [← hK.internal.submodule_iSup_eq_top]
    refine iSup_le fun i => ?_
    rcases i with _ | ⟨M, hM⟩
    · exact le_sup_of_le_left le_sup_left
    · by_cases hMN : M = N
      · subst hMN
        exact le_sup_of_le_left le_sup_right
      · exact le_sup_of_le_right (le_iSup₂_of_le ⟨M, hM⟩ hMN le_rfl)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
  have hsT : polar Q s b = 0 := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => polar Q s b = 0) hb ?_ ?_ ?_
    · intro M b hb'
      refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
        (motive := fun b => polar Q s b = 0) hb' ?_ ?_ ?_
      · intro hMN b hb''
        rw [polar_comm]
        exact polar_eq_zero_of_mem_sup hK hN M.2 hMN hb'' hsN
      · exact polar_zero_right Q s
      · intro x y hx hy
        rw [polar_add_right, hx, hy, add_zero]
    · exact polar_zero_right Q s
    · intro x y hx hy
      rw [polar_add_right, hx, hy, add_zero]
  have hbR : b ∈ rootSet Q (orthUSpan Q E) s := by
    refine Submodule.iSup_induction (fun M : {M : Subgroup E // Nat.card M = p} =>
      ⨆ (_ : M.1 ≠ N), lineSpace M.1) (motive := fun b => b ∈ rootSet Q (orthUSpan Q E) s)
      hb ?_ (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro M b hb'
    refine Submodule.iSup_induction (fun _ : M.1 ≠ N => lineSpace M.1)
      (motive := fun b => b ∈ rootSet Q (orthUSpan Q E) s) hb' ?_
      (AddSubgroup.zero_mem _) (fun x y hx hy => AddSubgroup.add_mem _ hx hy)
    intro hMN b hb''
    exact hpiv M.1 M.2 hMN b hb''
  have haperp : polar Q s a = 0 := by
    rw [polar_add_right, hsT, add_zero] at hw
    exact hw
  have haR : a ∈ rootSet Q (orthUSpan Q E) s :=
    ⟨haperp, orthU_eichler_mem_of_mem_sup hEΩ hN0 hsN ha⟩
  exact ((rootSet Q (orthUSpan Q E) s).add_mem haR hbR).2

theorem orthU_rootSet_ge_of_pivot (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {N M : Subgroup E}
    (hN : Nat.card N = p) (hM : Nat.card M = p) (hMN : M ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hPM : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M)) {s₀ : V}
    (hs₀N : s₀ ∈ lineSpace N) (hs₀0 : s₀ ≠ 0) (hs₀Q : Q s₀ = 0) {b : V} (hbM : b ∈ lineSpace M)
    (hb0 : b ≠ 0) (hbR : b ∈ rootSet Q (orthUSpan Q E) s₀) {s : V}
    (hsN : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∀ v ∈ lineSpace M, v ∈ rootSet Q (orthUSpan Q E) s := by
  classical
  have hN0 : N ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hN
    exact hp.one_lt.ne' hN.symm
  have hM0 : M ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hM
    exact hp.one_lt.ne' hM.symm
  have hne1 : (some ⟨N, hN⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ none := by simp
  have hne2 : (some ⟨M, hM⟩ : Option {M : Subgroup E // Nat.card M = p}) ≠ some ⟨N, hN⟩ :=
    fun h' => hMN (congrArg Subtype.val (Option.some.inj h'))
  have hH : orthUSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthUSpan_le_orthogonalGroup E
  have hs₀perp : ∀ u ∈ planeFixSpace E ⊔ lineSpace M, polar Q s₀ u = 0 := fun u hu => by
    obtain ⟨u₀, hu₀, u₁, hu₁, rfl⟩ := Submodule.mem_sup.1 hu
    have h0 := hK.orth _ _ hne1 s₀ hs₀N u₀ hu₀
    have h1 := hK.orth _ _ hne2.symm s₀ hs₀N u₁ hu₁
    rw [polarBilin_apply_apply] at h0 h1
    rw [polar_add_right, h0, h1, add_zero]
  have hall : ∀ y ∈ planeFixSpace E ⊔ lineSpace M, y ∈ rootSet Q (orthUSpan Q E) s₀ := by
    refine mem_of_invariant (regular_sup hK hM) hPM (rootSet Q (orthUSpan Q E) s₀)
      (fun e he w hw a ha _ => ?_) hbR (Submodule.mem_sup_right hbM) hb0
    have hgH : eichler Q e w ∈ orthUSpan Q E :=
      orthU_eichler_mem_of_mem_sup hEΩ hM0 he hw
    have hfix : eichler Q e w s₀ = s₀ :=
      eichler_apply_of_polar_eq_zero (polar_comm Q e s₀ ▸ hs₀perp e he)
        (polar_comm Q w s₀ ▸ hs₀perp w hw)
    have := rootSet_map hH hgH ha
    rwa [hfix] at this
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN)
    hPN (Submodule.mem_sup_right hs₀N) hsN hs₀0 hs0 (by rw [hs₀Q, hsQ])
  have hgH : g ∈ orthUSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => orthU_eichler_mem_of_mem_sup hEΩ hN0 he hw) hg
  intro v hv
  have hgv : g v = v := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hM hMN hv hu)
  have := rootSet_map hH hgH (hall v (Submodule.mem_sup_right hv))
  rwa [hgv, hgs] at this

theorem orthU_elementaryGroup_le_of_pivots (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime)
    (hQ : (polarBilin Q).Nondegenerate) {N : Subgroup E} (hN : Nat.card N = p)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N))
    (hpiv : ∀ M : Subgroup E, Nat.card M = p → M ≠ N → lineSpace M ≠ ⊥ →
      HasOrthPairs Q (planeFixSpace E ⊔ lineSpace M) ∧ ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧
        ∃ b ∈ lineSpace M, b ≠ 0 ∧ b ∈ rootSet Q (orthUSpan Q E) s₀) :
    elementaryGroup Q ≤ orthUSpan Q E := by
  obtain ⟨a₁, f₁, a₂, f₂, ha₁, hf₁, -, -, hQa₁, hQf₁, -, -, h11, -⟩ := id hPN
  have center : ∀ s ∈ planeFixSpace E ⊔ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthUSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine orthU_isRootCenter_of_pivots hK hEΩ hp hN hsN hs0 hsQ fun M hM hMN v hv => ?_
    by_cases hbot : lineSpace M = ⊥
    · rw [hbot, Submodule.mem_bot] at hv
      rw [hv]
      exact AddSubgroup.zero_mem _
    · obtain ⟨hPM, s₀, hs₀N, hs₀0, hs₀Q, b, hbM, hb0, hbR⟩ := hpiv M hM hMN hbot
      exact orthU_rootSet_ge_of_pivot hK hEΩ hp hN hM hMN hPN hPM hs₀N hs₀0 hs₀Q hbM hb0 hbR hsN
        hs0 hsQ v hv
  have ha₁0 : a₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_left] at h11
    exact zero_ne_one h11
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  exact elementaryGroup_le_of_hypPair hQ (orthUSpan_le_orthogonalGroup E)
    ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (center a₁ ha₁ ha₁0 hQa₁) (center f₁ hf₁ hf₁0 hQf₁)

end Pivots

theorem orthU_le_closure_of_normalized {P : Type} [Group P] [Finite P] {p n : ℕ}
    (hp : p.Prime) {E : Subgroup P} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    {Q : Subgroup P} (hnorm : ∀ e ∈ E, ∀ v ∈ Q, e * v * e⁻¹ ∈ Q) (hQp : ¬ p ∣ Nat.card Q)
    (hQn : ∀ v ∈ Q, v ^ n = 1) :
    Q ≤ Subgroup.closure {k : P | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ n = 1} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
  have hnt : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp.one_lt)
  have hAV : E ≤ Subgroup.normalizer (Q : Set P) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
    have := hnorm e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
    (V := Q) hAV hQp
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  intro k hk
  rw [Subgroup.mem_inf] at hk
  have hBcard : Nat.card B = p := by
    have h := B.card_mul_index
    rw [hB, hcard] at h
    have h2 : Nat.card B * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hBnt : Nontrivial B :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hBcard]; exact hp.one_lt)
  obtain ⟨b, hb⟩ := exists_ne (1 : B)
  refine Subgroup.subset_closure ⟨((b : E) : P), (b : E).2,
    fun h => hb (Subtype.ext (Subtype.ext h)), ?_, hQn k hk.1⟩
  exact (Subgroup.mem_centralizer_iff.1 hk.2 _ (Subgroup.mem_map_of_mem E.subtype b.2)).symm

section Parabolic

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [FiniteDimensional K V] in
theorem orthU_pow_ringChar_of_mem_qRad (h2 : ringChar K ≠ 2) {X : Submodule K V}
    {hX : ∀ x ∈ X, Q x = 0} {g : V ≃ₗ[K] V} (hg : g ∈ qRad Q X hX) : g ^ ringChar K = 1 := by
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hr : (ringChar K).Prime := by
    have := Fintype.ofFinite K
    exact CharP.char_is_prime K _
  set N : Module.End K V := autToEnd K V g - 1 with hNdef
  have hNx : ∀ x, N x = g x - x := fun x => by simp [hNdef, autToEnd_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ qPerp Q X := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ X := by rw [hNx]; exact hg2 _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : autToEnd K V g = 1 + N := by rw [hNdef]; abel
  have hchoose : (((ringChar K).choose 2 : ℕ) : K) = 0 :=
    (CharP.cast_eq_zero_iff K (ringChar K) _).mpr
      (hr.dvd_choose_self two_ne_zero (lt_of_le_of_ne hr.two_le (Ne.symm h2)))
  have hpow : autToEnd K V g ^ ringChar K = 1 := by
    rw [hg1', unip_pow_of_cube_eq_zero (K := K) hN3, ringChar.Nat.cast_ringChar,
      hchoose, zero_smul, zero_smul, add_zero, add_zero]
  have hpow' : autToEnd K V (g ^ ringChar K) = 1 := by rw [map_pow, hpow]
  refine LinearEquiv.ext fun v => ?_
  have := LinearMap.congr_fun hpow' v
  rw [autToEnd_apply] at this
  exact this

theorem orthU_closure_eq_top_of_singular_stable (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h2 : ringChar K ≠ 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) {W : Submodule K V} (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, Q x = 0)
    (hstab : ∀ e ∈ E, ∀ w ∈ W, ((e : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hpK : (p : K) ≠ 0 := by
    intro h0
    have hℓ : (ringChar K).Prime := by
      have := Fintype.ofFinite K
      exact CharP.char_is_prime K _
    have : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
    exact hpl ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  have hfinV : Finite V := Module.finite_of_finite K
  have hfinGL : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g => (g : V → V)) DFunLike.coe_injective
  obtain ⟨hGE, -⟩ := orthDerived_eq_and_le_closure hQ hT
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := hGE.ge
  have hGO : orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup Q
  have hEG : ∀ u w, eichler Q u w ∈ orthDerived Q := fun u w =>
    hEΩ (eichler_mem_elementaryGroup Q u w)
  set H : Subgroup (V ≃ₗ[K] V) := orthUSpan Q E with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthUSpan_le_orthogonalGroup E
  let ρ : E →* Module.End K V := (autToEnd K V).comp ((orthDerived Q).subtype.comp E.subtype)
  have hAc : ∀ a b : E, a * b = b * a := fun a b => Subtype.ext (hcomm _ a.2 _ b.2)
  have hAp : ∀ a : E, a ^ p = 1 := fun a => Subtype.ext (hexp _ a.2)
  have hAstab : ∀ a : E, ∀ w ∈ W, ρ a w ∈ W := fun a w hw => hstab a.1 a.2 w hw
  obtain ⟨F', hF'idx, hW1⟩ : ∃ F' : Subgroup E, F'.index = p ∧ hyperFixed ρ F' ⊓ W ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    have hmem := mem_iSup_hyperFixed_top hpK hAc hAp ρ W hAstab (k := 2) (by norm_num) hcard hm
    have hbot : (⨆ (F' : Subgroup E) (_ : F'.index = p), hyperFixed ρ F' ⊓ W) = ⊥ :=
      iSup_eq_bot.2 fun F' => iSup_eq_bot.2 fun hF' => hcon F' hF'
    rw [hbot] at hmem
    exact hm0 (by simpa using hmem)
  set C : Submodule K V := hyperFixed ρ F' with hC
  set X₁ : Submodule K V := hyperFixed ρ F' ⊓ W with hX₁
  have hX₁mem : ∀ v, v ∈ X₁ ↔ (∀ f ∈ F', ρ f v = v) ∧ v ∈ W := fun v => by
    rw [hX₁, Submodule.mem_inf, mem_hyperFixed]
  have hX₁C : X₁ ≤ C := inf_le_left
  have hX₁Q : ∀ x ∈ X₁, Q x = 0 := fun x hx => hW x ((hX₁mem x).1 hx).2
  let φ : F' →* (V ≃ₗ[K] V) := ((orthDerived Q).subtype.comp E.subtype).comp F'.subtype
  have hφ : ∀ f, φ f ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun f => hGO f.1.1.2
  have hqfix : qFix φ = C := by
    ext v
    rw [mem_qFix, hC, mem_hyperFixed]
    exact ⟨fun h n hn => h ⟨n, hn⟩, fun h f => h f.1 f.2⟩
  have : Fintype F' := Fintype.ofFinite F'
  have hcardF' : Nat.card F' = p := by
    have h := Subgroup.card_mul_index F'
    rw [hF'idx, hcard] at h
    have h2 : Nat.card F' * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos h2
  have hF : ((Fintype.card F' : ℕ) : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcardF']
    exact hpK
  have hF'nt : Nontrivial F' :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardF']; exact hp.one_lt)
  have hS : RootSetup Q H C := by
    refine ⟨hHO, hqfix ▸ polarNondegOn_qFix hQ hφ hF, fun v => ?_, fun u hu w hw => ?_⟩
    · exact ⟨qAvg φ v, hqfix ▸ qAvg_mem φ v, hqfix ▸ sub_qAvg_mem_qPerp hφ hF v⟩
    · obtain ⟨f₀, hf₀⟩ := exists_ne (1 : F')
      exact orthU_eichler_mem_of_fix hEΩ f₀.1.2
        (fun h => hf₀ (Subtype.ext (Subtype.ext h))) (mem_hyperFixed.1 hu f₀ f₀.2)
        (mem_hyperFixed.1 hw f₀ f₀.2)
  set 𝒜 : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype with h𝒜
  have h𝒜O : 𝒜 ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨x, -, rfl⟩
    exact hGO x.2
  have hC𝒜 : ∀ a ∈ 𝒜, ∀ c ∈ C, a c ∈ C := by
    rintro _ ⟨x, hx, rfl⟩ c hc
    exact apply_mem_hyperFixed hAc ⟨x, hx⟩ hc
  have hX₁𝒜 : ∀ a ∈ 𝒜, ∀ x ∈ X₁, a x ∈ X₁ := by
    rintro _ ⟨y, hy, rfl⟩ x hx
    rw [hX₁mem] at hx ⊢
    exact ⟨fun f hf => mem_hyperFixed.1 (apply_mem_hyperFixed hAc ⟨y, hy⟩
      (mem_hyperFixed.2 hx.1)) f hf, hAstab ⟨y, hy⟩ x hx.2⟩
  have hrad : ∀ X : Submodule K V, X ≤ C → (∀ x ∈ X, Q x = 0) →
      (∀ a ∈ 𝒜, ∀ x ∈ X, a x ∈ X) → ∀ x ∈ X, ∀ d ∈ qPerp Q X, eichler Q x d ∈ H := by
    intro X _ hXQ hX𝒜 x hx d hd
    set Qx : Subgroup (orthDerived Q) := (qRad Q X hXQ).comap (orthDerived Q).subtype with hQx
    have hnorm : ∀ e ∈ E, ∀ v ∈ Qx, e * v * e⁻¹ ∈ Qx := by
      intro e he v hv
      have haS : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V) y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e, he, rfl⟩ y hy
      have haS' : ∀ y ∈ X, ((e : orthDerived Q) : V ≃ₗ[K] V)⁻¹ y ∈ X := fun y hy =>
        hX𝒜 _ ⟨e⁻¹, E.inv_mem he, rfl⟩ y hy
      exact qRad_conj_mem (hX := hXQ) (hGO e.2) haS haS' hv
    have hQp : ¬ p ∣ Nat.card Qx :=
      not_dvd_card_comap_qRad (hX := hXQ) hp hp2 hpK (orthDerived Q)
    have hQr : ∀ v ∈ Qx, v ^ ringChar K = 1 := fun v hv =>
      Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact orthU_pow_ringChar_of_mem_qRad h2 (Subgroup.mem_comap.mp hv))
    have hle := orthU_le_closure_of_normalized hp ⟨⟨⟨hAc⟩⟩, hexp⟩ hcard hnorm hQp hQr
    have hmem : (⟨eichler Q x d, hEG x d⟩ : orthDerived Q) ∈ Qx :=
      eichler_mem_qRad (hX := hXQ) hx hd
    rw [hH, orthUSpan_eq_map]
    exact ⟨_, hle hmem, rfl⟩
  obtain ⟨e₀, he₀, he₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW1
  obtain ⟨a, b, ha, hb, hab⟩ := exists_rootCenter_pair hS h𝒜O hC𝒜 hrad hX₁C hX₁Q hX₁𝒜 he₀ he₀0
  let P₀ : HypPair Q :=
    { e := a
      f := (polar Q a b)⁻¹ • b
      Q_e := ha.2.1
      Q_f := by rw [map_smul_eq_sq, hb.2.1, mul_zero]
      polar_ef := by rw [polar_smul_right_eq, inv_mul_cancel₀ hab] }
  have hle : elementaryGroup Q ≤ H :=
    elementaryGroup_le_of_hypPair hQ hHO P₀ ha (hb.smul (inv_ne_zero hab))
  exact orthU_closure_eq_top_of_le E (hGE.le.trans hle)

end Parabolic

section ManyTwo

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem orthU_eichler_mem_of_plane (hEΩ : elementaryGroup Q ≤ orthDerived Q) {z : E}
    (hz1 : z ≠ 1)
    {e : V} (heQ : Q e = 0) {τ : K} (hτ : τ ≠ 0)
    (hrel : ((z : orthDerived Q) : V ≃ₗ[K] V) (((z : orthDerived Q) : V ≃ₗ[K] V) e) =
      τ • ((z : orthDerived Q) : V ≃ₗ[K] V) e - e)
    (hli : LinearIndependent K ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]) :
    ∀ w ∈ Submodule.span K (Set.range ![e, ((z : orthDerived Q) : V ≃ₗ[K] V) e]),
      eichler Q e w ∈ orthUSpan Q E := by
  classical
  set g : V ≃ₗ[K] V := ((z : orthDerived Q) : V ≃ₗ[K] V) with hg
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_mem_orthogonalGroup
  obtain ⟨hTQ, hTp⟩ := manyTwo_plane_facts hgO heQ hτ hrel
  set T := Submodule.span K (Set.range ![e, g e]) with hT
  have he : e ∈ T := Submodule.subset_span ⟨0, rfl⟩
  have hge : g e ∈ T := Submodule.subset_span ⟨1, rfl⟩
  have hT2 : finrank K T = 2 := by rw [hT, finrank_span_eq_card hli]; simp
  have hTg : ∀ t ∈ T, g t ∈ T := by
    intro t ht
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
    rw [hrel]
    exact T.add_mem (T.smul_mem _ hge) (T.smul_mem _ (T.sub_mem (T.smul_mem _ hge) he))
  have hdet := manyTwo_det_restrict_pair hli hrel hTg
  intro w hw
  have hc := commute_eichler_of_det_one hgO hT2 hTQ hTp hTg hdet he hw
  exact orthU_mem_of_commute (a := (z : orthDerived Q))
    (hEΩ (eichler_mem_elementaryGroup Q e w)) z.2 (fun h => hz1 (Subtype.ext h)) hc.eq
    (orthU_eichler_pow_ringChar e w)


theorem orthU_eichler_mem_of_pair_pieces (hQ : (polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hK : KernelLineData Q p E) (hEΩ : elementaryGroup Q ≤ orthDerived Q)
    (hNS : OrthNoInvariantSingular Q E) {M₁ M₂ : Subgroup E} (hM₁ : Nat.card M₁ = p)
    (hM₂ : Nat.card M₂ = p) (hM : M₁ ≠ M₂) {P₁ P₂ : Submodule K V} (hP₁ : IsPiece Q E P₁)
    (hP₂ : IsPiece Q E P₂) (h₁ : P₁ ≤ lineSpace M₁) (h₂ : P₂ ≤ lineSpace M₂)
    (hperp : OrthSep Q P₁ P₂) (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    ∀ e ∈ P₁ ⊔ P₂, ∀ w ∈ P₁ ⊔ P₂, eichler Q e w ∈ orthUSpan Q E := by
  classical
  obtain ⟨hp2, hpl⟩ := manyTwo_ne_two_and_ne_ringChar hp h2
  obtain ⟨x, y, τ, hτ, hnoroot, hcl, hx, hy⟩ :=
    exists_two_mixing_elements_aux hK hp hM₁ hM₂ hM hP₁ hP₂ h₁ h₂ h2
  set X : Submodule K V := P₁ ⊔ P₂ with hX
  have hXreg : PolarNondegOn Q X := polarNondegOn_sup hP₁.regular hP₂.regular hperp
  have hd₁ : finrank K P₁ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₁.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hd₂ : finrank K P₂ = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := hP₂.exists_line hK hp hp2 hpl
    exact h.trans h2
  have hX4 : finrank K X = 4 := by
    have hdisj := OrthSep.disjoint hP₁.regular hperp
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rw [hdisj.eq_bot, finrank_bot, add_zero, ← hX] at this
    omega
  have hXst : ∀ z : E, ∀ u ∈ X, ((z : orthDerived Q) : V ≃ₗ[K] V) u ∈ X := by
    intro z u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    exact Submodule.add_mem_sup (hP₁.eStable z z.2 u₁ hu₁) (hP₂.eStable z z.2 u₂ hu₂)
  have hroot : ∀ e ∈ X, e ≠ 0 → Q e = 0 → ∀ w ∈ X, polar Q e w = 0 →
      eichler Q e w ∈ orthUSpan Q E := by
    intro e heX he0 heQ w hwX hew
    have hrx := hx e heX
    have hry := hy e heX
    have hx1 : x ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hrx
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hy1 : y ≠ 1 := by
      rintro rfl
      have h1 : e = τ • e - e := hry
      have h3 : (τ - 2) • e = 0 := by linear_combination (norm := module) -h1
      have h4 : τ = 2 := sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_right he0)
      exact hnoroot 1 (by rw [h4]; norm_num)
    have hlix := manyTwo_linearIndependent_pair he0 hrx hnoroot
    have hliy := manyTwo_linearIndependent_pair he0 hry hnoroot
    obtain ⟨hTxQ, hTxp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (x : orthDerived Q))) heQ hτ hrx
    obtain ⟨hTyQ, hTyp⟩ := manyTwo_plane_facts
      (orthDerived_mem_orthogonalGroup (g := (y : orthDerived Q))) heQ hτ hry
    set Tx := Submodule.span K (Set.range ![e, ((x : orthDerived Q) : V ≃ₗ[K] V) e]) with hTx
    set Ty := Submodule.span K (Set.range ![e, ((y : orthDerived Q) : V ≃ₗ[K] V) e]) with hTy
    have hexT : e ∈ Tx := Submodule.subset_span ⟨0, rfl⟩
    have hexT' : e ∈ Ty := Submodule.subset_span ⟨0, rfl⟩
    have hTx2 : finrank K Tx = 2 := by rw [hTx, finrank_span_eq_card hlix]; simp
    have hTy2 : finrank K Ty = 2 := by rw [hTy, finrank_span_eq_card hliy]; simp
    set S : Submodule K V := X ⊓ LinearMap.ker (polarBilin Q e) with hS
    have hmemS : ∀ v, v ∈ S ↔ v ∈ X ∧ polar Q e v = 0 := fun v => by
      rw [hS, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply]
    have hTxX : Tx ≤ X := by
      rw [hTx, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst x e heX
    have hTyX : Ty ≤ X := by
      rw [hTy, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact heX
      · exact hXst y e heX
    have hTxS : Tx ≤ S := fun v hv => (hmemS v).mpr ⟨hTxX hv, hTxp e hexT v hv⟩
    have hTyS : Ty ≤ S := fun v hv => (hmemS v).mpr ⟨hTyX hv, hTyp e hexT' v hv⟩
    have hSlt : S < X := by
      refine lt_of_le_of_ne inf_le_left fun hSX => ?_
      obtain ⟨u, huX, hu⟩ := hXreg.exists_polar_ne_zero heX he0
      have : u ∈ S := hSX ▸ huX
      exact hu ((hmemS u).mp this).2
    have hS3 : finrank K S ≤ 3 := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt
      omega
    have hne : Tx ≠ Ty := by
      intro hxy
      have hTstx : ∀ t ∈ Tx, ((x : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hrx]
        have h1 : ((x : orthDerived Q) : V ≃ₗ[K] V) e ∈ Tx := Submodule.subset_span ⟨1, rfl⟩
        exact Tx.add_mem (Tx.smul_mem _ h1) (Tx.smul_mem _ (Tx.sub_mem (Tx.smul_mem _ h1) hexT))
      have hTsty : ∀ t ∈ Tx, ((y : orthDerived Q) : V ≃ₗ[K] V) t ∈ Tx := by
        intro t ht
        rw [hxy] at ht ⊢
        obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ht
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_smul]
        rw [hry]
        have h1 : ((y : orthDerived Q) : V ≃ₗ[K] V) e ∈ Ty := Submodule.subset_span ⟨1, rfl⟩
        exact Ty.add_mem (Ty.smul_mem _ h1) (Ty.smul_mem _ (Ty.sub_mem (Ty.smul_mem _ h1) hexT'))
      have hst := manyTwo_eStable_of_closure hK hp.pos hcl hTstx hTsty
      have hbot := hNS Tx hst hTxQ
      rw [hbot] at hexT
      exact he0 ((Submodule.mem_bot K).mp hexT)
    have hinf : finrank K ↥(Tx ⊓ Ty) ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have e1 : Tx ⊓ Ty = Tx :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
      have e2 : Tx ⊓ Ty = Ty :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
      exact hne (e1.symm.trans e2)
    have hsup3 : 3 ≤ finrank K ↥(Tx ⊔ Ty) := by
      have := Submodule.finrank_sup_add_finrank_inf_eq Tx Ty
      omega
    have hSeq : Tx ⊔ Ty = S :=
      Submodule.eq_of_le_of_finrank_le (sup_le hTxS hTyS) (by omega)
    have hwS : w ∈ Tx ⊔ Ty := by rw [hSeq, hmemS]; exact ⟨hwX, hew⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hwS
    rw [← eichler_mul (hTxp e hexT a ha) (hTyp e hexT' b hb)]
    exact (orthUSpan Q E).mul_mem
      (orthU_eichler_mem_of_plane hEΩ hx1 heQ hτ hrx hlix a ha)
      (orthU_eichler_mem_of_plane hEΩ hy1 heQ hτ hry hliy b hb)
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) (S := X) (by omega)
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  exact eichler_mem_of_relRoot (orthUSpan_le_orthogonalGroup E) hXreg huX hu'X huQ hu'Q
    (by rw [huu']; exact one_ne_zero) (fun w hw hpw => hroot u huX hu0 huQ w hw hpw)
    (fun w hw hpw => hroot u' hu'X hu'0 hu'Q w hw hpw)

end ManyTwo

section ManyTwoMain

theorem orthU3_three_le_card {K : Type} [Field K] [Finite K] (h2 : ringChar K ≠ 2) :
    3 ≤ Nat.card K := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hr, hcard⟩ := FiniteField.card K (ringChar K)
  rw [Nat.card_eq_fintype_card, hcard]
  have h3 : 3 ≤ ringChar K := by
    have := hr.two_le
    omega
  exact h3.trans (Nat.le_self_pow (PNat.ne_zero n) _)

theorem orthU_closure_eq_top_of_noSingular_two {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) (hK3 : 3 ≤ Nat.card K)
    (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h2 : orderOf ((Nat.card K : ℕ) : ZMod p) = 2) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  classical
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, hPV, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨a, b, hab⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hH : orthUSpan Q E ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthUSpan_le_orthogonalGroup E
  have hdimP : ∀ i, finrank K (P i) = 2 := fun i => (hMf i).trans h2
  have hV0reg : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have haniso : ∀ i, ∀ t ∈ P i, Q t = 0 → t = 0 := fun i =>
    (hP i).anisotropic_of_orderOf_two_of_ne_two hK hp hp2 hpl h2
  have hV02 : finrank K (planeFixSpace E) ≤ 2 := finrank_planeFixSpace_le_two hNS
  have hcount : 7 ≤ finrank K (planeFixSpace E) + 2 * n := by
    have h1 : finrank K V ≤ finrank K ↥(planeFixSpace E ⊔ ⨆ i, P i) := by
      rw [← finrank_top K V]
      exact Submodule.finrank_mono hPsp
    have h3 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) (⨆ i, P i)
    have h4 := manyTwo_finrank_iSup_fin_le P
    simp only [hdimP, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h4
    omega
  have hEichPair : ∀ i j : Fin n, i ≠ j → ∀ e ∈ P i ⊔ P j, ∀ w ∈ P i ⊔ P j,
      eichler Q e w ∈ orthUSpan Q E := by
    intro i j hij
    by_cases hM : M i = M j
    · have hle : P i ⊔ P j ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le ((hMP i).trans le_sup_right) ?_
        rw [hM]
        exact (hMP j).trans le_sup_right
      exact fun e he w hw => orthU_eichler_mem_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle he) (hle hw)
    · exact orthU_eichler_mem_of_pair_pieces hQ hp hK hEΩ hNS (hMc i) (hMc j) hM (hP i) (hP j)
        (hMP i) (hMP j) (hPP i j hij) h2
  have hY : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
      (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧ OrthSep Q Y (P a ⊔ P b) ∧
      PolarNondegOn Q Y ∧ (∀ e ∈ Y, ∀ w ∈ Y, eichler Q e w ∈ orthUSpan Q E) ∧
      3 ≤ finrank K Y ∧ (finrank K Y = 3 → (2 : K) ≠ 0) := by
    intro k hka hkb
    have hkab : OrthSep Q (P k) (P a ⊔ P b) :=
      manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb)
    by_cases hV0 : planeFixSpace E = ⊥
    ·
      have hn4 : 4 ≤ n := by
        have : finrank K (planeFixSpace E) = 0 := by rw [hV0]; exact finrank_bot K V
        omega
      obtain ⟨l, hl⟩ := manyTwo_exists_fin_notMem (S := {a, b, k}) (m := 3) (by omega)
        Finset.card_le_three
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      obtain ⟨hla, hlb, hlk⟩ := hl
      have hkl : OrthSep Q (P k) (P l) := hPP k l (Ne.symm hlk)
      have hlab : OrthSep Q (P l) (P a ⊔ P b) :=
        manyTwo_orthSep_sup_right (hPP l a hla) (hPP l b hlb)
      have hdisj := OrthSep.disjoint (hP k).regular hkl
      have hdimY : finrank K ↥(P k ⊔ P l) = 4 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (P k) (P l)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k, hdimP l] at this
        omega
      exact ⟨P k ⊔ P l, le_sup_left, fun h => absurd hV0 h, manyTwo_orthSep_sup_left hkab hlab,
        polarNondegOn_sup (hP k).regular (hP l).regular hkl,
        hEichPair k l (Ne.symm hlk), by omega, fun h => absurd h (by omega)⟩
    ·
      have hd0 : 1 ≤ finrank K (planeFixSpace E) := Submodule.one_le_finrank_iff.mpr hV0
      have hdisj := (hP k).disjoint.symm
      have hdimY : finrank K ↥(planeFixSpace E ⊔ P k) = finrank K (planeFixSpace E) + 2 := by
        have := Submodule.finrank_sup_add_finrank_inf_eq (planeFixSpace E) (P k)
        rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP k] at this
        omega
      have hle : planeFixSpace E ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M k) :=
        sup_le le_sup_left ((hMP k).trans le_sup_right)
      refine ⟨planeFixSpace E ⊔ P k, le_sup_right, fun _ => le_sup_left,
        manyTwo_orthSep_sup_left (manyTwo_orthSep_sup_right (hPV a) (hPV b)) hkab,
        polarNondegOn_sup hV0reg (hP k).regular (hPV k),
        fun e he w hw => orthU_eichler_mem_of_mem_sup hEΩ (ne_bot_of_card_prime hp (hMc k))
          (hle he) (hle hw), by omega, fun h3 => ?_⟩
      exact two_ne_zero_of_finrank_planeFixSpace hK (by omega)
  have hRoot : ∀ s ∈ P a ⊔ P b, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthUSpan Q E) s := by
    intro s hs hs0 hsQ
    have hrel : ∀ w ∈ P a ⊔ P b, polar Q s w = 0 → w ∈ rootSet Q (orthUSpan Q E) s :=
      fun w hw hsw => ⟨hsw, hEichPair a b hab' s hs w hw⟩
    have hYR : ∀ k : Fin n, k ≠ a → k ≠ b → ∃ Y : Submodule K V, P k ≤ Y ∧
        (planeFixSpace E ≠ ⊥ → planeFixSpace E ≤ Y) ∧
        ∀ y ∈ Y, y ∈ rootSet Q (orthUSpan Q E) s := by
      intro k hka hkb
      obtain ⟨Y, hPY, hV0Y, hYP, hYreg, hYH, hY3, h2Y⟩ := hY k hka hkb
      have hsY : ∀ y ∈ Y, polar Q s y = 0 := fun y hy => by
        rw [polar_comm]
        exact hYP y hy s hs
      have hmix := exists_mixed_vector hH (hP a).regular (hP b).regular (hP k).regular
        (hPP a b hab') (hPP a k (Ne.symm hka)) (hPP b k (Ne.symm hkb)) (hdimP a) (hdimP b)
        (hdimP k) (haniso a) (haniso b) (haniso k) hK3 hPY hYP
        (hEichPair b k (Ne.symm hkb)) hs hs0 hsQ hrel
      exact ⟨Y, hPY, hV0Y, manyTwo_subset_rootSet_of_pivot hH hYreg hY3 h2Y hYH hsY hmix⟩
    refine ⟨hs0, hsQ, fun w hsw => ?_⟩
    have hspan : (⊤ : Submodule K V) ≤ (P a ⊔ P b) ⊔
        (planeFixSpace E ⊔ ⨆ k : {k : Fin n // k ≠ a ∧ k ≠ b}, P k.1) := by
      refine hPsp.trans (sup_le ?_ (iSup_le fun i => ?_))
      · exact le_sup_of_le_right le_sup_left
      · by_cases hia : i = a
        · rw [hia]
          exact le_sup_of_le_left le_sup_left
        by_cases hib : i = b
        · rw [hib]
          exact le_sup_of_le_left le_sup_right
        · exact le_sup_of_le_right (le_sup_of_le_right
            (le_iSup (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1) ⟨i, hia, hib⟩))
    obtain ⟨w₁, hw₁, z, hz, rfl⟩ := Submodule.mem_sup.mp (hspan (Submodule.mem_top (x := w)))
    have hzR : polar Q s z = 0 ∧ z ∈ rootSet Q (orthUSpan Q E) s := by
      obtain ⟨v₀, hv₀, z', hz', rfl⟩ := Submodule.mem_sup.mp hz
      have hv₀perp : polar Q s v₀ = 0 := by
        rw [polar_comm]
        exact manyTwo_orthSep_sup_right (hPV a) (hPV b) v₀ hv₀ s hs
      have hz'R : polar Q s z' = 0 ∧ z' ∈ rootSet Q (orthUSpan Q E) s := by
        refine Submodule.iSup_induction (fun k : {k : Fin n // k ≠ a ∧ k ≠ b} => P k.1)
          (motive := fun x => polar Q s x = 0 ∧ x ∈ rootSet Q (orthUSpan Q E) s) hz'
          ?_ ⟨polar_zero_right Q s, AddSubgroup.zero_mem _⟩ ?_
        · rintro ⟨k, hka, hkb⟩ x hx
          obtain ⟨Y, hPY, -, hYR'⟩ := hYR k hka hkb
          refine ⟨?_, hYR' x (hPY hx)⟩
          rw [polar_comm]
          exact manyTwo_orthSep_sup_right (hPP k a hka) (hPP k b hkb) x hx s hs
        · rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
          exact ⟨by rw [polar_add_right, hx1, hy1, add_zero], AddSubgroup.add_mem _ hx2 hy2⟩
      have hv₀R : v₀ ∈ rootSet Q (orthUSpan Q E) s := by
        by_cases hV0 : planeFixSpace E = ⊥
        · rw [hV0] at hv₀
          rw [(Submodule.mem_bot K).mp hv₀]
          exact AddSubgroup.zero_mem _
        · have hn3 : 2 < n := by omega
          obtain ⟨k, hk⟩ := manyTwo_exists_fin_notMem (S := {a, b}) (m := 2) hn3 Finset.card_le_two
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          obtain ⟨Y, -, hV0Y, hYR'⟩ := hYR k hk.1 hk.2
          exact hYR' v₀ (hV0Y hV0 hv₀)
      exact ⟨by rw [polar_add_right, hv₀perp, hz'R.1, add_zero],
        AddSubgroup.add_mem _ hv₀R hz'R.2⟩
    have hw₁perp : polar Q s w₁ = 0 := by
      rw [polar_add_right, hzR.1, add_zero] at hsw
      exact hsw
    exact (AddSubgroup.add_mem _ (hrel w₁ hw₁ hw₁perp) hzR.2).2
  have hXreg : PolarNondegOn Q (P a ⊔ P b) :=
    polarNondegOn_sup (hP a).regular (hP b).regular (hPP a b hab')
  have hX3 : 3 ≤ finrank K ↥(P a ⊔ P b) := by
    have hdisj := OrthSep.disjoint (hP a).regular (hPP a b hab')
    have := Submodule.finrank_sup_add_finrank_inf_eq (P a) (P b)
    rw [hdisj.eq_bot, finrank_bot, add_zero, hdimP a, hdimP b] at this
    omega
  obtain ⟨u, huX, hu0, huQ⟩ := exists_singular_of_three_le_any (Q := Q) hX3
  obtain ⟨u', hu'X, hu'Q, huu'⟩ := exists_partner_of_polarNondegOn hXreg huX hu0 huQ
  have hu'0 : u' ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at huu'
    exact zero_ne_one huu'
  have hle : elementaryGroup Q ≤ orthUSpan Q E :=
    elementaryGroup_le_of_hypPair hQ hH ⟨u, u', huQ, hu'Q, huu'⟩ (hRoot u huX hu0 huQ)
      (hRoot u' hu'X hu'0 hu'Q)
  exact orthU_closure_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end ManyTwoMain

section Mixing

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

theorem orthU_transvectionUnit_pow_ringChar {K E W : Type*} [Field K] [Field E] [Algebra K E]
    [AddCommGroup W] [Module E W] (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) :
    transvectionUnit φ w hφ ^ ringChar K = 1 := by
  have h0 : ((ringChar K : ℕ) : E) = 0 := by
    rw [← map_natCast (algebraMap K E), ringChar.Nat.cast_ringChar, map_zero]
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  change (1 + φ.smulRight w) ^ ringChar K = 1
  rw [CFSG.RankThree.PartTwo.Census.one_add_pow_of_mul_self_eq_zero (smulRight_mul_self φ w hφ),
    ← Nat.cast_smul_eq_nsmul E, h0, zero_smul, add_zero]

theorem orthU_unitaryTransvection_eq {E W : Type*} [Field E] [AddCommGroup W]
    [Module E W] (H : W → W → E) (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) {e : W} (he : H e e = 0) (a : E) :
    unitaryTransvection H hadd₂ hsm₂ he a =
      transvectionUnit (hermTransvectionForm H hadd₂ hsm₂ e a) e
        (by simp [hermTransvectionForm, he]) := rfl

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem orthU_pow_ringChar_of_blockGL_eq (hx : OddOrderIsometry Q p x) {r : K[X]}
    [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap)
    {φ : primaryComponent x.toLinearMap r →ₗ[AdjoinRoot r] AdjoinRoot r}
    {w : primaryComponent x.toLinearMap r} {hφ : φ w = 0} {g : ↥(supportedBlock Q x r)}
    (hg : blockGL Q x r g = transvectionUnit φ w hφ) : (g : V ≃ₗ[K] V) ^ ringChar K = 1 := by
  have h1 : blockGL Q x r (g ^ ringChar K) = blockGL Q x r 1 := by
    rw [map_pow, hg, map_one]
    exact orthU_transvectionUnit_pow_ringChar (K := K) φ w hφ
  have h2 := hx.blockGL_injective hr h1
  have := congrArg Subtype.val h2
  simpa using this

theorem orthU_exists_selfdual_mixing_action (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) (h2 : (2 : K) ≠ 0) {S₁ S₂ : Submodule K V}
    (hS₂ : ∀ v ∈ S₂, x v ∈ S₂)
    (hperp : ∀ u ∈ S₁, ∀ w ∈ S₂, QuadraticMap.polar Q u w = 0)
    (hv : ∃ v ∈ S₁ ⊓ primaryComponent x.toLinearMap r, Q v ≠ 0)
    (hw : ∃ w ∈ S₂ ⊓ primaryComponent x.toLinearMap r, Q w ≠ 0) :
    ∃ g ∈ specialBlock Q x r, g ^ ringChar K = 1 ∧ ∃ u w : primaryComponent x.toLinearMap r,
      (u : V) ∈ S₁ ∧ (w : V) ∈ S₂ ∧ Q (u : V) ≠ 0 ∧ Q (w : V) ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x r u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x r w)) ∧
      ∃ lam mu : AdjoinRoot r, lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ z : AdjoinRoot r,
        g (eline x r u z) = eline x r u (lam * z) + eline x r w (mu * z) := by
  have : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  obtain ⟨v, hv1, hvQ⟩ := hv
  obtain ⟨w, hw1, hwQ⟩ := hw
  let u : primaryComponent x.toLinearMap r := ⟨v, hv1.2⟩
  let w' : primaryComponent x.toLinearMap r := ⟨w, hw1.2⟩
  have hu0 : u ≠ 0 := fun h => hvQ (by
    have : v = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hw0 : w' ≠ 0 := fun h => hwQ (by
    have : w = 0 := congrArg Subtype.val h
    rw [this, QuadraticMap.map_zero])
  have hHuw : H u w' = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w' c]
    exact hperp _ hv1.1 _ (smul_mem_of_stable hS₂ c w' hw1.1)
  have hHwu : H w' u = 0 := by rw [hsymm' u w', hHuw, map_zero]
  have hanis : ∀ y : primaryComponent x.toLinearMap r, Q (y : V) ≠ 0 → H y y ≠ 0 := by
    intro y hy h0
    have h1 := htr y y 1
    rw [h0, zero_mul, map_zero, one_smul, QuadraticMap.polar_self, two_nsmul] at h1
    have h3 : (2 : K) * Q (y : V) = 0 := by rw [two_mul]; exact h1.symm
    exact hy ((mul_eq_zero.mp h3).resolve_left h2)
  have hHuu : H u u ≠ 0 := hanis u hvQ
  have hHww : H w' w' ≠ 0 := hanis w' hwQ
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w' w') = H w' w' := (hsymm' w' w').symm
  have hreg : ∀ y : primaryComponent x.toLinearMap r, H y y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) := by
    intro y hy
    rintro _ ⟨z₁, rfl⟩ hxy
    have hz : ∀ z : AdjoinRoot r, Algebra.trace K (AdjoinRoot r) (hU.bar z₁ * H y y * z) = 0 := by
      intro z
      have h1 := hxy (eline x r y z) ⟨z, rfl⟩
      rw [eline_apply, eline_apply] at h1
      have h3 := htr (z₁ • y) y z
      rw [hsm₁', h1] at h3
      exact h3
    have h4 : hU.bar z₁ * H y y = 0 := eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) hz
    have h5 : hU.bar z₁ = 0 := (mul_eq_zero.mp h4).resolve_right hy
    have h6 : z₁ = 0 := by
      have := congrArg hU.bar h5
      rwa [hU.bar_bar, map_zero] at this
    rw [h6, map_zero]
  set f₀ : AdjoinRoot r := -(H u u) / H w' w' with hf₀
  have hf₀0 : f₀ ≠ 0 := div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w') (u + c • w') = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w' w') = f₀ * H w' w' := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  obtain ⟨z, hz⟩ := hU.exists_bar_ne
  set a : AdjoinRoot r := z - hU.bar z with ha
  have ha0 : a ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have haσ : hU.bar a = -a := by rw [ha, map_sub, hU.bar_bar]; ring
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hlam : 1 + a * H u u ≠ 0 := by
    intro h0
    have h1 := congrArg hU.bar h0
    rw [map_add, map_one, map_mul, haσ, hHuu_fix, map_zero] at h1
    have h3 : (2 : AdjoinRoot r) = 0 := by linear_combination h0 + h1
    have h4 : algebraMap K (AdjoinRoot r) 2 = 2 := map_ofNat _ 2
    exact h2 ((algebraMap K (AdjoinRoot r)).injective (by rw [h4, h3, map_zero]))
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + a * H u u) * z) • u + ((a * H u u * c) * z) • w' := by
    intro z
    have hHe : H (u + c • w') (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe]
    module
  have hgr : g.1 ^ ringChar K = 1 :=
    orthU_pow_ringChar_of_blockGL_eq hx hr (orthU_unitaryTransvection_eq H hadd₂ hsm₂ he a ▸ hg)
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, hgr, u, w', hv1.1, hw1.1, hvQ, hwQ, hreg u hHuu,
    hreg w' hHww, 1 + a * H u u, a * H u u * c, hlam,
    mul_ne_zero (mul_ne_zero ha0 hHuu) hc0, fun z => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm

theorem orthU_exists_selfdual_mixing_family (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {r : K[X]}
    [Fact (Irreducible r)] (hr : r ∈ primaryFactors x.toLinearMap) (hne1 : r ≠ X - 1)
    (hself : r = reciprocalPolynomial r) {S₁ S₂ : Submodule K V}
    (hS₂ : ∀ v ∈ S₂, x v ∈ S₂) (hperp : ∀ a ∈ S₁, ∀ b ∈ S₂, QuadraticMap.polar Q a b = 0)
    (u w : primaryComponent x.toLinearMap r) (hu : (u : V) ∈ S₁) (hw : (w : V) ∈ S₂)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) (hureg : PolarNondegOn Q (LinearMap.range (eline x r u)))
    (hwreg : PolarNondegOn Q (LinearMap.range (eline x r w))) :
    ∃ d : ℕ, r.natDegree = 2 * d ∧ ∃ c : AdjoinRoot r, c ≠ 0 ∧
      ∀ θ : AdjoinRoot r, frobPow K (AdjoinRoot r) d θ = -θ →
        ∃ g ∈ specialBlock Q x r, g ^ ringChar K = 1 ∧
          (∀ z : AdjoinRoot r, g (eline x r u z) =
            eline x r u ((1 + θ) * z) + eline x r w ((θ * c) * z)) ∧
          ∀ z z' : AdjoinRoot r, QuadraticMap.polar Q (eline x r u ((1 + θ) * z))
            (eline x r u ((1 + θ) * z')) =
            QuadraticMap.polar Q (eline x r u z) (eline x r u ((1 - θ ^ 2) * z')) := by
  obtain ⟨d, H, hdeg, -, htr, hadd₁, hadd₂, hsm₁, hsm₂, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hr hne1 hself
  have hfin : finrank K (AdjoinRoot r) = 2 * d := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible r).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, -, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot r) hfin
  have hfb : ∀ z, frobPow K (AdjoinRoot r) d z = hU.bar z := fun z => by
    rw [frobPow_apply, hbar]
  have hsm₁' : ∀ (c : AdjoinRoot r) u w, H (c • u) w = hU.bar c * H u w := fun c u w => by
    rw [hsm₁, hfb]
  have hsymm' : ∀ u w, H w u = hU.bar (H u w) := fun u w => by rw [hsymm, hfb]
  have hpolar : ∀ (y : primaryComponent x.toLinearMap r) (z z' : AdjoinRoot r),
      QuadraticMap.polar Q (eline x r y z) (eline x r y z') =
        Algebra.trace K (AdjoinRoot r) (hU.bar z * H y y * z') := by
    intro y z z'
    have h1 := htr (z • y) y z'
    rw [hsm₁'] at h1
    exact h1.symm
  have hHnz : ∀ y : primaryComponent x.toLinearMap r, y ≠ 0 →
      PolarNondegOn Q (LinearMap.range (eline x r y)) → H y y ≠ 0 := by
    intro y hy0 hyreg h0
    apply hy0
    have h1 : eline x r y 1 = 0 := hyreg _ ⟨1, rfl⟩ (by
      rintro _ ⟨z, rfl⟩
      rw [hpolar, h0, mul_zero, zero_mul, map_zero])
    rw [eline_apply, one_smul] at h1
    exact Subtype.ext h1
  have hHuu : H u u ≠ 0 := hHnz u hu0 hureg
  have hHww : H w w ≠ 0 := hHnz w hw0 hwreg
  have hHuw : H u w = 0 := by
    refine eq_zero_of_trace_mul_eq_zero K (AdjoinRoot r) fun c => ?_
    rw [htr u w c]
    exact hperp _ hu _ (smul_mem_of_stable hS₂ c w hw)
  have hHwu : H w u = 0 := by rw [hsymm' u w, hHuw, map_zero]
  have hHuu_fix : hU.bar (H u u) = H u u := (hsymm' u u).symm
  have hHww_fix : hU.bar (H w w) = H w w := (hsymm' w w).symm
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : AdjoinRoot r, f₀ = -(H u u) / H w w := ⟨_, rfl⟩
  have hf₀0 : f₀ ≠ 0 := by
    rw [hf₀]
    exact div_ne_zero (neg_ne_zero.mpr hHuu) hHww
  have hf₀fix : hU.bar f₀ = f₀ := by
    rw [hf₀, map_div₀, map_neg, hHuu_fix, hHww_fix]
  obtain ⟨c, hc⟩ := hU.normHom_surjective ⟨f₀, hU.mem_fixedField.mpr hf₀fix⟩
  have hcn : c * hU.bar c = f₀ := congrArg Subtype.val hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hf₀0 (by rw [← hcn, zero_mul])
  have he : H (u + c • w) (u + c • w) = 0 := by
    simp only [hadd₁, hadd₂, hsm₁', hsm₂, hHuw, hHwu, mul_zero, add_zero, zero_add]
    have : hU.bar c * (c * H w w) = f₀ * H w w := by rw [← hcn]; ring
    rw [this, hf₀, div_mul_cancel₀ _ hHww, add_neg_cancel]
  refine ⟨d, hdeg, c, hc0, fun θ hθ => ?_⟩
  have hθ' : hU.bar θ = -θ := by rw [← hfb]; exact hθ
  obtain ⟨a, ha⟩ : ∃ a : AdjoinRoot r, a = θ * (H u u)⁻¹ := ⟨_, rfl⟩
  have haσ : hU.bar a = -a := by
    rw [ha, map_mul, map_inv₀, hHuu_fix, hθ', neg_mul]
  have haH : a * H u u = θ := by rw [ha, mul_assoc, inv_mul_cancel₀ hHuu, mul_one]
  have hpres : ∀ y y' : primaryComponent x.toLinearMap r,
      H (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y)
        (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) y') = H y y' := by
    intro y y'
    rw [unitaryTransvection_apply, unitaryTransvection_apply]
    exact hermitian_transvection_preserves hU.bar H hadd₁ hadd₂ hsm₁' hsm₂ hsymm' he haσ y y'
  obtain ⟨g, hg⟩ := (hx.mem_range_blockGL_selfDual_iff hr hne1 hself H htr
    (unitaryTransvection H hadd₂ hsm₂ he a)).mpr hpres
  have hact : ∀ z : AdjoinRoot r,
      (((unitaryTransvection H hadd₂ hsm₂ he a : BlockGL x r) :
          Module.End (AdjoinRoot r) (primaryComponent x.toLinearMap r)) (z • u)) =
        ((1 + θ) * z) • u + ((θ * c) * z) • w := by
    intro z
    have hHe : H (u + c • w) (z • u) = z * H u u := by
      rw [hadd₁, hsm₁', hsm₂, hsm₂, hHwu, mul_zero, mul_zero, add_zero]
    rw [unitaryTransvection_apply, hHe, ← haH]
    module
  have hgr : g.1 ^ ringChar K = 1 :=
    orthU_pow_ringChar_of_blockGL_eq hx hr (orthU_unitaryTransvection_eq H hadd₂ hsm₂ he a ▸ hg)
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, hgr, fun z => ?_, fun z z' => ?_⟩
  · rw [blockDet_apply, hg]
    exact det_unitaryTransvection H hadd₂ hsm₂ he a
  · have h1 := coe_blockGL (Q := Q) (x := x) r g (z • u)
    rw [hg, hact, Submodule.coe_add] at h1
    exact h1.symm
  · have hbar1 : hU.bar (1 + θ) = 1 - θ := by rw [map_add, map_one, hθ']; ring
    rw [hpolar, hpolar, map_mul hU.bar (1 + θ) z, hbar1]
    congr 1
    ring

end Mixing

section PivotsMix

open Polynomial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

omit [Finite K] [FiniteDimensional K V] in
theorem orthU_exists_pivot_of_data_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) {g : V ≃ₗ[K] V} (hgH : g ∈ orthUSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s t : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (htP : t ∈ planeFixSpace E ⊔ lineSpace N)
    (hs0 : s ≠ 0) (hsQ : Q s = 0) (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0)
    (hs3 : polar Q s t = 0) (htw : polar Q t p₂ = 0) (htσ : polar Q t p₁ ≠ 0) :
    ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthUSpan Q E) s₀ := by
  classical
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hLP : ∀ a ∈ lineSpace L, ∀ y ∈ planeFixSpace E ⊔ lineSpace N, polar Q a y = 0 :=
    fun a ha y hy => polar_eq_zero_of_mem_sup hK hN hL hLN ha hy
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hθ : polar Q (g σ) t ≠ 0 := by
    rw [hgσ, polar_add_left, hLP a₁ ha₁ t htP, zero_add, polar_comm]
    exact htσ
  have hcomm := eichler_conj_pivot (Q := Q) (σ := g σ) (w := g w) (s := s) (t := t)
    (by rw [hQg, hQσ]) (by rw [hQg, hQw]) hsQ (by rw [hOg, hσw])
    (by rw [hgσ, polar_add_left, hLP a₁ ha₁ s hsP, zero_add, polar_comm, hs1])
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2]) hs3
    (by rw [hgw, polar_add_left, hLP a₂ ha₂ t htP, zero_add, polar_comm, htw])
  have hY : eichler Q s t ∈ orthUSpan Q E := orthU_eichler_mem_of_mem_sup hEΩ hN0 hsP htP
  have hZ : eichler Q (g σ) (g w) ∈ orthUSpan Q E := by
    rw [← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (orthU_eichler_mem_of_mem_sup hEΩ hL0 hσU hwU))
      (Subgroup.inv_mem _ hgH)
  have hW : eichler Q (g w) (polar Q (g σ) t • s) ∈ orthUSpan Q E := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hZ)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hY hZ) (Subgroup.inv_mem _ hY))
    rw [hcomm, ← mul_assoc, inv_mul_cancel, one_mul] at this
    exact this
  set θ : K := polar Q (g σ) t with hθdef
  have hQw' : Q (g w) = 0 := by rw [hQg, hQw]
  have hQs' : Q (θ • s) = 0 := by rw [map_smul_eq_sq, hsQ, mul_zero]
  have hpol : polar Q (g w) (θ • s) = 0 := by
    rw [polar_smul_right_eq, hgw, polar_add_left, hLP a₂ ha₂ s hsP, zero_add, polar_comm, hs2,
      mul_zero]
  have hdec : -(g w) = -p₂ + -a₂ := by
    rw [hgw]
    abel
  have hv1 : polar Q (θ • s) (-p₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, hs2]
    ring
  have hv2 : polar Q (θ • s) (-a₂) = 0 := by
    rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
    ring
  have hmulE : eichler Q (θ • s) (-p₂) * eichler Q (θ • s) (-a₂) =
      eichler Q (θ • s) (-(g w)) := by
    rw [eichler_mul hv1 hv2, ← hdec]
  have hθsP : θ • s ∈ planeFixSpace E ⊔ lineSpace N := Submodule.smul_mem _ _ hsP
  have hE1 : eichler Q (θ • s) (-p₂) ∈ orthUSpan Q E :=
    orthU_eichler_mem_of_mem_sup hEΩ hN0 hθsP (Submodule.neg_mem _ hp₂)
  have hE2 : eichler Q (θ • s) (-(g w)) ∈ orthUSpan Q E := by
    rw [← eichler_swap hQw' hQs' hpol]
    exact hW
  have hE3 : eichler Q (θ • s) (-a₂) ∈ orthUSpan Q E := by
    have : eichler Q (θ • s) (-a₂) =
        (eichler Q (θ • s) (-p₂))⁻¹ * eichler Q (θ • s) (-(g w)) := by
      rw [← hmulE]
      group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hE1) hE2
  refine ⟨θ • s, hθsP, smul_ne_zero hθ hs0, hQs', -a₂, (lineSpace L).neg_mem ha₂,
    neg_ne_zero.mpr ha₂0, ?_, hE3⟩
  rw [polar_smul_left_eq, polar_neg_right, polar_comm Q s a₂, hLP a₂ ha₂ s hsP]
  ring

theorem orthU_exists_pivot_center_lineSpace (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    (hpiv : ∃ s₀ ∈ planeFixSpace E ⊔ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L,
      b ≠ 0 ∧ b ∈ rootSet Q (orthUSpan Q E) s₀) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthUSpan Q E) s₀ := by
  obtain ⟨s₀, hs₀P, hs₀0, hs₀Q, b, hbL, hb0, hbR⟩ := hpiv
  obtain ⟨s₁, hs₁N, hs₁0, hs₁Q⟩ := exists_singular_of_three_le_any (Q := Q) h3N
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  obtain ⟨g, hg, hgs⟩ := exists_mem_eichlerGroupOn_apply_eq_of_pairs (regular_sup hK hN) hPN hs₀P
    (Submodule.mem_sup_right hs₁N) hs₀0 hs₁0 (by rw [hs₀Q, hs₁Q])
  have hgH : g ∈ orthUSpan Q E :=
    eichlerGroupOn_le (fun e he w hw => orthU_eichler_mem_of_mem_sup hEΩ hN0 he hw) hg
  have hgb : g b = b := eichlerGroupOn_apply_of_orth hg
    (fun u hu => polar_eq_zero_of_mem_sup hK hN hL hLN hbL hu)
  have := rootSet_map (orthUSpan_le_orthogonalGroup E) hgH hbR
  rw [hgb, hgs] at this
  exact ⟨s₁, hs₁N, hs₁0, hs₁Q, b, hbL, hb0, this⟩

theorem orthU_exists_pivot_of_triple (hK : KernelLineData Q p E)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) (hp : p.Prime) {L N : Subgroup E}
    (hL : Nat.card L = p) (hN : Nat.card N = p) (hLN : L ≠ N)
    (hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N))
    {g : V ≃ₗ[K] V} (hgH : g ∈ orthUSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {σ w a₁ a₂ p₁ p₂ s : V}
    (hσU : σ ∈ planeFixSpace E ⊔ lineSpace L) (hwU : w ∈ planeFixSpace E ⊔ lineSpace L)
    (hQσ : Q σ = 0) (hQw : Q w = 0) (hσw : polar Q σ w = 0) (ha₁ : a₁ ∈ lineSpace L)
    (ha₂ : a₂ ∈ lineSpace L) (hp₁ : p₁ ∈ planeFixSpace E ⊔ lineSpace N)
    (hp₂ : p₂ ∈ planeFixSpace E ⊔ lineSpace N)
    (hgσ : g σ = a₁ + p₁) (hgw : g w = a₂ + p₂) (ha₂0 : a₂ ≠ 0)
    (hsP : s ∈ planeFixSpace E ⊔ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0)
    (hs1 : polar Q s p₁ = 0) (hs2 : polar Q s p₂ = 0) (hind : ∀ c₁ c₂ : K, p₁ ≠ c₁ • s + c₂ • p₂) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthUSpan Q E) s₀ := by
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)
  obtain ⟨t, htP, hts, htw, htσ⟩ := exists_perp_not_perp_two hPreg hp₁ hsP hp₂ hind
  exact orthU_exists_pivot_center_lineSpace hK hEΩ hp hL hN hLN hPN h3N
    (orthU_exists_pivot_of_data_gen hK hp hEΩ hL hN hLN hgH hgO hσU hwU hQσ hQw hσw ha₁ ha₂ hp₂ hgσ
      hgw ha₂0 hsP htP hs0 hsQ hs1 hs2 (by rw [polar_comm]; exact hts) htw htσ)

theorem orthU_exists_pivot_of_mixing_gen (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N) (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιA : Function.Injective ιA) (hιB : Function.Injective ιB) (hα : Function.Injective α)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthUSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg0 : ∀ v ∈ planeFixSpace E, g v = v)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (h5L : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace L))
    (h5N : 5 ≤ finrank K ↥(planeFixSpace E ⊔ lineSpace N)) (h3N : 3 ≤ finrank K ↥(lineSpace N)) :
    ∃ s₀ ∈ lineSpace N, s₀ ≠ 0 ∧ Q s₀ = 0 ∧ ∃ b ∈ lineSpace L, b ≠ 0 ∧
      b ∈ rootSet Q (orthUSpan Q E) s₀ := by
  classical
  have hU₀reg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace L) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hL)
  have hPreg : PolarNondegOn Q (planeFixSpace E ⊔ lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) := hasOrthPairs_of_dim hPreg h5N
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  have hdisj : Disjoint (planeFixSpace E) (lineSpace N) := disjoint_planeFixSpace_lineSpace hK hN
  obtain ⟨σ, f₁, w, f₂, hσU, hf₁U, hwU, hf₂U, hQσ, hQf₁, hQw, hQf₂, h11, h22, h12, h1f2, hf1w,
    hf1f2⟩ := hasOrthPairs_of_dim hU₀reg h5L
  obtain ⟨σ₀, hσ₀, σL, hσL, hσeq⟩ := Submodule.mem_sup.mp hσU
  obtain ⟨w₀, hw₀, wL, hwL, hweq⟩ := Submodule.mem_sup.mp hwU
  rw [hLA] at hσL hwL
  obtain ⟨z₁, hz₁⟩ := hσL
  obtain ⟨z₂, hz₂⟩ := hwL
  have hσdec : σ = σ₀ + ιA z₁ := by rw [hz₁, hσeq]
  have hwdec : w = w₀ + ιA z₂ := by rw [hz₂, hweq]
  have hwf1 : polar Q w f₁ = 0 := by rw [polar_comm]; exact hf1w
  have hz₂0 : z₂ ≠ 0 := by
    intro h0
    have hw0 : w = w₀ := by rw [hwdec, h0, map_zero, add_zero]
    have : w = 0 := haniso w (hw0 ▸ hw₀) hQw
    have := h22
    rw [‹w = 0›, polar_zero_left] at this
    exact zero_ne_one this
  have hind : ∀ c : K, z₁ ≠ c • z₂ := by
    intro c hc
    have hσc : σ - c • w = σ₀ - c • w₀ := by
      rw [hσdec, hwdec, hc, map_smul]
      module
    have hmem : σ - c • w ∈ planeFixSpace E := by
      rw [hσc]; exact (planeFixSpace E).sub_mem hσ₀ ((planeFixSpace E).smul_mem _ hw₀)
    have hQ0 : Q (σ - c • w) = 0 := by
      rw [map_sub_smul', hQσ, hQw, h12]; ring
    have h0 : σ - c • w = 0 := haniso _ hmem hQ0
    have := congrArg (fun v => polar Q v f₁) h0
    simp only [polar_sub_left, polar_smul_left_eq, polar_zero_left, h11, hwf1] at this
    simp at this
  obtain ⟨p₁, hp₁def⟩ : ∃ p₁ : V, p₁ = σ₀ + ιB (β z₁) := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ p₂ : V, p₂ = w₀ + ιB (β z₂) := ⟨_, rfl⟩
  have hp₁P : p₁ ∈ planeFixSpace E ⊔ lineSpace N := hp₁def ▸ Submodule.add_mem_sup hσ₀ (hιBN _)
  have hp₂P : p₂ ∈ planeFixSpace E ⊔ lineSpace N := hp₂def ▸ Submodule.add_mem_sup hw₀ (hιBN _)
  have hgσ : g σ = ιA (α z₁) + p₁ := by
    rw [hσdec, map_add, hg0 σ₀ hσ₀, hgact, hp₁def]
    abel
  have hgw : g w = ιA (α z₂) + p₂ := by
    rw [hwdec, map_add, hg0 w₀ hw₀, hgact, hp₂def]
    abel
  have hli : ∀ c₁ c₂ : K, c₁ • p₁ + c₂ • p₂ = 0 → c₁ = 0 ∧ c₂ = 0 := by
    intro c₁ c₂ h0
    have h1 : (c₁ • σ₀ + c₂ • w₀) + ιB (β (c₁ • z₁ + c₂ • z₂)) = 0 := by
      rw [← h0, hp₁def, hp₂def]
      simp only [map_add, map_smul]
      module
    have hmem0 : c₁ • σ₀ + c₂ • w₀ ∈ planeFixSpace E :=
      (planeFixSpace E).add_mem ((planeFixSpace E).smul_mem _ hσ₀)
        ((planeFixSpace E).smul_mem _ hw₀)
    have h2 : c₁ • σ₀ + c₂ • w₀ = 0 :=
      Submodule.disjoint_def.mp hdisj _ hmem0 (by
        rw [eq_neg_of_add_eq_zero_left h1]
        exact (lineSpace N).neg_mem (hιBN _))
    have h3 : c₁ • z₁ + c₂ • z₂ = 0 := by
      rw [h2, zero_add] at h1
      have h4 : β (c₁ • z₁ + c₂ • z₂) = 0 := hιB (by rw [h1, map_zero])
      exact hβ (by rw [h4, map_zero])
    have hc₁ : c₁ = 0 := by
      by_contra hc
      refine hind (-(c₁⁻¹ * c₂)) ?_
      have h5 : c₁ • z₁ = -(c₂ • z₂) := eq_neg_of_add_eq_zero_left h3
      calc z₁ = c₁⁻¹ • (c₁ • z₁) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = (-(c₁⁻¹ * c₂)) • z₂ := by rw [h5, smul_neg, smul_smul, neg_smul]
    refine ⟨hc₁, ?_⟩
    rw [hc₁, zero_smul, zero_add] at h3
    exact (smul_eq_zero.mp h3).resolve_right hz₂0
  obtain ⟨s, hsP, hs0, hsQ, hsF⟩ := exists_singular_in_kernel_fin (Q := Q) (n := 2) (by omega)
    ![(polarBilin Q).flip p₁, (polarBilin Q).flip p₂]
  have hs1 : polar Q s p₁ = 0 := by simpa [polarBilin_apply_apply] using hsF 0
  have hs2 : polar Q s p₂ = 0 := by simpa [polarBilin_apply_apply] using hsF 1
  have hss : polar Q s s = 0 := polar_self_eq_zero hsQ
  have ha₂0 : ιA (α z₂) ≠ 0 := (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr hz₂0)
  by_cases hcase : ∃ c₁ c₂ : K, p₁ = c₁ • s + c₂ • p₂
  · obtain ⟨c₁, c₂, hc⟩ := hcase
    have hc₁ : c₁ ≠ 0 := by
      rintro rfl
      exact one_ne_zero (hli 1 (-c₂) (by rw [hc]; module)).1
    have hŝU : c₁⁻¹ • (σ - c₂ • w) ∈ planeFixSpace E ⊔ lineSpace L :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hσU (Submodule.smul_mem _ _ hwU))
    have hQŝ : Q (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [map_smul_eq_sq, map_sub_smul', hQσ, hQw, h12]
      ring
    have hσŝ : polar Q σ (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQσ, h12]
      ring
    have hwŝ : polar Q w (c₁⁻¹ • (σ - c₂ • w)) = 0 := by
      rw [polar_smul_right_eq, polar_sub_right, polar_smul_right_eq, polar_self_eq_zero hQw,
        polar_comm Q w σ, h12]
      ring
    have hgŝ : g (c₁⁻¹ • (σ - c₂ • w)) =
        ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) + s := by
      have h1 : p₁ - c₂ • p₂ = c₁ • s := by rw [hc]; module
      have h2 : s = c₁⁻¹ • (p₁ - c₂ • p₂) := by rw [h1, smul_smul, inv_mul_cancel₀ hc₁, one_smul]
      rw [map_smul, map_sub, map_smul, hgσ, hgw, h2]
      simp only [map_smul, map_sub]
      module
    have hâ0 : ιA (α (c₁⁻¹ • (z₁ - c₂ • z₂))) ≠ 0 := by
      refine (map_ne_zero_iff ιA hιA).mpr ((map_ne_zero_iff α hα).mpr ?_)
      exact smul_ne_zero (inv_ne_zero hc₁) (sub_ne_zero.mpr (hind c₂))
    by_cases hc₂ : c₂ = 0
    ·
      refine orthU_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := w)
        (w := c₁⁻¹ • (σ - c₂ • w)) hwU hŝU hQw hQŝ hwŝ (hιAL _) (hιAL _) hp₂P hsP hgw hgŝ hâ0
        hsP hs0 hsQ hs2 hss ?_
      intro d₁ d₂ hd
      have h1 : p₂ = (d₁ + d₂) • s := by rw [hd]; module
      have h2 : p₁ = c₁ • s := by rw [hc, hc₂]; module
      have := hli (-(d₁ + d₂)) c₁ (by rw [h2, h1]; module)
      exact hc₁ this.2
    · refine orthU_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO (σ := σ)
        (w := c₁⁻¹ • (σ - c₂ • w)) hσU hŝU hQσ hQŝ hσŝ (hιAL _) (hιAL _) hp₁P hsP hgσ hgŝ hâ0
        hsP hs0 hsQ hs1 hss ?_
      intro d₁ d₂ hd
      have hcp : c₂ • p₂ = (d₁ + d₂ - c₁) • s := by
        have : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [this] at hc
        rw [sub_smul, hc]
        module
      have := hli (d₁ + d₂ - c₁) (-((d₁ + d₂) * c₂)) (by
        have hd' : p₁ = (d₁ + d₂) • s := by rw [hd]; module
        rw [hd']
        have : ((d₁ + d₂) * c₂) • p₂ = (d₁ + d₂) • (c₂ • p₂) := by rw [mul_smul]
        rw [neg_smul, this, hcp]
        module)
      obtain ⟨h5, h6⟩ := this
      have h7 : d₁ + d₂ = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h6)).resolve_right hc₂
      exact hc₁ (by linear_combination h7 - h5)
  · push Not at hcase
    exact orthU_exists_pivot_of_triple hK hEΩ hp hL hN hLN hPN h3N hgH hgO hσU hwU hQσ hQw h12
      (hιAL _) (hιAL _) hp₁P hp₂P hgσ hgw ha₂0 hsP hs0 hsQ hs1 hs2 hcase


theorem orthU_exists_d4_pivot (hK : KernelLineData Q p E) (hp : p.Prime)
    (hEΩ : elementaryGroup Q ≤ orthDerived Q) {L N : Subgroup E} (hL : Nat.card L = p)
    (hN : Nat.card N = p) (hLN : L ≠ N)
    {W : Type} [AddCommGroup W] [Module K W] (ιA ιB : W →ₗ[K] V) (α β : W →ₗ[K] W)
    (hιB : Function.Injective ιB) (hα : Function.Injective α) (hιA : Function.Injective ιA)
    (hβ : Function.Injective β) (hLA : lineSpace L = LinearMap.range ιA)
    (hW4 : 4 ≤ finrank K W) (hsurj : ∀ s ∈ lineSpace N, ∃ z, ιB (β z) = s)
    (g : V ≃ₗ[K] V) (hgH : g ∈ orthUSpan Q E)
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgact : ∀ z, g (ιA z) = ιA (α z) + ιB (β z)) (hιBN : ∀ z, ιB z ∈ lineSpace N)
    (hstar : ∀ z : W, z ≠ 0 → ∀ c : K, ∃ z' : W,
      polar Q (ιA z') (ιA z) ≠ c * polar Q (ιB (β z')) (ιB (β z)))
    {s : V} (hsN : s ∈ lineSpace N) (hs0 : s ≠ 0) (hsQ : Q s = 0) :
    ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthUSpan Q E) s := by
  classical
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  have hAN : ∀ v ∈ lineSpace L, ∀ w ∈ lineSpace N, polar Q v w = 0 :=
    orthSep_lineSpace hK hL hN hLN
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hιAL : ∀ z, ιA z ∈ lineSpace L := fun z => hLA ▸ ⟨z, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : W →ₗ[K] V, b = ιB ∘ₗ β := ⟨_, rfl⟩
  have hbapp : ∀ z, b z = ιB (β z) := fun z => by rw [hb]; rfl
  have hbinj : Function.Injective b := fun z z' h =>
    hβ (hιB (by rw [← hbapp, ← hbapp]; exact h))
  have hbN : ∀ z, b z ∈ lineSpace N := fun z => by rw [hbapp]; exact hιBN _
  have hQg := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have hOg := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgO
  let QW : QuadraticForm K W := Q.comp ιA
  have hQW : ∀ z, QW z = Q (ιA z) := fun z => rfl
  have hpolW : ∀ z z', polar QW z z' = polar Q (ιA z) (ιA z') := fun z z' => by
    simp only [QuadraticMap.polar, QW, QuadraticMap.comp_apply, map_add]
  let ℓ : W →ₗ[K] K := (polarBilin Q).flip s ∘ₗ b
  have hℓ : ∀ z, ℓ z = polar Q (b z) s := fun z => by simp [ℓ, polarBilin_apply_apply]
  obtain ⟨ŝ, hŝ⟩ := hsurj s hsN
  have hbŝ : b ŝ = s := by rw [hbapp, hŝ]
  have hŝ0 : ŝ ≠ 0 := by
    rintro rfl
    exact hs0 (by rw [← hbŝ, map_zero])
  have hℓŝ : ℓ ŝ = 0 := by rw [hℓ, hbŝ]; exact polar_self_eq_zero hsQ
  have h3 : 3 ≤ finrank K ↥(LinearMap.ker ℓ) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker ℓ
    have h2 : finrank K (LinearMap.range ℓ) ≤ 1 := by
      have := Submodule.finrank_le (LinearMap.range ℓ)
      simpa using this
    omega
  have hstar' : ∀ c : K, ∃ z, polar QW z ŝ ≠ c * ℓ z := by
    intro c
    obtain ⟨z', hz'⟩ := hstar ŝ hŝ0 c
    refine ⟨z', ?_⟩
    have : polar Q (b z') s = polar Q (ιB (β z')) (ιB (β ŝ)) := by rw [hbapp, hŝ]
    rw [hpolW, hℓ, this]
    exact hz'
  obtain ⟨z₁, z₂, hz₁ℓ, hz₂ℓ, hz₁Q, hz₁0, hz₁z₂, hind, hspan⟩ :=
    exists_d4_choice QW ℓ ŝ h3 hℓŝ hŝ0 hstar'
  have hz₁s : polar Q (b z₁) s = 0 := by rw [← hℓ]; exact hz₁ℓ
  have hz₂s : polar Q (b z₂) s = 0 := by rw [← hℓ]; exact hz₂ℓ
  have hind' : ∀ c₁ c₂ : K, b z₁ ≠ c₁ • s + c₂ • b z₂ := by
    intro c₁ c₂ h
    apply hind c₁ c₂
    apply hbinj
    rw [map_add, map_smul, map_smul, hbŝ]
    exact h
  obtain ⟨t, htN, hts, htb₂, htb₁⟩ := exists_perp_not_perp_two hNreg (hbN z₁) hsN (hbN z₂) hind'
  obtain ⟨u, hu⟩ : ∃ u, u = g (ιA z₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = g (ιA z₂) := ⟨_, rfl⟩
  have hu' : u = ιA (α z₁) + b z₁ := by rw [hu, hgact, hbapp]
  have hy' : y = ιA (α z₂) + b z₂ := by rw [hy, hgact, hbapp]
  have huQ : Q u = 0 := by rw [hu, hQg, ← hQW, hz₁Q]
  have huy : polar Q u y = 0 := by rw [hu, hy, hOg, ← hpolW, hz₁z₂]
  have hus : polar Q u s = 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) s hsN, zero_add, hz₁s]
  have hsy : polar Q s y = 0 := by
    rw [hy', polar_add_right, polar_comm Q s (ιA (α z₂)), hAN _ (hιAL _) s hsN, zero_add,
      polar_comm, hz₂s]
  have hst : polar Q s t = 0 := by rw [polar_comm]; exact hts
  have hyt : polar Q y t = 0 := by
    rw [hy', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm, htb₂]
  have hθ : polar Q u t ≠ 0 := by
    rw [hu', polar_add_left, hAN _ (hιAL _) t htN, zero_add, polar_comm]
    exact htb₁
  have hC : eichler Q s t ∈ orthUSpan Q E :=
    orthU_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN) (Submodule.mem_sup_right htN)
  have hE : eichler Q u y ∈ orthUSpan Q E := by
    rw [hu, hy, ← eichler_conj hgO]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgH (orthU_eichler_mem_of_mem_sup hEΩ hL0
      (Submodule.mem_sup_right (hιAL z₁)) (Submodule.mem_sup_right (hιAL z₂))))
      (Subgroup.inv_mem _ hgH)
  have hmem := eichler_pivot_mem huQ hsQ hus huy hsy hst hyt hC hE
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = polar Q u t := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = Q y := ⟨_, rfl⟩
  rw [← hθdef, ← hcdef] at hmem
  obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ = -(θ • ιA (α (z₂ + c • z₁))) := ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = -(θ • (b z₂ + c • b z₁)) := ⟨_, rfl⟩
  have hsplit : -(θ • (y + c • u)) = y₀ + n₀ := by
    rw [hy', hu', hy₀, hn₀]
    simp only [map_add, map_smul]
    module
  have hy₀L : y₀ ∈ lineSpace L := by
    rw [hy₀]
    exact (lineSpace L).neg_mem ((lineSpace L).smul_mem _ (hιAL _))
  have hn₀N : n₀ ∈ lineSpace N := by
    rw [hn₀]
    exact (lineSpace N).neg_mem ((lineSpace N).smul_mem _ ((lineSpace N).add_mem (hbN _)
      ((lineSpace N).smul_mem _ (hbN _))))
  have hsy₀ : polar Q s y₀ = 0 := by
    rw [polar_comm]
    exact hAN _ hy₀L s hsN
  have hsn₀ : polar Q s n₀ = 0 := by
    rw [hn₀, polar_neg_right, polar_smul_right_eq, polar_add_right, polar_smul_right_eq,
      polar_comm Q s (b z₂), polar_comm Q s (b z₁), hz₂s, hz₁s]
    ring
  have hn₀H : eichler Q s n₀ ∈ orthUSpan Q E :=
    orthU_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN)
      (Submodule.mem_sup_right hn₀N)
  have hy₀H : eichler Q s y₀ ∈ orthUSpan Q E := by
    have h1 : eichler Q s y₀ * eichler Q s n₀ = eichler Q s (y₀ + n₀) := eichler_mul hsy₀ hsn₀
    have h2 : eichler Q s y₀ = eichler Q s (y₀ + n₀) * (eichler Q s n₀)⁻¹ := by
      rw [← h1]
      group
    rw [h2, ← hsplit]
    exact Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hn₀H)
  refine ⟨y₀, hy₀L, ?_, hsy₀, hy₀H⟩
  rw [hy₀]
  refine neg_ne_zero.mpr (smul_ne_zero (hθdef ▸ hθ) ((map_ne_zero_iff ιA hιA).mpr
    ((map_ne_zero_iff α hα).mpr fun h0 => hspan (-c) ?_)))
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left h0


end PivotsMix

section SelfDual

open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem orthU_closure_eq_top_of_selfdual_or_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : (2 : K) ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) (hsd : HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ ∨
      (finrank K ↥(planeFixSpace E) = 0 ∧ finrank K V = 8) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
  obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hL hN hLN hVL hVN
  have hx0 := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have haL : a ∉ L := not_mem_line_of_primary hx0 hh hne1 hvL hvh hv0
  have haN : a ∉ N := not_mem_line_of_primary hx0 hh hne1 hwN hwh hw0
  obtain ⟨x, hxa⟩ : ∃ x : V ≃ₗ[K] V, x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V) := ⟨_, rfl⟩
  rw [← hxa] at hh hvh hwh hm2 hx0
  have hx : OddOrderIsometry Q p x := hx0
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    obtain ⟨a₁, ha₁, ha₁1, h₁, hh₁, hne₁, hself₁⟩ := hsd
    have : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
    have hx₁ := oddOrderIsometry_of_mem hQ hp hpl hK (x := (⟨a₁, ha₁⟩ : E))
      (fun e => ha₁1 (congrArg Subtype.val e))
    obtain ⟨d, -, -, -, -, -, hroot, -⟩ := hx₁.selfDualModel hodd hh₁ hne₁ hself₁
    exact selfDual_of_dvd hx hh (hx₁.dvd_card_pow_add_one hp hh₁ hne₁ hroot)
  have hStL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hStN : ∀ s ∈ lineSpace N, x s ∈ lineSpace N := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm N a hs
  have hneL : lineSpace L ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hv0 (by
    have : v ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hvL, hvh⟩
    simpa using this)
  have hneN : lineSpace N ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hw0 (by
    have : w ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hwN, hwh⟩
    simpa using this)
  obtain ⟨g, hgS, hgr, u, w', hu, hw', hu0, hw0', hureg, hwreg, lam, mu, hlam, hmu, hact⟩ :
      ∃ g ∈ specialBlock Q x h, g ^ ringChar K = 1 ∧ ∃ u w' : primaryComponent x.toLinearMap h,
        (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
        PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
        PolarNondegOn Q (LinearMap.range (eline x h w')) ∧
        ∃ lam mu : AdjoinRoot h, lam ≠ 0 ∧ mu ≠ 0 ∧ ∀ z : AdjoinRoot h,
          g (eline x h u z) = eline x h u (lam * z) + eline x h w' (mu * z) := by
    obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
      (hK.regular (some ⟨L, hL⟩)) hneL
    obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
      (hK.regular (some ⟨N, hN⟩)) hneN
    obtain ⟨g, hgS, hgr, u, w', hu, hw', hQu, hQw', hureg, hwreg, lam, mu, hlam, hmu, hact⟩ :=
      orthU_exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN
        (orthSep_lineSpace hK hL hN hLN) ⟨u₀, hu₀, hQu₀⟩ ⟨w₀, hw₀, hQw₀⟩
    exact ⟨g, hgS, hgr, u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
      fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg, lam, mu, hlam, hmu, hact⟩
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
  have hLr : lineSpace L = LinearMap.range (eline x h u) :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hL hN hLN hVN haL hxa u hu hu0 hureg
  have hNr : lineSpace N = LinearMap.range (eline x h w') :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hN hL hLN.symm hVL haN hxa w' hw' hw0' hwreg
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdimL : finrank K ↥(lineSpace L) = h.natDegree := by
    rw [hLr, LinearMap.finrank_range_of_inj (eline_injective h hu0), hfin]
  have hdimN : finrank K ↥(lineSpace N) = h.natDegree := by
    rw [hNr, LinearMap.finrank_range_of_inj (eline_injective h hw0'), hfin]
  have hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥ := by
    intro M hM hML hMN
    by_contra hne
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hne with h' | h'
    · exact hML h'
    · exact hMN h'
  have hn := finrank_eq_of_two_active hK hL hN hLN hother
  have hV₀ : finrank K ↥(planeFixSpace E) ≤ 2 := by
    by_contra hcon
    obtain ⟨e, he, he0, heQ⟩ := exists_singular_of_three_le_any (Q := Q)
      (S := planeFixSpace E) (by omega)
    exact he0 (haniso e he heQ)
  by_cases hD : 0 < finrank K ↥(planeFixSpace E) ∨ 8 < finrank K V
  swap
  · right
    push Not at hD
    omega
  left
  have h3N : 3 ≤ finrank K ↥(lineSpace N) := by omega
  have hdimUL : finrank K ↥(planeFixSpace E ⊔ lineSpace L) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hL), hdimL]
  have hdimUN : finrank K ↥(planeFixSpace E ⊔ lineSpace N) =
      finrank K ↥(planeFixSpace E) + h.natDegree := by
    rw [finrank_sup_of_disjoint (disjoint_planeFixSpace_lineSpace hK hN), hdimN]
  have h5 : 5 ≤ finrank K ↥(planeFixSpace E) + h.natDegree := by omega
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthUSpan Q E := by
    refine orthU_mem_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_ hgr
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hg0 : ∀ v ∈ planeFixSpace E, g v = v := fun v hv =>
    (mem_supportedBlock.mp (specialBlock_le_supportedBlock h hgS)).2 v
      (fixedSpace_le_othersSpace hne1 hself (mem_fixedSpace.mpr (by
        rw [hxa]; exact apply_eq_of_mem_planeFixSpace a hv)))
  have hpiv := orthU_exists_pivot_of_mixing_gen hK hp hEΩ hL hN hLN haniso (eline x h u)
    (eline x h w') (LinearMap.mulLeft K lam) (LinearMap.mulLeft K mu) (eline_injective h hu0)
    (eline_injective h hw0') (mul_right_injective₀ hlam) (mul_right_injective₀ hmu) hLr g hgH hgO
    hg0 hact (fun z => smul_mem_of_stable hStN z w' hw') (by omega) (by omega) h3N
  have hPN : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace N) :=
    hasOrthPairs_of_dim (OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hN)) (by omega)
  have hPL : HasOrthPairs Q (planeFixSpace E ⊔ lineSpace L) :=
    hasOrthPairs_of_dim (OrthBlk.polarNondegOn_of_nondegenerate (regular_sup hK hL)) (by omega)
  have hle : elementaryGroup Q ≤ orthUSpan Q E := by
    refine orthU_elementaryGroup_le_of_pivots hK hEΩ hp hQ hN hPN fun M hM hMN hVM => ?_
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hVM with h' | h'
    · subst h'
      exact ⟨hPL, hpiv⟩
    · exact absurd h' hMN
  exact orthU_closure_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

theorem orthU_closure_eq_top_of_selfdual_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (hsd : HasSelfDualFactor Q E) (hV0 : finrank K ↥(planeFixSpace E) = 0)
    (hV8 : finrank K V = 8) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  obtain ⟨L, N, hL, hN, hLN, hVL, hVN⟩ := hK.two_active
  have hN0 : N ≠ ⊥ := ne_bot_of_card_prime hp hN
  have hL0 : L ≠ ⊥ := ne_bot_of_card_prime hp hL
  obtain ⟨a, ha, h, hh, hne1, hm2, ⟨v, hvL, hvh, hv0⟩, ⟨w, hwN, hwh, hw0⟩⟩ :=
    exists_mixing_factor_orth hQ hp hpl hK hL hN hLN hVL hVN
  have hx0 := oddOrderIsometry_of_mem hQ hp hpl hK ha
  have haL : a ∉ L := not_mem_line_of_primary hx0 hh hne1 hvL hvh hv0
  have haN : a ∉ N := not_mem_line_of_primary hx0 hh hne1 hwN hwh hw0
  obtain ⟨x, hxa⟩ : ∃ x : V ≃ₗ[K] V, x = (((a : E) : orthDerived Q) : V ≃ₗ[K] V) := ⟨_, rfl⟩
  rw [← hxa] at hh hvh hwh hm2 hx0
  have hx : OddOrderIsometry Q p x := hx0
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hself : h = reciprocalPolynomial h := by
    obtain ⟨a₁, ha₁, ha₁1, h₁, hh₁, hne₁, hself₁⟩ := hsd
    have : Fact (Irreducible h₁) := ⟨irreducible_of_mem_primaryFactors hh₁⟩
    have hx₁ := oddOrderIsometry_of_mem hQ hp hpl hK (x := (⟨a₁, ha₁⟩ : E))
      (fun e => ha₁1 (congrArg Subtype.val e))
    obtain ⟨d, -, -, -, -, -, hroot, -⟩ := hx₁.selfDualModel hodd hh₁ hne₁ hself₁
    exact selfDual_of_dvd hx hh (hx₁.dvd_card_pow_add_one hp hh₁ hne₁ hroot)
  have hStL : ∀ s ∈ lineSpace L, x s ∈ lineSpace L := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm L a hs
  have hStN : ∀ s ∈ lineSpace N, x s ∈ lineSpace N := fun s hs => by
    rw [hxa]; exact lineSpace_stable hK.comm N a hs
  have hneL : lineSpace L ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hv0 (by
    have : v ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hvL, hvh⟩
    simpa using this)
  have hneN : lineSpace N ⊓ primaryComponent x.toLinearMap h ≠ ⊥ := fun h0 => hw0 (by
    have : w ∈ (⊥ : Submodule K V) := h0 ▸ ⟨hwN, hwh⟩
    simpa using this)
  have hAN : ∀ s ∈ lineSpace L, ∀ t ∈ lineSpace N, polar Q s t = 0 :=
    orthSep_lineSpace hK hL hN hLN
  obtain ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩ : ∃ u w' : primaryComponent x.toLinearMap h,
      (u : V) ∈ lineSpace L ∧ (w' : V) ∈ lineSpace N ∧ u ≠ 0 ∧ w' ≠ 0 ∧
      PolarNondegOn Q (LinearMap.range (eline x h u)) ∧
      PolarNondegOn Q (LinearMap.range (eline x h w')) := by
    by_cases h2 : (2 : K) = 0
    · obtain ⟨-, -, u, w', hu, hw', hu0, hw0', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action_even hx hp hp5 hh hne1 hself h2 hStL hStN
          (hK.regular (some ⟨L, hL⟩)) (hK.regular (some ⟨N, hN⟩)) hAN hneL hneN
      exact ⟨u, w', hu, hw', hu0, hw0', hureg, hwreg⟩
    · obtain ⟨u₀, hu₀, hQu₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStL
        (hK.regular (some ⟨L, hL⟩)) hneL
      obtain ⟨w₀, hw₀, hQw₀⟩ := exists_map_ne_zero_of_selfdual hx hh hself hStN
        (hK.regular (some ⟨N, hN⟩)) hneN
      obtain ⟨-, -, u, w', hu, hw', hQu, hQw', hureg, hwreg, -⟩ :=
        exists_selfdual_mixing_action hx hodd hh hne1 hself h2 hStN hAN ⟨u₀, hu₀, hQu₀⟩
          ⟨w₀, hw₀, hQw₀⟩
      exact ⟨u, w', hu, hw', fun h0 => hQu (by rw [h0]; simp),
        fun h0 => hQw' (by rw [h0]; simp), hureg, hwreg⟩
  have hLr : lineSpace L = LinearMap.range (eline x h u) :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hL hN hLN hVN haL hxa u hu hu0 hureg
  have hNr : lineSpace N = LinearMap.range (eline x h w') :=
    lineSpace_eq_range_eline hQ hT hp hp2 hrank hK hN hL hLN.symm hVL haN hxa w' hw' hw0' hwreg
  have hfin : finrank K (AdjoinRoot h) = h.natDegree := by
    rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  have hdimL : finrank K ↥(lineSpace L) = h.natDegree := by
    rw [hLr, LinearMap.finrank_range_of_inj (eline_injective h hu0), hfin]
  have hdimN : finrank K ↥(lineSpace N) = h.natDegree := by
    rw [hNr, LinearMap.finrank_range_of_inj (eline_injective h hw0'), hfin]
  have hother : ∀ M : Subgroup E, Nat.card M = p → M ≠ L → M ≠ N → lineSpace M = ⊥ := by
    intro M hM hML hMN
    by_contra hne
    rcases eq_or_eq_of_active hQ hT hp hp2 hrank hK hL hN hLN hVL hVN hM hne with h' | h'
    · exact hML h'
    · exact hMN h'
  have hn := finrank_eq_of_two_active hK hL hN hLN hother
  obtain ⟨d, hdeg, -⟩ := hx.selfDualModel hodd hh hne1 hself
  have hn4 : h.natDegree = 4 := by omega
  have hd2 : 2 ≤ d := by omega
  have hV0' : planeFixSpace E = ⊥ := Submodule.finrank_eq_zero.mp hV0
  have htop : lineSpace L ⊔ lineSpace N = ⊤ := by
    have := sup_eq_top_of_two_active hK hL hN hother
    rwa [hV0', bot_sup_eq] at this
  obtain ⟨d', hdeg', c, hc0, hfam⟩ :=
    orthU_exists_selfdual_mixing_family hx hodd hh hne1 hself hStN hAN
    u w' hu hw' hu0 hw0' hureg hwreg
  have hdd : d' = d := by omega
  subst hdd
  obtain ⟨θ, hθ, hθK⟩ := exists_trace_zero_sq_not_mem hd2 (by rw [hfin, hdeg'])
  obtain ⟨g, hgS, hgr, hact, hbal⟩ := hfam θ hθ
  have hθ0 : θ ≠ 0 := fun h0 => hθK 0 (by rw [h0]; simp)
  have hlam : 1 + θ ≠ 0 := fun h0 => hθK 1 (by
    have : θ = -1 := eq_neg_of_add_eq_zero_right h0
    rw [this]
    simp)
  have hmu : θ * c ≠ 0 := mul_ne_zero hθ0 hc0
  have hgΩ : g ∈ orthDerived Q := hx.specialBlock_le_orthDerived hp (by omega) hh hne1 hm2 hgS
  obtain ⟨hgQ, hgx⟩ := mem_isometryCentralizer.mp (specialBlock_le_isometryCentralizer h hgS)
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hgQ
  have hgH : g ∈ orthUSpan Q E := by
    refine orthU_mem_of_commute (a := (a : orthDerived Q)) hgΩ a.2
      (fun e => ha (Subtype.ext e)) ?_ hgr
    rw [← hxa]
    exact LinearEquiv.ext fun v => hgx v
  have hιAL : ∀ z, eline x h u z ∈ lineSpace L := fun z => hLr ▸ ⟨z, rfl⟩
  have hιBN : ∀ z, eline x h w' z ∈ lineSpace N := fun z => smul_mem_of_stable hStN z w' hw'
  have hpivot : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      ∃ y ∈ lineSpace L, y ≠ 0 ∧ y ∈ rootSet Q (orthUSpan Q E) s := by
    intro s hsN hs0 hsQ
    refine orthU_exists_d4_pivot hK hp hEΩ hL hN hLN (eline x h u) (eline x h w')
      (LinearMap.mulLeft K (1 + θ)) (LinearMap.mulLeft K (θ * c)) (eline_injective h hw0')
      (mul_right_injective₀ hlam) (eline_injective h hu0) (mul_right_injective₀ hmu) hLr
      (by omega) ?_ g hgH hgO hact hιBN ?_ hsN hs0 hsQ
    · intro s' hs'
      rw [hNr] at hs'
      obtain ⟨z₀, rfl⟩ := hs'
      exact ⟨(θ * c)⁻¹ * z₀, by rw [LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hmu]⟩
    · exact not_proportional_of_mixing (eline x h u) (eline x h w') g hgO (1 + θ) (θ * c)
        (1 - θ ^ 2) hact (fun z z' => hAN _ (hιAL z) _ (hιBN z')) hbal hureg
        (eline_injective h hu0) (fun c' h0 => hθK c' (by rw [← h0]; ring))
  have hAreg : PolarNondegOn Q (lineSpace L) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨L, hL⟩))
  have hNreg : PolarNondegOn Q (lineSpace N) :=
    OrthBlk.polarNondegOn_of_nondegenerate (hK.regular (some ⟨N, hN⟩))
  have hcenter : ∀ s ∈ lineSpace N, s ≠ 0 → Q s = 0 →
      IsRootCenter Q (orthUSpan Q E) s := by
    intro s hsN hs0 hsQ
    obtain ⟨y₀, hy₀L, hy₀0, hy₀R⟩ := hpivot s hsN hs0 hsQ
    have hLR : ∀ a' ∈ lineSpace L, a' ∈ rootSet Q (orthUSpan Q E) s := by
      refine mem_of_invariant_of_ne_zero hAreg (by omega)
        (rootSet Q (orthUSpan Q E) s) ?_ hy₀R hy₀L hy₀0
      intro x₁ hx₁ z₁ hz₁ _ _ m hm _
      have hH : eichler Q x₁ z₁ ∈ orthUSpan Q E :=
        orthU_eichler_mem_of_mem_sup hEΩ hL0 (Submodule.mem_sup_right hx₁)
          (Submodule.mem_sup_right hz₁)
      have hfix : eichler Q x₁ z₁ s = s :=
        eichler_apply_of_polar_eq_zero (by rw [polar_comm]; exact hAN x₁ hx₁ s hsN)
          (by rw [polar_comm]; exact hAN z₁ hz₁ s hsN)
      have := rootSet_map (orthUSpan_le_orthogonalGroup E) hH hm
      rwa [hfix] at this
    refine ⟨hs0, hsQ, fun w₁ hw₁ => ?_⟩
    obtain ⟨a', ha', b, hb, rfl⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := w₁))
    have hsa : polar Q s a' = 0 := by rw [polar_comm]; exact hAN a' ha' s hsN
    have hsb : polar Q s b = 0 := by
      rw [polar_add_right, hsa, zero_add] at hw₁
      exact hw₁
    have hbR : b ∈ rootSet Q (orthUSpan Q E) s :=
      ⟨hsb, orthU_eichler_mem_of_mem_sup hEΩ hN0 (Submodule.mem_sup_right hsN)
        (Submodule.mem_sup_right hb)⟩
    exact ((rootSet Q (orthUSpan Q E) s).add_mem (hLR a' ha') hbR).2
  obtain ⟨a₁, ha₁N, ha₁0, hQa₁⟩ :=
    exists_singular_of_three_le_any (Q := Q) (S := lineSpace N) (by omega)
  obtain ⟨f₁, hf₁N, hQf₁, h11⟩ := exists_partner_of_polarNondegOn hNreg ha₁N hQa₁ ha₁0
  have hf₁0 : f₁ ≠ 0 := fun h0 => by
    rw [h0, polar_zero_right] at h11
    exact zero_ne_one h11
  have hle : elementaryGroup Q ≤ orthUSpan Q E :=
    elementaryGroup_le_of_hypPair hQ (orthUSpan_le_orthogonalGroup E)
      ⟨a₁, f₁, hQa₁, hQf₁, h11⟩ (hcenter a₁ ha₁N ha₁0 hQa₁) (hcenter f₁ hf₁N hf₁0 hQf₁)
  exact orthU_closure_eq_top_of_le E ((orthDerived_eq_and_le_closure hQ hT).1 ▸ hle)

theorem orthU_selfDualTwoBlocks (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : (2 : K) ≠ 0) (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (hrank : RankLE2 p (orthDerived Q))
    (E : Subgroup (orthDerived Q)) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hexp : ∀ x ∈ E, x ^ p = 1) (hcard : Nat.card E = p ^ 2)
    (haniso : ∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) (hsd : HasSelfDualFactor Q E) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  rcases orthU_closure_eq_top_of_selfdual_or_D4 hQ hT hdim h2 hp hp5 hpl hrank E hcomm hexp hcard
    haniso hsd with h | ⟨h0, h8⟩
  · exact h
  · exact orthU_closure_eq_top_of_selfdual_D4 hQ hT hp hp5 hpl hrank E hcomm hexp hcard hsd h0 h8

end SelfDual

section ManyBig

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {E : Subgroup (orthDerived Q)}

theorem orthU_eichler_mem_of_restricted_plane {U : Submodule K V} (hU : PolarNondegOn Q U)
    (hEU : orthDerived (Q.comp U.subtype) = elementaryGroup (Q.comp U.subtype))
    (E : Subgroup (orthDerived Q))
    (hstab : ∀ x : E, ((x : orthDerived Q) : V ≃ₗ[K] V) ∈ stab U)
    (hΩ : elementaryGroup Q ≤ orthDerived Q)
    (ρ : E →* orthDerived (Q.comp U.subtype))
    (hρ : ∀ (x : E) (u : U), (((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) u : V) =
      ((x : orthDerived Q) : V ≃ₗ[K] V) u)
    (hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ ringChar K = 1} = ⊤) :
    ∀ e ∈ U, ∀ w ∈ U, eichler Q e w ∈ orthUSpan Q E := by
  classical
  let φ : orthDerived (Q.comp U.subtype) →* (V ≃ₗ[K] V) :=
    (extU hU).comp (orthDerived (Q.comp U.subtype)).subtype
  have hle : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ ringChar K = 1} ≤ (orthUSpan Q E).comap φ := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, hx1, hhx, hhr⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hhE : extU hU (h : U ≃ₗ[K] U) ∈ eichlerGroupOn Q U :=
      extU_mem_eichlerGroupOn hU (hEU ▸ h.2)
    have hΩmem : extU hU (h : U ≃ₗ[K] U) ∈ orthDerived Q :=
      hΩ (eichlerGroupOn_le_elementaryGroup U hhE)
    have hpow : extU hU (h : U ≃ₗ[K] U) ^ ringChar K = 1 := by
      rw [← map_pow]
      have : (h : U ≃ₗ[K] U) ^ ringChar K = 1 := by
        have := congrArg Subtype.val hhr
        simpa using this
      rw [this, map_one]
    refine orthU_mem_of_commute (a := (x : orthDerived Q)) hΩmem x.2
      (fun h1 => hx1 (Subtype.ext h1)) ?_ hpow
    have hc : Commute (extU hU (h : U ≃ₗ[K] U)) ((x : orthDerived Q) : V ≃ₗ[K] V) := by
      refine commute_of_mem_eichlerGroupOn hU hhE (orthDerived_mem_orthogonalGroup) (hstab x) ?_
      intro u hu
      have hxu : ((x : orthDerived Q) : V ≃ₗ[K] V) u ∈ U := ((mem_stab.mp (hstab x)) u hu).1
      rw [extU_apply_mem hU _ hxu, extU_apply_mem hU _ hu]
      have e1 : (⟨((x : orthDerived Q) : V ≃ₗ[K] V) u, hxu⟩ : U) =
          ((ρ x : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U) ⟨u, hu⟩ :=
        Subtype.ext (hρ x ⟨u, hu⟩).symm
      rw [e1]
      have e2 := hρ x ((h : U ≃ₗ[K] U) ⟨u, hu⟩)
      rw [← e2]
      exact congrArg (fun y : orthDerived (Q.comp U.subtype) =>
        (((y : U ≃ₗ[K] U) ⟨u, hu⟩ : U) : V)) hhx
    exact hc.eq
  intro e he w hw
  have hmem : eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩ ∈
      orthDerived (Q.comp U.subtype) := by
    rw [hEU]
    exact eichler_mem_elementaryGroup _ _ _
  have htop : (⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ : orthDerived (Q.comp U.subtype))
      ∈ Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
        ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ ringChar K = 1} := by
    rw [hgen]
    exact Subgroup.mem_top _
  have := Subgroup.mem_comap.mp (hle htop)
  have e3 : φ ⟨eichler (Q.comp U.subtype) ⟨e, he⟩ ⟨w, hw⟩, hmem⟩ = eichler Q e w :=
    extU_eichler hU ⟨e, he⟩ ⟨w, hw⟩
  rwa [e3] at this

theorem orthU_eichler_mem_of_two_pieces (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h2 : (2 : K) ≠ 0)
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : p ≠ ringChar K) (hK : KernelLineData Q p E) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) {P₁ P₂ : Submodule K V}
    (h₁ : IsPiece Q E P₁) (h₂ : IsPiece Q E P₂) (h12 : OrthSep Q P₁ P₂) {M₁ M₂ : Subgroup E}
    (hM₁ : Nat.card M₁ = p) (hM₂ : Nat.card M₂ = p) (hM12 : M₁ ≠ M₂)
    (hk₁ : ∀ x : E, (∀ u ∈ P₁, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₁)
    (hk₂ : ∀ x : E, (∀ u ∈ P₂, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u) → x ∈ M₂)
    (hf₁ : finrank K P₁ = orderOf ((Nat.card K : ℕ) : ZMod p))
    (hf₂ : finrank K P₂ = orderOf ((Nat.card K : ℕ) : ZMod p)) :
    ∀ x ∈ planeFixSpace E ⊔ P₁ ⊔ P₂, ∀ y ∈ planeFixSpace E ⊔ P₁ ⊔ P₂,
      eichler Q x y ∈ orthUSpan Q E := by
  classical
  have hp2 : p ≠ 2 := by omega
  set U : Submodule K V := planeFixSpace E ⊔ P₁ ⊔ P₂
  have hV0 : PolarNondegOn Q (planeFixSpace E) := polarNondegOn_planeFixSpace hK
  have hP₁U : P₁ ≤ U := le_sup_of_le_left le_sup_right
  have hP₂U : P₂ ≤ U := le_sup_right
  have hU : PolarNondegOn Q U := polarNondegOn_sup (polarNondegOn_sup hV0 h₁.regular
    h₁.orthSep.symm) h₂.regular (manyBig_orthSep_sup_left h₂.orthSep.symm h12)
  have hdisj : Disjoint P₁ P₂ := OrthSep.disjoint h₁.regular h12
  have hdim12 : finrank K ↥(P₁ ⊔ P₂) = finrank K P₁ + finrank K P₂ := by
    have := Submodule.finrank_sup_add_finrank_inf_eq P₁ P₂
    rwa [hdisj.eq_bot, finrank_bot, add_zero] at this
  have hU8 : 8 ≤ finrank K U := by
    have : finrank K ↥(P₁ ⊔ P₂) ≤ finrank K U :=
      Submodule.finrank_mono (sup_le hP₁U hP₂U)
    omega
  have hUle : finrank K U ≤ finrank K (planeFixSpace E) + finrank K P₁ + finrank K P₂ := by
    have h1 : finrank K U ≤ finrank K ↥(planeFixSpace E ⊔ P₁) + finrank K P₂ :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (planeFixSpace E) P₁
    omega
  have hV02 := finrank_planeFixSpace_le_two hNS
  have hlt : finrank K U < 3 * orderOf ((Nat.card K : ℕ) : ZMod p) := by omega
  have hV0st : EStable E (planeFixSpace E) :=
    EStable.of_fixed fun x hx u hu => hu _ ⟨x, hx, rfl⟩
  have hUst : EStable E U := manyBig_eStable_sup (manyBig_eStable_sup hV0st h₁.eStable) h₂.eStable
  have hQU := nondegenerate_comp_subtype hU
  have hTU := exists_ts_three_comp hU hU8
  obtain ⟨ρ, hρ⟩ := manyBig_exists_restrict_hom hK hp hp2 hU hTU hUst
  have hfinE : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hK.card]; exact pow_ne_zero 2 hp.ne_zero)
  have hfix : ∀ x : E, ρ x = 1 → ∀ P : Submodule K V, P ≤ U →
      ∀ u ∈ P, ((x : orthDerived Q) : V ≃ₗ[K] V) u = u := by
    intro x hx P hPU u hu
    have := hρ x ⟨u, hPU hu⟩
    rw [hx] at this
    exact this.symm
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : x ∈ M₁ ⊓ M₂ :=
      ⟨hk₁ x (hfix x hx P₁ hP₁U), hk₂ x (hfix x hx P₂ hP₂U)⟩
    rwa [inf_eq_bot_of_card_prime' hp hM₁ hM₂ hM12, Subgroup.mem_bot] at h1
  have hcomm' : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hK.comm a b]
  have hexp' : ∀ x ∈ ρ.range, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hK.exp a, map_one]
  have hcard' : Nat.card ρ.range = p ^ 2 :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hK.card
  have haniso : ∀ u ∈ planeFixSpace ρ.range, (Q.comp U.subtype) u = 0 → u = 0 := by
    intro u hu hQu
    have hu0 : (u : V) ∈ planeFixSpace E := by
      refine mem_fixSpace.mpr fun g hg => ?_
      obtain ⟨x, hx, rfl⟩ := hg
      have h1 := mem_fixSpace.mp hu ((ρ ⟨x, hx⟩ : orthDerived (Q.comp U.subtype)) : U ≃ₗ[K] U)
        ⟨ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      have h2 := hρ ⟨x, hx⟩ u
      rw [h1] at h2
      exact h2.symm
    exact Subtype.ext (eq_zero_of_singular_planeFixSpace hNS hu0 hQu)
  have hclos := orthU_selfDualTwoBlocks (Q := Q.comp U.subtype) hQU hTU (by omega) h2 hp hp5 hpl
    (rankLE2_of_finrank_lt hQU hp hp2 hpl hlt) ρ.range hcomm' hexp' hcard' haniso
    (hasSelfDualFactor_restrict hK hp hpl hU ρ hρ h₁ hP₁U)
  have hgen : Subgroup.closure {h : orthDerived (Q.comp U.subtype) |
      ∃ x : E, x ≠ 1 ∧ h * ρ x = ρ x * h ∧ h ^ ringChar K = 1} = ⊤ := by
    rw [eq_top_iff, ← hclos]
    refine Subgroup.closure_mono ?_
    rintro h ⟨_, ⟨x, rfl⟩, hx1, hh, hr⟩
    exact ⟨x, fun h1 => hx1 (by rw [h1, map_one]), hh, hr⟩
  have hΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEU := (orthDerived_eq_and_le_closure hQU hTU).1
  exact orthU_eichler_mem_of_restricted_plane hU hEU E (manyBig_mem_stab hK hp.pos hUst) hΩ ρ hρ
    hgen

end ManyBig

section ManyBigMain

theorem orthU_closure_eq_top_of_noSingular_big {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : (2 : K) ≠ 0) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K)
    (E : Subgroup (orthDerived Q))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) (hNS : OrthNoInvariantSingular Q E)
    (h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)) :
    Subgroup.closure {h : orthDerived Q |
      ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤ := by
  classical
  have hp2 : p ≠ 2 := by omega
  haveI : Nontrivial V := nontrivial_of_three_singular hT
  obtain ⟨hK, -⟩ := exists_kernelLineData_of_le hQ hp hp2 hpl E hcomm hexp hcard
  obtain ⟨n, P, hP, hPP, -, hPsp⟩ :=
    exists_piece_decomposition hQ hp hp2 hpl E hcomm hexp hcard hNS
  choose M hMc hMP hMk hMf _ _ using fun i => (hP i).exists_line hK hp hp2 hpl
  obtain ⟨i, j, hij⟩ := exists_pieces_diff_lines hK hp hpl hP hPsp (M := M)
    fun i => ⟨hMc i, hMP i⟩
  have hji : j ≠ i := fun h => hij (h ▸ rfl)
  haveI : Nonempty {k : Fin n // k ≠ i} := ⟨⟨j, hji⟩⟩
  have hEΩ : elementaryGroup Q ≤ orthDerived Q := (orthDerived_eq_and_le_closure hQ hT).1.ge
  have hEich : ∀ k : {k : Fin n // k ≠ i}, ∀ x ∈ planeFixSpace E ⊔ P i ⊔ P k,
      ∀ y ∈ planeFixSpace E ⊔ P i ⊔ P k, eichler Q x y ∈ orthUSpan Q E := by
    intro k
    by_cases hM : M i = M k
    · have hle : planeFixSpace E ⊔ P i ⊔ P k ≤ planeFixSpace E ⊔ lineSpace (M i) := by
        refine sup_le (sup_le le_sup_left ((hMP i).trans le_sup_right)) ?_
        rw [hM]
        exact (hMP k).trans le_sup_right
      exact fun x hx y hy => orthU_eichler_mem_of_mem_sup hEΩ
        (ne_bot_of_card_prime hp (hMc i)) (hle hx) (hle hy)
    · exact orthU_eichler_mem_of_two_pieces hQ hT h2 hp hp5 hpl hK hNS h4 (hP i) (hP k)
        (hPP i k k.2.symm) (hMc i) (hMc k) hM (hMk i) (hMk k) (hMf i) (hMf k)
  have hspan : (⊤ : Submodule K V) ≤
      planeFixSpace E ⊔ P i ⊔ ⨆ k : {k : Fin n // k ≠ i}, P k := by
    refine hPsp.trans (sup_le (le_sup_of_le_left le_sup_left) (iSup_le fun k => ?_))
    by_cases hk : k = i
    · rw [hk]
      exact le_sup_of_le_left le_sup_right
    · exact le_sup_of_le_right (le_iSup (fun k : {k : Fin n // k ≠ i} => P k) ⟨k, hk⟩)
  have hle : elementaryGroup Q ≤ orthUSpan Q E :=
    elementaryGroup_le_of_pieces hQ (orthUSpan_le_orthogonalGroup E) (hP i).regular
      (by have := hMf i; omega) (fun k : {k : Fin n // k ≠ i} => P k) (hP i).orthSep
      (fun k => hPP i k k.2.symm) hspan hEich
  exact orthU_closure_eq_top_of_le E
    ((orthDerived_eq_and_le_closure hQ hT).1.le.trans hle)

end ManyBigMain

section Master

@[expose] def orthUPlaneGen {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
    Nat.card E = p ^ 2 →
      Subgroup.closure {h : orthDerived Q |
        ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h ∧ h ^ ringChar K = 1} = ⊤

theorem orthU_master {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) :
    orthUPlaneGen Q p := by
  intro E hcomm hexp hcard
  classical
  have h2' : (2 : K) ≠ 0 := Ring.two_ne_zero h2
  by_cases hNS : OrthNoInvariantSingular Q E
  · obtain ⟨he2, k, hk⟩ := noSingular_ord hQ hp (by omega) hpl E hcomm hexp hcard hNS
    by_cases h4 : 4 ≤ orderOf ((Nat.card K : ℕ) : ZMod p)
    · exact orthU_closure_eq_top_of_noSingular_big Q hQ hT hdim h2' hp hp5 hpl E hcomm hexp hcard
        hNS h4
    · exact orthU_closure_eq_top_of_noSingular_two Q hQ hT hdim hp (by omega) hpl
        (orthU3_three_le_card h2) E hcomm hexp hcard hNS (by omega)
  · have hNS' : ¬ ∀ T : Submodule K V, (∀ e ∈ E, ∀ vector ∈ T,
        ((e : orthDerived Q) : V ≃ₗ[K] V) vector ∈ T) → (∀ vector ∈ T, Q vector = 0) → T = ⊥ :=
      hNS
    push Not at hNS'
    obtain ⟨W, hWst, hWQ, hW0⟩ := hNS'
    exact orthU_closure_eq_top_of_singular_stable hQ hT h2 hp (by omega) hpl E hcomm hexp hcard
      hW0 hWQ hWst

end Master

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank in
theorem orthU_closure_statedProj_of_gen (hQ : ⇑Q = Q₀)
    (hE : orthDerived Q = elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate)
    [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgen : orthUPlaneGen Q p)
    (E : Subgroup (StatedProj (StatedOmega Q₀)))
    (hEab : CFSG.Open.IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega Q₀) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar K = 1} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ι → K) := inferInstance
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun g => (g : (ι → K) → (ι → K))) DFunLike.coe_injective
  let ψ : StatedOmega Q₀ ≃* orthDerived Q :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega Q₀,
      ((ψ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
        toLinEquiv ι K (y : GL ι K) := fun y => rfl
  let π : orthDerived Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K (ι → K)).subgroupOf (orthDerived Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have : IsMulCommutative E := hEab.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  exact uniClosure_of_lift π hπ hker' E hcomm hEab.2 fun E' hc he hcd =>
    hgen E' hc he (hcd.trans hcard)

end Lift

theorem orthU_ringChar_ne_two {K : Type} [Field K] (h2 : (2 : K) ≠ 0) : ringChar K ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := K)
  rw [h] at this
  exact_mod_cast this

section Master

theorem orthU3_master {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : ringChar K ≠ 2) (hpl : 3 ≠ ringChar K) : orthUPlaneGen Q 3 := by
  intro E hcomm hexp hcard
  classical
  by_cases hNS : OrthNoInvariantSingular Q E
  · obtain ⟨he2, -⟩ := noSingular_ord hQ Nat.prime_three (by norm_num) hpl E hcomm hexp hcard
      hNS
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hne : ((Nat.card K : ℕ) : ZMod 3) ≠ 0 := fun h0 =>
      manyThree_not_three_dvd_card hpl ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    have hle : orderOf ((Nat.card K : ℕ) : ZMod 3) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hne))
    exact orthU_closure_eq_top_of_noSingular_two Q hQ hT hdim Nat.prime_three (by norm_num) hpl
      (orthU3_three_le_card h2) E hcomm hexp hcard hNS (by omega)
  · have hNS' : ¬ ∀ T : Submodule K V, (∀ e ∈ E, ∀ vector ∈ T,
        ((e : orthDerived Q) : V ≃ₗ[K] V) vector ∈ T) → (∀ vector ∈ T, Q vector = 0) → T = ⊥ :=
      hNS
    push Not at hNS'
    obtain ⟨W, hWst, hWQ, hW0⟩ := hNS'
    exact orthU_closure_eq_top_of_singular_stable hQ hT h2 Nat.prime_three (by norm_num) hpl E
      hcomm hexp hcard hW0 hWQ hWst

theorem orthU3_master_odd {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    (h2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) :
    orthUPlaneGen Q p := by
  have hp3 := hp.two_le
  rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with rfl | rfl | hp5
  · exact orthU3_master Q hQ hT hdim h2 hpl
  · exact absurd hp (by norm_num)
  · exact orthU_master Q hQ hT hdim h2 hp hp5 hpl

end Master

section Leaves

open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank

theorem orthU3_oddPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h2 : (2 : K) ≠ 0)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar K = 1} = ⊤ := by
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthU_closure_statedProj_of_gen (coe_quadOdd r K)
    (commutator_orthogonalGroup_quadOdd h2 hr) hreg.1 hp hp2
    (orthU3_master_odd (quadOdd r K) hreg.1 hreg.2 hdim (orthU_ringChar_ne_two h2) hp hp2
      (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthU3_plusPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 4 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h2 : ringChar K ≠ 2)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar K = 1} = ⊤ := by
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthU_closure_statedProj_of_gen (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hp hp2
    (orthU3_master_odd (quadPlus r K) hreg.1 hreg.2 hdim h2 hp hp2
      (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

theorem orthU3_minusPlanes {r p : ℕ} {K : Type} [Field K] [Finite K] (b c : K) (hr : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K) (h2 : ringChar K ≠ 2)
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k ∧ k ^ ringChar K = 1} = ⊤ := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact orthU_closure_statedProj_of_gen (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 hp hp2
    (orthU3_master_odd (quadMinus r K b c) hreg.1 hreg.2 hdim h2 hp hp2
      (ne_ringChar_of_not_dvd_card hpK)) E hE hcard

end Leaves

section Cat

open CFSG.Assembly.LowTwoRank

theorem orthU3_uniSeitzPlanes_orthogonal :
    Inputs2311c.UniSeitzPlanes fun d p E => CFSG.LieType.SeitzGeneration.InnerPlane d p E ∧
      CFSG.LieType.SeitzGeneration.IsOrthogonalIndex d.1 ∧ d.1.characteristic ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, horth, hchar2⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 :=
      Ring.two_ne_zero (by rw [hring]; exact hq)
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero
        h2 hr3
    have : IsSimpleGroup (Cat ⟨.B r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.B r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen q.p E by simpa using h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthU3_oddPlanes hr3 hp hp2 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      h2 E₁ hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hq2 : q.p ≠ 2 := by simpa using hchar2
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
    have : IsSimpleGroup (Cat ⟨.D r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.D r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen q.p E by simpa using h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthU3_plusPlanes hr4 hp hp2 (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      (by rw [hring]; exact hq2) E₁ hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hq2 : q.p ≠ 2 := by simpa using hchar2
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
      q.exponent_pos hcard
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hr4 hirr
    have : IsSimpleGroup (Cat ⟨.twistedD r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedD r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    suffices h : Inputs2311c.UniPlaneGen q.p E by simpa using h
    rw [← hring]
    refine Inputs2311c.uniPlaneGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthU3_minusPlanes b c hr4 hirr hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') (by rw [hring]; exact hq2)
      E₁ hE₁ hcard₁

theorem orthU_uniSeitzPlanes_orthogonal_three :
    Inputs2311c.UniSeitzPlanes fun d p E => CFSG.LieType.SeitzGeneration.InnerPlane d p E ∧ p = 3 ∧
      CFSG.LieType.SeitzGeneration.IsOrthogonalIndex d.1 ∧ d.1.characteristic ≠ 2 :=
  orthU3_uniSeitzPlanes_orthogonal.mono fun _ _ _ h => ⟨h.1, h.2.2.1, h.2.2.2⟩

end Cat

end OrthUni

section OrthOut

open Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ClassicalGroups.Orthogonal

section Gen

variable {k : Type} [Field k] [Finite k] {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}

theorem orthOut_closure_pow_ringChar_matrixDerived (hnd : (polarBilin Q₀).Nondegenerate)
    (hT : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) :
    Subgroup.closure {g : matrixDerived Q₀ | g ^ ringChar k = 1} = ⊤ := by
  have hΩ : (matrixDerived Q₀).map (matrixLinearIso (d := d) (K := k)).toMonoidHom = elementaryGroup Q₀ := by
    rw [KCOrthogonalAut.map_matrixDerived, (CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hnd hT).1]
  set H : Subgroup (GL (Fin d) k) :=
    (Subgroup.closure {g : matrixDerived Q₀ | g ^ ringChar k = 1}).map (matrixDerived Q₀).subtype
  have hEich : elementaryGroup Q₀ ≤ H.map (matrixLinearIso (d := d) (K := k)).toMonoidHom := by
    rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨u, w, -, -, rfl⟩
    have hmem : eichler Q₀ u w ∈ (matrixDerived Q₀).map (matrixLinearIso (d := d) (K := k)).toMonoidHom := by
      rw [hΩ]
      exact eichler_mem_elementaryGroup Q₀ u w
    obtain ⟨A, hA, hAe⟩ := hmem
    refine ⟨A, ⟨⟨A, hA⟩, Subgroup.subset_closure ?_, rfl⟩, hAe⟩
    show (⟨A, hA⟩ : matrixDerived Q₀) ^ ringChar k = 1
    apply Subtype.ext
    apply (matrixLinearIso (d := d) (K := k)).injective
    have hAe' : matrixLinearIso A = eichler Q₀ u w := hAe
    rw [SubgroupClass.coe_pow, map_pow, hAe', orthU_eichler_pow_ringChar, OneMemClass.coe_one, map_one]
  rw [eq_top_iff]
  rintro g -
  have hg : (matrixLinearIso (d := d) (K := k)).toMonoidHom g ∈
      H.map (matrixLinearIso (d := d) (K := k)).toMonoidHom := by
    apply hEich
    rw [← hΩ]
    exact ⟨g, g.2, rfl⟩
  obtain ⟨A, ⟨h, hh, rfl⟩, hAg⟩ := hg
  have : h = g := Subtype.ext ((matrixLinearIso (d := d) (K := k)).injective hAg)
  exact this ▸ hh

theorem orthOut_closure_pow_ringChar_matrixProjectiveDerived (hnd : (polarBilin Q₀).Nondegenerate)
    (hT : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0) :
    Subgroup.closure {x : matrixProjectiveDerived Q₀ | x ^ ringChar k = 1} = ⊤ := by
  have h := congrArg (Subgroup.map (matrixProjectiveProjection Q₀))
    (orthOut_closure_pow_ringChar_matrixDerived hnd hT)
  rw [MonoidHom.map_closure,
    Subgroup.map_top_of_surjective _ (matrixProjectiveProjection_surjective Q₀)] at h
  rw [eq_top_iff, ← h]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨g, hg, rfl⟩
  show matrixProjectiveProjection Q₀ g ^ ringChar k = 1
  rw [← map_pow, show g ^ ringChar k = 1 from hg, map_one]

end Gen

section Fixed

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ} {Q₀ : QuadraticForm k (Fin d → k)}
  {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {hext : IsExtension k Q₀ Q}
  {hQσ : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)}

theorem orthOut_fixedSubgroup_fieldAutT_le_closure (hnd₀ : (polarBilin Q₀).Nondegenerate)
    (hT₀ : ∃ U : Submodule k (Fin d → k), finrank k U = 3 ∧ ∀ u ∈ U, Q₀ u = 0)
    (hfix : fixedSubgroup (fieldAutT Q σ hQσ) = (incl k hext).range) :
    fixedSubgroup (fieldAutT Q σ hQσ) ≤
      Subgroup.closure {x | fieldAutT Q σ hQσ x = x ∧ x ^ ringChar K = 1} := by
  have hchar : ringChar k = ringChar K := by
    have : CharP k (ringChar K) := inferInstance
    exact ringChar.eq _ _
  have hJ : (incl k hext).range ≤ fixedSubgroup (fieldAutT Q σ hQσ) := hfix.ge
  rw [hfix]
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ Subgroup.closure {x : matrixProjectiveDerived Q₀ | x ^ ringChar k = 1} := by
    rw [orthOut_closure_pow_ringChar_matrixProjectiveDerived hnd₀ hT₀]
    exact Subgroup.mem_top z
  have h1 := Subgroup.mem_map_of_mem (incl k hext) hz
  rw [MonoidHom.map_closure] at h1
  refine Subgroup.closure_mono ?_ h1
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨hJ ⟨x, rfl⟩, ?_⟩
  rw [← map_pow, ← hchar, show x ^ ringChar k = 1 from hx, map_one]

end Fixed

section Outer3

open CFSG.RankThree.Classical.SteinbergBY CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')

open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube (subfieldFixedGroup_le_derivedImage_of_odd_finrank)

open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus matrixProjectiveImage_eq_top_minus)

variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem orthOut3_fixedSubgroup_le_closure_odd (hadm : StatedLieAdmissible .POmegaOdd n ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadOdd n K))} (hα : IsOuterOfOrder p α) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} := by
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadOdd n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaOdd (Or.inl rfl) n ℓ f hM
      K hK (MulEquiv.refl _)
  have h2K : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg (matrixProjectiveImage_eq_top_odd K n hn3 h2K) hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaOdd (Or.inl rfl)
    n ℓ f p hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ _ => coordinateQuadOdd_fieldAut n σ) (fun U Q₀ _ hdisp => by
      obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      exact ⟨S, ν', hSQ, hSA⟩)
  have hconj : D⁻¹ * α * D⁻¹⁻¹ = fieldAutT (coordinateQuadOdd n K) σ (coordinateQuadOdd_fieldAut n σ) := by
    rw [hαD]
    group
  refine fixedSubgroup_le_closure_of_conj hconj ?_
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
  have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  obtain ⟨-, -, hfixiff, hJN, -⟩ :=
    (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaOdd (Or.inl rfl) n ℓ e p
      ⟨hℓ, he, hn3, hℓ2⟩ hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk).2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero h2K
  have hreg := regular_coordinateQuadOdd n (semilinearFixedSubfield σ) (two_ne_zero_of_subfield _ h2) hn3
  have hNJ := subfieldFixedGroup_le_derivedImage_of_odd_finrank (semilinearFixedSubfield σ)
    (by rw [finrank_subfield_eq _ hℓ he hcardk hK']; exact hp.odd_of_ne_two hp2)
    (coordinateQuadOdd_isExtension _ n) hreg.1 hreg.2 (regular_coordinateQuadOdd n K h2 hn3).1
  exact orthOut_fixedSubgroup_fieldAutT_le_closure hreg.1 hreg.2
    ((Subgroup.ext hfixiff).trans (le_antisymm hNJ hJN))

theorem orthOut3_fixedSubgroup_le_closure_minus {e : ℕ} (hn : 4 ≤ n) (hn1 : 1 ≤ n) (hℓ : ℓ.Prime)
    (he : 1 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {k : Subfield K}
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K}
    (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K)))}
    (hα : IsOuterOfOrder p α) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} := by
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hdeg := finrank_subfield_eq k hℓ he hk hK
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := rootFree_of_odd_degree k hp hp2 hdeg b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg
    (matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK) hp hp2 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
    (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) (by
      intro U Q₀ hord hdisp
      obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      have hfixV := hfixall U.val.right hord
      have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
        fun x => RingHom.mem_eqLocusField
      have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
      have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
      have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
        hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
      have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
        intro s hs hz
        have hsV : s ∈ CFSG.RankThree.PartOne.KCOrthogonalDescent.fixedField U.val :=
          (hσk' s).2 ((hfixV s).1 hs)
        exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
      obtain ⟨μ, hμk, hμQ⟩ :=
        CFSG.RankThree.PartOne.SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
      have hμσ : CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut (Fin (2 * n)) K
          U.val.right μ = μ :=
        Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
      refine ⟨μ * S, ν', fun v => ?_, ?_⟩
      · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        exact (hμQ _).trans (hSQ v)
      · rw [mul_assoc, hSA, map_mul, hμσ])
  have hconj : D⁻¹ * α * D⁻¹⁻¹ = fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
      (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c) := by
    rw [hαD]
    group
  refine fixedSubgroup_le_closure_of_conj hconj ?_
  obtain ⟨-, -, hfixiff, hJN, -⟩ :=
    (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus (Or.inr (Or.inr rfl)) n ℓ e
      p ⟨hℓ, he, hn⟩ hp hp2 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ) b c hirr).2
  have hreg := regular_coordinateQuadMinus n k b c hn hirr
  have hNJ := subfieldFixedGroup_le_derivedImage_of_odd_finrank k (by rw [hdeg]; exact hp.odd_of_ne_two hp2)
    (coordinateQuadMinus_isExtension k n hn1 b c) hreg.1 hreg.2
    (regular_coordinateQuadMinus n K (b : K) (c : K) hn hirrK).1
  exact orthOut_fixedSubgroup_fieldAutT_le_closure hreg.1 hreg.2
    ((Subgroup.ext hfixiff).trans (le_antisymm hNJ hJN))

end Outer3

section Outer

open CFSG.RankThree.Classical.SteinbergBY CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube (orthFixedLeDerivedAll_holds)


variable {n ℓ f p : ℕ} {K : Type} [Field K] [Finite K]

theorem orthOut_fixedSubgroup_le_closure_plus (hadm : StatedLieAdmissible .POmegaPlus n ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    {α : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hα : IsOuterOfOrder p α) :
    fixedSubgroup α ≤ Subgroup.closure {x | α x = x ∧ x ^ ringChar K = 1} := by
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  obtain ⟨hE, hD⟩ := outer_mem_E_not_D hg hp hp3 hα
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent _ .POmegaPlus
    (Or.inr (Or.inl rfl)) n ℓ f p hM hp hp3 hpℓ K hK (MulEquiv.refl _) α hE hD hα.1
  obtain ⟨D, -, σ, hσ, hαD⟩ := exists_conj_fieldAutT_of_descent _ hE hdesc
    (fun σ _ => coordinateQuadPlus_fieldAut n σ) (fun U Q₀ _ hdisp => by
      obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
      exact ⟨S, ν', hSQ, hSA⟩)
  have hconj : D⁻¹ * α * D⁻¹⁻¹ =
      fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) := by
    rw [hαD]
    group
  refine fixedSubgroup_le_closure_of_conj hconj ?_
  obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
  obtain ⟨e, rfl⟩ := hpf
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, mul_zero] at hf
      omega
    · exact h0
  rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
  have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
  have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
  have hadm0 : StatedLieAdmissible .POmegaPlus n ℓ e := ⟨hℓ, he, hn4⟩
  obtain ⟨-, hconc⟩ :=
    orthogonal_prime_subfield_fixed_group_and_full_centralizer_unconditional .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ e p hadm0 hp hp3 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ
      hσk
  have hNJ := (orthFixedLeDerivedAll_holds n ℓ e p).2.1 hadm0 hp hp3 hpℓ K
    (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
  obtain ⟨-, -, hfixiff, hJN, -⟩ := hconc
  have hreg := regular_coordinateQuadPlus n (semilinearFixedSubfield σ) (by omega)
  exact orthOut_fixedSubgroup_fieldAutT_le_closure hreg.1 hreg.2
    ((Subgroup.ext hfixiff).trans (le_antisymm hNJ hJN))

end Outer

section Model

theorem orthOut_uniPlaneGen_of_mulEquiv {G P : Type} [Group G] [Group P] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (ψ : G ≃* P) {p r : ℕ} (hp : p.Prime) (hd : FieldAutData P p)
    (hfix : ∀ τ : MulAut P, IsOuterOfOrder p τ →
      fixedSubgroup τ ≤ Subgroup.closure {x | τ x = x ∧ x ^ r = 1})
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ 2)
    (hout : ¬ E ≤ (MulAut.conj : G →* MulAut G).range) : UniPlaneGen r E := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup P := MulEquiv.isSimpleGroup ψ.symm
  have hnabP : ∃ a b : P, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨ψ a, ψ b, fun h => hab (ψ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr ψ).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr ψ hE)
  have hc' : Nat.card (E.map (MulAut.congr ψ).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr ψ).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr ψ hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  exact (uniPlaneGen_map_congr ψ r E).1 (uniPlaneGen_of_fieldAutData hnabP hp hd hfix _ hc' hout')

theorem orthOut_uniPlaneGen_of_model {G : Type} [Group G]
    {c : StatedLieTag} (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) {n ℓ f p : ℕ}
    (hM : StatedClassicalModel G c n ℓ f) (hp : p.Prime) (hp3 : 3 < p) (hpℓ : p ≠ ℓ)
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2)
    (hout : ¬ E ≤ (MulAut.conj : G →* MulAut G).range) : UniPlaneGen ℓ E := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hsimple, hperf⟩ := orth_facts_of_model hc hM
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative G ⟨⟨fun a b => hcon a b⟩⟩
  have hpair := subfieldPairOmega_of_char2
      (subfieldPairOmegaPlusChar2_of_F2 subfieldPairOmegaPlusF2_holds)
      (subfieldPairOmegaMinusChar2_of_F2 subfieldPairOmegaMinusF2_holds)
  rcases hc with rfl | rfl | rfl
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
    refine orthOut_uniPlaneGen_of_mulEquiv hnab (coordinateOddWitnessEquiv K e) hp
      (fieldAutData_odd hpair.1 hadm hK hp hp3 hpℓ) (fun τ hτ => ?_) hE hcard hout
    rw [← hchar]
    exact orthOut3_fixedSubgroup_le_closure_odd hadm hK hp (by omega) hpℓ hτ
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
    refine orthOut_uniPlaneGen_of_mulEquiv hnab (coordinatePlusWitnessEquiv K e) hp
      (fieldAutData_plus hpair.2.1 hadm hK hp hp3 hpℓ) (fun τ hτ => ?_) hE hcard hout
    rw [← hchar]
    exact orthOut_fixedSubgroup_le_closure_plus hadm hK hp hp3 hpℓ hτ
  · obtain ⟨hℓ, hf, hn⟩ := id hM.1
    have hn1 : 1 ≤ n := by omega
    have hσ : ∃ σ ∈ E, ∀ g : G, σ ≠ MulAut.conj g := by
      by_contra hcon
      push Not at hcon
      exact hout fun σ hσ => (hcon σ hσ).imp fun g hg => hg.symm
    obtain ⟨σ, hσE, hσinn⟩ := hσ
    have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
    have hσp : σ ^ p = 1 := hE.2 σ hσE
    have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
    obtain ⟨e, K, _, _, k, σ₀, b, c, he, -, hk, hK, hσ₀, hfix, hirr, ⟨ψ⟩⟩ :=
      exists_rational_model_minus hn1 hM hp hp3 hpℓ hσo
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hℓ (Nat.mul_pos he hp.pos) hK
    refine orthOut_uniPlaneGen_of_mulEquiv hnab ψ hp
      (fieldAutData_minus_rational hpair.2.2 hn hn1 hℓ he hp hp3 hpℓ hk hK hσ₀ hfix b c hirr)
      (fun τ hτ => ?_) hE hcard hout
    rw [← hchar]
    exact orthOut3_fixedSubgroup_le_closure_minus hn hn1 hℓ he hp (by omega) hpℓ hk hK hσ₀ hfix b c hirr hτ

end Model

section Cat

theorem orthOut_uniSeitzPlanes_orthogonal_outer :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, hp5, horth⟩
  have hp3 : 3 < p := by omega
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut_uniPlaneGen_of_model (Or.inl rfl) (n := r) (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3
      hq' hE hc hout
    simpa using h
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut_uniPlaneGen_of_model (Or.inr (Or.inl rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩ hp hp3 hq'
      hE hc hout
    simpa using h
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut_uniPlaneGen_of_model (Or.inr (Or.inr rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ hp hp3 hq' hE hc hout
    simpa using h

theorem orthOut_uniSeitzPlanes_orthogonal_outer_five :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ CFSG.LieType.SeitzGeneration.InnerPlane d p E ∧ 5 ≤ p ∧
      CFSG.LieType.SeitzGeneration.IsOrthogonalIndex d.1 ∧ d.1.characteristic ≠ 2 :=
  UniSeitzPlanes.mono (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩) orthOut_uniSeitzPlanes_orthogonal_outer

end Cat

end OrthOut

section OrthOut3

open Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical.SteinbergBY CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')

open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube (subfieldFixedGroup_le_derivedImage_of_odd_finrank)

open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus matrixProjectiveImage_eq_top_minus)

section Similarity

open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)


variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {f p : ℕ}

theorem orthOut3_plane_inf_inner_card (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2)
    (A : Subgroup (MulAut (matrixProjectiveDerived Q))) (hAE : A ≤ matrixProjectiveImage Q)
    (hAe : CFSG.IsElementaryAbelian p A) (hAcard : Nat.card A = p ^ 2)
    (hAH : ¬ A ≤ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    Nat.card (A ⊓ OuterAutomorphisms.inner (matrixProjectiveDerived Q) : Subgroup _) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have := hAe
  obtain ⟨-, ⟨ψ, -, hψker, -⟩, ⟨hHD, k₂, hk₂⟩, -⟩ := hg
  set D := (linearConjugationHom Q).range with hDdef
  set H := OuterAutomorphisms.inner (matrixProjectiveDerived Q) with hHdef
  have : H.Normal := OuterAutomorphisms.inner_normal _
  have : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hADH : A ⊓ D ≤ H := by
    rintro x ⟨hxA, hxD⟩
    exact CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow
      hk₂ hp hp2 hxD (CFSG.elemPow_eq_one_of_isElementaryAbelian x hxA)
  set φ : A →* (K ≃+* K) := ψ.comp (Subgroup.inclusion hAE) with hφ
  have hφker : φ.ker = D.subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      hψker, Subgroup.mem_subgroupOf]
    rfl
  have hφp : ∀ a : A, φ a ^ p = 1 := by
    intro a
    rw [← map_pow]
    have ha : a ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p p A) a
    rw [ha, map_one]
  have hrange_dvd : Nat.card φ.range ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun σ => ?_
    obtain ⟨a, ha⟩ := σ.2
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← ha, hφp, OneMemClass.coe_one]
  have hrange_ne : Nat.card φ.range ≠ 1 := by
    intro h1
    apply hAH
    intro x hx
    apply hADH
    refine ⟨hx, ?_⟩
    have hmem : (⟨x, hx⟩ : A) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have : φ ⟨x, hx⟩ ∈ φ.range := ⟨⟨x, hx⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [hφker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hrange : Nat.card φ.range = p := ((Nat.dvd_prime hp).mp hrange_dvd).resolve_left hrange_ne
  have hkercard : Nat.card φ.ker = p := by
    have h1 := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hrange, hAcard, _root_.sq] at h1
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hHD' : H ≤ D := hHD
  have hAHeq : A ⊓ H = A ⊓ D := le_antisymm (inf_le_inf_left _ hHD') (le_inf inf_le_left hADH)
  have hcardAD : Nat.card (A ⊓ D : Subgroup _) = p := by
    rw [← hkercard, hφker, inf_comm, ← Subgroup.subgroupOf_map_subtype,
      Subgroup.card_map_of_injective A.subtype_injective]
  rw [hAHeq, hcardAD]

theorem orthOut3_exists_conj_mem_of_plane (hg : OrthogonalGates Q f) (hp : p.Prime) (hp2 : p ≠ 2)
    (E : Subgroup (MulAut (matrixProjectiveDerived Q))) (hEQ : E ≤ matrixProjectiveImage Q)
    (hE : CFSG.IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2) :
    ∃ g : matrixProjectiveDerived Q, g ≠ 1 ∧ MulAut.conj g ∈ E := by
  have hp1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  have hnontriv : ∃ x : MulAut (matrixProjectiveDerived Q), x ∈ E ∧
      x ∈ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range ∧
        x ≠ 1 := by
    by_cases hin : E ≤
        (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range
    · have hne : E ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2, hin x.2, fun h => hx1 (Subtype.ext h)⟩
    · have hpl : Nat.card ↥(E ⊓ (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range) = p :=
        orthOut3_plane_inf_inner_card hg hp hp2 E hEQ hE hEc hin
      have hne : (E ⊓ (MulAut.conj : matrixProjectiveDerived Q →*
          MulAut (matrixProjectiveDerived Q)).range) ≠ ⊥ := fun h0 => by
        have := Subgroup.card_eq_one.2 h0
        rw [this] at hpl
        have := hp.one_lt
        omega
      obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
      exact ⟨x, x.2.1, x.2.2, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨x, hxE, ⟨g, hg'⟩, hx1⟩ := hnontriv
  exact ⟨g, fun h1 => hx1 (by rw [← hg', h1, map_one]), hg' ▸ hxE⟩

end Similarity

section Standard

theorem orthOut3_uniPlaneGen_of_standard {P : Type} [Group P] [IsSimpleGroup P]
    (hnab : ∃ a b : P, a * b ≠ b * a) {p r : ℕ} (hp : p.Prime) (A D : Subgroup (MulAut P))
    (S : Set (MulAut P)) (hdesc : ∀ α ∈ A, IsOuterOfOrder p α → ∃ d ∈ D, ∃ f ∈ S, α = d * f * d⁻¹)
    (hfixS : ∀ f ∈ S, ∀ f' ∈ S, fixedSubgroup f = fixedSubgroup f')
    (hcenter : ∀ f ∈ S, ∀ x ∈ fixedSubgroup f, (∀ y ∈ fixedSubgroup f, x * y = y * x) → x = 1)
    (hpair : ∀ f ∈ S, ∀ d ∈ D, (fixedSubgroup f).map d.toMonoidHom ≠ fixedSubgroup f →
      Subgroup.closure ((fixedSubgroup f : Set P) ∪ ((fixedSubgroup f).map d.toMonoidHom : Set P)) = ⊤)
    (hgen : ∀ f ∈ S, fixedSubgroup f ≤ Subgroup.closure {x | f x = x ∧ x ^ r = 1})
    (E : Subgroup (MulAut P)) [CFSG.IsElementaryAbelian p E] (hEA : E ≤ A)
    (hk : ∃ k : P, k ≠ 1 ∧ MulAut.conj k ∈ E) (hout : ¬ E ≤ (MulAut.conj : P →* MulAut P).range) :
    UniPlaneGen r E := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj := conj_injective_of_simple hnab
  obtain ⟨k, hk1, hkE⟩ := hk
  obtain ⟨σ, hσE, hσinn⟩ : ∃ σ ∈ E, ∀ g : P, σ ≠ MulAut.conj g := by
    by_contra hcon
    push Not at hcon
    exact hout fun σ hσ => (hcon σ hσ).imp fun g hg => hg.symm
  have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
  have hσp : σ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian σ hσE
  have hσo : IsOuterOfOrder p σ := ⟨orderOf_eq_prime hσp hσ1, hσinn⟩
  have hkp : k ^ p = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ hkE
  have hcomm : σ * MulAut.conj k = MulAut.conj k * σ := hcommE σ hσE _ hkE
  have hστE : σ * MulAut.conj k ∈ E := E.mul_mem hσE hkE
  have hστ1 : σ * MulAut.conj k ≠ 1 := by
    intro h
    apply hσinn k⁻¹
    rw [map_inv]
    exact eq_inv_of_mul_eq_one_left h
  have hστp : (σ * MulAut.conj k) ^ p = 1 := by
    rw [(show Commute σ (MulAut.conj k) from hcomm).mul_pow, hσp, ← map_pow, hkp, map_one, one_mul]
  have hστo : IsOuterOfOrder p (σ * MulAut.conj k) := by
    refine ⟨orderOf_eq_prime hστp hστ1, fun g h => hσinn (g * k⁻¹) ?_⟩
    rw [map_mul, map_inv, ← h, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨d₁, hd₁, f₁, hf₁, hσd⟩ := hdesc σ (hEA hσE) hσo
  obtain ⟨d₂, hd₂, f₂, hf₂, hτd⟩ := hdesc _ (hEA hστE) hστo
  set R := fixedSubgroup f₁ with hR
  have h₁ : fixedSubgroup σ = R.map d₁.toMonoidHom := by rw [hσd]; exact fixedSubgroup_conj d₁ f₁
  have h₂ : fixedSubgroup (σ * MulAut.conj k) = R.map d₂.toMonoidHom := by
    rw [hτd, fixedSubgroup_conj, hfixS f₂ hf₂ f₁ hf₁]
  have h₃ : R.map d₂.toMonoidHom = (R.map (d₁⁻¹ * d₂).toMonoidHom).map d₁.toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp
  have hcenσ : ∀ x ∈ fixedSubgroup σ, (∀ y ∈ fixedSubgroup σ, x * y = y * x) → x = 1 := by
    intro x hx hc
    rw [h₁] at hx hc
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : y = 1 := by
      refine hcenter f₁ hf₁ y hy fun z hz => ?_
      have h1 := hc (d₁ z) ⟨z, hz, rfl⟩
      exact d₁.injective (by simpa using h1)
    rw [hy1, map_one]
  have hσk : σ k = k := apply_eq_of_commute_conj hinj hcomm
  have hne : R.map (d₁⁻¹ * d₂).toMonoidHom ≠ R := by
    intro heq
    have hfeq : fixedSubgroup σ = fixedSubgroup (σ * MulAut.conj k) := by rw [h₁, h₂, h₃, heq]
    apply hk1
    refine hcenσ k hσk fun y hy => ?_
    have hy' : y ∈ fixedSubgroup (σ * MulAut.conj k) := hfeq ▸ hy
    have e1 : σ y = y := hy
    have e2 : (σ * MulAut.conj k) y = y := hy'
    have e3 : σ (k * y * k⁻¹) = k * y * k⁻¹ := by
      rw [map_mul, map_mul, map_inv, hσk, e1]
    have e4 : σ (k * y * k⁻¹) = y := by
      simpa [MulAut.mul_apply, MulAut.conj_apply] using e2
    rw [e4] at e3
    calc k * y = k * y * k⁻¹ * k := by group
      _ = y * k := by rw [← e3]
  have hgP : Subgroup.closure ((fixedSubgroup σ : Set P) ∪ (fixedSubgroup (σ * MulAut.conj k) : Set P)) = ⊤ := by
    have h4 := congrArg (Subgroup.map d₁.toMonoidHom)
      (hpair f₁ hf₁ _ (D.mul_mem (D.inv_mem hd₁) hd₂) hne)
    rw [map_closure_union, Subgroup.map_top_of_surjective _ d₁.surjective, ← h₃] at h4
    rw [h₁, h₂]
    exact h4
  have hfσ : fixedSubgroup σ ≤ Subgroup.closure {x | σ x = x ∧ x ^ r = 1} :=
    fixedSubgroup_le_closure_of_conj (c := d₁⁻¹) (by rw [hσd]; group) (hgen f₁ hf₁)
  have hfτ : fixedSubgroup (σ * MulAut.conj k) ≤
      Subgroup.closure {x | (σ * MulAut.conj k) x = x ∧ x ^ r = 1} :=
    fixedSubgroup_le_closure_of_conj (c := d₂⁻¹) (by rw [hτd]; group) (hgen f₂ hf₂)
  rw [UniPlaneGen, eq_top_iff, ← hgP, Subgroup.closure_le]
  rintro x (hx | hx)
  · refine ((Subgroup.closure_le _).2 ?_) (hfσ hx)
    rintro y ⟨hy, hyr⟩
    exact mem_uniPlaneClosure hσE hσ1 hy (n := 1) (by rw [pow_one]; exact hyr)
  · refine ((Subgroup.closure_le _).2 ?_) (hfτ hx)
    rintro y ⟨hy, hyr⟩
    exact mem_uniPlaneClosure hστE hστ1 hy (n := 1) (by rw [pow_one]; exact hyr)

end Standard

section Plus

open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)


variable {n ℓ f : ℕ} {K : Type} [Field K] [Finite K]

theorem orthOut3_uniPlaneGen_plus (hadm : StatedLieAdmissible .POmegaPlus n ℓ f)
    (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3)
    {E : Subgroup (MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hEQ : E ≤ matrixProjectiveImage (coordinateQuadPlus n K))
    (hout : ¬ E ≤ (MulAut.conj : matrixProjectiveDerived (coordinateQuadPlus n K) →*
      MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))).range) :
    UniPlaneGen (ringChar K) E := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n K)) .POmegaPlus n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨(coordinatePlusWitnessEquiv K (MulEquiv.refl _)).symm⟩⟩
  obtain ⟨-, -, hsimple, hperf⟩ := orth_facts_of_model (Or.inr (Or.inl rfl)) hM0
  have hnab : ∃ a b : matrixProjectiveDerived (coordinateQuadPlus n K), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
  have hEi : CFSG.IsElementaryAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr hE
  have hdata : ∀ (σ : K ≃+* K) (h : orderOf σ = 3),
      FixedGood (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) ∧
      fixedSubgroup (fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ)) ≤
        Subgroup.closure {x | fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ) x = x ∧
          x ^ ringChar K = 1} := by
    intro σ hσ
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * 3) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    have hconc := (orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ e 3 ⟨hℓ, he, hn4⟩ hp hp2 (Ne.symm hℓ3) K (semilinearFixedSubfield σ)
      hcardk hK' σ hσ hσk).2
    have hreg := regular_coordinateQuadPlus n (semilinearFixedSubfield σ) (by omega)
    have hNJ := subfieldFixedGroup_le_derivedImage_of_odd_finrank (semilinearFixedSubfield σ)
      (by rw [finrank_subfield_eq _ hℓ he hcardk hK']; decide)
      (coordinateQuadPlus_isExtension _ n) hreg.1 hreg.2 (regular_coordinateQuadPlus n K (by omega)).1
    refine ⟨fixedGood_of_subfieldConclusion hconc
      (subfieldPairOmegaThree_holds.2.1 n ℓ e hn4 hℓ hℓ3 he K (semilinearFixedSubfield σ) hcardk hK'), ?_⟩
    exact orthOut_fixedSubgroup_fieldAutT_le_closure hreg.1 hreg.2
      ((Subgroup.ext hconc.2.2.1).trans (le_antisymm hNJ hconc.2.2.2.1))
  refine orthOut3_uniPlaneGen_of_standard hnab hp (matrixProjectiveImage (coordinateQuadPlus n K))
    (linearConjugationHom (coordinateQuadPlus n K)).range
    {g | ∃ (σ : K ≃+* K) (_ : orderOf σ = 3),
      g = fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldAut n σ)} ?_ ?_ ?_ ?_ ?_ E hEQ
    (orthOut3_exists_conj_mem_of_plane hg hp hp2 E hEQ hEi hc) hout
  ·
    intro α hαE hα
    have hαp : α ^ 3 = 1 := hα.1 ▸ pow_orderOf_eq_one α
    have hD : α ∉ (linearConjugationHom (coordinateQuadPlus n K)).range := by
      intro hD
      obtain ⟨-, k₂, hk₂⟩ := hg.2.2.1
      have : (OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus n K))).Normal :=
        OuterAutomorphisms.inner_normal _
      obtain ⟨g, hgα⟩ :=
        CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk₂ hp hp2 hD hαp
      exact hα.2 g hgα.symm
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f 3 hM hp hp2 K hK (MulEquiv.refl _) α hαE hD hα.1
    obtain ⟨D, hD', σ, hσ, rfl⟩ := exists_conj_fieldAutT_of_descent _ hαE hdesc
      (fun σ _ => coordinateQuadPlus_fieldAut n σ) (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
    exact ⟨D, hD', _, ⟨σ, hσ, rfl⟩, rfl⟩
  ·
    rintro _ ⟨σ₁, h₁, rfl⟩ _ ⟨σ₂, h₂, rfl⟩
    have hz : ∀ {τ₁ τ₂ : K ≃+* K}, orderOf τ₁ = 3 → orderOf τ₂ = 3 →
        τ₂ ∈ Subgroup.zpowers τ₁ := fun {τ₁ τ₂} g₁ g₂ => by
      have := zpowers_ringEquiv_eq_of_orderOf hℓ hf hK g₁ g₂
      exact this ▸ Subgroup.mem_zpowers τ₂
    have hmem : ∀ {τ₁ τ₂ : K ≃+* K} (g₁ : orderOf τ₁ = 3) (g₂ : orderOf τ₂ = 3),
        fieldPair (coordinateQuadPlus n K) τ₂ (coordinateQuadPlus_fieldAut n τ₂) ∈
          Subgroup.zpowers (fieldPair (coordinateQuadPlus n K) τ₁ (coordinateQuadPlus_fieldAut n τ₁)) := by
      intro τ₁ τ₂ g₁ g₂
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hz g₁ g₂)
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, Subtype.ext ?_⟩
      rw [fieldPair_zpow_val, hm]
      rfl
    exact fixedSubgroup_eq_of_zpowers_eq (matrixProjectiveConjugationHom (coordinateQuadPlus n K))
      (le_antisymm ((Subgroup.zpowers_le).2 (hmem h₂ h₁)) ((Subgroup.zpowers_le).2 (hmem h₁ h₂)))
  · rintro _ ⟨σ, h, rfl⟩
    exact (hdata σ h).1.1
  · rintro _ ⟨σ, h, rfl⟩ g hg' hne
    exact (hdata σ h).1.2 g hg' hne
  · rintro _ ⟨σ, h, rfl⟩
    exact (hdata σ h).2

end Plus

section Model

theorem orthOut3_uniPlaneGen_of_model {G : Type} [Group G]
    {c : StatedLieTag} (hc : c = .POmegaOdd ∨ c = .POmegaPlus ∨ c = .POmegaMinus) {n ℓ f : ℕ}
    (hM : StatedClassicalModel G c n ℓ f) (hD4 : c = .POmegaPlus → n ≠ 4) (hℓ3 : ℓ ≠ 3)
    {E : Subgroup (MulAut G)} (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 2)
    (hout : ¬ E ≤ (MulAut.conj : G →* MulAut G).range) : UniPlaneGen ℓ E := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have : Fact (3 : ℕ).Prime := ⟨hp⟩
  obtain ⟨-, -, hsimple, hperf⟩ := orth_facts_of_model hc hM
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact Group.IsPerfect.not_isMulCommutative G ⟨⟨fun a b => hcon a b⟩⟩
  have hpair := subfieldPairOmegaThree_holds
  rcases hc with rfl | rfl | rfl
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
    refine orthOut_uniPlaneGen_of_mulEquiv hnab (coordinateOddWitnessEquiv K e) hp
      (fieldAutData_odd_three hpair.1 hadm hK hp rfl (Ne.symm hℓ3)) (fun τ hτ => ?_) hE hcard hout
    rw [← hchar]
    exact orthOut3_fixedSubgroup_le_closure_odd hadm hK hp hp2 (Ne.symm hℓ3) hτ
  · obtain ⟨hadm, K, _, _, hK, ⟨e⟩⟩ := id hM
    have hn5 : 5 ≤ n := by
      have := hD4 rfl
      have := hadm.2.2
      omega
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hadm.1 hadm.2.1 hK
    set ψ := coordinatePlusWitnessEquiv K e
    have hEQ : E.map (MulAut.congr ψ).toMonoidHom ≤ matrixProjectiveImage (coordinateQuadPlus n K) := by
      rw [matrixProjectiveImage_eq_top_plus K n hn5]
      exact le_top
    have h := orthOut3_uniPlaneGen_plus hadm hK hℓ3 (isElemAbelian_map_congr ψ hE)
      (by rw [card_map_congr, hcard]) hEQ (not_le_range_conj_map_congr ψ hout)
    rw [hchar] at h
    exact (uniPlaneGen_map_congr ψ ℓ E).1 h
  · obtain ⟨hℓ, hf, hn⟩ := id hM.1
    have hn1 : 1 ≤ n := by omega
    obtain ⟨σ, hσE, hσinn⟩ : ∃ σ ∈ E, ∀ g : G, σ ≠ MulAut.conj g := by
      by_contra hcon
      push Not at hcon
      exact hout fun σ hσ => (hcon σ hσ).imp fun g hg => hg.symm
    have hσ1 : σ ≠ 1 := fun h => hσinn 1 (by rw [h, map_one])
    have hσo : IsOuterOfOrder 3 σ := ⟨orderOf_eq_prime (hE.2 σ hσE) hσ1, hσinn⟩
    obtain ⟨e, K, _, _, k, σ₀, b, c, he, -, hk, hK, hσ₀, hfix, hirr, ⟨ψ⟩⟩ :=
      exists_rational_model_minus_three hn1 hM hp rfl hσo
    have hchar : ringChar K = ℓ := ringChar_eq_of_card_eq hℓ (Nat.mul_pos he hp.pos) hK
    refine orthOut_uniPlaneGen_of_mulEquiv hnab ψ hp
      (fieldAutData_minus_rational_three hpair.2.2 hn hn1 hℓ he hp rfl (Ne.symm hℓ3) hk hK hσ₀ hfix b c hirr)
      (fun τ hτ => ?_) hE hcard hout
    rw [← hchar]
    exact orthOut3_fixedSubgroup_le_closure_minus hn hn1 hℓ he hp hp2 (Ne.symm hℓ3) hk hK hσ₀ hfix b c hirr hτ

end Model

section Cat

theorem orthOut3_uniSeitzPlanes_orthogonal_outer_three_nonD4 :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1 ∧
      ¬ IsDFourIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, rfl, horth, hD4⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : q.p ≠ 3 := fun h => hpd (by simp [h])
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut3_uniPlaneGen_of_model (Or.inl rfl) (n := r) (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun h => nomatch h) hq' hE hc hout
    simpa using h
  ·
    have hq' : q.p ≠ 3 := fun h => hpd (by simp [h])
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut3_uniPlaneGen_of_model (Or.inr (Or.inl rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun _ h4 => hD4 ⟨q, congrArg (fun r' => TauCeti.LieTypeIndex.D r' q) h4⟩) hq' hE hc hout
    simpa using h
  ·
    have hq' : q.p ≠ 3 := fun h => hpd (by simp [h])
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h := orthOut3_uniPlaneGen_of_model (Or.inr (Or.inr rfl)) (n := r) (ℓ := q.p)
      (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ (fun h => nomatch h) hq' hE hc hout
    simpa using h

@[expose] def orthOut3_SimilarityPlane (d : TauCeti.ValidLieTypeIndex) (E : Subgroup (MulAut (Cat d))) : Prop :=
  ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = d.1.characteristic ^ f ∧
    ∃ ψ : Cat d ≃* matrixProjectiveDerived (coordinateQuadPlus 4 K),
      E.map (MulAut.congr ψ).toMonoidHom ≤ matrixProjectiveImage (coordinateQuadPlus 4 K)

theorem orthOut3_uniSeitzPlanes_dFour_similarity :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsDFourIndex d.1 ∧
      orthOut3_SimilarityPlane d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hout, rfl, ⟨q, rfl⟩, f, K, _, _, hK, ψ, hEQ⟩
  have hK' : Nat.card K = q.p ^ f := by simpa using hK
  have hq' : q.p ≠ 3 := fun h => hpd (by simp [h])
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK'
      exact absurd hK' (Finite.one_lt_card (α := K)).ne'
    · exact h0
  have hchar : ringChar K = q.p := ringChar_eq_of_card_eq q.prime_p hf hK'
  have h := orthOut3_uniPlaneGen_plus ⟨q.prime_p, hf, le_rfl⟩ hK' hq' (isElemAbelian_map_congr ψ hE)
    (by rw [card_map_congr, hc]) hEQ (not_le_range_conj_map_congr ψ hout)
  rw [hchar] at h
  simpa using (uniPlaneGen_map_congr ψ q.p E).1 h

theorem orthOut3_uniSeitzPlanes_orthogonal_outer_three_all :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1 ∧
      (IsDFourIndex d.1 → orthOut3_SimilarityPlane d E) :=
  UniSeitzPlanes.of_cover (fun d _ _ _ E ⟨hout, hp3, horth, hsim⟩ => by
      by_cases hD4 : IsDFourIndex d.1
      · exact Or.inr ⟨hout, hp3, hD4, hsim hD4⟩
      · exact Or.inl ⟨hout, hp3, horth, hD4⟩)
    orthOut3_uniSeitzPlanes_orthogonal_outer_three_nonD4 orthOut3_uniSeitzPlanes_dFour_similarity

theorem orthOut3_uniSeitzPlanes_orthogonal_outer_three :
    Inputs2311c.UniSeitzPlanes fun d p E => ¬ CFSG.LieType.SeitzGeneration.InnerPlane d p E ∧ p = 3 ∧
      CFSG.LieType.SeitzGeneration.IsOrthogonalIndex d.1 ∧ d.1.characteristic ≠ 2 ∧
      (CFSG.LieType.SeitzGeneration.IsDFourIndex d.1 → orthOut3_SimilarityPlane d E) :=
  UniSeitzPlanes.mono (fun _ _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩)
    orthOut3_uniSeitzPlanes_orthogonal_outer_three_all

end Cat

end OrthOut3


section E6FieldThree

open CFSG.LieType.SeitzGeneration.ExcOuterLeOne CFSG.LieType.SeitzGeneration.ExcWideThree
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Fischer

theorem eq_top_of_kernel_escape {P : Type*} [Group P] [Finite P] {N : Subgroup (MulAut P)} [N.Normal]
    {R : Subgroup P} (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤)
    (hker : ∀ ι ∈ N, (∀ x ∈ R, ι x = x) → ι = 1) {α ι ψa ψb : MulAut P} (hι1 : ι ≠ 1)
    (hιN : ι ∈ N) (hFa : fixedSubgroup (ψa * α * ψa⁻¹) = R)
    (hFb : fixedSubgroup (ψb * (α * ι) * ψb⁻¹) = R) {X : Subgroup P}
    (hXa : fixedSubgroup α ≤ X) (hXb : fixedSubgroup (α * ι) ≤ X) : X = ⊤ := by
  rw [fixedSubgroup_conj] at hFa hFb
  have hle : R ≤ X.map ψa.toMonoidHom := by
    rw [← hFa]
    exact Subgroup.map_mono hXa
  have hXeq : X = (X.map ψa.toMonoidHom).comap ψa.toMonoidHom :=
    (Subgroup.comap_map_eq_self_of_injective ψa.injective X).symm
  rcases hmax _ hle with h | h
  · exfalso
    have hXα : X = fixedSubgroup α := by
      rw [hXeq, h, ← hFa]
      exact Subgroup.comap_map_eq_self_of_injective ψa.injective _
    have hsub : fixedSubgroup (α * ι) ≤ fixedSubgroup α := hXα ▸ hXb
    have hcard : Nat.card (fixedSubgroup (α * ι)) = Nat.card (fixedSubgroup α) := by
      have h1 := congrArg (fun H : Subgroup P => Nat.card H) hFb
      have h2 := congrArg (fun H : Subgroup P => Nat.card H) hFa
      rw [Subgroup.card_map_of_injective ψb.injective] at h1
      rw [Subgroup.card_map_of_injective ψa.injective] at h2
      rw [h1, h2]
    have heq : fixedSubgroup (α * ι) = fixedSubgroup α :=
      Subgroup.eq_of_le_of_card_ge hsub (le_of_eq hcard.symm)
    have hιfix : ∀ x ∈ fixedSubgroup α, ι x = x := by
      intro x hx
      have hx' : x ∈ fixedSubgroup (α * ι) := heq ▸ hx
      have h1 : (α * ι) x = x := hx'
      have h2 : α x = x := hx
      simp only [MulAut.mul_apply] at h1
      exact α.injective (h1.trans h2.symm)
    have hι'fix : ∀ x ∈ R, (ψa * ι * ψa⁻¹) x = x := by
      intro x hx
      rw [← hFa] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      show (ψa * ι * ψa⁻¹) (ψa y) = ψa y
      simp [MulAut.mul_apply, hιfix y hy]
    have h1 := hker _ (‹N.Normal›.conj_mem ι hιN ψa) hι'fix
    apply hι1
    have h2 : ψa⁻¹ * (ψa * ι * ψa⁻¹) * ψa = ι := by group
    rw [← h2, h1]
    simp
  · rw [hXeq, h]
    exact Subgroup.comap_top _

theorem cubeDescent_of_not_three_dvd {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (h : ¬ 3 ∣ Nat.card (fixSubfield σ) - 1) : CubeDescent σ := by
  classical
  intro b _ _
  have : Fintype (fixSubfield σ) := Fintype.ofFinite _
  have hcop : (Nat.card (fixSubfield σ)ˣ).Coprime 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card]
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm
  refine ⟨(powCoprime hcop).symm b, ?_⟩
  have := (powCoprime hcop).apply_symm_apply b
  rw [powCoprime_apply] at this
  exact this.symm


theorem uniPlaneGen_E6_field_three {K : Type} [Field K] [Finite K] (hK3 : ringChar K ≠ 3)
    (hK2 : ringChar K ≠ 2) (hnd : ¬ 3 ∣ Nat.card K - 1)
    (E : Subgroup (MulAut ↥(adjointGroup Tag.E6 K))) [hE : CFSG.IsElementaryAbelian 3 ↥E]
    (hEc : Nat.card ↥E = 3 ^ 2) (hout : ¬ E ≤ innerAut (adjointGroup Tag.E6 K)) :
    UniPlaneGen (ringChar K) E := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have : CharP K (ringChar K) := ringChar.charP K
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have : Finite (adjointGroup Tag.E6 K) := Subtype.finite
  have hdiag : e6Inndiag K = innerAut (adjointGroup Tag.E6 K) := e6Inndiag_eq_innerAut_of_not_dvd K hnd
  have hout' : ¬ E ≤ e6Inndiag K := hdiag ▸ hout
  obtain ⟨Θ, -, -, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨ι, hιE, hι1, hιker⟩ :=
    exists_ne_one_mem_ker_of_plane Tag.E6 (Or.inl rfl) Nat.prime_three (by norm_num) Θ E hEc
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E, α ∉ e6Inndiag K := by
    by_contra h
    push Not at h
    exact hout' fun x hx => h x hx
  have hιdiag : ι ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι).1 hιker
  have hα1 : α ≠ 1 := fun h => hα (h ▸ one_mem _)
  have hβ : α * ι ∉ e6Inndiag K := fun h => hα (by simpa using mul_mem h (inv_mem hιdiag))
  have hβ1 : α * ι ≠ 1 := fun h => hβ (h ▸ one_mem _)
  have hα3 : α ^ 3 = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian α hαE
  have hβ3 : (α * ι) ^ 3 = 1 :=
    CFSG.elemPow_eq_one_of_isElementaryAbelian (α * ι) (E.mul_mem hαE hιE)
  obtain ⟨σa, hσa, -, ψa, hψa⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hα3 hα
  obtain ⟨σb, hσb, -, ψb, hψb⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos K hK
    Nat.prime_three (by norm_num) hβ3 hβ
  have hfix3 : ∀ σ : K ≃+* K, orderOf σ = 3 → ¬ 3 ∣ Nat.card (fixSubfield σ) - 1 := by
    intro σ hσ h3
    apply hnd
    have hcard := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hσ] at hcard
    rw [hcard]
    exact h3.trans (Nat.sub_one_dvd_pow_sub_one _ 3)
  have hbig : ∀ σ : K ≃+* K, orderOf σ = 3 → 2 < Nat.card (fixSubfield σ) := by
    intro σ _
    have hchar : ringChar (fixSubfield σ) = ringChar K := by
      have : CharP (fixSubfield σ) (ringChar K) := inferInstance
      exact ringChar.eq _ _
    have := orthU3_three_le_card (K := fixSubfield σ) (by rw [hchar]; exact hK2)
    omega
  have hgen : ∀ (β ψ : MulAut (adjointGroup Tag.E6 K)) (σ : K ≃+* K), orderOf σ = 3 →
      ψ * β * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ → β ∈ E → β ≠ 1 →
        fixedSubgroup β ≤ uniPlaneClosure (ringChar K) E := by
    intro β ψ σ hσ hψ hβE hβ1'
    have h1 := fixedSubgroup_le_closure_of_conj hψ (fixedSubgroup_entrywise_le_closure σ
      (entrywiseFixedGroup_eq_fixedFieldImage_E6_of_pow σ (cubeDescent_of_not_three_dvd σ
        (hfix3 σ hσ))))
    refine h1.trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hx, hxr⟩
    exact mem_uniPlaneClosure hβE hβ1' hx (n := 1) (by rw [pow_one]; exact hxr)
  have hRfix : fixedSubgroup (entrywiseAdjointAut Tag.E6 σb) =
      fixedSubgroup (entrywiseAdjointAut Tag.E6 σa) :=
    fixedSubgroup_eq_of_zpowers_eq (entrywiseAdjointAutHom (τ := Tag.E6))
      (zpowers_ringEquiv_eq_of_orderOf hℓ n.pos hK hσb hσa)
  refine eq_top_of_kernel_escape (N := Θ.ker)
    (R := fixedSubgroup (entrywiseAdjointAut Tag.E6 σa))
    (subfieldMaximalAllThree_E6 K σa 3 rfl (fun h => hK3 h.symm) hσa) ?_ hι1 hιker
    (by rw [hψa]) (by rw [hψb, hRfix]) (hgen α ψa σa hσa hψa hαE hα1)
    (hgen (α * ι) ψb σb hσb hψb (E.mul_mem hαE hιE) hβ1)
  intro ι' hι'ker hι'fix
  have hι'diag : ι' ∈ e6Inndiag K := (mem_ker_iff_mem_e6Inndiag Θ hker ι').1 hι'ker
  refine eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σa) (hbig σa hσa) hι'diag ?_
  intro x hx
  apply hι'fix
  have h1 := fixedFieldImage_le (σ := σa) hx
  rw [CFSG.RankThree.PartOne.CTP.mem_fixedSubgroup]
  refine Subtype.ext ?_
  rw [coe_entrywiseAdjointAut]
  exact ((mem_entrywiseFixedGroup).1 h1).2

theorem uniSeitzPlanes_E6_field_three :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧
      ∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ ¬ 3 ∣ q.card - 1 ∧ q.p ≠ 2 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, rfl, q, rfl, hq3, hq2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, _, _, hKq, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ E.map (MulAut.congr e).toMonoidHom ≤ innerAut (adjointGroup Tag.E6 K) := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => by
      obtain ⟨g, hg⟩ := h hφ
      exact ⟨g, hg⟩
  have h := (uniPlaneGen_map_congr e _ E).1 (uniPlaneGen_E6_field_three (K := K)
    (by rw [hchar]; exact fun h => hpd (by simpa using h.symm)) (by rw [hchar]; exact hq2) (by rw [hKq]; exact hq3) _ hc' hout')
  rw [hchar] at h
  simpa using h

end E6FieldThree

section ReeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree TauCeti


theorem uniSeitzPlanes_reeG2_inner :
    UniSeitzPlanes fun d p E => InnerPlane d p E ∧ IsReeG2Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hin, ⟨m, rfl⟩⟩
  have hp3 : p ≠ 3 := by simpa using hpd
  have hp4 : 3 < p := by
    have := hp.two_le
    omega
  obtain ⟨X, _, _, _, hX, ⟨e⟩⟩ := exists_reeGamma_equiv_cat_G2 hv
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.reeG2 m, hv⟩ →* MulAut _) :=
    conj_injective_of_mulEquiv e
      (conj_injective_of_center_eq_bot (ReeTag.center_reeGamma_G2_eq_bot hX))
  exact (false_of_inner_plane_of_no_plane hinj
    (fun F hF hc' => no_plane_cat_reeG2 hv hp hp4 F hF hc') hE hc hin).elim

end ReeInner

section TwE6Parabolic

open CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWeight CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.CTP
  CFSG.LieType.SeitzGeneration.ExcWideThree
open scoped Pointwise


theorem twE6_le_closure_uniCentSet (k : Type) [Field k] [Finite k]
    {r p : ℕ} [Fact r.Prime] [Fact p.Prime] [CharP k r] (hrp : r ≠ p) (σ : k ≃+* k)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.E6 k σ.toRingHom)]
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {A : Subgroup (ModGL TwistTag.E6.tag k)} (hA : IsElementaryAbelian p A)
    (hcard : p ^ 2 ≤ Nat.card A) {x : ModGL TwistTag.E6.tag k}
    (hx : x ∈ Subgroup.normalizer
      (graphFixedRootGroup TwistTag.E6 k σ.toRingHom : Set (ModGL TwistTag.E6.tag k)))
    (hAx : A.map (MulAut.conj x).toMonoidHom ≤
      graphFixedParabolic TwistTag.E6 k σ.toRingHom J ⊔ twistedE6DiagGL k σ) :
    graphFixedRootGroup TwistTag.E6 k σ.toRingHom ≤
      Subgroup.closure (uniCentSet (graphFixedRootGroup TwistTag.E6 k σ.toRingHom) A r) := by
  have := finite_modGL (τ := TwistTag.E6.tag) (K := k)
  haveI := hA
  obtain ⟨w₀, δ, hmax, hδδ, hδ, hcomm⟩ := exists_longest_fixed_data TwistTag.E6
  have hw : w₀ ∈ relWeylTwist TwistTag.E6 :=
    mem_relWeylTwist_of_forall_length_le hmax
  obtain ⟨-, hR, hH⟩ := canonical_weyl_root_transport TwistTag.E6.tag k
  set C := graphFixedRootGroup TwistTag.E6 k σ.toRingHom
  have hnC : canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀ ∈ C :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀
  have hpos : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_single TwistTag.E6.tag i), hδ]
  have hneg : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_neg_single TwistTag.E6.tag i), smul_neg, hδ, neg_neg]
  have hpos' : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1)) n, hneg, hδδ]
  have hneg' : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1)) n, hpos, hδδ]
  set J' := (fun i => TwistTag.E6.orbitIndex (δ i)) '' TwistTag.E6.orbitUnion J
  have hJJ' : δ '' TwistTag.E6.orbitUnion J = TwistTag.E6.orbitUnion J' := image_orbitUnion_eq
      hcomm J
  have hJ'J : δ '' TwistTag.E6.orbitUnion J' = TwistTag.E6.orbitUnion J := by
    rw [← hJJ', image_image_of_involutive hδδ]
  have hLn : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J :=
    map_conj_graphFixedParabolicLevi_le hnC (by
      rw [← hJ'J]
      exact map_conj_parabolicLevi_le_of_rootSubgroup (hH w₀) hpos hneg _)
  have hLn' : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J).map (MulAut.conj
      n⁻¹).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J' :=
    map_conj_graphFixedParabolicLevi_le (inv_mem hnC) (by
      rw [← hJJ']
      exact map_conj_parabolicLevi_le_of_rootSubgroup (inv_mem (hH w₀)) hpos' hneg' _)
  set Q := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J
  set Q' := (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J
  obtain ⟨-, -, -, -, -, -, -, -, hQP', hQnorm', hLP', -, -, -, -, -, hfin', -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J'
  have hQp : IsPGroup r Q := hfin r
  have hQ'p : IsPGroup r Q' := (hfin' r).map _
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := hQP.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J)
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hnC ((hQP'.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J'))
      hq))
      (inv_mem hnC)
  have hPQ : graphFixedParabolic TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hPQ' : graphFixedParabolic TwistTag.E6 k σ.toRingHom J' ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J' : Set (ModGL
      TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').1 hQnorm'
  have hLQ : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) := hLP.trans hPQ
  have hLQ' : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q' : Set (ModGL TwistTag.E6.tag k)) := fun m hm => by
    have h := mem_normalizer_map_conj_inv (n := n⁻¹) (m := m)
      (H := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J')
      (hPQ' (hLP' (hLn' (Subgroup.mem_map_of_mem _ hm))))
    rwa [inv_inv] at h
  have hgen : C ≤ Q ⊔ Q' ⊔ graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J := by
    refine sup_le ((graphFixedPosUnipotent_le_sup σ J).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
    rw [← map_conj_graphFixedPosUnipotent hmax]
    refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup σ J')).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left) (hLn.trans le_sup_right)
  have hLC : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤ C :=
    hLP.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J)
  have hAx' : A.map (MulAut.conj x).toMonoidHom ≤
      Q ⊔ (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ⊔ twistedE6DiagGL k σ) := by
    rw [← sup_assoc]
    have h := graphFixedParabolic_eq_radical_sup_levi k σ J
    rw [h] at hAx
    exact hAx
  exact le_closure_uniCentSet_of_normalizing hrp hQC hQ'C hLC (twistedE6DiagGL_le_normalizer_C0 k σ)
    hQp hQ'p hQ1 hLQ hLQ' (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical k σ J)
    (twistedE6DiagGL_le_normalizer_opposite k σ hw J') hgen hcard hx hAx'

theorem twE6InndiagUniGeneration_aux (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (f : ℕ) (hp : (ringChar K).Prime) (hf : 1 ≤ f)
    (hK3 : ringChar K ≠ 3) (hσq : ∀ c, σ c = c ^ (ringChar K ^ f))
    (hKq : Nat.card K = (ringChar K ^ f) ^ 2)
    (A : Subgroup (ModGL (TwTag K σ hσ) K)) (hAle : A ≤ twistedE6InndiagGL K σ)
    (hAEA : CFSG.IsElementaryAbelian 3 A) (hAcard : 3 ^ 2 ≤ Nat.card A)
    (R : Subgroup (ModGL (TwTag K σ hσ) K)) (hRC : R ≤ twistedE6RootGroup K σ)
    (hRp : IsPGroup (ringChar K) R) (hR1 : R ≠ ⊥)
    (hRn : A ≤ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K))) :
    (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) ≤
      Subgroup.closure (uniCentSet (twistedE6RootGroup K σ) A (ringChar K)) := by
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := TwTag K σ hσ) (K := K)
  haveI := hAEA
  have hcardTw : Nat.card K = (ringChar K ^ f) ^ TwistTag.E6.order := hKq
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 hp hf K hcardTw σ.toRingHom hσq
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := CFSG.LieType.SeitzGeneration.nonempty_derivedCentralQuotient_equiv _ _
    hperf.2.2.1 hZ
  haveI hSimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (CFSG.LieType.Simplicity.fam_2e6_simplicity
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ringChar K) f
      ⟨⟨hp, hf, rfl⟩, K, inferInstance, inferInstance, hcardTw, σ.toRingHom, hσq,
        ⟨ψ.symm⟩⟩).2
  obtain ⟨M, -, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, -, F, hF, -, ⟨g₀, hg₀, l₀, hl₀, hl₀1, hgl₀⟩,
      hdom, hsemi⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K)
      (ringChar K) R hRC hRp hR1
  obtain ⟨hJ, -, -, -, -⟩ := hdom g₀ hg₀ l₀ hl₀ hl₀1 hgl₀
  set J₀ : Set (Fin TwistTag.E6.foldedTag.rank) :=
    (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).face l₀ with hJ₀
  have hC0Inn : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ twistedE6InndiagGL K σ :=
    le_sup_left
  have hg₀I : g₀ ∈ twistedE6InndiagGL K σ := hC0Inn hg₀
  have hPh_le : graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ ≤
      twistedE6InndiagGL K σ :=
    sup_le ((graphFixedParabolic_le TwistTag.E6 K σ.toRingHom J₀).trans hC0Inn)
      (twistedE6DiagGL_le_twistedE6InndiagGL K σ)
  have hstabN : ∀ x : ModGL (TwTag K σ hσ) K, x ∈ twistedE6InndiagGL K σ →
      x ∈ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K)) →
      ∀ c : ℝ, (F c).map (x : Module.End K (RootModule (TwTag K σ hσ) K)) = F c := by
    intro x hx hxN c
    obtain ⟨c₀, hc₀, t₀, ht₀, rfl⟩ := mem_twistedE6InndiagGL_decompTw K σ hσ hx
    set s : RootModule (TwTag K σ hσ) K ≃ₗ[K] RootModule (TwTag K σ hσ) K :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (RootModule (TwTag K σ hσ) K) t₀
      with hs_def
    have hs_apply : ∀ v, s v = (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) v :=
      fun v => rfl
    have hs_symm : ∀ v, s.symm v =
        ((t₀⁻¹ : ModGL (TwTag K σ hσ) K) : Module.End K (RootModule (TwTag K σ hσ) K)) v := by
      intro v
      rw [LinearEquiv.symm_apply_eq, hs_apply, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_eq_id, LinearMap.id_apply]
    have hs_eq : ∀ g : ModGL (TwTag K σ hσ) K, semilinearConjUnit s g = t₀ * g * t₀⁻¹ := by
      intro g
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [coe_semilinearConjUnit, semilinearConj_apply, hs_symm, hs_apply, Units.val_mul,
        Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hsC : ∀ g : ModGL (TwTag K σ hσ) K,
        semilinearConjUnit s g ∈
            (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group ↔
          g ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group := by
      intro g
      rw [hs_eq]
      exact (Subgroup.mem_normalizer_iff.1 (twistedE6DiagGL_le_normalizer_C0 K σ ht₀) g).symm
    have hsW : ∀ χ ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weights,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
          s.toLinearMap =
          (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace
            ((LinearIsometryEquiv.refl ℝ
              (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) χ) := by
      intro χ _
      exact map_weightSpace_eq_of_mem_twistedE6DiagGL K σ hσ ht₀ χ
    have hQ' : ∀ x' : ModGL (TwTag K σ hσ) K, x' ∈ R ↔
        ∃ q ∈ R, c₀ * semilinearConjUnit s q * c₀⁻¹ = x' := by
      intro x'
      simp only [hs_eq]
      constructor
      · intro hx'
        refine ⟨(c₀ * t₀)⁻¹ * x' * (c₀ * t₀), ?_, ?_⟩
        · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) x').1 hx'
          rwa [inv_inv] at h'
        · group
      · rintro ⟨q, hq, rfl⟩
        have h' := (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
        have e : c₀ * (t₀ * q * t₀⁻¹) * c₀⁻¹ = c₀ * t₀ * q * (c₀ * t₀)⁻¹ := by group
        rw [e]
        exact h'
    have hcov := hsemi (RingHom.id K) (RingHom.id K) s hsC (LinearIsometryEquiv.refl ℝ _)
      (by simp) hsW c₀ hc₀ R hQ'
    have h1 := hcov.2.2 g₁ hg₁ l₁ hl₁ hgl₁ c
    have h2 := hF g₁ hg₁ l₁ hl₁ hgl₁ c
    have e : (F c).map s.toLinearMap =
        (F c).map (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) := rfl
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, ← e]
    exact h1.symm.trans h2
  have hstabG : ∀ x ∈ A, g₀⁻¹ * x * g₀ ∈
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    intro x hx
    have hxI := hAle hx
    have hxN := hRn hx
    have hgI : g₀⁻¹ * x * g₀ ∈ twistedE6InndiagGL K σ :=
      mul_mem (mul_mem (inv_mem hg₀I) hxI) hg₀I
    have key : ∀ c : ℝ,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c).map
          ((g₀⁻¹ * x * g₀ : ModGL (TwTag K σ hσ) K) :
            Module.End K (RootModule (TwTag K σ hσ) K)) =
        (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c := by
      intro c
      have h1 := hF g₀ hg₀ l₀ hl₀1 hgl₀ c
      have h2 := hstabN x hxI hxN c
      rw [submodule_map_units_mul, submodule_map_units_mul, h1, h2, ← h1,
        ← submodule_map_units_mul, inv_mul_cancel, Units.val_one, Module.End.one_eq_id,
        Submodule.map_id]
    exact mem_twistedParabolic_sup_torus_of_stab K σ hσ hl₀ hgI key
  have hA0 : A.map (MulAut.conj g₀⁻¹).toMonoidHom ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hstabG x hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h
  haveI hA0e : IsElementaryAbelian 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.map _
  have hA0p : IsPGroup 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) :=
    IsElementaryAbelian.isPGroup 3 _
  exact twE6_le_closure_uniCentSet K hK3 σ hJ (A := A) hAEA hAcard
    (twistedE6InndiagGL_le_normalizer K σ (inv_mem hg₀I)) hA0

theorem twE6InndiagParabolic_uni (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK3 : ringChar K ≠ 3) (hσ : ∀ c, σ c = c ^ q) (hK : Nat.card K = q ^ 2)
    (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    (hE : E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ) (hEab : CFSG.IsElementaryAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 2) (hnorm : TwE6NormalizesR K σ E) :
    UniPlaneGen (ringChar K) E := by
  classical
  obtain ⟨hp, f, hf, rfl⟩ := ExcHighThree.exists_pow_ringChar_of_card_sq K q hK
    (by
      by_contra h
      have hq : q ≤ 1 := by omega
      have : Nat.card K ≤ 1 := by
        rw [hK]; nlinarith [Nat.zero_le q]
      have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
      omega)
  have hinj := twistedE6InndiagConj_injective hp hf hK σ hσ
  obtain ⟨R, hRC, hR1, hRp, hRn⟩ := matrix_of_twE6NormalizesR σ E hE hnorm
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    have hsq : σ ^ 2 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hσσ : σ (σ c) = c := by
        haveI := Fintype.ofFinite K
        rw [hσ (σ c), hσ c, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using hσσ
    exact hsq
  have hAle : twPlanePre K σ E ≤ twistedE6InndiagGL K σ := by
    rintro _ hx
    obtain ⟨g, rfl, -⟩ := (mem_twPlanePre_iff K σ E _).1 hx
    exact g.2
  have hAcomm : ∀ a ∈ twPlanePre K σ E, ∀ b ∈ twPlanePre K σ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, rfl, hg⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    obtain ⟨h, rfl, hh⟩ := (mem_twPlanePre_iff K σ E b).1 hb
    have : g * h = h * g := by
      apply hinj
      rw [map_mul, map_mul]
      exact congrArg Subtype.val (hEab.is_comm.comm ⟨_, hg⟩ ⟨_, hh⟩)
    exact congrArg Subtype.val this
  have hAEA : CFSG.IsElementaryAbelian 3 (twPlanePre K σ E) :=
    CFSG.IsElementaryAbelian.of_forall hAcomm fun a ha =>
      pow_three_eq_one_of_mem_twPlanePre _ f hp hf K hK σ hσ E ha
  have hAcard : Nat.card (twPlanePre K σ E) = 3 ^ 2 := by
    rw [card_twPlanePre _ f hp hf K hK σ hσ E hE]
    exact hcard
  have hgen := twE6InndiagUniGeneration_aux K σ hσ2 f hp hf hK3 hσ hK (twPlanePre K σ E) hAle hAEA
    hAcard.ge R hRC hRp hR1 hRn
  have hsub : uniCentSet (twistedE6RootGroup K σ) (twPlanePre K σ E) (ringChar K) ⊆
      (uniPlaneClosure (ringChar K) E).map (twistedE6RootGroup K σ).subtype := by
    rintro y ⟨hyC, ⟨a, ha, ha1, hya⟩, n, hn⟩
    obtain ⟨g, rfl, hgE⟩ := (mem_twPlanePre_iff K σ E a).1 ha
    refine ⟨⟨y, hyC⟩, mem_uniPlaneClosure hgE ?_ ?_ (n := n) ?_, rfl⟩
    · intro h1
      have : g = 1 := hinj (by rw [h1, map_one])
      exact ha1 (by rw [this]; rfl)
    · apply Subtype.ext
      rw [twistedE6InndiagConj_apply, mul_inv_eq_iff_eq_mul]
      exact hya.symm
    · apply Subtype.ext
      simpa using hn
  have hle : (twistedE6RootGroup K σ : Subgroup (ModGL TwistTag.E6.tag K)) ≤
      (uniPlaneClosure (ringChar K) E).map (twistedE6RootGroup K σ).subtype :=
    hgen.trans ((Subgroup.closure_le _).2 hsub)
  rw [UniPlaneGen, eq_top_iff]
  intro y _
  obtain ⟨t, ht, hty⟩ := hle y.2
  have : t = y := Subtype.ext hty
  rw [← this]
  exact ht

@[expose] def IsTwE6DiagParabolicPlane (d : TauCeti.ValidLieTypeIndex)
    (E : Subgroup (MulAut (CFSG.LieType.SeitzGeneration.Cat d))) : Prop :=
  ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
    Nat.card K = (q.p ^ q.exponent) ^ 2 ∧ (∀ c, σ c = c ^ (q.p ^ q.exponent)) ∧
    ∃ e : CFSG.LieType.SeitzGeneration.Cat d ≃* twistedE6RootGroup K σ,
      E.map (MulAut.congr e).toMonoidHom ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ ∧
      TwE6NormalizesR K σ (E.map (MulAut.congr e).toMonoidHom)

theorem uniSeitzPlanes_twE6_diag_parabolic :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ p = 3 ∧ IsTwE6DiagParabolicPlane d E := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨-, rfl, q, rfl, K, _, _, σ, hK, hσ, e, hdiag, hnorm⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpq : 3 ≠ q.p := by simpa [TauCeti.ValidLieTypeIndex.characteristic] using hpd
  have hK' : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  have hchar : ringChar K = q.p := ringChar_eq_of_card_pow q.prime_p q.exponent_pos K hK'
  have hK3 : ringChar K ≠ 3 := by
    rw [hchar]
    exact fun h => hpq h.symm
  have hEi : CFSG.IsElementaryAbelian 3 (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = 3 ^ 2 := by
    rw [card_map_congr, hc]
  have h := (uniPlaneGen_map_congr e _ E).1
    (twE6InndiagParabolic_uni K σ (q.p ^ q.exponent) hK3 hσ hK _ hdiag hEi hc' hnorm)
  rw [hchar] at h
  simpa using h

end TwE6Parabolic

section TwOut

open CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section Generic

theorem twOut_pow_pow_card_eq_one {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime) {x : G} {n : ℕ}
    (hx : x ^ (r ^ n) = 1) : x ^ (r ^ Nat.card G) = 1 := by
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hr).1 (orderOf_dvd_of_pow_eq_one hx)
  have h1 : r ^ m ≤ Nat.card G := hm ▸ Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard x)
  have h2 : m ≤ Nat.card G := ((Nat.lt_pow_self hr.one_lt).le).trans h1
  rw [← orderOf_dvd_iff_pow_eq_one, hm]
  exact Nat.pow_dvd_pow r h2

theorem twOut_uniPlaneGen_of_pow {S : Type*} [Group S] {r N : ℕ} {E : Subgroup (MulAut S)}
    (h : UniPlaneGen (r ^ N) E) : UniPlaneGen r E := by
  unfold UniPlaneGen at h ⊢
  rw [eq_top_iff, ← h]
  refine Subgroup.closure_mono ?_
  rintro s ⟨e, he, he1, hes, n, hn⟩
  exact ⟨e, he, he1, hes, N * n, by rwa [pow_mul]⟩

theorem twOut_uniPlaneGen_of_fieldAutData {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hd : FieldAutData K p)
    (hfix : ∀ τ : MulAut K, IsOuterOfOrder p τ → ∃ c β : MulAut K, c * τ * c⁻¹ = β ∧
      fixedSubgroup β ≤ Subgroup.closure {x | β x = x ∧ ∃ n : ℕ, x ^ (r ^ n) = 1})
    (E : Subgroup (MulAut K)) [CFSG.IsElementaryAbelian p E] (hEc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g : K, φ = MulAut.conj g) : UniPlaneGen r E := by
  refine twOut_uniPlaneGen_of_pow (N := Nat.card K) (uniPlaneGen_of_fieldAutData hnab hp hd
    (fun τ hτ => ?_) E hEc hout)
  obtain ⟨c, β, h, hβ⟩ := hfix τ hτ
  exact fixedSubgroup_le_closure_of_conj h (hβ.trans (Subgroup.closure_mono
    fun x ⟨h1, _, h2⟩ => ⟨h1, twOut_pow_pow_card_eq_one hr h2⟩))

theorem twOut_le_closure_of_mulEquiv {A B : Type*} [Group A] [Group B] {r : ℕ} {Γ : Subgroup A}
    {H : Subgroup B} (φ : Γ ≃* H)
    (hH : H ≤ Subgroup.closure {s | s ∈ H ∧ ∃ n : ℕ, s ^ (r ^ n) = 1}) :
    Γ ≤ Subgroup.closure {x | x ∈ Γ ∧ ∃ n : ℕ, x ^ (r ^ n) = 1} := by
  have hH' : ∀ y : H, y ∈ Subgroup.closure {z : H | ∃ n : ℕ, z ^ (r ^ n) = 1} := by
    intro y
    have h1 : Subgroup.closure {s | s ∈ H ∧ ∃ n : ℕ, s ^ (r ^ n) = 1} ≤
        (Subgroup.closure {z : H | ∃ n : ℕ, z ^ (r ^ n) = 1}).map H.subtype := by
      rw [Subgroup.closure_le]
      rintro s ⟨hs, n, hn⟩
      exact ⟨⟨s, hs⟩, Subgroup.subset_closure ⟨n, Subtype.ext (by simpa using hn)⟩, rfl⟩
    obtain ⟨z, hz, hzy⟩ := h1 (hH y.2)
    rwa [show z = y from Subtype.ext hzy] at hz
  intro x hx
  have h2 : (⟨x, hx⟩ : Γ) ∈ (Subgroup.closure {z : H | ∃ n : ℕ, z ^ (r ^ n) = 1}).map
      φ.symm.toMonoidHom := ⟨φ ⟨x, hx⟩, hH' _, by simp⟩
  rw [MonoidHom.map_closure] at h2
  have h3 := Subgroup.mem_map_of_mem Γ.subtype h2
  rw [MonoidHom.map_closure] at h3
  refine Subgroup.closure_mono ?_ h3
  rintro _ ⟨_, ⟨z, ⟨n, hn⟩, rfl⟩, rfl⟩
  refine ⟨(φ.symm z).2, n, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]
  rw [← SubgroupClass.coe_pow, ← map_pow, hn, map_one, OneMemClass.coe_one]


theorem twOut_graphFixedRootGroup_le_closure (t : TwistTag) {k : Type} [Field k] [Finite k] (ℓ : ℕ)
    [CharP k ℓ] (σ₀ : k →+* k) :
    graphFixedRootGroup t k σ₀ ≤
      Subgroup.closure {s | s ∈ graphFixedRootGroup t k σ₀ ∧ ∃ n : ℕ, s ^ (ℓ ^ n) = 1} := by
  obtain ⟨-, hU, -, hV⟩ := (positive_root_triangularity.{0, 0} t.tag).2 k ℓ
  refine sup_le (fun s hs => Subgroup.subset_closure
      ⟨graphFixedPosUnipotent_le_graphFixedRootGroup t k σ₀ hs, ?_⟩)
    (fun s hs => Subgroup.subset_closure
      ⟨graphFixedNegUnipotent_le_graphFixedRootGroup t k σ₀ hs, ?_⟩)
  · obtain ⟨n, hn⟩ := hU ⟨s, (Subgroup.mem_inf.1 hs).1⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  · obtain ⟨n, hn⟩ := hV ⟨s, (Subgroup.mem_inf.1 hs).1⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

end Generic

section TwE6

open CFSG.HardMathSupport.Lang.E6Descent


theorem twOut_fixedSubgroup_fieldActor_twE6_le_closure {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp3 : 3 < p) {η : K ≃+* K} (hη : orderOf η = p) :
    fixedSubgroup (fieldActor (t := TwistTag.E6) σ η) ≤
      Subgroup.closure {x | fieldActor (t := TwistTag.E6) σ η x = x ∧ ∃ n : ℕ, x ^ (ℓ ^ n) = 1} := by
  obtain ⟨φ⟩ := CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.twE6_fixedSubgroup_equiv_subfield
    hℓ hf hK σ hσ hp hp3 hη
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ
    (by omega : 1 ≤ f * 2) (by rw [hK, ← pow_mul])
  have : Finite (fixSubfield η) := Subtype.finite
  exact twOut_le_closure_of_mulEquiv φ (twOut_graphFixedRootGroup_le_closure TwistTag.E6 ℓ _)


theorem twOut_uniPlaneGen_twE6_outer {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (E : Subgroup (MulAut (twistedE6RootGroup K σ)))
    [CFSG.IsElementaryAbelian p E] (hc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) : UniPlaneGen ℓ E := by
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (twistedE6RootGroup K σ) := Subtype.finite
  obtain ⟨hsimple, hnab⟩ := isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.E6 K σ
    (finite_fixed_root_group_perfect TwistTag.E6 hℓ hf K hK σ.toRingHom fun c => hσ c).1
  have : IsSimpleGroup (twistedE6RootGroup K σ) := hsimple
  refine twOut_uniPlaneGen_of_fieldAutData hnab hp hℓ
    (fieldAutData_twE6_of_subfieldMaximalAll ExcOuterLeOne.subfieldMaximalAllTwE6 hℓ hf hK σ hσ hp hp5
      hpℓ) (fun α hα => ?_) E hc hout
  obtain ⟨ψ, η, hη, h⟩ := exists_conj_fieldActor_twE6 hℓ hf hK σ hσ hp (by omega) α hα
  exact ⟨ψ, _, h, twOut_fixedSubgroup_fieldActor_twE6_le_closure hℓ hf hK σ hσ hp (by omega) hη⟩

theorem twOut_uniSeitzPlanes_twistedE6_outer_five :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTwistedE6Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, hp5, ⟨q, rfl⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  have hpq : p ≠ q.p := by simpa using hpd
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := (uniPlaneGen_map_congr e _ E).1 (twOut_uniPlaneGen_twE6_outer q.prime_p q.exponent_pos hK σ
    hσ hp hp5 hpq _ hc' hout')
  simpa using h

end TwE6

section Triality

open CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial


theorem twOut_fixedSubgroup_fieldActor_D4_le_closure {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p) {δ : K ≃+* K} (hδ : orderOf δ = p) :
    fixedSubgroup (fieldActor (t := TwistTag.D4) σ δ) ≤
      Subgroup.closure {x | fieldActor (t := TwistTag.D4) σ δ x = x ∧ ∃ n : ℕ, x ^ (ℓ ^ n) = 1} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hf3 : 1 ≤ 3 * f := by omega
  obtain ⟨φ, hφ, hφord, -, hcardAut, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ hf3 hK3
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hpf3 : p ∣ 3 * f := by
    rw [← hδ, ← hcardAut]
    exact orderOf_dvd_natCard δ
  have hpf : p ∣ f := by
    rcases (Nat.Prime.dvd_mul hp).1 hpf3 with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h
      omega
    · exact h
  obtain ⟨f', hff'⟩ := hpf
  have hf'1 : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h] at hff'
      omega
    · exact h
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega) (by rw [hφord, hff']; exact ⟨p, by ring⟩),
      hφord, hff', show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hfix : fixedSubgroup (fieldActor σ δ) = fixedSubgroup (fieldActor σ δc) :=
    fixedSubgroup_eq_of_zpowers_eq (fieldActorHom (t := TwistTag.D4) σ)
      (zpowers_ringEquiv_eq_of_orderOf hℓ hf3 hK3 hδ hδcord)
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by rw [hK3, hff']; ring_nf
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by rw [hσ, hff', mul_comm f' p]
  obtain ⟨-, -, hk, -, -, -, hfixJ, -⟩ :=
    triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hf'1 hp.two_le hm3 K hK' σ hσ'
      δc hδc
  have : CharP (fixSubfield δc) ℓ := finite_field_prime_power_characteristic hℓ (by omega) hk
  have : Finite (fixSubfield δc) := Subtype.finite
  let e3 : ↥(fixedSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  let e4 : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield δc)
      (fixSubfieldRestrict σ δc).toRingHom) ≃* ↥(trialityFieldImage σ δc) :=
    Subgroup.equivMapOfInjective _ _ (baseChangeGL_injective (fixSubfield δc).subtype)
  exact twOut_le_closure_of_mulEquiv (((MulEquiv.subgroupCongr hfix).trans e3).trans e4.symm)
    (twOut_graphFixedRootGroup_le_closure TwistTag.D4 ℓ _)


theorem twOut_uniPlaneGen_D4_outer {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)))
    [CFSG.IsElementaryAbelian p E] (hc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) : UniPlaneGen ℓ E := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := Subtype.finite
  obtain ⟨hsimple, hnab⟩ := isSimpleGroup_graphFixedRootGroup_of_perfect TwistTag.D4 K σ
    (finite_fixed_root_group_perfect TwistTag.D4 hℓ hf K hK σ.toRingHom fun c => hσ c).1
  have : IsSimpleGroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := hsimple
  have hdata : FieldAutData (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) p ∧
      ∃ Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K),
        ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ := by
    rcases eq_or_ne ℓ 2 with rfl | hℓ2
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hf K hK σ hσ
      exact ⟨CFSG.RankThree.PartOne.SEITZ2.fieldAutData_trialityD4
        (CFSG.RankThree.PartOne.SEITZ8.subfieldPairD4_of_two
          CFSG.RankThree.PartOne.SEITZ8.subfieldPairD4Two_holds) hp hp5 hf hK hσ, Θ, hΘ⟩
    · obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := odd_triality_exact_automorphism_normal_form hℓ hℓ2 hf K hK σ hσ
      exact ⟨CFSG.HardMathSupport.Seitz.TrialityOdd.fieldAutData_trialityD4_odd
        CFSG.HardMathSupport.Seitz.TrialityOdd.subfieldPairD4Odd_proof hℓ hℓ2 hp hp5 hf hK hσ, Θ, hΘ⟩
  obtain ⟨hd, Θ, hΘ⟩ := hdata
  refine twOut_uniPlaneGen_of_fieldAutData hnab hp hℓ hd (fun α hα => ?_) E hc hout
  obtain ⟨hord, hout'⟩ := hα
  obtain ⟨hηord, -, ⟨h₀, hh₀⟩, -⟩ :=
    triality_noninner_large_prime_field_descent_and_local_core_trivial hℓ hf K hK σ hσ Θ hΘ hp
      (by omega) ⊤ le_top ⟨α, Subgroup.mem_top _⟩ (fun ⟨g, hg⟩ => hout' g hg.symm)
      (by rw [Subgroup.orderOf_mk]; exact hord)
  exact ⟨MulAut.conj h₀, _, hh₀, twOut_fixedSubgroup_fieldActor_D4_le_closure hℓ hf hK σ hσ hp hp5 hηord⟩


theorem twOut_uniSeitzPlanes_triality_outer_five :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTrialityIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, hp5, ⟨q, rfl⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, σ, hK, hσ, -, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 q hv
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := (uniPlaneGen_map_congr e _ E).1 (twOut_uniPlaneGen_D4_outer q.prime_p q.exponent_pos hK σ hσ
    hp hp5 _ hc' hout')
  simpa using h

end Triality

section ReeG2

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag


theorem twOut_reeGamma_le_closure {b : ℕ} {k : Type} [Field k] [Finite k] [CharP k G2.prime]
    (hk : Nat.card k = 3 ^ (2 * b + 1)) :
    G2.reeGamma k b ≤ Subgroup.closure {s | s ∈ G2.reeGamma k b ∧ ∃ n : ℕ, s ^ (3 ^ n) = 1} := by
  obtain ⟨-, hU, -, -⟩ := (positive_root_triangularity.{0, 0} G2.tag).2 k G2.prime
  intro x hx
  rw [← ree_normal_positive_generation G2 b k hk] at hx
  refine Subgroup.closure_mono ?_ hx
  rintro _ ⟨g, hg, u, hu, rfl⟩
  obtain ⟨n, hn⟩ := hU ⟨u, (Subgroup.mem_inf.1 hu).1⟩
  have hun : u ^ (G2.prime ^ n) = 1 := by simpa using congrArg Subtype.val hn
  refine ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.1 hu).2) (inv_mem hg), n, ?_⟩
  change (g * u * g⁻¹) ^ (G2.prime ^ n) = 1
  rw [conj_pow, hun, mul_one, mul_inv_cancel]

theorem twOut_fixedSubgroup_reeGammaFieldAut_le_closure {a p : ℕ} (ha : 1 ≤ a) {K : Type} [Field K]
    [Finite K] [CharP K G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (G2.reeGamma K a)) (hα : IsOuterOfOrder p α) :
    ∃ c β : MulAut (G2.reeGamma K a), c * α * c⁻¹ = β ∧
      fixedSubgroup β ≤ Subgroup.closure {x | β x = x ∧ ∃ n : ℕ, x ^ (3 ^ n) = 1} := by
  obtain ⟨hord, hout⟩ := hα
  have hαp : α ^ p = 1 := hord ▸ pow_orderOf_eq_one α
  obtain ⟨hpa, δ, σ, -, hδ, hcard, hmap⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.small_Ree_odd_prime_field_descent a ha K hK hp hp2 α hαp
      (fun ⟨g, hg⟩ => hout g hg.symm)
  refine ⟨δ, _, hδ, ?_⟩
  obtain ⟨d, hd⟩ := hpa
  have hd0 : 0 < p := hp.pos
  have hdp : (2 * a + 1) / p = d := by rw [hd, Nat.mul_div_cancel_left d hd0]
  have hdodd : d % 2 = 1 := by
    have h1 : Odd (p * d) := hd ▸ odd_two_mul_add_one a
    exact Nat.odd_iff.1 (Nat.odd_mul.1 h1).2
  have hb : (2 * a + 1) / p = 2 * (((2 * a + 1) / p - 1) / 2) + 1 := by rw [hdp]; omega
  have hk : Nat.card (fixSubfield σ) = 3 ^ (2 * (((2 * a + 1) / p - 1) / 2) + 1) := by
    rw [hcard, ← hb]
  have : Finite (fixSubfield σ) := Subtype.finite
  let φ : ↥(fixedSubgroup (G2.reeGammaFieldAut K a σ)) ≃*
      ↥(G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2)) :=
    ((Subgroup.equivMapOfInjective _ (G2.reeGamma K a).subtype
      (G2.reeGamma K a).subtype_injective).trans (MulEquiv.subgroupCongr hmap)).trans
      ((G2.reeGamma (fixSubfield σ) (((2 * a + 1) / p - 1) / 2)).equivMapOfInjective _
        (baseChangeGL_injective (τ := G2.tag) (fixSubfield σ).subtype)).symm
  exact twOut_le_closure_of_mulEquiv φ (twOut_reeGamma_le_closure hk)


theorem twOut_uniPlaneGen_reeG2_outer {a p : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (E : Subgroup (MulAut (G2.reeGamma K a))) [CFSG.IsElementaryAbelian p E] (hc : Nat.card E = p ^ 2)
    (hout : ¬ ∀ φ ∈ E, ∃ g, φ = MulAut.conj g) : UniPlaneGen 3 E := by
  have : Finite (ModGL G2.tag K) := finite_modGL
  have : Finite (G2.reeGamma K a) := Subtype.finite
  obtain ⟨-, hsimple, hnab⟩ := CFSG.ComponentClassification.CatalogueBSmallRee.reeGamma_G2_simple ha K hK
  have : IsSimpleGroup (G2.reeGamma K a) := hsimple
  exact twOut_uniPlaneGen_of_fieldAutData hnab hp Nat.prime_three
    (CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.fieldAutData_reeG2
      CFSG.LocalAnalysis.SubfieldPairReeG2.subfieldPairReeG2_of_pieces hp hp5 ha hK)
    (fun α hα => twOut_fixedSubgroup_reeGammaFieldAut_le_closure ha hK hp (by omega) α hα) E hc hout

theorem twOut_uniSeitzPlanes_reeG2_outer :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ IsReeG2Index d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd _ E hE hc ⟨hout, ⟨m, rfl⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : p ≠ 3 := by simpa using hpd
  have hp5 : 5 ≤ p := by
    have := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h | h
    · exact absurd h hp2
    · exact absurd h hp3
    · exact absurd (h ▸ hp) (by norm_num)
    · exact h
  obtain ⟨X, _, _, _, ha, hX, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Curtis.Coordinator.SeitzCyc.exists_reeG2_model (K := Cat ⟨.reeG2 m, hv⟩)
      ⟨hv, ⟨MulEquiv.refl _⟩⟩
  have hEi : CFSG.IsElementaryAbelian p (E.map (MulAut.congr e).toMonoidHom) :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).mpr (isElemAbelian_map_congr e hE)
  have hc' : Nat.card (E.map (MulAut.congr e).toMonoidHom) = p ^ 2 := by
    rw [card_map_congr, hc]
  have hout' : ¬ ∀ φ ∈ E.map (MulAut.congr e).toMonoidHom, ∃ g, φ = MulAut.conj g := by
    intro h
    exact not_le_range_conj_map_congr e hout fun φ hφ => (h φ hφ).imp fun g hg => hg.symm
  have h := (uniPlaneGen_map_congr e _ E).1 (twOut_uniPlaneGen_reeG2_outer ha hX hp hp5 _ hc' hout')
  simpa using h

theorem twOut_uniSeitzPlanes_reeG2_outer_five :
    UniSeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsReeG2Index d.1 :=
  twOut_uniSeitzPlanes_reeG2_outer.mono fun _ _ _ h => ⟨h.1, h.2.2⟩

end ReeG2

end TwOut

@[expose] def OddCpfRest2
    (d : TauCeti.ValidLieTypeIndex) (p : ℕ) (E : Subgroup (MulAut (Cat d))) : Prop :=
  OddCpfRest d p E ∧
    ((¬ InnerPlane d p E ∧ p = 3 ∧ IsDFourIndex d.1 ∧ ¬ orthOut3_SimilarityPlane d E) ∨
      (InnerPlane d p E ∧ IsChevalleyExcIndex d.1) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ (∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ 3 ∣ q.card - 1) ∧
        ¬ IsE6DiagPlane d E) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsTwistedE6Index d.1 ∧ ¬ IsTwE6DiagParabolicPlane d E) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsTrialityIndex d.1))

@[expose] def Input23_11BarRest :
    Prop :=
  UniSeitzPlanes OddCpfRest2 ∧ Input23_11Thm4Rest ∧ Inputs2311.Input14_2Struct

section Assembly

set_option linter.unusedSectionVars false

open CFSG.RankThree.PartOne


theorem uniSeitzPlanes_proved :
    UniSeitzPlanes fun d p E =>
      (InnerPlane d p E ∧ p = 3 ∧ IsSymplecticIndex d.1 ∧ d.1.characteristic ≠ 2) ∨
      (InnerPlane d p E ∧ 5 ≤ p ∧ IsSymplecticIndex d.1 ∧ d.1.characteristic ≠ 2) ∨
      (¬ InnerPlane d p E ∧ IsSymplecticIndex d.1) ∨
      (InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧ d.1.characteristic ≠ 2) ∨
      (¬ InnerPlane d p E ∧ IsUnitaryIndex' d.1 ∧ CentralPrimeFree p d.1 ∧ d.1.characteristic ≠ 2) ∨
      (InnerPlane d p E ∧ IsReeG2Index d.1) ∨
      (¬ InnerPlane d p E ∧ IsReeG2Index d.1) ∨
      (InnerPlane d p E ∧ IsOrthogonalIndex d.1 ∧ d.1.characteristic ≠ 2) ∨
      (¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsOrthogonalIndex d.1) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsOrthogonalIndex d.1 ∧
        (IsDFourIndex d.1 → orthOut3_SimilarityPlane d E)) ∨
      (¬ InnerPlane d p E ∧ IsG2Index d.1 ∧ d.1.characteristic ≠ 2) ∨
      (¬ InnerPlane d p E ∧ (IsF4Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1)) ∨
      (¬ InnerPlane d p E ∧ IsE6Index d.1 ∧ 5 ≤ p) ∨
      (¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTwistedE6Index d.1) ∨
      (¬ InnerPlane d p E ∧ 5 ≤ p ∧ IsTrialityIndex d.1) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsE6DiagPlane d E) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧
        ∃ q : TauCeti.PrimePower, d.1 = .E6 q ∧ ¬ 3 ∣ q.card - 1 ∧ q.p ≠ 2) ∨
      (¬ InnerPlane d p E ∧ p = 3 ∧ IsTwE6DiagParabolicPlane d E) := by
  exact UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_symplectic_three
   (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_symplectic_five
    (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_symplectic_outer
     (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_unitary_inner_all
      (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_unitary_outer
       (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_reeG2_inner
        (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) twOut_uniSeitzPlanes_reeG2_outer
         (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) orthU3_uniSeitzPlanes_orthogonal
          (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) orthOut_uniSeitzPlanes_orthogonal_outer
           (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h)
             orthOut3_uniSeitzPlanes_orthogonal_outer_three_all
            (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_G2_outer
             (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_F4E78_outer
              (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_E6_outer_five
               (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) twOut_uniSeitzPlanes_twistedE6_outer_five
                (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) twOut_uniSeitzPlanes_triality_outer_five
                 (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_E6_diag
                  (UniSeitzPlanes.of_cover (fun _ _ _ _ _ h => h) uniSeitzPlanes_E6_field_three
                   uniSeitzPlanes_twE6_diag_parabolic))))))))))))))))

theorem uniSeitzPlanes_oddCpfRest_of_rest2 (h : UniSeitzPlanes OddCpfRest2) : UniSeitzPlanes OddCpfRest := by
  refine UniSeitzPlanes.of_cover (fun d p hp hp2 E hE => ?_) uniSeitzPlanes_proved h
  have hch := hE.1.1
  have hcpf := hE.1.2
  have hlin := hE.2.1
  have hp35 : p = 3 ∨ 5 ≤ p := by
    have h2 := hp.two_le
    rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact Or.inl h'
    · exact absurd (h' ▸ hp) (by norm_num)
    · exact Or.inr h'
  have hrange : d.1.InStandardRange := ((TauCeti.LieTypeIndex.valid_iff _).1 d.2).1
  by_cases hcl : IsClassicalIndex d.1
  · rcases (isClassicalIndex_iff hrange).1 hcl with hl | hu | hs | ho
    · exact absurd hl hlin
    ·
      left
      iterate 3 right
      by_cases hin : InnerPlane d p E
      · exact Or.inl ⟨hin, hu, hcpf, hch⟩
      · exact Or.inr (Or.inl ⟨hin, hu, hcpf, hch⟩)
    ·
      left
      by_cases hin : InnerPlane d p E
      · rcases hp35 with hp3 | hp5
        · exact Or.inl ⟨hin, hp3, hs, hch⟩
        · exact Or.inr (Or.inl ⟨hin, hp5, hs, hch⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨hin, hs⟩))
    ·
      by_cases hin : InnerPlane d p E
      · left
        iterate 7 right
        exact Or.inl ⟨hin, ho, hch⟩
      · rcases hp35 with hp3 | hp5
        · by_cases hsim : IsDFourIndex d.1 → orthOut3_SimilarityPlane d E
          · left
            iterate 9 right
            exact Or.inl ⟨hin, hp3, ho, hsim⟩
          · right
            push Not at hsim
            exact ⟨hE, Or.inl ⟨hin, hp3, hsim.1, hsim.2⟩⟩
        · left
          iterate 8 right
          exact Or.inl ⟨hin, hp5, ho⟩
  · rcases (not_isClassicalIndex_iff d.1).1 hcl with hexc | hree
    · by_cases hin : InnerPlane d p E
      · exact Or.inr ⟨hE, Or.inr (Or.inl ⟨hin, hexc⟩)⟩
      · have hexc' : (IsG2Index d.1 ∨ IsF4Index d.1 ∨ IsE6Index d.1 ∨ IsE7Index d.1 ∨ IsE8Index d.1) ∨
            (IsTrialityIndex d.1 ∨ IsTwistedE6Index d.1) := hexc
        rcases hexc' with (hg | hf | he6 | he7 | he8) | (htri | htw)
        · left
          iterate 10 right
          exact Or.inl ⟨hin, hg, hch⟩
        · left
          iterate 11 right
          exact Or.inl ⟨hin, Or.inl hf⟩
        · obtain ⟨q, hq⟩ := he6
          rcases hp35 with hp3 | hp5
          · by_cases hdiag : IsE6DiagPlane d E
            · left
              iterate 15 right
              exact Or.inl ⟨hin, hp3, hdiag⟩
            · by_cases hq3 : 3 ∣ q.card - 1
              · exact Or.inr ⟨hE, Or.inr (Or.inr (Or.inl ⟨hin, hp3, ⟨q, hq, hq3⟩, hdiag⟩))⟩
              · left
                iterate 16 right
                refine Or.inl ⟨hin, hp3, q, hq, hq3, fun hq2 => hch ?_⟩
                rw [hq]
                simpa using hq2
          · left
            iterate 12 right
            exact Or.inl ⟨hin, ⟨q, hq⟩, hp5⟩
        · left
          iterate 11 right
          exact Or.inl ⟨hin, Or.inr (Or.inl he7)⟩
        · left
          iterate 11 right
          exact Or.inl ⟨hin, Or.inr (Or.inr he8)⟩
        · rcases hp35 with hp3 | hp5
          · exact Or.inr ⟨hE, Or.inr (Or.inr (Or.inr (Or.inr ⟨hin, hp3, htri⟩)))⟩
          · left
            iterate 14 right
            exact Or.inl ⟨hin, hp5, htri⟩
        · rcases hp35 with hp3 | hp5
          · by_cases hpar : IsTwE6DiagParabolicPlane d E
            · left
              iterate 17 right
              exact ⟨hin, hp3, hpar⟩
            · exact Or.inr ⟨hE, Or.inr (Or.inr (Or.inr (Or.inl ⟨hin, hp3, htw, hpar⟩)))⟩
          · left
            iterate 13 right
            exact Or.inl ⟨hin, hp5, htw⟩
    · have hree' : (∃ m : ℕ, d.1 = .suzuki m) ∨ IsReeG2Index d.1 ∨ (∃ m : ℕ, d.1 = .reeF4 m) ∨
          d.1 = .tits := hree
      rcases hree' with ⟨m, hm⟩ | hre | ⟨m, hm⟩ | ht
      · exact absurd (by rw [hm]; simp) hch
      · left
        iterate 5 right
        by_cases hin : InnerPlane d p E
        · exact Or.inl ⟨hin, hre⟩
        · exact Or.inr (Or.inl ⟨hin, hre⟩)
      · exact absurd (by rw [hm]; simp) hch
      · exact absurd (by rw [ht]; simp) hch

theorem input23_11Thm4_of_uniRest2 (hU : UniSeitzPlanes OddCpfRest2) (hR : Input23_11Thm4Rest) :
    Inputs2311.Input23_11Thm4 :=
  input23_11Thm4_of_uniRest (uniSeitzPlanes_oddCpfRest_of_rest2 hU) hR

theorem input23_11Bar_of_uniRest2 (hU : UniSeitzPlanes OddCpfRest2) (hR : Input23_11Thm4Rest)
    (hs : Inputs2311.Input14_2Struct) : Inputs2311.Input23_11Bar :=
  input23_11Bar_of_uniRest (uniSeitzPlanes_oddCpfRest_of_rest2 hU) hR hs

theorem input23_11Bar_of_rest (h : Input23_11BarRest) : Inputs2311.Input23_11Bar :=
  input23_11Bar_of_uniRest2 h.1 h.2.1 h.2.2

end Assembly

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311d

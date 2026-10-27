module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotAutDTwo
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviKer
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.Timmesfeld.LieEmbed CFSG.HardMathSupport.Solomon.LocalBalance CFSG.StandardType
open CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6ThreeEnd CFSG.SeitzReduction
open scoped MatrixGroups

section Words

variable {R : Type*} [CommRing R]

@[expose] def tvMat (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 6) R :=
  if p.1 = p.2 then 1 else Matrix.transvection p.1 p.2 1

@[expose] def tvMatWord (w : List (Fin 6 × Fin 6)) : Matrix (Fin 6) (Fin 6) R :=
  (w.map tvMat).prod

@[expose] def hornerL : List ℕ → Matrix (Fin 6) (Fin 6) R → Matrix (Fin 6) (Fin 6) R
  | [], _ => 0
  | a :: cs, A => (a : Matrix (Fin 6) (Fin 6) R) + A * hornerL cs A

@[expose] def revWord (w : List (Fin 6 × Fin 6)) : List (Fin 6 × Fin 6) :=
  w.map fun p => (Fin.rev p.2, Fin.rev p.1)

theorem map_tvMat {S : Type*} [CommRing S] (f : R →+* S) (p : Fin 6 × Fin 6) :
    (tvMat p : Matrix (Fin 6) (Fin 6) R).map f = tvMat p := by
  unfold tvMat
  split_ifs with h
  · exact Matrix.map_one f f.map_zero f.map_one
  · ext a b
    simp only [Matrix.transvection, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp

theorem map_tvMatWord {S : Type*} [CommRing S] (f : R →+* S) (w : List (Fin 6 × Fin 6)) :
    (tvMatWord w : Matrix (Fin 6) (Fin 6) R).map f = tvMatWord w := by
  induction w with
  | nil => exact Matrix.map_one f f.map_zero f.map_one
  | cons p w ih =>
    rw [tvMatWord, List.map_cons, List.prod_cons, Matrix.map_mul, map_tvMat]
    exact congrArg _ ih

theorem map_hornerL {S : Type*} [CommRing S] (f : R →+* S) (c : List ℕ)
    (A : Matrix (Fin 6) (Fin 6) R) : (hornerL c A).map f = hornerL c (A.map f) := by
  induction c with
  | nil => exact Matrix.map_zero f f.map_zero
  | cons a c ih =>
    have e := map_add f.mapMatrix (a : Matrix (Fin 6) (Fin 6) R) (A * hornerL c A)
    rw [map_mul, map_natCast] at e
    simp only [RingHom.mapMatrix_apply] at e
    rw [hornerL, hornerL, e, ih]

theorem hornerL_conj (c : List ℕ) (A M M' : Matrix (Fin 6) (Fin 6) R) (hM : M * M' = 1) :
    hornerL c (M * A * M') = M * hornerL c A * M' := by
  have hM' : M' * M = 1 := mul_eq_one_comm.mp hM
  induction c with
  | nil => simp [hornerL]
  | cons a c ih =>
    rw [hornerL, hornerL, ih, Matrix.mul_add, Matrix.add_mul, (Nat.cast_commute a M).eq.symm,
      Matrix.mul_assoc (a : Matrix (Fin 6) (Fin 6) R) M M', hM, Matrix.mul_one]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc M' M, hM', Matrix.one_mul]

end Words

section SL

variable {K : Type} [Field K]

@[expose] noncomputable def tvSL (p : Fin 6 × Fin 6) : SL(6, K) :=
  if h : p.1 = p.2 then 1 else Matrix.SpecialLinearGroup.transvection h 1

@[expose] noncomputable def tvSLWord (w : List (Fin 6 × Fin 6)) : SL(6, K) :=
  (w.map tvSL).prod

theorem coe_tvSL (p : Fin 6 × Fin 6) :
    ((tvSL p : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = tvMat p := by
  unfold tvSL tvMat
  split_ifs <;> rfl

theorem coe_tvSLWord (w : List (Fin 6 × Fin 6)) :
    ((tvSLWord w : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = tvMatWord w := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [tvSLWord, tvMatWord, List.map_cons, List.prod_cons,
      Matrix.SpecialLinearGroup.coe_mul] at ih ⊢
    rw [ih, coe_tvSL]

theorem tvSLWord_append (w w' : List (Fin 6 × Fin 6)) :
    (tvSLWord (w ++ w') : SL(6, K)) = tvSLWord w * tvSLWord w' := by
  rw [tvSLWord, tvSLWord, tvSLWord, List.map_append, List.prod_append]

variable [CharP K 2]

theorem tvMatWord_eq_map (w : List (Fin 6 × Fin 6)) :
    (tvMatWord w : Matrix (Fin 6) (Fin 6) K) =
      (tvMatWord w : Matrix (Fin 6) (Fin 6) (ZMod 2)).map (ZMod.castHom (dvd_refl 2) K) :=
  (map_tvMatWord _ w).symm

theorem hornerL_tvMatWord_eq_zero {c : List ℕ} {w : List (Fin 6 × Fin 6)}
    (h : hornerL c (tvMatWord (R := ZMod 2) w) = 0) :
    hornerL c (tvMatWord w : Matrix (Fin 6) (Fin 6) K) = 0 := by
  rw [tvMatWord_eq_map, ← map_hornerL, h, Matrix.map_zero _ (map_zero _)]

theorem hornerL_tvMatWord_ne_zero {c : List ℕ} {w : List (Fin 6 × Fin 6)}
    (h : hornerL c (tvMatWord (R := ZMod 2) w) ≠ 0) :
    hornerL c (tvMatWord w : Matrix (Fin 6) (Fin 6) K) ≠ 0 := by
  rw [tvMatWord_eq_map, ← map_hornerL]
  intro h0
  apply h
  ext i j
  have e := congrArg (fun A => A i j) h0
  simp only [Matrix.map_apply, Matrix.zero_apply] at e
  exact (ZMod.castHom (dvd_refl 2) K).injective (e.trans (map_zero _).symm)

end SL

section E6

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem coe_slToAdjointE6_tvSL (p : Fin 6 × Fin 6) :
    ((slToAdjointE6 K (tvSL p) : adjointGroup .E6 K) : ModGL .E6 K) =
      if p.1 = p.2 then 1 else pinnedX .E6 K (a5Root p.1 p.2) 1 := by
  unfold tvSL
  split_ifs with h
  · simp
  · exact coe_slToAdjointE6_transvection h 1

theorem conj_exactQ_slToAdjointE6_tvSL (p : Fin 6 × Fin 6) :
    exactQ .E6 K 1 * (slToAdjointE6 K (tvSL p) : ModGL .E6 K) * (exactQ .E6 K 1)⁻¹ =
      (slToAdjointE6 K (tvSL (Fin.rev p.2, Fin.rev p.1)) : ModGL .E6 K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [coe_slToAdjointE6_tvSL, coe_slToAdjointE6_tvSL]
  by_cases h : p.1 = p.2
  · have h' : Fin.rev p.2 = Fin.rev p.1 := by rw [h]
    simp only [h, h', ↓reduceIte, mul_one, mul_inv_cancel]
  · have h' : ¬ Fin.rev p.2 = Fin.rev p.1 := fun e => h (Fin.rev_inj.1 e).symm
    simp only [h, h', ↓reduceIte]
    rw [exactQ_one_conj_pinnedX h2 (isRoot_a5Root h) 1, permLattice_a5Root]

theorem coe_slToAdjointE6_tvSLWord (w : List (Fin 6 × Fin 6)) :
    ((slToAdjointE6 K (tvSLWord w) : adjointGroup .E6 K) : ModGL .E6 K) =
      (w.map fun p => ((slToAdjointE6 K (tvSL p) : adjointGroup .E6 K) : ModGL .E6 K)).prod := by
  induction w with
  | nil => simp [tvSLWord]
  | cons p w ih =>
    simp only [tvSLWord, List.map_cons, List.prod_cons, map_mul, Subgroup.coe_mul] at ih ⊢
    rw [ih]

theorem conj_exactQ_slToAdjointE6_tvSLWord (w : List (Fin 6 × Fin 6)) :
    exactQ .E6 K 1 * (slToAdjointE6 K (tvSLWord w) : ModGL .E6 K) * (exactQ .E6 K 1)⁻¹ =
      (slToAdjointE6 K (tvSLWord (revWord w)) : ModGL .E6 K) := by
  rw [coe_slToAdjointE6_tvSLWord, coe_slToAdjointE6_tvSLWord]
  induction w with
  | nil => simp [revWord]
  | cons p w ih =>
    have e : ∀ a b : ModGL .E6 K, exactQ .E6 K 1 * (a * b) * (exactQ .E6 K 1)⁻¹ =
        (exactQ .E6 K 1 * a * (exactQ .E6 K 1)⁻¹) * (exactQ .E6 K 1 * b * (exactQ .E6 K 1)⁻¹) := by
      intro a b
      group
    simp only [revWord, List.map_cons, List.prod_cons] at ih ⊢
    rw [e, conj_exactQ_slToAdjointE6_tvSL, ih]

variable (K) in
@[expose] noncomputable def uTheta : adjointGroup .E6 K :=
  E6Pilot.e6RepConj K 2 * uE6Two 0 * (E6Pilot.e6RepConj K 2)⁻¹

theorem coe_uTheta_mem_highRootSL2 :
    ((uTheta K : adjointGroup .E6 K) : ModGL .E6 K) ∈ EPilot.highRootSL2 .E6 K :=
  coe_conj_uE6Two_zero_mem_highRootSL2

theorem orderOf_uTheta : orderOf (uTheta K) = 3 := by
  rw [uTheta, ← MulAut.conj_apply, ← MulEquiv.coe_toMonoidHom,
    orderOf_injective _ (MulAut.conj _).injective, orderOf_uE6Two CharTwo.two_eq_zero 0]

theorem zpowers_uTheta_le :
    Subgroup.zpowers (uTheta K) ≤
      (EPilot.highRootSL2 .E6 K).subgroupOf (adjointGroup .E6 K) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
  exact coe_uTheta_mem_highRootSL2

theorem card_zpowers_uTheta (hK : Nat.card K = 2) :
    Nat.card (Subgroup.zpowers (uTheta K)) = Nat.card K + 1 := by
  rw [Nat.card_zpowers, orderOf_uTheta, hK]

theorem uTheta_comm_of_mem_a5Levi (hK : Nat.card K = 2) {d : adjointGroup .E6 K}
    (hd : d ∈ a5Levi K) : uTheta K * d = d * uTheta K := by
  have h := (centralizer_nonsplit_E6 zpowers_uTheta_le (card_zpowers_uTheta hK)
    (Subgroup.isCyclic_zpowers _)).2.2 (Subgroup.mem_zpowers (uTheta K))
  exact (Subgroup.mem_centralizer_iff.1 h d hd).symm

theorem mem_innerAut_of_fix_theta (hK : Nat.card K = 2) {t : adjointGroup .E6 K}
    (ht : uTheta K * t = t * uTheta K) (w : List (Fin 6 × Fin 6)) (c : List ℕ)
    (hY : slToAdjointE6 K (tvSLWord w) * t = t * slToAdjointE6 K (tvSLWord w))
    (h0 : hornerL c (tvMatWord (R := ZMod 2) w) = 0)
    (h1 : hornerL c (tvMatWord (R := ZMod 2) (revWord w)) ≠ 0)
    (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ y ∈ Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)), α y = y) :
    α ∈ innerAut (adjointGroup .E6 K) := by
  classical
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hunit : ∀ u : Kˣ, u = 1 := by
    have hc : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
    have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hc).1
    exact fun u => Subsingleton.elim u 1
  have hK01 : ∀ c : K, c = 0 ∨ c = 1 := by
    intro c
    by_cases hc : c = 0
    · exact Or.inl hc
    · exact Or.inr (congrArg Units.val (hunit (Units.mk0 c hc)))
  obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form .E6 (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hga⟩ := hex α
  have ha : a = 1 := funext fun i => hunit (a i)
  have hσ : σ = RingEquiv.refl K := RingEquiv.ext fun c => by
    rcases hK01 c with rfl | rfl
    · rw [map_zero, RingEquiv.refl_apply]
    · rw [map_one, RingEquiv.refl_apply]
  subst ha hσ
  have hαg : ∀ x : adjointGroup .E6 K, (α x : ModGL .E6 K) =
      (g : ModGL .E6 K) * (exactQ .E6 K ε * (x : ModGL .E6 K) * (exactQ .E6 K ε)⁻¹) *
        (g : ModGL .E6 K)⁻¹ := by
    intro x
    have e1 : Units.map (entrywiseHom (RingEquiv.refl K).toRingHom) (x : ModGL .E6 K) = x :=
      Units.ext (entrywise_id _)
    rw [hga x, e1, rootDiagUnit_one]
    group
  rcases (show (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 by
    have := ε.isLt
    change (ε : ℕ) < 2 at this
    omega) with hε | hε
  ·
    refine ⟨g, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hαg x, hε, exactQ_zero, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, one_mul, inv_one, mul_one]
  · exfalso
    have hQ1 : exactQ .E6 K ε = exactQ .E6 K 1 := by rw [hε]
    have hθc : uTheta K ∈ Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 ht
    have e1 := congrArg Subtype.val (hα _ hθc)
    rw [hαg, hQ1, exactQ_one_conj_of_mem_highRootSL2 coe_uTheta_mem_highRootSL2] at e1
    have hg : g ∈ Subgroup.centralizer
        ((Subgroup.zpowers (uTheta K) : Subgroup (adjointGroup .E6 K)) :
          Set (adjointGroup .E6 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, rfl⟩
      have hgθ : uTheta K * g = g * uTheta K := by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        calc ((uTheta K : adjointGroup .E6 K) : ModGL .E6 K) * g
            = g * (uTheta K : ModGL .E6 K) * (g : ModGL .E6 K)⁻¹ * g := by rw [e1]
          _ = g * (uTheta K : ModGL .E6 K) := by group
      exact (Commute.zpow_left hgθ k).eq
    obtain ⟨y, hy, d, hd, rfl⟩ := exists_mul_of_mem_centralizer_nonsplit_E6 zpowers_uTheta_le
      (card_zpowers_uTheta hK) (Subgroup.isCyclic_zpowers _) hg
    have hyD : ∀ x ∈ a5Levi K, y * x = x * y := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      intro x hx
      exact (Commute.zpow_left (uTheta_comm_of_mem_a5Levi hK hx) k).eq
    set Y : SL(6, K) := tvSLWord w with hYdef
    set Y' : SL(6, K) := tvSLWord (revWord w) with hY'def
    have hYc : slToAdjointE6 K Y ∈ Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2 hY
    have e2 := congrArg Subtype.val (hα _ hYc)
    rw [hαg, hQ1, conj_exactQ_slToAdjointE6_tvSLWord] at e2
    have hY'D : slToAdjointE6 K Y' ∈ a5Levi K := by
      rw [← range_slToAdjointE6]
      exact ⟨Y', rfl⟩
    have hdY : d * slToAdjointE6 K Y' * d⁻¹ ∈ a5Levi K :=
      mul_mem (mul_mem hd hY'D) (inv_mem hd)
    have e3 : d * slToAdjointE6 K Y' * d⁻¹ = slToAdjointE6 K Y := by
      have e3' : y * d * slToAdjointE6 K Y' * (y * d)⁻¹ = slToAdjointE6 K Y :=
        Subtype.ext (by simpa [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] using e2)
      calc d * slToAdjointE6 K Y' * d⁻¹
          = y * (d * slToAdjointE6 K Y' * d⁻¹) * y⁻¹ := by
            rw [hyD _ hdY, mul_inv_cancel_right]
        _ = slToAdjointE6 K Y := by rw [← e3']; group
    obtain ⟨M, rfl⟩ : d ∈ (slToAdjointE6 K).range := by
      rw [range_slToAdjointE6]
      exact hd
    have e4 : slToAdjointE6 K (M * Y' * M⁻¹ * Y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, e3, mul_inv_cancel]
    have hz : M * Y' * M⁻¹ * Y⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 6) K) := by
      rw [← ker_slToAdjointE6]
      exact e4
    obtain ⟨r, hr6, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
    have hr1 : r = 1 := by
      rcases hK01 r with rfl | rfl
      · simp at hr6
      · rfl
    have e5 : M * Y' * M⁻¹ = Y := by
      have e6 : M * Y' * M⁻¹ * Y⁻¹ = 1 := by
        refine Subtype.ext ?_
        rw [← hrz, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]
      exact mul_inv_eq_one.1 e6
    have hY0 : hornerL c (Y : Matrix (Fin 6) (Fin 6) K) = 0 := by
      rw [hYdef, coe_tvSLWord]
      exact hornerL_tvMatWord_eq_zero h0
    have hMM : (M : Matrix (Fin 6) (Fin 6) K) *
        ((M⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hMM' : ((M⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        (M : Matrix (Fin 6) (Fin 6) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hconj := hornerL_conj c ((Y' : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) M (M⁻¹ : SL(6, K))
      hMM
    have e7 : (M : Matrix (Fin 6) (Fin 6) K) * ((Y' : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
        ((M⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = Y := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, e5]
    rw [e7, hY0] at hconj
    have hY'0 : hornerL c ((Y' : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) = 0 := by
      have e8 : ((M⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
          ((M : Matrix (Fin 6) (Fin 6) K) * hornerL c ((Y' : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) *
            ((M⁻¹ : SL(6, K)) : Matrix (Fin 6) (Fin 6) K)) * M =
          hornerL c ((Y' : SL(6, K)) : Matrix (Fin 6) (Fin 6) K) := by
        simp only [Matrix.mul_assoc]
        rw [hMM', Matrix.mul_one, ← Matrix.mul_assoc, hMM', Matrix.one_mul]
      rw [← e8, ← hconj, Matrix.mul_zero, Matrix.zero_mul]
    apply hornerL_tvMatWord_ne_zero (K := K) h1
    rw [← coe_tvSLWord]
    exact hY'0

theorem mem_innerAut_of_fix_conj {G : Type*} [Group G] {t : G} (c : G)
    (h : ∀ α : MulAut G, (∀ y ∈ Subgroup.centralizer ({c * t * c⁻¹} : Set G), α y = y) →
      α ∈ innerAut G)
    (α : MulAut G) (hα : ∀ y ∈ Subgroup.centralizer ({t} : Set G), α y = y) :
    α ∈ innerAut G := by
  set β := MulAut.conj c * α * (MulAut.conj c)⁻¹ with hβ
  have hβfix : ∀ y ∈ Subgroup.centralizer ({c * t * c⁻¹} : Set G), β y = y := by
    intro y hy
    have hy' : c⁻¹ * y * c ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      calc c⁻¹ * y * c * t = c⁻¹ * (y * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * t * c⁻¹) * y) * c := by rw [hy]
        _ = t * (c⁻¹ * y * c) := by group
    have e := hα _ hy'
    have hβy : β y = c * α (c⁻¹ * y * c) * c⁻¹ := by
      rw [hβ, ← map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply,
        MulAut.conj_apply, inv_inv]
    rw [hβy, e]
    group
  obtain ⟨k, hk⟩ := h β hβfix
  refine ⟨c⁻¹ * k * c, ?_⟩
  rw [map_mul, map_mul, hk, hβ, map_inv]
  group

theorem e6RepWeyl_two_smul_bE6_one : E6Pilot.e6RepWeyl 2 • bE6 1 = a5Root 3 5 := by
  have h := (wordPos_spec (Tag.rootCertificate_check .E6) (E6Pilot.e6RepWord 2) (k := 2)
    (by decide)).2
  have hb : Tag.E6.rootCertificate.root 2 = bE6 1 := by decide
  rw [hb] at h
  change weylOfWord .E6 (E6Pilot.e6RepWord 2) • bE6 1 = _
  rw [← h]
  decide +kernel

theorem e6RepWeyl_two_smul_bE6_two : E6Pilot.e6RepWeyl 2 • bE6 2 = a5Root 0 2 := by
  have h := (wordPos_spec (Tag.rootCertificate_check .E6) (E6Pilot.e6RepWord 2) (k := 4)
    (by decide)).2
  have hb : Tag.E6.rootCertificate.root 4 = bE6 2 := by decide
  rw [hb] at h
  change weylOfWord .E6 (E6Pilot.e6RepWord 2) • bE6 2 = _
  rw [← h]
  decide +kernel

theorem e6RepWeyl_two_smul_bE6_three : E6Pilot.e6RepWeyl 2 • bE6 3 = a5Root 4 1 := by
  have h := (wordPos_spec (Tag.rootCertificate_check .E6) (E6Pilot.e6RepWord 2) (k := 43)
    (by decide)).2
  have hb : Tag.E6.rootCertificate.root 43 = bE6 3 := by decide
  rw [hb] at h
  change weylOfWord .E6 (E6Pilot.e6RepWord 2) • bE6 3 = _
  rw [← h]
  decide +kernel

theorem conj_uE6Two_eq_of_smul {k : Fin 4} {i j : Fin 6} (hij : i ≠ j)
    (hw : E6Pilot.e6RepWeyl 2 • bE6 k = a5Root i j) (hji : a5Root j i = -a5Root i j) :
    E6Pilot.e6RepConj K 2 * uE6Two k * (E6Pilot.e6RepConj K 2)⁻¹ =
      slToAdjointE6 K (tvSLWord [(i, j), (j, i)]) := by
  apply Subtype.ext
  have h1 := canonicalRep_mul_pinnedX_mul_inv_of_charTwo (K := K) (E6Pilot.e6RepWeyl 2)
    (isRoot_bE6 k) 1
  have h2 := canonicalRep_mul_pinnedX_mul_inv_of_charTwo (K := K) (E6Pilot.e6RepWeyl 2)
    (isRoot_neg_bE6 k) 1
  rw [hw] at h1
  rw [smul_neg, hw, ← hji] at h2
  rw [coe_slToAdjointE6_tvSLWord]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    coe_slToAdjointE6_tvSL, hij, Ne.symm hij, ↓reduceIte]
  change canonicalRep (coxeterSystem .E6) K (E6Pilot.e6RepWeyl 2) *
      (pinnedX .E6 K (bE6 k) 1 * pinnedX .E6 K (-bE6 k) 1) *
        (canonicalRep (coxeterSystem .E6) K (E6Pilot.e6RepWeyl 2))⁻¹ = _
  rw [← h1, ← h2]
  group

theorem conj_uE6Two_one :
    E6Pilot.e6RepConj K 2 * uE6Two 1 * (E6Pilot.e6RepConj K 2)⁻¹ =
      slToAdjointE6 K (tvSLWord [(3, 5), (5, 3)]) :=
  conj_uE6Two_eq_of_smul (by decide) e6RepWeyl_two_smul_bE6_one (by decide)

theorem conj_uE6Two_two :
    E6Pilot.e6RepConj K 2 * uE6Two 2 * (E6Pilot.e6RepConj K 2)⁻¹ =
      slToAdjointE6 K (tvSLWord [(0, 2), (2, 0)]) :=
  conj_uE6Two_eq_of_smul (by decide) e6RepWeyl_two_smul_bE6_two (by decide)

theorem conj_uE6Two_three :
    E6Pilot.e6RepConj K 2 * uE6Two 3 * (E6Pilot.e6RepConj K 2)⁻¹ =
      slToAdjointE6 K (tvSLWord [(4, 1), (1, 4)]) :=
  conj_uE6Two_eq_of_smul (by decide) e6RepWeyl_two_smul_bE6_three (by decide)

theorem tvSLWord_comm {w w' : List (Fin 6 × Fin 6)}
    (h : tvMatWord (R := ZMod 2) w * tvMatWord w' = tvMatWord w' * tvMatWord w) :
    (tvSLWord w : SL(6, K)) * tvSLWord w' = tvSLWord w' * tvSLWord w := by
  refine Subtype.ext ?_
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_tvSLWord]
  rw [tvMatWord_eq_map w, tvMatWord_eq_map w', ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem mem_innerAut_of_fix_of_conj (hK : Nat.card K = 2) {t : adjointGroup .E6 K}
    (z w : List (Fin 6 × Fin 6)) (c : List ℕ)
    (ht : E6Pilot.e6RepConj K 2 * t * (E6Pilot.e6RepConj K 2)⁻¹ =
      uTheta K * slToAdjointE6 K (tvSLWord z))
    (hzw : tvMatWord (R := ZMod 2) w * tvMatWord z = tvMatWord z * tvMatWord w)
    (h0 : hornerL c (tvMatWord (R := ZMod 2) w) = 0)
    (h1 : hornerL c (tvMatWord (R := ZMod 2) (revWord w)) ≠ 0)
    (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ y ∈ Subgroup.centralizer ({t} : Set (adjointGroup .E6 K)), α y = y) :
    α ∈ innerAut (adjointGroup .E6 K) := by
  have hD : ∀ v, slToAdjointE6 K (tvSLWord v) ∈ a5Levi K := fun v => by
    rw [← range_slToAdjointE6]
    exact ⟨_, rfl⟩
  refine mem_innerAut_of_fix_conj (E6Pilot.e6RepConj K 2) (fun β hβ => ?_) α hα
  rw [ht] at hβ
  refine mem_innerAut_of_fix_theta hK ?_ w c ?_ h0 h1 β hβ
  · rw [mul_assoc (uTheta K) _ (uTheta K), ← uTheta_comm_of_mem_a5Levi hK (hD z)]
  · have hc := tvSLWord_comm (K := K) hzw
    calc slToAdjointE6 K (tvSLWord w) * (uTheta K * slToAdjointE6 K (tvSLWord z))
        = slToAdjointE6 K (tvSLWord w) * uTheta K * slToAdjointE6 K (tvSLWord z) := by
          rw [mul_assoc]
      _ = uTheta K * slToAdjointE6 K (tvSLWord w) * slToAdjointE6 K (tvSLWord z) := by
          rw [← uTheta_comm_of_mem_a5Levi hK (hD w)]
      _ = uTheta K * (slToAdjointE6 K (tvSLWord z) * slToAdjointE6 K (tvSLWord w)) := by
          rw [mul_assoc, ← map_mul, hc, map_mul]
      _ = uTheta K * slToAdjointE6 K (tvSLWord z) * slToAdjointE6 K (tvSLWord w) := by
          rw [mul_assoc]

@[expose] def wordY7 : List (Fin 6 × Fin 6) := [(0, 3), (3, 0), (2, 3), (3, 2), (2, 3)]

@[expose] def wordY15 : List (Fin 6 × Fin 6) := [(0, 1), (1, 0), (2, 1), (2, 4), (0, 2), (4, 2)]

theorem hornerL_wordY7 : hornerL [1, 0, 1, 1, 1] (tvMatWord (R := ZMod 2) wordY7) = 0 := by
  decide +kernel

theorem hornerL_revWord_wordY7 :
    hornerL [1, 0, 1, 1, 1] (tvMatWord (R := ZMod 2) (revWord wordY7)) ≠ 0 := by
  decide +kernel

theorem hornerL_wordY15 : hornerL [1, 0, 1, 0, 1, 1] (tvMatWord (R := ZMod 2) wordY15) = 0 := by
  decide +kernel

theorem hornerL_revWord_wordY15 :
    hornerL [1, 0, 1, 0, 1, 1] (tvMatWord (R := ZMod 2) (revWord wordY15)) ≠ 0 := by
  decide +kernel

theorem comm_wordY7_nil :
    tvMatWord (R := ZMod 2) wordY7 * tvMatWord [] = tvMatWord [] * tvMatWord wordY7 := by
  decide +kernel

theorem comm_wordY7_three : tvMatWord (R := ZMod 2) wordY7 * tvMatWord [(4, 1), (1, 4)] =
    tvMatWord [(4, 1), (1, 4)] * tvMatWord wordY7 := by
  decide +kernel

theorem comm_wordY15_two_three :
    tvMatWord (R := ZMod 2) wordY15 * tvMatWord [(0, 2), (2, 0), (4, 1), (1, 4)] =
      tvMatWord [(0, 2), (2, 0), (4, 1), (1, 4)] * tvMatWord wordY15 := by
  decide +kernel

theorem mem_innerAut_of_fix_u0 (hK : Nat.card K = 2) (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ y ∈ Subgroup.centralizer ({uE6Two 0} : Set (adjointGroup .E6 K)), α y = y) :
    α ∈ innerAut (adjointGroup .E6 K) := by
  refine mem_innerAut_of_fix_of_conj hK [] wordY7 [1, 0, 1, 1, 1] ?_ comm_wordY7_nil
    hornerL_wordY7 hornerL_revWord_wordY7 α hα
  have e : (tvSLWord [] : SL(6, K)) = 1 := rfl
  rw [e, map_one, mul_one]
  rfl

theorem mem_innerAut_of_fix_u0u3 (hK : Nat.card K = 2) (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ y ∈ Subgroup.centralizer ({uE6Two 0 * uE6Two 3} : Set (adjointGroup .E6 K)),
      α y = y) :
    α ∈ innerAut (adjointGroup .E6 K) := by
  refine mem_innerAut_of_fix_of_conj hK [(4, 1), (1, 4)] wordY7 [1, 0, 1, 1, 1] ?_
    comm_wordY7_three hornerL_wordY7 hornerL_revWord_wordY7 α hα
  rw [← conj_uE6Two_three, uTheta]
  group

theorem mem_innerAut_of_fix_u0u2u3 (hK : Nat.card K = 2) (α : MulAut (adjointGroup .E6 K))
    (hα : ∀ y ∈ Subgroup.centralizer
      ({uE6Two 0 * uE6Two 2 * uE6Two 3} : Set (adjointGroup .E6 K)), α y = y) :
    α ∈ innerAut (adjointGroup .E6 K) := by
  refine mem_innerAut_of_fix_of_conj hK [(0, 2), (2, 0), (4, 1), (1, 4)] wordY15
    [1, 0, 1, 0, 1, 1] ?_ comm_wordY15_two_three hornerL_wordY15 hornerL_revWord_wordY15 α hα
  have e : ([(0, 2), (2, 0), (4, 1), (1, 4)] : List (Fin 6 × Fin 6)) =
      [(0, 2), (2, 0)] ++ [(4, 1), (1, 4)] := rfl
  rw [e, tvSLWord_append, map_mul, ← conj_uE6Two_two, ← conj_uE6Two_three, uTheta]
  group

end E6

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3E6

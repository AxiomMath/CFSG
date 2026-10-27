module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1116
public import CFSG.Sporadic.Bridge.Fi22Surj
public import CFSG.RankThree.PartTwo.KFacts.KS10L27Aut
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.Timmesfeld.Orders.ClassicalOmega
public import CFSG.Alternating.Multipliers.Main
public import CFSG.Sporadic.Schreier.TitsIso
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

namespace CatalogInputs

theorem center_eq_bot_of_simple_not_prime {X : Type} [Group X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hc | hc
  · exact hc
  · exfalso
    have : IsMulCommutative X := Subgroup.center_eq_top_iff.mp hc
    exact h ((Group.is_simple_iff_prime_card).mp inferInstance)

theorem card_quotient_center_of_eq_bot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Nat.card (X ⧸ Subgroup.center X) = Nat.card X :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot).toEquiv

theorem card_GL_zmod_two_eq (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℕ)
    (hk : Fintype.card ι = k) :
    Nat.card (Matrix.GeneralLinearGroup ι (ZMod 2)) = ∏ i : Fin k, (2 ^ k - 2 ^ (i : ℕ)) := by
  have e : Matrix.GeneralLinearGroup ι (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin k) (ZMod 2) :=
    Units.mapEquiv (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) (Fintype.equivFinOfCardEq hk)).toMulEquiv
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, ZMod.card]

theorem card_statedProj_zmod_two (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2))) :
    Nat.card (CFSG.Open.StatedProj H) = Nat.card H := by
  unfold CFSG.Open.StatedProj
  rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot ι, Subgroup.bot_subgroupOf]
  exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv

theorem fi22_nonempty_mulEquiv_native {X : Type} [Group X]
    (hX : IsSporType .Fi22 X) : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Fi22) := by
  obtain ⟨e⟩ := hX
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact ⟨e.trans b.symm⟩

end CatalogInputs

section Fi22

theorem Input_Fi22_centreless_holds :
    Input_Fi22_centreless := by
  intro X _ _ hX
  obtain ⟨e⟩ := CatalogInputs.fi22_nonempty_mulEquiv_native hX
  haveI : IsSimpleGroup X :=
    @MulEquiv.isSimpleGroup X _ _ _ CFSG.Sporadic.Fi22.isSimpleGroup_Fi22 e
  apply CatalogInputs.center_eq_bot_of_simple_not_prime
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi22.card_Fi22]
  norm_num

theorem Input_order_dvd_holds :
    Input_order_dvd := by
  intro X _ _ p _ hcase
  rcases hcase with ⟨rfl, hX⟩ | ⟨rfl, hL⟩
  · obtain ⟨e⟩ := CatalogInputs.fi22_nonempty_mulEquiv_native hX
    rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Fi22.card_Fi22]
    norm_num
  · obtain ⟨K, _, _, hK4, ⟨f⟩⟩ := hL
    have hc : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
      rw [Nat.card_congr f.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3) (by norm_num),
        hK4]
      decide
    have h3 : 3 ∣ Nat.card (X ⧸ Subgroup.center X) := by
      rw [hc]
      norm_num
    exact h3.trans (Subgroup.card_quotient_dvd_card _)

end Fi22

theorem Input_not_LTwoTwentySeven_holds : Input_not_LTwoTwentySeven := by
  intro X _ _ hX hor
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 3 3 (by norm_num)]
      norm_num)
  haveI : IsSimpleGroup X := e.isSimpleGroup
  have hX27 : Nat.card X = 9828 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.card_psl2_27
  have hZ : Subgroup.center X = ⊥ :=
    CatalogInputs.center_eq_bot_of_simple_not_prime (by rw [hX27]; norm_num)
  have hcard : Nat.card (X ⧸ Subgroup.center X) = 9828 := by
    rw [CatalogInputs.card_quotient_center_of_eq_bot hZ, hX27]
  rcases hor with hL | hA
  · obtain ⟨K, _, _, hK4, ⟨f⟩⟩ := hL
    have h1 : Nat.card (X ⧸ Subgroup.center X) = 20160 := by
      rw [Nat.card_congr f.toEquiv,
        CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3) (by norm_num),
        hK4]
      decide
    omega
  · obtain ⟨g⟩ := hA
    have h1 : Nat.card (X ⧸ Subgroup.center X) = 60 := by
      rw [Nat.card_congr g.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      norm_num [Nat.factorial]
    omega

namespace CatalogInputs

open Matrix

section Ext

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

structure HypExt (E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2))
    (R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)) (P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)) :
    Prop where
  RE : ∀ w, R (E w) = w
  PE : ∀ w, P (E w) = 0
  RP : ∀ z, R (P z) = 0
  PP : ∀ z, P (P z) = P z
  sum : ∀ z, E (R z) + P z = z

noncomputable def extMat {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) : Matrix I I (ZMod 2) →* Matrix J J (ZMod 2) where
  toFun M := LinearMap.toMatrix' (E ∘ₗ Matrix.toLin' M ∘ₗ R + P)
  map_one' := by
    have hid : E ∘ₗ LinearMap.id ∘ₗ R + P = LinearMap.id :=
      LinearMap.ext fun z => by simp [h.sum z]
    rw [Matrix.toLin'_one, hid, LinearMap.toMatrix'_id]
  map_mul' M N := by
    rw [← LinearMap.toMatrix'_mul]
    congr 1
    refine LinearMap.ext fun z => ?_
    simp [Matrix.toLin'_mul, h.RE, h.RP, h.PE, h.PP, map_add]

theorem extMat_mulVec {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) (M : Matrix I I (ZMod 2)) (z : J → ZMod 2) :
    extMat h M *ᵥ z = E (M *ᵥ R z) + P z := by
  change LinearMap.toMatrix' (E ∘ₗ Matrix.toLin' M ∘ₗ R + P) *ᵥ z = _
  rw [LinearMap.toMatrix'_mulVec]
  simp [Matrix.toLin'_apply]

theorem extMat_injective {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) : Function.Injective (extMat h) := by
  intro M N hMN
  have hE : Function.Injective E := fun a b hab => by
    have := congrArg R hab
    simpa only [h.RE] using this
  refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
  apply hE
  have h1 := congrArg (fun A : Matrix J J (ZMod 2) => A *ᵥ E w) hMN
  simp only [extMat_mulVec, h.RE, h.PE, add_zero] at h1
  simpa only [Matrix.toLin'_apply] using h1

theorem units_map_injective {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) : Function.Injective (Units.map (extMat h)) :=
  fun a b hab => Units.ext (extMat_injective h (congrArg Units.val hab))

theorem isometry_extMat {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) {Q : (I → ZMod 2) → ZMod 2} {Q' : (J → ZMod 2) → ZMod 2}
    (hQ : ∀ w z, Q' (E w + P z) = Q w + Q' (P z))
    {M : Matrix I I (ZMod 2)} (hM : ∀ v, Q (M *ᵥ v) = Q v) (z : J → ZMod 2) :
    Q' (extMat h M *ᵥ z) = Q' z := by
  have h1 := hQ (R z) z
  rw [h.sum z] at h1
  rw [extMat_mulVec, hQ, hM, h1]

theorem map_isometryCore_le {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) {Q : (I → ZMod 2) → ZMod 2} {Q' : (J → ZMod 2) → ZMod 2}
    (hQ : ∀ w z, Q' (E w + P z) = Q w + Q' (P z)) :
    (CFSG.MatrixModel.isometryCore Q).map (Units.map (extMat h)) ≤
      CFSG.MatrixModel.isometryCore Q' := by
  unfold CFSG.MatrixModel.isometryCore
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  apply Subgroup.subset_closure
  show ∀ v, Q' ((Units.map (extMat h) g : Matrix J J (ZMod 2)) *ᵥ v) = Q' v
  intro v
  exact isometry_extMat h hQ (show ∀ v, Q (_ *ᵥ v) = Q v from hg) v

theorem map_commutator_le {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) {Q : (I → ZMod 2) → ZMod 2} {Q' : (J → ZMod 2) → ZMod 2}
    (hQ : ∀ w z, Q' (E w + P z) = Q w + Q' (P z)) :
    (⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆).map
        (Units.map (extMat h)) ≤
      ⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ := by
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono (map_isometryCore_le h hQ) (map_isometryCore_le h hQ)

theorem orderOf_dvd_card_commutator_ext {E : (I → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    {R : (J → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2)} {P : (J → ZMod 2) →ₗ[ZMod 2] (J → ZMod 2)}
    (h : HypExt E R P) {Q : (I → ZMod 2) → ZMod 2} {Q' : (J → ZMod 2) → ZMod 2}
    (hQ : ∀ w z, Q' (E w + P z) = Q w + Q' (P z))
    {A : Matrix.GeneralLinearGroup I (ZMod 2)}
    (hA : A ∈ ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆) :
    orderOf A ∣ Nat.card ↥⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ := by
  have hB : Units.map (extMat h) A ∈
      ⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆ :=
    map_commutator_le h hQ (Subgroup.mem_map_of_mem _ hA)
  have hord : orderOf (Units.map (extMat h) A) = orderOf A :=
    orderOf_injective (Units.map (extMat h)) (units_map_injective h) A
  have := orderOf_dvd_natCard
    (⟨Units.map (extMat h) A, hB⟩ :
      ↥⁅CFSG.MatrixModel.isometryCore Q', CFSG.MatrixModel.isometryCore Q'⁆)
  rwa [Subgroup.orderOf_mk, hord] at this

end Ext

def plusE (n : ℕ) : (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) where
  toFun y := Sum.elim (Fin.cons 0 (fun i : Fin n => y (Sum.inl i)))
    (Fin.cons 0 (fun i : Fin n => y (Sum.inr i)))
  map_add' y z := by
    ext (j | j) <;> induction j using Fin.cases <;> simp
  map_smul' c y := by
    ext (j | j) <;> induction j using Fin.cases <;> simp

def plusR (n : ℕ) : (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2) where
  toFun z := Sum.elim (fun i : Fin n => z (Sum.inl i.succ)) (fun i : Fin n => z (Sum.inr i.succ))
  map_add' y z := by
    ext (i | i) <;> simp
  map_smul' c y := by
    ext (i | i) <;> simp

def plusP (n : ℕ) :
    (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) →ₗ[ZMod 2] (Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) where
  toFun z := Sum.elim (fun j => if j = 0 then z (Sum.inl 0) else 0)
    (fun j => if j = 0 then z (Sum.inr 0) else 0)
  map_add' y z := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [hj]
  map_smul' c y := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [hj]

theorem plus_hyp (n : ℕ) : HypExt (plusE n) (plusR n) (plusP n) where
  RE w := by
    ext (i | i) <;> simp [plusR, plusE]
  PE w := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [plusP, plusE, hj]
  RP z := by
    ext (i | i) <;> simp [plusR, plusP]
  PP z := by
    ext (j | j) <;> by_cases hj : j = 0 <;> simp [plusP, hj]
  sum z := by
    ext (j | j) <;> induction j using Fin.cases <;> simp [plusE, plusR, plusP]

theorem plus_hQ (n : ℕ) (w : Fin n ⊕ Fin n → ZMod 2) (z : Fin (n + 1) ⊕ Fin (n + 1) → ZMod 2) :
    CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2) (plusE n w + plusP n z) =
      CFSG.Open.StatedQuadPlus n (ZMod 2) w +
        CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2) (plusP n z) := by
  simp [CFSG.Open.StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, plusE, plusP,
    Fin.sum_univ_succ, Pi.single_apply]
  ring

theorem plus_dvd (n : ℕ) {A : Matrix.GeneralLinearGroup (Fin n ⊕ Fin n) (ZMod 2)}
    (hA : A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n (ZMod 2))) :
    orderOf A ∣ Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2))) :=
  orderOf_dvd_card_commutator_ext (Q := CFSG.Open.StatedQuadPlus n (ZMod 2))
    (Q' := CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2)) (plus_hyp n) (plus_hQ n) hA

def minusE (m : ℕ) :
    (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) where
  toFun y := Sum.elim (Fin.cons 0 (fun i : Fin m => y (Sum.inl i)))
    (Sum.elim (Fin.cons 0 (fun i : Fin m => y (Sum.inr (Sum.inl i))))
      (fun j : Fin 2 => y (Sum.inr (Sum.inr j))))
  map_add' y z := by
    ext (j | j | j)
    · induction j using Fin.cases <;> simp
    · induction j using Fin.cases <;> simp
    · simp
  map_smul' c y := by
    ext (j | j | j)
    · induction j using Fin.cases <;> simp
    · induction j using Fin.cases <;> simp
    · simp

def minusR (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2] (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) where
  toFun z := Sum.elim (fun i : Fin m => z (Sum.inl i.succ))
    (Sum.elim (fun i : Fin m => z (Sum.inr (Sum.inl i.succ))) (fun j : Fin 2 => z (Sum.inr (Sum.inr j))))
  map_add' y z := by
    ext (i | i | i) <;> simp
  map_smul' c y := by
    ext (i | i | i) <;> simp

def minusP (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) →ₗ[ZMod 2]
      (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) where
  toFun z := Sum.elim (fun j => if j = 0 then z (Sum.inl 0) else 0)
    (Sum.elim (fun j => if j = 0 then z (Sum.inr (Sum.inl 0)) else 0) 0)
  map_add' y z := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [hj]
  map_smul' c y := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [hj]

theorem minus_hyp (m : ℕ) : HypExt (minusE m) (minusR m) (minusP m) where
  RE w := by
    ext (i | i | i) <;> simp [minusR, minusE]
  PE w := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [minusP, minusE, hj]
  RP z := by
    ext (i | i | i) <;> simp [minusR, minusP]
  PP z := by
    ext (j | j | j) <;> by_cases hj : j = 0 <;> simp [minusP, hj]
  sum z := by
    ext (j | j | j) <;> induction j using Fin.cases <;> simp [minusE, minusR, minusP]

theorem minus_hQ (m : ℕ) (w : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)
    (z : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) :
    CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (minusE m w + minusP m z) =
      CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1 w +
        CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1 (minusP m z) := by
  simp [CFSG.Open.StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, minusE, minusP,
    Fin.sum_univ_succ, Pi.single_apply]
  ring

theorem minus_dvd (m : ℕ) {A : Matrix.GeneralLinearGroup (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)}
    (hA : A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1)) :
    orderOf A ∣
      Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1)) :=
  orderOf_dvd_card_commutator_ext (Q := CFSG.Open.StatedQuadMinus (m + 1) (ZMod 2) 1 1)
    (Q' := CFSG.Open.StatedQuadMinus (m + 1 + 1) (ZMod 2) 1 1) (minus_hyp m) (minus_hQ m) hA

end CatalogInputs

theorem Prop1116.InputOmegaDvd_holds : Prop1116.InputOmegaDvd := by
  intro Y _ _ p ε n _ hY hfp
  cases ε with
  | true =>
    obtain ⟨A, hA, hord, -⟩ := hfp
    obtain ⟨e⟩ := hY
    rw [Nat.card_congr e.toEquiv, ← hord]
    exact CatalogInputs.plus_dvd n hA
  | false =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    obtain ⟨A, hA, hord, -⟩ := hfp
    obtain ⟨e⟩ := hY
    rw [Nat.card_congr e.toEquiv, ← hord]
    exact CatalogInputs.minus_dvd m hA

theorem Prop1116.InputNotL27Pi_holds : Prop1116.InputNotL27Pi := by
  intro X _ _ hX hPi
  obtain ⟨e⟩ := hX
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 3)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by
      rw [GaloisField.card 3 3 (by norm_num)]
      norm_num)
  haveI : IsSimpleGroup X := @MulEquiv.isSimpleGroup X _ _ _ inferInstance e
  have hX27 : Nat.card X = 9828 :=
    (Nat.card_congr e.toEquiv).trans CFSG.RankThree.PartTwo.KFacts.card_psl2_27
  have hZ : Subgroup.center X = ⊥ :=
    CatalogInputs.center_eq_bot_of_simple_not_prime (by rw [hX27]; norm_num)
  have hcard : Nat.card (X ⧸ Subgroup.center X) = 9828 := by
    rw [CatalogInputs.card_quotient_center_of_eq_bot hZ, hX27]
  rcases hPi with ⟨n, hn5, ⟨g⟩, -⟩ | ⟨ε, n, hn1, hO, -⟩
  ·
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h1 : Nat.card (alternatingGroup (Fin n)) = 9828 := by
      rw [← Nat.card_congr g.toEquiv, hcard]
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 : 2 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
    have hfac : n.factorial = 19656 := by omega
    rcases Nat.lt_or_ge n 8 with h8 | h8
    · interval_cases n <;> simp [Nat.factorial] at hfac
    · have h8' := Nat.factorial_le h8
      norm_num [Nat.factorial] at h8'
      omega
  · cases ε with
    | true =>
      obtain ⟨g'⟩ := hO
      rcases Nat.lt_or_ge (n + 1) 4 with hd | hd
      · have hn3 : n < 3 := by omega
        have hdvd : Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2))) ∣
            Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1) ⊕ Fin (n + 1)) (ZMod 2)) :=
          Subgroup.card_subgroup_dvd_card _
        rw [← Nat.card_congr g'.toEquiv, hcard] at hdvd
        interval_cases n
        · rw [CatalogInputs.card_GL_zmod_two_eq (Fin (1 + 1) ⊕ Fin (1 + 1)) 4 (by simp)] at hdvd
          norm_num [Fin.prod_univ_four] at hdvd
        · rw [CatalogInputs.card_GL_zmod_two_eq (Fin (2 + 1) ⊕ Fin (2 + 1)) 6 (by simp)] at hdvd
          norm_num [Fin.prod_univ_six] at hdvd
      · have hform := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadPlus
          (K := ZMod 2) hd
        rw [CatalogInputs.card_statedProj_zmod_two (Fin (n + 1) ⊕ Fin (n + 1)), Nat.card_zmod,
          Nat.cast_ofNat] at hform
        have hdvdZ : (2 : ℤ) ^ ((n + 1) * (n + 1 - 1)) ∣
            ((Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2))) : ℕ) :
              ℤ) := by
          rw [hform]
          exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
        have hdvdN : 2 ^ ((n + 1) * (n + 1 - 1)) ∣
            Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus (n + 1) (ZMod 2))) := by
          exact_mod_cast hdvdZ
        rw [← Nat.card_congr g'.toEquiv, hcard] at hdvdN
        have hm : 4 * 3 ≤ (n + 1) * (n + 1 - 1) := Nat.mul_le_mul hd (by omega)
        have h12 : 2 ^ 12 ∣ 2 ^ ((n + 1) * (n + 1 - 1)) :=
          pow_dvd_pow 2 (le_trans (by norm_num : 12 ≤ 4 * 3) hm)
        have h9828 := h12.trans hdvdN
        norm_num at h9828
    | false =>
      obtain ⟨g'⟩ := hO
      rcases Nat.lt_or_ge (n + 1) 4 with hd | hd
      · have hn3 : n < 3 := by omega
        have hdvd : Nat.card ↥(CFSG.Open.StatedOmega
              (CFSG.Open.StatedQuadMinus (n + 1) (ZMod 2) 1 1)) ∣
            Nat.card (Matrix.GeneralLinearGroup (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2)
              (ZMod 2)) :=
          Subgroup.card_subgroup_dvd_card _
        rw [← Nat.card_congr g'.toEquiv, hcard] at hdvd
        interval_cases n
        · rw [CatalogInputs.card_GL_zmod_two_eq (Fin (1 + 1 - 1) ⊕ Fin (1 + 1 - 1) ⊕ Fin 2) 4
            (by simp)] at hdvd
          norm_num [Fin.prod_univ_four] at hdvd
        · rw [CatalogInputs.card_GL_zmod_two_eq (Fin (2 + 1 - 1) ⊕ Fin (2 + 1 - 1) ⊕ Fin 2) 6
            (by simp)] at hdvd
          norm_num [Fin.prod_univ_six] at hdvd
      · have hirr : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide
        have hform := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus
          (K := ZMod 2) (b := 1) (c := 1) hd hirr
        rw [CatalogInputs.card_statedProj_zmod_two
          (Fin (n + 1 - 1) ⊕ Fin (n + 1 - 1) ⊕ Fin 2), Nat.card_zmod, Nat.cast_ofNat] at hform
        have hdvdZ : (2 : ℤ) ^ ((n + 1) * (n + 1 - 1)) ∣
            ((Nat.card ↥(CFSG.Open.StatedOmega
              (CFSG.Open.StatedQuadMinus (n + 1) (ZMod 2) 1 1)) : ℕ) : ℤ) := by
          rw [hform]
          exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
        have hdvdN : 2 ^ ((n + 1) * (n + 1 - 1)) ∣
            Nat.card ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (n + 1) (ZMod 2) 1 1)) := by
          exact_mod_cast hdvdZ
        rw [← Nat.card_congr g'.toEquiv, hcard] at hdvdN
        have hm : 4 * 3 ≤ (n + 1) * (n + 1 - 1) := Nat.mul_le_mul hd (by omega)
        have h12 : 2 ^ 12 ∣ 2 ^ ((n + 1) * (n + 1 - 1)) :=
          pow_dvd_pow 2 (le_trans (by norm_num : 12 ≤ 4 * 3) hm)
        have h9828 := h12.trans hdvdN
        norm_num at h9828

theorem Prop1116.InputSchurAlt_holds : Prop1116.InputSchurAlt := by
  intro X _ _ p hp hp2 hq hO n hnp hA
  obtain ⟨hcomm, hsimp⟩ := hq
  obtain ⟨e⟩ := hA
  haveI : Group.IsPerfect X := Group.isPerfect_def.mpr hcomm
  haveI : Nontrivial (X ⧸ Subgroup.center X) := hsimp.toNontrivial
  have hY1 : 1 < Nat.card (X ⧸ Subgroup.center X) := Finite.one_lt_card
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hdvd : p ∣ n - 2 :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq
      (hnp.trans (Nat.mod_eq_of_lt (by omega : 2 < p)).symm))
  have hn5 : 5 ≤ n := by
    by_contra hlt
    rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 by omega) with rfl | rfl | rfl | rfl | rfl
    · rw [Nat.zero_mod] at hnp
      omega
    · rw [Nat.mod_eq_of_lt (by omega : 1 < p)] at hnp
      omega
    · have h2 : Nat.card (X ⧸ Subgroup.center X) = 1 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        norm_num [Nat.factorial]
      omega
    · have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    · have := Nat.le_of_dvd (by norm_num) hdvd
      omega
  haveI : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)⟩
  let π : X →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center X := by
    ext x
    simp [π, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  obtain ⟨-, h, -, -, -, -, eK, -⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_hopf_multiplier π hπ hker.le
  have hcardK : Nat.card (Subgroup.center X) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin n))) := by
    rw [← hker, ← Nat.card_congr eK.toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  obtain ⟨-, hcard⟩ := CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput n hn5
  rw [hcard] at hcardK
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center X)) := by
    split_ifs at hcardK with h67
    · rcases h67 with rfl | rfl
      · exfalso
        have h4 : p ∣ 2 ^ 2 := hdvd
        have h2 : p ∣ 2 := hp.dvd_of_dvd_pow h4
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
      · have h5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hdvd
        subst h5
        exact Nat.Coprime.coprime_dvd_right hcardK (by norm_num)
    · exact Nat.Coprime.coprime_dvd_right hcardK
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hO' : CFSG.pPrimeCore p X = ⊥ := hO
  exact (CFSG.pPrimeCore_eq_bot_iff.mp hO') (Subgroup.center X) inferInstance hcop

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

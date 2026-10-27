module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine

public section

namespace CFSG.ClassicalInvolution.Phan

section SL2Part

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.GorensteinWalter
open CFSG.LieType.Steinberg (diagGL coe_diagGL coe_diagGL_inv card_specialLinearGroup_fin_two)
open scoped MatrixGroups LinearAlgebra.Projectivization

namespace SL2Aut

section ProjectiveLine

variable (k : Type*) [Field k]

def projPt (c : k) : ℙ k (Fin 2 → k) :=
  Projectivization.mk k ![c, 1] (fun h => (one_ne_zero : (1 : k) ≠ 0) (by simpa using congrFun h 1))

variable {k}

theorem projPt_inj {x y : k} (h : projPt k x = projPt k y) : x = y := by
  unfold projPt at h
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  have h0 := congrFun ha 0
  simp [Units.smul_def] at h1 h0
  subst h1
  simpa using h0.symm

theorem projPt_ne_infty (x : k) : projPt k x ≠ psl2ProjectiveInfinity k := by
  intro h
  unfold projPt psl2ProjectiveInfinity at h
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h1 := congrFun ha 1
  simp at h1

theorem exists_projPt_of_ne_infty {ω : ℙ k (Fin 2 → k)} (h : ω ≠ psl2ProjectiveInfinity k) :
    ∃ x, ω = projPt k x := by
  induction ω using Projectivization.ind with
  | h v hv =>
    have h1 : v 1 ≠ 0 := by
      intro h1
      apply h
      unfold psl2ProjectiveInfinity
      rw [Projectivization.mk_eq_mk_iff]
      have h0 : v 0 ≠ 0 := by
        intro h0
        apply hv
        ext i
        fin_cases i <;> simp [h0, h1]
      refine ⟨Units.mk0 (v 0) h0, ?_⟩
      ext i
      fin_cases i <;> simp [Units.smul_def, h1]
    refine ⟨v 0 / v 1, ?_⟩
    unfold projPt
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (v 1) h1, ?_⟩
    ext i
    fin_cases i
    · simp [Units.smul_def]
      field_simp
    · simp [Units.smul_def]

theorem smul_projPt (c y : k) : sl2Upper k c • projPt k y = projPt k (y + c) := by
  unfold projPt
  rw [Projectivization.smul_mk]
  congr 1
  change (sl2Upper k c).val *ᵥ ![y, 1] = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem three_le_card_projLine [Finite k] : 3 ≤ Nat.card (ℙ k (Fin 2 → k)) := by
  have hinj : Function.Injective
      (fun o : Option k => o.elim (psl2ProjectiveInfinity k) (projPt k)) := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some y => exact absurd h.symm (projPt_ne_infty y)
    | some x =>
      cases b with
      | none => exact absurd h (projPt_ne_infty x)
      | some y => exact congrArg some (projPt_inj h)
  have h1 : Nat.card (Option k) ≤ Nat.card (ℙ k (Fin 2 → k)) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option] at h1
  have h2 : 1 < Nat.card k := Finite.one_lt_card
  omega

abbrev upperSub (k : Type*) [Field k] : Subgroup SL(2, k) :=
  sl2RootX (MonoidHom.id SL(2, k))

abbrev lowerSub (k : Type*) [Field k] : Subgroup SL(2, k) :=
  sl2RootY (MonoidHom.id SL(2, k))

theorem upperSub_le_stabilizer :
    upperSub k ≤ MulAction.stabilizer SL(2, k) (psl2ProjectiveInfinity k) := by
  rintro _ ⟨c, rfl⟩
  exact (sl2_mem_stabilizer_infinity_iff _).2 (by simp)

theorem upperSub_normal :
    ((upperSub k).subgroupOf
      (MulAction.stabilizer SL(2, k) (psl2ProjectiveInfinity k))).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨c, hc⟩ := hx
  have key := sl2Borel_conj_upperUnipotent (K := k) (A := (g : SL(2, k))) g.2 c
  refine ⟨((g : SL(2, k)) : Matrix (Fin 2) (Fin 2) k) 0 0 ^ 2 * c, ?_⟩
  have hc' : sl2Upper k c = (x : SL(2, k)) := hc
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.id_apply]
  rw [← hc']
  exact key.symm

theorem upperSub_regular {ω ω' : ℙ k (Fin 2 → k)} (hω : ω ≠ psl2ProjectiveInfinity k)
    (hω' : ω' ≠ psl2ProjectiveInfinity k) : ∃! u : upperSub k, (u : SL(2, k)) • ω = ω' := by
  obtain ⟨y, rfl⟩ := exists_projPt_of_ne_infty hω
  obtain ⟨y', rfl⟩ := exists_projPt_of_ne_infty hω'
  refine ⟨⟨sl2Upper k (y' - y), ⟨_, rfl⟩⟩, ?_, ?_⟩
  · show sl2Upper k (y' - y) • projPt k y = projPt k y'
    rw [smul_projPt]
    congr 1
    ring
  · rintro ⟨u, c, rfl⟩ h
    have h' : sl2Upper k c • projPt k y = projPt k y' := h
    rw [smul_projPt] at h'
    have hc : c = y' - y := by
      have := projPt_inj h'
      linear_combination this
    subst hc
    rfl

theorem sl2Weyl_not_mem_stabilizer :
    sl2Weyl k 1 • psl2ProjectiveInfinity k ≠ psl2ProjectiveInfinity k := by
  intro h
  have := (sl2_mem_stabilizer_infinity_iff (sl2Weyl k 1)).1 (MulAction.mem_stabilizer_iff.2 h)
  simp at this

theorem map_conj_weyl_upperSub :
    (upperSub k).map (MulAut.conj (sl2Weyl k 1)).toMonoidHom = lowerSub k := by
  have key : ∀ d : k, sl2Weyl k 1 * sl2Upper k d * (sl2Weyl k 1)⁻¹ = sl2Lower k (-d) := by
    intro d
    rw [mul_inv_eq_iff_eq_mul, sl2Weyl_mul_upper]
    simp
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨-c, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    exact (key c).symm
  · rintro ⟨c, rfl⟩
    refine ⟨sl2Upper k (-c), ⟨-c, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    rw [key, neg_neg]

theorem upperSub_sup_lowerSub : upperSub k ⊔ lowerSub k = ⊤ := by
  have h : ((upperSub k : Set SL(2, k)) ∪ (lowerSub k : Set SL(2, k))) =
      Set.range (sl2Upper k) ∪ Set.range (sl2Lower k) := rfl
  rw [← Subgroup.closure_eq (upperSub k), ← Subgroup.closure_eq (lowerSub k),
    ← Subgroup.closure_union, h, sl2_closure_upper_lower]

end ProjectiveLine

section Sylow

variable (k : Type*) [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]

omit [Fact p.Prime] in
theorem exists_card_eq_pow : ∃ n : ℕ, 1 ≤ n ∧ Nat.card k = p ^ n := by
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨n, -, hn⟩ := FiniteField.card k p
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

omit [Finite k] in
theorem card_upperSub : Nat.card (upperSub k) = Nat.card k := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : k => (⟨sl2Upper k c, c, rfl⟩ : upperSub k)) ⟨?_, ?_⟩)).symm
  · intro c d h
    have := congrFun (congrFun (congrArg Subtype.val (congrArg Subtype.val h)) 0) 1
    simpa using this
  · rintro ⟨_, c, rfl⟩
    exact ⟨c, rfl⟩

omit [Fact p.Prime] in
theorem isPGroup_upperSub : IsPGroup p (upperSub k) := by
  obtain ⟨n, -, hn⟩ := exists_card_eq_pow k p
  exact IsPGroup.of_card (by rw [card_upperSub, hn])

theorem not_dvd_index_upperSub : ¬ p ∣ (upperSub k).index := by
  obtain ⟨n, hn1, hn⟩ := exists_card_eq_pow k p
  have h1 := Subgroup.index_mul_card (upperSub k)
  rw [card_upperSub, card_specialLinearGroup_fin_two] at h1
  have hq : 0 < Nat.card k := Finite.card_pos
  have h2 : (upperSub k).index = Nat.card k ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_right hq
    rw [h1, mul_comm]
  rw [h2]
  intro hdvd
  have hpq : p ∣ Nat.card k := by rw [hn]; exact dvd_pow_self p (by omega)
  have hpq2 : p ∣ Nat.card k ^ 2 := dvd_pow hpq two_ne_zero
  have h3 : Nat.card k ^ 2 - 1 + 1 = Nat.card k ^ 2 := Nat.sub_add_cancel (Nat.one_le_pow _ _ hq)
  have h4 : p ∣ 1 := (Nat.dvd_add_right hdvd).1 (h3 ▸ hpq2)
  exact (Fact.out : p.Prime).not_dvd_one h4

@[expose] noncomputable def upperSylow : Sylow p SL(2, k) :=
  (isPGroup_upperSub k p).toSylow (not_dvd_index_upperSub k p)

theorem coe_upperSylow : (upperSylow k p : Subgroup SL(2, k)) = upperSub k :=
  IsPGroup.toSylow_coe _ _

end Sylow

section Classification

variable {k : Type*} [Field k] [Finite k]

omit [Finite k] in
theorem hom_eq_of_eqOn_upper_lower {M : Type*} [Group M] {f g : SL(2, k) →* M}
    (hU : ∀ c, f (sl2Upper k c) = g (sl2Upper k c))
    (hL : ∀ c, f (sl2Lower k c) = g (sl2Lower k c)) : f = g := by
  refine MonoidHom.eq_of_eqOn_dense (sl2_closure_upper_lower (K := k)) ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  exacts [hU c, hL c]

omit [Finite k] in
theorem toGL_upper_conj (a : kˣ) (ψ : k ≃+* k) (c : k) :
    Matrix.SpecialLinearGroup.toGL (sl2Upper k (a * ψ c)) =
      diagGL ![a, 1] * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (ψ : k →+* k) (sl2Upper k c)) * (diagGL ![a, 1])⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, coe_sl2Upper]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Finite k] in
theorem toGL_lower_conj (a : kˣ) (ψ : k ≃+* k) (c : k) :
    Matrix.SpecialLinearGroup.toGL (sl2Lower k (((a⁻¹ : kˣ) : k) * ψ c)) =
      diagGL ![a, 1] * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (ψ : k →+* k) (sl2Lower k c)) * (diagGL ![a, 1])⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, coe_sl2Lower]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply]
  exact mul_comm _ _

end Classification

end SL2Aut

section MainSL2

open SL2Aut

variable {k : Type*} [Field k] [Finite k]

theorem exists_toGL_eq_conj_map (α : MulAut SL(2, k)) :
    ∃ (G : GL (Fin 2) k) (ψ : k ≃+* k), ∀ A : SL(2, k),
      Matrix.SpecialLinearGroup.toGL (α A) =
        G * Matrix.SpecialLinearGroup.toGL
          (Matrix.SpecialLinearGroup.map (ψ : k →+* k) A) * G⁻¹ := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k _⟩
  have : CharP k (ringChar k) := ringChar.charP k
  set p := ringChar k with hp
  have hΩ : 3 ≤ Nat.card (ℙ k (Fin 2 → k)) := three_le_card_projLine
  have hUξ : (upperSylow k p : Subgroup SL(2, k)) ≤
      MulAction.stabilizer SL(2, k) (psl2ProjectiveInfinity k) := by
    rw [coe_upperSylow]
    exact upperSub_le_stabilizer
  have hUn : ((upperSylow k p : Subgroup SL(2, k)).subgroupOf
      (MulAction.stabilizer SL(2, k) (psl2ProjectiveInfinity k))).Normal := by
    rw [coe_upperSylow]
    exact upperSub_normal
  have hreg : ∀ ω ω' : ℙ k (Fin 2 → k), ω ≠ psl2ProjectiveInfinity k →
      ω' ≠ psl2ProjectiveInfinity k →
      ∃! u : ↥(upperSylow k p : Subgroup SL(2, k)), (u : SL(2, k)) • ω = ω' := by
    have h := coe_upperSylow k p
    generalize (upperSylow k p : Subgroup SL(2, k)) = X at h ⊢
    subst h
    exact fun ω ω' hω hω' => upperSub_regular hω hω'
  have hgen : (upperSylow k p : Subgroup SL(2, k)) ⊔
      (upperSylow k p : Subgroup SL(2, k)).map (MulAut.conj (sl2Weyl k 1)).toMonoidHom = ⊤ := by
    rw [coe_upperSylow, map_conj_weyl_upperSub]
    exact upperSub_sup_lowerSub
  obtain ⟨-, hconj, -⟩ := large_Ree_root_pair_restriction (Ω := ℙ k (Fin 2 → k))
    (ξ := psl2ProjectiveInfinity k) (U := upperSylow k p) hΩ hUξ hUn hreg (sl2Weyl k 1)
    sl2Weyl_not_mem_stabilizer hgen
  obtain ⟨g, β, hβ, rfl⟩ := hconj α
  rw [coe_upperSylow, map_conj_weyl_upperSub] at hβ
  have hker : ∀ g : SL(2, k), (MonoidHom.id SL(2, k)) g = 1 → ∃ l : kˣ, l ^ 2 = 1 ∧
      (g : Matrix (Fin 2) (Fin 2) k) = (l : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    intro g hg
    refine ⟨1, one_pow 2, ?_⟩
    have : g = 1 := hg
    subst this
    simp
  obtain ⟨hparam, -⟩ := central_SL2_root_pair_semilinear_parameters (MonoidHom.id SL(2, k))
    Function.surjective_id hker
  obtain ⟨⟨a, ψ⟩, ⟨hx, hy, -⟩, -⟩ := hparam β hβ
  refine ⟨Matrix.SpecialLinearGroup.toGL g * diagGL ![a, 1], ψ, fun A => ?_⟩
  have hβA : Matrix.SpecialLinearGroup.toGL (β A) =
      diagGL ![a, 1] * Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map (ψ : k →+* k) A) * (diagGL ![a, 1])⁻¹ := by
    have hF : (Matrix.SpecialLinearGroup.toGL : SL(2, k) →* GL (Fin 2) k).comp β.toMonoidHom =
        (MulAut.conj (diagGL ![a, 1])).toMonoidHom.comp ((Matrix.SpecialLinearGroup.toGL).comp
          (Matrix.SpecialLinearGroup.map (ψ : k →+* k))) := by
      refine hom_eq_of_eqOn_upper_lower (fun c => ?_) (fun c => ?_)
      · have := hx c
        simp only [MonoidHom.id_apply] at this
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [this]
        exact toGL_upper_conj a ψ c
      · have := hy c
        simp only [MonoidHom.id_apply] at this
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [this]
        exact toGL_lower_conj a ψ c
    exact DFunLike.congr_fun hF A
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, hβA]
  group

end MainSL2

end SL2Part

section SUAut

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (diagGL coe_diagGL coe_diagGL_inv conjTr_diagonal conj_mem_SUid
  normOne mem_normOne)

section FieldAut

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem map_unitaryInvolution (φ : K ≃+* K) (c : K) :
    φ (unitaryInvolution K p f c) = unitaryInvolution K p f (φ c) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, map_pow]

theorem conjTr_map (φ : K ≃+* K) {d : ℕ} (A : Matrix (Fin d) (Fin d) K) :
    conjTr (unitaryInvolution K p f) (A.map φ) = (conjTr (unitaryInvolution K p f) A).map φ := by
  ext i j
  simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, map_unitaryInvolution]

theorem map_mem_SUid (φ : K ≃+* K) {d : ℕ} {A : GL (Fin d) K}
    (hA : A ∈ SUid (unitaryInvolution K p f) d) :
    Matrix.GeneralLinearGroup.map (φ : K →+* K) A ∈ SUid (unitaryInvolution K p f) d := by
  obtain ⟨hdet, hu⟩ := hA
  refine ⟨?_, ?_⟩
  · show ((A : Matrix (Fin d) (Fin d) K).map (φ : K →+* K)).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
  · show conjTr (unitaryInvolution K p f) ((A : Matrix (Fin d) (Fin d) K).map φ) *
      (A : Matrix (Fin d) (Fin d) K).map φ = 1
    rw [conjTr_map, ← Matrix.map_mul, hu, Matrix.map_one _ (map_zero φ) (map_one φ)]

variable (p f) in
@[expose] noncomputable def fieldAutSU (φ : K ≃+* K) (d : ℕ) : MulAut (Su K p f d) where
  toFun A := ⟨Matrix.GeneralLinearGroup.map (φ : K →+* K) A.1, map_mem_SUid φ A.2⟩
  invFun A := ⟨Matrix.GeneralLinearGroup.map (φ.symm : K →+* K) A.1, map_mem_SUid φ.symm A.2⟩
  left_inv A := Subtype.ext (Units.ext (by ext i j; simp))
  right_inv A := Subtype.ext (Units.ext (by ext i j; simp))
  map_mul' A B := Subtype.ext (map_mul _ _ _)

theorem coe_fieldAutSU (φ : K ≃+* K) {d : ℕ} (A : Su K p f d) :
    ((fieldAutSU p f φ d A : Su K p f d) : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.map (φ : K →+* K) (A : GL (Fin d) K) :=
  rfl

theorem coe_coe_fieldAutSU (φ : K ≃+* K) {d : ℕ} (A : Su K p f d) :
    (((fieldAutSU p f φ d A : Su K p f d) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ((A : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).map φ :=
  rfl

end FieldAut

section UnitaryConj

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem conjTr_inv_mul_self (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ} (D : GL (Fin d) K)
    (hD : conjTr (unitaryInvolution K p f) (D : Matrix (Fin d) (Fin d) K) *
      (D : Matrix (Fin d) (Fin d) K) = 1) :
    conjTr (unitaryInvolution K p f) ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  set Dm := (D : Matrix (Fin d) (Fin d) K)
  set Di := ((D⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
  have hDDi : Dm * Di = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDi : Di = conjTr (unitaryInvolution K p f) Dm := by
    calc Di = conjTr (unitaryInvolution K p f) Dm * Dm * Di := by rw [hD, Matrix.one_mul]
      _ = conjTr (unitaryInvolution K p f) Dm := by rw [Matrix.mul_assoc, hDDi, Matrix.mul_one]
  have hcc : conjTr (unitaryInvolution K p f) (conjTr (unitaryInvolution K p f) Dm) = Dm := by
    ext i j
    simp only [conjTr, Matrix.transpose_apply, Matrix.map_apply, unitaryInvolution_involutive hK]
  rw [hDi, hcc, ← hDi, hDDi]

variable (p f) in
@[expose] noncomputable def unitaryConj (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ} (D : GL (Fin d) K)
    (hD : conjTr (unitaryInvolution K p f) (D : Matrix (Fin d) (Fin d) K) *
      (D : Matrix (Fin d) (Fin d) K) = 1) : MulAut (Su K p f d) where
  toFun A := ⟨D * A.1 * D⁻¹, conj_mem_SUid (unitaryInvolution_involutive hK) hD A.2⟩
  invFun A := ⟨D⁻¹ * A.1 * D⁻¹⁻¹,
    conj_mem_SUid (unitaryInvolution_involutive hK) (conjTr_inv_mul_self hK D hD) A.2⟩
  left_inv A := Subtype.ext (by simp [mul_assoc])
  right_inv A := Subtype.ext (by simp [mul_assoc])
  map_mul' A B := Subtype.ext (by simp [mul_assoc])

theorem coe_unitaryConj (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ} (D : GL (Fin d) K)
    (hD : conjTr (unitaryInvolution K p f) (D : Matrix (Fin d) (Fin d) K) *
      (D : Matrix (Fin d) (Fin d) K) = 1) (A : Su K p f d) :
    ((unitaryConj p f hK D hD A : Su K p f d) : GL (Fin d) K) = D * A * D⁻¹ :=
  rfl

theorem diagGL_conjTr_mul_self {d : ℕ} (t : Fin d → Kˣ)
    (ht : ∀ i, unitaryInvolution K p f (t i : K) * (t i : K) = 1) :
    conjTr (unitaryInvolution K p f) ((diagGL t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
      ((diagGL t : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
  rw [coe_diagGL, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact ht i

variable (p f) in
@[expose] noncomputable def diagConj (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ}
    (t : Fin d → normOne (unitaryInvolution K p f)) : MulAut (Su K p f d) :=
  unitaryConj p f hK (diagGL fun i => ((t i : normOne (unitaryInvolution K p f)) : Kˣ))
    (diagGL_conjTr_mul_self _ fun i => (mem_normOne (unitaryInvolution K p f)).1 (t i).2)

theorem coe_diagConj (hK : Nat.card K = (p ^ f) ^ 2) {d : ℕ}
    (t : Fin d → normOne (unitaryInvolution K p f)) (A : Su K p f d) :
    ((diagConj p f hK t A : Su K p f d) : GL (Fin d) K) =
      diagGL (fun i => ((t i : normOne (unitaryInvolution K p f)) : Kˣ)) * A *
        (diagGL (fun i => ((t i : normOne (unitaryInvolution K p f)) : Kˣ)))⁻¹ :=
  rfl

end UnitaryConj

end SUAut

section Transport

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (diagGL coe_diagGL coe_diagGL_inv fixedSubfield hypEquiv hypMat
  coe_hypHom hypEquiv_apply)
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem exists_ringEquiv_extend (ψ : fixedSubfield K p f ≃+* fixedSubfield K p f) :
    ∃ φ : K ≃+* K, ∀ x : fixedSubfield K p f, φ (x : K) = ((ψ x : fixedSubfield K p f) : K) := by
  classical
  have : Fintype (fixedSubfield K p f) := Fintype.ofFinite _
  let : Algebra (ZMod p) (fixedSubfield K p f) := ZMod.algebra _ p
  let ψAlg : fixedSubfield K p f ≃ₐ[ZMod p] fixedSubfield K p f :=
    AlgEquiv.ofRingEquiv (f := ψ) (by
      intro x
      have h : (ψ.toRingHom.comp (algebraMap (ZMod p) (fixedSubfield K p f)) : ZMod p →+* _) =
          algebraMap (ZMod p) (fixedSubfield K p f) := RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  obtain ⟨⟨i, hi⟩, hψ⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p)
    (fixedSubfield K p f)).2 ψAlg
  refine ⟨iterateFrobeniusEquiv K p i, fun x => ?_⟩
  have hψx := DFunLike.congr_fun hψ x
  have hx : ψ x = x ^ (p ^ i) := by
    calc ψ x = ψAlg x := rfl
      _ = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (fixedSubfield K p f) ^ i) x :=
        hψx.symm
      _ = ((⇑(FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) (fixedSubfield K p f)))^[i]) x := by
        rw [AlgEquiv.coe_pow]
      _ = x ^ (Fintype.card (ZMod p) ^ i) :=
        congrFun (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod p)
          (fixedSubfield K p f) i) x
      _ = x ^ (p ^ i) := by rw [ZMod.card]
  rw [hx, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  simp

theorem hypEquiv_coe_eq {ζ : K} (hζ0 : ζ ≠ 0) (hζ : unitaryInvolution K p f ζ = -ζ)
    (A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f)) :
    ((hypEquiv hζ0 hζ A : SU (unitaryInvolution K p f) 2) : GL (Fin 2) K) =
      diagGL ![1, (Units.mk0 ζ hζ0)⁻¹] * Matrix.SpecialLinearGroup.mapGL K A *
        (diagGL ![1, (Units.mk0 ζ hζ0)⁻¹])⁻¹ := by
  apply Units.ext
  rw [hypEquiv_apply, coe_hypHom]
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe]
  have halg : ∀ x : fixedSubfield K p f, algebraMap (fixedSubfield K p f) K x = (x : K) :=
    fun _ => rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hypMat, Matrix.mul_apply, Matrix.diagonal_apply, halg] <;> field_simp

theorem exists_eq_conj_map (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2)) :
    ∃ (u : GL (Fin 2) K) (φ : K ≃+* K), ∀ B : Su K p f 2,
      ((α B : Su K p f 2) : GL (Fin 2) K) =
        u * Matrix.GeneralLinearGroup.map (φ : K →+* K) (B : GL (Fin 2) K) * u⁻¹ := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hK
  obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
  let Θ : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f) ≃* Su K p f 2 :=
    (hypEquiv hζ0 hζ).trans (conjEquiv P hP)
  let H : GL (Fin 2) K := diagGL ![1, (Units.mk0 ζ hζ0)⁻¹]
  let Q : GL (Fin 2) K := P * H
  have hΘ : ∀ A, ((Θ A : Su K p f 2) : GL (Fin 2) K) =
      Q * Matrix.SpecialLinearGroup.mapGL K A * Q⁻¹ := by
    intro A
    show P * ((hypEquiv hζ0 hζ A : SU (unitaryInvolution K p f) 2) : GL (Fin 2) K) * P⁻¹ = _
    rw [hypEquiv_coe_eq hζ0 hζ A]
    simp only [Q, H, _root_.mul_inv_rev, mul_assoc]
  let α' : MulAut (Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f)) :=
    Θ.trans (α.trans Θ.symm)
  obtain ⟨G, ψ, hG⟩ := exists_toGL_eq_conj_map α'
  obtain ⟨φ, hφ⟩ := exists_ringEquiv_extend ψ
  have halg : ∀ x : fixedSubfield K p f, algebraMap (fixedSubfield K p f) K x = (x : K) :=
    fun _ => rfl
  have hmapGL : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f),
      Matrix.SpecialLinearGroup.mapGL K
      (Matrix.SpecialLinearGroup.map (ψ : fixedSubfield K p f →+* fixedSubfield K p f) A) =
        Matrix.GeneralLinearGroup.map (φ : K →+* K) (Matrix.SpecialLinearGroup.mapGL K A) := by
    intro A
    apply Units.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix, halg, hφ]
  have hmapGL' : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (fixedSubfield K p f),
      Matrix.SpecialLinearGroup.mapGL K A =
      Matrix.GeneralLinearGroup.map (algebraMap (fixedSubfield K p f) K)
        (Matrix.SpecialLinearGroup.toGL A) := fun A => Units.ext rfl
  refine ⟨Q * Matrix.GeneralLinearGroup.map (algebraMap (fixedSubfield K p f) K) G *
    (Matrix.GeneralLinearGroup.map (φ : K →+* K) Q)⁻¹, φ, fun B => ?_⟩
  obtain ⟨A, rfl⟩ := Θ.surjective B
  have h1 : α (Θ A) = Θ (α' A) := by simp [α']
  rw [h1, hΘ (α' A)]
  have h2 : Matrix.SpecialLinearGroup.mapGL K (α' A) =
      Matrix.GeneralLinearGroup.map (algebraMap (fixedSubfield K p f) K) G *
        Matrix.GeneralLinearGroup.map (φ : K →+* K) (Matrix.SpecialLinearGroup.mapGL K A) *
        (Matrix.GeneralLinearGroup.map (algebraMap (fixedSubfield K p f) K) G)⁻¹ := by
    rw [hmapGL' (α' A), hG A, map_mul, map_mul, map_inv, ← hmapGL' , hmapGL]
  have h3 : Matrix.SpecialLinearGroup.mapGL K A =
      Q⁻¹ * ((Θ A : Su K p f 2) : GL (Fin 2) K) * Q := by
    rw [hΘ]
    group
  rw [h2, h3]
  simp only [map_mul, map_inv]
  group

end Transport

section Torus

open Matrix CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg (diagGL coe_diagGL coe_diagGL_inv normOne mem_normOne torusTwo
  exists_norm_one_orderOf_eq)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem conj_w_eq_map (σ : K →+* K) (A : Matrix (Fin 2) (Fin 2) K)
    (hdet : A.det = 1) (hu : (A.map σ)ᵀ * A = 1) :
    !![0, 1; -1, 0] * A * !![0, -1; 1, 0] = A.map σ := by
  have h1 : A⁻¹ = (A.map σ)ᵀ := Matrix.inv_eq_left_inv hu
  have h2 : A⁻¹ = A.adjugate := by
    rw [Matrix.inv_def, hdet]; simp
  have h3 : A.map σ = (A.adjugate)ᵀ := by
    rw [← h2, h1, transpose_transpose]
  rw [h3]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem monomial_aux {x y z w s t : K} (hs : s ^ 2 ≠ 1) (hs0 : s ≠ 0) (hdet : x * w - y * z ≠ 0)
    (E00 : x * s = t * x) (E01 : y * s⁻¹ = t * y) (E10 : z * s = t⁻¹ * z)
    (E11 : w * s⁻¹ = t⁻¹ * w) :
    (y = 0 ∧ z = 0) ∨ (x = 0 ∧ w = 0) := by
  have hss : s⁻¹ - s ≠ 0 := by
    intro h
    apply hs
    have h1 : s * (s⁻¹ - s) = 0 := by rw [h, mul_zero]
    field_simp at h1
    linear_combination -h1
  by_cases hx : x = 0
  · right
    refine ⟨hx, ?_⟩
    have hy : y ≠ 0 := by
      intro hy
      apply hdet
      rw [hx, hy]
      ring
    have hts : t = s⁻¹ := by
      apply mul_left_cancel₀ hy
      rw [mul_comm y t, ← E01]
    rw [hts, inv_inv] at E11
    have : w * (s⁻¹ - s) = 0 := by linear_combination E11
    exact (mul_eq_zero.1 this).resolve_right hss
  · left
    have hts : t = s := by
      apply mul_left_cancel₀ hx
      rw [mul_comm x t, ← E00]
    rw [hts] at E01 E10
    refine ⟨?_, ?_⟩
    · have : y * (s⁻¹ - s) = 0 := by linear_combination E01
      exact (mul_eq_zero.1 this).resolve_right hss
    · have : z * (s - s⁻¹) = 0 := by linear_combination E10
      exact (mul_eq_zero.1 this).resolve_right (by
        intro h
        apply hss
        linear_combination -h)

variable (K p f) in
@[expose] noncomputable def weylElt : Su K p f 2 :=
  ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩,
    by simp [Matrix.det_fin_two],
    by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem weylElt_conj (B : Su K p f 2) :
    ((weylElt K p f : Su K p f 2) : GL (Fin 2) K) * (B : GL (Fin 2) K) *
        ((weylElt K p f : Su K p f 2) : GL (Fin 2) K)⁻¹ =
      Matrix.GeneralLinearGroup.map (unitaryInvolution K p f : K →+* K) (B : GL (Fin 2) K) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact conj_w_eq_map (unitaryInvolution K p f : K →+* K) _ B.2.1 B.2.2

theorem exists_normOne_of_diag (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (x w : Kˣ) (φ : K ≃+* K)
    (hα : ∀ B : Su K p f 2, ((α B : Su K p f 2) : GL (Fin 2) K) =
      diagGL ![x, w] * Matrix.GeneralLinearGroup.map (φ : K →+* K) (B : GL (Fin 2) K) *
        (diagGL ![x, w])⁻¹) :
    ∃ a : normOne (unitaryInvolution K p f),
      α = diagConj p f hK ![a, 1] * fieldAutSU p f φ 2 := by
  have hMv : (((α (weylElt K p f) : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      !![0, (x : K) * ((w⁻¹ : Kˣ) : K); -((w : K) * ((x⁻¹ : Kˣ) : K)), 0] := by
    rw [hα]
    simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [weylElt, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hunit := (α (weylElt K p f)).2.2
  rw [hMv] at hunit
  have h11 := congrFun (congrFun hunit 1) 1
  simp [conjTr, Matrix.mul_apply, Fin.sum_univ_two] at h11
  have hN : unitaryInvolution K p f (((x * w⁻¹ : Kˣ)) : K) * ((x * w⁻¹ : Kˣ) : K) = 1 := by
    simpa [Units.val_mul] using h11
  refine ⟨⟨x * w⁻¹, (mem_normOne _).2 hN⟩, MulEquiv.ext fun B => Subtype.ext (Units.ext ?_)⟩
  show (((α B : Su K p f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    ((diagConj p f hK ![⟨x * w⁻¹, (mem_normOne _).2 hN⟩, 1] (fieldAutSU p f φ 2 B) :
      Su K p f 2) : GL (Fin 2) K)
  rw [coe_diagConj, hα B]
  simp only [Units.val_mul, coe_diagGL, coe_diagGL_inv, coe_fieldAutSU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal] <;> field_simp

theorem exists_diagConj_fieldAut (hK : Nat.card K = (p ^ f) ^ 2) (α : MulAut (Su K p f 2))
    (hα : (torusTwo (unitaryInvolution K p f)).range.map α.toMonoidHom ≤
      (torusTwo (unitaryInvolution K p f)).range) :
    ∃ (a b : normOne (unitaryInvolution K p f)) (φ : K ≃+* K),
      α = diagConj p f hK ![a, b] * fieldAutSU p f φ 2 := by
  obtain ⟨u, φ, hu⟩ := exists_eq_conj_map hK α
  obtain ⟨l, hl, hlo⟩ := exists_norm_one_orderOf_eq hK
  have hl2 : l ^ 2 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hlo] at h1
    have h2 := Nat.le_of_dvd (by norm_num) h1
    have := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hK
    omega
  let s0 : normOne (unitaryInvolution K p f) := ⟨l, hl⟩
  obtain ⟨t, ht⟩ := hα (Subgroup.mem_map_of_mem α.toMonoidHom
    (MonoidHom.mem_range.2 ⟨s0, rfl⟩ :
      torusTwo (unitaryInvolution K p f) s0 ∈ (torusTwo (unitaryInvolution K p f)).range))
  have ht' : α (torusTwo (unitaryInvolution K p f) s0) = torusTwo (unitaryInvolution K p f) t :=
    ht.symm
  have h1 : (diagGL ![(t : Kˣ), (t : Kˣ)⁻¹] : GL (Fin 2) K) =
      u * Matrix.GeneralLinearGroup.map (φ : K →+* K) (diagGL ![l, l⁻¹]) * u⁻¹ := by
    have := hu (torusTwo (unitaryInvolution K p f) s0)
    rw [ht'] at this
    exact this
  have h2 : (diagGL ![(t : Kˣ), (t : Kˣ)⁻¹] : GL (Fin 2) K) * u =
      u * Matrix.GeneralLinearGroup.map (φ : K →+* K) (diagGL ![l, l⁻¹]) := by
    rw [h1, mul_assoc, inv_mul_cancel, mul_one]
  have hm := congrArg Units.val h2
  have e00 := congrFun (congrFun hm 0) 0
  have e01 := congrFun (congrFun hm 0) 1
  have e10 := congrFun (congrFun hm 1) 0
  have e11 := congrFun (congrFun hm 1) 1
  simp [Units.val_mul, coe_diagGL, Matrix.mul_apply, Matrix.diagonal_apply] at e00 e01 e10 e11
  have hs : (φ (l : K)) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    apply hl2
    have h' := φ.injective (h.trans (map_one φ).symm)
    exact Units.ext (by simpa using h')
  have hs0 : φ (l : K) ≠ 0 := (map_ne_zero φ).2 (Units.ne_zero l)
  have hdet : (u : Matrix (Fin 2) (Fin 2) K) 0 0 * (u : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (u : Matrix (Fin 2) (Fin 2) K) 0 1 * (u : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact (Matrix.isUnits_det_units u).ne_zero
  rcases monomial_aux hs hs0 hdet e00.symm e01.symm e10.symm e11.symm with ⟨hy, hz⟩ | ⟨hx, hw⟩
  ·
    have hxw : (u : Matrix (Fin 2) (Fin 2) K) 0 0 * (u : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
      simpa [hy, hz] using hdet
    obtain ⟨x', w', hx0, hw0, hu_eq⟩ : ∃ (x' w' : K) (hx0 : x' ≠ 0) (hw0 : w' ≠ 0),
        u = diagGL ![Units.mk0 x' hx0, Units.mk0 w' hw0] :=
      ⟨_, _, left_ne_zero_of_mul hxw, right_ne_zero_of_mul hxw, by
        apply Units.ext
        rw [coe_diagGL]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hy, hz]⟩
    rw [hu_eq] at hu
    obtain ⟨a, ha⟩ := exists_normOne_of_diag hK α _ _ φ hu
    exact ⟨a, 1, φ, ha⟩
  ·
    have hyz : (u : Matrix (Fin 2) (Fin 2) K) 0 1 * (u : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
      simpa [hx, hw] using hdet
    obtain ⟨y', z', hy0, hz0, hu_eq⟩ : ∃ (y' z' : K) (hy0 : y' ≠ 0) (hz0 : z' ≠ 0),
        u = diagGL ![Units.mk0 y' hy0, Units.mk0 (-z') (neg_ne_zero.2 hz0)] *
          ((weylElt K p f : Su K p f 2) : GL (Fin 2) K) :=
      ⟨_, _, left_ne_zero_of_mul hyz, right_ne_zero_of_mul hyz, by
        apply Units.ext
        rw [Units.val_mul, coe_diagGL]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [weylElt, hx, hw, Matrix.diagonal_mul]⟩
    rw [hu_eq] at hu
    have hα' : ∀ B : Su K p f 2, ((α B : Su K p f 2) : GL (Fin 2) K) =
        diagGL ![Units.mk0 y' hy0, Units.mk0 (-z') (neg_ne_zero.2 hz0)] *
          Matrix.GeneralLinearGroup.map
            ((φ.trans (unitaryInvolution K p f) : K ≃+* K) : K →+* K) (B : GL (Fin 2) K) *
          (diagGL ![Units.mk0 y' hy0, Units.mk0 (-z') (neg_ne_zero.2 hz0)])⁻¹ := by
      intro B
      rw [hu B]
      have hW := weylElt_conj (fieldAutSU p f φ 2 B)
      rw [coe_fieldAutSU] at hW
      calc _ = diagGL ![Units.mk0 y' hy0, Units.mk0 (-z') (neg_ne_zero.2 hz0)] *
            (((weylElt K p f : Su K p f 2) : GL (Fin 2) K) *
              Matrix.GeneralLinearGroup.map (φ : K →+* K) (B : GL (Fin 2) K) *
              ((weylElt K p f : Su K p f 2) : GL (Fin 2) K)⁻¹) *
            (diagGL ![Units.mk0 y' hy0, Units.mk0 (-z') (neg_ne_zero.2 hz0)])⁻¹ := by
            simp only [_root_.mul_inv_rev, mul_assoc]
        _ = _ := by rw [hW]; rfl
    obtain ⟨a, ha⟩ := exists_normOne_of_diag hK α _ _ (φ.trans (unitaryInvolution K p f)) hα'
    exact ⟨a, 1, φ.trans (unitaryInvolution K p f), ha⟩

end Torus

end CFSG.ClassicalInvolution.Phan

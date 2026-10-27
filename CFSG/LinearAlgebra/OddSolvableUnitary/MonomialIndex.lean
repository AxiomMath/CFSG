module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.OddSolvableUnitary

open Subgroup Matrix CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K]

theorem coe_cycGL_eq_permMatrix :
    ((cycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMatrix 3 K (finRotate 3) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_cycGL, cycMat, permMatrix_apply]

theorem coe_s01GL_eq_permMatrix [CharP K 2] :
    ((s01GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMatrix 3 K (Equiv.swap 0 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_s01GL, s01Mat, permMatrix_apply, Equiv.swap_apply_def, CharTwo.neg_eq]

theorem s01GL_conj_cycGL : (s01GL : GL (Fin 3) K) * cycGL * s01GL⁻¹ = cycGL⁻¹ := by
  apply Units.ext
  rw [s01GL_inv, Units.val_mul, Units.val_mul, coe_s01GL, coe_cycGL, coe_cycGL_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s01Mat, cycMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem s01GL_ne_one : (s01GL : GL (Fin 3) K) ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K))
    h) 0) 0
  simp [coe_s01GL, s01Mat] at this

theorem orderOf_s01GL : orderOf (s01GL : GL (Fin 3) K) = 2 :=
  orderOf_eq_prime s01GL_sq s01GL_ne_one

theorem mem_normOne_iff_norm (hK : UnitaryFieldData 2 f K) {a : Kˣ} :
    a ∈ normOne K (2 ^ f) ↔ hK.norm a = 1 := by
  rw [mem_normOne, hK.norm_eq_pow, ← Units.val_pow_eq_pow_val, Units.val_eq_one]

theorem card_normOne_eq (hK : UnitaryFieldData 2 f K) :
    Nat.card (normOne K (2 ^ f)) = 2 ^ f + 1 :=
  have := hK.finite
  card_normOne hK.card_eq_sq

theorem odd_card_normOne (hK : UnitaryFieldData 2 f K) : Odd (Nat.card (normOne K (2 ^ f))) := by
  rw [card_normOne_eq hK]
  have : Even (2 ^ f) := (Nat.even_pow' (by have := hK.one_le; omega)).2 even_two
  exact this.add_one

@[expose] noncomputable def homologyHom (M : Subgroup Kˣ) : M →* GL (Fin 3) K where
  toFun a := diagHom 3 ![(a : Kˣ), (a : Kˣ), ((a : Kˣ) * a)⁻¹]
  map_one' := by
    rw [← map_one (diagHom (K := K) 3)]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' a b := by
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem homologyHom_apply (M : Subgroup Kˣ) (a : M) :
    homologyHom M a = diagHom 3 ![(a : Kˣ), (a : Kˣ), ((a : Kˣ) * a)⁻¹] :=
  rfl

theorem homologyHom_injective (M : Subgroup Kˣ) : Function.Injective (homologyHom (K := K) M) := by
  intro a b h
  have h0 := congrFun (diagHom_injective 3 h) 0
  exact Subtype.ext h0

@[expose] noncomputable def homologyTorus (M : Subgroup Kˣ) : Subgroup (GL (Fin 3) K) :=
  (homologyHom M).range

theorem card_homologyTorus [Finite K] (M : Subgroup Kˣ) :
    Nat.card (homologyTorus (K := K) M) = Nat.card M := by
  rw [homologyTorus, ← Nat.card_congr (MonoidHom.ofInjective (homologyHom_injective M)).toEquiv]

theorem homologyTorus_le_torus3 (M : Subgroup Kˣ) : homologyTorus (K := K) M ≤ torus3 M := by
  rintro _ ⟨a, rfl⟩
  refine (mem_torus3 M).2 ⟨_, fun i => ?_, ?_, rfl⟩
  · fin_cases i
    · exact a.2
    · exact a.2
    · exact M.inv_mem (M.mul_mem a.2 a.2)
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    exact mul_inv_cancel _

theorem s01GL_commute_homologyHom (M : Subgroup Kˣ) (a : M) :
    s01GL * homologyHom M a * s01GL⁻¹ = homologyHom M a := by
  rw [homologyHom_apply, s01GL_conj_diagHom]
  rfl

section Monomial

variable (M : Subgroup Kˣ)

noncomputable abbrev monomialX : Subgroup (GL (Fin 3) K) :=
  torus3 M ⊔ zpowers (cycGL : GL (Fin 3) K)

theorem s01GL_conj_mem_torus3 {x : GL (Fin 3) K} (hx : x ∈ torus3 M) :
    s01GL * x * s01GL⁻¹ ∈ torus3 M := by
  obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 hx
  rw [s01GL_conj_diagHom]
  refine (mem_torus3 M).2 ⟨_, fun i => ?_, ?_, rfl⟩
  · fin_cases i <;> simp [hdM]
  · change d 1 * d 0 * d 2 = 1
    rw [← hd]
    ac_rfl

theorem commutatorElement_diagHom_s01GL (d : Fin 3 → Kˣ) :
    ⁅diagHom 3 d, (s01GL : GL (Fin 3) K)⁆ = diagHom 3 ![d 0 * (d 1)⁻¹, d 1 * (d 0)⁻¹, 1] := by
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc s01GL, ← map_inv,
    s01GL_conj_diagHom, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

variable [Finite K]

theorem s01GL_conj_mem_monomialX {x : GL (Fin 3) K} (hx : x ∈ monomialX M) :
    s01GL * x * s01GL⁻¹ ∈ monomialX M := by
  obtain ⟨d, hd, j, -, rfl⟩ := exists_mem_torus3_mul_cyc M hx
  have e : s01GL * (d * cycGL ^ j) * s01GL⁻¹ =
      (s01GL * d * s01GL⁻¹) * (s01GL * cycGL * s01GL⁻¹) ^ j := by
    rw [conj_pow]; group
  rw [e, s01GL_conj_cycGL]
  exact mul_mem (mem_sup_left (s01GL_conj_mem_torus3 M hd))
    (mem_sup_right (pow_mem (inv_mem (mem_zpowers _)) j))

theorem s01GL_mem_normalizer_monomialX :
    (s01GL : GL (Fin 3) K) ∈ normalizer (monomialX M : Set (GL (Fin 3) K)) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨s01GL_conj_mem_monomialX M, fun hx => ?_⟩
  have h := s01GL_conj_mem_monomialX M hx
  rwa [s01GL_inv, show s01GL * (s01GL * x * s01GL) * s01GL = (s01GL * s01GL) * x *
    (s01GL * s01GL) by group, ← sq, s01GL_sq, one_mul, mul_one] at h

theorem commutator_monomialX_le :
    ⁅monomialX M, zpowers (s01GL : GL (Fin 3) K)⁆ ≤ monomialX M := by
  rw [commutator_le]
  intro x hx y hy
  have hyN : y ∈ normalizer (monomialX M : Set (GL (Fin 3) K)) :=
    (zpowers_le.2 (s01GL_mem_normalizer_monomialX M)) hy
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine mul_mem hx ?_
  rw [← mul_assoc]
  exact (mem_normalizer_iff.1 hyN _).1 (inv_mem hx)

theorem exists_sq_eq_of_odd {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) (a : G) :
    ∃ b : G, b ^ 2 = a := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨a ^ (k + 1), ?_⟩
  rw [← pow_mul, show (k + 1) * 2 = Nat.card G + 1 by omega, pow_succ, pow_card_eq_one',
    one_mul]

omit [Finite K] in
theorem commutatorElement_cycGL_sq_s01GL :
    ⁅(cycGL : GL (Fin 3) K) ^ 2, (s01GL : GL (Fin 3) K)⁆ = cycGL := by
  have h1 : (s01GL : GL (Fin 3) K) * ((cycGL : GL (Fin 3) K) ^ 2)⁻¹ * s01GL⁻¹ =
      cycGL ^ 2 := by
    rw [← inv_pow, ← conj_pow, ← conj_inv, s01GL_conj_cycGL, inv_inv]
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc s01GL, h1,
    ← pow_add, show 2 + 2 = 3 + 1 by rfl, pow_succ, cycGL_pow_three, one_mul]

theorem commutator_monomialX_eq (hM : Odd (Nat.card M)) :
    ⁅monomialX M, zpowers (s01GL : GL (Fin 3) K)⁆ = monomialX M := by
  refine le_antisymm (commutator_monomialX_le M) ?_
  set C := ⁅monomialX M, zpowers (s01GL : GL (Fin 3) K)⁆
  have hcomm : ∀ x ∈ monomialX M, ⁅x, s01GL⁆ ∈ C := fun x hx =>
    commutator_mem_commutator hx (mem_zpowers _)
  have hA12 : ∀ a ∈ M, diagHom 3 ![a, a⁻¹, 1] ∈ C := by
    intro a ha
    obtain ⟨b, hb⟩ := exists_sq_eq_of_odd hM ⟨a, ha⟩
    have hbT : diagHom 3 ![(b : Kˣ), (b : Kˣ)⁻¹, 1] ∈ monomialX M := by
      refine mem_sup_left ((mem_torus3 M).2 ⟨_, fun i => ?_, by simp, rfl⟩)
      fin_cases i
      · exact b.2
      · exact M.inv_mem b.2
      · exact M.one_mem
    have h := hcomm _ hbT
    rw [commutatorElement_diagHom_s01GL] at h
    have hb' : (b : Kˣ) * (b : Kˣ) = a := by rw [← sq]; exact congrArg Subtype.val hb
    convert h using 2
    funext i
    fin_cases i
    · simp [← hb']
    · simp [← hb']
    · rfl
  have hs : (cycGL : GL (Fin 3) K) ∈ C := by
    have h := hcomm (cycGL ^ 2) (mem_sup_right (pow_mem (mem_zpowers _) 2))
    rwa [commutatorElement_cycGL_sq_s01GL] at h
  have hA23 : ∀ a ∈ M, diagHom 3 ![1, a, a⁻¹] ∈ C := by
    intro a ha
    have h := C.mul_mem (C.mul_mem hs (hA12 a ha)) (C.inv_mem hs)
    rw [cycGL_conj_diagHom] at h
    exact h
  have hT : torus3 M ≤ C := by
    intro x hx
    obtain ⟨d, hdM, hd, rfl⟩ := (mem_torus3 M).1 hx
    have hd1 : d 1 = (d 0)⁻¹ * (d 2)⁻¹ := by
      calc d 1 = (d 0)⁻¹ * (d 0 * d 1 * d 2) * (d 2)⁻¹ := by group
        _ = (d 0)⁻¹ * (d 2)⁻¹ := by rw [hd]; group
    have e : diagHom 3 d = diagHom 3 ![d 0, (d 0)⁻¹, 1] * diagHom 3 ![1, (d 2)⁻¹, (d 2)⁻¹⁻¹] := by
      rw [← map_mul]
      congr 1
      funext i
      fin_cases i
      · simp
      · simp [hd1]
      · simp
    rw [e]
    exact C.mul_mem (hA12 _ (hdM 0)) (hA23 _ (M.inv_mem (hdM 2)))
  exact sup_le hT (zpowers_le.2 hs)

theorem mem_homologyTorus_of_mul_eq {x : GL (Fin 3) K} (hx : x ∈ monomialX M) {c : Kˣ}
    (h : x * s01GL = Matrix.GeneralLinearGroup.scalar (Fin 3) c * (s01GL * x)) :
    c = 1 ∧ x ∈ homologyTorus M := by
  obtain ⟨d, hd, j, hj, rfl⟩ := exists_mem_torus3_mul_cyc M hx
  obtain ⟨e, heM, he, rfl⟩ := (mem_torus3 M).1 hd
  have hm := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, coe_diagHom, coe_cycGL, coe_s01GL,
    Matrix.GeneralLinearGroup.coe_scalar] at hm
  interval_cases j
  · have h22 := congrFun (congrFun hm 2) 2
    have h01 := congrFun (congrFun hm 0) 1
    simp [s01Mat, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul, dotProduct] at h22 h01
    have hc : c = 1 := by
      have h2 : (e 2 : K) ≠ 0 := (e 2).ne_zero
      ext
      simpa [h2] using h22
    subst hc
    have he01 : e 0 = e 1 := Units.ext (by simpa using h01)
    refine ⟨rfl, ⟨e 0, heM 0⟩, ?_⟩
    rw [pow_zero, mul_one, homologyHom_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact he01
    · change ((e 0 : Kˣ) * e 0)⁻¹ = e 2
      rw [inv_eq_iff_mul_eq_one, ← he, he01]
  · have h00 := congrFun (congrFun hm 0) 0
    simp [s01Mat, cycMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply,
      Matrix.vecMul, dotProduct] at h00
  · have h00 := congrFun (congrFun hm 0) 0
    simp [s01Mat, cycMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, sq,
      Matrix.vecMul, dotProduct] at h00

end Monomial

section Counting

variable {G G' : Type*} [Group G] [Group G']

theorem card_map_mul_card_ker [Finite G] (φ : G →* G') {K : Subgroup G} (hK : φ.ker ≤ K) :
    Nat.card (K.map φ) * Nat.card φ.ker = Nat.card K := by
  let ψ := φ.comp K.subtype
  have hrange : ψ.range = K.map φ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : ψ.ker = φ.ker.subgroupOf K := by
    ext x
    simp [ψ, Subgroup.mem_subgroupOf]
  rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv, ← hker,
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem ncard_conj_mul_card_inf_centralizer (P : Subgroup G) [Finite P] (g : G) :
    {y | ∃ x ∈ P, x * g * x⁻¹ = y}.ncard * Nat.card (P ⊓ centralizer {g} : Subgroup G) =
      Nat.card P := by
  let _ : MulAction P G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp P.subtype)
  have hsmul : ∀ (x : P) (y : G), x • y = (x : G) * y * (x : G)⁻¹ := fun x y =>
    ConjAct.toConjAct_smul (x : G) y
  have horb : MulAction.orbit P g = {y | ∃ x ∈ P, x * g * x⁻¹ = y} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x g).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hsmul _ g⟩
  have hstab : MulAction.stabilizer P g = (centralizer {g}).subgroupOf P := by
    ext x
    rw [MulAction.mem_stabilizer_iff, hsmul, mem_subgroupOf, mem_centralizer_singleton_iff,
      mul_inv_eq_iff_eq_mul]
  have h := (MulAction.stabilizer P g).index_mul_card
  rw [MulAction.index_stabilizer, horb, hstab, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h
  exact h

theorem commutator_subgroupOf_eq {S X : Subgroup G} {t : G} (hXS : X ≤ S) (htS : t ∈ S)
    (h : ⁅X, zpowers t⁆ = X) :
    ⁅X.subgroupOf S, zpowers (⟨t, htS⟩ : S)⁆ = X.subgroupOf S := by
  apply Subgroup.map_injective S.subtype_injective
  rw [Subgroup.map_commutator, MonoidHom.map_zpowers, subgroupOf_map_subtype,
    inf_of_le_left hXS, Subgroup.coe_subtype, h]

end Counting

section Unitary

variable (hK : UnitaryFieldData 2 f K)
include hK

theorem cycGL_mem_unitarySU : (cycGL : GL (Fin 3) K) ∈ unitarySU 2 f K 3 := by
  have : CharP K 2 := hK.charP
  exact (monomialData_statedSU (p := 2) (f := f)).cyc_mem

theorem s01GL_mem_unitarySU : (s01GL : GL (Fin 3) K) ∈ unitarySU 2 f K 3 := by
  have : CharP K 2 := hK.charP
  exact (monomialData_statedSU (p := 2) (f := f)).s01_mem

theorem monomialX_le_unitarySU : monomialX (normOne K (2 ^ f)) ≤ unitarySU 2 f K 3 := by
  have : CharP K 2 := hK.charP
  exact sup_le (torus3_le _ (monomialData_statedSU (p := 2) (f := f)))
    (zpowers_le.2 (cycGL_mem_unitarySU hK))

theorem card_monomialX : Nat.card (monomialX (normOne K (2 ^ f))) = 3 * (2 ^ f + 1) ^ 2 := by
  have := hK.finite
  rw [card_torus3_sup_cyc, card_normOne_eq hK]

theorem coe_mem_homologyTorus_of_mem_unitaryScalars {z : unitarySU 2 f K 3}
    (hz : z ∈ unitaryScalars hK 3) : (z : GL (Fin 3) K) ∈ homologyTorus (normOne K (2 ^ f)) := by
  obtain ⟨c, hcN, hc3, hz⟩ := mem_unitaryScalars.1 hz
  refine ⟨⟨c, (mem_normOne_iff_norm hK).2 hcN⟩, ?_⟩
  rw [hz, homologyHom_apply]
  apply Units.ext
  rw [coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  congr 1
  funext i
  fin_cases i
  · rfl
  · rfl
  · change (((c * c)⁻¹ : Kˣ) : K) = c
    rw [show (c * c)⁻¹ = c from inv_eq_of_mul_eq_one_left (by rw [← pow_three]; exact hc3)]

end Unitary

section Quotient

noncomputable abbrev monomialSU : Subgroup (unitarySU 2 f K 3) :=
  (monomialX (normOne K (2 ^ f))).subgroupOf (unitarySU 2 f K 3)

noncomputable abbrev homologySU : Subgroup (unitarySU 2 f K 3) :=
  (homologyTorus (normOne K (2 ^ f))).subgroupOf (unitarySU 2 f K 3)

variable (hK : UnitaryFieldData 2 f K)

abbrev transpositionSU : unitarySU 2 f K 3 :=
  ⟨s01GL, s01GL_mem_unitarySU hK⟩

theorem homologySU_le_monomialSU : (homologySU : Subgroup (unitarySU 2 f K 3)) ≤ monomialSU :=
  fun _ hx => mem_sup_left (homologyTorus_le_torus3 _ hx)

theorem unitaryScalars_le_homologySU : unitaryScalars hK 3 ≤ homologySU :=
  fun _ hz => coe_mem_homologyTorus_of_mem_unitaryScalars hK hz

include hK in
theorem card_monomialSU : Nat.card (monomialSU : Subgroup (unitarySU 2 f K 3)) =
    3 * (2 ^ f + 1) ^ 2 := by
  rw [Nat.card_congr (subgroupOfEquivOfLe (monomialX_le_unitarySU hK)).toEquiv,
    card_monomialX hK]

include hK in
theorem card_homologySU : Nat.card (homologySU : Subgroup (unitarySU 2 f K 3)) = 2 ^ f + 1 := by
  have := hK.finite
  rw [Nat.card_congr (subgroupOfEquivOfLe ((homologyTorus_le_torus3 _).trans
    (le_sup_left.trans (monomialX_le_unitarySU hK)))).toEquiv, card_homologyTorus,
    card_normOne_eq hK]

variable {G' : Type*} [Group G'] (ψ : unitarySU 2 f K 3 →* G') (hψ : ψ.ker ≤ unitaryScalars hK 3)
include hψ

theorem orderOf_map_transpositionSU : orderOf (ψ (transpositionSU hK)) = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [← map_pow]
    convert map_one ψ
    exact Subtype.ext s01GL_sq
  · obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 (hψ (MonoidHom.mem_ker.2 h))
    have := congrFun (congrFun (congrArg (fun g : GL (Fin 3) K =>
      (g : Matrix (Fin 3) (Fin 3) K)) hc) 0) 0
    simp [coe_s01GL, s01Mat, Matrix.GeneralLinearGroup.coe_scalar] at this
    exact c.ne_zero this.symm

omit hψ in
theorem commutator_map_monomialSU :
    ⁅monomialSU.map ψ, zpowers (ψ (transpositionSU hK))⁆ = monomialSU.map ψ := by
  have := hK.finite
  rw [← MonoidHom.map_zpowers, ← Subgroup.map_commutator,
    commutator_subgroupOf_eq (monomialX_le_unitarySU hK) (s01GL_mem_unitarySU hK)
      (commutator_monomialX_eq _ (odd_card_normOne hK))]

theorem card_map_monomialSU [Finite K] :
    Nat.card (monomialSU.map ψ) * Nat.card ψ.ker = 3 * (2 ^ f + 1) ^ 2 := by
  rw [card_map_mul_card_ker ψ (hψ.trans ((unitaryScalars_le_homologySU hK).trans
    homologySU_le_monomialSU)), card_monomialSU hK]

theorem card_map_homologySU [Finite K] :
    Nat.card (homologySU.map ψ) * Nat.card ψ.ker = 2 ^ f + 1 := by
  rw [card_map_mul_card_ker ψ (hψ.trans (unitaryScalars_le_homologySU hK)), card_homologySU hK]

theorem inf_centralizer_map_monomialSU [Finite K] :
    monomialSU.map ψ ⊓ centralizer {ψ (transpositionSU hK)} = homologySU.map ψ := by
  refine le_antisymm ?_ (le_inf (map_mono homologySU_le_monomialSU) ?_)
  · intro y hy
    obtain ⟨⟨x, hxX, rfl⟩, hxc⟩ := Subgroup.mem_inf.1 hy
    rw [mem_centralizer_singleton_iff] at hxc
    have hker : x * transpositionSU hK * x⁻¹ * (transpositionSU hK)⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hxc]
      group
    obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.1 (hψ hker)
    have hrel : (x : GL (Fin 3) K) * s01GL =
        Matrix.GeneralLinearGroup.scalar (Fin 3) c * (s01GL * (x : GL (Fin 3) K)) := by
      rw [← hc]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    exact ⟨x, (mem_homologyTorus_of_mul_eq _ hxX hrel).2, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    obtain ⟨a, ha⟩ := hx
    apply Subtype.ext
    have h := s01GL_commute_homologyHom (normOne K (2 ^ f)) a
    rw [ha, Subgroup.coe_subtype] at h
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    calc (x : GL (Fin 3) K) * s01GL =
        s01GL * (x : GL (Fin 3) K) * s01GL⁻¹ * s01GL := by rw [h]
      _ = s01GL * (x : GL (Fin 3) K) := by group

theorem ncard_conj_map_transpositionSU [Finite K] :
    {y | ∃ x ∈ monomialSU.map ψ, x * ψ (transpositionSU hK) * x⁻¹ = y}.ncard =
      3 * (2 ^ f + 1) := by
  have : Finite (monomialSU.map ψ : Subgroup G') :=
    Finite.of_surjective _ (ψ.subgroupMap_surjective monomialSU)
  have h := ncard_conj_mul_card_inf_centralizer (monomialSU.map ψ) (ψ (transpositionSU hK))
  rw [inf_centralizer_map_monomialSU hK ψ hψ] at h
  have h1 := card_map_monomialSU hK ψ hψ
  have h2 := card_map_homologySU hK ψ hψ
  rw [← h, mul_assoc, h2] at h1
  have hq : 0 < 2 ^ f + 1 := by positivity
  exact Nat.eq_of_mul_eq_mul_right hq (by rw [h1]; ring)

end Quotient

theorem even_unitary_three_monomial_odd_subgroup_involution_index (hK : UnitaryFieldData 2 f K)
    (Z₀ : Subgroup (unitarySU 2 f K 3)) (hZ₀ : Z₀ ≤ unitaryScalars hK 3) :
    haveI : Z₀.Normal := normal_of_le_center (hZ₀.trans (unitaryScalars_le_center hK 3))
    let π : unitarySU 2 f K 3 →* unitarySU 2 f K 3 ⧸ Z₀ := QuotientGroup.mk' Z₀
    (∀ a : Kˣ, a ∈ normOne K (2 ^ f) ↔ hK.norm a = 1) ∧
      ((cycGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMatrix 3 K (finRotate 3) ∧
      ((s01GL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = permMatrix 3 K (Equiv.swap 0 1) ∧
      monomialX (normOne K (2 ^ f)) ≤ unitarySU 2 f K 3 ∧
      Nat.card (monomialX (normOne K (2 ^ f))) = 3 * (2 ^ f + 1) ^ 2 ∧
      Odd (Nat.card (monomialX (normOne K (2 ^ f)))) ∧
      (s01GL : GL (Fin 3) K) ∈ unitarySU 2 f K 3 ∧ orderOf (s01GL : GL (Fin 3) K) = 2 ∧
      (s01GL : GL (Fin 3) K) ∈ normalizer (monomialX (normOne K (2 ^ f)) : Set (GL (Fin 3) K)) ∧
      ⁅monomialX (normOne K (2 ^ f)), zpowers (s01GL : GL (Fin 3) K)⁆ =
        monomialX (normOne K (2 ^ f)) ∧
      orderOf (π (transpositionSU hK)) = 2 ∧
      ⁅monomialSU.map π, zpowers (π (transpositionSU hK))⁆ = monomialSU.map π ∧
      Nat.card (monomialSU.map π) = 3 * (2 ^ f + 1) ^ 2 / Nat.card Z₀ ∧
      monomialSU.map π ⊓ centralizer {π (transpositionSU hK)} = homologySU.map π ∧
      Nat.card (homologySU.map π) = (2 ^ f + 1) / Nat.card Z₀ ∧
      {y | ∃ x ∈ monomialSU.map π, x * π (transpositionSU hK) * x⁻¹ = y}.ncard =
        3 * (2 ^ f + 1) ∧
      Nat.card (unitaryScalars hK 3) = Nat.gcd 3 (2 ^ f + 1) ∧
      (Z₀ = unitaryScalars hK 3 →
        Nat.card (monomialSU.map π) = 3 * (2 ^ f + 1) ^ 2 / Nat.gcd 3 (2 ^ f + 1)) := by
  have := hK.finite
  have : CharP K 2 := hK.charP
  have : Z₀.Normal := normal_of_le_center (hZ₀.trans (unitaryScalars_le_center hK 3))
  intro π
  have hπ : π.ker ≤ unitaryScalars hK 3 := by
    rw [QuotientGroup.ker_mk']
    exact hZ₀
  have hker : Nat.card π.ker = Nat.card Z₀ := by rw [QuotientGroup.ker_mk']
  have hZpos : 0 < Nat.card Z₀ := Nat.card_pos
  have hX := card_map_monomialSU hK π hπ
  have hH := card_map_homologySU hK π hπ
  rw [hker] at hX hH
  have hcardZ := card_unitaryScalars hK (n := 3) (by norm_num)
  refine ⟨fun a => mem_normOne_iff_norm hK, coe_cycGL_eq_permMatrix, coe_s01GL_eq_permMatrix,
    monomialX_le_unitarySU hK, card_monomialX hK, ?_, s01GL_mem_unitarySU hK, orderOf_s01GL,
    s01GL_mem_normalizer_monomialX _, commutator_monomialX_eq _ (odd_card_normOne hK),
    orderOf_map_transpositionSU hK π hπ, commutator_map_monomialSU hK π,
    (Nat.div_eq_of_eq_mul_left hZpos hX.symm).symm, inf_centralizer_map_monomialSU hK π hπ,
    (Nat.div_eq_of_eq_mul_left hZpos hH.symm).symm, ncard_conj_map_transpositionSU hK π hπ,
    hcardZ, fun h => ?_⟩
  · rw [card_monomialX hK]
    have h2 : Odd (2 ^ f + 1) := by
      have : Even (2 ^ f) := (Nat.even_pow' (by have := hK.one_le; omega)).2 even_two
      exact this.add_one
    exact (by decide : Odd 3).mul (h2.pow)
  · have hZ : Nat.card Z₀ = Nat.gcd 3 (2 ^ f + 1) := by rw [← hcardZ, h]
    rw [← hZ]
    exact (Nat.div_eq_of_eq_mul_left hZpos hX.symm).symm

end CFSG.OddSolvableUnitary

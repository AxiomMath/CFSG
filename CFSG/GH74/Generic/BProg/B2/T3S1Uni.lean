module

public import CFSG.GH74.Generic.BProg.B2.T3S1Lin
public import CFSG.GH74.Generic.S1.UniGraphA
public import CFSG.GH74.Generic.S1.UniClassify
public import CFSG.GH74.Generic.BProg.B2.GenLocU4OutFrame

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.Generic CFSG.Assembly.LowTwoRank Matrix Subgroup
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.Generic.S1.Uni
open scoped MatrixGroups

theorem goodFixedQ8_of_sl2 {K : Type} [Group K] {E : Type} [Field E] [Finite E] (hE4 : 4 ≤ Nat.card E)
    (hE2 : ringChar E ≠ 2) {T : Prop} (α : MulAut K) (ι : SL(2, E) →* K) (hfix : ∀ X, α (ι X) = ι X)
    (hc : ι (-1) ∈ Subgroup.center K) (h1 : ι (-1) ≠ 1) : GoodFixedQ8 T α := by
  obtain ⟨⟨a, b, hab⟩, H⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.odd_field_two_dimensional_quaternion_matrices hE2
  obtain ⟨hdI, hdJ, hII, hJJ, hIJ, -⟩ := H a b hab
  let I' : SL(2, E) := ⟨_, hdI⟩
  let J' : SL(2, E) := ⟨_, hdJ⟩
  have hI'I' : I' * I' = -1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact congrFun (congrFun hII i) j
  have hJ'J' : J' * J' = -1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one]
    exact congrFun (congrFun hJJ i) j
  have hI'J' : I' * J' = -1 * (J' * I') := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_one_mul]
    exact congrFun (congrFun hIJ i) j
  have hSL : Group.IsPerfect (SpecialLinearGroup (Fin 2) E) :=
    CFSG.ClassicalInvolution.sl2_isPerfect hE4
  refine ⟨ι.range, ?_, Or.inl (Subgroup.isPerfect_iff.1 (Group.IsPerfect.range ι)), ι I', ⟨I', rfl⟩,
    ι J', ⟨J', rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨X, rfl⟩
    exact hfix X
  · rw [← map_mul, hI'I']
    exact hc
  · rw [← map_mul, hI'I']
    exact h1
  · rw [← map_mul, ← map_mul, hI'I', hJ'J']
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hI'I', hI'J']

theorem fix_of_conj_gen {F : Type} [Field F] {S : Subgroup (GL (Fin 4) F)} {α : MulAut ↥S}
    {ρ P : GL (Fin 4) F} {μ : Fin 4 → F}
    (hα : ∀ k : ↥S, ((α k : ↥S) : GL (Fin 4) F) = ρ * k * ρ⁻¹)
    (hP : ((P⁻¹ * ρ * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal μ) :
    ∀ k ∈ ((signDiag4 F).map (MulAut.conj P).toMonoidHom).comap S.subtype, α k = k := by
  intro k hk
  obtain ⟨s, ⟨ε, -, hs⟩, hsk⟩ := hk
  have hsk' : (k : GL (Fin 4) F) = P * s * P⁻¹ := hsk.symm
  have hc : (P⁻¹ * ρ * P) * s = s * (P⁻¹ * ρ * P) := comm_of_diag hP hs
  apply Subtype.ext
  rw [hα, hsk']
  calc ρ * (P * s * P⁻¹) * ρ⁻¹ = P * ((P⁻¹ * ρ * P) * s) * (P⁻¹ * ρ * P)⁻¹ * P⁻¹ := by group
    _ = P * (s * (P⁻¹ * ρ * P)) * (P⁻¹ * ρ * P)⁻¹ * P⁻¹ := by rw [hc]
    _ = P * s * P⁻¹ := by group

namespace Uni

variable {p f : ℕ} {F : Type} [Field F]

theorem unitary_mul' (h : UnitaryFieldData p f F) {A B : Matrix (Fin 4) (Fin 4) F}
    (hA : cT h A * A = 1) (hB : cT h B * B = 1) : cT h (A * B) * (A * B) = 1 := by
  rw [cT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (cT h A), hA, Matrix.one_mul, hB]

theorem coe_inv_of_unitary (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1) :
    ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = cT h (P : Matrix (Fin 4) (Fin 4) F) :=
  Units.inv_eq_of_mul_eq_one_left hP

theorem unitary_inv (h : UnitaryFieldData p f F) {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1) :
    cT h ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [coe_inv_of_unitary h hP, cT_cT]
  exact mul_eq_one_comm.1 hP

theorem bar_sign (h : UnitaryFieldData p f F) {a : F} (ha : a * a = 1) : h.bar a = a := by
  rcases eq_one_or_neg_one_of_mul_self ha with rfl | rfl
  · exact map_one _
  · rw [map_neg, map_one]

theorem unitary_of_mem_signDiag4 (h : UnitaryFieldData p f F) {d : GL (Fin 4) F}
    (hd : d ∈ signDiag4 F) : cT h (d : Matrix (Fin 4) (Fin 4) F) * (d : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨ε, ⟨hε, -⟩, hd⟩ := hd
  rw [hd, cT_def, Matrix.diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal]
  rw [show (fun i => h.bar (ε i) * ε i) = fun _ => (1 : F) from funext fun i => by
    rw [bar_sign h (hε i), hε i], diagonal_one]

theorem mem_su_iff (h : UnitaryFieldData p f F) (A : GL (Fin 4) F) :
    A ∈ StatedSU 4 (p ^ f) F ↔ (A : Matrix (Fin 4) (Fin 4) F).det = 1 ∧
      cT h (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [show StatedSU 4 (p ^ f) F = unitarySU p f F 4 from rfl, mem_unitarySU_iff h]
  rfl

theorem conj_mem_su (h : UnitaryFieldData p f F) (P : GL (Fin 4) F)
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1) :
    ∀ d ∈ signDiag4 F, P * d * P⁻¹ ∈ (StatedSU 4 (p ^ f) F).subtype.range := by
  intro d hd
  refine ⟨⟨P * d * P⁻¹, (mem_su_iff h _).2 ⟨?_, ?_⟩⟩, rfl⟩
  · rw [Lin.det_conj, det_of_mem_signDiag4 hd]
  · rw [Units.val_mul, Units.val_mul]
    exact unitary_mul' h (unitary_mul' h hP (unitary_of_mem_signDiag4 h hd)) (unitary_inv h hP)

theorem unitary_frame (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (E : Subgroup (GL (Fin 4) F))
    (hEU : ∀ x ∈ E, cT h (x : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    ∃ P : GL (Fin 4) F, cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      ∀ x ∈ E, ∃ μ : Fin 4 → F, (∀ j, μ j * μ j = 1) ∧
        ((P⁻¹ * x * P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = diagonal μ := by
  classical
  have hpq : 2 ∣ p ^ f + 1 := even_iff_two_dvd.1 ((h.prime.odd_of_ne_two hp2).pow).add_one
  set U : Subgroup (GL (Fin 4) F) := primeFormUnitary h (CFSG.RankThree.PartOne.KCUnitaryModel.idGram F 4) with hU
  have hEU' : E ≤ U := by
    intro x hx
    rw [hU, mem_primeFormUnitary]
    simp only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one]
    exact hEU x hx
  set G : Subgroup ↥U := E.subgroupOf U with hG
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h Nat.prime_two hpq G
    (fun a ha b hb => Subtype.ext (hcomm _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb)))
    (fun a ha => Subtype.ext (by rw [Subgroup.coe_pow, sq, Subgroup.coe_one]
                                 exact hsq _ (mem_subgroupOf.1 ha)))
  have hPU : cT h ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((P : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    have h1 := (mem_primeFormUnitary (h := h)).1 P.2
    simp only [CFSG.RankThree.PartOne.KCUnitaryModel.idGram, Units.val_one, Matrix.mul_one] at h1
    exact h1
  refine ⟨(P : GL (Fin 4) F), hPU, fun x hx => ?_⟩
  have hD := hP ⟨x, hEU' hx⟩ (mem_subgroupOf.2 hx)
  set D : Matrix (Fin 4) (Fin 4) F :=
    (((P⁻¹ * ⟨x, hEU' hx⟩ * P : ↥U) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) with hDdef
  have hDeq : D = Matrix.diagonal (fun k => D k k) := hD.diagonal_diag.symm
  have hcoe : ((P : GL (Fin 4) F)⁻¹ * x * (P : GL (Fin 4) F) : GL (Fin 4) F) =
      ((P⁻¹ * ⟨x, hEU' hx⟩ * P : ↥U) : GL (Fin 4) F) := rfl
  have hDD : D * D = 1 := by
    have e : (P⁻¹ * ⟨x, hEU' hx⟩ * P) * (P⁻¹ * ⟨x, hEU' hx⟩ * P) = (1 : ↥U) := by
      have hxx : (⟨x, hEU' hx⟩ : ↥U) * ⟨x, hEU' hx⟩ = 1 := Subtype.ext (hsq x hx)
      calc (P⁻¹ * ⟨x, hEU' hx⟩ * P) * (P⁻¹ * ⟨x, hEU' hx⟩ * P)
          = P⁻¹ * ((⟨x, hEU' hx⟩ : ↥U) * ⟨x, hEU' hx⟩) * P := by group
        _ = 1 := by rw [hxx]; group
    have := congrArg (fun u : ↥U => ((u : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) e
    simpa [hDdef] using this
  refine ⟨fun k => D k k, fun j => ?_, ?_⟩
  · have := congrFun (congrFun hDD j) j
    rw [hDeq] at this
    simpa [Matrix.diagonal_mul_diagonal] using this
  · rw [hcoe]
    exact hDeq

theorem center_uni {q : ℕ} (hF : Nat.card F = q ^ 2) (hq : q % 4 = 1) [Finite F] :
    ∃ z : ↥(StatedSU 4 q F), z ≠ 1 ∧
      (∀ g : ↥(StatedSU 4 q F), g ∈ Subgroup.center ↥(StatedSU 4 q F) ↔ g = 1 ∨ g = z) ∧
      ∀ E : Subgroup ↥(StatedSU 4 q F), IsE8 E → z ∈ E := by
  obtain ⟨F', _, _, -, z, hz⟩ := B1.PilotS1.grpS1_uni hF hq
  refine ⟨z, ?_, hz.center, fun E hE => hz.e8 E hE.1 hE.2⟩
  intro h1
  have := hz.like.z_ord
  rw [h1, orderOf_one] at this
  omega

theorem frame_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (E : Subgroup ↥(StatedSU 4 (p ^ f) F))
    (hE : IsE8 E) :
    ∃ P : GL (Fin 4) F, cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 ∧
      ∀ e ∈ E, P⁻¹ * (e : GL (Fin 4) F) * P ∈ signDiag4 F := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' : Subgroup (GL (Fin 4) F) := E.map (StatedSU 4 (p ^ f) F).subtype with hE'
  have hel := hE.1
  have hcomm : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hel.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun g : ↥E => ((g : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F)) this
  have hsq : ∀ x ∈ E', x * x = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) a ha
    rw [sq] at this
    exact congrArg Subtype.val this
  have hEU : ∀ x ∈ E', cT h (x : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rintro _ ⟨a, -, rfl⟩
    exact ((mem_su_iff h _).1 a.2).2
  obtain ⟨P, hPU, hP⟩ := unitary_frame h hp2 E' hEU hcomm hsq
  refine ⟨P, hPU, fun e he => ?_⟩
  obtain ⟨μ, hμ, hPe⟩ := hP _ ⟨e, he, rfl⟩
  exact mem_signDiag4_of_frame hμ hPe ((mem_su_iff h _).1 e.2).1

theorem conj_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (E E' : Subgroup ↥(StatedSU 4 (p ^ f) F))
    (hE : IsE8 E) (hE' : IsE8 E') :
    ∃ k : ↥(StatedSU 4 (p ^ f) F), E' = E.map (MulAut.conj k).toMonoidHom := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  obtain ⟨P, hPU, hP⟩ := frame_uni h hp2 E hE
  obtain ⟨P', hPU', hP'⟩ := frame_uni h hp2 E' hE'
  have hdP : (P : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units P).ne_zero
  have hdP' : (P' : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := (Matrix.isUnits_det_units P').ne_zero
  have hdetcT : ∀ M : Matrix (Fin 4) (Fin 4) F, (cT h M).det = h.bar M.det := fun M => by
    rw [cT, Matrix.det_transpose]
    exact (RingHom.map_det (h.bar : F →+* F) M).symm
  have hN : ∀ Q : GL (Fin 4) F, cT h (Q : Matrix (Fin 4) (Fin 4) F) * (Q : Matrix (Fin 4) (Fin 4) F) = 1 →
      h.bar (Q : Matrix (Fin 4) (Fin 4) F).det * (Q : Matrix (Fin 4) (Fin 4) F).det = 1 := by
    intro Q hQ
    have := congrArg Matrix.det hQ
    rwa [det_mul, hdetcT, det_one] at this
  set t : F := (P : Matrix (Fin 4) (Fin 4) F).det / (P' : Matrix (Fin 4) (Fin 4) F).det with ht
  have ht0 : t ≠ 0 := div_ne_zero hdP hdP'
  have htN : h.bar t * t = 1 := by
    have h1 := hN P hPU
    have h2' := hN P' hPU'
    rw [ht, map_div₀]
    have hb' : h.bar (P' : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h2'
      exact zero_ne_one h2'
    field_simp
    linear_combination h1 - h2'
  let d : GL (Fin 4) F := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagonal ![t, 1, 1, 1])
    (by rw [det_diagonal, Fin.prod_univ_four]; simpa using ht0)
  have hd : (d : Matrix (Fin 4) (Fin 4) F) = diagonal ![t, 1, 1, 1] := rfl
  have hdU : cT h (d : Matrix (Fin 4) (Fin 4) F) * (d : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [hd, cT_def, Matrix.diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal]
    rw [show (fun i => h.bar ((![t, 1, 1, 1] : Fin 4 → F) i) * (![t, 1, 1, 1] : Fin 4 → F) i) =
      fun _ => (1 : F) from funext fun i => by
        fin_cases i <;> simp [htN], diagonal_one]
  have hP'' : ∀ e ∈ E', (P' * d)⁻¹ * (e : GL (Fin 4) F) * (P' * d) ∈ signDiag4 F :=
    fun e he => frame_mul_diag hd (hP' e he)
  have hk : P' * d * P⁻¹ ∈ StatedSU 4 (p ^ f) F := by
    rw [mem_su_iff h]
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hd, det_diagonal, Fin.prod_univ_four]
      have h1 := Lin.det_inv_mul P
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, mul_one]
      rw [ht]
      field_simp
      linear_combination h1
    · rw [Units.val_mul, Units.val_mul]
      exact unitary_mul' h (unitary_mul' h hPU' hdU) (unitary_inv h hPU)
  exact ⟨⟨_, hk⟩, conj_of_frames (StatedSU 4 (p ^ f) F).subtype (Subgroup.subtype_injective _) h2
    hE.2 hE'.2 hP hP'' rfl⟩

theorem invol_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (t : ↥(StatedSU 4 (p ^ f) F))
    (ht : t * t = 1) : ∃ E : Subgroup ↥(StatedSU 4 (p ^ f) F), IsE8 E ∧ t ∈ E := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  set W : Subgroup (GL (Fin 4) F) := zpowers (t : GL (Fin 4) F) with hW
  have htt : (t : GL (Fin 4) F) * t = 1 := congrArg Subtype.val ht
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow_self _ m n).eq
  have hsq : ∀ x ∈ W, x * x = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show (t : GL (Fin 4) F) ^ (2 : ℤ) = 1 by
      rw [_root_.zpow_two, htt], _root_.one_zpow]
  have htU : cT h ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((t : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := ((mem_su_iff h _).1 t.2).2
  have hEU : ∀ x ∈ W, cT h (x : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show (t : GL (Fin 4) F) ^ (j + j) = 1 by
        rw [← two_mul, _root_.zpow_mul, _root_.zpow_two, htt, _root_.one_zpow]]
      simp [cT_one]
    · rw [show (t : GL (Fin 4) F) ^ (2 * j + 1) = t by
        rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_two, htt, _root_.one_zpow, one_mul,
          zpow_one]]
      exact htU
  obtain ⟨P, hPU, hP⟩ := unitary_frame h hp2 W hEU hcomm hsq
  obtain ⟨μ, hμ, hPt⟩ := hP _ (mem_zpowers _)
  have hts : P⁻¹ * (t : GL (Fin 4) F) * P ∈ signDiag4 F :=
    mem_signDiag4_of_frame hμ hPt ((mem_su_iff h _).1 t.2).1
  refine ⟨((signDiag4 F).map (MulAut.conj P).toMonoidHom).comap (StatedSU 4 (p ^ f) F).subtype,
    isE8_comap _ (Subgroup.subtype_injective _) h2 P (conj_mem_su h P hPU), ?_⟩
  refine ⟨P⁻¹ * (t : GL (Fin 4) F) * P, hts, ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, Subgroup.coe_subtype]
  group

theorem diag_normalize (h : UnitaryFieldData p f F) (hp2 : p ≠ 2)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) {A : GL (Fin 4) F}
    (hAu : cT h (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1)
    (hαA : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = A * (k : GL (Fin 4) F) * A⁻¹)
    {c : F} (hc0 : c ≠ 0) (hAA : (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = c • 1) :
    ∃ Bm : Matrix (Fin 4) (Fin 4) F, Bm * Bm = 1 ∧ (cT h Bm * Bm = 1 ∨ cT h Bm * Bm = -1) ∧
      ∀ k : ↥(StatedSU 4 (p ^ f) F),
        (((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
          Bm * ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm := by
  classical
  set Ar : Matrix (Fin 4) (Fin 4) F := (A : Matrix (Fin 4) (Fin 4) F) with hAr
  have hcN : h.norm c = 1 := norm_eq_one_of_sq h hAu hAA
  obtain ⟨l, hl0, hlc⟩ := exists_sq_eq_of_norm_eq_one h hp2 hcN
  have hlN : h.norm l = 1 ∨ h.norm l = -1 := by
    have h1 : h.norm l * h.norm l = 1 := by
      rw [← norm_mul_eq', ← pow_two, hlc, hcN]
    exact mul_self_eq_one_iff.mp h1
  set Bm : Matrix (Fin 4) (Fin 4) F := l⁻¹ • Ar with hBm
  have hBB : Bm * Bm = 1 := by
    rw [hBm, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hAA, smul_smul]
    have : l⁻¹ * l⁻¹ * c = 1 := by
      rw [← hlc]
      field_simp
    rw [this, one_smul]
  have hBu := cT_mul_smul h hAu hl0
  have hAinv : ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = c⁻¹ • Ar := by
    have h1 : (c⁻¹ • Ar) * Ar = 1 := by
      rw [Matrix.smul_mul, hAA, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    exact Units.inv_eq_of_mul_eq_one_left h1
  have hαB : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      (((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Bm * ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm := by
    intro k
    rw [hαA k, Units.val_mul, Units.val_mul, hAinv, hBm, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← hAr]
    congr 1
    rw [← hlc]
    field_simp
  refine ⟨Bm, hBB, ?_, hαB⟩
  rcases hlN with hl1 | hl1
  · left
    rw [hBu, hl1, inv_one, one_smul]
  · right
    rw [hBu, hl1, inv_neg, inv_one, neg_one_smul]

theorem fix_paired (h : UnitaryFieldData p f F) {α : MulAut ↥(StatedSU 4 (p ^ f) F)}
    {Bm : Matrix (Fin 4) (Fin 4) F} (hBB : Bm * Bm = 1)
    (hα : ∀ k : ↥(StatedSU 4 (p ^ f) F),
      (((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        Bm * ((k : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm)
    {P : GL (Fin 4) F} (hP1 : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (hP2 : Bm * (P : Matrix (Fin 4) (Fin 4) F) =
      (P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1)) :
    ∀ X : SpecialLinearGroup (Fin 2) F, α (iotaHom h hP1 X) = iotaHom h hP1 X := by
  have hPPi : (P : Matrix (Fin 4) (Fin 4) F) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  set D : Matrix (Fin 4) (Fin 4) F := blk4 (1 : Matrix (Fin 2) (Fin 2) F) (-1) with hD
  have hBPi : ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm =
      D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
    calc ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Bm
        = ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (Bm * ((P : Matrix (Fin 4) (Fin 4) F) *
          ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))) := by rw [hPPi, Matrix.mul_one]
      _ = D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
        rw [← Matrix.mul_assoc Bm, hP2]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc _ (P : Matrix (Fin 4) (Fin 4) F), hPiP, Matrix.one_mul]
  intro X
  apply Subtype.ext
  apply Units.ext
  rw [hα, iotaHom_val, Units.val_mul, Units.val_mul]
  set Lm : Matrix (Fin 4) (Fin 4) F := ((leviHom h X : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    with hLm
  have hDL : D * Lm = Lm * D := by
    rw [hD, hLm, levi_val, blk4_mul, blk4_mul]
    simp
  have hcomm : Bm * ((P : Matrix (Fin 4) (Fin 4) F) * Lm *
      ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) =
      ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Bm := by
    calc Bm * ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
        = (Bm * (P : Matrix (Fin 4) (Fin 4) F)) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin 4) (Fin 4) F) * (D * Lm) * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) := by
          rw [hP2]; simp only [Matrix.mul_assoc]
      _ = (P : Matrix (Fin 4) (Fin 4) F) * Lm * (D * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
          rw [hDL]; simp only [Matrix.mul_assoc]
      _ = ((P : Matrix (Fin 4) (Fin 4) F) * Lm * ((P⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) * Bm := by
          rw [← hBPi]; simp only [Matrix.mul_assoc]
  rw [hcomm, Matrix.mul_assoc _ Bm Bm, hBB, Matrix.mul_one]

theorem fix_adapted (h : UnitaryFieldData p f F) {α : MulAut ↥(StatedSU 4 (p ^ f) F)} {g : GL (Fin 4) F}
    {ε s : F} (hε : ε = 1 ∨ ε = -1) (hs : s ≠ 0)
    (hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹)
    {P : GL (Fin 4) F}
    (hP : cT h (P : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F) = wMat)
    (hgP : (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar =
      s • ((P : Matrix (Fin 4) (Fin 4) F) * blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1))) :
    ∀ X : SpecialLinearGroup (Fin 2) h.fixedField,
      α (((iotaHom h hP).comp (SpecialLinearGroup.map h.fixedField.subtype)) X) =
        ((iotaHom h hP).comp (SpecialLinearGroup.map h.fixedField.subtype)) X := by
  classical
  let K₀ := h.fixedField
  let ι : K₀ →+* F := K₀.subtype
  have hεε : ε * ε = 1 := by rcases hε with h1 | h1 <;> rw [h1] <;> norm_num
  let D : Matrix (Fin 4) (Fin 4) F := blk4 (1 : Matrix (Fin 2) (Fin 2) F) (ε • 1)
  have hDD : D * D = 1 := by
    simp only [D]
    rw [blk4_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one, hεε,
      one_smul, blk4_one]
  let Dgl : GL (Fin 4) F := ⟨D, D, hDD, hDD⟩
  let sc : GL (Fin 4) F := Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 s hs)
  have hgPGL : g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P = sc * (P * Dgl) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul]
    change (g : Matrix (Fin 4) (Fin 4) F) * (P : Matrix (Fin 4) (Fin 4) F).map h.bar = _
    rw [hgP, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
    rfl
  intro X
  let Y : SpecialLinearGroup (Fin 2) F := SpecialLinearGroup.map ι X
  have hY : (Y : Matrix (Fin 2) (Fin 2) F).map h.bar = Y := by
    have : (Y : Matrix (Fin 2) (Fin 2) F) = (X : Matrix (Fin 2) (Fin 2) K₀).map ι := rfl
    rw [this]
    exact map_fixedField_bar h _
  have hLbar := levi_bar_fixed h Y hY
  have hLb : Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (leviHom h Y) = leviHom h Y :=
    Units.ext hLbar
  apply Subtype.ext
  rw [hαg]
  change g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (P * leviHom h Y * P⁻¹) * g⁻¹ =
    P * leviHom h Y * P⁻¹
  rw [map_mul, map_mul, map_inv, hLb]
  have e1 : g * (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P * leviHom h Y *
      (Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P)⁻¹) * g⁻¹ =
      (g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P) * leviHom h Y *
        (g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) P)⁻¹ := by group
  rw [e1, hgPGL]
  have hDL : Dgl * leviHom h Y = leviHom h Y * Dgl := Units.ext (blk4_comm_levi h ε Y)
  have e2 : (sc * (P * Dgl)) * leviHom h Y * (sc * (P * Dgl))⁻¹ =
      sc * (P * (Dgl * leviHom h Y * Dgl⁻¹) * P⁻¹) * sc⁻¹ := by group
  have e3 : Dgl * leviHom h Y * Dgl⁻¹ = leviHom h Y := by rw [hDL, mul_inv_cancel_right]
  rw [e2, e3, Matrix.GeneralLinearGroup.scalar_commute (Units.mk0 s hs) _, mul_inv_cancel_right]

theorem fix_graph_sym (h : UnitaryFieldData p f F) {α : MulAut ↥(StatedSU 4 (p ^ f) F)}
    {g U : GL (Fin 4) F} {δ : Fin 4 → F}
    (hα : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
      g * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * g⁻¹)
    (hU : cT h (U : Matrix (Fin 4) (Fin 4) F) * (U : Matrix (Fin 4) (Fin 4) F) = 1)
    (hgU : (g : Matrix (Fin 4) (Fin 4) F) = (U : Matrix (Fin 4) (Fin 4) F) * diagonal δ *
      (U : Matrix (Fin 4) (Fin 4) F)ᵀ) :
    ∀ k ∈ ((signDiag4 F).map (MulAut.conj U).toMonoidHom).comap (StatedSU 4 (p ^ f) F).subtype,
      α k = k := by
  intro k hk
  obtain ⟨s, hsD, hsk⟩ := hk
  obtain ⟨ε, ⟨hε, -⟩, hs⟩ := hsD
  have hsk' : (k : GL (Fin 4) F) = U * s * U⁻¹ := hsk.symm
  set Um : Matrix (Fin 4) (Fin 4) F := (U : Matrix (Fin 4) (Fin 4) F) with hUm
  have hUi : ((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = cT h Um := coe_inv_of_unitary h hU
  have hUiU : ((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Um = 1 := by
    rw [hUm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hTU : Umᵀ * Um.map h.bar = 1 := by
    have := congrArg Matrix.transpose hU
    rwa [cT_def, transpose_mul, transpose_transpose, transpose_one] at this
  have hbarUi : (((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).map h.bar = Umᵀ := by
    rw [hUi, cT_def, Matrix.transpose_map, Matrix.map_map]
    rw [show (h.bar ∘ h.bar : F → F) = id from funext fun c => h.bar_bar c, Matrix.map_id]
  have hbars : (diagonal ε).map h.bar = diagonal ε := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact bar_sign h (hε i)
  have hDs : diagonal δ * diagonal ε = diagonal ε * diagonal δ := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  apply Subtype.ext
  rw [hα, mul_inv_eq_iff_eq_mul, hsk']
  apply Units.ext
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul,
    Units.val_mul, Units.val_mul]
  change (g : Matrix (Fin 4) (Fin 4) F) * (Um.map h.bar * ((s : Matrix (Fin 4) (Fin 4) F).map h.bar) *
      (((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)).map h.bar) =
    Um * (s : Matrix (Fin 4) (Fin 4) F) * ((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      (g : Matrix (Fin 4) (Fin 4) F)
  rw [hbarUi, hs, hbars, hgU]
  calc Um * diagonal δ * Umᵀ * (Um.map h.bar * diagonal ε * Umᵀ)
      = Um * diagonal δ * (Umᵀ * Um.map h.bar) * diagonal ε * Umᵀ := by simp only [Matrix.mul_assoc]
    _ = Um * (diagonal δ * diagonal ε) * Umᵀ := by rw [hTU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Um * (diagonal ε * diagonal δ) * Umᵀ := by rw [hDs]
    _ = Um * diagonal ε * (((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * Um) * diagonal δ * Umᵀ := by
        rw [hUiU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = Um * diagonal ε * ((U⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (Um * diagonal δ * Umᵀ) := by simp only [Matrix.mul_assoc]

theorem card_ge_four (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) : 4 ≤ Nat.card F := by
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  have h3 : 3 ≤ p := by have := h.prime.two_le; omega
  have hq3 : 3 ≤ p ^ f := le_trans h3 (Nat.le_self_pow (by have := h.one_le; omega) p)
  rw [hF]
  nlinarith

theorem dich_uni (h : UnitaryFieldData p f F) (hp2 : p ≠ 2) (hq4 : p ^ f % 4 = 1)
    (α : MulAut ↥(StatedSU 4 (p ^ f) F)) (hα : α * α = 1) :
    (∃ E : Subgroup ↥(StatedSU 4 (p ^ f) F), IsE8 E ∧ ∀ e ∈ E, α e = e) ∨
      GoodFixedQ8 (ThreeModel ↥(StatedSU 4 (p ^ f) F)) α := by
  classical
  have hfin : Finite F := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have hF : Nat.card F = (p ^ f) ^ 2 := h.card_eq_sq
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd h hp2
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero h2
  have hneg1 : xGL F ≠ 1 := by
    intro h1
    have h' := congrArg (fun g : GL (Fin 4) F => (g : Matrix (Fin 4) (Fin 4) F) 0 0) h1
    simp only [xGL_eq_neg_one, Units.val_neg, Units.val_one] at h'
    apply h2
    have : (-1 : Matrix (Fin 4) (Fin 4) F) 0 0 = -1 := by simp
    rw [this, Matrix.one_apply_eq] at h'
    linear_combination (-1 : F) * h'
  have hU1 : cT h ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * ((1 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [Units.val_one, cT_one, Matrix.one_mul]
  by_cases hα1 : α = 1
  · left
    exact ⟨_, isE8_comap _ (Subgroup.subtype_injective _) h2 1 (conj_mem_su h 1 hU1),
      fun e _ => by rw [hα1]; rfl⟩
  obtain ⟨A, σ, hσ, hAu, hαA, hid, hbar⟩ := aut_form_uni h hp2 α hα hα1
  have hAu' : cT h (A : Matrix (Fin 4) (Fin 4) F) * (A : Matrix (Fin 4) (Fin 4) F) = 1 := hAu
  rcases hσ with rfl | hσb
  ·
    obtain ⟨c, hc0, hAA⟩ := hid rfl
    have hαA' : ∀ k : ↥(StatedSU 4 (p ^ f) F),
        ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = A * (k : GL (Fin 4) F) * A⁻¹ :=
      fun k => by rw [hαA k, glAut_refl_apply]
    obtain ⟨Bm, hBB, hBu, hαB⟩ := diag_normalize h hp2 α hAu' hαA' hc0 hAA
    rcases hBu with hBu | hBu
    ·
      left
      set Bg : GL (Fin 4) F := ⟨Bm, Bm, hBB, hBB⟩ with hBg
      have hBgi : Bg⁻¹ = Bg := inv_eq_of_mul_eq_one_right (Units.ext hBB)
      have hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F),
          ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = Bg * (k : GL (Fin 4) F) * Bg⁻¹ := by
        intro k
        rw [hBgi]
        exact Units.ext (hαB k)
      set W : Subgroup (GL (Fin 4) F) := zpowers Bg with hW
      have hBgBg : Bg * Bg = 1 := Units.ext hBB
      have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
        intro x hx y hy
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        exact (Commute.zpow_zpow_self _ m n).eq
      have hsq : ∀ x ∈ W, x * x = 1 := by
        intro x hx
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← _root_.zpow_add, ← two_mul, _root_.zpow_mul, show Bg ^ (2 : ℤ) = 1 by
          rw [_root_.zpow_two, hBgBg], _root_.one_zpow]
      have hEU : ∀ x ∈ W, cT h (x : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
        intro x hx
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
        rcases Int.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · rw [show Bg ^ (j + j) = 1 by
            rw [← two_mul, _root_.zpow_mul, _root_.zpow_two, hBgBg, _root_.one_zpow]]
          exact hU1
        · rw [show Bg ^ (2 * j + 1) = Bg by
            rw [_root_.zpow_add, _root_.zpow_mul, _root_.zpow_two, hBgBg, _root_.one_zpow, one_mul,
              zpow_one]]
          exact hBu
      obtain ⟨P, hPU, hP⟩ := unitary_frame h hp2 W hEU hcomm hsq
      obtain ⟨μ, -, hPB⟩ := hP Bg (mem_zpowers Bg)
      exact ⟨_, isE8_comap _ (Subgroup.subtype_injective _) h2 P (conj_mem_su h P hPU),
        fix_of_conj_gen hαg hPB⟩
    ·
      right
      obtain ⟨P, hP1, hP2⟩ := exists_paired_basis h hp2 hBB hBu
      refine goodFixedQ8_of_sl2 (card_ge_four h hp2) hF2 α (iotaHom h hP1)
        (fix_paired h hBB hαB hP1 hP2) ?_ ?_
      · rw [mem_center_statedSU_four_iff hF hq4]
        right
        exact iotaHom_of_neg_one h hP1 (-1) (by simp)
      · intro h1
        apply hneg1
        rw [← iotaHom_of_neg_one h hP1 (-1) (by simp), h1]
        rfl
  ·
    obtain ⟨c, hc0, hAA⟩ := hbar hσb
    have hαg : ∀ k : ↥(StatedSU 4 (p ^ f) F), ((α k : ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) =
        A * Matrix.GeneralLinearGroup.map (h.bar : F →+* F) (k : GL (Fin 4) F) * A⁻¹ := by
      intro k
      rw [hαA k]
      congr 2
      apply Units.ext
      ext i j
      simp [coe_glAut, hσb]
    obtain ⟨g', ε, hε, hu', hgg', hsym, hαg'⟩ := normalize_graph h hp2 hq4 α hAA hαg
    rcases hε with rfl | rfl
    ·
      left
      have hsym' : (g' : Matrix (Fin 4) (Fin 4) F)ᵀ = g' := by rw [hsym, one_smul]
      obtain ⟨Um, δ, hUU, -, hgU⟩ := GenLocU4OutFrame.exists_sym_nf h hp2 hsym' hu'
      have hUU' : Um * cT h Um = 1 := mul_eq_one_comm.1 hUU
      set U : GL (Fin 4) F := ⟨Um, cT h Um, hUU', hUU⟩ with hUdef
      exact ⟨_, isE8_comap _ (Subgroup.subtype_injective _) h2 U (conj_mem_su h U hUU),
        fix_graph_sym h hαg' hUU hgU⟩
    ·
      right
      obtain ⟨P, s, hs, hP1, hP2⟩ := adapted_skew h hp2 hu' hgg'
      have hK4 : 4 ≤ Nat.card h.fixedField := by
        rw [h.card_fixedField]
        have h3 : 3 ≤ p := by have := h.prime.two_le; omega
        have hq3 : 3 ≤ p ^ f := le_trans h3 (Nat.le_self_pow (by have := h.one_le; omega) p)
        omega
      have hK2 : ringChar h.fixedField ≠ 2 := by
        apply ringChar_ne_two_of_two_ne_zero
        intro h0
        apply h2
        have := congrArg h.fixedField.subtype h0
        rw [map_ofNat, map_zero] at this
        exact this
      refine goodFixedQ8_of_sl2 hK4 hK2 α ((iotaHom h hP1).comp
        (SpecialLinearGroup.map h.fixedField.subtype))
        (fix_adapted h (Or.inr rfl) hs hαg' hP1 hP2) ?_ ?_
      · rw [mem_center_statedSU_four_iff hF hq4]
        right
        apply iotaHom_of_neg_one h hP1
        show (-1 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype = -1
        ext i j
        simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
        split_ifs <;> simp
      · intro h1
        apply hneg1
        have h3 : ((iotaHom h hP1 (SpecialLinearGroup.map h.fixedField.subtype (-1)) :
            ↥(StatedSU 4 (p ^ f) F)) : GL (Fin 4) F) = xGL F := by
          apply iotaHom_of_neg_one h hP1
          show (-1 : Matrix (Fin 2) (Fin 2) h.fixedField).map h.fixedField.subtype = -1
          ext i j
          simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply]
          split_ifs <;> simp
        rw [← h3]
        have := congrArg (fun z : ↥(StatedSU 4 (p ^ f) F) => (z : GL (Fin 4) F)) h1
        exact this

end Uni

theorem s1Facts_uni {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 4 = 1) : S1Facts ↥(StatedSU 4 q F) := by
  have hc := Uni.center_uni hF hq
  obtain ⟨p, f, h, rfl, hp2⟩ := S1.exists_unitaryFieldData hF hq
  exact ⟨hc, Uni.conj_uni h hp2, Uni.invol_uni h hp2, Uni.dich_uni h hp2 hq⟩


end CFSG.GH74.Generic.BProg.B2.T3S1

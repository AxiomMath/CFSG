module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.CommutingPair
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Perm
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.Basic
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus
public import CFSG.RankThree.Classical.SteinbergBTUnitarySubfield
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Timmesfeld.FieldBonus

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.HardMathSupport.Timmesfeld.Tables.Census
open CFSG.SectionRank.ClassicalEven (torusDiag torusDiag_mem_SU coe_torusDiag scalar_eq_torusDiag
  torusDiag_injective)

variable {f : ℕ} {K : Type} [Field K]

abbrev S3 (h : UnitaryFieldData 2 f K) : Type :=
  ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))

abbrev Z3 (h : UnitaryFieldData 2 f K) : Subgroup (S3 h) :=
  normOneScalars h (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3

theorem mem_gramSU_of_unitarySU (h : UnitaryFieldData 2 f K) {A : GL (Fin 3) K}
    (hA : A ∈ unitarySU 2 f K 3) :
    A ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
  have h1 := unitarySU_eq_gramSU h 3
  rw [h1] at hA
  exact hA

@[expose] noncomputable def dS (h : UnitaryFieldData 2 f K) (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (hdq : d ^ (2 ^ f + 1) = 1) : S3 h :=
  ⟨torusDiag d, mem_gramSU_of_unitarySU h
    (torusDiag_mem_SU (pow_pos (by norm_num) f).ne' hd hdq)⟩

theorem coe_dS (h : UnitaryFieldData 2 f K) (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (hdq : d ^ (2 ^ f + 1) = 1) : ((dS h d hd hdq : S3 h) : GL (Fin 3) K) = torusDiag d := rfl

theorem permGL_mem_unitarySU (h : UnitaryFieldData 2 f K) (σ : Equiv.Perm (Fin 3)) :
    permGL 3 K σ ∈ unitarySU 2 f K 3 := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · rw [det_permGL]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
    · rw [h1]; simp
    · rw [h1]; simp [CharTwo.neg_eq]
  · rw [coe_permGL]
    have h1 : ((σ⁻¹.permMatrix K).map h.bar) = σ⁻¹.permMatrix K := by
      ext i j
      simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
      split_ifs <;> simp
    rw [h1, transpose_permMatrix, ← permMatrix_mul]
    simp

@[expose] noncomputable def tS (h : UnitaryFieldData 2 f K) : S3 h :=
  ⟨permGL 3 K (Equiv.swap 0 1), mem_gramSU_of_unitarySU h (permGL_mem_unitarySU h _)⟩

theorem tS_sq (h : UnitaryFieldData 2 f K) : tS h ^ 2 = 1 := by
  apply Subtype.ext
  show (permGL 3 K (Equiv.swap 0 1)) ^ 2 = 1
  rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]

theorem tS_ne_one (h : UnitaryFieldData 2 f K) : tS h ≠ 1 := by
  intro h1
  have := congrArg (fun g : S3 h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
  simp [tS, coe_permGL, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply] at this

section Fixed

variable (h : UnitaryFieldData 2 f K) (hC : IsPrimeFormGram (1 : GL (Fin 3) K))

theorem fieldSU_apply (σ : K ≃+* K) (g : S3 h) :
    ((primeFormFieldSU h hC σ g : S3 h) : GL (Fin 3) K) = glAut σ (g : GL (Fin 3) K) := rfl

theorem fieldSU_dS (σ : K ≃+* K) (d : Fin 3 → Kˣ) (hd : ∏ i, d i = 1)
    (hdq : d ^ (2 ^ f + 1) = 1) (hσ : ∀ i, σ (d i : K) = d i) :
    primeFormFieldSU h hC σ (dS h d hd hdq) = dS h d hd hdq := by
  apply Subtype.ext
  rw [fieldSU_apply, coe_dS]
  apply Units.ext
  rw [coe_glAut, coe_torusDiag, diagonal_map (map_zero σ)]
  congr 1
  funext i
  exact hσ i

theorem fieldSU_tS (σ : K ≃+* K) : primeFormFieldSU h hC σ (tS h) = tS h := by
  apply Subtype.ext
  rw [fieldSU_apply]
  apply Units.ext
  rw [coe_glAut]
  show ((Equiv.swap (0 : Fin 3) 1)⁻¹.permMatrix K).map σ = (Equiv.swap (0 : Fin 3) 1)⁻¹.permMatrix K
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem three_dvd_two_pow_add_one {f : ℕ} (hf : Odd f) : 3 ∣ 2 ^ f + 1 := by
  obtain ⟨k, rfl⟩ := hf
  have h1 : 2 ^ (2 * k + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * k + 1) = N at h1 ⊢
  omega

include h in
theorem exists_fixed_cube_root (hf : Odd f) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ (2 ^ f + 1) = 1 ∧ σ (ω : K) = ω := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfin := h.finite
  have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h Nat.prime_three
    (by norm_num) hσ
  have hfin₀ : Finite (CFSG.LieType.Chevalley.fixSubfield σ) := inferInstance
  have hcard := h₀.card
  have h3 : 3 ∣ Nat.card (CFSG.LieType.Chevalley.fixSubfield σ)ˣ := by
    rw [Nat.card_units, hcard]
    have : 2 ^ (2 * (f / 3)) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    have h1 : 1 ≤ 2 ^ (2 * (f / 3)) := Nat.one_le_two_pow
    omega
  obtain ⟨ω₀, hω₀⟩ :=
    exists_prime_orderOf_dvd_card' (G := (CFSG.LieType.Chevalley.fixSubfield σ)ˣ) 3 h3
  refine ⟨Units.map (CFSG.LieType.Chevalley.fixSubfield σ).subtype.toMonoidHom ω₀, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, ← hω₀, pow_orderOf_eq_one, map_one]
  · intro h1
    have h2 : ω₀ = 1 := Units.map_injective (CFSG.LieType.Chevalley.fixSubfield σ).subtype.injective
      (by rw [h1, map_one])
    rw [h2, orderOf_one] at hω₀
    omega
  · obtain ⟨m, hm⟩ := three_dvd_two_pow_add_one hf
    rw [hm, pow_mul, ← map_pow, ← hω₀, pow_orderOf_eq_one, map_one, one_pow]
  · exact ω₀.1.2

@[expose] noncomputable def zS (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ f + 1) = 1) : S3 h :=
  dS h (fun _ => ω) (by rw [Fin.prod_univ_three, ← pow_three', hω3])
    (by funext i; simp [hωq])

@[expose] noncomputable def aS (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ f + 1) = 1) : S3 h :=
  dS h ![1, ω, ω ^ 2]
    (by simp only [Fin.prod_univ_three]; simp; rw [← pow_succ']; exact hω3)
    (by funext i; fin_cases i <;> simp [hωq] <;> rw [← pow_mul, mul_comm, pow_mul, hωq, one_pow])

theorem zS_pow_three (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ f + 1) = 1) :
    zS h ω hω3 hωq ^ 3 = 1 := by
  apply Subtype.ext
  show torusDiag (fun _ : Fin 3 => ω) ^ 3 = 1
  rw [← map_pow, ← map_one (torusDiag (ι := Fin 3) (K := K))]
  congr 1
  funext i
  simp [hω3]

theorem aS_pow_three (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ f + 1) = 1) :
    aS h ω hω3 hωq ^ 3 = 1 := by
  apply Subtype.ext
  show torusDiag ![1, ω, ω ^ 2] ^ 3 = 1
  rw [← map_pow, ← map_one (torusDiag (ι := Fin 3) (K := K))]
  congr 1
  funext i
  fin_cases i <;> simp [hω3] <;> rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]

theorem zS_comm (ω : Kˣ) (hω3 : ω ^ 3 = 1) (hωq : ω ^ (2 ^ f + 1) = 1) :
    zS h ω hω3 hωq * aS h ω hω3 hωq = aS h ω hω3 hωq * zS h ω hω3 hωq := by
  apply Subtype.ext
  exact ((Commute.all _ _).map (torusDiag (ι := Fin 3) (K := K))).eq

theorem zmod3_pow_three : ∀ b : Multiplicative (ZMod 3 × ZMod 3), b ^ 3 = 1 := by decide

theorem isElemAbelian_range_of_comm_pow {p : ℕ} {A G : Type*} [Group A] [Group G]
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) (g : A →* G) :
    IsElemAbelian p g.range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]

theorem card_range_pairHom {X : Type*} [Group X] (A B : X) (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A)
    (hind : ∀ i j : ℕ, i < 3 → j < 3 → A ^ i * B ^ j = 1 → i = 0 ∧ j = 0) :
    Nat.card (pairHom A B hA hB hAB).range = 9 := by
  have hinj : Function.Injective (pairHom A B hA hB hAB) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    induction x using Multiplicative.rec with
    | ofAdd x =>
      obtain ⟨a, b⟩ := x
      have h := hind a.val b.val (ZMod.val_lt a) (ZMod.val_lt b) hx
      have ha : a = 0 := (ZMod.val_eq_zero a).1 h.1
      have hb : b = 0 := (ZMod.val_eq_zero b).1 h.2
      rw [ha, hb]
      rfl
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_prod, Nat.card_zmod]

theorem fbCore_fieldSU [Finite K] (hf : Odd f) (hm : CFSG.Open.pRank 3 (⊤ : Subgroup (S3 h)) = 2)
    (hw : GLATwoLocalRank 3 (S3 h) = 1) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    FBCore (S3 h) 3 (primeFormFieldSU h hC σ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω3, hω1, hωq, hσω⟩ := exists_fixed_cube_root h hf hσ
  set ψ := primeFormFieldSU h hC σ with hψ
  set z := zS h ω hω3 hωq with hz
  set a := aS h ω hω3 hωq with ha
  have hzfix : ψ z = z :=
    fieldSU_dS h hC σ _ _ _ (fun i => hσω)
  have hafix : ψ a = a := by
    refine fieldSU_dS h hC σ _ _ _ (fun i => ?_)
    fin_cases i
    · simp
    · simpa using hσω
    · simp [hσω]
  have hz3 : z ^ 3 = 1 := zS_pow_three h ω hω3 hωq
  have ha3 : a ^ 3 = 1 := aS_pow_three h ω hω3 hωq
  have hcomm : z * a = a * z := zS_comm h ω hω3 hωq
  have hz1 : z ≠ 1 := by
    intro h1
    have := congrArg (fun g : S3 h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp [hz, zS, coe_dS, coe_torusDiag] at this
    exact hω1 this
  have hzord : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have hω3' : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have hzc : z ∈ Subgroup.center (S3 h) := by
    refine normOneScalars_le_center h _ 3 ⟨ω, ?_, hω3, ?_⟩
    · rw [h.norm_eq_pow, ← Units.val_pow_eq_pow_val, hωq, Units.val_one]
    · exact (scalar_eq_torusDiag ω).symm
  let T : Subgroup (S3 h) := Subgroup.zpowers (tS h)
  refine ⟨T, ?_, ?_, ?_, Subgroup.zpowers z,
    (CFSG.HardMathSupport.Timmesfeld.Tables.Census.pairHom z a hz3 ha3 hcomm).range,
    ⟨inferInstance, ?_⟩, isElemAbelian_range_of_comm_pow (p := 3)
      (A := Multiplicative (ZMod 3 × ZMod 3)) ?_ ?_ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro hT
    apply tS_ne_one h
    have : tS h ∈ T := Subgroup.mem_zpowers _
    rw [hT] at this
    exact this
  · intro x
    obtain ⟨y, k, rfl⟩ := x
    refine ⟨1, Subtype.ext ?_⟩
    show (tS h ^ k) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      tS_sq, _root_.one_zpow]
  · show (Subgroup.zpowers (tS h)).map (ψ : S3 h →* S3 h) = Subgroup.zpowers (tS h)
    rw [MonoidHom.map_zpowers]
    show Subgroup.zpowers (ψ (tS h)) = _
    rw [hψ, fieldSU_tS]
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hz3,
      _root_.one_zpow]
  · intro a b
    exact mul_comm a b
  · exact zmod3_pow_three
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_iff.2 (fun y => ?_)
    have hcen : z * y * z⁻¹ = y := by
      rw [← Subgroup.mem_center_iff.1 hzc y, mul_inv_cancel_right]
    rw [hcen]
  · rw [Nat.card_zpowers, hzord, hw, pow_one]
  · have hind : ∀ i j : ℕ, i < 3 → j < 3 → z ^ i * a ^ j = 1 → i = 0 ∧ j = 0 := by
      intro i j hi hj hij
      have h1 := congrArg (fun g : S3 h => (g : GL (Fin 3) K)) hij
      simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one] at h1
      have h2 : torusDiag ((fun _ : Fin 3 => ω) ^ i * ![1, ω, ω ^ 2] ^ j) =
          torusDiag (1 : Fin 3 → Kˣ) := by
        rw [map_mul, map_pow, map_pow, map_one]
        exact h1
      have h3 := congrFun (torusDiag_injective h2)
      have e0 := h3 0
      have e1 := h3 1
      simp at e0 e1
      have hωi : ω ^ i = 1 := e0
      have hωj : ω ^ j = 1 := by
        rw [hωi, one_mul] at e1
        exact e1
      have hdi : 3 ∣ i := hω3' ▸ orderOf_dvd_of_pow_eq_one hωi
      have hdj : 3 ∣ j := hω3' ▸ orderOf_dvd_of_pow_eq_one hωj
      omega
    rw [card_range_pairHom z a hz3 ha3 hcomm hind, hm]
    norm_num
  · intro e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [map_zpow, hzfix]
  · intro e he
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 he
    induction x using Multiplicative.rec with
    | ofAdd x =>
      obtain ⟨i, j⟩ := x
      show ψ (pairHom z a hz3 ha3 hcomm (Multiplicative.ofAdd (i, j))) = _
      rw [pairHom_apply, map_mul, map_pow, map_pow, hzfix, hafix]

end Fixed

section Induced

variable (h : UnitaryFieldData 2 f K)

@[expose] noncomputable def eP (hZ : Z3 h = Subgroup.center (S3 h)) :
    primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≃*
      (S3 h ⧸ Subgroup.center (S3 h)) :=
  QuotientGroup.quotientMulEquivOfEq hZ

@[expose] noncomputable def PhiAut (hZ : Z3 h = Subgroup.center (S3 h)) :
    MulAut (S3 h) →* MulAut (primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
  (MulAut.congr (eP h hZ).symm).toMonoidHom.comp
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (S3 h))

theorem PhiAut_mk (hZ : Z3 h = Subgroup.center (S3 h)) (ψ : MulAut (S3 h)) (g : S3 h) :
    PhiAut h hZ ψ (g : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      ((ψ g : S3 h) : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
  show (eP h hZ).symm (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient ψ
    (eP h hZ (g : primeFormP h _))) = _
  have h1 : eP h hZ (g : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      (QuotientGroup.mk' (Subgroup.center (S3 h)) g) := QuotientGroup.quotientMulEquivOfEq_mk _ _
  rw [h1, CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  exact (eP h hZ).symm_apply_eq.2 (QuotientGroup.quotientMulEquivOfEq_mk _ _).symm

end Induced

end CFSG.HardMathSupport.Timmesfeld.FieldBonus

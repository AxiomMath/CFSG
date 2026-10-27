module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniCover
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZLin3Data
import CFSG.RankThree.PartOne.Q1327C.BU5Diag
import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CTrans
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniNine
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ZUniZ3Data

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

variable {ℓ f : ℕ} {K : Type} [Field K]

private theorem mulAut_congr_inv_apply {M : Type} [Group M] (e γ : MulAut M) :
    MulAut.congr e⁻¹ γ = e⁻¹ * γ * e :=
  MulEquiv.ext fun _ => rfl

private theorem z3Data_of_map {p : ℕ} (hp : p.Prime) {M : Type} [Group M] [Finite M] (e : MulAut M)
    {E : Subgroup (MulAut M)} (hE : Z3Data p M (E.map (MulAut.congr e⁻¹).toMonoidHom)) :
    Z3Data p M E := by
  have hid : (MulAut.congr e).toMonoidHom.comp (MulAut.congr e⁻¹).toMonoidHom =
      MonoidHom.id _ := by
    ext γ x
    change e (e⁻¹ (γ (e (e⁻¹ x)))) = γ x
    simp
  have := CFSG.LocalAnalysis.GLTheoremA.S267Z.z3Data_congr hp e hE
  rwa [Subgroup.map_map, hid, Subgroup.map_id] at this

section Frame

variable [Finite K]

theorem mul_map_conjUHom_eq_smul {h : UnitaryFieldData ℓ f K} (σ : K ≃+* K) (P : UG h)
    {a : SG h} {c : Kˣ}
    (hc : ((fieldUHom h σ a : SG h) : GL (Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 3) c * (a : GL (Fin 3) K)) :
    (((P : GL (Fin 3) K)⁻¹ * glAut σ (P : GL (Fin 3) K) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *
        (((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      (c : K) • ((((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        (((P : GL (Fin 3) K)⁻¹ * glAut σ (P : GL (Fin 3) K) : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) := by
  set s := Matrix.GeneralLinearGroup.scalar (Fin 3) c with hsdef
  have ha : glAut σ (a : GL (Fin 3) K) = s * (a : GL (Fin 3) K) := hc
  have hs : ((P : GL (Fin 3) K))⁻¹ * s = s * ((P : GL (Fin 3) K))⁻¹ :=
    (commute_scalar c ((P : GL (Fin 3) K))⁻¹).eq
  have hgl : ((P : GL (Fin 3) K)⁻¹ * glAut σ (P : GL (Fin 3) K) : GL (Fin 3) K) *
      glAut σ ((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) =
        s * (((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) *
          ((P : GL (Fin 3) K)⁻¹ * glAut σ (P : GL (Fin 3) K) : GL (Fin 3) K)) := by
    rw [coe_conjUHom_apply, Subgroup.coe_inv, inv_inv, map_mul, map_mul, map_inv, ha]
    calc _ = ((P : GL (Fin 3) K))⁻¹ * s * (a : GL (Fin 3) K) * glAut σ (P : GL (Fin 3) K) := by
          group
      _ = s * ((P : GL (Fin 3) K))⁻¹ * (a : GL (Fin 3) K) * glAut σ (P : GL (Fin 3) K) := by
          rw [hs]
      _ = _ := by group
  have e := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hgl
  simpa only [Units.val_mul, coe_glAut, hsdef, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
    ← smul_eq_diagonal_mul, Matrix.mul_assoc] using e

private theorem inv_mul_mul_eq_of_isDiag {T Y : GL (Fin 3) K}
    (hT : ((T : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hY : ((Y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag) : Y⁻¹ * T * Y = T := by
  have hc : T * Y = Y * T := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hT.diagonal_diag, ← hY.diagonal_diag,
      diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_frame (h : UnitaryFieldData ℓ f K) {σ : K ≃+* K} (hσ : orderOf σ = 3) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ f₀) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ f₀)) (hpQ : 3 ∣ ℓ ^ f₀ + 1) {lam : K}
    (hlamn : h.bar lam * lam = 1) (hlam : IsPrimitiveRoot lam 9) {AM : Subgroup (SG h)}
    (hAMc : ∀ a ∈ AM, ∀ b ∈ AM, a * b = b * a)
    (hAM3 : ∀ a ∈ AM, a ^ 3 ∈ normOneScalars h (SG h) 3) (hcard : 27 ≤ Nat.card AM)
    (hAMσ : ∀ a ∈ AM, fieldUHom h σ a * a⁻¹ ∈ normOneScalars h (SG h) 3) :
    ∃ Q : UG h, glAut σ (Q : GL (Fin 3) K) = Q ∧
      (∀ a ∈ AM, (((conjUHom h Q⁻¹ a : SG h) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).IsDiag) ∧
      ∃ a ∈ AM, conjUHom h Q⁻¹ a = tOne h hlamn := by
  have hAM9 : ∀ a ∈ AM, a ^ 9 = 1 := by
    intro a ha
    obtain ⟨c, -, hc3, hc⟩ := mem_normOneScalars.1 (hAM3 a ha)
    apply Subtype.ext
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
    rfl
  have h9 : 9 ∣ ℓ ^ f + 1 := hlam.dvd_of_pow_eq_one _ (by
    rw [pow_succ, ← UnitaryFieldData.bar_apply]
    exact hlamn)
  have hle : SG h ≤ UG h := fun g hg => ((mem_gramSU_iff_unitary h).1 hg).1
  obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m h hlam h9
    (AM.map (Subgroup.inclusion hle))
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hAMc a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hAM9 a ha, map_one])
  have hconj : ∀ (R : UG h) (a : SG h), ((conjUHom h R⁻¹ a : SG h) : GL (Fin 3) K) =
      ((R : GL (Fin 3) K))⁻¹ * (a : GL (Fin 3) K) * (R : GL (Fin 3) K) := fun R a => by
    rw [coe_conjUHom_apply, Subgroup.coe_inv, inv_inv]
  have hPd : ∀ a ∈ AM, (((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro a ha
    have hd := hP (Subgroup.inclusion hle a) ⟨a, ha, rfl⟩
    have e : ((conjUHom h P⁻¹ a : SG h) : GL (Fin 3) K) =
        ((P⁻¹ * Subgroup.inclusion hle a * P : UG h) : GL (Fin 3) K) := by
      rw [hconj, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [e]
    exact hd
  have hscal : ∀ (R : UG h), ∀ z ∈ normOneScalars h (SG h) 3, conjUHom h R z = z := by
    rintro R z ⟨c, -, -, hz⟩
    apply Subtype.ext
    rw [coe_conjUHom_apply, hz, (commute_scalar c (R : GL (Fin 3) K)).eq, mul_inv_cancel_right]
  set AM' := AM.map (conjUHom h P⁻¹).toMonoidHom with hAM'
  have hcard' : 27 ≤ Nat.card AM' := by
    rw [hAM', Subgroup.card_map_of_injective (conjUHom h P⁻¹).injective]
    exact hcard
  have hAM'd : ∀ s ∈ AM', ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    rintro _ ⟨a, ha, rfl⟩
    exact hPd a ha
  have hAM'9 : ∀ s ∈ AM', s ^ 9 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hAM9 a ha, map_one]
  have hAM'3 : ∀ s ∈ AM', s ^ 3 ∈ normOneScalars h (SG h) 3 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hscal _ _ (hAM3 a ha)]
    exact hAM3 a ha
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  have hlam9 : lam ^ 9 = 1 := hlam.pow_eq_one
  have htD : (((tOne h hlamn : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    isDiag_diagU _ _ _
  have htpow : ∀ n : ℕ, (((tOne h hlamn ^ n : SG h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal (dOne lam ^ n) := fun n => by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, tOne, coe_diagU, diagonal_pow]
  have ht9 : tOne h hlamn ^ 9 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [htpow, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · show ((lam ^ 2)⁻¹) ^ 9 = 1
      rw [inv_pow, ← pow_mul, show 2 * 9 = 9 * 2 from rfl, pow_mul, hlam9, one_pow, inv_one]
    · exact hlam9
    · exact hlam9
  have hlam3n : h.norm ((Units.mk0 (lam ^ 3) (pow_ne_zero 3 hlam0) : Kˣ) : K) = 1 := by
    rw [Units.val_mk0, UnitaryFieldData.norm, map_pow, ← mul_pow, mul_comm, hlamn, one_pow]
  have hlam33 : (Units.mk0 (lam ^ 3) (pow_ne_zero 3 hlam0) : Kˣ) ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, hlam9, Units.val_one]
  have ht3 : tOne h hlamn ^ 3 ∈ normOneScalars h (SG h) 3 := by
    refine ⟨Units.mk0 (lam ^ 3) (pow_ne_zero 3 hlam0), hlam3n, hlam33, ?_⟩
    apply Units.ext
    rw [htpow, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply, Units.val_mk0]
    congr 1
    funext i
    fin_cases i
    · show ((lam ^ 2)⁻¹) ^ 3 = lam ^ 3
      rw [inv_pow, ← pow_mul]
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_add, show 2 * 3 + 3 = 9 from rfl, hlam9]
    · rfl
    · rfl
  have htA : tOne h hlamn ∈ AM' := mem_of_isDiag_of_le_card hAM'd hAM'9 hAM'3 hcard' htD ht9 ht3
  obtain ⟨ζ, hζσ, hζ, hζn⟩ := exists_primitiveRoot_fixed h Nat.prime_three hK0 hbar hpQ
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (by norm_num)
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  have ht'D : (((tTwo h hζn : SG h) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag :=
    isDiag_diagU _ _ _
  have ht'pow : ∀ n : ℕ, (((tTwo h hζn ^ n : SG h) : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = diagonal ((![1, ζ, ζ⁻¹] : Fin 3 → K) ^ n) := fun n => by
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, tTwo, coe_diagU, diagonal_pow]
  have ht'3 : tTwo h hζn ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [ht'pow, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp [hζ3, inv_pow]
  have ht'9 : tTwo h hζn ^ 9 = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, ht'3, one_pow]
  have ht'A : tTwo h hζn ∈ AM' := mem_of_isDiag_of_le_card hAM'd hAM'9 hAM'3 hcard' ht'D ht'9
    (by rw [ht'3]; exact one_mem _)
  set X : GL (Fin 3) K := (P : GL (Fin 3) K)⁻¹ * glAut σ (P : GL (Fin 3) K) with hXdef
  have hrel : ∀ s ∈ AM', ∃ c : Kˣ, c ^ 3 = 1 ∧
      (X : Matrix (Fin 3) (Fin 3) K) * ((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
        (c : K) • (((s : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (X : Matrix (Fin 3) (Fin 3) K)) := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, -, hc3, hc⟩ := mem_normOneScalars.1 (hAMσ a ha)
    refine ⟨c, hc3, mul_map_conjUHom_eq_smul σ P ?_⟩
    rw [← hc, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  have hX0 : (X : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  obtain ⟨c₁, hc₁, h₁⟩ := hrel _ htA
  obtain ⟨c₂, -, h₂⟩ := hrel _ ht'A
  rw [tOne, coe_diagU, diagonal_map (map_zero σ)] at h₁
  rw [tTwo, coe_diagU, diagonal_map (map_zero σ)] at h₂
  have hfixζ : (fun i => σ ((![1, ζ, ζ⁻¹] : Fin 3 → K) i)) = ![1, ζ, ζ⁻¹] := by
    funext i
    fin_cases i <;> simp [hζσ, map_inv₀]
  rw [hfixζ] at h₂
  obtain ⟨-, x01, x02, x10, x20⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3.blockDiag_of_mul_eq_smul hX0 (prod_dOne hlam0)
      (by rw [← map_prod, prod_dOne hlam0, map_one]) (dOne_one_eq_two lam)
    rfl (dOne_zero_ne_one hlam0 (fun h3 => by
      have := hlam.dvd_of_pow_eq_one 3 h3
      omega))
    (by rw [← Units.val_pow_eq_pow_val, hc₁, Units.val_one]) h₁
  have hζne : ζ ≠ ζ⁻¹ := by
    intro he
    have h2 : ζ ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [he]; exact mul_inv_cancel₀ hζ0
    have := hζ.dvd_of_pow_eq_one 2 h2
    omega
  obtain ⟨-, x12, x21⟩ := CFSG.LocalAnalysis.GLTheoremA.S267Z.Lin3.diag_of_blockDiag hX0 x01 x02
    x10 x20 (by simp) (by simpa using hζne) h₂
  have hXd : (X : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
  obtain ⟨Y, hYU, hYd, hPY⟩ := exists_fixed_mul_isDiag h hσ hf₀ hK0 hbar P.2 hXd
  refine ⟨⟨(P : GL (Fin 3) K) * Y, mul_mem P.2 hYU⟩, hPY, ?_⟩
  have hQP : ∀ a ∈ AM, conjUHom h (⟨(P : GL (Fin 3) K) * Y, mul_mem P.2 hYU⟩ : UG h)⁻¹ a =
      conjUHom h P⁻¹ a := by
    intro a ha
    apply Subtype.ext
    have e := inv_mul_mul_eq_of_isDiag (hPd a ha) hYd
    rw [hconj] at e
    rw [hconj, hconj]
    show ((P : GL (Fin 3) K) * Y)⁻¹ * (a : GL (Fin 3) K) * ((P : GL (Fin 3) K) * Y) =
      ((P : GL (Fin 3) K))⁻¹ * (a : GL (Fin 3) K) * (P : GL (Fin 3) K)
    rw [← e]
    group
  refine ⟨fun a ha => by rw [hQP a ha]; exact hPd a ha, ?_⟩
  obtain ⟨a₁, ha₁, ht₁⟩ := htA
  exact ⟨a₁, ha₁, (hQP a₁ ha₁).trans ht₁⟩

end Frame

section Data

variable [Finite K] (h : UnitaryFieldData ℓ f K) (hℓ : ℓ ≠ 2) (hperf : commutator (SG h) = ⊤)
include hℓ hperf

theorem z3Data_of_fieldUHom_mem {σ : K ≃+* K} (hσ : orderOf σ = 3)
    (hK0 : Nat.card (semilinearFixedSubfield σ) = (ℓ ^ (f / 3)) ^ 2)
    (hbar : ∀ x : K, σ x = x → h.bar x = x ^ (ℓ ^ (f / 3))) (hpf : 3 ∣ f)
    (hpQ : 3 ∣ ℓ ^ (f / 3) + 1) {E : Subgroup (MulAut (SG h))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3)
    (hcomm : ∀ s t : SG h, MulAut.conj s ∈ E → MulAut.conj t ∈ E → s * t = t * s)
    (hσE : fieldUHom h σ ∈ E) : Z3Data 3 (SG h) E := by
  haveI : Fact ℓ.Prime := ⟨h.prime⟩
  haveI : CharP K ℓ := h.charP
  have hK : Nat.card K = (ℓ ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hq : ℓ ^ f = (ℓ ^ (f / 3)) ^ 3 := by rw [← pow_mul, Nat.div_mul_cancel hpf]
  have hq0 : 5 ≤ ℓ ^ (f / 3) := by
    have hodd : Odd (ℓ ^ (f / 3)) := (h.prime.odd_of_ne_two hℓ).pow
    obtain ⟨m, hm⟩ := hodd
    obtain ⟨k, hk⟩ := hpQ
    omega
  have hf₀ : 1 ≤ f / 3 := by
    rcases Nat.eq_zero_or_pos (f / 3) with h0 | h0
    · rw [h0, pow_zero] at hq0
      omega
    · exact h0
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  obtain ⟨lam, hlamn, hlam, -⟩ := exists_primitiveRoot_nine h hσ3 hq hpQ
  have hlam0 : lam ≠ 0 := ne_zero_of_norm hlamn
  set AM := E.comap (MulAut.conj : SG h →* MulAut (SG h)) with hAMdef
  have hAMc : ∀ a ∈ AM, ∀ b ∈ AM, a * b = b * a := fun a ha b hb => hcomm a b ha hb
  have hZ : Subgroup.center (SG h) ≤ AM := by
    intro z hz
    change MulAut.conj z ∈ E
    have : MulAut.conj z = 1 := MulEquiv.ext fun g => by
      rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.1 hz g),
        mul_inv_cancel_right]
    rw [this]
    exact one_mem E
  have hconj3 : ∀ a ∈ AM, a ^ 3 ∈ normOneScalars h (SG h) 3 := by
    intro a ha
    rw [← center_SG h hℓ, Subgroup.mem_center_iff]
    intro g
    have e : MulAut.conj (a ^ 3) = 1 := by rw [map_pow]; exact hE.2 _ ha
    have := congrArg (fun φ : MulAut (SG h) => φ g) e
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * a ^ 3 = a ^ 3 * g * (a ^ 3)⁻¹ * a ^ 3 := by rw [this]
      _ = a ^ 3 * g := by group
  have hAMσ : ∀ a ∈ AM, fieldUHom h σ a * a⁻¹ ∈ normOneScalars h (SG h) 3 := by
    intro a ha
    have hc : fieldUHom h σ * MulAut.conj a = MulAut.conj a * fieldUHom h σ :=
      congrArg (Subtype.val : E → MulAut (SG h)) (hE.1.is_comm.comm ⟨_, hσE⟩ ⟨_, ha⟩)
    have h1 : MulAut.conj (fieldUHom h σ a) = MulAut.conj a := by
      have e : MulAut.conj (fieldUHom h σ a) =
          fieldUHom h σ * MulAut.conj a * (fieldUHom h σ)⁻¹ := by
        ext g
        simp [MulAut.conj_apply]
      rw [e, hc, mul_inv_cancel_right]
    have h2 : MulAut.conj (fieldUHom h σ a * a⁻¹) = 1 := by
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    rw [← center_SG h hℓ, Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut (SG h) => φ g) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * (fieldUHom h σ a * a⁻¹) =
          (fieldUHom h σ a * a⁻¹) * g * (fieldUHom h σ a * a⁻¹)⁻¹ * (fieldUHom h σ a * a⁻¹) := by
          rw [this]
      _ = (fieldUHom h σ a * a⁻¹) * g := by group
  have h9 := nine_le_card_inf_range h hℓ hσ hK0 hq hpQ hperf hE hσE (by rw [hcard]; norm_num)
  have hcardA : 27 ≤ Nat.card AM := by
    have h1 := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker
      (MulAut.conj : SG h →* MulAut (SG h)) AM
    have hmap : AM.map (MulAut.conj : SG h →* MulAut (SG h)) =
        E ⊓ (MulAut.conj : SG h →* MulAut (SG h)).range := by
      rw [hAMdef, Subgroup.map_comap_eq, inf_comm]
    rw [hmap] at h1
    set ω : Kˣ := Units.mk0 (lam ^ 3) (pow_ne_zero 3 hlam0) with hω
    have hωn : h.norm (ω : K) = 1 := by
      rw [Units.val_mk0, UnitaryFieldData.norm, map_pow, ← mul_pow, mul_comm, hlamn, one_pow]
    have hω3 : ω ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← pow_mul, hlam.pow_eq_one, Units.val_one]
    have hz1 : scalarU h ω hωn hω3 ≠ 1 := by
      intro h1'
      have e := congrArg (fun g : SG h => ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0) h1'
      simp only [coe_scalarU, diagonal_apply_eq, Subgroup.coe_one, Units.val_one, one_apply_eq,
        hω, Units.val_mk0] at e
      have := hlam.dvd_of_pow_eq_one 3 e
      omega
    have hzord : orderOf (scalarU h ω hωn hω3) = 3 := by
      refine orderOf_eq_prime ?_ hz1
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, coe_scalarU, diagonal_pow, Subgroup.coe_one,
        Units.val_one, ← diagonal_one]
      congr 1
      funext i
      rw [Pi.pow_apply, ← Units.val_pow_eq_pow_val, hω3, Units.val_one]
    have hzle : Subgroup.zpowers (scalarU h ω hωn hω3) ≤
        AM ⊓ (MulAut.conj : SG h →* MulAut (SG h)).ker := by
      rw [Subgroup.zpowers_le]
      have hzc : scalarU h ω hωn hω3 ∈ Subgroup.center (SG h) := by
        rw [center_SG h hℓ]
        exact ⟨ω, hωn, hω3, rfl⟩
      refine ⟨hZ hzc, ?_⟩
      show MulAut.conj (scalarU h ω hωn hω3) = 1
      exact MulEquiv.ext fun g => by
        rw [MulAut.conj_apply, MulAut.one_apply, ← (Subgroup.mem_center_iff.1 hzc g),
          mul_inv_cancel_right]
    have h3 : 3 ≤ Nat.card ↥(AM ⊓ (MulAut.conj : SG h →* MulAut (SG h)).ker) :=
      calc 3 = Nat.card (Subgroup.zpowers (scalarU h ω hωn hω3)) := by
            rw [Nat.card_zpowers, hzord]
        _ ≤ _ := Subgroup.card_le_of_le hzle
    rw [← h1]
    calc 27 = 9 * 3 := rfl
      _ ≤ _ := Nat.mul_le_mul h9 h3
  obtain ⟨Q, hQσ, hQd, a₀, ha₀, ht₀⟩ := exists_frame h hσ hf₀ hK0 hbar hpQ hlamn hlam hAMc hconj3
    hcardA hAMσ
  set e := conjUHom h Q with he
  have he_inv : ∀ a : SG h, e⁻¹ a = conjUHom h Q⁻¹ a := fun a => by rw [he, map_inv]
  have hQU : primeFormFieldU h (isPrimeFormGram_one (n := 3)) σ Q = Q := Subtype.ext hQσ
  have hfe : fieldUHom h σ * e = e * fieldUHom h σ := by
    have := fieldUHom_conj σ Q
    rw [hQU, ← he] at this
    calc fieldUHom h σ * e = fieldUHom h σ * e * (fieldUHom h σ)⁻¹ * fieldUHom h σ := by group
      _ = e * fieldUHom h σ := by rw [this]
  have hfe' : e⁻¹ * fieldUHom h σ * e = fieldUHom h σ := by
    rw [mul_assoc, hfe, ← mul_assoc, inv_mul_cancel, one_mul]
  apply z3Data_of_map Nat.prime_three e
  refine z3Data_std hℓ hK hσ hK0 hbar hpQ hq hq0 hlamn hlam ?_ ?_ ?_
  ·
    refine ⟨MulAut.conj a₀, ha₀, ?_⟩
    change MulAut.congr e⁻¹ (MulAut.conj a₀) = _
    rw [mulAut_congr_inv_apply, ← ht₀, ← he_inv]
    ext g
    simp [MulAut.conj_apply]
  · exact ⟨fieldUHom h σ, hσE, by
      change MulAut.congr e⁻¹ (fieldUHom h σ) = _
      rw [mulAut_congr_inv_apply, hfe']⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    obtain ⟨k, s, hsE, rfl⟩ := exists_eq_zpow_mul_conj h hℓ hσ hK0 hq hpQ hperf hE hσE hγ
    have hs9 : s ^ 9 = 1 := by
      obtain ⟨c, -, hc3, hc⟩ := mem_normOneScalars.1 (hconj3 s hsE)
      apply Subtype.ext
      rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, Subgroup.coe_pow, hc, ← map_pow, hc3, map_one]
      rfl
    refine ⟨k, e⁻¹ s, ?_, ?_, ?_⟩
    · rw [he_inv]
      exact hQd s hsE
    · rw [← map_pow, hs9, map_one]
    · change MulAut.congr e⁻¹ (fieldUHom h σ ^ k * MulAut.conj s) = _
      have hc : ∀ γ : MulAut (SG h), e⁻¹ * γ * e = MulAut.conj e⁻¹ γ := fun γ => by
        rw [MulAut.conj_apply, inv_inv]
      rw [mulAut_congr_inv_apply, hc, map_mul, map_zpow, ← hc, hfe', ← hc]
      congr 1
      ext g
      simp [MulAut.conj_apply]

theorem z3Model_SG (hℓ3 : ℓ ≠ 3) (h3 : 3 ∣ ℓ ^ f + 1) : Z3Model 3 (SG h) := by
  refine ⟨fun E hE => card_le_pow_three_SG hℓ hperf Nat.prime_three (by norm_num) (Ne.symm hℓ3) hE,
    ?_⟩
  intro E hE hcard AM hAM hZ hEq
  have hinj := quotU_injective hℓ hperf
  have hE' : IsElemAbelian 3 (E.map (quotU h hℓ)) :=
    (CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hinj 3 E).2 hE
  have hcard' : Nat.card (E.map (quotU h hℓ)) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective hinj, hcard]
  obtain ⟨_, ⟨α, hαE, rfl⟩, -, σ, hσ, -, hpf, hpQ, hK0, hbar, M, hM⟩ :=
    exists_fieldAut_mem h hℓ Nat.prime_three (by norm_num) (Ne.symm hℓ3) hE' hcard'
  set e := conjUHom h M with he
  have hα : e⁻¹ * α * e = fieldUHom h σ := hinj (by
    rw [map_mul, map_mul, map_inv, he, quotU_conjUHom, quotU_fieldUHom]
    exact hM)
  have hmemAM : ∀ s : SG h, MulAut.conj s ∈ E → s ∈ AM := by
    intro s hs
    have h1 : MulAut.conj s ∈ AM.map (MulAut.conj : SG h →* MulAut (SG h)) := by
      rw [← hEq]
      exact ⟨hs, s, rfl⟩
    obtain ⟨a, ha, has⟩ := h1
    have hc : a⁻¹ * s ∈ Subgroup.center (SG h) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have e1 : a * g * a⁻¹ = s * g * s⁻¹ := by
        have := congrArg (fun φ : MulAut (SG h) => φ g) has
        simpa [MulAut.conj_apply] using this
      calc g * (a⁻¹ * s) = a⁻¹ * (a * g * a⁻¹) * s := by group
        _ = a⁻¹ * (s * g * s⁻¹) * s := by rw [e1]
        _ = a⁻¹ * s * g := by group
    have := mul_mem ha (hZ hc)
    rwa [mul_inv_cancel_left] at this
  have hcomm : ∀ s t : SG h, MulAut.conj s ∈ E → MulAut.conj t ∈ E → s * t = t * s :=
    fun s t hs ht => congrArg Subtype.val (hAM.is_comm.comm ⟨s, hmemAM s hs⟩ ⟨t, hmemAM t ht⟩)
  apply z3Data_of_map Nat.prime_three e
  have hφ : Function.Injective (MulAut.congr e⁻¹).toMonoidHom := (MulAut.congr e⁻¹).injective
  have hconjE : ∀ s : SG h, MulAut.conj s ∈ E.map (MulAut.congr e⁻¹).toMonoidHom →
      MulAut.conj (e s) ∈ E := by
    rintro s ⟨γ, hγ, hγs⟩
    have e1 : e⁻¹ * γ * e = MulAut.conj s := (mulAut_congr_inv_apply e γ).symm.trans hγs
    have e2 : γ = MulAut.conj (e s) := by
      have : γ = e * MulAut.conj s * e⁻¹ := by rw [← e1]; group
      rw [this]
      ext g
      simp [MulAut.conj_apply]
    rw [← e2]
    exact hγ
  refine z3Data_of_fieldUHom_mem h hℓ hperf hσ hK0 hbar hpf hpQ
    ((CFSG.LocalAnalysis.GLTheoremA.T123C.isElemAbelian_map_iff hφ 3 E).2 hE)
    (by rw [Subgroup.card_map_of_injective hφ, hcard]) (fun s t hs ht => ?_)
    ⟨α, hαE, by change MulAut.congr e⁻¹ α = _; rw [mulAut_congr_inv_apply, hα]⟩
  apply e.injective
  rw [map_mul, map_mul]
  exact hcomm _ _ (hconjE s hs) (hconjE t ht)

end Data

theorem z3UniBranch_holds : Z3UniBranch := by
  intro p Q hp hp2 hQ2 hQp M _ _ hM hO hZ hcat
  obtain ⟨hp3, K, _, _, h, h3, ⟨e⟩⟩ := exists_mulEquiv_SG_of_cover hp hp2 hQ2 hM hO hZ hcat
  subst hp3
  have hperf : commutator (SG h) = ⊤ :=
    (CFSG.ComponentClassification.Components.quasisimple_of_equiv e.symm hM).1
  exact CFSG.LocalAnalysis.GLTheoremA.S267Z.z3Model_congr Nat.prime_three e.symm
    (z3Model_SG h hQ2 hperf hQp h3)

end CFSG.LocalAnalysis.GLTheoremA.S267Z.Uni

end

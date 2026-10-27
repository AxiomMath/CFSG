module

public import CFSG.LieType.Chevalley.E6A5CubeLevi
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Model
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.RankThree.PartTwo.KFacts.K71G2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6A5Cube
open CFSG.LieType.Universal.Unitary (SU SUid antidiag conjTr conjEquiv exists_wittMatrix)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply)
open CFSG.ClassicalInvolution.Phan (Su)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU mem_coordBlockSU_iff)

section SUMap

variable {F : Type*} [Field F] (σ : F ≃+* F)

theorem conjTr_map_of_comm {n : ℕ} {δ : F ≃+* F} (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (A : Matrix (Fin n) (Fin n) F) : conjTr σ (A.map δ) = (conjTr σ A).map δ := by
  ext i j
  simp [conjTr, hδσ]

theorem antidiag_map (δ : F ≃+* F) (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) F).map δ = antidiag n := by
  ext i j
  simp only [antidiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem det_map_ringEquiv {n : ℕ} (δ : F ≃+* F) (A : Matrix (Fin n) (Fin n) F) :
    (A.map δ).det = δ A.det := by
  rw [RingEquiv.map_det, RingEquiv.mapMatrix_apply]

@[expose] def suMap (n : ℕ) {δ : F ≃+* F} (hδσ : ∀ c, δ (σ c) = σ (δ c)) : SU σ n →* SU σ n :=
  ((Matrix.GeneralLinearGroup.map δ.toRingHom).comp (SU σ n).subtype).codRestrict _ fun A => by
    obtain ⟨hdet, hiso⟩ := A.2
    refine ⟨?_, ?_⟩
    · change (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ).det = 1
      rw [det_map_ringEquiv, hdet, map_one]
    · change conjTr σ (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ) * antidiag n *
          ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ = antidiag n
      rw [conjTr_map_of_comm σ hδσ, ← antidiag_map δ n, ← Matrix.map_mul, ← Matrix.map_mul, hiso]

@[expose] def suidMap (n : ℕ) {δ : F ≃+* F} (hδσ : ∀ c, δ (σ c) = σ (δ c)) :
    SUid σ n →* SUid σ n :=
  ((Matrix.GeneralLinearGroup.map δ.toRingHom).comp (SUid σ n).subtype).codRestrict _ fun A => by
    obtain ⟨hdet, hiso⟩ := A.2
    refine ⟨?_, ?_⟩
    · change (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ).det = 1
      rw [det_map_ringEquiv, hdet, map_one]
    · change conjTr σ (((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ) *
          ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ = 1
      rw [conjTr_map_of_comm σ hδσ, ← Matrix.map_mul, hiso, Matrix.map_one _ (map_zero δ) (map_one δ)]

theorem coe_suidMap (n : ℕ) {δ : F ≃+* F} (hδσ : ∀ c, δ (σ c) = σ (δ c)) (A : SUid σ n) :
    (((suidMap σ n hδσ A : SUid σ n) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((A : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ :=
  rfl

theorem conjEquiv_symm_suidMap {n : ℕ} {δ : F ≃+* F} (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (P : GL (Fin n) F)
    (hP : conjTr σ (P : Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F) = antidiag n)
    (hPδ : ∀ i j, δ ((P : Matrix (Fin n) (Fin n) F) i j) = (P : Matrix (Fin n) (Fin n) F) i j)
    (y : SUid σ n) :
    (conjEquiv P hP).symm (suidMap σ n hδσ y) = suMap σ n hδσ ((conjEquiv P hP).symm y) := by
  have hPm : (P : Matrix (Fin n) (Fin n) F).map δ = P := by
    ext i j
    exact hPδ i j
  have hPi : ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ = (P⁻¹ : GL (Fin n) F) := by
    have h1 : (P : Matrix (Fin n) (Fin n) F).map δ *
        ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.map_one _ (map_zero δ) (map_one δ)]
    rw [hPm] at h1
    calc ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ
        = ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((P : Matrix (Fin n) (Fin n) F) *
          ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ) := by
          rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
      _ = _ := by rw [h1, Matrix.mul_one]
  apply Subtype.ext
  apply Units.ext
  show ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).map δ * (P : Matrix (Fin n) (Fin n) F) =
    (((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((y : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) * (P : Matrix (Fin n) (Fin n) F)).map δ
  rw [Matrix.map_mul, Matrix.map_mul, hPm, hPi]

theorem commute_of_coe_eq_smul {n : ℕ} {z : SUid σ n} {μ : F}
    (hz : ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = μ • (1 : Matrix (Fin n) (Fin n) F))
    (w : SUid σ n) : z * w = w * z := by
  apply Subtype.ext
  apply Units.ext
  show ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
    ((w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * ((z : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  rw [hz, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

end SUMap

section Levi

variable {K : Type} [Field K] [Finite K]

theorem entrywise_liftA (δ : K →+* K) (h : SpecialLinearGroup (Fin 6) K) :
    Units.map (entrywiseHom δ) ((liftA K h : groupA K) : ModGL Tag.E6 K) =
      ((liftA K (SpecialLinearGroup.map δ h) : groupA K) : ModGL Tag.E6 K) := by
  have key : (Units.map (entrywiseHom δ)).comp ((groupA K).subtype.comp (liftA K)) =
      ((groupA K).subtype.comp (liftA K)).comp (SpecialLinearGroup.map δ) := by
    refine MonoidHom.eq_of_eqOn_dense closure_adjSet ?_
    rintro _ ⟨t, c, rfl | rfl⟩
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, liftA_upAdj, map_upAdj]
      apply Units.ext
      rw [← pinnedX_single, ← pinnedX_single]
      exact entrywise_pinnedX δ _ c
    · simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, liftA_downAdj, map_downAdj]
      apply Units.ext
      rw [← pinnedX_neg_single, ← pinnedX_neg_single]
      exact entrywise_pinnedX δ _ c
  exact DFunLike.congr_fun key h

theorem map_eDiag {δ : K ≃+* K} {ζ : K} (hδζ : δ ζ = ζ) (i : Fin 6) : δ (eDiag K ζ i) = eDiag K ζ i := by
  fin_cases i <;> simp [eDiag, hδζ]

theorem map_conjSU {σ δ : K ≃+* K} (hδσ : ∀ c, δ (σ c) = σ (δ c)) {ζ : K} (hζ : ζ ≠ 0)
    (hδζ : δ ζ = ζ) (x : SU σ 6) :
    SpecialLinearGroup.map δ.toRingHom (conjSU σ hζ x) = conjSU σ hζ (suMap σ 6 hδσ x) := by
  apply Subtype.ext
  rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change ((diagonal (eDiag K ζ) * ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) *
      diagonal fun i => (eDiag K ζ i)⁻¹).map δ) =
    diagonal (eDiag K ζ) * ((x : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).map δ *
      diagonal fun i => (eDiag K ζ i)⁻¹
  have he : (fun i => δ (eDiag K ζ i)) = eDiag K ζ := funext (map_eDiag hδζ)
  have hi : (fun i => δ ((eDiag K ζ i)⁻¹)) = fun i => (eDiag K ζ i)⁻¹ :=
    funext fun i => by rw [map_inv₀, map_eDiag hδζ i]
  rw [Matrix.map_mul, Matrix.map_mul, diagonal_map (map_zero δ), diagonal_map (map_zero δ), he, hi]

theorem entrywise_leviHomA {σ δ : K ≃+* K} (hδσ : ∀ c, δ (σ c) = σ (δ c)) {ζ : K} (hζ : ζ ≠ 0)
    (hδζ : δ ζ = ζ) (x : SU σ 6) :
    Units.map (entrywiseHom δ.toRingHom) ((leviHomA σ hζ x : groupA K) : ModGL Tag.E6 K) =
      ((leviHomA σ hζ (suMap σ 6 hδσ x) : groupA K) : ModGL Tag.E6 K) := by
  rw [leviHomA, MonoidHom.comp_apply, MonoidHom.comp_apply, entrywise_liftA,
    map_conjSU hδσ hζ hδζ]

end Levi

section Count

variable {K : Type} [Field K] [Finite K]

theorem eq_one_of_forall_fixed {Q : ℕ} (hK : Nat.card K = Q ^ 2) (hQ : 2 ≤ Q) {p : ℕ}
    (hp : p.Prime) {τ : K ≃+* K} (hτp : τ ^ p = 1)
    (hτ : ∀ x : Kˣ, x ^ (Q + 1) = 1 → τ (x : K) = x) : τ = 1 := by
  classical
  have hcardU : Nat.card Kˣ = Q ^ 2 - 1 := by rw [Nat.card_units, hK]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hgo : orderOf g = Q ^ 2 - 1 := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcardU
  have hQ2 : Q ^ 2 - 1 = (Q + 1) * (Q - 1) := by
    have h1 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, (by omega : 1 ≤ Q)]
    ring
  have hdvd : Q + 1 ∣ orderOf g := by rw [hgo, hQ2]; exact Dvd.intro _ rfl
  have hg0 : orderOf g ≠ 0 := by
    rw [hgo, hQ2]
    exact Nat.mul_ne_zero (by omega) (by omega)
  set x := g ^ (orderOf g / (Q + 1)) with hx
  have hxo : orderOf x = Q + 1 := orderOf_pow_orderOf_div hg0 hdvd
  have hxτ : τ (x : K) = x := hτ x (by rw [← hxo]; exact pow_orderOf_eq_one x)
  set F := fixSubfield τ with hF
  haveI : Finite F := Subtype.finite
  have hxF : (x : K) ∈ F := (mem_fixSubfield τ).2 hxτ
  have hxiF : ((x⁻¹ : Kˣ) : K) ∈ F := by
    rw [Units.val_inv_eq_inv_val]
    exact F.inv_mem hxF
  set y : Fˣ := ⟨⟨x, hxF⟩, ⟨_, hxiF⟩, Subtype.ext (Units.mul_inv x), Subtype.ext (Units.inv_mul x)⟩
  have hyo : orderOf y = Q + 1 := by
    rw [← hxo]
    have hinj : Function.Injective (Units.map F.subtype.toMonoidHom) :=
      Units.map_injective fun a b h => Subtype.ext h
    have e : Units.map F.subtype.toMonoidHom y = x := Units.ext rfl
    rw [← e, orderOf_injective _ hinj y]
  have hFd : Q + 1 ∣ Nat.card F - 1 := by
    have h1 := orderOf_dvd_natCard y
    rwa [hyo, Nat.card_units] at h1
  have hc := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow τ
  by_contra hne
  have hτo : orderOf τ = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hτp) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne
    · exact h
  rw [hτo, hK] at hc
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  have hle : Nat.card F ^ 2 ≤ Q ^ 2 := by
    rw [← hc]
    exact Nat.pow_le_pow_right (by omega) hp.two_le
  have hFQ : Nat.card F ≤ Q := by
    by_contra h
    have : Q ^ 2 < Nat.card F ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
    omega
  have := Nat.le_of_dvd (by omega) hFd
  omega

end Count

section Fixed

variable {K : Type} [Field K] [Finite K]

theorem card_fixSubfield_of_orderOf {ℓ p d : ℕ} (hp : p.Prime) (hK : Nat.card K = (ℓ ^ (p * d)) ^ 2)
    {δ : K ≃+* K} (hδ : orderOf δ = p) : Nat.card (fixSubfield δ) = (ℓ ^ d) ^ 2 := by
  have hc := CFSG.RankThree.PartTwo.KFacts.card_fixSubfield_pow δ
  rw [hδ, hK] at hc
  have e : (ℓ ^ (p * d)) ^ 2 = ((ℓ ^ d) ^ 2) ^ p := by ring
  rw [e] at hc
  exact Nat.pow_left_injective hp.ne_zero hc

theorem pow_eq_of_mem_fixSubfield {ℓ p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (ℓ ^ (p * d)) ^ 2) {δ : K ≃+* K} (hδ : orderOf δ = p) {x : K}
    (hx : x ∈ fixSubfield δ) : x ^ (ℓ ^ (p * d)) = x ^ (ℓ ^ d) := by
  set F := fixSubfield δ with hF
  have hcard : Nat.card F = (ℓ ^ d) ^ 2 := card_fixSubfield_of_orderOf hp hK hδ
  have hpow : ∀ y ∈ F, y ^ ((ℓ ^ d) ^ 2) = y := by
    intro y hy
    haveI : Fintype F := Fintype.ofFinite F
    have h1 := FiniteField.pow_card (⟨y, hy⟩ : F)
    rw [← Nat.card_eq_fintype_card, hcard] at h1
    exact congrArg Subtype.val h1
  have hpowm : ∀ y ∈ F, ∀ m : ℕ, y ^ (((ℓ ^ d) ^ 2) ^ m) = y := by
    intro y hy m
    induction m with
    | zero => rw [pow_zero, pow_one]
    | succ m ih => rw [pow_succ, pow_mul, ih, hpow y hy]
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have e : ℓ ^ (p * d) = ℓ ^ d * ((ℓ ^ d) ^ 2) ^ m := by
    rw [hm]
    ring
  rw [e, pow_mul]
  exact hpowm _ (F.pow_mem hx _) m

end Fixed

section Sub

variable {K : Type} [Field K] [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
  {p d : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (ℓ ^ (p * d)) ^ 2)
  {δ : K ≃+* K} (hδ : orderOf δ = p)

include hp hp2 hK hδ in
theorem coe_unitaryInvolution_fixSubfield (x : fixSubfield δ) :
    ((unitaryInvolution (fixSubfield δ) ℓ d x : fixSubfield δ) : K) =
      unitaryInvolution K ℓ (p * d) (x : K) := by
  rw [unitaryInvolution_apply, unitaryInvolution_apply, SubmonoidClass.coe_pow]
  exact (pow_eq_of_mem_fixSubfield hp hp2 hK hδ x.2).symm

include hp hp2 hK hδ in
theorem conjTr_map_fixSubfield {n : ℕ} (A : Matrix (Fin n) (Fin n) (fixSubfield δ)) :
    conjTr (unitaryInvolution K ℓ (p * d)) (A.map (fixSubfield δ).subtype) =
      (conjTr (unitaryInvolution (fixSubfield δ) ℓ d) A).map (fixSubfield δ).subtype := by
  ext i j
  show unitaryInvolution K ℓ (p * d) ((A j i : fixSubfield δ) : K) =
    ((unitaryInvolution (fixSubfield δ) ℓ d (A j i) : fixSubfield δ) : K)
  exact (coe_unitaryInvolution_fixSubfield hp hp2 hK hδ (A j i)).symm

@[expose] noncomputable def suidSub (n : ℕ) : Su (fixSubfield δ) ℓ d n →* Su K ℓ (p * d) n :=
  ((Matrix.GeneralLinearGroup.map (fixSubfield δ).subtype).comp
    (SUid (unitaryInvolution (fixSubfield δ) ℓ d) n).subtype).codRestrict _ fun A => by
    obtain ⟨hdet, hiso⟩ := A.2
    refine ⟨?_, ?_⟩
    · change (((A : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
        (fixSubfield δ).subtype).det = 1
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet, map_one]
    · change conjTr (unitaryInvolution K ℓ (p * d))
          (((A : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
            (fixSubfield δ).subtype) *
          ((A : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
            (fixSubfield δ).subtype = 1
      rw [conjTr_map_fixSubfield hp hp2 hK hδ, ← Matrix.map_mul, hiso,
        Matrix.map_one _ (map_zero _) (map_one _)]

theorem coe_suidSub {n : ℕ} (A : Su (fixSubfield δ) ℓ d n) :
    (((suidSub hp hp2 hK hδ n A : Su K ℓ (p * d) n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
        (fixSubfield δ).subtype :=
  rfl

theorem suidSub_injective (n : ℕ) : Function.Injective (suidSub hp hp2 hK hδ n) := by
  intro A B h
  apply Subtype.ext
  apply Units.ext
  ext i j
  have h1 := congrArg (fun g : Su K ℓ (p * d) n =>
    ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) h
  simp only [coe_suidSub, Matrix.map_apply] at h1
  exact h1

theorem suidSub_fixed {n : ℕ} (A : Su (fixSubfield δ) ℓ d n) (i j : Fin n) :
    δ ((((suidSub hp hp2 hK hδ n A : Su K ℓ (p * d) n) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i j) =
      (((suidSub hp hp2 hK hδ n A : Su K ℓ (p * d) n) : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) i j :=
  (mem_fixSubfield δ).1
    (((A : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)) i j).2

theorem mem_range_suidSub {n : ℕ} {B : Su K ℓ (p * d) n}
    (hB : ∀ i j, δ (((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) =
      ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j) :
    B ∈ (suidSub hp hp2 hK hδ n).range := by
  set A : Matrix (Fin n) (Fin n) (fixSubfield δ) :=
    Matrix.of fun i j => ⟨_, (mem_fixSubfield δ).2 (hB i j)⟩ with hA
  have hAB : A.map (fixSubfield δ).subtype = ((B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rfl
  have hdet : A.det = 1 := by
    apply Subtype.val_injective
    have h1 := RingHom.map_det (fixSubfield δ).subtype A
    rw [RingHom.mapMatrix_apply, hAB, B.2.1] at h1
    exact h1
  set A' : GL (Fin n) (fixSubfield δ) :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero) with hA'
  have hA'm : (A' : Matrix (Fin n) (Fin n) (fixSubfield δ)) = A := rfl
  have hmem : A' ∈ SUid (unitaryInvolution (fixSubfield δ) ℓ d) n := by
    refine ⟨by rw [hA'm]; exact hdet, ?_⟩
    have h1 := B.2.2
    rw [← hAB, conjTr_map_fixSubfield hp hp2 hK hδ, ← Matrix.map_mul] at h1
    rw [hA'm]
    ext i j
    have h2 := congrFun (congrFun h1 i) j
    rw [Matrix.map_apply] at h2
    refine h2.trans ?_
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  exact ⟨⟨A', hmem⟩, Subtype.ext (Units.ext hAB)⟩

include hp hp2 hK hδ in
theorem exists_unitaryInvolution_eq_neg_fixed :
    ∃ ζ : K, ζ ≠ 0 ∧ unitaryInvolution K ℓ (p * d) ζ = -ζ ∧ δ ζ = ζ := by
  obtain ⟨z, hz0, hz⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg
    (card_fixSubfield_of_orderOf hp hK hδ)
  refine ⟨z, fun h => hz0 (Subtype.ext h), ?_, (mem_fixSubfield δ).1 z.2⟩
  rw [← coe_unitaryInvolution_fixSubfield hp hp2 hK hδ, hz]
  rfl

include hp hp2 hK hδ in
theorem exists_wittMatrix_fixed (n : ℕ) :
    ∃ P : GL (Fin n) K, conjTr (unitaryInvolution K ℓ (p * d)) (P : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K) = antidiag n ∧
      ∀ i j, δ ((P : Matrix (Fin n) (Fin n) K) i j) = (P : Matrix (Fin n) (Fin n) K) i j := by
  obtain ⟨P₀, hP₀⟩ := exists_wittMatrix (card_fixSubfield_of_orderOf hp hK hδ) n
  refine ⟨Matrix.GeneralLinearGroup.map (fixSubfield δ).subtype P₀, ?_, fun i j =>
    (mem_fixSubfield δ).1 (((P₀ : GL (Fin n) (fixSubfield δ)) :
      Matrix (Fin n) (Fin n) (fixSubfield δ)) i j).2⟩
  change conjTr (unitaryInvolution K ℓ (p * d))
      (((P₀ : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
        (fixSubfield δ).subtype) *
      ((P₀ : GL (Fin n) (fixSubfield δ)) : Matrix (Fin n) (Fin n) (fixSubfield δ)).map
        (fixSubfield δ).subtype = antidiag n
  rw [conjTr_map_fixSubfield hp hp2 hK hδ, ← Matrix.map_mul, hP₀]
  ext i j
  simp only [antidiag, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem suidMap_suidSub {n : ℕ} (A : Su (fixSubfield δ) ℓ d n) :
    suidMap (unitaryInvolution K ℓ (p * d)) n (ringEquiv_comm_of_finite _ δ)
      (suidSub hp hp2 hK hδ n A) = suidSub hp hp2 hK hδ n A := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact suidSub_fixed hp hp2 hK hδ A i j

theorem suidSub_mem_coordBlockSU {n : ℕ} {J : Finset (Fin n)} {A : Su (fixSubfield δ) ℓ d n}
    (hA : A ∈ coordBlockSU (fixSubfield δ) ℓ d J) :
    suidSub hp hp2 hK hδ n A ∈ coordBlockSU K ℓ (p * d) J := by
  rw [mem_coordBlockSU_iff] at hA ⊢
  intro i j hij
  rw [coe_suidSub, Matrix.map_apply, hA i j hij]
  split_ifs <;> simp

end Sub

section SUTwo

variable {F : Type} [Field F] [Finite F] {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]

theorem exists_su_two_orderOf_not_commute {d : ℕ} (hF : Nat.card F = (ℓ ^ d) ^ 2) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ (ℓ ^ d) ^ 2 - 1) :
    ∃ M W : Su F ℓ d 2, orderOf M = p ∧ M * W ≠ W * M := by
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := exists_wittMatrix hF 2
  set e := (CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans (conjEquiv P hP) with he
  have hF0 : Nat.card (CFSG.LieType.Steinberg.fixedSubfield F ℓ d) = ℓ ^ d :=
    CFSG.LieType.Steinberg.card_fixedSubfield hF
  obtain ⟨A, hA⟩ := exists_orderOf_eq_sl2 hp (by rw [hF0]; exact hpF)
  obtain ⟨W, hW⟩ := exists_not_commute_sl2 hp (hp.odd_of_ne_two hp2) hA
  refine ⟨e A, e W, ?_, fun h => hW (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact (orderOf_injective e.toMonoidHom e.injective A).trans hA

end SUTwo

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Outer

end

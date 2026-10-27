module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth23InnerModule
public import CFSG.Monster.B.GSide.EdgeAut
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverAction
import all CFSG.Fischer.F4

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6.Stroth23Inner

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Unitary
  CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.GSide
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped Matrix

@[expose] noncomputable def frobP1 : P1 →* Multiplicative (ZMod 2) :=
  SemidirectProduct.rightHom.comp (phiU.toMonoidHom.comp p1Proj)

theorem frobP1_apply (p : P1) : frobP1 p = (phiU (p1Proj p)).right := rfl

theorem commutator_P1_le_ker : commutator P1 ≤ frobP1.ker :=
  Abelianization.commutator_subset_ker frobP1

theorem frobP1_surjective : Function.Surjective frobP1 := by
  obtain ⟨p, hp⟩ := p1Proj_surjective (genU 5)
  have h5 : frobP1 p ≠ 1 := by
    rw [frobP1_apply, hp, phiU_genU]
    change Multiplicative.ofAdd (b6Frob 5) ≠ 1
    decide
  intro e
  rcases (show ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 by decide) e
    with rfl | rfl
  · exact ⟨1, map_one _⟩
  · refine ⟨p, ?_⟩
    rcases (show ∀ e : Multiplicative (ZMod 2), e = 1 ∨ e = Multiplicative.ofAdd 1 by decide)
      (frobP1 p) with h | h
    · exact absurd h h5
    · exact h

theorem mem_commutator_P1_iff (p : P1) : p ∈ commutator P1 ↔ frobP1 p = 1 := by
  have hidx : frobP1.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ frobP1_surjective,
      Subgroup.card_top, Nat.card_eq_fintype_card]
    rfl
  have : frobP1.ker.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have heq := Subgroup.eq_of_index_dvd_index commutator_P1_le_ker
    (by rw [index_commutator_P1, hidx])
  rw [heq]
  rfl

theorem phiU_p1Proj_eq_inl {p : P1} (hp : p ∈ commutator P1) :
    phiU (p1Proj p) = SemidirectProduct.inl (phiU (p1Proj p)).left := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right (phiU (p1Proj p))]
  rw [show (phiU (p1Proj p)).right = 1 from (mem_commutator_P1_iff p).1 hp, map_one, mul_one]

@[expose] noncomputable def piU : commutator P1 →* SUh ⧸ Zh where
  toFun q := (phiU (p1Proj (q : P1))).left
  map_one' := by simp
  map_mul' q q' := by
    rw [Subgroup.coe_mul, map_mul, map_mul, SemidirectProduct.mul_left,
      show (phiU (p1Proj (q : P1))).right = 1 from (mem_commutator_P1_iff _).1 q.2, map_one,
      MulAut.one_apply]

theorem inl_piU (q : commutator P1) :
    SemidirectProduct.inl (piU q) = phiU (p1Proj (q : P1)) :=
  (phiU_p1Proj_eq_inl q.2).symm

theorem phiU_symm_inl_piU (q : commutator P1) :
    phiU.symm (SemidirectProduct.inl (piU q)) = p1Proj (q : P1) := by
  rw [inl_piU, MulEquiv.symm_apply_apply]

theorem rhoU_piU (q : commutator P1) : rhoU (piU q) = perpEnd (p1Proj (q : P1)) := by
  rw [rhoU, phiU_symm_inl_piU]

theorem piU_surjective : Function.Surjective piU := by
  intro u
  obtain ⟨p, hp⟩ := p1Proj_surjective (phiU.symm (SemidirectProduct.inl u))
  have hpc : p ∈ commutator P1 := by
    rw [mem_commutator_P1_iff, frobP1_apply, hp, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨⟨p, hpc⟩, ?_⟩
  have h : (SemidirectProduct.inl (piU ⟨p, hpc⟩) : SigmaU6) = SemidirectProduct.inl u := by
    rw [inl_piU, hp, MulEquiv.apply_symm_apply]
  exact SemidirectProduct.inl_injective h

theorem piU_eq_one_iff (q : commutator P1) : piU q = 1 ↔ (q : P1) ∈ N1.subgroupOf P1 := by
  rw [← ker_p1Proj, MonoidHom.mem_ker, ← phiU_symm_inl_piU, MulEquiv.map_eq_one_iff]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)

theorem lieModel_U : CFSG.Blueprint.LieModel (SUh ⧸ Zh) .PSU 6 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, CFSG.Fischer.F4, inferInstance,
    inferInstance, natCard_F4,
    ⟨Unitary.psiQ.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hF4 (by norm_num))⟩⟩

theorem card_outer_U : Nat.card (Outer (SUh ⧸ Zh)) = 6 :=
  CFSG.EvenSmallLie.UnitarySix.card_outer_of_lieModel lieModel_U

instance finite_outer_U : Finite (Outer (SUh ⧸ Zh)) :=
  Nat.finite_of_card_ne_zero (by rw [card_outer_U]; norm_num)

@[expose] def IsTwist (β : MulAut (SUh ⧸ Zh)) : Prop :=
  ∃ A : Module.End (ZMod 2) sigmaPerp, A sigmaP = sigmaP ∧ ∀ u x, A (rhoU u x) = rhoU (β u) (A x)

theorem rhoU_sigmaP (u : SUh ⧸ Zh) : rhoU u sigmaP = sigmaP := perpEnd_sigmaP _

attribute [local irreducible] rhoU

theorem isTwist_one : IsTwist 1 := ⟨1, rfl, fun _ _ => rfl⟩

set_option maxHeartbeats 1000000 in
theorem isTwist_mul {β β' : MulAut (SUh ⧸ Zh)} (h : IsTwist β) (h' : IsTwist β') :
    IsTwist (β * β') := by
  obtain ⟨A, hAσ, hA⟩ := h
  obtain ⟨A', hAσ', hA'⟩ := h'
  refine ⟨A * A', by rw [Module.End.mul_apply, hAσ', hAσ], fun u x => ?_⟩
  rw [Module.End.mul_apply, Module.End.mul_apply, hA', hA, MulAut.mul_apply]

@[expose] noncomputable def twistOuter : Subgroup (Outer (SUh ⧸ Zh)) :=
  have hmul : ∀ {a b : Outer (SUh ⧸ Zh)}, a ∈ {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧
      IsTwist β} → b ∈ {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧ IsTwist β} →
      a * b ∈ {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧ IsTwist β} := by
    rintro _ _ ⟨β, rfl, hβ⟩ ⟨β', rfl, hβ'⟩
    exact ⟨β * β', rfl, isTwist_mul hβ hβ'⟩
  have hpow : ∀ {a : Outer (SUh ⧸ Zh)} (n : ℕ), a ∈ {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧
      IsTwist β} → a ^ n ∈ {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧ IsTwist β} := by
    intro a n ha
    induction n with
    | zero => exact ⟨1, by rw [pow_zero]; rfl, isTwist_one⟩
    | succ n ih => rw [pow_succ]; exact hmul ih ha
  { carrier := {o | ∃ β, (QuotientGroup.mk β : Outer _) = o ∧ IsTwist β}
    one_mem' := ⟨1, rfl, isTwist_one⟩
    mul_mem' := hmul
    inv_mem' := fun {a} ha => by
      have h := hpow (Nat.card (Outer (SUh ⧸ Zh)) - 1) ha
      have hn : 0 < Nat.card (Outer (SUh ⧸ Zh)) := Nat.card_pos
      have e : a ^ (Nat.card (Outer (SUh ⧸ Zh)) - 1) = a⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hn, pow_card_eq_one']
      rwa [e] at h }

@[expose] def Dmat : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4 :=
  Matrix.of fun i => vec6 (#[2, 4, 16, 128, 256, 1024][(i : ℕ)]!)

@[expose] def Dinv : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4 :=
  Matrix.of fun i => vec6 (#[3, 4, 16, 192, 256, 1024][(i : ℕ)]!)

theorem Dmat_mul_Dinv : Dmat * Dinv = 1 := by decide +kernel

theorem Dinv_mul_Dmat : Dinv * Dmat = 1 := by decide +kernel

theorem Dmat_cube : Dmat * Dmat * Dmat = 1 := by decide +kernel

theorem Dinv_gram : Dinv * hGram * (barM Dinv)ᵀ = hGram := by decide +kernel

theorem Dmat_gram : Dmat * hGram * (barM Dmat)ᵀ = hGram := by decide +kernel

theorem Dinv_b6Mat_Dmat : ∀ k : Fin 17, (k : ℕ) = 0 ∨ (k : ℕ) = 6 ∨ (k : ℕ) = 7 ∨
    (k : ℕ) = 8 ∨ (k : ℕ) = 9 ∨ (k : ℕ) = 16 → Dinv * b6Mat k * Dmat = b6Mat k := by
  decide +kernel

theorem Dinv_b6Mat_four_Dmat :
    Dinv * b6Mat 4 * Dmat = Matrix.scalar (Fin 6) (⟨3⟩ : CFSG.Fischer.F4) *
      (b6Mat 2 * b6Mat 1 * b6Mat 1 * b6Mat 4) := by
  decide +kernel

@[expose] def DGL : GL (Fin 6) CFSG.Fischer.F4 := ⟨Dmat, Dinv, Dmat_mul_Dinv, Dinv_mul_Dmat⟩

theorem gram_mul_right {G : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4}
    (hG : G * hGram * (barM G)ᵀ = hGram) (X : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) :
    G * (hGram * ((barM G)ᵀ * X)) = hGram * X := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hG]

theorem conj_mem_SUh {G : GL (Fin 6) CFSG.Fischer.F4}
    (hG : (G : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) * hGram *
      (barM (G : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4))ᵀ = hGram)
    (hG' : ((G⁻¹ : GL (Fin 6) CFSG.Fischer.F4) : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) * hGram *
      (barM ((G⁻¹ : GL (Fin 6) CFSG.Fischer.F4) : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4))ᵀ = hGram)
    {A : GL (Fin 6) CFSG.Fischer.F4} (hA : A ∈ SUh) : G⁻¹ * A * G ∈ SUh := by
  rw [mem_SUh_iff_gram] at hA ⊢
  obtain ⟨hdet, hgram⟩ := hA
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet, mul_one,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  · rw [Units.val_mul, Units.val_mul, barM_mul, barM_mul, Matrix.transpose_mul,
      Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [gram_mul_right hG, gram_mul_right (by simpa only [Matrix.mul_assoc] using hgram)]
    simpa only [Matrix.mul_assoc] using hG'

theorem DGL_gram : (DGL : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) * hGram *
    (barM (DGL : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4))ᵀ = hGram := Dmat_gram

theorem DGL_inv_gram : ((DGL⁻¹ : GL (Fin 6) CFSG.Fischer.F4) : Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4) *
    hGram * (barM ((DGL⁻¹ : GL (Fin 6) CFSG.Fischer.F4) :
      Matrix (Fin 6) (Fin 6) CFSG.Fischer.F4))ᵀ = hGram := Dinv_gram

@[expose] noncomputable def conjDSU : SUh ≃* SUh where
  toFun A := ⟨DGL⁻¹ * A * DGL, conj_mem_SUh DGL_gram DGL_inv_gram A.2⟩
  invFun A := ⟨DGL⁻¹⁻¹ * A * DGL⁻¹,
    conj_mem_SUh DGL_inv_gram (by rw [inv_inv]; exact DGL_gram) A.2⟩
  left_inv A := Subtype.ext (by simp [mul_assoc])
  right_inv A := Subtype.ext (by simp [mul_assoc])
  map_mul' A B := Subtype.ext (by simp [mul_assoc])

theorem coe_conjDSU (A : SUh) : ((conjDSU A : SUh) : GL (Fin 6) CFSG.Fischer.F4) = DGL⁻¹ * A * DGL :=
  rfl

theorem conjDSU_eq_of_mem_Zh {z : SUh} (hz : z ∈ Zh) : conjDSU z = z := by
  obtain ⟨c, hc⟩ := hz
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 6) c * DGL = DGL * Matrix.GeneralLinearGroup.scalar (Fin 6) c :=
    Units.ext (by
      rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
      exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq)
  apply Subtype.ext
  rw [coe_conjDSU, hc, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem map_Zh_conjDSU : Zh.map conjDSU.toMonoidHom = Zh := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, conjDSU_eq_of_mem_Zh hw]
    exact hw
  · intro hz
    exact ⟨z, hz, conjDSU_eq_of_mem_Zh hz⟩

@[expose] noncomputable def deltaU : MulAut (SUh ⧸ Zh) :=
  QuotientGroup.congr Zh Zh conjDSU map_Zh_conjDSU

theorem deltaU_mk (A : SUh) : deltaU (A : SUh ⧸ Zh) = (conjDSU A : SUh ⧸ Zh) := rfl

theorem deltaU_pow_three : deltaU ^ 3 = 1 := by
  refine MulEquiv.ext fun u => ?_
  induction u using QuotientGroup.induction_on with
  | H A =>
  have hD : DGL * DGL * DGL = 1 := Units.ext Dmat_cube
  have e : conjDSU (conjDSU (conjDSU A)) = A := by
    apply Subtype.ext
    rw [coe_conjDSU, coe_conjDSU, coe_conjDSU]
    calc DGL⁻¹ * (DGL⁻¹ * (DGL⁻¹ * (A : GL (Fin 6) CFSG.Fischer.F4) * DGL) * DGL) * DGL =
        (DGL * DGL * DGL)⁻¹ * A * (DGL * DGL * DGL) := by group
      _ = A := by rw [hD, inv_one, one_mul, mul_one]
  rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, deltaU_mk, deltaU_mk,
    deltaU_mk, e, MulAut.one_apply]

theorem b6N_eq {k : Fin 17} (hk : (k : ℕ) ≠ 5) : b6N k = b6Mat k := by
  rw [b6N, barPowM, b6Frob_eq_zero k hk, ite_eq_left rfl]

theorem conjDSU_b6SU {k : Fin 17} (hk : (k : ℕ) = 0 ∨ (k : ℕ) = 6 ∨ (k : ℕ) = 7 ∨
    (k : ℕ) = 8 ∨ (k : ℕ) = 9 ∨ (k : ℕ) = 16) : conjDSU (b6SU k) = b6SU k := by
  have h5 : (k : ℕ) ≠ 5 := by omega
  apply Subtype.ext
  apply Units.ext
  rw [coe_conjDSU, Units.val_mul, Units.val_mul, coe_b6SU, b6N_eq h5]
  exact Dinv_b6Mat_Dmat k hk

theorem uOf_of_lt {k : ℕ} (hk : k < 17) : uOf k = (b6SU ⟨k, hk⟩ : SUh ⧸ Zh) := by
  rw [uOf, dite_eq_left hk]

theorem deltaU_uOf_fixed {k : ℕ} (hk : k = 0 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) :
    deltaU (uOf k) = uOf k := by
  have hk17 : k < 17 := by omega
  rw [uOf_of_lt hk17, deltaU_mk, conjDSU_b6SU (k := ⟨k, hk17⟩) hk]

theorem scalar_omega2_mem : (⟨Matrix.GeneralLinearGroup.scalar (Fin 6)
    (Units.mk0 (⟨3⟩ : CFSG.Fischer.F4) (by decide)), scalar_mem_SUh _⟩ : SUh) ∈ Zh :=
  ⟨_, rfl⟩

theorem deltaU_uOf_four : deltaU (uOf 4) = uWord [2, 1, 1, 4] := by
  set z : SUh := ⟨Matrix.GeneralLinearGroup.scalar (Fin 6)
    (Units.mk0 (⟨3⟩ : CFSG.Fischer.F4) (by decide)), scalar_mem_SUh _⟩ with hz
  have e : conjDSU (b6SU 4) = z * (b6SU 2 * b6SU 1 * b6SU 1 * b6SU 4) := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_conjDSU, Units.val_mul, Units.val_mul, coe_b6SU, b6N_eq (by decide)]
    simp only [hz, Subgroup.coe_mul, Units.val_mul, coe_b6SU, b6N_eq (show ((2 : Fin 17) : ℕ) ≠ 5
      by decide), b6N_eq (show ((1 : Fin 17) : ℕ) ≠ 5 by decide),
      b6N_eq (show ((4 : Fin 17) : ℕ) ≠ 5 by decide), Matrix.GeneralLinearGroup.coe_scalar]
    exact Dinv_b6Mat_four_Dmat
  have hz1 : (z : SUh ⧸ Zh) = 1 := (QuotientGroup.eq_one_iff z).2 scalar_omega2_mem
  rw [uOf_of_lt (by norm_num : 4 < 17), deltaU_mk]
  rw [show (⟨4, by norm_num⟩ : Fin 17) = 4 from rfl, e, QuotientGroup.mk_mul, hz1, one_mul]
  simp [uWord, uOf_of_lt, mul_assoc]

theorem deltaU_letters : ∀ k, (k = 0 ∨ k = 4 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 16) →
    deltaU.toMonoidHom (uOf k) = uWord (deltaLetter k) := by
  intro k hk
  rw [MulEquiv.coe_toMonoidHom]
  by_cases h4 : k = 4
  · subst h4
    rw [deltaU_uOf_four]
    rfl
  · rw [deltaU_uOf_fixed (by omega), deltaLetter, ite_eq_right h4, uWord_singleton]

theorem not_isTwist_deltaU : ¬ IsTwist deltaU := by
  rintro ⟨A, hσ, hA⟩
  exact no_twist_of_delta (β := deltaU.toMonoidHom) deltaU_letters (A := A) (fun u x => hA u x) hσ

set_option maxHeartbeats 1000000 in
theorem isTwist_conj (v : SUh ⧸ Zh) : IsTwist (MulAut.conj v) := by
  refine ⟨rhoU v⁻¹, rhoU_sigmaP _, fun u x => ?_⟩
  have h : rhoU (MulAut.conj v u) = rhoU v⁻¹ * rhoU u * rhoU v := by
    rw [MulAut.conj_apply, rhoU_mul, rhoU_mul, mul_assoc]
  have h1 : rhoU v * rhoU v⁻¹ = 1 := by rw [← rhoU_mul, inv_mul_cancel, rhoU_one]
  calc rhoU v⁻¹ (rhoU u x) = (rhoU v⁻¹ * rhoU u * (rhoU v * rhoU v⁻¹)) x := by
        rw [h1, mul_one]; rfl
    _ = rhoU (MulAut.conj v u) (rhoU v⁻¹ x) := by rw [h, ← mul_assoc]; rfl

theorem mk_deltaU_not_mem : (QuotientGroup.mk deltaU : Outer (SUh ⧸ Zh)) ∉ twistOuter := by
  rintro ⟨β, hβ, hβt⟩
  obtain ⟨v, hv⟩ : β⁻¹ * deltaU ∈ inner (SUh ⧸ Zh) := QuotientGroup.eq.1 hβ
  have e : deltaU = β * MulAut.conj v := by rw [hv, mul_inv_cancel_left]
  exact not_isTwist_deltaU (e ▸ isTwist_mul hβt (isTwist_conj v))

theorem card_twistOuter_le_two : Nat.card twistOuter ≤ 2 :=
  CFSG.EvenSmallLie.UnitarySix.card_le_two_of_not_mem card_outer_U twistOuter
    (by rw [← QuotientGroup.mk_pow, deltaU_pow_three, QuotientGroup.mk_one]) mk_deltaU_not_mem

theorem inl_range_normal :
    (SemidirectProduct.inl : SUh ⧸ Zh →* SigmaU6).range.Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

attribute [local instance] inl_range_normal

@[expose] noncomputable def inlEquiv : (SUh ⧸ Zh) ≃* (SemidirectProduct.inl :
    SUh ⧸ Zh →* SigmaU6).range :=
  MonoidHom.ofInjective SemidirectProduct.inl_injective

@[expose] noncomputable def conjU : P1 →* MulAut (SUh ⧸ Zh) :=
  (MulAut.congr inlEquiv).symm.toMonoidHom.comp
    (MulAut.conjNormal.comp (phiU.toMonoidHom.comp p1Proj))

theorem inl_conjU (p : P1) (u : SUh ⧸ Zh) :
    SemidirectProduct.inl (conjU p u) =
      phiU (p1Proj p) * SemidirectProduct.inl u * (phiU (p1Proj p))⁻¹ := by
  have h := congrArg Subtype.val (inlEquiv.apply_symm_apply
    (MulAut.conjNormal (phiU (p1Proj p)) (inlEquiv u)))
  exact h

theorem conjU_of_mem {q : P1} (hq : q ∈ commutator P1) :
    conjU q = MulAut.conj (piU ⟨q, hq⟩) := by
  refine MulEquiv.ext fun u => ?_
  have h : (SemidirectProduct.inl (conjU q u) : SigmaU6) =
      SemidirectProduct.inl (MulAut.conj (piU ⟨q, hq⟩) u) := by
    rw [inl_conjU, MulAut.conj_apply, map_mul, map_mul, map_inv, inl_piU]
  exact SemidirectProduct.inl_injective h

set_option maxHeartbeats 1000000 in
theorem isTwist_conjU (p : P1) : IsTwist (conjU p) := by
  set g : Usig := p1Proj p with hg
  have hρ : ∀ u, rhoU (conjU p u) = perpEnd g⁻¹ * rhoU u * perpEnd g := fun u => by
    have e : phiU.symm (SemidirectProduct.inl (conjU p u)) =
        g * phiU.symm (SemidirectProduct.inl u) * g⁻¹ := by
      rw [inl_conjU, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [rhoU, rhoU, e, perpEnd_mul, perpEnd_mul, mul_assoc]
  have h1 : perpEnd g * perpEnd g⁻¹ = 1 := by rw [← perpEnd_mul, inv_mul_cancel, perpEnd_one]
  refine ⟨perpEnd g⁻¹, perpEnd_sigmaP _, fun u x => ?_⟩
  calc perpEnd g⁻¹ (rhoU u x) = (perpEnd g⁻¹ * rhoU u * (perpEnd g * perpEnd g⁻¹)) x := by
        rw [h1, mul_one]; rfl
    _ = rhoU (conjU p u) (perpEnd g⁻¹ x) := by rw [hρ, ← mul_assoc]; rfl

theorem eq_one_of_commute_inl (t : SigmaU6)
    (h : ∀ u : SUh ⧸ Zh, t * SemidirectProduct.inl u = SemidirectProduct.inl u * t) : t = 1 := by
  have hθ : ∀ u : SUh ⧸ Zh, thetaEquiv (SemidirectProduct.inl u) =
      SemidirectProduct.inl (Unitary.psiQ u) := fun u => by
    change theta ⟨u, Multiplicative.ofAdd 0⟩ = _
    rw [theta_mk, ite_eq_left rfl, mul_one]
    rfl
  have hc : ∀ q : CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hF4 6,
      thetaEquiv t * SemidirectProduct.inl q = SemidirectProduct.inl q * thetaEquiv t := fun q => by
    obtain ⟨u, rfl⟩ := Unitary.psiQ.surjective q
    rw [← hθ, ← map_mul, ← map_mul, h]
  exact thetaEquiv.injective ((eq_one_of_forall_commute _ hc).trans (map_one _).symm)

theorem mk_conjU_ne_one {j : P1} (hj : j ∉ commutator P1) :
    (QuotientGroup.mk (conjU j) : Outer (SUh ⧸ Zh)) ≠ 1 := by
  intro h
  obtain ⟨v, hv⟩ := (QuotientGroup.eq_one_iff _).1 h
  have ht : ∀ u : SUh ⧸ Zh, ((SemidirectProduct.inl v)⁻¹ * phiU (p1Proj j)) *
      SemidirectProduct.inl u =
      SemidirectProduct.inl u * ((SemidirectProduct.inl v)⁻¹ * phiU (p1Proj j)) := fun u => by
    have e := inl_conjU j u
    rw [← hv, MulAut.conj_apply, map_mul, map_mul, map_inv] at e
    have e' : phiU (p1Proj j) * SemidirectProduct.inl u =
        SemidirectProduct.inl v * SemidirectProduct.inl u * (SemidirectProduct.inl v)⁻¹ *
          phiU (p1Proj j) := by
      rw [e, inv_mul_cancel_right]
    rw [mul_assoc, e']
    group
  have h1 := eq_one_of_commute_inl _ ht
  have hs : phiU (p1Proj j) = SemidirectProduct.inl v := (inv_mul_eq_one.1 h1).symm
  apply hj
  rw [mem_commutator_P1_iff, frobP1_apply, hs]
  rfl
theorem twistOuter_cases {j : P1} (hj : j ∉ commutator P1) {o : Outer (SUh ⧸ Zh)}
    (ho : o ∈ twistOuter) : o = 1 ∨ o = QuotientGroup.mk (conjU j) := by
  by_contra hne
  push Not at hne
  have hj1 := mk_conjU_ne_one hj
  have hsub : ({1, QuotientGroup.mk (conjU j), o} : Set (Outer (SUh ⧸ Zh))) ⊆ twistOuter := by
    rintro x (rfl | rfl | rfl)
    · exact twistOuter.one_mem
    · exact ⟨conjU j, rfl, isTwist_conjU j⟩
    · exact ho
  have hcard : ({1, QuotientGroup.mk (conjU j), o} : Set (Outer (SUh ⧸ Zh))).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
      rintro (h | h)
      · exact hj1 h.symm
      · exact hne.1 h.symm), Set.ncard_pair (Ne.symm hne.2)]
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, ← Nat.card_coe_set_eq] at h3
  have h2 := card_twistOuter_le_two
  change Nat.card (twistOuter : Set (Outer (SUh ⧸ Zh))) ≤ 2 at h2
  omega

end CFSG.EvenSmallLie.TwoE6.Stroth23Inner

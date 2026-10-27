module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseAMon
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseANT
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALinRed

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem relIndex_map_range_dvd {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (M : Subgroup G) : (M.map f).relIndex f.range ∣ M.index := by
  have h : (M.map f).subgroupOf f.range = M.map f.rangeRestrict := by
    ext ⟨y, hy⟩
    constructor
    · intro h1
      obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 h1)
      exact ⟨m, hm, Subtype.ext hmy⟩
    · rintro ⟨m, hm, h2⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨m, hm, congrArg Subtype.val h2⟩
  rw [Subgroup.relIndex, h]
  exact Subgroup.index_map_dvd (H := M) f.rangeRestrict_surjective


variable {K : Type} [Field K] {p : ℕ}

theorem fieldAut_conj_conjAut (σ : K ≃+* K) (g : GL (Fin p) K) :
    fieldAut p K σ * conjAut p K g * (fieldAut p K σ)⁻¹ =
      conjAut p K (GeneralLinearGroup.map (σ : K →+* K) g) :=
  (standard_automorphism_transport (K := K) (n := p)).2.2.1 σ g

theorem fieldDual_conj_conjAut (σ : K ≃+* K) (g : GL (Fin p) K) :
    (fieldAut p K σ * dualAut p K) * conjAut p K g * (fieldAut p K σ * dualAut p K)⁻¹ =
      conjAut p K
        (GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose g)) := by
  obtain ⟨-, -, -, hdd, h5, -⟩ := standard_automorphism_transport (K := K) (n := p)
  have hinv : (dualAut p K)⁻¹ = dualAut p K := inv_eq_of_mul_eq_one_right hdd
  rw [_root_.mul_inv_rev, hinv, ← fieldAut_conj_conjAut, ← h5 g]
  group

theorem map_diagGL (σ : K ≃+* K) (d : Fin p → Kˣ) :
    GeneralLinearGroup.map (σ : K →+* K) (diagGL p K d) =
      diagGL p K (fun i => Units.map (σ : K →* K) (d i)) := by
  apply Units.ext
  change (Matrix.diagonal (fun i => (d i : K))).map σ =
    Matrix.diagonal (fun i => ((Units.map (σ : K →* K) (d i) : Kˣ) : K))
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h]

theorem inverseTranspose_diagGL (d : Fin p → Kˣ) :
    GeneralLinearGroup.inverseTranspose (diagGL p K d) = diagGL p K (fun i => (d i)⁻¹) := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose]
  have : (diagGL p K d)⁻¹ = diagGL p K (fun i => (d i)⁻¹) := by
    rw [← map_inv]
    rfl
  rw [this, diagGL_val, Matrix.diagonal_transpose]

theorem map_rotGL (σ : K ≃+* K) :
    GeneralLinearGroup.map (σ : K →+* K) (rotGL p K) = rotGL p K := by
  apply Units.ext
  change ((rotGL p K : GL (Fin p) K) : Matrix (Fin p) (Fin p) K).map σ = _
  rw [rotGL_val]
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem inverseTranspose_rotGL : GeneralLinearGroup.inverseTranspose (rotGL p K) = rotGL p K := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose]
  have : ((rotGL p K)⁻¹ : GL (Fin p) K) =
      (Matrix.permMatrixHom (n := Fin p) (R := K)).toHomUnits (finRotate p)⁻¹ := by
    rw [rotGL, ← map_inv]
  rw [this]
  change (((finRotate p)⁻¹⁻¹).permMatrix K)ᵀ = ((finRotate p)⁻¹).permMatrix K
  rw [Matrix.transpose_permMatrix, inv_inv]


theorem map_eq_of_mem_monoQ (σ : K ≃+* K) (Q : Subgroup Kˣ)
    (hfix : ∀ x ∈ Q, Units.map (σ : K →* K) x = x) (hp : 2 ≤ p) :
    ∀ g ∈ monoQ (p := p) (K := K) Q, GeneralLinearGroup.map (σ : K →+* K) g = g := by
  have hle : monoQ (p := p) (K := K) Q ≤
      (GeneralLinearGroup.map (σ : K →+* K)).eqLocus (MonoidHom.id (GL (Fin p) K)) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      show GeneralLinearGroup.map (σ : K →+* K) (diagQ Q c) = diagQ Q c
      have h1 : diagQ Q c = diagGL p K (fun i => ((c i : Q) : Kˣ)) := rfl
      rw [h1, map_diagGL]
      congr 1
      funext i
      exact hfix _ (c i).2
    · rw [Subgroup.zpowers_le]
      exact map_rotGL σ
  exact fun g hg => hle hg

theorem map_dual_eq_of_mem_monoQ (σ : K ≃+* K) (Q : Subgroup Kˣ)
    (hfix : ∀ x ∈ Q, (Units.map (σ : K →* K) x)⁻¹ = x) :
    ∀ g ∈ monoQ (p := p) (K := K) Q,
      GeneralLinearGroup.map (σ : K →+* K) (GeneralLinearGroup.inverseTranspose g) = g := by
  have hle : monoQ (p := p) (K := K) Q ≤
      ((GeneralLinearGroup.map (σ : K →+* K)).comp
        (GeneralLinearGroup.inverseTranspose : MulAut (GL (Fin p) K)).toMonoidHom).eqLocus
          (MonoidHom.id (GL (Fin p) K)) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨c, rfl⟩
      show GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose (diagQ Q c)) = diagQ Q c
      have h1 : diagQ Q c = diagGL p K (fun i => ((c i : Q) : Kˣ)) := rfl
      rw [h1, inverseTranspose_diagGL, map_diagGL]
      congr 1
      funext i
      rw [map_inv]
      exact hfix _ (c i).2
    · rw [Subgroup.zpowers_le]
      show GeneralLinearGroup.map (σ : K →+* K)
        (GeneralLinearGroup.inverseTranspose (rotGL p K)) = rotGL p K
      rw [inverseTranspose_rotGL, map_rotGL]
  exact fun g hg => hle hg


theorem det_map_gl (σ : K ≃+* K) (y : GL (Fin p) K) :
    GeneralLinearGroup.det (GeneralLinearGroup.map (σ : K →+* K) y) =
      Units.map (σ : K →* K) (GeneralLinearGroup.det y) := by
  refine Units.ext ?_
  rw [GeneralLinearGroup.val_det_apply, Units.coe_map, GeneralLinearGroup.val_det_apply]
  change Matrix.det ((σ : K →+* K).mapMatrix ((y : GL (Fin p) K) : Matrix (Fin p) (Fin p) K)) = _
  rw [← RingHom.map_det]
  rfl

theorem det_relation_field [Finite K] (hn : 3 ≤ p) (σ : K ≃+* K) (y : GL (Fin p) K)
    (hc : fieldAut p K σ * conjAut p K y = conjAut p K y * fieldAut p K σ) :
    ∃ l : Kˣ, (Units.map (σ : K →* K) (GeneralLinearGroup.det y)) ^ (1 : ℤ) =
      l ^ p * GeneralLinearGroup.det y := by
  have h1 : fieldAut p K σ * conjAut p K y * (fieldAut p K σ)⁻¹ = conjAut p K y := by
    rw [mul_inv_eq_iff_eq_mul, hc]
  rw [fieldAut_conj_conjAut] at h1
  have h2 : conjAut p K (y⁻¹ * GeneralLinearGroup.map (σ : K →+* K) y) * fieldAut p K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨-, c, hc'⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h2
  have h3 := congrArg GeneralLinearGroup.det hc'
  rw [GeneralLinearGroup.det_scalar, map_mul, map_inv, det_map_gl, Fintype.card_fin] at h3
  refine ⟨c, ?_⟩
  rw [zpow_one, h3, mul_comm (GeneralLinearGroup.det y)⁻¹, mul_assoc, inv_mul_cancel, mul_one]

theorem det_relation_fieldDual [Finite K] (hn : 3 ≤ p) (σ : K ≃+* K) (y : GL (Fin p) K)
    (hc : (fieldAut p K σ * dualAut p K) * conjAut p K y =
      conjAut p K y * (fieldAut p K σ * dualAut p K)) :
    ∃ l : Kˣ, (Units.map (σ : K →* K) (GeneralLinearGroup.det y)) ^ (-1 : ℤ) =
      l ^ p * GeneralLinearGroup.det y := by
  have h1 : (fieldAut p K σ * dualAut p K) * conjAut p K y *
      (fieldAut p K σ * dualAut p K)⁻¹ = conjAut p K y := by
    rw [mul_inv_eq_iff_eq_mul, hc]
  rw [fieldDual_conj_conjAut] at h1
  have h2 : conjAut p K (y⁻¹ * GeneralLinearGroup.map (σ : K →+* K)
      (GeneralLinearGroup.inverseTranspose y)) * fieldAut p K 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, h1, inv_mul_cancel]
  obtain ⟨-, c, hc'⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ 1 h2
  have h3 := congrArg GeneralLinearGroup.det hc'
  rw [GeneralLinearGroup.det_scalar, map_mul, map_inv, det_map_gl, det_inverseTranspose',
    Fintype.card_fin, map_inv] at h3
  refine ⟨c, ?_⟩
  rw [_root_.zpow_neg_one, h3, mul_comm (GeneralLinearGroup.det y)⁻¹, mul_assoc,
    inv_mul_cancel, mul_one]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA Subgroup Matrix
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem kd292StdSylow_holds : KD292StdSylow := by
  intro p K _ _ hp hp5 y hdet S hS2 hSnf hSc
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ p := by omega
  have hdU : ∀ b : Kˣ, b ^ p ≠ GeneralLinearGroup.det y := by
    intro b hb
    exact hdet (b : K) (by rw [← Units.val_pow_eq_pow_val, hb, GeneralLinearGroup.val_det_apply])
  have hpN : p ∣ Nat.card Kˣ := by
    by_contra hnd
    have hcop : Nat.Coprime (Nat.card Kˣ) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    obtain ⟨b, hb⟩ := (powCoprime hcop).surjective (GeneralLinearGroup.det y)
    exact hdU b (by simpa using hb)
  have hpK : p ∣ Nat.card K - 1 := by rwa [Nat.card_units] at hpN
  obtain ⟨Q⟩ : Nonempty (Sylow p Kˣ) := inferInstance
  refine ⟨(monoQ (p := p) (K := K) (Q : Subgroup Kˣ)).map (conjAut p K), ?_, ?_, ?_, ?_⟩
  · rw [linearAutGroup_eq_range]
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  · exact (isPGroup_monoQ hp.two_le Q.isPGroup').map _
  · rw [linearAutGroup_eq_range]
    intro h
    exact not_dvd_index_monoQ hp2 Q hpK (h.trans (relIndex_map_range_dvd _ _))
  · intro s hs r hr
    obtain ⟨σ, ε, hε, hsnf⟩ := hSnf s hs
    obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    have hj : 1 ≤ k + 1 := by omega
    have hsj : s ^ (2 ^ (k + 1)) = 1 := by rw [pow_succ, pow_mul, hk', one_pow]
    have hc := hSc s hs
    have hdd : dualAut p K * dualAut p K = 1 :=
      (standard_automorphism_transport (K := K) (n := p)).2.2.2.1
    have hfd : Commute (fieldAut p K σ) (dualAut p K) := (dualAut_mul_fieldAut σ).symm
    have hinj : ∀ τ : K ≃+* K, fieldAut p K τ = 1 → τ = 1 := fun τ hτ =>
      (eq_one_of_conjAut_mul_fieldAut_eq_one hn3 1 τ (by rw [map_one, one_mul]; exact hτ)).1
    obtain rfl | rfl : ε = 0 ∨ ε = 1 := by omega
    ·
      rw [pow_zero, mul_one] at hsnf
      subst hsnf
      have hσ : σ ^ (2 ^ (k + 1)) = 1 := hinj _ (by rw [map_pow]; exact hsj)
      obtain ⟨l, hl⟩ := det_relation_field hn3 σ y hc
      have hfix := trivial_of_field_aut hp hp2 Q σ hj hσ (Or.inl rfl) hdU ⟨l, hl⟩
      have hg' := map_eq_of_mem_monoQ σ (Q : Subgroup Kˣ)
        (fun x hx => by simpa using hfix x hx) hp.two_le g hg
      have h1 := fieldAut_conj_conjAut σ g
      rw [hg'] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1)
    ·
      rw [pow_one] at hsnf
      subst hsnf
      have hδ : dualAut p K ^ (2 ^ (k + 1)) = 1 := by
        rw [pow_succ', pow_mul, pow_two, hdd, one_pow]
      have hσ : σ ^ (2 ^ (k + 1)) = 1 := by
        apply hinj
        rw [map_pow]
        rwa [hfd.mul_pow, hδ, mul_one] at hsj
      obtain ⟨l, hl⟩ := det_relation_fieldDual hn3 σ y hc
      have hfix := trivial_of_field_aut hp hp2 Q σ hj hσ (Or.inr rfl) hdU ⟨l, hl⟩
      have hg' := map_dual_eq_of_mem_monoQ σ (Q : Subgroup Kˣ)
        (fun x hx => by simpa using hfix x hx) g hg
      have h1 := fieldDual_conj_conjAut σ g
      rw [hg'] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1

theorem kd292CaseALin_of_lang (h1 : KD292LangConjInput) : KD292CaseALin :=
  kd292CaseALin_of_conj_std h1 kd292StdSylow_holds

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

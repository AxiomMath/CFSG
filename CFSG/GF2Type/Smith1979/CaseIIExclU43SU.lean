module

public import CFSG.GF2Type.Smith1979.CaseIIExclU43Core
public import CFSG.GF2Type.Smith1979.CaseIIExclU43Lin
public import CFSG.Open.StatedDefs

public section

namespace CFSG.GF2Type.Smith1979.Case2.U43SU

open CFSG.Open Matrix CFSG.GF2Type.Smith1979.Case2.U43Grp

variable {K : Type} [Field K]

theorem det_eq_one_of_mem_stated {n q : ℕ} {g : GL (Fin n) K} (hg : g ∈ StatedSU n q K) :
    (g : Matrix (Fin n) (Fin n) K).det = 1 := by
  have hle : StatedSU n q K ≤ (Matrix.GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
    unfold StatedSU
    rw [Subgroup.closure_le]
    intro A hA
    rw [SetLike.mem_coe, MonoidHom.mem_ker, ← Units.val_eq_one,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact hA.1
  have h := hle hg
  rw [MonoidHom.mem_ker, ← Units.val_eq_one, Matrix.GeneralLinearGroup.val_det_apply] at h
  exact h

theorem scalar_mem_stated (c : Kˣ) (hc : (c : K) ^ 4 = 1) :
    Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ StatedSU 4 (3 ^ 1) K := by
  unfold StatedSU
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal, hc]
  · have h3 : (c : K) ^ 3 * (c : K) = 1 := by
      rw [show (c : K) ^ 3 * (c : K) = (c : K) ^ 4 by ring]
      exact hc
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_map,
      Matrix.diagonal_mul_diagonal, h3, Pi.one_def]

theorem scalar_comm (c : Kˣ) (g : GL (Fin 4) K) :
    Matrix.GeneralLinearGroup.scalar (Fin 4) c * g =
      g * Matrix.GeneralLinearGroup.scalar (Fin 4) c := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 4) c ∈ Subgroup.center (GL (Fin 4) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact MonoidHom.mem_range.2 ⟨c, rfl⟩
  exact ((Subgroup.mem_center_iff.1 hz) g).symm

@[expose] noncomputable def stateψ {X : Type} [Group X]
    (e : X ≃* StatedProj (StatedSU 4 (3 ^ 1) K)) : StatedSU 4 (3 ^ 1) K →* X :=
  e.symm.toMonoidHom.comp (QuotientGroup.mk' _)

theorem stateψ_surjective {X : Type} [Group X] (e : X ≃* StatedProj (StatedSU 4 (3 ^ 1) K)) :
    Function.Surjective (stateψ e) := by
  intro x
  obtain ⟨q, hq⟩ := QuotientGroup.mk'_surjective _ (e x)
  refine ⟨q, ?_⟩
  show e.symm (QuotientGroup.mk' _ q) = x
  rw [hq, MulEquiv.symm_apply_apply]

theorem stateψ_eq_one_iff {X : Type} [Group X] (e : X ≃* StatedProj (StatedSU 4 (3 ^ 1) K))
    (g : StatedSU 4 (3 ^ 1) K) :
    stateψ e g = 1 ↔
      ∃ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin 4) c = (g : GL (Fin 4) K) := by
  have h1 : stateψ e g = 1 ↔
      g ∈ (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (3 ^ 1) K) := by
    rw [stateψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  rw [h1, Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range

theorem two_ne_zero_of_card_nine [Finite K] (hK : Nat.card K = 9) : (2 : K) ≠ 0 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card] at hK
  obtain ⟨p, hchar, n, hpp, hcard⟩ := FiniteField.card' K
  rw [hK] at hcard
  have hdvd : p ∣ 9 := by
    rw [hcard]
    exact dvd_pow_self p (PNat.ne_zero n)
  have hp3 : p = 3 := by
    have h3 : p ∣ 3 := hpp.dvd_of_dvd_pow (show p ∣ 3 ^ 2 by norm_num; exact hdvd)
    exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 h3
  subst hp3
  intro h
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K 3] at h2
  norm_num at h2

theorem exists_sqrt_neg_one [Finite K] (hK : Nat.card K = 9) : ∃ i : K, i * i = -1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hsq : IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hK]
    norm_num
  obtain ⟨r, hr⟩ := hsq
  exact ⟨r, hr.symm⟩

@[expose] def negSU (K : Type) [Field K] : StatedSU 4 (3 ^ 1) K :=
  ⟨Matrix.GeneralLinearGroup.scalar (Fin 4) (-1),
    scalar_mem_stated (-1) (by norm_num)⟩

@[expose] noncomputable def liftSetup [Finite K] (hK : Nat.card K = 9) {X : Type} [Group X]
    (e : X ≃* StatedProj (StatedSU 4 (3 ^ 1) K)) : LiftSetup (StatedSU 4 (3 ^ 1) K) X where
  ψ := stateψ e
  lift := Function.surjInv (stateψ_surjective e)
  hlift := Function.surjInv_eq (stateψ_surjective e)
  neg := negSU K
  neg_ne_one := by
    intro h
    have hG : (negSU K : GL (Fin 4) K) = 1 := congrArg Subtype.val h
    have h' : ((negSU K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hG, Units.val_one]
    have h0 := congrFun (congrFun h' 0) 0
    apply two_ne_zero_of_card_nine hK
    simp [negSU, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h0
    linear_combination -h0
  neg_mul_self := by
    apply Subtype.ext
    show Matrix.GeneralLinearGroup.scalar (Fin 4) (-1) *
      Matrix.GeneralLinearGroup.scalar (Fin 4) (-1) = 1
    rw [← map_mul, neg_mul_neg, mul_one, map_one]
  ker_neg := by
    rw [stateψ_eq_one_iff]
    exact ⟨-1, rfl⟩
  ker_central := by
    intro z hz g
    obtain ⟨c, hc⟩ := (stateψ_eq_one_iff e z).1 hz
    apply Subtype.ext
    show (z : GL (Fin 4) K) * (g : GL (Fin 4) K) = (g : GL (Fin 4) K) * (z : GL (Fin 4) K)
    rw [← hc]
    exact scalar_comm c (g : GL (Fin 4) K)
  ker_pow_four := by
    intro z hz
    obtain ⟨c, hc⟩ := (stateψ_eq_one_iff e z).1 hz
    have hdet := det_eq_one_of_mem_stated z.2
    rw [← hc] at hdet
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
    have hc4 : (c : K) ^ 4 = 1 := by simpa using hdet
    apply Subtype.ext
    show (z : GL (Fin 4) K) ^ 4 = 1
    rw [← hc, ← map_pow]
    have hc4' : c ^ 4 = 1 := Units.ext (by simpa using hc4)
    rw [hc4', map_one]
  ker_sq := by
    intro z hz hzz
    obtain ⟨c, hc⟩ := (stateψ_eq_one_iff e z).1 hz
    have hzz' : Matrix.GeneralLinearGroup.scalar (Fin 4) c *
        Matrix.GeneralLinearGroup.scalar (Fin 4) c = 1 := by
      rw [hc]
      have := congrArg Subtype.val hzz
      simpa using this
    rw [← map_mul] at hzz'
    have hcc : (c : K) * (c : K) = 1 := by
      have := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 0) hzz'
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this
    rcases mul_self_eq_one_iff.1 hcc with h | h
    · left
      have hc1 : c = 1 := Units.ext h
      apply Subtype.ext
      show (z : GL (Fin 4) K) = 1
      rw [← hc, hc1, map_one]
    · right
      have hc1 : c = -1 := Units.ext h
      apply Subtype.ext
      show (z : GL (Fin 4) K) = Matrix.GeneralLinearGroup.scalar (Fin 4) (-1)
      rw [← hc, hc1]
  ker_sqrt := by
    obtain ⟨i, hi⟩ := exists_sqrt_neg_one hK
    have hi0 : i ≠ 0 := by
      intro h0
      rw [h0] at hi
      simp at hi
    have hi4 : i ^ 4 = 1 := by
      calc i ^ 4 = (i * i) * (i * i) := by ring
        _ = 1 := by rw [hi]; norm_num
    refine ⟨⟨Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 i hi0),
      scalar_mem_stated _ hi4⟩, ?_, ?_⟩
    · exact (stateψ_eq_one_iff e _).2 ⟨Units.mk0 i hi0, rfl⟩
    · apply Subtype.ext
      show Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 i hi0) *
        Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 i hi0) =
          Matrix.GeneralLinearGroup.scalar (Fin 4) (-1)
      rw [← map_mul]
      congr 1
      apply Units.ext
      simp [hi]

theorem card_le_eight_stated [Finite K] (hK : Nat.card K = 9)
    (A : Subgroup (StatedSU 4 (3 ^ 1) K))
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1) :
    Nat.card A ≤ 8 := by
  have hA : Nat.card A = Nat.card (A.map (StatedSU 4 (3 ^ 1) K).subtype) :=
    Nat.card_congr (Subgroup.equivMapOfInjective A _ Subtype.val_injective).toEquiv
  rw [hA]
  apply U43Lin.card_le_eight_of_subgroup (two_ne_zero_of_card_nine hK)
  · intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    exact congrArg Subtype.val (hcomm a' ha' b' hb')
  · intro a ha
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    exact congrArg Subtype.val (hsq a' ha')
  · intro a ha
    obtain ⟨a', -, rfl⟩ := Subgroup.mem_map.1 ha
    exact det_eq_one_of_mem_stated a'.2

theorem false_of_stated {X : Type} [Group X] [Finite K] (hK : Nat.card K = 9)
    (e : X ≃* StatedProj (StatedSU 4 (3 ^ 1) K)) {y : X} (hy : orderOf y = 7)
    {S : Subgroup X} (hS2 : ∀ s ∈ S, s * s = 1) (hS8 : Nat.card S = 8)
    (hyS : ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hfpf : ∀ s ∈ S, y * s * y⁻¹ = s → s = 1) : False :=
  LiftSetup.false_of_lift (liftSetup hK e)
    (fun A hc hs => card_le_eight_stated hK A hc hs) hy hS2 hS8 hyS hfpf

end CFSG.GF2Type.Smith1979.Case2.U43SU

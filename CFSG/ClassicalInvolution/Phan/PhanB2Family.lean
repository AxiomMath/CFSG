module

public import CFSG.ClassicalInvolution.Phan.PhanB1Coord
public import CFSG.ClassicalInvolution.Phan.PhanD4Tor

public section

namespace CFSG.ClassicalInvolution.PhanB3

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.ClassicalInvolution.PhanD4 (torusTwo_mul_mul_inv conjDiag_mul conjDiag_one
  conjDiag_two_mul embSUid_two_torus_conj_zero embSUid_zero_torus_conj_two
  conjDiag_embSUid_two conjDiag_embSUid_zero)

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}

variable (C : B2Coord hK F h2) in
structure PhanFamilyB3 (Y : Type) [Group Y] where
  ι : Fin 3 → (Su K p f 2 →* Y)
  θ : Su K p f 3 →* Y
  ϑ : StatedSp 2 F →* Y
  left : θ.comp (embSUid (unitaryInvolution K p f) 2) = ι 0
  right : θ.comp (embSUid (unitaryInvolution K p f) 0) = ι 1
  ℓ_eq : ϑ.comp C.ℓ = ι 1
  s_eq : ϑ.comp C.s = ι 2
  comm : ∀ a b, ι 0 a * ι 2 b = ι 2 b * ι 0 a

variable {C : B2Coord hK F h2} {G : Type} [Group G] (S : PhanFamilyB3 C G)

theorem ι_zero (A : Su K p f 2) :
    S.ι 0 A = S.θ (embSUid (unitaryInvolution K p f) 2 A) :=
  (DFunLike.congr_fun S.left A).symm

theorem ι_one_θ (A : Su K p f 2) :
    S.ι 1 A = S.θ (embSUid (unitaryInvolution K p f) 0 A) :=
  (DFunLike.congr_fun S.right A).symm

theorem ι_one_ϑ (A : Su K p f 2) : S.ι 1 A = S.ϑ (C.ℓ A) :=
  (DFunLike.congr_fun S.ℓ_eq A).symm

theorem ι_two (A : Su K p f 2) : S.ι 2 A = S.ϑ (C.s A) :=
  (DFunLike.congr_fun S.s_eq A).symm

@[expose] noncomputable def tor (i : Fin 3) : normOne (unitaryInvolution K p f) →* G :=
  (S.ι i).comp (torusTwo (unitaryInvolution K p f))

theorem tor_zero_comm_one (x y : normOne (unitaryInvolution K p f)) :
    tor S 0 x * tor S 1 y = tor S 1 y * tor S 0 x := by
  simp only [tor, MonoidHom.comp_apply, ι_zero, ι_one_θ, ← map_mul]
  rw [embSUid_two_torus_comm]

theorem tor_one_comm_two (x y : normOne (unitaryInvolution K p f)) :
    tor S 1 x * tor S 2 y = tor S 2 y * tor S 1 x := by
  simp only [tor, MonoidHom.comp_apply, ι_one_ϑ, ι_two, ← map_mul]
  rw [C.comm_tor]

theorem tor_zero_comm_two (x y : normOne (unitaryInvolution K p f)) :
    tor S 0 x * tor S 2 y = tor S 2 y * tor S 0 x :=
  S.comm _ _

theorem tor_comm (i j : Fin 3) (x y : normOne (unitaryInvolution K p f)) :
    tor S i x * tor S j y = tor S j y * tor S i x := by
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]
    rw [← map_mul, ← map_mul, mul_comm]
  · exact tor_zero_comm_one S x y
  · exact tor_zero_comm_two S x y
  · exact (tor_zero_comm_one S y x).symm
  · simp only [Fin.mk_one, Fin.isValue]
    rw [← map_mul, ← map_mul, mul_comm]
  · exact tor_one_comm_two S x y
  · exact (tor_zero_comm_two S y x).symm
  · exact (tor_one_comm_two S y x).symm
  · simp only [Fin.reduceFinMk, Fin.isValue]
    rw [← map_mul, ← map_mul, mul_comm]

@[expose] noncomputable def chi (i j : Fin 3) (x : normOne (unitaryInvolution K p f)) :
    normOne (unitaryInvolution K p f) :=
  if i = j then x * x
  else if i = 2 ∧ j = 1 then x⁻¹ * x⁻¹
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) then 1
  else x⁻¹

theorem chi_self (i : Fin 3) (x : normOne (unitaryInvolution K p f)) : chi i i x = x * x := by
  simp [chi]

theorem chi_zero_one (x : normOne (unitaryInvolution K p f)) : chi 0 1 x = x⁻¹ := by
  simp [chi]

theorem chi_one_zero (x : normOne (unitaryInvolution K p f)) : chi 1 0 x = x⁻¹ := by
  simp [chi]

theorem chi_one_two (x : normOne (unitaryInvolution K p f)) : chi 1 2 x = x⁻¹ := by
  simp [chi]

theorem chi_two_one (x : normOne (unitaryInvolution K p f)) : chi 2 1 x = x⁻¹ * x⁻¹ := by
  simp [chi]

theorem chi_zero_two (x : normOne (unitaryInvolution K p f)) : chi 0 2 x = 1 := by
  simp [chi]

theorem chi_two_zero (x : normOne (unitaryInvolution K p f)) : chi 2 0 x = 1 := by
  simp [chi]

include hK in
theorem tor_conj_self (i : Fin 3) (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    tor S i x * S.ι i A * (tor S i x)⁻¹ = S.ι i (conjDiag hK ![x * x, 1] A) := by
  show S.ι i (torusTwo (unitaryInvolution K p f) x) * S.ι i A *
    (S.ι i (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul, torusTwo_mul_mul_inv hK]

include hK in
theorem tor_conj_ι (i j : Fin 3) (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    tor S i x * S.ι j A * (tor S i x)⁻¹ = S.ι j (conjDiag hK ![chi i j x, 1] A) := by
  have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
    ext i
    fin_cases i <;> rfl
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, chi_self]
    exact tor_conj_self S 0 x A
  · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, chi_zero_one]
    show S.ι 0 (torusTwo (unitaryInvolution K p f) x) * S.ι 1 A *
      (S.ι 0 (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_zero, ι_one_θ, ι_one_θ, ← map_inv, ← map_mul, ← map_mul,
      embSUid_two_torus_conj_zero hK]
  · simp only [Fin.zero_eta, Fin.reduceFinMk, Fin.isValue, chi_zero_two, h11]
    have hc : tor S 0 x * S.ι 2 A = S.ι 2 A * tor S 0 x := S.comm _ _
    rw [hc, mul_inv_cancel_right, conjDiag_one hK A]
  · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, chi_one_zero]
    show S.ι 1 (torusTwo (unitaryInvolution K p f) x) * S.ι 0 A *
      (S.ι 1 (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_one_θ, ι_zero, ι_zero, ← map_inv, ← map_mul, ← map_mul,
      embSUid_zero_torus_conj_two hK]
  · simp only [Fin.mk_one, Fin.isValue, chi_self]
    exact tor_conj_self S 1 x A
  · simp only [Fin.mk_one, Fin.reduceFinMk, Fin.isValue, chi_one_two]
    show S.ι 1 (torusTwo (unitaryInvolution K p f) x) * S.ι 2 A *
      (S.ι 1 (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_one_ϑ, ι_two, ι_two, ← map_inv, ← map_mul, ← map_mul, C.conj_ℓ_s]
  · simp only [Fin.reduceFinMk, Fin.zero_eta, Fin.isValue, chi_two_zero, h11]
    have hc : tor S 2 x * S.ι 0 A = S.ι 0 A * tor S 2 x := (S.comm _ _).symm
    rw [hc, mul_inv_cancel_right, conjDiag_one hK A]
  · simp only [Fin.reduceFinMk, Fin.mk_one, Fin.isValue, chi_two_one]
    show S.ι 2 (torusTwo (unitaryInvolution K p f) x) * S.ι 1 A *
      (S.ι 2 (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_two, ι_one_ϑ, ι_one_ϑ, ← map_inv, ← map_mul, ← map_mul, C.conj_s_ℓ]
  · simp only [Fin.reduceFinMk, Fin.isValue, chi_self]
    exact tor_conj_self S 2 x A

@[expose] noncomputable def mTor : (Fin 3 → normOne (unitaryInvolution K p f)) →* G :=
  MonoidHom.noncommPiCoprod (fun i => tor S i) (fun i j _ x y => tor_comm S i j x y)

theorem mTor_mulSingle (i : Fin 3) (x : normOne (unitaryInvolution K p f)) :
    mTor S (Pi.mulSingle i x) = tor S i x :=
  MonoidHom.noncommPiCoprod_mulSingle (N := fun _ => normOne (unitaryInvolution K p f))
    (fun i => tor S i) i x

theorem mTor_apply (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    mTor S t = tor S 0 (t 0) * tor S 1 (t 1) * tor S 2 (t 2) := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [ht]
  simp only [map_mul, mTor_mulSingle]

@[expose] noncomputable def rho (j : Fin 3) (t : Fin 3 → normOne (unitaryInvolution K p f)) :
    normOne (unitaryInvolution K p f) :=
  chi 0 j (t 0) * chi 1 j (t 1) * chi 2 j (t 2)

include hK in
theorem mTor_conj_ι (t : Fin 3 → normOne (unitaryInvolution K p f)) (j : Fin 3)
    (A : Su K p f 2) :
    mTor S t * S.ι j A * (mTor S t)⁻¹ = S.ι j (conjDiag hK ![rho j t, 1] A) := by
  rw [mTor_apply]
  set a := tor S 0 (t 0)
  set b := tor S 1 (t 1)
  set c := tor S 2 (t 2)
  have e : a * b * c * S.ι j A * (a * b * c)⁻¹ =
      a * (b * (c * S.ι j A * c⁻¹) * b⁻¹) * a⁻¹ := by group
  rw [e]
  simp only [a, b, c]
  rw [tor_conj_ι S 2 j, tor_conj_ι S 1 j, tor_conj_ι S 0 j,
    ← conjDiag_two_mul, ← conjDiag_two_mul, rho, mul_assoc]

end CFSG.ClassicalInvolution.PhanB3

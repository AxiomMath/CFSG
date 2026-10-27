module

public import CFSG.ClassicalInvolution.Phan.PhanD1Family
public import CFSG.ClassicalInvolution.Phan.Torus
import CFSG.ClassicalInvolution.Phan.Parabolic.Generation

public section

namespace CFSG.ClassicalInvolution.PhanD4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.ClassicalGroups.Unitary
open CFSG.Timmesfeld (edgeD)

section Conj

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  (hK : Nat.card K = (p ^ f) ^ 2)

theorem conjDiag_mul {k : ℕ} (e e' : Fin k → normOne (unitaryInvolution K p f)) (A : Su K p f k) :
    conjDiag hK (e * e') A = conjDiag hK e (conjDiag hK e' A) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  rw [coe_conjDiag_apply, coe_conjDiag_apply, coe_conjDiag_apply]
  simp only [Pi.mul_apply, Subgroup.coe_mul, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val]
  field_simp

theorem conjDiag_one {k : ℕ} (A : Su K p f k) :
    conjDiag hK (1 : Fin k → normOne (unitaryInvolution K p f)) A = A := by
  refine Subtype.ext (Units.ext (Matrix.ext fun x y => ?_))
  rw [coe_conjDiag_apply]
  simp

theorem conjDiag_two_mul (a b : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    conjDiag hK ![a * b, 1] A = conjDiag hK ![a, 1] (conjDiag hK ![b, 1] A) := by
  rw [← conjDiag_mul]
  congr 2
  ext i
  fin_cases i <;> simp

theorem torusTwo_mul_mul_inv (v : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    torusTwo (unitaryInvolution K p f) v * A * (torusTwo (unitaryInvolution K p f) v)⁻¹ =
      conjDiag hK ![v * v, 1] A := by
  have : conjDiag hK ![v * v, 1] = conjDiag hK ![v, v⁻¹] := by
    rw [conjDiag_two hK v v⁻¹, inv_inv]
  rw [this]
  have hd : (fun x => (((![v, v⁻¹] : Fin 2 → normOne (unitaryInvolution K p f)) x : _) : Kˣ)) =
      ![(v : Kˣ), (v : Kˣ)⁻¹] := by
    funext i
    fin_cases i <;> rfl
  refine Subtype.ext ?_
  rw [coe_conjDiag, hd]
  rfl

end Conj


section Cross

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  (hK : Nat.card K = (p ^ f) ^ 2)

theorem embSUid_two_torus_conj_zero (v : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) v) *
        embSUid (unitaryInvolution K p f) 0 A *
        (embSUid (unitaryInvolution K p f) 2 (torusTwo (unitaryInvolution K p f) v))⁻¹ =
      embSUid (unitaryInvolution K p f) 0 (conjDiag hK ![v⁻¹, 1] A) := by
  rw [← map_inv, ← map_inv]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, coe_conjDiag_apply]

theorem embSUid_zero_torus_conj_two (v : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) v) *
        embSUid (unitaryInvolution K p f) 2 A *
        (embSUid (unitaryInvolution K p f) 0 (torusTwo (unitaryInvolution K p f) v))⁻¹ =
      embSUid (unitaryInvolution K p f) 2 (conjDiag hK ![v⁻¹, 1] A) := by
  rw [← map_inv, ← map_inv]
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul, coe_embSUid, coe_torusTwo]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embPair, Matrix.mul_apply, Fin.sum_univ_three, coe_conjDiag_apply] <;>
    field_simp

theorem conjDiag_embSUid_two (e : Fin 3 → normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    conjDiag hK e (embSUid (unitaryInvolution K p f) 2 A) =
      embSUid (unitaryInvolution K p f) 2 (conjDiag hK ![e 0, e 1] A) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [coe_conjDiag_apply]
  simp only [coe_embSUid]
  fin_cases i <;> fin_cases j <;>
    simp [embPair, coe_conjDiag_apply]

theorem conjDiag_embSUid_zero (e : Fin 3 → normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    conjDiag hK e (embSUid (unitaryInvolution K p f) 0 A) =
      embSUid (unitaryInvolution K p f) 0 (conjDiag hK ![e 1, e 2] A) := by
  refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
  rw [coe_conjDiag_apply]
  simp only [coe_embSUid]
  fin_cases i <;> fin_cases j <;>
    simp [embPair, coe_conjDiag_apply]

end Cross

section Tori

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  (hK : Nat.card K = (p ^ f) ^ 2) {G : Type} [Group G] (S : PhanFamilyD4 K p f G)

@[expose] noncomputable def tor (i : Fin 4) : normOne (unitaryInvolution K p f) →* G :=
  (S.ι i).comp (torusTwo (unitaryInvolution K p f))

theorem ι_src (e : Fin 3) (A : Su K p f 2) :
    S.ι (edgeSrc e) A = S.θ e (embSUid (unitaryInvolution K p f) 2 A) :=
  (DFunLike.congr_fun (S.left e) A).symm

theorem ι_tgt (e : Fin 3) (A : Su K p f 2) :
    S.ι (edgeTgt e) A = S.θ e (embSUid (unitaryInvolution K p f) 0 A) :=
  (DFunLike.congr_fun (S.right e) A).symm

theorem tor_comm_edge (e : Fin 3) (x y : normOne (unitaryInvolution K p f)) :
    tor S (edgeSrc e) x * tor S (edgeTgt e) y = tor S (edgeTgt e) y * tor S (edgeSrc e) x := by
  simp only [tor, MonoidHom.comp_apply, ι_src, ι_tgt, ← map_mul]
  rw [embSUid_two_torus_comm]

theorem tor_comm (i j : Fin 4) (x y : normOne (unitaryInvolution K p f)) :
    tor S i x * tor S j y = tor S j y * tor S i x := by
  rcases eq_or_ne i j with rfl | hij
  · rw [← map_mul, ← map_mul, mul_comm]
  by_cases h1 : edgeD 4 i j
  · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff i j).1 h1
    exact tor_comm_edge S e x y
  by_cases h2 : edgeD 4 j i
  · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff j i).1 h2
    exact (tor_comm_edge S e y x).symm
  · exact S.comm i j hij h1 h2 _ _

@[expose] noncomputable def chi (i j : Fin 4) (x : normOne (unitaryInvolution K p f)) :
    normOne (unitaryInvolution K p f) :=
  if i = j then x * x else if edgeD 4 i j ∨ edgeD 4 j i then x⁻¹ else 1

theorem chi_self (i : Fin 4) (x : normOne (unitaryInvolution K p f)) : chi i i x = x * x := by
  simp [chi]

theorem edgeD_ne {i j : Fin 4} (h : edgeD 4 i j) : i ≠ j := by
  revert i j
  decide

theorem chi_edge {i j : Fin 4} (h : edgeD 4 i j) (x : normOne (unitaryInvolution K p f)) :
    chi i j x = x⁻¹ := by
  simp [chi, edgeD_ne h, h]

theorem chi_edge' {i j : Fin 4} (h : edgeD 4 j i) (x : normOne (unitaryInvolution K p f)) :
    chi i j x = x⁻¹ := by
  simp [chi, (edgeD_ne h).symm, h]

theorem chi_far {i j : Fin 4} (hij : i ≠ j) (h1 : ¬ edgeD 4 i j) (h2 : ¬ edgeD 4 j i)
    (x : normOne (unitaryInvolution K p f)) : chi i j x = 1 := by
  simp [chi, hij, h1, h2]

theorem tor_conj_ι (i j : Fin 4) (x : normOne (unitaryInvolution K p f)) (A : Su K p f 2) :
    tor S i x * S.ι j A * (tor S i x)⁻¹ = S.ι j (conjDiag hK ![chi i j x, 1] A) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [chi_self]
    show S.ι i (torusTwo (unitaryInvolution K p f) x) * S.ι i A *
      (S.ι i (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, torusTwo_mul_mul_inv hK]
  by_cases h1 : edgeD 4 i j
  · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff i j).1 h1
    rw [chi_edge h1]
    show S.ι (edgeSrc e) (torusTwo (unitaryInvolution K p f) x) * S.ι (edgeTgt e) A *
      (S.ι (edgeSrc e) (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_src, ι_tgt, ι_tgt, ← map_inv, ← map_mul, ← map_mul, embSUid_two_torus_conj_zero hK]
  by_cases h2 : edgeD 4 j i
  · obtain ⟨e, rfl, rfl⟩ := (edgeD_iff j i).1 h2
    rw [chi_edge' h2]
    show S.ι (edgeTgt e) (torusTwo (unitaryInvolution K p f) x) * S.ι (edgeSrc e) A *
      (S.ι (edgeTgt e) (torusTwo (unitaryInvolution K p f) x))⁻¹ = _
    rw [ι_tgt, ι_src, ι_src, ← map_inv, ← map_mul, ← map_mul, embSUid_zero_torus_conj_two hK]
  · rw [chi_far hij h1 h2]
    have hc : tor S i x * S.ι j A = S.ι j A * tor S i x := S.comm i j hij h1 h2 _ _
    rw [hc, mul_inv_cancel_right]
    congr 1
    have h11 : (![1, 1] : Fin 2 → normOne (unitaryInvolution K p f)) = 1 := by
      ext i
      fin_cases i <;> rfl
    rw [h11, conjDiag_one hK A]

@[expose] noncomputable def mTor : (Fin 4 → normOne (unitaryInvolution K p f)) →* G :=
  MonoidHom.noncommPiCoprod (fun i => tor S i) (fun i j _ x y => tor_comm S i j x y)

theorem mTor_mulSingle (i : Fin 4) (x : normOne (unitaryInvolution K p f)) :
    mTor S (Pi.mulSingle i x) = tor S i x :=
  MonoidHom.noncommPiCoprod_mulSingle (N := fun _ => normOne (unitaryInvolution K p f))
    (fun i => tor S i) i x

theorem mTor_apply (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    mTor S t = tor S 0 (t 0) * tor S 1 (t 1) * tor S 2 (t 2) * tor S 3 (t 3) := by
  have ht : t = Pi.mulSingle 0 (t 0) * Pi.mulSingle 1 (t 1) * Pi.mulSingle 2 (t 2) *
      Pi.mulSingle 3 (t 3) := by
    ext i
    fin_cases i <;> simp
  conv_lhs => rw [ht]
  simp only [map_mul, mTor_mulSingle]

@[expose] noncomputable def rho (j : Fin 4) (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    normOne (unitaryInvolution K p f) :=
  chi 0 j (t 0) * chi 1 j (t 1) * chi 2 j (t 2) * chi 3 j (t 3)

theorem mTor_conj_ι (t : Fin 4 → normOne (unitaryInvolution K p f)) (j : Fin 4)
    (A : Su K p f 2) :
    mTor S t * S.ι j A * (mTor S t)⁻¹ = S.ι j (conjDiag hK ![rho j t, 1] A) := by
  rw [mTor_apply]
  set a := tor S 0 (t 0)
  set b := tor S 1 (t 1)
  set c := tor S 2 (t 2)
  set d := tor S 3 (t 3)
  have e : a * b * c * d * S.ι j A * (a * b * c * d)⁻¹ =
      a * (b * (c * (d * S.ι j A * d⁻¹) * c⁻¹) * b⁻¹) * a⁻¹ := by group
  rw [e]
  simp only [a, b, c, d]
  rw [tor_conj_ι hK S 3 j, tor_conj_ι hK S 2 j, tor_conj_ι hK S 1 j, tor_conj_ι hK S 0 j,
    ← conjDiag_two_mul, ← conjDiag_two_mul, ← conjDiag_two_mul, rho, mul_assoc, mul_assoc]

@[expose] noncomputable def lam (e : Fin 3) (t : Fin 4 → normOne (unitaryInvolution K p f)) :
    Fin 3 → normOne (unitaryInvolution K p f) :=
  ![rho (edgeSrc e) t * rho (edgeTgt e) t, rho (edgeTgt e) t, 1]

theorem mTor_conj_θ (hq : p ^ f ≠ 2) (e : Fin 3) (t : Fin 4 → normOne (unitaryInvolution K p f))
    (g : Su K p f 3) :
    mTor S t * S.θ e g * (mTor S t)⁻¹ = S.θ e (conjDiag hK (lam e t) g) := by
  have hle : B12 K p f ⊔ B23 K p f ≤
      MonoidHom.eqLocus ((MulAut.conj (mTor S t)).toMonoidHom.comp (S.θ e))
        ((S.θ e).comp (conjDiag hK (lam e t))) := by
    refine sup_le ?_ ?_
    · rintro _ ⟨A, rfl⟩
      show mTor S t * S.θ e (embSUid (unitaryInvolution K p f) 2 A) * (mTor S t)⁻¹ =
        S.θ e (conjDiag hK (lam e t) (embSUid (unitaryInvolution K p f) 2 A))
      rw [← ι_src, mTor_conj_ι hK, ι_src, conjDiag_embSUid_two hK]
      congr 2
      have : conjDiag hK ![lam e t 0, lam e t 1] = conjDiag hK ![rho (edgeSrc e) t, 1] := by
        rw [conjDiag_two hK]
        simp [lam]
      rw [this]
    · rintro _ ⟨A, rfl⟩
      show mTor S t * S.θ e (embSUid (unitaryInvolution K p f) 0 A) * (mTor S t)⁻¹ =
        S.θ e (conjDiag hK (lam e t) (embSUid (unitaryInvolution K p f) 0 A))
      rw [← ι_tgt, mTor_conj_ι hK, ι_tgt, conjDiag_embSUid_zero hK]
      rfl
  rw [B12_sup_B23_eq_top hK hq] at hle
  exact hle (Subgroup.mem_top g)

end Tori

end CFSG.ClassicalInvolution.PhanD4

module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeNodeSolv

public section

namespace CFSG.ClassicalInvolution.RouteD.NodeModel

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_elt_positiveLong)
open CFSG.LieType.Steinberg (sl2Upper)
open CFSG.LieType.Steinberg.Sp (blockMat)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.RouteD.LeviModel
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem mat_longBlock_one_upper (c : F) :
    mat 2 F (longBlock F 2 1 (sl2Upper c)) = 1 + c • Matrix.single (Sum.inl 1) (Sum.inr 1) 1 := by
  rw [longBlock_sl2Upper, mat_elt_positiveLong, Matrix.transvection, Matrix.smul_single,
    smul_eq_mul, mul_one]

theorem eq_of_pow_eq_char {p : ℕ} [Fact p.Prime] [CharP F p] {a b : F} (h : a ^ p = b ^ p) :
    a = b := by
  have h1 : (a - b) ^ p = 0 := by rw [sub_pow_char, h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero |>.mp h1)

theorem conjSp_eq_id_of_pow {p : ℕ} [Fact p.Prime] [CharP F p] (A : gsp 2 F)
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F).IsDiag)
    (h : ∀ x, conjSp 2 F (A ^ p) x = x) (x : StatedSp 2 F) : conjSp 2 F A x = x := by
  set a : Mat4 F := ((A : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) with ha
  have hab : a * (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) = 1 := by
    rw [ha, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hdiag : Matrix.diagonal a.diag = a := (Matrix.isDiag_iff_diagonal_diag a).mp hA
  have hpowmat : (((A ^ p : gsp 2 F) : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) = a ^ p := by
    rw [ha]
    simp
  have key : ∀ y : StatedSp 2 F, a ^ p * mat 2 F y = mat 2 F y * a ^ p := fun y => by
    rw [← hpowmat]
    exact mat_comm_of_conj_fix' (A ^ p) y (h y)
  rw [← hdiag, Matrix.diagonal_pow] at key
  have e1 := key (longBlock F 2 0 (sl2Upper 1))
  have e2 := key (shortBlock F fin_two_zero_ne_one (sl2Upper 1))
  have e3 := key (longBlock F 2 1 (sl2Upper 1))
  rw [mat_longBlock_zero_upper] at e1
  rw [mat_shortBlock] at e2
  rw [mat_longBlock_one_upper] at e3
  have f1 := congrFun (congrFun e1 (Sum.inl 0)) (Sum.inr 0)
  have f2 := congrFun (congrFun e2 (Sum.inl 0)) (Sum.inl 1)
  have f3 := congrFun (congrFun e3 (Sum.inl 1)) (Sum.inr 1)
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at f1 f2 f3
  simp [Eu, Matrix.fromBlocks_apply₁₁, blockMat, sl2Upper] at f1 f2 f3
  have g1 := eq_of_pow_eq_char f1
  have g2 := eq_of_pow_eq_char f2
  have g3 := eq_of_pow_eq_char f3
  have hall : ∀ i, a i i = a (Sum.inl 0) (Sum.inl 0) := by
    intro i
    rcases i with i | i <;> fin_cases i
    · rfl
    · simpa using g2.symm
    · simpa using g1.symm
    · simpa using g3.symm.trans g2.symm
  have hscal : a = (a (Sum.inl 0) (Sum.inl 0)) • (1 : Mat4 F) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
      exact hall i
    · rw [hA hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]
  have hcomm : a * mat 2 F x = mat 2 F x * a := by
    rw [hscal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have h1 : mat 2 F (conjSp 2 F A (fieldSp 2 F 1 x)) =
      a * mat 2 F x * (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Mat4 F) := by
    rw [mat_conjSp_fieldSp, map_one_ringEquiv]
  have hx : conjSp 2 F A x = conjSp 2 F A (fieldSp 2 F 1 x) := by
    rw [map_one, MulAut.one_apply]
  apply mat_injective
  rw [hx, h1, hcomm, Matrix.mul_assoc, hab, Matrix.mul_one]

end CFSG.ClassicalInvolution.RouteD.NodeModel

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.RouteD.NodeModel
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open scoped MatrixGroups commutatorElement

section Group

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem DiagAct.pow_act {ψ : StatedSp 2 (GaloisField p f) →* G} {c : G}
    {A : gsp 2 (GaloisField p f)}
    (h : ∀ x, c * ψ x * c⁻¹ = ψ (conjSp 2 (GaloisField p f) A x)) (k : ℕ)
    (x : StatedSp 2 (GaloisField p f)) :
    c ^ k * ψ x * (c ^ k)⁻¹ = ψ (conjSp 2 (GaloisField p f) (A ^ k) x) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    calc c ^ (k + 1) * ψ x * (c ^ (k + 1))⁻¹
        = c * (c ^ k * ψ x * (c ^ k)⁻¹) * c⁻¹ := by group
      _ = ψ (conjSp 2 (GaloisField p f) A (conjSp 2 (GaloisField p f) (A ^ k) x)) := by
          rw [ih, h]
      _ = ψ (conjSp 2 (GaloisField p f) (A ^ (k + 1)) x) := by
          rw [pow_succ', map_mul, MulAut.mul_apply]

theorem DiagAct.centralizes_of_pow_eq_one {ψ : StatedSp 2 (GaloisField p f) →* G}
    (hψ : Function.Injective ψ) {c : G} (hc : DiagAct ψ c) (hcp : c ^ p = 1)
    (x : StatedSp 2 (GaloisField p f)) : c * ψ x = ψ x * c := by
  obtain ⟨A, hd, hA⟩ := hc
  have h1 : ∀ x, conjSp 2 (GaloisField p f) (A ^ p) x = x := fun x => by
    apply hψ
    rw [← DiagAct.pow_act hA, hcp]
    simp
  have h2 := conjSp_eq_id_of_pow A hd h1 x
  have h3 := hA x
  rw [h2] at h3
  exact mul_inv_eq_iff_eq_mul.mp h3

end Group

section Levi

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G} {S : CSetupW p f 2 Ω K z} {Fr : Frame p f 2 Ω K z}
  (P : LeviParams S Fr)

namespace LeviParams

theorem eq_one_of_pow_eq_one (hconn : DeltaConnected Ω) (hZ : Subgroup.center G = ⊥) {c : G}
    (hcY : c ∈ P.T₀ ⊔ P.T₁) (hcT : ∀ t ∈ P.T₀, t * c = c * t) (hcp : c ^ p = 1) : c = 1 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two S.odd
  have hdiag : DiagAct P.ψ₂ c := by
    rcases P.act_dichotomy hconn hZ hcT with ⟨hd, -⟩ | hswap
    · exact hd
    · exfalso
      have hz2c : c * Fr.zf 2 = Fr.zf 2 * c := (hcT _ (P.zf_two_mem hconn hZ)).symm
      have hz20 : Fr.zf 2 * Fr.zf 0 = Fr.zf 1 := by
        have h2 := zf_two_eq S hconn hZ Fr
        have hsq : Fr.zf 0 * Fr.zf 0 = 1 := by
          have h := pow_orderOf_eq_one (Fr.zf 0)
          rw [(Fr.clsW S 0).orderOf_eq_two, pow_two] at h
          exact h
        rw [h2, mul_assoc, Fr.zf_commW S 1 0, ← mul_assoc, hsq, one_mul]
      have hsq2 : Fr.zf 2 * Fr.zf 2 = 1 := by
        have h := pow_orderOf_eq_one (Fr.zf 2)
        rw [(Fr.clsW S 2).orderOf_eq_two, pow_two] at h
        exact h
      have hu : (c ^ 2) * Fr.zf 0 = Fr.zf 0 * (c ^ 2) := by
        have h1 : c * (Fr.zf 2 * Fr.zf 0) * c⁻¹ = Fr.zf 2 * (c * Fr.zf 0 * c⁻¹) := by
          calc c * (Fr.zf 2 * Fr.zf 0) * c⁻¹ = (c * Fr.zf 2 * c⁻¹) * (c * Fr.zf 0 * c⁻¹) := by
                group
            _ = Fr.zf 2 * (c * Fr.zf 0 * c⁻¹) := by
                rw [mul_inv_eq_iff_eq_mul.mpr hz2c]
        have h2 : c * (c * Fr.zf 0 * c⁻¹) * c⁻¹ = Fr.zf 0 := by
          rw [hswap, ← hz20, h1, hswap, ← hz20, ← mul_assoc, hsq2, one_mul]
        have h3 : c ^ 2 * Fr.zf 0 * (c ^ 2)⁻¹ = Fr.zf 0 := by
          calc c ^ 2 * Fr.zf 0 * (c ^ 2)⁻¹ = c * (c * Fr.zf 0 * c⁻¹) * c⁻¹ := by
                rw [pow_two]
                group
            _ = Fr.zf 0 := h2
        exact mul_inv_eq_iff_eq_mul.mp h3
      obtain ⟨m, hm⟩ := hodd
      have h1 : c * (c ^ 2) ^ m = 1 := by
        rw [← pow_mul, ← pow_succ', ← hm]
        exact hcp
      have h2 : c = ((c ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hc' : Commute (((c ^ 2) ^ m)⁻¹) (Fr.zf 0) :=
        ((show Commute (c ^ 2) (Fr.zf 0) from hu).pow_left m).inv_left
      rw [← h2] at hc'
      have hcz : c * Fr.zf 0 * c⁻¹ = Fr.zf 0 := mul_inv_eq_iff_eq_mul.mpr hc'.eq
      exact zf_ne_of_ne S Fr (i := 0) (j := 1) (by decide) (hcz.symm.trans hswap)
  have hM : ∀ m ∈ Mf Fr 0 1, m * c = c * m := by
    intro m hm
    rw [← P.ψ₂_range] at hm
    obtain ⟨x, rfl⟩ := hm
    exact (DiagAct.centralizes_of_pow_eq_one P.ψ₂_injective hdiag hcp x).symm
  have hx₂ : P.x₂ * c = c * P.x₂ := by
    have hd₀₁ : P.x₀ * P.x₁ ∈ Mf Fr 0 1 := (Mf Fr 0 1).mul_mem
      (Tf_le_Mf Fr 0 (Or.inl rfl) P.x₀_mem) (Tf_le_Mf Fr 1 (Or.inr rfl) P.x₁_mem)
    have hh := P.mem_centralizer_h hcY
    have h1 : (P.x₀ * P.x₁) * c = c * (P.x₀ * P.x₁) := hM _ hd₀₁
    have h2 : (P.x₀ * P.x₁) * (P.x₂ * c) = (P.x₀ * P.x₁) * (c * P.x₂) := by
      calc (P.x₀ * P.x₁) * (P.x₂ * c) = (P.x₀ * P.x₁ * P.x₂) * c := by group
        _ = c * (P.x₀ * P.x₁ * P.x₂) := hh.symm
        _ = (c * (P.x₀ * P.x₁)) * P.x₂ := by group
        _ = ((P.x₀ * P.x₁) * c) * P.x₂ := by rw [h1]
        _ = (P.x₀ * P.x₁) * (c * P.x₂) := by group
    exact mul_left_cancel h2
  have hdiag' := P.diagAct_of_centralizes_layer hM hx₂
  have hM' : ∀ m ∈ Mf Fr 1 2, m * c = c * m := by
    intro m hm
    rw [← P.ψ₀_range] at hm
    obtain ⟨x, rfl⟩ := hm
    exact (DiagAct.centralizes_of_pow_eq_one P.ψ₀_injective hdiag' hcp x).symm
  have hcen : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hle : Mf Fr 0 1 ⊔ Mf Fr 1 2 ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hM m hm))
        (fun m hm => Subgroup.mem_centralizer_singleton_iff.mpr (hM' m hm))
    have hg : g ∈ Mf Fr 0 1 ⊔ Mf Fr 1 2 := by
      rw [Mf_sup_Mf_eq_top S hconn Fr]
      exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hcen

end LeviParams

end Levi

end CFSG.ClassicalInvolution.RouteD

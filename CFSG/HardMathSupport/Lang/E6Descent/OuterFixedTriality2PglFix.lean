module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTriality2PglFrob
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofEven
public import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4Unitary

public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec8
open CFSG.RankThree.PartTwo.Sec8.LangTwisted2Proof

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped MatrixGroups

theorem card_pgl_three {K : Type} [Field K] [Finite K] :
    Nat.card PGL(3, K) =
      Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (GL (Fin 3) K))
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 3) (R := K)) := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hab
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h
  have h3 : Nat.card (Subgroup.center (GL (Fin 3) K)) = Nat.card Kˣ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h4 := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  have h5 : Nat.card PGL(3, K) = Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have : Nat.card PGL(3, K) * Nat.card Kˣ =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) * Nat.card Kˣ := by
      rw [h4, h1, h3]
      rfl
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [h5, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3)]
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]

variable {L : Type} [Field L] [CharP L 2]

theorem secD_mul (μ ν : Lˣ) : (secD μ : GL (Fin 3) L) * secD ν = secD (μ * ν) := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_secD, coe_secD, coe_secD, Matrix.diagonal_mul_diagonal]
  congr 1
  funext k
  fin_cases k <;> simp

theorem map_secD (Fr : L →+* L) (ν : Lˣ) :
    Matrix.GeneralLinearGroup.map Fr (secD ν : GL (Fin 3) L) = secD (Units.map Fr.toMonoidHom ν) := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_map_apply, coe_secD, coe_secD,
    Matrix.diagonal_map (map_zero Fr)]
  congr 1
  funext k
  fin_cases k <;> simp

theorem exists_secD_fix [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (μ : Lˣ) :
    ∃ G₀ : GL (Fin 3) L, secD μ * Matrix.GeneralLinearGroup.map Fr G₀ = G₀ := by
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq ((μ⁻¹ : Lˣ) : L) (show 0 < q - 1 by omega)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hν
    exact (Units.ne_zero _) hν.symm
  refine ⟨secD (Units.mk0 ν hν0), ?_⟩
  rw [map_secD, secD_mul]
  congr 1
  refine Units.ext ?_
  simp only [Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Units.val_mk0, hFr]
  have hq1 : ν ^ q = ν ^ (q - 1) * ν := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hq1, hν, Units.val_inv_eq_inv_val]
  field_simp

theorem secFrE_conj {μ : Lˣ} {Fr : L →+* L} {G₀ : GL (Fin 3) L}
    (hG : secD μ * Matrix.GeneralLinearGroup.map Fr G₀ = G₀) (x : GL (Fin 3) L) :
    secD μ * Matrix.GeneralLinearGroup.map Fr (G₀ * x * G₀⁻¹) * (secD μ)⁻¹ =
      G₀ * Matrix.GeneralLinearGroup.map Fr x * G₀⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  calc _ = (secD μ * Matrix.GeneralLinearGroup.map Fr G₀) * Matrix.GeneralLinearGroup.map Fr x *
        (secD μ * Matrix.GeneralLinearGroup.map Fr G₀)⁻¹ := by group
    _ = _ := by rw [hG]

theorem exists_frobGL_fixed [IsAlgClosed L] {q : ℕ} (hq : 2 ≤ q) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ q) (y : GL (Fin 3) L)
    (hy : ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map Fr y) = ProjGenLinGroup.mk y) :
    ∃ y' : GL (Fin 3) L, ProjGenLinGroup.mk y' = ProjGenLinGroup.mk y ∧
      Matrix.GeneralLinearGroup.map Fr y' = y' :=
  CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.exists_map_frob_fixed hq hFr y hy

section Iso

variable {K' : Type} [Field K'] [Fintype K'] (ι : K' →+* L) {q : ℕ} (hq : 2 ≤ q)
  (hK' : Nat.card K' = q) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ q) (μ : Lˣ)
  {G₀ : GL (Fin 3) L} (hG : secD μ * Matrix.GeneralLinearGroup.map Fr G₀ = G₀)

include hK' hFr

theorem frob_ι (x : K') : Fr (ι x) = ι x := by
  rw [hFr, ← map_pow, ← hK', Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem map_map_ι (h : GL (Fin 3) K') :
    Matrix.GeneralLinearGroup.map Fr (Matrix.GeneralLinearGroup.map ι h) =
      Matrix.GeneralLinearGroup.map ι h := by
  refine Units.ext ?_
  ext i j
  simp only [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply]
  exact frob_ι ι hK' hFr _

include hG

theorem pguHom_mem_pglFixE (P : PGL(3, K')) : pguHom ι G₀ P ∈ pglFixE μ Fr := by
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective P
  change secFrE μ Fr (pguHom ι G₀ (ProjGenLinGroup.mk h)) = pguHom ι G₀ (ProjGenLinGroup.mk h)
  rw [pguHom_mk, secFrE_mk, secFrE_conj hG, map_map_ι ι hK' hFr]

theorem exists_pguHom_eqE [IsAlgClosed L] (hq : 2 ≤ q) {Q : PGL(3, L)} (hQ : Q ∈ pglFixE μ Fr) :
    ∃ P : PGL(3, K'), pguHom ι G₀ P = Q := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective Q
  set y := G₀⁻¹ * g * G₀ with hy
  have hgy : g = G₀ * y * G₀⁻¹ := by rw [hy]; group
  clear_value y
  have hQ' : secFrE μ Fr (ProjGenLinGroup.mk g) = ProjGenLinGroup.mk g := hQ
  rw [secFrE_mk, hgy, secFrE_conj hG] at hQ'
  rw [map_mul, map_mul, map_mul, map_mul] at hQ'
  have hy' : ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map Fr y) = ProjGenLinGroup.mk y :=
    mul_left_cancel (mul_right_cancel hQ')
  obtain ⟨y', hyy', hfix⟩ := exists_frobGL_fixed hq hFr y hy'
  have hent : ∀ i j, (y' : Matrix (Fin 3) (Fin 3) L) i j ∈ ι.range := by
    intro i j
    have hx := congrFun (congrFun (congrArg (fun x : GL (Fin 3) L => (x : Matrix (Fin 3) (Fin 3) L))
      hfix) i) j
    simp only [Matrix.GeneralLinearGroup.val_map_apply, Matrix.map_apply, hFr] at hx
    exact mem_range_of_pow_card_eq ι (by rw [hK']; exact hx)
  obtain ⟨h, rfl⟩ := exists_map_eq_of_mem_range ι y' hent
  refine ⟨ProjGenLinGroup.mk h, ?_⟩
  rw [pguHom_mk, map_mul, map_mul, hyy', ← map_mul, ← map_mul, ← hgy]

@[expose] def pglFixEHom : PGL(3, K') →* pglFixE μ Fr where
  toFun P := ⟨pguHom ι G₀ P, pguHom_mem_pglFixE ι hK' hFr μ hG P⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[expose] def pglFixEEquiv [IsAlgClosed L] : PGL(3, K') ≃* pglFixE μ Fr :=
  MulEquiv.ofBijective (pglFixEHom ι hK' hFr μ hG)
    ⟨fun P P' h => pguHom_injective ι G₀ (congrArg Subtype.val h), fun Q => by
      obtain ⟨P, hPQ⟩ := exists_pguHom_eqE ι hK' hFr μ hG hq Q.2
      exact ⟨P, Subtype.ext hPQ⟩⟩

end Iso

end CFSG.HardMathSupport.Lang.E6Descent.Tri2Pgl

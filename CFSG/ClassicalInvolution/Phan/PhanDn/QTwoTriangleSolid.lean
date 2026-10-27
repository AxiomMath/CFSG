module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwoHermitian
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
import all CFSG.ClassicalInvolution.Phan.PhanDn.FlipSpace

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K}

private theorem isFlipflopSub_sup_disjoint_of_flipColl_triangle (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {n : ℕ} {p q r : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) (hr : IsFlipflopPt σ r)
    (hpq : FlipColl σ p q) (hqr : FlipColl σ q r) (hrp : FlipColl σ r p) :
    IsFlipflopSub σ ((p ⊔ q) ⊔ r) ∧ Disjoint (p ⊔ q) r := by
  have hr_sub : IsFlipflopSub σ r := by
    have h := hr
    change IsFlipflopSub σ r ∧ Module.finrank K r = 1 at h
    exact h.1
  have hp_qperp : p ≤ qPerp n K r := by
    intro x hx
    rw [mem_qPerp]
    intro y hy
    rw [polar_comm]
    exact (mem_qPerp.mp (hrp.le_qPerp hy)) x hx
  have hrp' : FlipColl σ p r := ⟨hrp.1.symm, by rw [sup_comm]; exact hrp.2⟩
  exact IsFlipflopSub.sup_of_orth hσ.invol (hpq.isFlipLine hp hq).1 hr_sub
    (sup_le hp_qperp hqr.le_qPerp)
    (sup_le (FlipColl.le_flipOrth_of_card_four hσ hK hrp' hp hr)
      (FlipColl.le_flipOrth_of_card_four hσ hK hqr hq hr))

theorem isFlipflopSub_sup_of_flipColl_triangle (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {n : ℕ} {p q r : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) (hr : IsFlipflopPt σ r)
    (hpq : FlipColl σ p q) (hqr : FlipColl σ q r) (hrp : FlipColl σ r p) :
    IsFlipflopSub σ ((p ⊔ q) ⊔ r) :=
  (isFlipflopSub_sup_disjoint_of_flipColl_triangle hσ hK hp hq hr hpq hqr hrp).1

theorem finrank_sup_of_flipColl_triangle (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {n : ℕ} {p q r : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) (hr : IsFlipflopPt σ r)
    (hpq : FlipColl σ p q) (hqr : FlipColl σ q r) (hrp : FlipColl σ r p) :
    Module.finrank K ↥((p ⊔ q) ⊔ r) = 3 := by
  have hr_fin : Module.finrank K r = 1 := by
    have h := hr
    change IsFlipflopSub σ r ∧ Module.finrank K r = 1 at h
    exact h.2
  have hinf : (p ⊔ q) ⊓ r = ⊥ := disjoint_iff.mp
    (isFlipflopSub_sup_disjoint_of_flipColl_triangle hσ hK hp hq hr hpq hqr hrp).2
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (p ⊔ q) r
  rw [hinf, finrank_bot, add_zero, (hpq.isFlipLine hp hq).2, hr_fin] at hdim
  omega

theorem isFlipflopSub_finrank_exists_solid_sup_of_flipColl_triangle
    (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 4)
    {p q r : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) (hr : IsFlipflopPt σ r)
    (hpq : FlipColl σ p q) (hqr : FlipColl σ q r) (hrp : FlipColl σ r p) :
    IsFlipflopSub σ ((p ⊔ q) ⊔ r) ∧ Module.finrank K ↥((p ⊔ q) ⊔ r) = 3 ∧
      ∃ S, IsSolid σ S ∧ ((p ⊔ q) ⊔ r) ≤ S := by
  have hY_sub := isFlipflopSub_sup_of_flipColl_triangle hσ hK hp hq hr hpq hqr hrp
  have hY_fin := finrank_sup_of_flipColl_triangle hσ hK hp hq hr hpq hqr hrp
  have hY_lt : Module.finrank K ↥((p ⊔ q) ⊔ r) < 4 := by rw [hY_fin]; norm_num
  obtain ⟨S, -, hS, -, hYS, -, -, -⟩ :=
    IsFlipflopSub.exists_solid_le (n := 4) hσ hY_sub hY_lt
  exact ⟨hY_sub, hY_fin, S, hS, hYS⟩

theorem exists_solid_contains_of_flipColl_triangle (hσ : IsUnitaryInvolution σ)
    (hK : Nat.card K = 4) {p q r : Submodule K (Fin 4 ⊕ Fin 4 → K)}
    (hp : IsFlipflopPt σ p) (hq : IsFlipflopPt σ q) (hr : IsFlipflopPt σ r)
    (hpq : FlipColl σ p q) (hqr : FlipColl σ q r) (hrp : FlipColl σ r p) :
    ∃ S, IsSolid σ S ∧ p ≤ S ∧ q ≤ S ∧ r ≤ S := by
  obtain ⟨-, -, S, hS, hYS⟩ :=
    isFlipflopSub_finrank_exists_solid_sup_of_flipColl_triangle hσ hK hp hq hr hpq hqr hrp
  exact ⟨S, hS, le_trans le_sup_left (le_trans le_sup_left hYS),
    le_trans le_sup_right (le_trans le_sup_left hYS), le_trans le_sup_right hYS⟩

end CFSG.ClassicalInvolution.PhanDn

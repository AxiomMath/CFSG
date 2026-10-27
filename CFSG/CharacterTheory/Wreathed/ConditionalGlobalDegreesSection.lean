module

public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesTable
public import CFSG.CharacterTheory.Wreathed.ConditionalGlobalDegreesValues

public section

open scoped BigOperators Classical

namespace CFSG.Wreathed.ConditionalGlobalDegrees

open CFSG.Wreathed.ConditionalFourier CFSG.Wreathed.ConditionalGeneralBase
  CFSG.Wreathed.ConditionalCompleteBase CFSG.Wreathed.ConditionalFiveFixed

variable {ι : Type*} [DecidableEq ι] {G : Type*} [Group G]

structure SectionTable (B : Finset ι) (p A Bq Dq ω : ι) (σ τ₀ κ : ℤ) (m M : ℕ) [NeZero m]
    (J : Finset ℕ) (χ : ℕ → ι) (γ : ℕ → Fin 4 → ι) (εs : ℕ → Fin 4 → ℤ)
    (P Q : ℕ → Fin 2 → ι) (er : ℕ → Fin 2) (ψ : ZMod m × ZMod m → ι) (ρ₀ : ℤ)
    (V : Finset (ZMod m × ZMod m)) (yc cc : ℕ → ι → ℤ) (Cz : ZMod m → ZMod m → ι → ℤ)
    (ζ : ℂ) (Xf : ι → ℕ → ℂ) (cb : ZMod m → ZMod m → ι → ℂ) (ch : ι → G → ℂ) (a : G)
    (Φ : G → ℂ) (ε : ℤ) : Prop
    extends ColumnTable B p A Bq Dq ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V yc cc Cz where
  hζ : IsPrimitiveRoot ζ m
  hpow : ∃ n, m = 2 ^ n
  hX : ∀ j ∈ Finset.Ico 1 m, ∀ φ ∈ B, Xf φ j = cc j φ
  hcb : ∀ i j, ∀ φ ∈ B, cb i j φ = Cz i j φ
  hval : ∀ φ ∈ B, ∀ k ∈ Finset.Ico 1 m, ∀ z ∈ Subgroup.centralizer {a ^ k}, Odd (orderOf z) →
    2 * ch φ (a ^ k * z) =
      (1 - ε * Φ z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) * Xf φ j +
      (1 + ε * Φ z) * ∑ j ∈ Finset.Ico 1 m, ζ ^ (-((j : ℤ) * k)) *
        (∑ i : ZMod m, cb i (0 - i) φ - ∑ i : ZMod m, cb i (-(j : ZMod m) - i) φ)

namespace SectionTable

variable {B : Finset ι} {p A Bq Dq ω : ι} {σ τ₀ κ : ℤ} {m M : ℕ} [NeZero m] {J : Finset ℕ}
  {χ : ℕ → ι} {γ : ℕ → Fin 4 → ι} {εs : ℕ → Fin 4 → ℤ} {P Q : ℕ → Fin 2 → ι}
  {er : ℕ → Fin 2} {ψ : ZMod m × ZMod m → ι} {ρ₀ : ℤ} {V : Finset (ZMod m × ZMod m)}
  {yc cc : ℕ → ι → ℤ} {Cz : ZMod m → ZMod m → ι → ℤ} {ζ : ℂ} {Xf : ι → ℕ → ℂ}
  {cb : ZMod m → ZMod m → ι → ℂ} {ch : ι → G → ℂ} {a : G} {Φ : G → ℂ} {ε : ℤ}
  (S : SectionTable B p A Bq Dq ω σ τ₀ κ m M J χ γ εs P Q er ψ ρ₀ V yc cc Cz ζ Xf cb ch a Φ ε)
include S

theorem X_const {φ : ι} (hφ : φ ∈ B) {x₀ : ℤ} (h : ∀ j ∈ Finset.Ico 1 m, cc j φ = x₀)
    (j : ℕ) (hj : j ∈ Finset.Ico 1 m) : Xf φ j = (x₀ : ℂ) := by
  rw [S.hX j hj φ hφ, h j hj]

theorem half_mem : M ∈ Finset.Ico 1 m := by
  have h1 := S.hm
  have h2 := S.hM
  exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem vA {k : ℕ} (hk : k ∈ Finset.Ico 1 m) {z : G} (hz : z ∈ Subgroup.centralizer {a ^ k})
    (hzo : Odd (orderOf z)) : ch A (a ^ k * z) = -(σ : ℂ) * ε * Φ z := by
  have T := S.toColumnTable
  have h := value_off_zero S.hζ hk (X := Xf A) (f := fun i j => cb i j A)
    (x₀ := ((-σ : ℤ) : ℂ)) (c₀ := ((-σ : ℤ) : ℂ)) (S.X_const T.core.hA T.xA)
    (by rw [S.hcb 0 0 A T.core.hA, T.rep.zero A T.core.hA, Int.cast_zero])
    (fun i j hij => by rw [S.hcb i j A T.core.hA, T.rowA (i, j) hij])
    (S.hval A T.core.hA k hk z hz hzo)
  push_cast at h
  linear_combination h / 2

theorem vω {k : ℕ} (hk : k ∈ Finset.Ico 1 m) {z : G} (hz : z ∈ Subgroup.centralizer {a ^ k})
    (hzo : Odd (orderOf z)) : ch ω (a ^ k * z) = (τ₀ : ℂ) * (1 + ε * Φ z) := by
  have T := S.toColumnTable
  have h := value_off_zero S.hζ hk (X := Xf ω) (f := fun i j => cb i j ω)
    (x₀ := ((0 : ℤ) : ℂ)) (c₀ := ((2 * τ₀ : ℤ) : ℂ)) (S.X_const T.core.hω T.xω)
    (by rw [S.hcb 0 0 ω T.core.hω, T.rep.zero ω T.core.hω, Int.cast_zero])
    (fun i j hij => by rw [S.hcb i j ω T.core.hω, T.rowω (i, j) hij])
    (S.hval ω T.core.hω k hk z hz hzo)
  push_cast at h
  linear_combination h / 2

theorem vB {k : ℕ} (hk : k ∈ Finset.Ico 1 m) {z : G} (hz : z ∈ Subgroup.centralizer {a ^ k})
    (hzo : Odd (orderOf z)) :
    ch Bq (a ^ k * z) = (τ₀ : ℂ) * (1 + (-1) ^ k * (1 + ε * Φ z)) := by
  have T := S.toColumnTable
  have h := value_middle T.hm T.hM S.hζ hk (X := Xf Bq) (f := fun i j => cb i j Bq)
    (x₀ := ((-τ₀ : ℤ) : ℂ)) (c₀ := ((-τ₀ : ℤ) : ℂ)) (S.X_const T.core.hBq T.xB)
    (fun i j => by
      rw [S.hcb i j Bq T.core.hBq, T.rowB (i, j)]
      split_ifs <;> push_cast <;> rfl)
    (S.hval Bq T.core.hBq k hk z hz hzo)
  push_cast at h
  linear_combination h / 2

theorem vD {k : ℕ} (hk : k ∈ Finset.Ico 1 m) {z : G} (hz : z ∈ Subgroup.centralizer {a ^ k})
    (hzo : Odd (orderOf z)) :
    ch Dq (a ^ k * z) = (κ : ℂ) * ε * Φ z + κ * (-1) ^ k * (1 + ε * Φ z) := by
  have T := S.toColumnTable
  have h := value_middle T.hm T.hM S.hζ hk (X := Xf Dq) (f := fun i j => cb i j Dq)
    (x₀ := ((κ : ℤ) : ℂ)) (c₀ := ((-κ : ℤ) : ℂ)) (S.X_const T.core.hDq T.xD)
    (fun i j => by
      rw [S.hcb i j Dq T.core.hDq, T.rowD (i, j)]
      split_ifs <;> push_cast <;> rfl)
    (S.hval Dq T.core.hDq k hk z hz hzo)
  push_cast at h
  linear_combination h / 2

theorem vχ {h : ℕ} (hh : h ∈ J) {k : ℕ} (hk : k ∈ Finset.Ico 1 m) {z : G}
    (hz : z ∈ Subgroup.centralizer {a ^ k}) (hzo : Odd (orderOf z)) :
    ch (χ h) (a ^ k * z) = (σ : ℂ) * (1 - ε * Φ z) * ζ ^ (-((h : ℤ) * k)) := by
  have T := S.toColumnTable
  have hhm : h ∈ Finset.Ico 1 m := by
    have := T.hJ
    rw [this] at hh
    exact (Finset.mem_filter.mp hh).1
  have hv := value_single hhm (ζ := ζ) (X := Xf (χ h)) (f := fun i j => cb i j (χ h))
    (x₀ := ((2 * σ : ℤ) : ℂ))
    (fun j hj => by
      rw [S.hX j hj _ (T.core.hχB h hh), xrow_odd T.core T.hm T.hJ T.quad hh j hj]
      split_ifs <;> push_cast <;> rfl)
    (fun i j => by rw [S.hcb i j _ (T.core.hχB h hh), T.rowχ hh (i, j), Int.cast_zero])
    (S.hval (χ h) (T.core.hχB h hh) k hk z hz hzo)
  push_cast at hv
  linear_combination hv / 2

theorem vPx {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) :
    ch (P t e) (a ^ M) = (τ₀ : ℂ) * (1 + (1 + ε * Φ 1) * (-1) ^ t) := by
  have T := S.toColumnTable
  set i₀ : ZMod m := if e = er t then (t : ZMod m) else ((t + M : ℕ) : ZMod m) with hi₀
  have hiP : labelRep m M er t e = (i₀, i₀) := by
    simp only [labelRep, hi₀]
    split_ifs <;> rfl
  have h := value_diag T.hm T.hM S.hζ S.hpow ht (i₀ := i₀) (X := Xf (P t e))
    (f := fun i j => cb i j (P t e)) (x₀ := ((τ₀ : ℤ) : ℂ)) (c₀ := ((-τ₀ : ℤ) : ℂ))
    (by rw [hi₀]; split_ifs <;> simp)
    (fun j hj => by
      rw [S.hX j hj _ (T.P_mem ht e), T.xP ht e j hj]
      split_ifs <;> push_cast <;> rfl)
    (fun i j => by
      rw [S.hcb i j _ (T.P_mem ht e), T.rowP ht e (i, j), hiP]
      split_ifs <;> push_cast <;> rfl)
    (S.hval (P t e) (T.P_mem ht e) M S.half_mem 1 (Subgroup.one_mem _) (by simp))
  rw [mul_one] at h
  push_cast at h
  linear_combination h / 2

theorem vQx {t : ℕ} (ht : t ∈ Finset.Ico 1 M) (e : Fin 2) :
    ch (Q t e) (a ^ M) = (κ : ℂ) * (ε * Φ 1 + (1 + ε * Φ 1) * (-1) ^ t) := by
  have T := S.toColumnTable
  set i₀ : ZMod m := if e = er t then (t : ZMod m) else ((t + M : ℕ) : ZMod m) with hi₀
  have hiP : labelRep m M er t e = (i₀, i₀) := by
    simp only [labelRep, hi₀]
    split_ifs <;> rfl
  have h := value_diag T.hm T.hM S.hζ S.hpow ht (i₀ := i₀) (X := Xf (Q t e))
    (f := fun i j => cb i j (Q t e)) (x₀ := ((-κ : ℤ) : ℂ)) (c₀ := ((-κ : ℤ) : ℂ))
    (by rw [hi₀]; split_ifs <;> simp)
    (fun j hj => by
      rw [S.hX j hj _ (T.Q_mem ht e), T.xQ ht e j hj]
      split_ifs <;> push_cast <;> rfl)
    (fun i j => by
      rw [S.hcb i j _ (T.Q_mem ht e), T.rowQ ht e (i, j), hiP]
      split_ifs <;> push_cast <;> rfl)
    (S.hval (Q t e) (T.Q_mem ht e) M S.half_mem 1 (Subgroup.one_mem _) (by simp))
  rw [mul_one] at h
  push_cast at h
  linear_combination h / 2

theorem vψx {I : ZMod m × ZMod m} (hI : I ∈ V)
    (h6 : (MulAction.orbit (dualGroup m) I).ncard = 6) :
    ch (ψ I) (a ^ M) = -(ρ₀ : ℂ) * (1 + ε * Φ 1) *
      ((-1) ^ I.1.val + (-1) ^ I.2.val + (-1) ^ (I.1.val + I.2.val)) := by
  have T := S.toColumnTable
  have hψB := (T.gen I hI).1
  have h := value_six T.hm T.hM S.hζ h6 (X := Xf (ψ I)) (f := fun i j => cb i j (ψ I))
    (c₀ := ((ρ₀ : ℤ) : ℂ))
    (fun j hj => by rw [S.hX j hj _ hψB, T.xψ hI j hj, Int.cast_zero])
    (fun i j => by
      rw [S.hcb i j _ hψB, T.rowψ hI (i, j)]
      split_ifs <;> push_cast <;> rfl)
    (S.hval (ψ I) hψB M S.half_mem 1 (Subgroup.one_mem _) (by simp))
  rw [mul_one] at h
  linear_combination h / 2

end SectionTable

end CFSG.Wreathed.ConditionalGlobalDegrees

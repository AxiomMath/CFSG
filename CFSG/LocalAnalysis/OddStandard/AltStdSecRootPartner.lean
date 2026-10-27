module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.AltStdSecFuseBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStd

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup CFSG.OddStandard.AltStdBal Equiv

section Partner

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

theorem rootPartner_z_not_mem_L (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) :
    z ∉ L := by
  simpa using not_conj_mem_L h d hQ2 1

omit [Finite G] in
theorem conj_commute_z {y g w : G} (hg : g * z * g⁻¹ = z * y) (hwz : w * z = z * w)
    (hwy : w * y = y * w) : (g⁻¹ * w * g) * z = z * (g⁻¹ * w * g) := by
  have h1 : w * (z * y) = (z * y) * w := by
    calc w * (z * y) = (w * z) * y := by group
      _ = (z * w) * y := by rw [hwz]
      _ = z * (w * y) := by group
      _ = z * (y * w) := by rw [hwy]
      _ = (z * y) * w := by group
  have hz : g⁻¹ * (z * y) * g = z := by rw [← hg]; group
  calc g⁻¹ * w * g * z = g⁻¹ * (w * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * (w * (z * y)) * g := by rw [hg]
    _ = g⁻¹ * ((z * y) * w) * g := by rw [h1]
    _ = (g⁻¹ * (z * y) * g) * (g⁻¹ * w * g) := by group
    _ = z * (g⁻¹ * w * g) := by rw [hz]

theorem conj_mem_of_odd (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {y g : G} (hg : g * z * g⁻¹ = z * y) {w : G}
    (hwL : w ∈ L) (hwy : w * y = y * w) (hodd : Odd (orderOf w)) : g⁻¹ * w * g ∈ L := by
  have hwz : w * z = z * w := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hwL)
  have hc : g⁻¹ * w * g ∈ centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.2 (conj_commute_z hg hwz hwy)
  obtain ⟨l, hl, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 (hE hc)
  rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with hq1 | hq1
  · rw [hq1, mul_one] at hlq
    rw [← hlq]
    exact hl
  · rw [hq1] at hlq
    exfalso
    obtain ⟨j, hj⟩ := hodd
    have hord : (g⁻¹ * w * g) ^ orderOf w = 1 := by
      have : g⁻¹ * w * g = (MulAut.conj g⁻¹) w := by simp
      rw [this, ← map_pow, pow_orderOf_eq_one, map_one]
    have hlz : Commute l z := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
    rw [← hlq, hlz.mul_pow] at hord
    have hzk : z ^ orderOf w = z := by
      rw [hj, pow_succ, pow_mul, sq, d.mul_self, one_pow, one_mul]
    rw [hzk] at hord
    have : z = (l ^ orderOf w)⁻¹ := eq_inv_of_mul_eq_one_right hord
    exact rootPartner_z_not_mem_L h d hQ2 (this ▸ inv_mem (pow_mem hl _))

theorem normalizes_conj (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {y g : G} (hy : y ∈ L) (hg : g * z * g⁻¹ = z * y)
    {N : Subgroup G} (hNL : N ≤ L)
    (hN : ∀ c ∈ L, c * y = y * c → c ∈ normalizer (N : Set G)) {l : G} (hl : l ∈ L)
    (hly : l * (g⁻¹ * y * g) = (g⁻¹ * y * g) * l) :
    l ∈ normalizer ((conjSub g⁻¹ N : Subgroup G) : Set G) := by
  have hyz : y * z = z * y := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hy)
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (le_centralizer_single h d hl)
  set c' : G := g * l * g⁻¹ with hc'
  have hc'y : c' * y = y * c' := by
    calc c' * y = g * (l * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc']; group
      _ = g * ((g⁻¹ * y * g) * l) * g⁻¹ := by rw [hly]
      _ = y * c' := by rw [hc']; group
  have hca : c' * (z * y) = (z * y) * c' := by
    rw [← hg]
    calc c' * (g * z * g⁻¹) = g * (l * z) * g⁻¹ := by rw [hc']; group
      _ = g * (z * l) * g⁻¹ := by rw [hlz]
      _ = (g * z * g⁻¹) * c' := by rw [hc']; group
  have hc'z : c' * z = z * c' := by
    have h2 : (c' * z) * y = (z * c') * y := by
      calc (c' * z) * y = c' * (z * y) := by group
        _ = (z * y) * c' := hca
        _ = z * (y * c') := by group
        _ = z * (c' * y) := by rw [hc'y]
        _ = (z * c') * y := by group
    exact mul_right_cancel h2
  have hcmem : c' ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hc'z
  have hzN : z ∈ normalizer (N : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro n hn
    exact mem_centralizer_singleton_iff.1 (le_centralizer_single h d (hNL hn))
  have hc'N : c' ∈ normalizer (N : Set G) := by
    obtain ⟨l₀, hl₀, q, hq, hlq⟩ := (mem_sup_iff_mul d).1 (hE hcmem)
    rcases eq_one_or_eq_of_card_eq_two d hQ2 hq with hq1 | hq1
    · rw [hq1, mul_one] at hlq
      rw [← hlq]
      refine hN _ hl₀ ?_
      rw [hlq]
      exact hc'y
    · rw [hq1] at hlq
      have hl₀y : l₀ * y = y * l₀ := by
        have h2 : (l₀ * z) * y = y * (l₀ * z) := by rw [hlq]; exact hc'y
        have h3 : (l₀ * y) * z = (y * l₀) * z := by
          calc (l₀ * y) * z = l₀ * (y * z) := by group
            _ = l₀ * (z * y) := by rw [hyz]
            _ = (l₀ * z) * y := by group
            _ = y * (l₀ * z) := h2
            _ = (y * l₀) * z := by group
        exact mul_right_cancel h3
      rw [← hlq]
      exact mul_mem (hN _ hl₀ hl₀y) hzN
  have := (mem_normalizer_map_conj_iff (A := N) (g := g⁻¹) (y := l)).2 (by simpa [hc'] using hc'N)
  exact this

theorem le_conjSub_of_orderOf_three (h : Setting G L n) (d : Cyc L Q z) (hQ2 : Nat.card Q = 2)
    (hE : centralizer ({z} : Set G) ≤ L ⊔ Q) {y g : G} (hg : g * z * g⁻¹ = z * y)
    {N : Subgroup G} (hNL : N ≤ L) (hNy : ∀ w ∈ N, w * y = y * w) {f : ℕ}
    (φ : N ≃* alternatingGroup (Fin f)) : N ≤ conjSub g L := by
  have h3 : ∀ x ∈ N, orderOf x = 3 → x ∈ conjSub g L := fun x hx hx3 =>
    mem_conjSub_iff.2 (conj_mem_of_odd h d hQ2 hE hg (hNL hx) (hNy x hx)
      (by rw [hx3]; exact ⟨1, rfl⟩))
  set M' : Subgroup N := (conjSub g L).comap N.subtype with hM'
  have hT : (Subgroup.closure {a : alternatingGroup (Fin f) | (a : Perm (Fin f)).IsThreeCycle}) ≤
      M'.map φ.toMonoidHom := by
    rw [Subgroup.closure_le]
    intro a ha
    have ha3 : orderOf (φ.symm a) = 3 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact Equiv.Perm.IsThreeCycle.orderOf ha
    refine ⟨φ.symm a, h3 _ (φ.symm a).2 ?_, by simp⟩
    show orderOf (((φ.symm a : N)) : G) = 3
    rw [Subgroup.orderOf_coe]
    exact ha3
  rw [alternatingGroup.closure_isThreeCycles_eq_top] at hT
  intro x hx
  have : φ ⟨x, hx⟩ ∈ M'.map φ.toMonoidHom := hT (mem_top _)
  obtain ⟨u, hu, hux⟩ := this
  have : u = ⟨x, hx⟩ := φ.injective hux
  rw [this] at hu
  exact hu

end Partner

end CFSG.OddStandard.AltStdSec

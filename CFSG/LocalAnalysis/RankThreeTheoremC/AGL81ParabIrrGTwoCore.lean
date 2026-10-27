module

public import Mathlib.Algebra.Group.End
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

variable {G : Type*} [Group G]

structure ParabLeviData (A L U T O : Subgroup G) : Prop where
  L_le : L ≤ A
  U_le : U ≤ O
  T_le : T ≤ A
  O_norm : ∀ a ∈ A, ∀ o ∈ O, a * o * a⁻¹ ∈ O
  U_norm : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U
  T_norm : ∀ t ∈ T, ∀ m ∈ L, t * m * t⁻¹ ∈ L
  L_inf_O : ∀ x ∈ L, x ∈ O → x = 1
  center_L : ∀ c ∈ L, (∀ s ∈ L, c * s = s * c) → c = 1
  T_comm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a
  decomp : ∀ a ∈ A, ∃ t ∈ T, ∃ m ∈ L, ∃ u ∈ U, a = t * (m * u)

namespace ParabLeviData

variable {A L U T O : Subgroup G} (hD : ParabLeviData A L U T O)
include hD

theorem conj_mem_L {t m s : G} (ht : t ∈ T) (hm : m ∈ L) (hs : s ∈ L) :
    t * m * s * (t * m)⁻¹ ∈ L := by
  have e : t * m * s * (t * m)⁻¹ = t * (m * s * m⁻¹) * t⁻¹ := by group
  rw [e]
  exact hD.T_norm t ht _ (L.mul_mem (L.mul_mem hm hs) (L.inv_mem hm))

theorem centralizes {t m u g : G} (ht : t ∈ T) (hm : m ∈ L) (hu : u ∈ U) (hgeq : g = t * (m * u))
    (hg : ∀ s ∈ L, g * s * g⁻¹ * s⁻¹ ∈ O) : ∀ s ∈ L, t * m * s = s * (t * m) := by
  intro s hs
  have hzA : t * m ∈ A := A.mul_mem (hD.T_le ht) (hD.L_le hm)
  have hsA : s ∈ A := hD.L_le hs
  have huO : u ∈ O := hD.U_le hu
  have hX : u * s * u⁻¹ * s⁻¹ ∈ O := by
    have e : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
    rw [e]
    exact O.mul_mem huO (hD.O_norm s hsA _ (O.inv_mem huO))
  have hO1 : t * m * s * (t * m)⁻¹ * s⁻¹ ∈ O := by
    have e : t * m * s * (t * m)⁻¹ * s⁻¹ =
        (t * m * (u * s * u⁻¹ * s⁻¹) * (t * m)⁻¹)⁻¹ * (g * s * g⁻¹ * s⁻¹) := by
      rw [hgeq]
      group
    rw [e]
    exact O.mul_mem (O.inv_mem (hD.O_norm _ hzA _ hX)) (hg s hs)
  have hL1 : t * m * s * (t * m)⁻¹ * s⁻¹ ∈ L :=
    L.mul_mem (hD.conj_mem_L ht hm hs) (L.inv_mem hs)
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 (hD.L_inf_O _ hL1 hO1))

theorem commute_of_centralizes {t m : G} (hm : m ∈ L) (hz : ∀ s ∈ L, t * m * s = s * (t * m)) :
    Commute t m := by
  have h' : t * m * m = m * t * m := by rw [hz m hm]; group
  exact mul_right_cancel h'

theorem commute_torus {t m : G} (ht : t ∈ T) (hm : m ∈ L)
    (hz : ∀ s ∈ L, t * m * s = s * (t * m)) {t' : G} (ht' : t' ∈ T) : Commute t' (t * m) := by
  have hc : t' * t = t * t' := hD.T_comm t' ht' t ht
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = t' * (t * m) * t'⁻¹ * (t * m)⁻¹ := ⟨_, rfl⟩
  have hcL : c ∈ L := by
    have e : c = t * (t' * m * t'⁻¹ * m⁻¹) * t⁻¹ := by
      rw [hcdef]
      calc t' * (t * m) * t'⁻¹ * (t * m)⁻¹ = (t' * t) * m * t'⁻¹ * (t * m)⁻¹ := by group
        _ = (t * t') * m * t'⁻¹ * (t * m)⁻¹ := by rw [hc]
        _ = t * (t' * m * t'⁻¹ * m⁻¹) * t⁻¹ := by group
    rw [e]
    exact hD.T_norm t ht _ (L.mul_mem (hD.T_norm t' ht' m hm) (L.inv_mem hm))
  have h2 : ∀ s ∈ L, Commute (t' * (t * m) * t'⁻¹) s := by
    intro s hs
    have hs' : t'⁻¹ * s * t'⁻¹⁻¹ ∈ L := hD.T_norm t'⁻¹ (T.inv_mem ht') s hs
    have h1 := hz _ hs'
    show t' * (t * m) * t'⁻¹ * s = s * (t' * (t * m) * t'⁻¹)
    calc t' * (t * m) * t'⁻¹ * s = t' * ((t * m) * (t'⁻¹ * s * t'⁻¹⁻¹)) * t'⁻¹ := by group
      _ = t' * ((t'⁻¹ * s * t'⁻¹⁻¹) * (t * m)) * t'⁻¹ := by rw [h1]
      _ = s * (t' * (t * m) * t'⁻¹) := by group
  have hcs : ∀ s ∈ L, c * s = s * c := by
    intro s hs
    have h3 : Commute (t * m)⁻¹ s := Commute.inv_left (show Commute (t * m) s from hz s hs)
    have h4 : Commute c s := by
      rw [hcdef]
      exact (h2 s hs).mul_left h3
    exact h4.eq
  have hc1 := hD.center_L c hcL hcs
  rw [hcdef] at hc1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hc1)

theorem map_eq_pow {S : MulAut G} {n : ℕ} (hSL : ∀ x ∈ L, S x ∈ L) (hSL' : ∀ x ∈ L, S⁻¹ x ∈ L)
    (hST : ∀ t ∈ T, S t = t ^ n) {t m : G} (ht : t ∈ T) (hm : m ∈ L)
    (hz : ∀ s ∈ L, t * m * s = s * (t * m)) : S (t * m) = (t * m) ^ n := by
  have hcomm : Commute t m := hD.commute_of_centralizes hm hz
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = S (t * m) * ((t * m) ^ n)⁻¹ := ⟨_, rfl⟩
  have hcL : c ∈ L := by
    have e : c = t ^ n * (S m * (m ^ n)⁻¹) * (t ^ n)⁻¹ := by
      rw [hcdef, hcomm.mul_pow, map_mul, hST t ht]
      group
    rw [e]
    exact hD.T_norm _ (T.pow_mem ht n) _ (L.mul_mem (hSL m hm) (L.inv_mem (L.pow_mem hm n)))
  have hSz : ∀ s ∈ L, Commute (S (t * m)) s := by
    intro s hs
    have h1 : (t * m) * S⁻¹ s = S⁻¹ s * (t * m) := hz _ (hSL' s hs)
    have h2 : S (t * m) * S (S⁻¹ s) = S (S⁻¹ s) * S (t * m) := by
      rw [← map_mul, ← map_mul]
      exact congrArg S h1
    rwa [MulAut.apply_inv_self] at h2
  have hcs : ∀ s ∈ L, c * s = s * c := by
    intro s hs
    have h2 : Commute ((t * m) ^ n) s := (show Commute (t * m) s from hz s hs).pow_left n
    have h4 : Commute c s := by
      rw [hcdef]
      exact (hSz s hs).mul_left h2.inv_left
    exact h4.eq
  have hc1 := hD.center_L c hcL hcs
  rw [hcdef] at hc1
  exact mul_inv_eq_one.1 hc1

theorem conj_pow_mem {t m : G} (ht : t ∈ T) (hm : m ∈ L) (hz : ∀ s ∈ L, t * m * s = s * (t * m))
    (n : ℕ) {h : G} (hh : h ∈ A) : h * (t * m) ^ n * h⁻¹ * ((t * m) ^ n)⁻¹ ∈ U := by
  have hzA : (t * m) ^ n ∈ A := A.pow_mem (A.mul_mem (hD.T_le ht) (hD.L_le hm)) n
  obtain ⟨t', ht', m', hm', u', hu', rfl⟩ := hD.decomp h hh
  have hw : Commute (t' * m') ((t * m) ^ n) := by
    refine Commute.mul_left ?_ ?_
    · exact (hD.commute_torus ht hm hz ht').pow_right n
    · exact (show Commute (t * m) m' from hz m' hm').symm.pow_right n
  have hwA : t' * m' ∈ A := A.mul_mem (hD.T_le ht') (hD.L_le hm')
  have hc : (t' * m')⁻¹ * ((t * m) ^ n)⁻¹ = ((t * m) ^ n)⁻¹ * (t' * m')⁻¹ := hw.inv_inv.eq
  generalize (t * m) ^ n = z' at hzA hw hc ⊢
  have e : t' * (m' * u') * z' * (t' * (m' * u'))⁻¹ * z'⁻¹ =
      t' * m' * (u' * (z' * u'⁻¹ * z'⁻¹)) * (t' * m')⁻¹ := by
    calc t' * (m' * u') * z' * (t' * (m' * u'))⁻¹ * z'⁻¹
        = t' * m' * u' * z' * u'⁻¹ * ((t' * m')⁻¹ * z'⁻¹) := by group
      _ = t' * m' * u' * z' * u'⁻¹ * (z'⁻¹ * (t' * m')⁻¹) := by rw [hc]
      _ = t' * m' * (u' * (z' * u'⁻¹ * z'⁻¹)) * (t' * m')⁻¹ := by group
  rw [e]
  exact hD.U_norm _ hwA _ (U.mul_mem hu' (hD.U_norm _ hzA _ (U.inv_mem hu')))

theorem pow_mul_mem {z u : G} (hz : z ∈ A) (hu : u ∈ O) (j : ℕ) :
    (z ^ j)⁻¹ * (z * u) ^ j ∈ O := by
  induction j with
  | zero => simpa using O.one_mem
  | succ j ih =>
    have e : (z ^ (j + 1))⁻¹ * (z * u) ^ (j + 1) = z⁻¹ * ((z ^ j)⁻¹ * (z * u) ^ j) * z * u := by
      rw [pow_succ, pow_succ]
      generalize (z * u) ^ j = y
      generalize z ^ j = w
      group
    have h1 : z⁻¹ * ((z ^ j)⁻¹ * (z * u) ^ j) * z⁻¹⁻¹ ∈ O := hD.O_norm _ (A.inv_mem hz) _ ih
    rw [inv_inv] at h1
    rw [e]
    exact O.mul_mem h1 hu

theorem mem_core {S : MulAut G} {n : ℕ} (hSL : ∀ x ∈ L, S x ∈ L) (hSL' : ∀ x ∈ L, S⁻¹ x ∈ L)
    (hSU : ∀ u ∈ U, S u ∈ U) (hST : ∀ t ∈ T, S t = t ^ n) {g : G} (hg : g ∈ A)
    (hgL : ∀ s ∈ L, g * s * g⁻¹ * s⁻¹ ∈ O) {h : G} (hh : h ∈ A) :
    h * S g * h⁻¹ * (g ^ n)⁻¹ ∈ O := by
  obtain ⟨t, ht, m, hm, u, hu, hgeq⟩ := hD.decomp g hg
  have hz := hD.centralizes ht hm hu hgeq hgL
  have hS := hD.map_eq_pow hSL hSL' hST ht hm hz
  have hzA : t * m ∈ A := A.mul_mem (hD.T_le ht) (hD.L_le hm)
  have h1 := hD.conj_pow_mem ht hm hz n hh
  have hgz : g = t * m * u := by rw [hgeq, mul_assoc]
  have h2 : ((t * m) ^ n)⁻¹ * g ^ n ∈ O := by
    rw [hgz]
    exact hD.pow_mul_mem hzA (hD.U_le hu) n
  have hSg : S g = (t * m) ^ n * S u := by rw [hgz, map_mul, hS]
  have hnA : (t * m) ^ n ∈ A := A.pow_mem hzA n
  have hUu : h * S u * h⁻¹ ∈ O := hD.U_le (hD.U_norm h hh _ (hSU u hu))
  generalize (t * m) ^ n = a at h1 h2 hSg hnA
  generalize g ^ n = b at h2 ⊢
  rw [hSg]
  generalize S u = w at hUu ⊢
  have e : h * (a * w) * h⁻¹ * b⁻¹ =
      (h * a * h⁻¹ * a⁻¹) * (a * ((h * w * h⁻¹) * (a⁻¹ * b)⁻¹) * a⁻¹) := by group
  rw [e]
  exact O.mul_mem (hD.U_le h1) (hD.O_norm _ hnA _ (O.mul_mem hUu (O.inv_mem h2)))

end ParabLeviData

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabIrr.GTwo

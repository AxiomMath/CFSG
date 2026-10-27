module

public import CFSG.ClassicalInvolution.Asc77.AscC25W4
public import CFSG.ClassicalInvolution.Asc77.AscC25H1
public import CFSG.Assembly.RankThreeEvenDefs

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.C25W (InFour exists_conj_ge_sylow)
open CFSG.ClassicalInvolution.Asc77.ExactLayer (isPGroup_zpowers_of_sq_eq_one)
open CFSG.ClassicalInvolution.Asc77.C25Y (GoodFusion)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S : Sylow 2 G}

theorem sylow_le_centralizer_of_central {a : G} {S : Sylow 2 G}
    (hcen : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
  intro s hs
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc s * a = (s * a * s⁻¹) * s := by group
    _ = a * s := by rw [hcen s hs]

theorem exists_exceptional_in_S {a : G}
    (hcen : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a) (hz2 : z * z = 1)
    (hnGF : ¬ GoodFusion z a) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧
      g * z * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) ∧
      ∀ h ∈ Subgroup.centralizer ({a} : Set G), h * z * h⁻¹ ≠ g * z * g⁻¹ := by
  unfold GoodFusion at hnGF
  push Not at hnGF
  obtain ⟨w, hwC, hw⟩ := hnGF
  have hSH : (S : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) :=
    sylow_le_centralizer_of_central hcen
  have hb2 : (w * z * w⁻¹) * (w * z * w⁻¹) = 1 := by
    calc (w * z * w⁻¹) * (w * z * w⁻¹) = w * (z * z) * w⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have hT2 : IsPGroup 2 (Subgroup.zpowers (w * z * w⁻¹)) := isPGroup_zpowers_of_sq_eq_one hb2
  have hTH : Subgroup.zpowers (w * z * w⁻¹) ≤ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.zpowers_le.mpr hwC
  obtain ⟨c, hc, hcT⟩ := exists_conj_ge_sylow hSH hT2 hTH
  refine ⟨c⁻¹ * w, ?_, ?_, ?_⟩
  · have := hcT (w * z * w⁻¹) (Subgroup.mem_zpowers _)
    convert this using 1
    group
  · have h1 : c⁻¹ * (w * z * w⁻¹) * c ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hwC) hc
    convert h1 using 1
    group
  · intro h hh heq
    apply hw (c * h) (Subgroup.mul_mem _ hc hh)
    calc c * h * z * (c * h)⁻¹ = c * (h * z * h⁻¹) * c⁻¹ := by group
      _ = c * (c⁻¹ * w * z * (c⁻¹ * w)⁻¹) * c⁻¹ := by rw [heq]
      _ = w * z * w⁻¹ := by group

theorem z_mem_zpowers_of_sq {y b : G} (hyz : y * y = z) (hz2 : z * z = 1)
    (hb : b ∈ Subgroup.zpowers y) (hb1 : b ≠ 1) : z ∈ Subgroup.zpowers b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rcases Int.even_or_odd' k with ⟨k', hk | hk⟩
  · have h1 : y ^ k = z ^ k' := by rw [hk, zpow_mul, zpow_two, hyz]
    rcases C25H.zpow_eq_one_or_self hz2 k' with h | h
    · exact absurd (h1.trans h) hb1
    · rw [h1, h]
      exact Subgroup.mem_zpowers z
  · refine ⟨2, ?_⟩
    have h1 : y ^ k = z ^ k' * y := by
      rw [hk, zpow_add_one, zpow_mul, zpow_two, hyz]
    have hzy : z * y = y * z := by
      have : y * (y * y) = (y * y) * y := by group
      rw [hyz] at this
      exact this.symm
    have hzc : z ^ k' * y = y * z ^ k' := (Commute.zpow_left (show Commute z y from hzy) k').eq
    show (y ^ k) ^ (2 : ℤ) = z
    rw [zpow_two, h1]
    calc z ^ k' * y * (z ^ k' * y) = z ^ k' * (y * z ^ k') * y := by group
      _ = z ^ k' * (z ^ k' * y) * y := by rw [← hzc]
      _ = (z ^ k' * z ^ k') * (y * y) := by group
      _ = z := by
        rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hz2, one_zpow, one_mul, hyz]

theorem inFour_iff_mem_closure {a : G} (ha2 : a * a = 1) (hz2 : z * z = 1) (haz : a * z = z * a)
    {f : G} : InFour a z f ↔ f ∈ Subgroup.closure ({a, z} : Set G) := by
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · intro h
    exact C25Y.mem_closure_pair ha2 hz2 haz h

theorem conj_mem_closure_pair {a : G} {S : Sylow 2 G} (ha2 : a * a = 1) (hz2 : z * z = 1)
    (haz' : a * z = z * a)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z) :
    ∀ s ∈ (S : Subgroup G), ∀ g ∈ Subgroup.closure ({a, z} : Set G),
      s * g * s⁻¹ ∈ Subgroup.closure ({a, z} : Set G) := by
  intro s hs g hg
  rcases C25Y.mem_closure_pair ha2 hz2 haz' hg with h | h | h | h
  · rw [h]
    simp
  · rw [h]
    rcases hconj s hs with h' | h'
    · rw [h']; exact Subgroup.subset_closure (by simp)
    · rw [h']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · rw [h, hzS s hs]; exact Subgroup.subset_closure (by simp)
  · rw [h]
    have e : s * (a * z) * s⁻¹ = (s * a * s⁻¹) * (s * z * s⁻¹) := by group
    rw [e, hzS s hs]
    rcases hconj s hs with h' | h'
    · rw [h']
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h']
      have : a * z * z = a := by rw [mul_assoc, hz2, mul_one]
      rw [this]
      exact Subgroup.subset_closure (by simp)

theorem conjSub_closure_pair {a : G} {S : Sylow 2 G} (ha2 : a * a = 1) (hz2 : z * z = 1)
    (haz' : a * z = z * a)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z)
    (hzS : ∀ s ∈ (S : Subgroup G), s * z * s⁻¹ = z) :
    ∀ s ∈ (S : Subgroup G), conjSub s (Subgroup.closure ({a, z} : Set G)) =
      Subgroup.closure ({a, z} : Set G) := by
  intro s hs
  have hc := conj_mem_closure_pair ha2 hz2 haz' hconj hzS
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := hc s hs _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := hc s⁻¹ ((S : Subgroup G).inv_mem hs) _ hx
    simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S

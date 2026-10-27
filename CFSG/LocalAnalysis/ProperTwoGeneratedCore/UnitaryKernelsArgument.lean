module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.UnitaryKernelsHull

public section

namespace CFSG.ProperTwoGeneratedCore.UnitaryKernels

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open CFSG.ProperTwoGeneratedCore.RankOnePair
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem unitary_root_mem_or_mul_mem_partner_hull {H : Subgroup G} {z w₁ w₂ : G}
    {U R₁ : Subgroup G} {q : ℕ} [Finite G] (hzU : z ∈ U)
    (hw : ∀ x : G, Commute x w₁ → Commute x z → Commute x w₂)
    (h₂ : UnitaryKernelHullData H z w₂ U q) (hR₁ : UnitaryKernelRootData H z w₁ U R₁ q) :
    ∀ r ∈ R₁, r ∈ localInvolutionPointHull z w₂ ∨ w₂ * r ∈ localInvolutionPointHull z w₂ := by
  intro r hr
  obtain ⟨R₂⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w₂ ⊓ H)) := inferInstance
  have hR₂ := h₂.sylow R₂
  have hrU : ∀ y ∈ U, r * y = y * r := fun y hy => (((hR₁.mem_center y).mp hy).2 r hr).symm
  have hrw₁ : Commute r w₁ := Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z w₁ (hR₁.le hr).1)
  have hrw₂ : r ∈ Subgroup.centralizer ({w₂} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hw r hrw₁ (hrU z hzU))
  rcases hR₂.aut ⟨r, hrw₂⟩ (hR₁.le hr).2 hrU (hR₁.sq_mem r hr) with ⟨r₂, hr₂R, hγ⟩ | hγ
  · have hkC : r * (r₂ : G)⁻¹ ∈
        Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) := by
      have := (h₂.ker (⟨r, hrw₂⟩ * r₂⁻¹)).mp (by rw [map_mul, map_inv, hγ, mul_inv_cancel])
      exact this
    have hr₂L : (r₂ : G) ∈ localInvolutionPointHull z w₂ := (hR₂.le hr₂R).1
    have hcomm : (r₂ : G) * (r * (r₂ : G)⁻¹) = r * (r₂ : G)⁻¹ * r₂ :=
      Subgroup.mem_centralizer_iff.mp hkC _ hr₂L
    have hrr₂ : Commute r (r₂ : G) := by
      have h1 : (r₂ : G) * r * (r₂ : G)⁻¹ = r := by
        rw [mul_assoc, hcomm, inv_mul_cancel_right]
      calc r * r₂ = ((r₂ : G) * r * (r₂ : G)⁻¹) * r₂ := by rw [h1]
        _ = r₂ * r := by group
    have hk2U : (r * (r₂ : G)⁻¹) ^ 2 ∈ U := by
      rw [hrr₂.inv_right.mul_pow, inv_pow]
      exact U.mul_mem (hR₁.sq_mem r hr) (U.inv_mem (hR₂.sq_mem _ hr₂R))
    have hk2 : (r * (r₂ : G)⁻¹) ^ 2 = 1 :=
      hR₂.inter_centralizer _ hk2U (Subgroup.pow_mem _ hkC 2)
    by_cases hk1 : r * (r₂ : G)⁻¹ = 1
    · left
      rw [mul_inv_eq_one] at hk1
      rw [hk1]
      exact hr₂L
    · right
      have hkw : r * (r₂ : G)⁻¹ = w₂ := Set.mem_singleton_iff.mp
        ((Set.ext_iff.mp h₂.involutions _).mp
          ⟨Subgroup.mul_mem _ hrw₂ (Subgroup.inv_mem _ r₂.2), hkC, orderOf_eq_prime hk2 hk1⟩)
      have hw₂2 : w₂ * w₂ = 1 := by rw [← hkw, ← pow_two, hk2]
      have : w₂ * r = r₂ := by
        have hr' : r = w₂ * r₂ := by
          calc r = r * (r₂ : G)⁻¹ * r₂ := by group
            _ = w₂ * r₂ := by rw [hkw]
        rw [hr', ← mul_assoc, hw₂2, one_mul]
      rw [this]
      exact hr₂L
  · left
    have hr2C : r ^ 2 ∈ Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) := by
      have := (h₂.ker (⟨r, hrw₂⟩ ^ 2)).mp (by rw [map_pow, hγ])
      exact this
    have hr2 : r ^ 2 = 1 := hR₂.inter_centralizer _ (hR₁.sq_mem r hr) hr2C
    exact h₂.le_hull (hR₁.inv_mem r hr hr2)

theorem unitary_kernel_eq_zpowers_of_partner {H : Subgroup G} {z w₁ w₂ : G}
    {U R₁ : Subgroup G} {q : ℕ} (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hzU : z ∈ U)
    (hw : ∀ x : G, Commute x w₂ → Commute x z → Commute x w₁)
    (h₁ : UnitaryKernelHullData H z w₁ U q) (h₂ : UnitaryKernelHullData H z w₂ U q)
    (hcc : Subgroup.centralizer (localInvolutionPointHull z w₁ : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) = ⊥)
    (hR₁ : UnitaryKernelRootData H z w₁ U R₁ q)
    (hcoset : ∃ a ∈ R₁, ∀ b ∈ R₁, b ∈ localInvolutionPointHull z w₂ ∨
      a⁻¹ * b ∈ localInvolutionPointHull z w₂) :
    Subgroup.centralizer ({w₂} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) =
      Subgroup.zpowers w₂ := by
  apply le_antisymm
  · rintro k ⟨hkw₂, hkL₂⟩
    have hkU : ∀ y ∈ U, k * y = y * k := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hkL₂ y (h₂.le_hull hy)).symm
    have hkz : Commute k z := hkU z hzU
    have hkH : k ∈ H := hzH (Subgroup.mem_centralizer_singleton_iff.mpr hkz)
    have hkw₁ : k ∈ Subgroup.centralizer ({w₁} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hw k (Subgroup.mem_centralizer_singleton_iff.mp hkw₂) hkz)
    obtain ⟨y, hyU, hγ⟩ := hR₁.fix _ h₂.le_hull hcoset ⟨k, hkw₁⟩ hkH hkU
      (fun y _ hyL => (Subgroup.mem_centralizer_iff.mp hkL₂ y hyL).symm)
    have hk2L₁ : k ^ 2 ∈ Subgroup.centralizer (localInvolutionPointHull z w₁ : Set G) := by
      have hy2 : y ^ 2 = 1 := Subtype.ext (h₁.sq_eq_one _ hyU)
      exact (h₁.ker (⟨k, hkw₁⟩ ^ 2)).mp (by rw [map_pow, hγ, ← map_pow, hy2, map_one])
    have hk2 : k ^ 2 = 1 := by
      have : k ^ 2 ∈ (⊥ : Subgroup G) := hcc ▸ ⟨hk2L₁, Subgroup.pow_mem _ hkL₂ 2⟩
      exact Subgroup.mem_bot.mp this
    by_cases hk1 : k = 1
    · rw [hk1]
      exact Subgroup.one_mem _
    · have hkw : k = w₂ := Set.mem_singleton_iff.mp
        ((Set.ext_iff.mp h₂.involutions k).mp ⟨hkw₂, hkL₂, orderOf_eq_prime hk2 hk1⟩)
      rw [hkw]
      exact Subgroup.mem_zpowers w₂
  · rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (localInvolutionPointHull_le_centralizer z w₂ hl)

theorem unitary_sylow_inter_hull_mul_centralizer [Finite G] {H : Subgroup G} {z u : G}
    {U R : Subgroup G} {q : ℕ} (hR : UnitaryKernelRootData H z u U R q)
    (hK : Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) = Subgroup.zpowers u)
    (hprod : ∀ b ∈ Subgroup.zpowers u ⊔ R, ∃ a ∈ Subgroup.zpowers u, ∃ r ∈ R, b = a * r)
    (T₁ : Sylow 2 ↥(H ⊓ Subgroup.centralizer ({u} : Set G)))
    (huA : u ∈ (T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype) :
    ((T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype : Set G) ∩
        ((localInvolutionPointHull z u : Set G) *
          (Subgroup.centralizer (localInvolutionPointHull z u : Set G) : Set G)) =
      ((Subgroup.zpowers u ⊔ R : Subgroup G) : Set G) := by
  have hAK : (T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype ≤
      H ⊓ Subgroup.centralizer ({u} : Set G) := Subgroup.map_subtype_le _
  have hRK : R ≤ H ⊓ Subgroup.centralizer ({u} : Set G) := fun r hr =>
    ⟨(hR.le hr).2, localInvolutionPointHull_le_centralizer z u (hR.le hr).1⟩
  have hnormal : (R.subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G))).Normal := by
    refine ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr ?_⟩
    have hnR := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨k, hk⟩ := hR.pow_two _ hnR
    exact hR.two_mem _ (centralizer_conj_mem_hull z u g.2.2 (hR.le hnR).1)
      (H.mul_mem (H.mul_mem g.2.1 (hRK hnR).1) (H.inv_mem g.2.1))
      ⟨k, conj_pow_two_pow_eq_one hk⟩
  have hp : IsPGroup 2 (R.subgroupOf (H ⊓ Subgroup.centralizer ({u} : Set G))) := by
    rintro ⟨n, hn⟩
    obtain ⟨k, hk⟩ := hR.pow_two _ (Subgroup.mem_subgroupOf.mp hn)
    exact ⟨k, Subtype.ext (Subtype.ext hk)⟩
  have hRT := hp.le_sylow_of_normal T₁
  have hRA : R ≤ (T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype :=
    fun r hr => ⟨⟨r, hRK hr⟩, hRT (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
  have hpowA : ∀ x ∈ (T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype,
      ∃ k : ℕ, x ^ 2 ^ k = 1 := fun x hx => pow_two_pow_of_mem_sylow_map T₁ hx
  generalize (T₁ : Subgroup _).map (H ⊓ Subgroup.centralizer ({u} : Set G)).subtype = A at *
  have huA' : Subgroup.zpowers u ≤ A := Subgroup.zpowers_le.mpr huA
  have huC : Subgroup.zpowers u ≤
      Subgroup.centralizer (localInvolutionPointHull z u : Set G) := by
    rw [← hK]
    exact inf_le_right
  ext x
  constructor
  · rintro ⟨hxA, l, hl, c, hc, rfl⟩
    have hxK := hAK hxA
    have hcu : c ∈ Subgroup.centralizer ({u} : Set G) := by
      have := Subgroup.mul_mem _
        (Subgroup.inv_mem _ (localInvolutionPointHull_le_centralizer z u hl)) hxK.2
      rwa [inv_mul_cancel_left] at this
    have hcz : c ∈ Subgroup.zpowers u := hK ▸ ⟨hcu, hc⟩
    have hlA : l ∈ A := by
      have := A.mul_mem hxA (A.inv_mem (huA' hcz))
      rwa [mul_inv_cancel_right] at this
    have hlR : l ∈ R := hR.two_mem l hl (hAK hlA).1 (hpowA l hlA)
    have hlc : l * c = c * l := Subgroup.mem_centralizer_iff.mp hc l hl
    change l * c ∈ Subgroup.zpowers u ⊔ R
    rw [hlc]
    exact Subgroup.mul_mem_sup hcz hlR
  · intro hx
    obtain ⟨a, ha, r, hr, rfl⟩ := hprod x hx
    exact ⟨A.mul_mem (huA' ha) (hRA hr), r, (hR.le hr).1, a, huC ha,
      Subgroup.mem_centralizer_iff.mp (huC ha) r (hR.le hr).1⟩

theorem centralizer_root_solvable {H : Subgroup G} {z u : G} {U R : Subgroup G} {q : ℕ}
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hzU : z ∈ U)
    (hu : UnitaryKernelHullData H z u U q) (hR : UnitaryKernelRootData H z u U R q)
    (hK : Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) = Subgroup.zpowers u) :
    Group.IsSolvable ↥(Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G)) := by
  set B := Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G)
  obtain ⟨A, hAsolv, hA⟩ := hR.solvable
  let φ : B →* MulAut (hullQuotient (localInvolutionPointHull z u)) :=
    (originalCentralizerHullQuotientConjugation z u).comp (Subgroup.inclusion inf_le_left)
  have hφA : φ.range ≤ A := by
    rintro _ ⟨b, rfl⟩
    have hbU : ∀ y ∈ U, (b : G) * y = y * b := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp b.2.2 y hy).symm
    exact hA _ (hzH (Subgroup.mem_centralizer_singleton_iff.mpr (hbU z hzU))) hbU
  have hker : ∀ b ∈ φ.ker, (b : G) ∈ Subgroup.zpowers u := by
    intro b hb
    rw [← hK]
    exact ⟨b.2.1, (hu.ker _).mp hb⟩
  have : Group.IsSolvable φ.ker := Group.isSolvable_of_comm fun a b => by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hker a a.2)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hker b b.2)
    apply Subtype.ext
    apply Subtype.ext
    change ((a : B) : G) * ((b : B) : G) = ((b : B) : G) * ((a : B) : G)
    rw [← hm, ← hn]
    exact ((Commute.refl u).zpow_left m).zpow_right n
  have : Group.IsSolvable φ.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hφA)
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

end CFSG.ProperTwoGeneratedCore.UnitaryKernels

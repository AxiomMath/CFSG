module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.PointKernelRootProductHull

public section

namespace CFSG.ProperTwoGeneratedCore.RankOnePair

open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

theorem exists_coset_of_mem_or_mul_mem {R Y : Subgroup G} {w : G}
    (h : ∀ r ∈ R, r ∈ Y ∨ w * r ∈ Y) : ∃ a ∈ R, ∀ b ∈ R, b ∈ Y ∨ a⁻¹ * b ∈ Y := by
  by_cases hall : ∀ b ∈ R, b ∈ Y
  · exact ⟨1, R.one_mem, fun b hb => Or.inl (hall b hb)⟩
  · push Not at hall
    obtain ⟨a, haR, haY⟩ := hall
    have hwa := (h a haR).resolve_left haY
    refine ⟨a, haR, fun b hb => ?_⟩
    rcases h b hb with hbY | hwb
    · exact Or.inl hbY
    · right
      have := Y.mul_mem (Y.inv_mem hwa) hwb
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_left] at this

theorem relIndex_le_two_of_mem_or_mul_mem {R Y : Subgroup G} {w : G}
    (h : ∀ r ∈ R, r ∈ Y ∨ w * r ∈ Y) : Y.relIndex R ≤ 2 := by
  obtain ⟨a, haR, hab⟩ := exists_coset_of_mem_or_mul_mem h
  exact relIndex_le_two_of_forall haR hab

theorem root_mem_or_mul_mem_partner_hull {H : Subgroup G} {z w₁ w₂ : G} {U R₁ : Subgroup G}
    {q i : ℕ} [Finite G] (hzU : z ∈ U)
    (hw : ∀ x : G, Commute x w₁ → Commute x z → Commute x w₂)
    (h₂ : PointKernelHullData H z w₂ U q i) (hR₁ : PointKernelRootData H z w₁ U R₁ q i) :
    ∀ r ∈ R₁, r ∈ localInvolutionPointHull z w₂ ∨ w₂ * r ∈ localInvolutionPointHull z w₂ := by
  intro r hr
  obtain ⟨R₂⟩ : Nonempty (Sylow 2 ↥(localInvolutionPointHull z w₂ ⊓ H)) := inferInstance
  have hR₂ := h₂.sylow R₂
  have hrU : ∀ y ∈ U, r * y = y * r := fun y hy => (((hR₁.mem_center y).mp hy).2 r hr).symm
  have hrw₁ : Commute r w₁ := Subgroup.mem_centralizer_singleton_iff.mp
    (localInvolutionPointHull_le_centralizer z w₁ (hR₁.le hr).1)
  have hrw₂ : r ∈ Subgroup.centralizer ({w₂} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hw r hrw₁ (hrU z hzU))
  obtain ⟨r₂, hr₂R, hγ⟩ := hR₂.aut ⟨r, hrw₂⟩ (hR₁.le hr).2 hrU
  have hkC : r * (r₂ : G)⁻¹ ∈ Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) := by
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

theorem relIndex_partner_hull_le_two {H : Subgroup G} {z w₁ w₂ : G} {U R₁ : Subgroup G}
    {q i : ℕ} [Finite G] (hzU : z ∈ U)
    (hw : ∀ x : G, Commute x w₁ → Commute x z → Commute x w₂)
    (h₂ : PointKernelHullData H z w₂ U q i) (hR₁ : PointKernelRootData H z w₁ U R₁ q i) :
    (localInvolutionPointHull z w₂).relIndex R₁ ≤ 2 :=
  relIndex_le_two_of_mem_or_mul_mem (root_mem_or_mul_mem_partner_hull hzU hw h₂ hR₁)

theorem kernel_eq_zpowers_of_partner {H : Subgroup G} {z w₁ w₂ : G} {U R₁ : Subgroup G}
    {q i : ℕ} (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hzU : z ∈ U)
    (hw : ∀ x : G, Commute x w₂ → Commute x z → Commute x w₁)
    (h₁ : PointKernelHullData H z w₁ U q i) (h₂ : PointKernelHullData H z w₂ U q i)
    (hcc : Subgroup.centralizer (localInvolutionPointHull z w₁ : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z w₂ : Set G) = ⊥)
    (hR₁ : PointKernelRootData H z w₁ U R₁ q i)
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

theorem oddCore_eq_bot_of_kernel {z w : G} (hw : orderOf w = 2)
    (hcentral : CFSG.oddCore (localInvolutionPointHull z w) ≤
      Subgroup.center (localInvolutionPointHull z w))
    (hnot : w ∉ localInvolutionPointHull z w)
    (hK : Subgroup.centralizer ({w} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z w : Set G) = Subgroup.zpowers w) :
    CFSG.oddCore (localInvolutionPointHull z w) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxK : (x : G) ∈ Subgroup.centralizer ({w} : Set G) ⊓
      Subgroup.centralizer (localInvolutionPointHull z w : Set G) := by
    refine ⟨localInvolutionPointHull_le_centralizer z w x.2,
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp (hcentral hx)) ⟨l, hl⟩)
  rw [hK] at hxK
  rcases (mem_zpowers_involution_iff hw).mp hxK with h1 | h1
  · exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  · have hwL : w ∈ localInvolutionPointHull z w := by
      have h2 := x.2
      rwa [h1] at h2
    exact absurd hwL hnot

theorem centralizer_image_mul_eq (u : G) (U : Subgroup G) :
    Subgroup.centralizer ((fun x : G => u * x) '' (U : Set G)) =
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_image, SetLike.mem_coe,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have hu : u * g = g * u := by simpa using h 1 U.one_mem
    refine ⟨hu, fun y hy => ?_⟩
    have := h y hy
    rw [mul_assoc, ← mul_assoc g, ← hu, mul_assoc] at this
    exact mul_left_cancel this
  · rintro ⟨hu, hU⟩ y hy
    rw [mul_assoc, hU y hy, ← mul_assoc, hu, mul_assoc]

theorem centralizer_root_eq {H : Subgroup G} {z u : G} {U R : Subgroup G} {q i : ℕ}
    (hzH : Subgroup.centralizer ({z} : Set G) ≤ H) (hzU : z ∈ U)
    (hu : PointKernelHullData H z u U q i) (hR : PointKernelRootData H z u U R q i)
    (hK : Subgroup.centralizer ({u} : Set G) ⊓
        Subgroup.centralizer (localInvolutionPointHull z u : Set G) = Subgroup.zpowers u) :
    Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) =
        Subgroup.zpowers u ⊔ R ∧
      ∀ b ∈ Subgroup.zpowers u ⊔ R, ∃ a ∈ Subgroup.zpowers u, ∃ r ∈ R, b = a * r := by
  have hprod : ∀ b ∈ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G),
      ∃ a ∈ Subgroup.zpowers u, ∃ r ∈ R, b = a * r := by
    rintro b ⟨hbu, hbU⟩
    have hbU' : ∀ y ∈ U, b * y = y * b := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hbU y hy).symm
    have hbH : b ∈ H := hzH (Subgroup.mem_centralizer_singleton_iff.mpr (hbU' z hzU))
    obtain ⟨r, hrR, hγ⟩ := hR.aut ⟨b, hbu⟩ hbH hbU'
    have hc : b * (r : G)⁻¹ ∈ Subgroup.centralizer (localInvolutionPointHull z u : Set G) :=
      (hu.ker (⟨b, hbu⟩ * r⁻¹)).mp (by rw [map_mul, map_inv, hγ, mul_inv_cancel])
    have hcu : b * (r : G)⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
      Subgroup.mul_mem _ hbu (Subgroup.inv_mem _ r.2)
    refine ⟨b * (r : G)⁻¹, hK ▸ ⟨hcu, hc⟩, r, hrR, by group⟩
  have hle : Subgroup.zpowers u ⊔ R ≤
      Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) := by
    refine sup_le ?_ fun r hr => ⟨?_, ?_⟩
    · rw [Subgroup.zpowers_le]
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl,
        Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (localInvolutionPointHull_le_centralizer z u (hu.le_hull hy))
    · exact localInvolutionPointHull_le_centralizer z u (hR.le hr).1
    · exact Subgroup.mem_centralizer_iff.mpr fun y hy => ((hR.mem_center y).mp hy).2 r hr
  have heq : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) =
      Subgroup.zpowers u ⊔ R := by
    refine le_antisymm (fun b hb => ?_) hle
    obtain ⟨a, ha, r, hr, rfl⟩ := hprod b hb
    exact Subgroup.mul_mem_sup ha hr
  exact ⟨heq, fun b hb => hprod b (heq ▸ hb)⟩

theorem sylow_inter_hull_mul_centralizer [Finite G] {H : Subgroup G} {z u : G}
    {U R : Subgroup G} {q i : ℕ} (hR : PointKernelRootData H z u U R q i)
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

end CFSG.ProperTwoGeneratedCore.RankOnePair

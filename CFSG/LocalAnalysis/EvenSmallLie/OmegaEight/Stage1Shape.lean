module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Defs
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage1

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem exists_involution_mem_centralizer (hset : StandardSetting G L) :
    ∃ t ∈ centralizer (L : Set G), orderOf t = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set G)) 2
    (even_iff_two_dvd.mp hset.standard.2.1)
  exact ⟨c, c.2, by rwa [orderOf_coe]⟩

theorem stepK (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : FoursGroupCondition L) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) :
    centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      t ∉ L := by
  refine ⟨inf_centralizer_eq_zpowers_of_standard hset hI hFG htC ht,
    fun l hl => mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC l hl),
    centralizer_le_normalizer_of_standard hset.standard htC ht, fun htL => ?_⟩
  have h1 : t ∈ L ⊓ centralizer (L : Set G) := ⟨htL, htC⟩
  rw [inf_centralizer_eq_center, hZ, Subgroup.map_bot, mem_bot] at h1
  rw [h1, orderOf_one] at ht
  exact absurd ht (by decide)

omit [Finite G] in
theorem exists_automizer {t : G} (hLt : L ≤ centralizer ({t} : Set G))
    (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ∃ θ : centralizer ({t} : Set G) →* MulAut L,
      (∀ h l, ((θ h l : L) : G) = h * l * (h : G)⁻¹) ∧
      (∀ h, θ h = 1 ↔ (h : G) ∈ zpowers t) ∧
      ∀ h, (∃ m : L, θ h = MulAut.conj m) ↔ (h : G) ∈ L ⊔ zpowers t := by
  set θ := L.normalizerMonoidHom.comp (inclusion hHN) with hθ
  have hθa : ∀ h l, ((θ h l : L) : G) = h * l * (h : G)⁻¹ := fun h l => rfl
  have hker : ∀ h, θ h = 1 ↔ (h : G) ∈ zpowers t := by
    intro h
    rw [← hK]
    constructor
    · intro h1
      refine ⟨mem_centralizer_iff.2 fun l hl => ?_, h.2⟩
      have h2 : (h : G) * l * (h : G)⁻¹ = l := by
        have h3 := hθa h ⟨l, hl⟩
        rw [h1] at h3
        exact h3.symm
      calc l * (h : G) = (h * l * (h : G)⁻¹) * h := by rw [h2]
        _ = h * l := by group
    · rintro ⟨hC, -⟩
      refine MulEquiv.ext fun l => Subtype.ext ?_
      rw [hθa, ← mem_centralizer_iff.1 hC l l.2, mul_inv_cancel_right]
      rfl
  have hθm : ∀ (m : G) (hm : m ∈ L), θ ⟨m, hLt hm⟩ = MulAut.conj ⟨m, hm⟩ :=
    fun m hm => MulEquiv.ext fun l => Subtype.ext rfl
  refine ⟨θ, hθa, hker, fun h => ⟨?_, fun hh => ?_⟩⟩
  · rintro ⟨⟨m, hmL⟩, hm⟩
    have h1 : θ (⟨m, hLt hmL⟩⁻¹ * h) = 1 := by
      rw [map_mul, map_inv, hθm m hmL, hm, inv_mul_cancel]
    have h2 := (hker _).1 h1
    have h3 : (h : G) = m * (m⁻¹ * h) := by group
    rw [h3]
    exact mul_mem_sup hmL (by simpa using h2)
  · obtain ⟨l, hl, z, hz, hlz⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute a t from
          mem_centralizer_singleton_iff.1 (hLt ha)) k).eq) hh
    have hzt : z ∈ centralizer ({t} : Set G) :=
      zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl) hz
    have hsplit : h = ⟨l, hLt hl⟩ * ⟨z, hzt⟩ := Subtype.ext hlz.symm
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hsplit, map_mul, hθm l hl, (hker _).2 hz, mul_one]

omit [Finite G] in
theorem shapeA_or_exists_outer {t : G} (ht : orderOf t = 2) (htL : t ∉ L)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hK : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    ShapeA t L ∨ ∃ h ∈ centralizer ({t} : Set G), ∀ m ∈ L, ∃ x ∈ L,
      h * x * h⁻¹ ≠ m * x * m⁻¹ := by
  by_cases hsh : centralizer ({t} : Set G) ≤ L ⊔ zpowers t
  · exact Or.inl ⟨ht, htL, hLt, le_antisymm hsh
      (sup_le hLt (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)))⟩
  · right
    obtain ⟨h, hh, hout⟩ := IsConcreteLE.not_le_iff_exists.1 hsh
    obtain ⟨θ, hθ, -, hinn⟩ := exists_automizer hLt hHN hK
    refine ⟨h, hh, fun m hm => ?_⟩
    by_contra hcon
    push Not at hcon
    apply hout
    refine (hinn ⟨h, hh⟩).1 ⟨⟨m, hm⟩, MulEquiv.ext fun x => Subtype.ext ?_⟩
    rw [hθ]
    exact hcon x x.2

theorem l1 (hset : StandardSetting G L) (hZ : center L = ⊥)
    (hI : HypothesisOne (L ⧸ center L)) (hFG : FoursGroupCondition L) :
    ∃ t ∈ centralizer (L : Set G), orderOf t = 2 ∧ t ∉ L ∧
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t ∧
      L ≤ centralizer ({t} : Set G) ∧ centralizer ({t} : Set G) ≤ normalizer (L : Set G) ∧
      (ShapeA t L ∨ ∃ h ∈ centralizer ({t} : Set G), ∀ m ∈ L, ∃ x ∈ L,
        h * x * h⁻¹ ≠ m * x * m⁻¹) := by
  obtain ⟨t, htC, ht⟩ := exists_involution_mem_centralizer hset
  obtain ⟨hK, hLt, hHN, htL⟩ := stepK hset hZ hI hFG htC ht
  exact ⟨t, htC, ht, htL, hK, hLt, hHN, shapeA_or_exists_outer ht htL hLt hHN hK⟩

end CFSG.EvenSmallLie.OmegaEight.Stage1

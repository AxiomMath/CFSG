module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitTwo
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.ChainSplitCount

public section

namespace CFSG.EvenSmallLie.OmegaEight.Chain

open Subgroup Matrix Stage1 SplitIn CFSG.EvenSmallLie.UnitarySix.YamadaPar

theorem eq_of_toMat4_mul4 {A B C D : Array (Array ℕ)}
    (h : toMat4 A * toMat4 B = toMat4 C * toMat4 D) : mul4 A B = mul4 C D := by
  rw [← toMat4_mul4, ← toMat4_mul4] at h
  simp only [mul4]
  congr 1
  funext i
  congr 1
  funext j
  have := congrFun (congrFun h i) j
  simp only [toMat4, mul4, m4Get_ofFn, of_apply] at this
  have h2 := (ZMod.natCast_eq_natCast_iff' _ _ 4).1 this
  rwa [Nat.mod_mod, Nat.mod_mod] at h2

theorem eq_of_toVec4_mv4 {A B : Array (Array ℕ)} {v w : Array ℕ}
    (h : toMat4 A *ᵥ toVec4 v = toMat4 B *ᵥ toVec4 w) : mv4 A v = mv4 B w := by
  rw [← toVec4_mv4, ← toVec4_mv4] at h
  exact eq_of_toVec4_eq h

variable {G : Type} [Group G]

namespace Config

variable {ε : Eps} {t : G} {L H₀ U Q P : Subgroup G} {a : G} {ψ : V6 → G}
  {p u : Fin 6 → G} {x₀ : G} {W : Subgroup G} (hS : SetupX ε t L H₀ U Q P a ψ p u x₀)
  (hC : Config t Q (P ⊔ zpowers x₀) 2 W) {Φ : (Fin 6 → ZMod 4) → G} (hΦ : Coord4 W ψ Φ)
  (hrept : Rep Φ t (-1)) {ρ : G} (hρ : ρ = x₀ ∨ ρ = t * x₀)
  (hrepU : ∀ h ∈ U ⊔ zpowers ρ, ∃ i < 128, Rep Φ h (toMat4 (tilGet ε i)))
include hS hC hΦ hrept hρ hrepU

theorem card_centralizer_leX [Finite G] {b h : G} (hb : b ∈ W) {i : ℕ}
    (hhi : Rep Φ h (toMat4 (tilGet ε i))) :
    Nat.card ((W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) ⊓ centralizer {b * h} : Subgroup G) ≤
      Nat.card (W ⊓ centralizer ({h} : Set G) : Subgroup G) *
        (2 * centc ε (tilGet ε i)) := by
  classical
  set F := (Finset.range 128).filter fun j =>
    (mul4 (tilGet ε i) (tilGet ε j) == mul4 (tilGet ε j) (tilGet ε i)) = true
  set S := F.image (fun j => toMat4 (tilGet ε j)) ∪ F.image (fun j => -toMat4 (tilGet ε j))
  have hS2 : S.card ≤ 2 * centc ε (tilGet ε i) := by
    have hF : F.card = centc ε (tilGet ε i) := by
      rw [centc, Finset.card_def, Finset.filter_val, Finset.range_val, Multiset.range,
        Multiset.filter_coe, Multiset.coe_card]
      simp only [Bool.decide_eq_true]
    calc S.card ≤ (F.image _).card + (F.image _).card := Finset.card_union_le _ _
      _ ≤ F.card + F.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * centc ε (tilGet ε i) := by rw [hF]; ring
  have hbr : Rep Φ (b * h) (toMat4 (tilGet ε i)) := by
    have := Coord4.rep_mul (hΦ.rep_of_mem_A hC.level.comm hb) hhi
    rwa [one_mul] at this
  have h1 := card_le_of_reps (C := (W ⊔ (U ⊔ zpowers x₀ ⊔ zpowers t)) ⊓ centralizer {b * h})
    (W := W) S (fun c hc => ?_) (fun c hc hc1 => hC.mem_W_of_repX hS hΦ hrept hρ hc.1 hc1)
  · rw [hC.inf_centralizer_eqX hb] at h1
    exact h1.trans (Nat.mul_le_mul_left _ hS2)
  · obtain ⟨j, hj, s, hcj⟩ := hC.exists_rep_TX hS hΦ hrept hρ hrepU hc.1
    have hcu := mem_centralizer_singleton_iff.1 hc.2
    have hcomm := hΦ.rep_unique (Coord4.rep_mul hcj hbr)
      (hcu ▸ Coord4.rep_mul hbr hcj)
    have hjF : j ∈ F := by
      refine Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, beq_iff_eq.2 (eq_of_toMat4_mul4 ?_)⟩
      cases s
      · simpa only [Bool.false_eq_true, ↓reduceIte] using hcomm.symm
      · simp only [↓reduceIte, neg_mul, mul_neg, neg_inj] at hcomm
        exact hcomm.symm
    refine ⟨_, ?_, hcj⟩
    cases s
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hjF)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hjF)

end Config

end CFSG.EvenSmallLie.OmegaEight.Chain

module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift centralizerPerfectCore)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem rootSL2_eq_sup_zpowers_xab_two {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)}
    (hX₀ : X₀ ≤ rootSL2 a b) (hX₀c : Nat.card X₀ = Nat.card K + 1) :
    rootSL2 (K := K) a b = X₀ ⊔ zpowers (xab hab 1) := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have hle : X₀ ⊔ zpowers (xab hab 1) ≤ rootSL2 (K := K) a b :=
    sup_le hX₀ ((zpowers_le (G := LinearFlag.projectiveSL n K)).2 (xab_mem_rootSL2 hab 1))
  refine (eq_of_le_of_card_ge hle ?_).symm
  rw [card_rootSL2_two hK hn hab]
  have h3 : 3 ∣ Nat.card (X₀ ⊔ zpowers (xab hab 1) : Subgroup _) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : X₀ ≤ X₀ ⊔ zpowers (xab hab 1))
    rwa [hX₀c, hK] at this
  have h2 : 2 ∣ Nat.card (X₀ ⊔ zpowers (xab hab 1) : Subgroup _) := by
    have := Subgroup.card_dvd_of_le (le_sup_right : zpowers (xab hab 1) ≤ X₀ ⊔ zpowers (xab hab 1))
    rwa [Nat.card_zpowers, (isInvolutionClass_one_xab hab).orderOf_eq_two one_ne_zero] at this
  have h6 : 6 ∣ Nat.card (X₀ ⊔ zpowers (xab hab 1) : Subgroup _) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2 h3
  exact Nat.le_of_dvd Nat.card_pos h6

theorem rootSL2_le_centralizer_or_card_dvd_linear_two (hset : SeitzSetting G L) {n : ℕ}
    {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (hB : ∀ x ∈ centralizerPerfectCore X,
      x ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype →
      ∀ y ∈ centralizerPerfectCore X, x * y = y * x)
    (hAut : (∀ x ∈ centralizerPerfectCore X,
        ((e.symm (xab hab 1) : L) : G) * x * ((e.symm (xab hab 1) : L) : G)⁻¹ *
          (t * x * t⁻¹)⁻¹ ∈
            (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype) ∨
      ∀ x ∈ centralizerPerfectCore X,
        ((e.symm (xab hab 1) : L) : G) * x * ((e.symm (xab hab 1) : L) : G)⁻¹ * x⁻¹ ∈
          (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype) :
    (∃ g : G, (centralizerPerfectCore X).map (MulAut.conj g).toMonoidHom ≤ L ∧
        Nat.card (centralizerPerfectCore X) ∣ Nat.card L) ∨
      ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype ≤
        centralizer (centralizerPerfectCore X : Set G) := by
  rcases hAut with hact | hact
  · exact .inl (card_dvd_of_acts_as_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX hB hact)
  · right
    have hjX : ((e.symm (xab hab 1) : L) : G) ∈ normalizer (X : Set G) := by
      rw [hX]
      exact map_symm_mem_normalizer e (mem_normalizer_of_mem_rootSL2_two hK (by omega) hab hX₀
        hX₀c (xab_mem_rootSL2 hab 1))
    have hjE := mem_normalizer_centralizerPerfectCore hjX
    have hjC : ((e.symm (xab hab 1) : L) : G) ∈ centralizer (centralizerPerfectCore X : Set G) :=
      mem_centralizer_of_forall_commutator_mem (CFSG.Quasithin.perfectCore_perfect _) hB
        (fun x hx => (mem_normalizer_iff.1 hjE x).1 hx) hact
    have hXC : X ≤ centralizer (centralizerPerfectCore X : Set G) :=
      le_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer X)
    rw [rootSL2_eq_sup_zpowers_xab_two hK (by omega) hab hX₀ hX₀c, Subgroup.map_sup,
      Subgroup.map_sup, ← hX]
    refine sup_le hXC ?_
    rw [Subgroup.map_map, MonoidHom.map_zpowers, zpowers_le]
    exact hjC

end CFSG.SeitzReduction.LinearPilot

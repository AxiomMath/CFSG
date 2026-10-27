module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionGeneric
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotFusionNotTransvection
public import CFSG.LocalAnalysis.SeitzReduction.RankOneEndingsTransfer

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.EvenSmallLie CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem commutator_eq_top_of_seitzSetting (hset : SeitzSetting G L) : commutator G = ⊤ := by
  have := hset.standardSetting.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · obtain ⟨a, b, hab⟩ := hset.standardSetting.nonab
    have hc : ⁅a, b⁆ ∈ commutator G := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact absurd hc hab
  · exact h

theorem exists_conj_eq_mul_transvection_of_commutator_mem (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* projectiveSL n K)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (hU : ∀ (U : Sylow 2 L) {z : L}, z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      IsInvolutionClass 1 (e z))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t)
    (habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L) :
    ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G) := by
  have htC := mem_centralizer_of_inf_eq_zpowers hKt
  obtain ⟨g, z, hzL, hgz, hz1, U, hUz⟩ := exists_conj_eq_mul_of_commutator_eq_top
    (commutator_eq_top_of_seitzSetting hset) ht (le_centralizer_of_mem_centralizer htC)
    (centralizer_le_normalizer_of_standard hset.standardSetting.standard htC ht) hKt
    (not_forall_commute_sylow_of_isInvolutionClass_one hset hn hK e hU htC ht) hAutU habel
  refine ⟨g, ⟨z, hzL⟩, hU U (fun h => hz1 (congrArg Subtype.val h)) fun u hu => ?_, hgz⟩
  exact Subtype.ext (hUz u hu)

theorem exists_conj_eq_mul_transvection_or_residual (hset : SeitzSetting G L) {n f : ℕ}
    (hn : 4 ≤ n) {K : Type} [Field K] (hK : Nat.card K = 2 ^ f) (e : L ≃* projectiveSL n K)
    (hAutU : ∀ (U : Sylow 2 L) (β : MulAut L), (∀ u ∈ (U : Subgroup L), β u = u) →
      β ∈ (MulAut.conj : L →* MulAut L).range)
    (hU : ∀ (U : Sylow 2 L) {z : L}, z ≠ 1 → (∀ u ∈ (U : Subgroup L), u * z = z * u) →
      IsInvolutionClass 1 (e z))
    {t : G} (ht : orderOf t = 2)
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) :
    (∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) ∨
      ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) ∧
        ∃ y ∈ (S : Subgroup G), ∃ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∉ L := by
  by_cases habel : ∀ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({t} : Set G) →
      ∀ y ∈ (S : Subgroup G), ∀ z ∈ (S : Subgroup G), y * z * y⁻¹ * z⁻¹ ∈ L
  · exact Or.inl
      (exists_conj_eq_mul_transvection_of_commutator_mem hset hn hK e hAutU hU ht hKt habel)
  · right
    push Not at habel
    exact habel

theorem false_of_rigid (hset : SeitzSetting G L) {t : G} (ht : orderOf t = 2) (S : Sylow 2 G)
    (hSt : (S : Subgroup G) ≤ centralizer ({t} : Set G))
    (χ : centralizer ({t} : Set G) →* Multiplicative (ZMod 2))
    (hχS : ∃ s : G, ∃ hs : s ∈ (S : Subgroup G), χ ⟨s, hSt hs⟩ ≠ 1)
    (hrig : ∀ g y : G, g⁻¹ * t * g ∈ centralizer ({t} : Set G) →
      ∀ (hy : y ∈ centralizer ({t} : Set G)) (hgy : g * y * g⁻¹ ∈ centralizer ({t} : Set G)),
        y * (g⁻¹ * t * g) = (g⁻¹ * t * g) * y → χ ⟨y, hy⟩ = χ ⟨g * y * g⁻¹, hgy⟩) :
    False := by
  have := hset.standardSetting.simple
  exact CFSG.SeitzReduction.RankOne.Endings.not_exists_normal_index_two
    hset.standardSetting.nonab (exists_normal_index_two_of_rigid ht S hSt χ hχS hrig)

section Block

omit [Finite G]

theorem exists_conj_eq_mul_mem_blockSL {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]
    (e : L ≃* projectiveSL n K) {t : G} (hLt : L ≤ centralizer ({t} : Set G))
    {I : Finset (Fin n)} (hI : 2 ≤ I.card)
    (h : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) :
    ∃ (g : G) (y : L), IsInvolutionClass 1 (e y) ∧ e y ∈ blockSL I ∧
      g⁻¹ * t * g = t * (y : G) := by
  obtain ⟨g, z, hz, hgz⟩ := h
  obtain ⟨c, hc1, hcI⟩ := exists_conj_mem_blockSL_of_isInvolutionClass_one hI hz
  set m : L := e.symm c with hm
  have hey : e (m * z * m⁻¹) = c * e z * c⁻¹ := by
    rw [map_mul, map_mul, map_inv, hm, MulEquiv.apply_symm_apply]
  have hmt : (m : G) * t = t * m := mem_centralizer_singleton_iff.1 (hLt m.2)
  refine ⟨g * (m : G)⁻¹, m * z * m⁻¹, hey ▸ hc1, hey ▸ hcI, ?_⟩
  calc (g * (m : G)⁻¹)⁻¹ * t * (g * (m : G)⁻¹) = m * (g⁻¹ * t * g) * (m : G)⁻¹ := by group
    _ = m * t * z * (m : G)⁻¹ := by rw [hgz, mul_assoc (m : G) t]
    _ = t * ((m * z * m⁻¹ : L) : G) := by
      rw [hmt]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group

theorem exists_conj_eq_mul_mem_blockSL_compl_pair {n : ℕ} {K : Type*} [Field K] [Finite K]
    [CharP K 2] (e : L ≃* projectiveSL n K) {t : G} (hLt : L ≤ centralizer ({t} : Set G))
    (hn : 4 ≤ n) {a b : Fin n} (hab : a ≠ b)
    (h : ∃ (g : G) (z : L), IsInvolutionClass 1 (e z) ∧ g⁻¹ * t * g = t * (z : G)) :
    ∃ (g : G) (y : L), IsInvolutionClass 1 (e y) ∧
      e y ∈ blockSL ({a, b}ᶜ : Finset (Fin n)) ∧ g⁻¹ * t * g = t * (y : G) := by
  refine exists_conj_eq_mul_mem_blockSL e hLt ?_ h
  rw [Finset.card_compl, Finset.card_pair hab, Fintype.card_fin]
  omega

end Block

end CFSG.SeitzReduction.LinearPilot

module

public import CFSG.LocalAnalysis.OddStandard.ONanFusBase
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup

section Counting

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_centralizer_dvd {W K : Subgroup G} (hK : K ≤ normalizer (W : Set G)) :
    (centralizer (W : Set G)).relIndex K ∣
      ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).index := by
  have h1 : W.normalizerMonoidHom.ker.relIndex (K.subgroupOf (normalizer (W : Set G))) =
      Nat.card ((K.subgroupOf (normalizer (W : Set G))).map W.normalizerMonoidHom) :=
    relIndex_ker _ _
  rw [W.normalizerMonoidHom_ker, relIndex_subgroupOf hK] at h1
  rw [← W.normalizerMonoidHom_ker, index_ker, h1]
  exact card_dvd_of_le (map_le_range _ _)

theorem seven_dvd_index_of_transitive {W : Subgroup G} (h8 : Nat.card W = 8) {z : G}
    (hz : z ∈ W)
    (htr : ∀ w ∈ W, w ≠ 1 → ∃ n ∈ normalizer (W : Set G), n * z * n⁻¹ = w) :
    7 ∣ ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).index := by
  classical
  have hz1 : z ≠ 1 := by
    intro h1
    have : Nontrivial W := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨w, hw⟩ := exists_ne (1 : W)
    obtain ⟨n, -, hn⟩ := htr w w.2 (fun h => hw (Subtype.ext h))
    apply hw
    apply Subtype.ext
    rw [← hn, h1]
    simp
  rw [← W.normalizerMonoidHom_ker, index_ker]
  set x : W := ⟨z, hz⟩ with hx
  have horb : MulAction.orbit W.normalizerMonoidHom.range x = ({1} : Set W)ᶜ := by
    ext y
    rw [Set.mem_compl_singleton_iff]
    constructor
    · rintro ⟨r, rfl⟩ h
      have h2 : (r : MulAut W) x = 1 := h
      have h3 : x = 1 := by
        have := congrArg (r : MulAut W).symm h2
        simpa using this
      exact hz1 (congrArg Subtype.val h3)
    · intro hy
      obtain ⟨n, hn, hny⟩ := htr y y.2 (fun h => hy (Subtype.ext h))
      refine ⟨⟨W.normalizerMonoidHom ⟨n, hn⟩, ⟨n, hn⟩, rfl⟩, ?_⟩
      apply Subtype.ext
      exact hny
  have hcard : (MulAction.orbit W.normalizerMonoidHom.range x).ncard = 7 := by
    rw [horb, Set.ncard_compl, Set.ncard_singleton, h8]
  have hidx := MulAction.index_stabilizer W.normalizerMonoidHom.range x
  rw [hcard] at hidx
  rw [← hidx]
  exact index_dvd_card _

theorem card_normalizer_eq_of_dvd {W : Subgroup G} (hW : CFSG.Open.IsElemAbelian 2 W)
    (h8 : Nat.card W = 8)
    (h56 : 56 ∣ ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).index) :
    Nat.card (normalizer (W : Set G)) = 168 * Nat.card (centralizer (W : Set G)) := by
  obtain ⟨θ, hθ, hker⟩ := CFSG.ComponentClassification.GHarris.exists_GL32_of_dvd_index hW h8 h56
  have hidx : ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).index = 168 := by
    rw [← hker, index_ker, MonoidHom.range_eq_top.2 hθ, card_top,
      CFSG.ComponentClassification.GHarris.card_GL32_gh]
  have hle : centralizer (W : Set G) ≤ normalizer (W : Set G) := centralizer_le_normalizer _
  have h := ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]

end Counting

theorem sq_mul_sq_mem_alpW {G : Type*} [Group G] (v1 v2 v3 : G) : v1 ^ 2 * v3 ^ 2 ∈ alpW v1 v2 v3 :=
  mul_mem (subset_closure (by simp)) (subset_closure (by simp))

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem isElemAbelian_W : CFSG.Open.IsElemAbelian 2 (alpW v1 v2 v3) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · exact (mem_centralizer_iff.1 (D.V_le_centralizer_W (D.W_le_V a.2)) b b.2).symm
  · rw [pow_two]
    exact (D.mem_W_iff.1 hx).2

theorem relIndex_centralizer_W_P :
    (centralizer (alpW v1 v2 v3 : Set G)).relIndex (alpP v1 v2 v3 s t) = 8 := by
  have h := relIndex_mul_card (H := centralizer (alpW v1 v2 v3 : Set G))
    (K := alpP v1 v2 v3 s t)
  rw [inf_comm, D.P_inf_centralizer_W, AlpEmb.card_alpV D.E, AlpEmb.card_alpP D.E] at h
  omega

theorem card_normalizer_W
    (htr : ∀ w ∈ alpW v1 v2 v3, w ≠ 1 → ∃ n ∈ normalizer (alpW v1 v2 v3 : Set G),
      n * (v1 ^ 2 * v3 ^ 2) * n⁻¹ = w) :
    Nat.card (normalizer (alpW v1 v2 v3 : Set G)) =
      168 * Nat.card (centralizer (alpW v1 v2 v3 : Set G)) := by
  have h7 := seven_dvd_index_of_transitive (AlpEmb.card_alpW D.E D.hF) (sq_mul_sq_mem_alpW v1 v2 v3) htr
  have h8 := relIndex_centralizer_dvd D.P_le_normalizer_W
  rw [D.relIndex_centralizer_W_P] at h8
  have h56 : 7 * 8 ∣ ((centralizer (alpW v1 v2 v3 : Set G)).subgroupOf
      (normalizer (alpW v1 v2 v3 : Set G))).index :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 h8
  exact card_normalizer_eq_of_dvd D.isElemAbelian_W (AlpEmb.card_alpW D.E D.hF) h56

end FusCtx

end CFSG.OddStandard.ONanRec

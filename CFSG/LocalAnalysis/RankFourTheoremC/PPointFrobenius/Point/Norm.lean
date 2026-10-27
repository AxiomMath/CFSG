module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Torus
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.Point.Struct

public section

open Subgroup
open scoped MatrixGroups

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.LocalAnalysis.RankFourTheoremC CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem pt_P_le_centralizer_of_mem (hab : IsMulCommutative (P : Subgroup G)) {a : G}
    (ha : a ∈ (P : Subgroup G)) : (P : Subgroup G) ≤ centralizer ({a} : Set G) := by
  intro g hg
  rw [mem_centralizer_singleton_iff]
  have h := hab.is_comm.comm (⟨a, ha⟩ : (P : Subgroup G)) ⟨g, hg⟩
  exact (congrArg Subtype.val h).symm

theorem pt_isSylowOf_of_le [Fact p.Prime] (Q : Sylow p G) {K : Subgroup G}
    (hQK : (Q : Subgroup G) ≤ K) : IsSylowOf p (Q : Subgroup G) K :=
  isSylowOf_iff.mpr ⟨hQK, Q.isPGroup', fun h =>
    Q.not_dvd_index (h.trans (relIndex_dvd_index_of_le hQK))⟩

theorem pt_isPPoint_of_mem [Fact p.Prime] (hl : PtPoint p P M x) {a : G}
    (ha : a ∈ (P : Subgroup G)) (hao : orderOf a = p) (hC : ¬ centralizer ({a} : Set G) ≤ M) :
    IsPPoint p P M a := by
  have hp : p.Prime := Fact.out
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hl.loc
  have hPC := pt_P_le_centralizer_of_mem hl.abel ha
  have h4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hl.loc.beta P
  have hinf : (P : Subgroup G) ⊓ centralizer ({a} : Set G) = P := inf_of_le_left hPC
  have h3 : 3 ≤ CFSG.Open.pRank p (M ⊓ centralizer ({a} : Set G)) :=
    (by norm_num : 3 ≤ 4).trans (h4.trans
      (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp (le_inf hPM hPC)))
  refine ⟨?_, ha, ?_, ?_⟩
  · unfold IsPElement
    exact ⟨hPM ha, hao, h3, hC⟩
  · rw [hinf]
    exact pt_isSylowOf_of_le P hPC
  · rw [hinf]
    omega

theorem pt_ptPoint_of_mem [Fact p.Prime] (hl : PtPoint p P M x) {a : G}
    (ha : a ∈ (P : Subgroup G)) (hao : orderOf a = p) (hC : ¬ centralizer ({a} : Set G) ≤ M) :
    PtPoint p P M a :=
  ⟨hl.p5, hl.loc, pt_isPPoint_of_mem hl ha hao hC, hl.conf, hl.abel⟩

theorem pt_weakly_closed_P (hl : PtLocal p P M x) {h : G} (hh : h * x * h⁻¹ ∈ (P : Subgroup G)) :
    zpowers (h * x * h⁻¹) = zpowers x := by
  have hg : CFSG.Open.GLBConj h⁻¹ (zpowers x) ≤ (P : Subgroup G) := by
    unfold CFSG.Open.GLBConj
    rw [inv_inv, MonoidHom.map_zpowers, zpowers_le]
    exact hh
  have h1 := hl.weak h⁻¹ hg
  unfold CFSG.Open.GLBConj at h1
  rw [inv_inv, MonoidHom.map_zpowers] at h1
  simpa [MulAut.conj_apply] using h1

theorem pt_conj_zpowers_of_mul {Q U Z : Subgroup G} (hQ : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hUQ : U ≤ Q) (hZQ : Z ≤ Q) (hUZ : U ⊓ Z = ⊥) {u z t : G} (hu : u ∈ U) (hz : z ∈ Z)
    (htU : t ∈ normalizer (U : Set G)) (htZ : t * z * t⁻¹ = z)
    (hx : t * (u * z) * t⁻¹ ∈ zpowers (u * z)) :
    ∀ d ∈ zpowers u, t * d * t⁻¹ ∈ zpowers u := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx
  have huz : Commute u z := hQ u (hUQ hu) z (hZQ hz)
  have htu : t * u * t⁻¹ ∈ U := (mem_normalizer_iff.mp htU u).mp hu
  have hexp : t * (u * z) * t⁻¹ = (t * u * t⁻¹) * z := by
    calc t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) := by group
      _ = (t * u * t⁻¹) * z := by rw [htZ]
  have hpow : u ^ k * z ^ k = (t * u * t⁻¹) * z := by
    rw [← huz.mul_zpow, hk, hexp]
  have h1 : (t * u * t⁻¹)⁻¹ * u ^ k = z * (z ^ k)⁻¹ := by
    calc (t * u * t⁻¹)⁻¹ * u ^ k = (t * u * t⁻¹)⁻¹ * (u ^ k * z ^ k) * (z ^ k)⁻¹ := by group
      _ = (t * u * t⁻¹)⁻¹ * ((t * u * t⁻¹) * z) * (z ^ k)⁻¹ := by rw [hpow]
      _ = z * (z ^ k)⁻¹ := by group
  have hmemU : (t * u * t⁻¹)⁻¹ * u ^ k ∈ U := U.mul_mem (U.inv_mem htu) (U.zpow_mem hu k)
  have hmemZ : (t * u * t⁻¹)⁻¹ * u ^ k ∈ Z := by
    rw [h1]
    exact Z.mul_mem hz (Z.inv_mem (Z.zpow_mem hz k))
  have hbot : (t * u * t⁻¹)⁻¹ * u ^ k ∈ (⊥ : Subgroup G) := hUZ ▸ ⟨hmemU, hmemZ⟩
  have hv : t * u * t⁻¹ = u ^ k := by
    have h0 : (t * u * t⁻¹)⁻¹ * u ^ k = 1 := mem_bot.mp hbot
    exact (inv_mul_eq_one.mp h0)
  intro d hd
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hd
  rw [← conj_zpow, hv, ← zpow_mul]
  exact mem_zpowers_iff.mpr ⟨k * j, rfl⟩

theorem pt_centralizer_le_M [Fact p.Prime] (hk : PtKFacts) (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtLocal p P M x) {a : G} (ha : a ∈ (P : Subgroup G)) (hao : orderOf a = p)
    (hax : zpowers a ≠ zpowers x) : centralizer ({a} : Set G) ≤ M := by
  by_contra hC
  have hla : PtPoint p P M a := pt_ptPoint_of_mem hl.toPtPoint ha hao hC
  have hLL : LayerLocal p P M a := ⟨hla, pt_structure hk hs hG hla⟩
  obtain ⟨t, htL, htN, htmove⟩ := pt_exists_torus_lines hG hLL
  obtain ⟨n, -, -, -, hUel, -⟩ := lp_layer_sylow hG hLL
  obtain ⟨u, hu, z, hz, hxuz⟩ := lp_P_decomp hG hLL hl.point.mem
  have htz : t * z * t⁻¹ = z := by
    have h := mem_centralizer_iff.mp hz.2 t htL
    rw [h]
    group
  have htu : t * u * t⁻¹ ∈ frU P a := (mem_normalizer_iff.mp htN u).mp hu
  have hexp : t * (u * z) * t⁻¹ = (t * u * t⁻¹) * z := by
    calc t * (u * z) * t⁻¹ = (t * u * t⁻¹) * (t * z * t⁻¹) := by group
      _ = (t * u * t⁻¹) * z := by rw [htz]
  have htx : t * x * t⁻¹ ∈ (P : Subgroup G) := by
    rw [hxuz, hexp]
    exact P.mul_mem htu.1 hz.1
  have htxmem : t * x * t⁻¹ ∈ zpowers x := by
    rw [← pt_weakly_closed_P hl htx]
    exact mem_zpowers _
  have hu1 : u ≠ 1 := by
    rintro rfl
    have hxz : x = z := by rw [hxuz, one_mul]
    have hxp : Nat.card (zpowers x) = p := by
      rw [Nat.card_zpowers]
      exact hl.point.elem.2.1
    have hle : zpowers x ≤ (P : Subgroup G) ⊓ centralizer ((layerOf a : Subgroup G) : Set G) :=
      zpowers_le.mpr (hxz ▸ hz)
    exact hax (lp_Z0_unique hLL hle hxp).symm
  have hup : u ^ p = 1 := hUel.2 u hu
  have hDcard : Nat.card (zpowers u) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hup hu1
  obtain ⟨d, hd, hdt⟩ := htmove (zpowers u) (zpowers_le.mpr hu) hDcard
  have hstab := pt_conj_zpowers_of_mul (Q := (P : Subgroup G)) (U := frU P a)
    (Z := (P : Subgroup G) ⊓ centralizer ((layerOf a : Subgroup G) : Set G))
    (fun a ha b hb => by
      have h := hl.abel.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
      exact congrArg Subtype.val h)
    inf_le_left inf_le_left (lp_P_eq_sup hG hLL).2 hu hz htN htz
    (by rw [← hxuz]; exact htxmem)
  exact hdt (hstab d hd)

theorem pt_norm [Fact p.Prime] (hk : PtKFacts) (hs : PtSchurBound) (hG : FrobGlobal G)
    (hl : PtLocal p P M x) : PtNorm p P M x := by
  intro P₁ hP₁P hP₁c hP₁x
  have hp : p.Prime := Fact.out
  haveI : IsCyclic P₁ := isCyclic_of_prime_card hP₁c
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P₁)
  have hP₁eq : P₁ = zpowers (g : G) := by
    ext y
    constructor
    · intro hy
      obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      exact mem_zpowers_iff.mpr ⟨j, by simpa using congrArg Subtype.val hj⟩
    · intro hy
      exact zpowers_le.mpr g.2 hy
  have haP : (g : G) ∈ (P : Subgroup G) := hP₁P g.2
  have hao : orderOf (g : G) = p := by
    rw [← Nat.card_zpowers, ← hP₁eq]
    exact hP₁c
  have hCM : centralizer ({(g : G)} : Set G) ≤ M :=
    pt_centralizer_le_M hk hs hG hl haP hao (hP₁eq ▸ hP₁x)
  have hP4 : 4 ≤ CFSG.Open.pRank p (P : Subgroup G) := four_le_pRank_sylow hl.loc.beta P
  have hinf : (P : Subgroup G) ⊓ centralizer ({(g : G)} : Set G) = P :=
    inf_of_le_left (pt_P_le_centralizer_of_mem hl.abel haP)
  have hN := normalizer_zpowers_le_of_centralizer_le hG.fullCore hl.loc hCM
    (by rw [hinf]; omega)
  rw [hP₁eq]
  exact hN

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

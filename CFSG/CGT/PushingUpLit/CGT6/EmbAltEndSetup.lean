module

public import CFSG.CGT.PushingUpLit.CGT6.EmbEndStd
public import CFSG.LocalAnalysis.EvenSmallLie.OddTranspAlt.Setup

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open
open CFSG.EvenSmallLie.OddTranspAlt (cls)
open scoped commutatorElement

section Aux

private theorem emSetup_isSubnormal_map_range {H Γ : Type*} [Group H] [Group Γ] (f : H →* Γ)
    {A : Subgroup H} (hA : A.IsSubnormal) : CFSG.Open.IsSubnormal (A.map f) f.range := by
  have h1 := (CFSG.Open.IsSubnormal.of_mathlib hA).map f
  rwa [← MonoidHom.range_eq_map] at h1

private theorem emSetup_le_of_not_mem_zc {Γ : Type*} [Group Γ] {Λ N : Subgroup Γ} [Λ.Normal]
    [N.Normal] (hqs : CFSG.IsQuasisimple ↥Λ) (hcent : Subgroup.centralizer (Λ : Set Γ) ≤ Λ)
    {t : Γ} (htN : t ∈ N) (htz : t ∉ Λ ⊓ Subgroup.centralizer (Λ : Set Γ)) : Λ ≤ N := by
  by_cases hcase : Λ ⊓ N ≤ Subgroup.centralizer (Λ : Set Γ)
  · exfalso
    have h1 : ⁅Λ, N⁆ ≤ Subgroup.centralizer (Λ : Set Γ) :=
      (le_inf (Subgroup.commutator_le_left Λ N) (Subgroup.commutator_le_right Λ N)).trans hcase
    have h2 : ⁅⁅Λ, N⁆, Λ⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1
    have h3 : ⁅Λ, N⁆ = ⊥ := LocalCores.perfect_double_commutator hqs.1 h2
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
    exact htz ⟨hcent (h3 htN), h3 htN⟩
  · have hn : ((Λ ⊓ N).subgroupOf Λ).Normal := Subgroup.normal_subgroupOf
    rcases LocalCores.quasisimple_normal_subgroups hqs hn with h | h
    · intro x hx
      have hx' : (⟨x, hx⟩ : Λ) ∈ (Λ ⊓ N).subgroupOf Λ := by rw [h]; trivial
      exact hx'.2
    · exfalso
      refine hcase fun x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hx' : (⟨x, hx.1⟩ : Λ) ∈ (Λ ⊓ N).subgroupOf Λ := hx
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (h hx') ⟨l, hl⟩)

end Aux

section Setup

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem EndCfg4.exists_involution (h : EndCfg4 G T Y) :
    ∃ t : ↥G, orderOf t = 2 ∧ (t : MulAut V) ∈ T ∧
      (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) := by
  obtain ⟨n, hn⟩ := h.adm.hT2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact h.adm.hT1 hn
  have h2 : 2 ∣ Nat.card ↥T := by
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨⟨(x : MulAut V), h.adm.hTG x.2⟩, ?_, x.2, fun y hy => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    show orderOf (x : MulAut V) = 2
    rw [Subgroup.orderOf_coe]
    exact hx
  · exact ((Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2) x x.2).symm

theorem EndCfg4.isComponentOf (h : EndCfg4 G T Y) {m : ℕ} (hm : 7 ≤ m) (hY : YAlt Y m)
    {t : ↥G} (ht : orderOf t = 2)
    (htY : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V))) :
    IsComponentOf (Y.subgroupOf G) (Subgroup.centralizer ({t} : Set ↥G)) := by
  have hcomm : ∀ y ∈ Y, (t : MulAut V) * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp htY y hy).symm
  have hcent : ∀ x : ↥G, (x : MulAut V) ∈ Y →
      (x : MulAut V) ∈ Subgroup.centralizer ({(t : MulAut V)} : Set (MulAut V)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact hcomm x hx
  have hle : Y.subgroupOf G ≤ Subgroup.centralizer ({t} : Set ↥G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [Set.mem_singleton_iff.mp hs]
    exact Subtype.ext (hcomm y hy)
  refine ⟨hle, ?_, (h.std_of_YAlt hm hY).1⟩
  have hne : (t : MulAut V) ≠ 1 := fun h1 => by
    have h2 : t = 1 := Subtype.ext h1
    rw [h2, orderOf_one] at ht
    omega
  have hsq : (t : MulAut V) ^ 2 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht] at h1
    exact congrArg Subtype.val h1
  have hsub := h.cent (t : MulAut V) ⟨t.2, htY⟩ hne hsq
  have key := emSetup_isSubnormal_map_range (Subgroup.inclusion (inf_le_left : G ⊓
    Subgroup.centralizer ({(t : MulAut V)} : Set (MulAut V)) ≤ G)) hsub
  have e1 : (Y.subgroupOf (G ⊓ Subgroup.centralizer ({(t : MulAut V)} : Set (MulAut V)))).map
      (Subgroup.inclusion inf_le_left) = Y.subgroupOf G := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      exact hd
    · intro hx
      exact ⟨⟨(x : MulAut V), x.2, hcent x hx⟩, hx, rfl⟩
  have e2 : (Subgroup.inclusion (inf_le_left : G ⊓
      Subgroup.centralizer ({(t : MulAut V)} : Set (MulAut V)) ≤ G)).range =
      Subgroup.centralizer ({t} : Set ↥G) := by
    ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨⟨d, hdG, hdC⟩, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hdC (t : MulAut V) rfl)
    · intro hx
      have hc := Subgroup.mem_centralizer_iff.mp hx t rfl
      refine ⟨⟨(x : MulAut V), x.2, ?_⟩, rfl⟩
      show (x : MulAut V) ∈ Subgroup.centralizer ({(t : MulAut V)} : Set (MulAut V))
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      rw [Set.mem_singleton_iff.mp hs]
      exact congrArg Subtype.val hc
  rw [e1, e2] at key
  exact key

theorem EndCfg4.le_closure_cls (h : EndCfg4 G T Y) {t : ↥G} (ht : orderOf t = 2) :
    Y.subgroupOf G ≤ Subgroup.closure (cls t) := by
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hXG : conjClosure Y G ≤ G := conjClosure_le hYG
  have hΛn : ((conjClosure Y G).subgroupOf G).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXG).mpr le_normalizer_conjClosure
  have hqsX : CFSG.IsQuasisimple ↥(conjClosure Y G) :=
    ⟨⟨h.quasi.1⟩, h.quasi.2,
      ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ h.quasi⟩
  have hqs : CFSG.IsQuasisimple ↥((conjClosure Y G).subgroupOf G) :=
    LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hXG).symm hqsX
  have hcent : Subgroup.centralizer (((conjClosure Y G).subgroupOf G : Subgroup ↥G) : Set ↥G) ≤
      (conjClosure Y G).subgroupOf G := by
    have := centralizer_generalizedFitting_le ↥G
    rwa [h.fstar] at this
  have htz : t ∉ (conjClosure Y G).subgroupOf G ⊓
      Subgroup.centralizer (((conjClosure Y G).subgroupOf G : Subgroup ↥G) : Set ↥G) := by
    rintro ⟨htΛ, htC⟩
    have hz : (⟨(t : MulAut V), htΛ⟩ : ↥(conjClosure Y G)) ∈
        Subgroup.center ↥(conjClosure Y G) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgΛ : (⟨(g : MulAut V), hXG g.2⟩ : ↥G) ∈ (conjClosure Y G).subgroupOf G := g.2
      have hgt := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp htC _ hgΛ)
      exact Subtype.ext hgt
    have hord : orderOf (⟨(t : MulAut V), htΛ⟩ : ↥(conjClosure Y G)) = 2 := by
      rw [← Subgroup.orderOf_coe]
      show orderOf (t : MulAut V) = 2
      rw [Subgroup.orderOf_coe]
      exact ht
    have hdvd := orderOf_dvd_natCard
      (⟨⟨(t : MulAut V), htΛ⟩, hz⟩ : ↥(Subgroup.center ↥(conjClosure Y G)))
    rw [← Subgroup.orderOf_coe, hord] at hdvd
    exact h.oddZ.not_two_dvd_nat hdvd
  have hΛN := emSetup_le_of_not_mem_zc (N := Subgroup.normalClosure {t}) hqs hcent
    (Subgroup.subset_normalClosure (Set.mem_singleton t)) htz
  have hNcls : Subgroup.normalClosure ({t} : Set ↥G) ≤ Subgroup.closure (cls t) := by
    refine Subgroup.closure_mono fun x hx => ?_
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff.mp ha] at hconj
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    exact ⟨c, rfl⟩
  exact fun y hy => hNcls (hΛN (le_conjClosure hy))

end Setup

end CFSG.CGT.PushingUpLit.CGT6

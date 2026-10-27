module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3Main
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open

section Solvable

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_inf_centralizer_of_isSylowTwoOf {K P : Subgroup G} (hP : IsSylowTwoOf P K) :
    Group.IsSolvable ↥(K ⊓ Subgroup.centralizer (P : Set G)) := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer (P : Set G) with hC
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hZ
  have hZC : Z ≤ C := le_inf (inf_le_left.trans hP.le) inf_le_right
  have hZ2 : IsPGroup 2 Z := hP.isPGroup.to_le inf_le_left
  have hW : ∀ W : Subgroup G, W ≤ C → IsPGroup 2 W → W ≤ Z := by
    intro W hWC hW2
    have hWN : W ≤ Subgroup.normalizer (P : Set G) := fun w hw =>
      Subgroup.centralizer_le_normalizer _ (hWC hw).2
    have hPW : IsPGroup 2 ↥(P ⊔ W) := hP.isPGroup.to_sup_of_normal_left' hW2 hWN
    have h1 : P ⊔ W = P :=
      hP.eq_of_le le_sup_left (sup_le hP.le (hWC.trans inf_le_left)) hPW
    exact le_inf (le_sup_right.trans h1.le) (hWC.trans inf_le_right)
  obtain ⟨S₀, hS₀⟩ := exists_isSylowTwoOf C
  have hZS₀ : Z = S₀ := hS₀.eq_of_le (hW S₀ hS₀.le hS₀.isPGroup) hZC hZ2
  have hZsyl : IsSylowTwoOf Z C := hZS₀ ▸ hS₀
  have hZcentral : ∀ c ∈ C, ∀ y ∈ Z, c * y = y * c := fun c hc y hy =>
    (Subgroup.mem_centralizer_iff.mp hc.2 y hy.1).symm
  have hZn : (Z.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : (g : G) * n * (g : G)⁻¹ = n := by
      rw [hZcentral g g.2 n hn]
      group
    show (g : G) * (n : G) * (g : G)⁻¹ ∈ Z
    rw [h1]
    exact hn
  have hsolvZ : Group.IsSolvable ↥(Z.subgroupOf C) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    have ha : ((a : ↥C) : G) ∈ Z := a.2
    have hb : ((b : ↥C) : G) ∈ Z := b.2
    have h1 : ((b : ↥C) : G) * ((a : ↥C) : G) = ((a : ↥C) : G) * ((b : ↥C) : G) :=
      Subgroup.mem_centralizer_iff.mp ha.2 _ hb.1
    exact Subtype.ext (Subtype.ext h1.symm)
  have hnd : ¬ 2 ∣ (Z.subgroupOf C).index := hZsyl.2.2
  have hodd : Odd (Nat.card (↥C ⧸ Z.subgroupOf C)) := by
    rw [← Subgroup.index_eq_card]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  have hsolvQ : Group.IsSolvable (↥C ⧸ Z.subgroupOf C) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_subgroup_quotient (Z.subgroupOf C)

omit [Finite G] in
theorem eq_one_of_perfect_of_isSolvable {Γ A : Type*} [Group Γ] [Group A] [hA : Group.IsSolvable A]
    (hΓ : Group.IsPerfect Γ) (f : Γ →* A) (γ : Γ) : f γ = 1 := by
  obtain ⟨n, hn⟩ := hA.solvable
  have hds : ∀ m : ℕ, derivedSeries Γ m = ⊤ := by
    intro m
    induction m with
    | zero => exact derivedSeries_zero Γ
    | succ m ih => rw [derivedSeries_succ, ih]; exact Group.isPerfect_def.mp hΓ
  have h1 : f γ ∈ (derivedSeries Γ n).map f :=
    Subgroup.mem_map_of_mem f (by rw [hds n]; trivial)
  have h2 := map_derivedSeries_le_derivedSeries f n h1
  rw [hn, Subgroup.mem_bot] at h2
  exact h2

end Solvable

section Components

variable {G : Type} [Group G]

theorem subgroupOf_isSubnormal_of_le {L C A : Subgroup G} (hCA : C ≤ A)
    (h : (L.subgroupOf A).IsSubnormal) : (L.subgroupOf C).IsSubnormal := by
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := h.subgroupOf
  have hcomap : L.subgroupOf C = ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).comap
      (Subgroup.subgroupOfEquivOfLe hCA).symm.toMonoidHom := by
    ext x
    rfl
  rw [hcomap]
  exact h1.comap _

theorem subgroupOf_isSubnormal_iff {L C A : Subgroup G} (hLC : L ≤ C) (hCA : C ≤ A)
    (hC : (C.subgroupOf A).IsSubnormal) :
    (L.subgroupOf A).IsSubnormal ↔ (L.subgroupOf C).IsSubnormal := by
  refine ⟨subgroupOf_isSubnormal_of_le hCA, fun h => ?_⟩
  have hcomap : (L.subgroupOf A).subgroupOf (C.subgroupOf A) =
      (L.subgroupOf C).comap (Subgroup.subgroupOfEquivOfLe hCA).toMonoidHom := by
    ext x
    rfl
  have h1 : ((L.subgroupOf A).subgroupOf (C.subgroupOf A)).IsSubnormal := by
    rw [hcomap]
    exact h.comap _
  exact Subgroup.IsSubnormal.trans (fun x hx => hLC hx) h1 hC

theorem isComponentIn_of_le_of_isSubnormal {L X H : Subgroup G} (hL : IsComponentIn L X)
    (hXH : X ≤ H) (hsub : (L.subgroupOf H).IsSubnormal) : IsComponentIn L H := by
  have hLH : L ≤ H := hL.1.trans hXH
  exact ⟨hLH, CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm
    (BenderBranch.isQuasisimple_of_isComponentIn hL), hsub⟩

theorem normalizer_le_normalizer_centralizer (V : Subgroup G) :
    Subgroup.normalizer (V : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have hfwd : ∀ g ∈ Subgroup.normalizer (V : Set G), ∀ c ∈ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (inv_mem hg) v).1 hv
    have hwc := Subgroup.mem_centralizer_iff.1 hc _ hw
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [hwc]
      _ = g * c * g⁻¹ * v := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨hfwd g hg c, fun hc => ?_⟩
  have h := hfwd g⁻¹ (inv_mem hg) _ hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h

theorem charTwo_of_normal_of_quotient {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN : CharTwo N)
    (hquot : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : CharTwo X := by
  set Q := pCoreOf 2 X with hQ
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  have hON : pCoreOf 2 N ≤ Q := by
    refine le_pCoreOf_of_normal_pGroup
      ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N).trans hNX) ?_
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N)
    exact hXN.trans
      (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 N)
  set C : Subgroup G := X ⊓ Subgroup.centralizer (Q : Set G) with hC
  have hC2 : IsPGroup 2 ↥C := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk⟩ := hquot g hg.1
    have hgc : g ^ 2 ^ k ∈ Subgroup.centralizer (pCoreOf 2 N : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Commute.pow_right (show Commute q g from
        Subgroup.mem_centralizer_iff.mp hg.2 q (hON hq)) _).eq
    have hmem : g ^ 2 ^ k ∈ pCoreOf 2 N := hN ⟨hk, hgc⟩
    obtain ⟨j, hj⟩ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N ⟨_, hmem⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hXC : X ≤ Subgroup.normalizer (C : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf X X _
      Subgroup.le_normalizer (hXQ.trans (normalizer_le_normalizer_centralizer Q))
  have hCQ : C ≤ Q := le_pCoreOf_of_normal_pGroup inf_le_left hXC hC2
  exact fun c hc => hCQ hc

end Components

end CFSG.QuasithinUnique.Fin253

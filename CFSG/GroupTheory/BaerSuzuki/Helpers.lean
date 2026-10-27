module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace BaerSuzuki.Helpers

universe u

theorem subgroup_isSubnormal_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (H : Subgroup G) : H.IsSubnormal := by
  classical
  let : Group.IsNilpotent G := hG.isNilpotent
  refine WellFounded.induction (Finite.to_wellFoundedGT : WellFoundedGT (Subgroup G)) H ?_
  intro K ih
  by_cases hK : K = ⊤
  · subst K
    exact Subgroup.Normal.isSubnormal Subgroup.normal_top
  · have hNK : K < Subgroup.normalizer (K : Set G) := by
      refine lt_of_le_of_ne Subgroup.le_normalizer ?_
      intro hEq
      exact hK ((normalizerCondition_iff_only_full_group_self_normalizing.mp
        Group.normalizerCondition_of_isNilpotent) K hEq.symm)
    refine Subgroup.IsSubnormal.trans Subgroup.le_normalizer ?_ (ih _ hNK)
    exact Subgroup.Normal.isSubnormal (by infer_instance)

theorem pCore_normal {G : Type*} [Group G] (p : ℕ) :
    (CFSG.pCore p G).Normal := by
  apply Subgroup.sSup_normal
  intro N hN
  exact hN.1

theorem pCore_isPGroup {G : Type*} [Group G] (p : ℕ) :
    IsPGroup p (CFSG.pCore p G) := by
  apply Sylow.sSup_of_normal
  · intro N hN
    exact hN.2
  · intro N hN
    exact hN.1

theorem le_pCore_of_normal_isPGroup
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G}
    (hHn : H.Normal) (hHp : IsPGroup p H) :
    H ≤ CFSG.pCore p G := by
  exact le_sSup ⟨hHn, hHp⟩

theorem pCore_characteristic {G : Type*} [Group G] (p : ℕ) :
    (CFSG.pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  apply le_pCore_of_normal_isPGroup
  · exact (pCore_normal (G := G) p).map φ.toMonoidHom φ.surjective
  · exact (pCore_isPGroup (G := G) p).map φ.toMonoidHom

theorem mem_pCore_of_mem_pCore_normal
    {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (hN : N.Normal) {x : G} (hxN : x ∈ N)
    (hx : (⟨x, hxN⟩ : N) ∈ CFSG.pCore p N) :
    x ∈ CFSG.pCore p G := by
  let : N.Normal := hN
  let : (CFSG.pCore p N).Characteristic :=
    pCore_characteristic p
  let K : Subgroup G :=
    (CFSG.pCore p N).map N.subtype
  have hKn : K.Normal := by
    dsimp [K]
    infer_instance
  have hKp : IsPGroup p K := by
    exact (pCore_isPGroup (G := N) p).map N.subtype
  apply le_pCore_of_normal_isPGroup hKn hKp
  exact ⟨⟨x, hxN⟩, hx, rfl⟩

theorem pairwise_conjugates_subgroup
    {G : Type*} [Group G] {p : ℕ} (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (N : Subgroup G) (hxN : x ∈ N) :
    ∀ g : N, IsPGroup p
      (Subgroup.closure
        ({(⟨x, hxN⟩ : N), g * ⟨x, hxN⟩ * g⁻¹} : Set N)) := by
  intro g
  apply ((h (g : G)).comap_of_injective N.subtype N.subtype_injective).to_le
  rw [Subgroup.closure_le]
  rintro y (rfl | hy)
  · exact Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp))
  · rw [Set.mem_singleton_iff] at hy
    subst y
    apply Subgroup.mem_comap.mpr
    apply Subgroup.subset_closure
    simp

theorem pairwise_conjugates_of_isConj
    {G : Type*} [Group G] {p : ℕ} {x y : G}
    (hxy : IsConj x y)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    ∀ g : G, IsPGroup p
      (Subgroup.closure ({y, g * y * g⁻¹} : Set G)) := by
  obtain ⟨a, rfl⟩ := isConj_iff.mp hxy
  intro g
  have hp := (h (a⁻¹ * g * a)).map (MulAut.conj a).toMonoidHom
  have hsecond :
      (MulAut.conj a) (a⁻¹ * g * a * x * (a⁻¹ * g * a)⁻¹) =
        g * (a * x * a⁻¹) * g⁻¹ := by
    simp only [MulAut.conj_apply]
    group
  rw [MonoidHom.map_closure] at hp
  change IsPGroup p (Subgroup.closure
    ((MulAut.conj a : G → G) ''
      {x, a⁻¹ * g * a * x * (a⁻¹ * g * a)⁻¹})) at hp
  rw [Set.image_insert_eq, Set.image_singleton, hsecond] at hp
  exact hp

theorem exists_conjugate_enlargement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {S P K : Subgroup G} (hSP : S ≤ P) (hPK : P ≤ K)
    (hP : IsPGroup p P) (hPnK : K ≤ Subgroup.normalizer (P : Set G))
    (hSnK : ¬ K ≤ Subgroup.normalizer (S : Set G)) :
    ∃ a : G, a ∈ K ∧ a ∉ Subgroup.normalizer (S : Set G) ∧
      S.map (MulAut.conj a).toMonoidHom ≤
        P ⊓ Subgroup.normalizer (S : Set G) := by
  classical
  by_cases hSnP : (S.subgroupOf P).Normal
  · have hPle : P ≤ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mp hSnP
    obtain ⟨a, haK, haS⟩ := SetLike.not_le_iff_exists.mp hSnK
    refine ⟨a, haK, haS, ?_⟩
    rintro y ⟨s, hs, rfl⟩
    have hconjP : a * s * a⁻¹ ∈ P :=
      (hPnK haK s).mp (hSP hs)
    exact ⟨hconjP, hPle hconjP⟩
  · let A : Subgroup P := S.subgroupOf P
    let B : Subgroup P := Subgroup.normalizer (A : Set P)
    have hBne : B ≠ ⊤ := by
      intro hB
      apply hSnP
      exact Subgroup.normalizer_eq_top_iff.mp hB
    let : Group.IsNilpotent P := hP.isNilpotent
    have hBlt : B < Subgroup.normalizer (B : Set P) := by
      refine lt_of_le_of_ne Subgroup.le_normalizer ?_
      intro hEq
      exact hBne ((normalizerCondition_iff_only_full_group_self_normalizing.mp
        Group.normalizerCondition_of_isNilpotent) B hEq.symm)
    obtain ⟨a, haB, haNB⟩ := SetLike.exists_of_lt hBlt
    refine ⟨(a : G), hPK a.2, ?_, ?_⟩
    · intro haS
      apply haNB
      change a ∈ Subgroup.normalizer (A : Set P)
      rw [← Subgroup.subgroupOf_normalizer_eq hSP]
      exact haS
    · rintro y ⟨s, hs, rfl⟩
      have hsA : (⟨s, hSP hs⟩ : P) ∈ A := hs
      have hsB : (⟨s, hSP hs⟩ : P) ∈ B := Subgroup.le_normalizer hsA
      have hconjB := (haB (⟨s, hSP hs⟩ : P)).mp hsB
      have hconjP : (a : G) * s * (a : G)⁻¹ ∈ P := by
        exact P.mul_mem (P.mul_mem a.2 (hSP hs)) (P.inv_mem a.2)
      have hconjNorm : (a : G) * s * (a : G)⁻¹ ∈
          Subgroup.normalizer (S : Set G) := by
        have hz : (⟨(a : G) * s * (a : G)⁻¹, hconjP⟩ : P) ∈
            (Subgroup.normalizer (S : Set G)).subgroupOf P := by
          rw [Subgroup.subgroupOf_normalizer_eq hSP]
          exact hconjB
        exact hz
      exact ⟨hconjP, hconjNorm⟩

theorem map_pCore_le {G : Type*} [Group G] {p : ℕ} (K : Subgroup G) :
    (CFSG.pCore p K).map K.subtype ≤ K := by
  rintro y ⟨z, _hz, rfl⟩
  exact z.2

theorem le_normalizer_map_pCore
    {G : Type*} [Group G] {p : ℕ} (K : Subgroup G) :
    K ≤ Subgroup.normalizer
      ((CFSG.pCore p K).map K.subtype : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk y hy
  obtain ⟨z, hz, rfl⟩ := hy
  let kk : K := ⟨k, hk⟩
  refine ⟨kk * z * kk⁻¹, (pCore_normal (G := K) p).conj_mem z hz kk, ?_⟩
  rfl

theorem closure_le_map_pCore
    {G : Type*} [Group G] {p : ℕ} {x : G} {C : Set G}
    (hC : C ⊆ Group.conjugatesOfSet ({x} : Set G))
    (K : Subgroup G) (hCK : Subgroup.closure C ≤ K)
    (hlocal : ∀ c : G, c ∈ Group.conjugatesOfSet ({x} : Set G) →
      ∀ hcK : c ∈ K,
        (⟨c, hcK⟩ : K) ∈ CFSG.pCore p K) :
    Subgroup.closure C ≤
      (CFSG.pCore p K).map K.subtype := by
  rw [Subgroup.closure_le]
  intro c hc
  have hcK : c ∈ K := hCK (Subgroup.subset_closure hc)
  exact ⟨⟨c, hcK⟩, hlocal c (hC hc) hcK, rfl⟩

theorem closure_subnormal_in_proper_overgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {x : G} {C : Set G}
    (hC : C ⊆ Group.conjugatesOfSet ({x} : Set G))
    (K : Subgroup G) (hCK : Subgroup.closure C ≤ K)
    (hlocal : ∀ c : G, c ∈ Group.conjugatesOfSet ({x} : Set G) →
      ∀ hcK : c ∈ K,
        (⟨c, hcK⟩ : K) ∈ CFSG.pCore p K) :
    (Subgroup.closure C).subgroupOf K |>.IsSubnormal := by
  let P : Subgroup G :=
    (CFSG.pCore p K).map K.subtype
  have hSP : Subgroup.closure C ≤ P :=
    closure_le_map_pCore hC K hCK hlocal
  have hPK : P ≤ K := map_pCore_le K
  have hPp : IsPGroup p P :=
    (pCore_isPGroup (G := K) p).map K.subtype
  have hPnormK : (P.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_map_pCore K)
  have hSPK : (Subgroup.closure C).subgroupOf K ≤ P.subgroupOf K := by
    intro s hs
    exact hSP hs
  have hPsubP : IsPGroup p (P.subgroupOf K) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  exact Subgroup.IsSubnormal.trans hSPK
    (subgroup_isSubnormal_of_isPGroup hPsubP _) hPnormK.isSubnormal

theorem unique_coatom_of_closure_conjugates
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (hlocal : ∀ (K : Subgroup G), K < ⊤ →
      ∀ c : G, c ∈ Group.conjugatesOfSet ({x} : Set G) →
      ∀ hcK : c ∈ K,
        (⟨c, hcK⟩ : K) ∈ CFSG.pCore p K)
    {C : Set G} (hC : C ⊆ Group.conjugatesOfSet ({x} : Set G))
    (hCp : IsPGroup p (Subgroup.closure C))
    (hCnot : ¬(Subgroup.closure C).IsSubnormal) :
    ∃! M : Subgroup G, IsCoatom M ∧ Subgroup.closure C ≤ M := by
  classical
  let motive : Subgroup G → Prop := fun S =>
    ∀ (D : Set G), Subgroup.closure D = S →
      D ⊆ Group.conjugatesOfSet ({x} : Set G) →
      IsPGroup p S → ¬S.IsSubnormal →
      ∃! M : Subgroup G, IsCoatom M ∧ S ≤ M
  have hall : ∀ S : Subgroup G, motive S := by
    intro S
    refine WellFounded.induction (Finite.to_wellFoundedGT : WellFoundedGT (Subgroup G)) S ?_
    intro S ih D hDS hD hSp hSnot
    have hSnorm : ¬S.Normal := fun h => hSnot h.isSubnormal
    have hNne : Subgroup.normalizer (S : Set G) ≠ ⊤ := by
      simpa [Subgroup.normalizer_eq_top_iff] using hSnorm
    obtain hNtop | ⟨M, hM, hNM⟩ :=
      IsCoatomic.eq_top_or_exists_le_coatom (Subgroup.normalizer (S : Set G))
    · exact (hNne hNtop).elim
    have hSM : S ≤ M := Subgroup.le_normalizer.trans hNM
    refine ⟨M, ⟨hM, hSM⟩, ?_⟩
    intro K hK
    rcases hK with ⟨hK, hSK⟩
    by_cases hKnS : K ≤ Subgroup.normalizer (S : Set G)
    · exact ((hK.le_iff_eq hM.ne_top).mp (hKnS.trans hNM)).symm
    · let P : Subgroup G :=
        (CFSG.pCore p K).map K.subtype
      have hKtop : K < ⊤ := hK.lt_top
      have hSP : S ≤ P := by
        rw [← hDS]
        exact closure_le_map_pCore hD K (by simpa [hDS] using hSK)
          (fun c hc hcK => hlocal K hKtop c hc hcK)
      have hPK : P ≤ K := map_pCore_le K
      have hPp : IsPGroup p P :=
        (pCore_isPGroup (G := K) p).map K.subtype
      have hPnK : K ≤ Subgroup.normalizer (P : Set G) :=
        le_normalizer_map_pCore K
      obtain ⟨a, haK, haS, haMap⟩ :=
        exists_conjugate_enlargement hSP hPK hPp hPnK hKnS
      let T : Subgroup G := S ⊔ S.map (MulAut.conj a).toMonoidHom
      have hST : S ≤ T := le_sup_left
      have hTP : T ≤ P := sup_le hSP (haMap.trans inf_le_left)
      have hTN : T ≤ Subgroup.normalizer (S : Set G) :=
        sup_le Subgroup.le_normalizer (haMap.trans inf_le_right)
      have hTM : T ≤ M := hTN.trans hNM
      have hTK : T ≤ K := hTP.trans hPK
      have hSTlt : S < T := by
        refine hST.lt_of_ne ?_
        intro hEq
        have hmapS : S.map (MulAut.conj a).toMonoidHom ≤ S := by
          have hr : S.map (MulAut.conj a).toMonoidHom ≤ T := le_sup_right
          exact hr.trans (le_of_eq hEq.symm)
        have hcard : Nat.card S ≤
            Nat.card (S.map (MulAut.conj a).toMonoidHom) := by
          exact (Subgroup.card_map_of_injective (K := S)
            (MulAut.conj a).injective).ge
        have heqmap : S.map (MulAut.conj a).toMonoidHom = S :=
          Subgroup.eq_of_le_of_card_ge hmapS hcard
        exact haS (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heqmap)
      have hTp : IsPGroup p T := hPp.to_le hTP
      let E : Set G := D ∪ (MulAut.conj a : G → G) '' D
      have hET : Subgroup.closure E = T := by
        dsimp [E, T]
        rw [Subgroup.closure_union]
        have hm := (MonoidHom.map_closure (MulAut.conj a).toMonoidHom D).symm
        change Subgroup.closure ((MulAut.conj a : G → G) '' D) =
          (Subgroup.closure D).map (MulAut.conj a).toMonoidHom at hm
        rw [hm, hDS]
        change S ⊔ S.map (MulAut.conj a).toMonoidHom =
          S ⊔ S.map (MulAut.conj a).toMonoidHom
        rfl
      have hE : E ⊆ Group.conjugatesOfSet ({x} : Set G) := by
        rintro y (hy | ⟨z, hz, rfl⟩)
        · exact hD hy
        · exact Group.conj_mem_conjugatesOfSet (hD hz)
      have hTnot : ¬T.IsSubnormal := by
        intro hTsub
        have hSsubT : (S.subgroupOf T).IsSubnormal := by
          rw [← hDS]
          apply closure_subnormal_in_proper_overgroup (p := p) (x := x) hD T
            (by simpa [hDS] using hST)
          intro c hc hcT
          exact hlocal T (hTM.trans_lt hM.lt_top) c hc hcT
        exact hSnot (Subgroup.IsSubnormal.trans hST hSsubT hTsub)
      obtain ⟨U, hU, hUuniq⟩ := ih T hSTlt E hET hE hTp hTnot
      have hMU : M = U := hUuniq M ⟨hM, hTM⟩
      have hKU : K = U := hUuniq K ⟨hK, hTK⟩
      exact hKU.trans hMU.symm
  exact hall (Subgroup.closure C) C rfl hC hCp hCnot

theorem mem_pCore_of_pairwise_conjugates_top
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (hlocal : ∀ (K : Subgroup G), K < ⊤ →
      ∀ c : G, c ∈ Group.conjugatesOfSet ({x} : Set G) →
      ∀ hcK : c ∈ K,
        (⟨c, hcK⟩ : K) ∈ CFSG.pCore p K)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (htop : Subgroup.normalClosure ({x} : Set G) = ⊤) :
    x ∈ CFSG.pCore p G := by
  classical
  let S : Subgroup G := Subgroup.closure ({x} : Set G)
  have hxS : x ∈ S := Subgroup.subset_closure (by simp)
  have hSp : IsPGroup p S := by
    have hp := h (1 : G)
    have hs : ({x, (1 : G) * x * (1 : G)⁻¹} : Set G) = {x} := by simp
    rw [hs] at hp
    exact hp
  by_cases hSsub : S.IsSubnormal
  · rcases hSsub.lt_normal with hSt | ⟨N, hNn, hSN, hNt⟩
    · apply le_pCore_of_normal_isPGroup Subgroup.normal_top
        (by rw [hSt] at hSp; exact hSp)
      exact Subgroup.mem_top x
    · apply mem_pCore_of_mem_pCore_normal hNn (hSN hxS)
      exact hlocal N hNt x
        (Group.subset_conjugatesOfSet (by simp)) (hSN hxS)
  · have hC : ({x} : Set G) ⊆ Group.conjugatesOfSet ({x} : Set G) :=
      Group.subset_conjugatesOfSet
    obtain ⟨M, ⟨hM, hSM⟩, hMuniq⟩ :=
      unique_coatom_of_closure_conjugates x hlocal hC hSp hSsub
    by_cases hgen : ∃ g : G,
        Subgroup.closure ({x, g * x * g⁻¹} : Set G) = ⊤
    · obtain ⟨g, hg⟩ := hgen
      apply le_pCore_of_normal_isPGroup Subgroup.normal_top
        (by have hp := h g; rw [hg] at hp; exact hp)
      exact Subgroup.mem_top x
    · have hconjM : ∀ g : G, g * x * g⁻¹ ∈ M := by
        intro g
        let Q : Subgroup G :=
          Subgroup.closure ({x, g * x * g⁻¹} : Set G)
        have hQne : Q ≠ ⊤ := fun hQt => hgen ⟨g, hQt⟩
        obtain hQt | ⟨K, hK, hQK⟩ :=
          IsCoatomic.eq_top_or_exists_le_coatom Q
        · exact (hQne hQt).elim
        have hSK : S ≤ K := by
          change Subgroup.closure ({x} : Set G) ≤ K
          rw [Subgroup.closure_le]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst y
          apply hQK
          apply Subgroup.subset_closure
          simp
        have hKM : K = M := hMuniq K ⟨hK, hSK⟩
        rw [← hKM]
        exact hQK (Subgroup.subset_closure (by simp))
      have hnle : Subgroup.normalClosure ({x} : Set G) ≤ M := by
        rw [Subgroup.normalClosure, Subgroup.closure_le]
        intro y hy
        rcases Group.mem_conjugatesOfSet_iff.mp hy with ⟨z, hz, hzy⟩
        rw [Set.mem_singleton_iff] at hz
        subst z
        obtain ⟨g, rfl⟩ := isConj_iff.mp hzy
        exact hconjM g
      rw [htop] at hnle
      exact (hM.ne_top (top_unique hnle)).elim

theorem mem_pCore_of_pairwise_conjugates
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G))) :
    x ∈ CFSG.pCore p G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (A : Type u) [Group A] [Finite A] (y : A), Nat.card A = n →
      (∀ g : A, IsPGroup p
        (Subgroup.closure ({y, g * y * g⁻¹} : Set A))) →
      y ∈ CFSG.pCore p A
  have hP : ∀ n : ℕ, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp [P]
      intro A _instGroup _instFinite y hcard hy
      let N : Subgroup A := Subgroup.normalClosure ({y} : Set A)
      have hyN : y ∈ N := Subgroup.subset_normalClosure (by simp)
      by_cases hNtop : N = ⊤
      · have hlocal : ∀ (K : Subgroup A), K < ⊤ →
            ∀ c : A, c ∈ Group.conjugatesOfSet ({y} : Set A) →
            ∀ hcK : c ∈ K,
              (⟨c, hcK⟩ : K) ∈
                CFSG.pCore p K := by
          intro K hKt c hc hcK
          have hKcardA : Nat.card K < Nat.card A := by
            refine lt_of_le_of_ne (Subgroup.card_le_card_group K) ?_
            intro heq
            exact hKt.ne (Subgroup.card_eq_iff_eq_top K |>.mp heq)
          have hKcard : Nat.card K < n := by simpa [hcard] using hKcardA
          obtain ⟨z, hz, hzc⟩ := Group.mem_conjugatesOfSet_iff.mp hc
          rw [Set.mem_singleton_iff] at hz
          subst z
          have hcy := pairwise_conjugates_of_isConj hzc hy
          exact ih (Nat.card K) hKcard K (⟨c, hcK⟩ : K) rfl
            (pairwise_conjugates_subgroup c hcy K hcK)
        exact mem_pCore_of_pairwise_conjugates_top y hlocal hy hNtop
      · have hNt : N < ⊤ := lt_top_iff_ne_top.mpr hNtop
        have hNcardA : Nat.card N < Nat.card A := by
          refine lt_of_le_of_ne (Subgroup.card_le_card_group N) ?_
          intro heq
          exact hNtop (Subgroup.card_eq_iff_eq_top N |>.mp heq)
        have hNcard : Nat.card N < n := by simpa [hcard] using hNcardA
        have hyr := ih (Nat.card N) hNcard N (⟨y, hyN⟩ : N) rfl
          (pairwise_conjugates_subgroup y hy N hyN)
        exact mem_pCore_of_mem_pCore_normal Subgroup.normalClosure_normal hyN hyr
  exact hP (Nat.card G) G x rfl h

end BaerSuzuki.Helpers

end CFSG

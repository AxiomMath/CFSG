module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbEdge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Rank2SL3
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Rank2Sp4
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.Rank2A6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcAdjacent
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCentral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev

open CFSG.Open CFSG.Quasithin CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.AGLEmbeddingD2.Tits.GN516.Edge Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}

private theorem le_of_perfect_of_twoQuotient {G : Type*} [Group G] [Finite G] {L N : Subgroup G}
    (hL : ⁅L, L⁆ = L) (hLN : L ≤ Subgroup.normalizer (N : Set G))
    (h2 : ∀ y ∈ L, ∃ k : ℕ, y ^ 2 ^ k ∈ N) : L ≤ N := by
  haveI : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hL
  have hMn : ((L ⊓ N).subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    exact ⟨L.mul_mem (L.mul_mem hk hh.1) (L.inv_mem hk),
      (Subgroup.mem_normalizer_iff.mp (hLN hk) h).mp hh.2⟩
  have hQ2 : IsPGroup 2 (L ⧸ (L ⊓ N).subgroupOf L) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h2 (y : G) y.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨(y ^ 2 ^ k).2, by simpa using hk⟩
  haveI : Group.IsPerfect (L ⧸ (L ⊓ N).subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hQs : Subsingleton (L ⧸ (L ⊓ N).subgroupOf L) := by
    by_contra hns
    haveI : Nontrivial (L ⧸ (L ⊓ N).subgroupOf L) := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isNilpotent _ (IsPGroup.isNilpotent hQ2)
  exact (Subgroup.subgroupOf_eq_top.mp (QuotientGroup.subsingleton_iff.mp hQs)).trans inf_le_right

theorem twoResidual_eq_self_of_perfect {G : Type*} [Group G] [Finite G] {X : Subgroup G}
    (h : ⁅X, X⁆ = X) : twoResidual X = X :=
  le_antisymm (twoResidual_le X)
    (le_iInf₂ fun N hN => le_of_perfect_of_twoQuotient h hN.2.1 hN.2.2)

theorem edgeLevi_symm {u v : Fin D.rank} (h : EdgeLevi D u v) : EdgeLevi D v u := by
  unfold EdgeLevi at h ⊢
  rw [sup_comm]
  exact h

private theorem card_eq_two_or_four_le (F : Type) [Field F] [Finite F] [CharP F 2] :
    Nat.card F = 2 ∨ 4 ≤ Nat.card F := by
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  have hpos := n.pos
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · left
    have h1 : (n : ℕ) = 1 := by omega
    rw [h1]
    norm_num
  · right
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem edgeLevi_of_sl3 {F : Type} [Field F] [Finite F] [CharP F 2] {u v : Fin D.rank}
    (l : SpecialLinearGroup (Fin 3) F →* K) (hl : Function.Injective l)
    (hr : l.range = rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) : EdgeLevi D u v := by
  haveI : Fintype F := Fintype.ofFinite F
  have hp : ⁅(⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)), ⊤⁆ = ⊤ := sl3_perfect F
  have hXperf : ⁅rankOne D.rootGroup u ⊔ rankOne D.rootGroup v,
      rankOne D.rootGroup u ⊔ rankOne D.rootGroup v⁆ =
        rankOne D.rootGroup u ⊔ rankOne D.rootGroup v := by
    rw [← hr]
    have h1 := Subgroup.map_commutator (f := l) (⊤ : Subgroup (SpecialLinearGroup (Fin 3) F)) ⊤
    rw [hp, ← MonoidHom.range_eq_map] at h1
    exact h1.symm
  have hres : twoResidual (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) =
      rankOne D.rootGroup u ⊔ rankOne D.rootGroup v :=
    twoResidual_eq_self_of_perfect hXperf
  have e : SpecialLinearGroup (Fin 3) F ≃* ↥(rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) :=
    (MonoidHom.ofInjective hl).trans (MulEquiv.subgroupCongr hr)
  have hX : IsQuasisimpleTwoNonab ↥(rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) :=
    IsQuasisimpleTwoNonab.of_mulEquiv e (isQuasisimpleTwoNonab_sl3 F)
  unfold EdgeLevi
  rw [hres]
  exact hX

theorem edgeLevi_of_simplyLacedLevis {F : Type} [Field F] [Finite F] [CharP F 2]
    {adj : Fin D.rank → Fin D.rank → Prop} {x : (Fin D.rank → ℤ) → F → K}
    (hL : CFSG.Timmesfeld.SimplyLacedLevis D F adj x) {u v : Fin D.rank} (huv : adj u v) :
    EdgeLevi D u v := by
  obtain ⟨l, hl, hlt⟩ := hL.sl3 u v huv
  have hroot : ∀ k : Fin D.rank, (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots ∧
      (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := fun k =>
    ⟨(CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k,
      (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        ((CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)⟩
  have hX1 : D.rootGroup (Pi.single u 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot u).1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 0 1 c, (hlt c).1⟩
  have hX2 : D.rootGroup (-Pi.single u 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot u).2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 0 c, (hlt c).2.1⟩
  have hX3 : D.rootGroup (Pi.single v 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot v).1 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 1 2 c, (hlt c).2.2.1⟩
  have hX4 : D.rootGroup (-Pi.single v 1) ≤ l.range := fun g hg => by
    obtain ⟨c, rfl⟩ := hL.surj _ (hroot v).2 g hg
    exact MonoidHom.mem_range.mpr ⟨CFSG.Timmesfeld.tv 2 1 c, (hlt c).2.2.2.1⟩
  have hle : l.range ≤ rankOne D.rootGroup u ⊔ rankOne D.rootGroup v := by
    intro z hz
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hz
    exact CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional.range_le_of_sl3
      hL huv hlt g
  have hge : rankOne D.rootGroup u ⊔ rankOne D.rootGroup v ≤ l.range :=
    sup_le (sup_le hX1 hX2) (sup_le hX3 hX4)
  exact edgeLevi_of_sl3 l hl (le_antisymm hle hge)

theorem edgeLevi_of_sp4 {F : Type} [Field F] [Finite F] [CharP F 2] {u v : Fin D.rank}
    (l : StatedSp 2 F →* K) (hl : Function.Injective l)
    (hr : l.range = rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) : EdgeLevi D u v := by
  haveI : Fintype F := Fintype.ofFinite F
  have hres : (twoResidual (⊤ : Subgroup (StatedSp 2 F))).map l =
      twoResidual (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) := by
    rw [CFSG.AGLEmbeddingD2.Tits.GN516.map_twoResidual, ← MonoidHom.range_eq_map, hr]
  have hS : IsQuasisimpleTwoNonab ↥(twoResidual (⊤ : Subgroup (StatedSp 2 F))) := by
    rcases card_eq_two_or_four_le F with hq | hq
    ·
      have hK : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hq
      let e₀ : StatedSp 2 F ≃* Equiv.Perm (Fin 6) :=
        CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm F hK
      have hperfA6 : ⁅alternatingGroup (Fin 6), alternatingGroup (Fin 6)⁆ =
          alternatingGroup (Fin 6) := by
        haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
          ⟨isQuasisimpleTwoNonab_alternatingGroup_six.1⟩
        exact Subgroup.commutator_eq_self
      have hnorm : Subgroup.normalizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr inferInstance
      have hA6 : twoResidual (⊤ : Subgroup (Equiv.Perm (Fin 6))) = alternatingGroup (Fin 6) := by
        apply le_antisymm
        · refine twoResidual_le_of_isTwoQuotient le_top hnorm.ge ?_
          intro x _
          refine ⟨1, ?_⟩
          rw [Equiv.Perm.mem_alternatingGroup, map_pow, pow_one, Int.units_sq]
        · refine le_iInf₂ fun N hN => ?_
          exact le_of_perfect_of_twoQuotient hperfA6 (le_trans le_top hN.2.1)
            (fun y _ => hN.2.2 y (Subgroup.mem_top y))
      have hmap : (twoResidual (⊤ : Subgroup (StatedSp 2 F))).map e₀.toMonoidHom =
          alternatingGroup (Fin 6) := by
        rw [CFSG.AGLEmbeddingD2.Tits.GN516.map_twoResidual,
          Subgroup.map_top_of_surjective e₀.toMonoidHom e₀.surjective, hA6]
      have e' : ↥(twoResidual (⊤ : Subgroup (StatedSp 2 F))) ≃* ↥(alternatingGroup (Fin 6)) :=
        (Subgroup.equivMapOfInjective _ e₀.toMonoidHom e₀.injective).trans
          (MulEquiv.subgroupCongr hmap)
      exact IsQuasisimpleTwoNonab.of_mulEquiv e'.symm isQuasisimpleTwoNonab_alternatingGroup_six
    ·
      obtain ⟨hperf, -, -⟩ := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 F (by norm_num)
        (Or.inl (Or.inr hq))
      rw [twoResidual_eq_self_of_perfect (X := (⊤ : Subgroup (StatedSp 2 F)))
        hperf.commutator_eq_top]
      exact IsQuasisimpleTwoNonab.of_mulEquiv Subgroup.topEquiv.symm
        (isQuasisimpleTwoNonab_sp4 F hq)
  have e : ↥(twoResidual (⊤ : Subgroup (StatedSp 2 F))) ≃*
      ↥(twoResidual (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v)) :=
    (Subgroup.equivMapOfInjective _ l hl).trans (MulEquiv.subgroupCongr hres)
  unfold EdgeLevi
  exact IsQuasisimpleTwoNonab.of_mulEquiv e hS

theorem degree_ne_of_path {m : ℕ} (hm : 3 ≤ m) {A : Matrix (Fin m) (Fin m) ℤ}
    (hA : TauCeti.IsFiniteType A)
    (hpath : ∀ i j : Fin m, i ≠ j → (A i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val))
    {i j : Fin m} (hi : i.val + 1 = m) (hj : j.val + 2 = m) :
    (TauCeti.diagramGraph A).degree i ≠ (TauCeti.diagramGraph A).degree j := by
  obtain ⟨a, ha⟩ : ∃ a : Fin m, a.val + 2 = m :=
    ⟨⟨m - 2, by omega⟩, by show m - 2 + 2 = m; omega⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin m, b.val + 3 = m :=
    ⟨⟨m - 3, by omega⟩, by show m - 3 + 3 = m; omega⟩
  have hij : i ≠ j := fun h => by subst h; omega
  have hib : i ≠ b := fun h => by have := congrArg Fin.val h; omega
  have hjb : j ≠ b := fun h => by have := congrArg Fin.val h; omega
  have hdi : (TauCeti.diagramGraph A).degree i ≤ 1 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_le_one]
    have key : ∀ x ∈ (TauCeti.diagramGraph A).neighborFinset i, x = a := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset, hA.diagramGraph_adj_iff] at hx
      obtain ⟨hne, h0⟩ := hx
      rcases (hpath i x hne).mp h0 with h1 | h1
      · have := x.isLt
        omega
      · exact Fin.ext (by omega)
    intro x hx y hy
    rw [key x hx, key y hy]
  have hdj : 2 ≤ (TauCeti.diagramGraph A).degree j := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have hsub : ({i, b} : Finset (Fin m)) ⊆ (TauCeti.diagramGraph A).neighborFinset j := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset, hA.diagramGraph_adj_iff]
      rcases Finset.mem_insert.mp hx with hxi | hxb
      · rw [hxi]
        exact ⟨hij.symm, (hpath j i hij.symm).mpr (Or.inl (by omega))⟩
      · rw [Finset.mem_singleton.mp hxb]
        exact ⟨hjb, (hpath j b hjb).mpr (Or.inr (by omega))⟩
    have hcard := Finset.card_le_card hsub
    rwa [Finset.card_pair hib] at hcard
  intro heq
  omega

end CFSG.AGLEmbeddingD2.Tits.GN516.EdgeLev

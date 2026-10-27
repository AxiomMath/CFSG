module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Rows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Type418
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Def


@[expose] def KF418ModelAltSpor : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L ∈ thetaComponents 3 G →
    (Sec4.IsList46Four (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsList46Five (L ⧸ aschbacherSolvableCore 3 L)) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
      a ∈ Subgroup.normalizer (L : Set G) → b ∈ Subgroup.normalizer (L : Set G) →
      b ∉ Sec4.thetaQuotCentralizer L → (∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L) →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → Sec8.IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
        ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField)

end Def

theorem card_centralizer_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    Nat.card (Subgroup.centralizer ({e x} : Set Y)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) := by
  have hmap : (Subgroup.centralizer ({x} : Set X)).map e.toMonoidHom =
      Subgroup.centralizer ({e x} : Set Y) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← hmap, Subgroup.card_map_of_injective e.injective]


theorem kF418ModelAltSpor_of_excl
    (hexcl : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X →
      (Sec4.IsList46Four X ∨ Sec4.IsList46Five X) →
      ∀ y : X ⧸ Subgroup.center X, orderOf y = 3 →
        ¬ (3 ^ 4 ∣ Nat.card (Subgroup.centralizer ({y} : Set (X ⧸ Subgroup.center X))) ∧
          7 ∣ Nat.card (Subgroup.centralizer ({y} : Set (X ⧸ Subgroup.center X))))) :
    KF418ModelAltSpor := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hT := type418Arith_of hn hKq htype
  obtain ⟨haK, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta (k := .field) K hKa (by decide)
  have hKM := le_of_mem_thetaComponentsIn hK
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := hKM.trans inf_le_right
  have hβ1 : rho L ⟨b, hbN⟩ ≠ 1 := fun h => hbC ⟨⟨b, hbN⟩, h, rfl⟩
  have hpow : ∀ (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)), g ^ 3 = 1 →
      rho L ⟨g, hg⟩ ^ 3 = 1 := by
    intro g hg hg3
    rw [← map_pow]
    have : (⟨g, hg⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simp [hg3])
    rw [this, map_one]
  have hαI : rho L ⟨a, haN⟩ ∈ innBar L := mem_range_conj_of_list46FourFive hq hl (hpow a haN ha3)
  have hβI : rho L ⟨b, hbN⟩ ∈ innBar L := mem_range_conj_of_list46FourFive hq hl (hpow b hbN hb3)
  obtain ⟨hβo, h81, h7⟩ :=
    exists_centralizer_of_inner hKL hKb ha3 hb3 hab haN hbN hβ1 haK hout hT hαI hβI
  set e := quotCenterEquivInn (L ⧸ aschbacherSolvableCore 3 L)
  set z : innBar L := ⟨rho L ⟨b, hbN⟩, hβI⟩
  have hcz := card_centralizer_subtype (innBar L) z
  have hce := card_centralizer_mulEquiv e.symm z
  refine hexcl _ hq hl (e.symm z) ?_ ⟨?_, ?_⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hβo
  · rw [hce, hcz]
    exact h81
  · rw [hce, hcz]
    exact h7

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

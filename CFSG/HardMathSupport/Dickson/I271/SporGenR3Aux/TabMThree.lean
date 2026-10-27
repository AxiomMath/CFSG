module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterTwoA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBCoset
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThreeBSylFact
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Witness
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.GmatGen

public section

set_option linter.unusedSectionVars false

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Blueprint CFSG.Monster.Existence CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Timmesfeld.ComponentBalance
  CFSG.LocalAnalysis.GLTheoremA CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Proving
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.AGLEmbedding.Norton.MON5_7 (tbw)

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (SylFact)

section Residuals

@[expose] def CentThreeA (G : Type) [Group G] : Prop :=
  ∀ k α : G, orderOf k = 3 → orderOf α = 2 →
    Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder →
    α * k * α⁻¹ = k⁻¹ →
    Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≃*
      NativeSporadic.Fi23) →
    CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({k} : Set G)) ∧
      Nonempty (↥(Subgroup.centralizer ({k} : Set G)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({k} : Set G)) ≃* NativeSporadic.Fi24prime)

@[expose] def CentThreeC (G : Type) [Group G] : Prop :=
  ∀ k α : G, orderOf k = 3 → orderOf α = 2 →
    Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder →
    α * k * α⁻¹ = k⁻¹ →
    Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≃*
      NativeSporadic.Th) →
    Nat.card ↥(Subgroup.centralizer ({k} : Set G)) ≤ 3 * 90745943887872000

end Residuals

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem tabMThree_mulEquiv_inf (e : G ≃* G') (α k : G) :
    Nonempty (↥(Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)) ≃*
      ↥(Subgroup.centralizer ({e α} : Set G') ⊓ Subgroup.centralizer ({e k} : Set G'))) := by
  have h : (Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({k} : Set G)).map
      e.toMonoidHom =
      Subgroup.centralizer ({e α} : Set G') ⊓ Subgroup.centralizer ({e k} : Set G') := by
    rw [Subgroup.map_inf _ _ _ e.injective, map_centralizer_singleton, map_centralizer_singleton]
  exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

theorem tabMThree_mulEquiv_cent (e : G ≃* G') (k : G) :
    Nonempty (↥(Subgroup.centralizer ({k} : Set G)) ≃* ↥(Subgroup.centralizer ({e k} : Set G'))) :=
  ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_singleton e k))⟩

theorem tabMThree_map_center {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    (Subgroup.center A).map φ.toMonoidHom = Subgroup.center B := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨a, rfl⟩ := φ.surjective g
    simpa using congrArg φ (hx a)
  · intro hy
    refine ⟨φ.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy ⊢
    intro g
    apply φ.injective
    simpa using hy (φ g)

noncomputable def tabMThree_quotCenterEquiv {A B : Type} [Group A] [Group B] (φ : A ≃* B) :
    A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
  QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) φ (tabMThree_map_center φ)

theorem CentThreeA.of_equiv (e : G ≃* G') (h : CentThreeA G') : CentThreeA G := by
  intro k α hk hα2 hαc hα hH
  obtain ⟨f⟩ := hH
  obtain ⟨g⟩ := tabMThree_mulEquiv_inf e α k
  obtain ⟨φ⟩ := tabMThree_mulEquiv_cent e k
  obtain ⟨hq, ⟨f'⟩⟩ := h (e k) (e α) (by rw [MulEquiv.orderOf_eq]; exact hk)
    (by rw [MulEquiv.orderOf_eq]; exact hα2)
    (by rw [natCard_centralizer_mulEquiv]; exact hαc)
    (by simpa using congrArg e hα) ⟨g.symm.trans f⟩
  exact ⟨isQuasisimple_of_mulEquiv' φ.symm hq, ⟨(tabMThree_quotCenterEquiv φ).trans f'⟩⟩

theorem CentThreeC.of_equiv (e : G ≃* G') (h : CentThreeC G') : CentThreeC G := by
  intro k α hk hα2 hαc hα hH
  obtain ⟨f⟩ := hH
  obtain ⟨g⟩ := tabMThree_mulEquiv_inf e α k
  have h1 := h (e k) (e α) (by rw [MulEquiv.orderOf_eq]; exact hk)
    (by rw [MulEquiv.orderOf_eq]; exact hα2)
    (by rw [natCard_centralizer_mulEquiv]; exact hαc)
    (by simpa using congrArg e hα) ⟨g.symm.trans f⟩
  rwa [natCard_centralizer_mulEquiv] at h1

end Transport

section TwoA

theorem invertedByTwoA_data_twoA {G : Type} [Group G] (hE : MonsterExistenceStatement G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : G} (hs : orderOf s = p) (hinv : InvertedByTwoA s) :
    ∃ α : G, orderOf α = 2 ∧
      Nat.card ↥(Subgroup.centralizer ({α} : Set G)) = 2 * monsterBabyOrder ∧
      α * s * α⁻¹ = s⁻¹ ∧ ∃ i : Fin 9, suborbitClassOrder i = p ∧
        TwoPointShape
          (Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({s} : Set G)) i := by
  obtain ⟨-, a, hcls, -, hshape⟩ := twoA_data_of_existence hE
  obtain ⟨α, hα2, hαc, hαs⟩ := hinv
  have hαA : IsConj a α := hcls α hα2 hαc
  have hαα : α * α = 1 := by
    have := pow_orderOf_eq_one α
    rwa [hα2, sq] at this
  have hαi : α⁻¹ = α := inv_eq_of_mul_eq_one_right hαα
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsodd : Odd (orderOf s⁻¹) := by rw [orderOf_inv, hs]; exact hpodd
  have hinv' : α * s⁻¹ * α⁻¹ = (s⁻¹)⁻¹ := by
    have := conj_inv (a := s) (b := α)
    rw [hαs, inv_inv] at this
    rw [inv_inv]
    exact this.symm
  have hβ : IsConj a (s⁻¹ * α) := hαA.trans (isConj_mul_of_inverts_odd hinv' hsodd)
  have hαβ : α * (s⁻¹ * α) = s := by
    calc α * (s⁻¹ * α) = α * s⁻¹ * α⁻¹ := by rw [hαi]; group
      _ = s := by rw [hinv', inv_inv]
  refine ⟨α, hα2, hαc, hαs, ?_⟩
  obtain ⟨i, hi, hsh⟩ := hshape α (s⁻¹ * α) hαA hβ
  rw [hαβ, hs] at hi
  refine ⟨i, hi, ?_⟩
  have := centralizer_inf_centralizer_mul_eq α (s⁻¹ * α)
  rw [hαβ] at this
  rw [← this]
  exact hsh

end TwoA

end CFSG.HardMathSupport.Dickson.I271

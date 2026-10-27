module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAComponentSelf
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma31Proof
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_9_1
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4

open scoped commutatorElement

section Rec

variable {X : Type} [Group X] [Finite X]

theorem glaPComponent_centralizer {p : ℕ} (hp : p.Prime) {K J C : Subgroup X}
    (hK : IsSubnormal K ⊤) (hJ : GLAPComponent p (K ⊓ C) J) : GLAPComponent p C J := by
  have h1 : IsSubnormal (K ⊓ C) C := by
    have := isSubnormal_inf hK C
    rwa [top_inf_eq] at this
  exact glaPComponent_of_isSubnormal' hp h1 hJ

theorem primeCore_eq_bot_of_isSubnormal {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hO : GLAPPrimeCore p Y = ⊥) {L : Subgroup Y} (hsn : IsSubnormal L ⊤) :
    GLAPPrimeCore p ↥L = ⊥ := by
  have h : GLAPPrimeCoreOf p L = ⊥ :=
    le_bot_iff.1 ((glaPPrimeCoreOf_le_of_isSubnormal hp hsn).trans
      (glaPPrimeCoreOf_top_eq_bot_of_eq_bot hO).le)
  unfold GLAPPrimeCoreOf at h
  exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).1 h

theorem recursionData {p : ℕ} (hp : p.Prime) {C J B : Subgroup X} (hJ : GLAPComponent p C J)
    (hBC : B ≤ C) (hBJ : B ≤ Subgroup.normalizer (J : Set X)) (hSC : IsSCp p ⊤ B) :
    GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ ∧
      GLAPComponent p ⊤ (barX p C J) ∧ IsSCp p ⊤ (barX p C B) ∧
      barX p C B ≤ Subgroup.normalizer (barX p C J : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  refine ⟨hcore, ?_, ?_, barX_le_normalizer hBJ⟩
  · exact glaPComponent_of_isSubnormal' hp hJ.2.2.1.2.1
      (CFSG.HardMathSupport.Timmesfeld.Proving.glaPComponent_self hJ.2.2.1.2.2
        (primeCore_eq_bot_of_isSubnormal hp hcore hJ.2.2.1.2.1))
  · have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf_of_le hSC hBC le_top
    exact isSCp_map_quotient (GLAPPrimeCore p ↥C)
      ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hB'

theorem stronglyLocallyOneBalanced_of_bar {p : ℕ} (hp : p.Prime) {a : X} {B J : Subgroup X}
    (hJsn : IsSubnormal J (Subgroup.centralizer ({a} : Set X)))
    (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (h : IsStronglyBalancedIn p (barX p (Subgroup.centralizer ({a} : Set X)) B)
      (barX p (Subgroup.centralizer ({a} : Set X)) J)) :
    IsStronglyLocallyOneBalanced p B a J := by
  intro S hSN hScop hBS
  set C := Subgroup.centralizer ({a} : Set X) with hC
  have hSC : S ≤ C := (le_inf_iff.1 hSN).2
  have hSJ : S ≤ Subgroup.normalizer (J : Set X) := (le_inf_iff.1 hSN).1
  have hJC : J ≤ C := hJsn.le
  have hBS' : B ≤ Subgroup.normalizer (S : Set X) := fun b hb => hBS ⟨hb, hBJ hb⟩
  have hSbarN : barX p C S ≤ Subgroup.normalizer (barX p C J : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    barX_le_normalizer hSJ
  have hSbarc : Nat.Coprime p (Nat.card (barX p C S)) := by
    have h1 : Nat.card (barX p C S) ∣ Nat.card (S.subgroupOf C) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (S.subgroupOf C) = Nat.card S :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSC).toEquiv
    rw [h2] at h1
    exact Nat.Coprime.coprime_dvd_right h1 hScop
  have hBSbar : barX p C B ⊓ Subgroup.normalizer (barX p C J : Set (↥C ⧸ GLAPPrimeCore p ↥C)) ≤
      Subgroup.normalizer (barX p C S : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    inf_le_left.trans (barX_le_normalizer hBS')
  have hcent := h (barX p C S) hSbarN hSbarc hBSbar
  rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJsn]
  refine Subgroup.commutator_le.2 fun j hj s hs => ?_
  refine ⟨?_, ?_⟩
  · have : ⁅j, s⁆ = j * (s * j⁻¹ * s⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [this]
    exact J.mul_mem hj ((Subgroup.mem_normalizer_iff.1 (hSJ hs) j⁻¹).1 (J.inv_mem hj))
  · set jC : ↥C := ⟨j, hJC hj⟩ with hjC
    set sC : ↥C := ⟨s, hSC hs⟩ with hsC
    have hjmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) jC ∈ barX p C J :=
      ⟨jC, Subgroup.mem_subgroupOf.2 hj, rfl⟩
    have hsmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) sC ∈ barX p C S :=
      ⟨sC, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 (hcent hsmem) _ hjmem
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥C) (jC * sC * jC⁻¹ * sC⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    exact ⟨jC * sC * jC⁻¹ * sC⁻¹, h2, rfl⟩

theorem card_bar_lt {C : Subgroup X} (hC : C ≠ ⊤) (N : Subgroup ↥C) [N.Normal] :
    Nat.card (↥C ⧸ N) < Nat.card X := by
  have h1 : Nat.card (↥C ⧸ N) ≤ Nat.card C :=
    Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective N)
  have h2 : Nat.card C ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card C)
  have h3 : Nat.card C ≠ Nat.card X := fun h => hC ((Subgroup.card_eq_iff_eq_top C).1 h)
  omega

theorem centralizer_ne_top_of_not_mem {K : Subgroup X} {a : X}
    (ha : a ∉ Subgroup.centralizer (K : Set X)) :
    Subgroup.centralizer ({a} : Set X) ≠ ⊤ := by
  intro h
  apply ha
  rw [Subgroup.mem_centralizer_iff]
  intro k _
  have : k ∈ Subgroup.centralizer ({a} : Set X) := h ▸ Subgroup.mem_top k
  exact Subgroup.mem_centralizer_singleton_iff.1 this

end Rec

end CFSG.HardMathSupport.Dickson.I271

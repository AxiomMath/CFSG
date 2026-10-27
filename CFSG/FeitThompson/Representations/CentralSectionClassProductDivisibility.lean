module

public import CFSG.FeitThompson.Representations.TINormalCentralSectionGeometry
public import CFSG.FeitThompson.Representations.ClassSumsIntegerStructureConstants
import CFSG.FeitThompson.Foundations.OrbitStabilizerIndex

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open MulAction Subgroup

variable {G : Type*} [Group G]

theorem mem_mapSubgroup_toConjAct {H : Subgroup G} {c : ConjAct G} :
    c ∈ (ConjAct.toConjAct : G ≃* ConjAct G).mapSubgroup H ↔ ConjAct.ofConjAct c ∈ H := by
  simp only [MulEquiv.mapSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk, Subgroup.mem_map]
  exact ⟨fun ⟨x, hx, hxc⟩ => by simpa [← hxc] using hx,
    fun hc => ⟨ConjAct.ofConjAct c, hc, by simp⟩⟩

theorem natCard_dvd_of_stabilizer_eq_bot {Q X : Type*} [Group Q] [MulAction Q X]
    (hst : ∀ b : X, stabilizer Q b = ⊥) : Nat.card Q ∣ Nat.card X := by
  rw [Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hst), Nat.card_prod]
  exact Dvd.intro_left _ rfl

def classesMeeting (s : Set G) : Set (ConjClasses G) := {K | (K.carrier ∩ s).Nonempty}

theorem mem_classesMeeting {s : Set G} {K : ConjClasses G} :
    K ∈ classesMeeting s ↔ ∃ g ∈ s, ConjClasses.mk g = K := by
  simp only [classesMeeting, Set.mem_ofPred_eq, Set.inter_nonempty]
  exact ⟨fun ⟨g, hg1, hg2⟩ => ⟨g, hg2, ConjClasses.mem_carrier_iff_mk_eq.1 hg1⟩,
    fun ⟨g, hg, hgK⟩ => ⟨g, hgK ▸ ConjClasses.mem_carrier_mk, hg⟩⟩

theorem mem_classesMeeting_mk {s : Set G} {g : G} (hg : g ∈ s) :
    ConjClasses.mk g ∈ classesMeeting s := mem_classesMeeting.2 ⟨g, hg, rfl⟩

theorem notMem_classesMeeting_iff {s : Set G} {K : ConjClasses G} :
    K ∉ classesMeeting s ↔ K.carrier ∩ s = ∅ := by
  rw [classesMeeting, Set.mem_ofPred_eq, Set.not_nonempty_iff_eq_empty]

def classProdPairsClass (K L M : ConjClasses G) : SubMulAction (ConjAct G) (G × G) where
  carrier := {q | ConjClasses.mk q.1 = K ∧ ConjClasses.mk q.2 = L ∧ ConjClasses.mk (q.1 * q.2) = M}
  smul_mem' c q hq := by
    obtain ⟨h1, h2, h3⟩ := hq
    refine ⟨?_, ?_, ?_⟩
    · change ConjClasses.mk (ConjAct.ofConjAct c * q.1 * (ConjAct.ofConjAct c)⁻¹) = K
      rw [mk_conj, h1]
    · change ConjClasses.mk (ConjAct.ofConjAct c * q.2 * (ConjAct.ofConjAct c)⁻¹) = L
      rw [mk_conj, h2]
    · change ConjClasses.mk (ConjAct.ofConjAct c * q.1 * (ConjAct.ofConjAct c)⁻¹ *
        (ConjAct.ofConjAct c * q.2 * (ConjAct.ofConjAct c)⁻¹)) = M
      rw [show ConjAct.ofConjAct c * q.1 * (ConjAct.ofConjAct c)⁻¹ *
        (ConjAct.ofConjAct c * q.2 * (ConjAct.ofConjAct c)⁻¹) =
        ConjAct.ofConjAct c * (q.1 * q.2) * (ConjAct.ofConjAct c)⁻¹ by group, mk_conj, h3]

theorem mem_classProdPairsClass {K L M : ConjClasses G} {q : G × G} :
    q ∈ classProdPairsClass K L M ↔
      ConjClasses.mk q.1 = K ∧ ConjClasses.mk q.2 = L ∧ ConjClasses.mk (q.1 * q.2) = M := Iff.rfl

section Fin

variable [Fintype G] [DecidableEq G]

private noncomputable def classProdPairsClassFinset (K L M : ConjClasses G) : Finset (G × G) :=
  M.carrier.toFinset.biUnion fun z => classProdPairs K L z

private theorem coe_classProdPairsClassFinset (K L M : ConjClasses G) :
    (classProdPairsClassFinset K L M : Set (G × G)) =
      (classProdPairsClass K L M : Set (G × G)) := by
  ext q
  simp only [classProdPairsClassFinset, Finset.coe_biUnion, Set.mem_iUnion,
    Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq, SetLike.mem_coe, mem_classProdPairsClass,
    mem_classProdPairs]
  exact ⟨fun ⟨z, hz, h1, h2, h3⟩ => ⟨h1, h2, by rw [h3, hz]⟩,
    fun ⟨h1, h2, h3⟩ => ⟨q.1 * q.2, h3, h1, h2, rfl⟩⟩

private theorem card_classProdPairsClassFinset (K L M : ConjClasses G) :
    (classProdPairsClassFinset K L M).card =
      classStructureConstant K L M * Nat.card M.carrier := by
  rw [classProdPairsClassFinset, Finset.card_biUnion, Finset.sum_congr rfl
    (g := fun _ => classStructureConstant K L M), Finset.sum_const, mul_comm, smul_eq_mul,
    Nat.card_eq_card_toFinset]
  · intro z hz
    rw [Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq] at hz
    rw [← hz, classStructureConstant_eq_card]
  · intro z hz w hw hzw
    simp only [Finset.disjoint_left, mem_classProdPairs]
    rintro q ⟨-, -, h3⟩ ⟨-, -, h4⟩
    exact hzw (h3 ▸ h4)

theorem natCard_classProdPairsClass (K L M : ConjClasses G) :
    Nat.card (classProdPairsClass K L M) =
      classStructureConstant K L M * Nat.card M.carrier := by
  rw [← card_classProdPairsClassFinset]
  have hc : Nat.card ((classProdPairsClassFinset K L M : Set (G × G))) =
      (classProdPairsClassFinset K L M).card := by simp
  rw [← hc, coe_classProdPairsClassFinset]
  rfl

end Fin

namespace IsTINormalCentralSection

variable {p : ℕ} {P : Sylow p G} {L Z : Subgroup G} {h : ℕ}
  (hs : IsTINormalCentralSection p P L Z h) {Ki Kj Kk : ConjClasses G}
include hs

theorem stabilizer_classProdPairsClass_eq_bot [Finite G]
    (hi : Ki ∈ classesMeeting ((Z : Set G) \ {1})) (hj : Kj ∈ classesMeeting ((Z : Set G) \ {1}))
    (hk : Kk ∉ classesMeeting (Z : Set G)) (q : classProdPairsClass Ki Kj Kk) :
    stabilizer ((ConjAct.toConjAct : G ≃* ConjAct G).mapSubgroup (P : Subgroup G)) q = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro c hc
  obtain ⟨hq1, hq2, hq3⟩ := mem_classProdPairsClass.1 q.2
  set x : G := ConjAct.ofConjAct (c : ConjAct G) with hx
  have hxP : x ∈ (P : Subgroup G) := mem_mapSubgroup_toConjAct.1 c.2
  have hcq : (c : ConjAct G) • (q : G × G) = (q : G × G) :=
    congrArg Subtype.val (mem_stabilizer_iff.1 hc)
  have hc1 : x * (q : G × G).1 * x⁻¹ = (q : G × G).1 := congrArg Prod.fst hcq
  have hc2 : x * (q : G × G).2 * x⁻¹ = (q : G × G).2 := congrArg Prod.snd hcq
  by_cases hx1 : x = 1
  · exact Subtype.ext (by simpa [hx, map_eq_one_iff] using hx1)
  · exfalso
    obtain ⟨z, ⟨hz, hz1⟩, hzi⟩ := mem_classesMeeting.1 hi
    obtain ⟨w, ⟨hw, hw1⟩, hwj⟩ := mem_classesMeeting.1 hj
    have hcomm : ∀ y : G, x * y * x⁻¹ = y → x * y = y * x := fun y hy =>
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [hy]
    have h1 : (q : G × G).1 ∈ Z := (hs.mem_Z_of_isConj_of_commute hz (by simpa using hz1)
      (ConjClasses.mk_eq_mk_iff_isConj.1 (hzi.trans hq1.symm)) hxP hx1 (hcomm _ hc1)).1
    have h2 : (q : G × G).2 ∈ Z := (hs.mem_Z_of_isConj_of_commute hw (by simpa using hw1)
      (ConjClasses.mk_eq_mk_iff_isConj.1 (hwj.trans hq2.symm)) hxP hx1 (hcomm _ hc2)).1
    have hmem : (q : G × G).1 * (q : G × G).2 ∈ Kk.carrier ∩ (Z : Set G) :=
      ⟨ConjClasses.mem_carrier_iff_mk_eq.2 hq3, mul_mem h1 h2⟩
    rw [notMem_classesMeeting_iff.1 hk] at hmem
    exact hmem

theorem natCard_orbit_classProdPairsClass [Finite G]
    (hi : Ki ∈ classesMeeting ((Z : Set G) \ {1})) (hj : Kj ∈ classesMeeting ((Z : Set G) \ {1}))
    (hk : Kk ∉ classesMeeting (Z : Set G)) (q : classProdPairsClass Ki Kj Kk) :
    Nat.card (orbit ((ConjAct.toConjAct : G ≃* ConjAct G).mapSubgroup (P : Subgroup G)) q) =
      Nat.card (P : Subgroup G) := by
  have hst := hs.stabilizer_classProdPairsClass_eq_bot hi hj hk q
  have hkey := natCard_orbit_mul_natCard_stabilizer
    (G := (ConjAct.toConjAct : G ≃* ConjAct G).mapSubgroup (P : Subgroup G)) q
  rw [hst, Subgroup.card_bot, mul_one] at hkey
  rw [hkey, Subgroup.card_mapSubgroup]

theorem natCard_sylow_dvd_classStructureConstant_mul [Fintype G] [DecidableEq G]
    (hi : Ki ∈ classesMeeting ((Z : Set G) \ {1})) (hj : Kj ∈ classesMeeting ((Z : Set G) \ {1}))
    (hk : Kk ∉ classesMeeting (Z : Set G)) :
    Nat.card (P : Subgroup G) ∣ classStructureConstant Ki Kj Kk * Nat.card Kk.carrier := by
  rw [← natCard_classProdPairsClass,
    ← Subgroup.card_mapSubgroup (P : Subgroup G) (ConjAct.toConjAct : G ≃* ConjAct G)]
  exact natCard_dvd_of_stabilizer_eq_bot (hs.stabilizer_classProdPairsClass_eq_bot hi hj hk)

theorem intCast_natCard_sylow_dvd [Fintype G] [DecidableEq G]
    (hi : Ki ∈ classesMeeting ((Z : Set G) \ {1})) (hj : Kj ∈ classesMeeting ((Z : Set G) \ {1}))
    (hk : Kk ∉ classesMeeting (Z : Set G)) :
    (Nat.card (P : Subgroup G) : ℤ) ∣
      (classStructureConstant Ki Kj Kk : ℤ) * (Nat.card Kk.carrier : ℤ) := by
  exact_mod_cast Int.natCast_dvd_natCast.2
    (hs.natCard_sylow_dvd_classStructureConstant_mul hi hj hk)

end IsTINormalCentralSection

end CFSG.FeitThompson

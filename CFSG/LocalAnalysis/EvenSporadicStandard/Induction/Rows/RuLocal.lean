module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.PairShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.EmbedLam
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsRu
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSQuasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOne

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.RuStd
open scoped commutatorElement

@[expose] def RuPair : PairClass := PairShape (fun n => n = 29120)

structure RuLocalFacts : Prop where
  exists_pair : ∀ (G : Type) [Group G] (L : Subgroup G), IsSporadic ↥L .Ru →
    ∃ (K : Subgroup G) (u : G), RuPair G L K u
  simple : ∀ (G : Type) [Group G] (L K : Subgroup G) (u : G), IsSporadic ↥L .Ru →
    RuPair G L K u → IsSimpleGroup ↥K
  normal : ∀ (G : Type) [Group G] (L K : Subgroup G) (u : G), IsSporadic ↥L .Ru →
    RuPair G L K u → (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).Normal
  card_centralizer : ∀ (G : Type) [Group G] (L K : Subgroup G) (u : G), IsSporadic ↥L .Ru →
    RuPair G L K u → Nat.card ↥(L ⊓ centralizer (K : Set G)) = 4

theorem le_commutator_of_isPerfect {X : Type*} [Group X] {P : Subgroup X}
    (hp : _root_.commutator ↥P = ⊤) : P ≤ _root_.commutator X := by
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥P) ∈ _root_.commutator ↥P := by
    rw [hp]
    exact mem_top _
  have h1 := Subgroup.mem_map_of_mem P.subtype hx'
  rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h1
  rw [_root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top h1

theorem le_commutator_of_perfect_of_le {X : Type*} [Group X] {P C : Subgroup X}
    (hp : _root_.commutator ↥P = ⊤) (hPC : P ≤ C) : P ≤ ⁅C, C⁆ := by
  have h1 : ⁅P, P⁆ = P := by
    have h := congrArg (Subgroup.map P.subtype) hp
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  rw [← h1]
  exact Subgroup.commutator_mono hPC hPC

theorem eq_commutator_of_perfect_of_index_le_four {X : Type} [Group X] [Finite X]
    {E : Subgroup X} (hn : E.Normal) (hp : _root_.commutator ↥E = ⊤) (hi : E.index ≤ 4) :
    E = _root_.commutator X := by
  apply le_antisymm (le_commutator_of_isPerfect hp)
  have hc : IsMulCommutative (X ⧸ E) :=
    isMulCommutative_of_card_le_four (by rw [← Subgroup.index_eq_card]; exact hi)
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro a _ b _
  have hmk : (QuotientGroup.mk' E) ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (hc.is_comm.comm _ _)
  exact (QuotientGroup.eq_one_iff _).1 hmk

theorem card_centralizer_subgroupOf {G : Type} [Group G] {L K : Subgroup G} (hKL : K ≤ L) :
    Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) =
      Nat.card ↥(L ⊓ centralizer (K : Set G)) := by
  have h : (centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)).map L.subtype =
      L ⊓ centralizer (K : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.coe_subtype, mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun k hk => ?_⟩
      have := hy ⟨k, hKL hk⟩ (by simpa [mem_subgroupOf] using hk)
      exact congrArg Subtype.val this
    · rintro ⟨hxL, hx⟩
      refine ⟨⟨x, hxL⟩, fun k hk => ?_, rfl⟩
      exact Subtype.ext (hx k (mem_subgroupOf.1 hk))
  rw [← h, Subgroup.card_map_of_injective L.subtype_injective]

theorem not_comm_of_simple_not_prime {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  exact h (IsSimpleGroup.prime_card (α := X))

theorem factorization_two_29120 : (29120 : ℕ).factorization 2 = 6 := by
  have h : (29120 : ℕ) = 2 ^ 6 * 455 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

theorem factorization_two_four : (4 : ℕ).factorization 2 = 2 := by
  have h : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem ruPair_not_mem (hf : RuLocalFacts) {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    {u : G} (hL : IsSporadic ↥L .Ru) (hQ : RuPair G L K u) : u ∉ K := by
  intro huK
  have hs := hf.simple G L K u hL hQ
  have hna : ∃ a b : ↥K, a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hQ.2.2.2.2]; norm_num)
  have hz : (⟨u, huK⟩ : ↥K) ∈ center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (hQ.2.2.2.1 k k.2)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥K) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    have h1 : u = 1 := congrArg Subtype.val hz
    have := hQ.2.1
    rw [h1, orderOf_one] at this
    omega
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ center ↥K := h ▸ mem_top a
    exact hab (Subgroup.mem_center_iff.1 ha b).symm

section Derived

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {u : G}

theorem card_centralizer_of_ruPair (hL : IsSporadic ↥L .Ru) (hQ : RuPair G L K u) :
    Nat.card ↥(L ⊓ centralizer ({u} : Set G)) = 116480 := by
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  have hF := ruFacts_of_isSporadic hL
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have h1 := hF.card_centralizer ⟨u, huL⟩ hu'
  rw [card_centralizer_subtype L ⟨u, huL⟩] at h1
  have hKle : K ≤ L ⊓ centralizer ({u} : Set G) := fun k hk =>
    ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have h3 : Nat.card K ∣ Nat.card ↥(L ⊓ centralizer ({u} : Set G)) :=
    Subgroup.card_dvd_of_le hKle
  rw [hcard] at h3
  rcases h1 with h | h
  · exact absurd (h ▸ h3) (by norm_num)
  · exact h

theorem ruPair_eq_commutator (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair G L K u) :
    K.subgroupOf (L ⊓ centralizer ({u} : Set G)) =
      _root_.commutator ↥(L ⊓ centralizer ({u} : Set G)) := by
  have hQ' := hQ
  obtain ⟨huL, hu2, hKL, hKu, hcard⟩ := hQ
  set C : Subgroup G := L ⊓ centralizer ({u} : Set G) with hC
  have hKle : K ≤ C := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  have hn := hf.normal G L K u hL hQ'
  have hs := hf.simple G L K u hL hQ'
  let e : ↥(K.subgroupOf C) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKle
  have hsE : IsSimpleGroup ↥(K.subgroupOf C) := (MulEquiv.isSimpleGroup_congr e).2 hs
  have hcardE : Nat.card ↥(K.subgroupOf C) = 29120 := (Nat.card_congr e.toEquiv).trans hcard
  have hnaE : ∃ a b : ↥(K.subgroupOf C), a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hcardE]; norm_num)
  have hperf : _root_.commutator ↥(K.subgroupOf C) = ⊤ :=
    (isQuasisimple_of_simple hsE hnaE).1
  have hC116 : Nat.card ↥C = 116480 := card_centralizer_of_ruPair hL hQ'
  have hidx : (K.subgroupOf C).index ≤ 4 := by
    have h := Subgroup.card_mul_index (K.subgroupOf C)
    rw [hcardE, hC116] at h
    omega
  exact eq_commutator_of_perfect_of_index_le_four hn hperf hidx

theorem ruPair_eq_derived (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair G L K u) :
    K = ⁅L ⊓ centralizer ({u} : Set G), L ⊓ centralizer ({u} : Set G)⁆ := by
  have hKle : K ≤ L ⊓ centralizer ({u} : Set G) := fun k hk =>
    ⟨hQ.2.2.1 hk, mem_centralizer_singleton_iff.2 (hQ.2.2.2.1 k hk)⟩
  have h := ruPair_eq_commutator hf hL hQ
  have h2 := congrArg (Subgroup.map (L ⊓ centralizer ({u} : Set G)).subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hKle, _root_.commutator_def, Subgroup.map_commutator,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2

theorem ruPair_isQuasisimple (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair G L K u) : CFSG.IsQuasisimple ↥K := by
  have hs := hf.simple G L K u hL hQ
  have hna : ∃ a b : ↥K, a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hQ.2.2.2.2]; norm_num)
  exact (CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.2 (isQuasisimple_of_simple hs hna)

theorem ruPair_characteristic (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair G L K u) : (K.subgroupOf (L ⊓ centralizer ({u} : Set G))).Characteristic := by
  rw [ruPair_eq_commutator hf hL hQ]
  infer_instance

end Derived

section Standard

variable {Λ : Type} [Group Λ] [Finite Λ]

theorem ruPair_solStd (hf : RuLocalFacts) (hΛ : IsSporadic ↥(⊤ : Subgroup Λ) .Ru)
    {K : Subgroup Λ} {u : Λ} (hQ : RuPair Λ ⊤ K u) : SolStd K := by
  have hQ' := hQ
  obtain ⟨-, hu2, -, hKu, hcard⟩ := hQ
  have hs := hf.simple Λ ⊤ K u hΛ hQ'
  have hna : ∃ a b : ↥K, a * b ≠ b * a :=
    not_comm_of_simple_not_prime (by rw [hcard]; norm_num)
  have hKq : CFSG.Open.IsQuasisimple ↥K := isQuasisimple_of_simple hs hna
  have huC : u ∈ centralizer (K : Set Λ) := mem_centralizer_iff.2 hKu
  have hc4 : Nat.card ↥(centralizer (K : Set Λ)) = 4 := by
    have h := hf.card_centralizer Λ ⊤ K u hΛ hQ'
    rwa [top_inf_eq] at h
  have hcent : twoAdic (centralizer (K : Set Λ)) < twoAdic K := by
    unfold twoAdic
    rw [hc4, hcard, factorization_two_four, factorization_two_29120]
    norm_num
  have huniq : ∀ t : Λ, orderOf t = 2 → t ∈ centralizer (K : Set Λ) →
      ∀ K' : Subgroup Λ, K' ≤ centralizer ({t} : Set Λ) → Group.IsPerfect K' →
        Nat.card K' = Nat.card K → K' = K := by
    intro t ht2 htC K' hK' hperf hc
    have hQt : RuPair Λ ⊤ K t :=
      ⟨mem_top _, ht2, le_top, fun k hk => mem_centralizer_iff.1 htC k hk, hcard⟩
    have hder := ruPair_eq_derived hf hΛ hQt
    have hK'le : K' ≤ ⊤ ⊓ centralizer ({t} : Set Λ) := fun x hx => ⟨mem_top _, hK' hx⟩
    have hle : K' ≤ K := by
      rw [hder]
      exact le_commutator_of_perfect_of_le (Group.isPerfect_def.1 hperf) hK'le
    exact Subgroup.eq_of_le_of_card_ge hle hc.ge
  exact solStd_of_standardComponentIsStandard (standard_of_unique hKq hu2 huC huniq hcent)

end Standard

section LocalQ

variable {H : Type} [Group H] [Finite H] {L K : Subgroup H} {u : H}

theorem ruPair_twoAdic_aut (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    twoAdic (autCentralizer L K) ≤ 2 := by
  have hinn := CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic hL
  have h1 := twoAdic_autCentralizer_le_of_allInner (L := L) (K := K) (fun α => by
    obtain ⟨g, hg⟩ := hinn α
    exact ⟨g, fun x => by rw [hg]; rfl⟩)
  refine h1.trans ?_
  unfold twoAdic
  rw [card_centralizer_subgroupOf hQ.2.2.1, hf.card_centralizer H L K u hL hQ,
    factorization_two_four]

theorem solomonLocalQ_ru (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair H L K u) : SolomonLocalQ L K u where
  u_order := hQ.2.1
  u_mem := Subgroup.le_normalizer hQ.1
  u_not_central := by
    intro hc
    have hZ : center ↥L = ⊥ := center_eq_bot_of_isSporadic_ru hL
    have hz : (⟨u, hQ.1⟩ : ↥L) ∈ center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hc g g.2)
    rw [hZ, Subgroup.mem_bot] at hz
    have h1 : u = 1 := congrArg Subtype.val hz
    have := hQ.2.1
    rw [h1, orderOf_one] at this
    omega
  K_le := hQ.2.2.1
  u_mem_centralizer_K := mem_centralizer_iff.2 hQ.2.2.2.1
  standard_in_L := by
    obtain ⟨e⟩ := hL
    exact ruPair_solStd hf ⟨Subgroup.topEquiv.trans e⟩ (pairShape_restrict hQ)
  autCentralizer_two := ruPair_twoAdic_aut hf hL hQ

theorem card_autCentralizer_ru_le (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru)
    (hQ : RuPair H L K u) : Nat.card ↥(autCentralizer L K) ≤ 4 := by
  have hinn := CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic hL
  have hle := autCentralizer_le_map_centralizer (L := L) (K := K) (fun α => by
    obtain ⟨g, hg⟩ := hinn α
    exact ⟨g, fun x => by rw [hg]; rfl⟩)
  have hc4 : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 4 := by
    rw [card_centralizer_subgroupOf hQ.2.2.1]
    exact hf.card_centralizer H L K u hL hQ
  exact (Subgroup.card_le_of_le hle).trans
    ((Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)).trans hc4.le)

theorem ruAut_solvable (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    Group.IsSolvable ↥(autCentralizer L K) := by
  have : IsMulCommutative ↥(autCentralizer L K) :=
    isMulCommutative_of_card_le_four (card_autCentralizer_ru_le hf hL hQ)
  infer_instance

theorem ruAut_elemBound (hf : RuLocalFacts) (hL : IsSporadic ↥L .Ru) (hQ : RuPair H L K u) :
    ElemBound 4 ↥(autCentralizer L K) := fun E _ _ =>
  (Subgroup.card_le_card_group E).trans (card_autCentralizer_ru_le hf hL hQ)

theorem ruAut_inner (hL : IsSporadic ↥L .Ru) :
    ∀ α ∈ autCentralizer L K, ∃ g : ↥L, α = MulAut.conj g := fun α _ =>
  CFSG.EvenSporadicStandard.TwoRu.HypOne.allInner_of_isSporadic hL α

end LocalQ

end CFSG.EvenSporadicStandard.Induction

module

public import CFSG.ClassicalInvolution.SmallCases.NDBG8
public import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.Asc77.AscL62Main
public import CFSG.ClassicalInvolution.Asc77.WP3LayerConj
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic
public import CFSG.Assembly.BalancedOddCoreCompletion
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.Dichotomy (involutionOddCore odd_card_involutionOddCore)

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def LitO2 (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (z : G) : Prop :=
  ∀ M ∈ tqMembers Ω z, ∀ m : G, IsClassicalMember p f M m →
    ∀ o ∈ involutionOddCore z, o * m = m * o

@[expose] def PairProd (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∀ N₁ ∈ tqMembers Ω x, ∀ N₂ ∈ tqMembers Ω x, ∀ n₁ n₂ : G, IsClassicalMember p f N₁ n₁ →
    IsClassicalMember p f N₂ n₂ → n₁ ≠ x → n₂ ≠ x → n₁ ≠ n₂ → n₁ * n₂ = x

omit [Finite G] in
theorem mul_comm_of_mem_centralizer {z x : G} (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    x * z = z * x :=
  Subgroup.mem_centralizer_singleton_iff.mp hx

omit [Finite G] in
theorem mul_comm_of_mem_involutionOddCore {z o : G} (ho : o ∈ involutionOddCore z) :
    o * z = z * o := by
  obtain ⟨o', -, rfl⟩ := ho
  exact mul_comm_of_mem_centralizer o'.2

theorem eq_of_oddQuotMk_eq {z a b : G} (ha : a ∈ Subgroup.centralizer ({z} : Set G))
    (hb : b ∈ Subgroup.centralizer ({z} : Set G)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hab : oddQuotMk z ⟨a, ha⟩ = oddQuotMk z ⟨b, hb⟩)
    (hc : ∀ o ∈ involutionOddCore z, o * b = b * o) : a = b := by
  have hab' : a * b ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.mul_mem _ ha hb
  have hmem : a * b ∈ involutionOddCore z := by
    refine Asc77.Lemma52Proof.mem_involutionOddCore_of_oddQuotMk_eq_one hab' ?_
    have e : (⟨a * b, hab'⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    have e2 : (⟨b, hb⟩ * ⟨b, hb⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext hb2
    rw [e, map_mul, hab, ← map_mul, e2, map_one]
  obtain ⟨o, ho, hao⟩ := DeltaClosure.exists_conj_of_mul_mem hb2 ha2
    (odd_card_involutionOddCore z) hmem
  rw [hao, hc o ho, mul_assoc, mul_inv_cancel, mul_one]

theorem mul_eq_of_litO2 {z : G} (C : Asc77.XCtx p f Ω z)
    (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f Ω A)
    (hall : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2) (hL : LitO2 p f Ω z) :
    PairProd p f Ω z := by
  intro N₁ h₁ N₂ h₂ n₁ n₂ hn₁ hn₂ hz₁ hz₂ hne
  have hc₁ := C.involution_mem_centralizer h₁ hn₁
  have hc₂ := C.involution_mem_centralizer h₂ hn₂
  have hs₁ : n₁ * n₁ = 1 := hn₁.isCentralInvolution.sq
  have hs₂ : n₂ * n₂ = 1 := hn₂.isCentralInvolution.sq
  have hz2 : z * z = 1 := C.hKz.sq
  rcases NDBG.nbar_eq_or_mul_eq C hnoF hall h₁ h₂ hn₁ hn₂ hz₁ hz₂ with h | h
  · exact absurd (eq_of_oddQuotMk_eq hc₁ hc₂ hs₁ hs₂ h (hL N₂ h₂ n₂ hn₂)) hne
  have hzn : z * n₂ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mul_mem _ (Asc77.XCtx.hzC z) hc₂
  have hcomm : n₂ * z = z * n₂ := mul_comm_of_mem_centralizer hc₂
  have hs : z * n₂ * (z * n₂) = 1 := by
    calc z * n₂ * (z * n₂) = z * (n₂ * z) * n₂ := by group
      _ = z * z * (n₂ * n₂) := by rw [hcomm]; group
      _ = 1 := by rw [hz2, hs₂, one_mul]
  have heq : oddQuotMk z ⟨n₁, hc₁⟩ = oddQuotMk z ⟨z * n₂, hzn⟩ := by
    have e : (⟨z * n₂, hzn⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨z, Asc77.XCtx.hzC z⟩ * ⟨n₂, hc₂⟩ := rfl
    have e2 : (⟨n₂, hc₂⟩ * ⟨n₂, hc₂⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
      Subtype.ext hs₂
    rw [e, map_mul, ← h, mul_assoc, ← map_mul, e2, map_one, mul_one]
  have hcz : ∀ o ∈ involutionOddCore z, o * (z * n₂) = z * n₂ * o := by
    intro o ho
    rw [← mul_assoc, mul_comm_of_mem_involutionOddCore ho, mul_assoc,
      hL N₂ h₂ n₂ hn₂ o ho, mul_assoc]
  rw [eq_of_oddQuotMk_eq hc₁ hzn hs₁ hs heq hcz, mul_assoc, hs₂, mul_one]

theorem pairProd_conj (hΩ : ConjInvariant Ω) {x : G} (h : PairProd p f Ω x) (g : G) :
    PairProd p f Ω (g * x * g⁻¹) := by
  intro N₁ h₁ N₂ h₂ n₁ n₂ hn₁ hn₂ hx₁ hx₂ hne
  rw [tqMembers_conj hΩ g x] at h₁ h₂
  obtain ⟨M₁, hM₁, rfl⟩ := h₁
  obtain ⟨M₂, hM₂, rfl⟩ := h₂
  have hm₁ := hn₁.conj g⁻¹
  have hm₂ := hn₂.conj g⁻¹
  rw [conjSub_inv_conjSub] at hm₁ hm₂
  have key := h M₁ hM₁ M₂ hM₂ _ _ hm₁ hm₂ (fun e => hx₁ (by rw [← e]; group))
    (fun e => hx₂ (by rw [← e]; group)) (fun e => hne (by
      calc n₁ = g * (g⁻¹ * n₁ * g⁻¹⁻¹) * g⁻¹ := by group
        _ = g * (g⁻¹ * n₂ * g⁻¹⁻¹) * g⁻¹ := by rw [e]
        _ = n₂ := by group))
  calc n₁ * n₂ = g * ((g⁻¹ * n₁ * g⁻¹⁻¹) * (g⁻¹ * n₂ * g⁻¹⁻¹)) * g⁻¹ := by group
    _ = g * x * g⁻¹ := by rw [key]

theorem mem_tqMembers_of_dAdj (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : Asc77.HypOmegaMod p f Ω)
    {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) (hadj : Disconnected.dAdj Ω L L') {x : G}
    (hx : IsClassicalMember p f L x) : L' ∈ tqMembers Ω x := by
  have hN : L' ∈ Asc77.omegaNbr Ω L := by
    rcases hadj with h | h
    · exact h
    · exact Asc77.T3.omegaNbr_symm (Asc77.l6_2 p f) hp2 hq hΩ hL' hL h
  obtain ⟨a, ha, htq⟩ := Disconnected.tq_of_mem_omegaNbr hp2 hq hΩ.classical hL hN
  have hax : a = x := (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hx)
  subst hax
  exact ⟨hL', mem_trivialOnQuot_iff_actsTrivOnQuot.mpr htq⟩

theorem false_of_litO2 [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hconn : Disconnected.DConnected (𝒞 K))
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) (hL : LitO2 p f (𝒞 K) z) : False := by
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D
  have hΩ : Asc77.HypOmegaMod p f (𝒞 K) := C.hΩ
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  have huniq : ∀ {L : Subgroup G} {x y : G}, IsClassicalMember p f L x →
      IsClassicalMember p f L y → x = y := fun hx hy =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hx).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hy)
  have hP : PairProd p f (𝒞 K) z := mul_eq_of_litO2 C hno hall' hL
  have hPall : ∀ {L : Subgroup G} {x : G}, L ∈ 𝒞 K → IsClassicalMember p f L x →
      PairProd p f (𝒞 K) x := by
    rintro L x ⟨g, rfl⟩ hx
    rw [← huniq (hz.conj g) hx]
    exact pairProd_conj hΩ.conjInvariant hP g
  obtain ⟨w, hwC, hwm⟩ : ∃ w : G, w ∈ Subgroup.centralizer ({z} : Set G) ∧
      ∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m = z ∨ m = w ∨
        m = z * w := by
    by_cases hex : ∃ N ∈ tqMembers (𝒞 K) z, ∃ n : G, IsClassicalMember p f N n ∧ n ≠ z
    · obtain ⟨N, hN, w, hw, hwz⟩ := hex
      refine ⟨w, C.involution_mem_centralizer hN hw, fun M hM m hm => ?_⟩
      by_cases hmz : m = z
      · exact Or.inl hmz
      by_cases hmw : m = w
      · exact Or.inr (Or.inl hmw)
      have e := hP M hM N hN m w hm hw hmz hwz hmw
      have hw2 : w * w = 1 := hw.isCentralInvolution.sq
      refine Or.inr (Or.inr ?_)
      calc m = m * w * w := by rw [mul_assoc, hw2, mul_one]
        _ = z * w := by rw [e]
    · push Not at hex
      exact ⟨z, Asc77.XCtx.hzC z, fun M hM m hm => Or.inl (hex M hM m hm)⟩
  set E : Subgroup G := Subgroup.closure ({z, w} : Set G) with hE
  have hzE : z ∈ E := Subgroup.subset_closure (Set.mem_insert z _)
  have hwE : w ∈ E := Subgroup.subset_closure (Set.mem_insert_of_mem z rfl)
  let Inv : Subgroup G → Prop := fun L => L ∈ 𝒞 K ∧ ∀ x : G, IsClassicalMember p f L x →
    x ∈ E ∧ ∀ M ∈ tqMembers (𝒞 K) x, ∀ m : G, IsClassicalMember p f M m → m ∈ E
  have hbase : Inv K := by
    refine ⟨mem_conjClass_self K, fun x hx => ?_⟩
    rw [← huniq hz hx]
    refine ⟨hzE, fun M hM m hm => ?_⟩
    rcases hwm M hM m hm with rfl | rfl | rfl
    · exact hzE
    · exact hwE
    · exact E.mul_mem hzE hwE
  have hstep : ∀ L L' : Subgroup G, Inv L → L' ∈ 𝒞 K → Disconnected.dAdj (𝒞 K) L L' →
      Inv L' := by
    intro L L' ⟨hL, hI⟩ hL' hadj
    obtain ⟨x, hx⟩ := hΩ.classical L hL
    refine ⟨hL', fun x' hx' => ?_⟩
    have hx'E : x' ∈ E := (hI x hx).2 L' (mem_tqMembers_of_dAdj hp2 hq hΩ hL hL' hadj hx) x' hx'
    refine ⟨hx'E, fun M hM m hm => ?_⟩
    have hLx' : L ∈ tqMembers (𝒞 K) x' :=
      mem_tqMembers_of_dAdj hp2 hq hΩ hL' hL (Disconnected.dAdj_symm hadj) hx'
    by_cases hm1 : m = x'
    · rw [hm1]
      exact hx'E
    by_cases hm2 : m = x
    · rw [hm2]
      exact (hI x hx).1
    by_cases hxx : x = x'
    · rw [← hxx] at hM
      exact (hI x hx).2 M hM m hm
    have e := hPall hL' hx' M hM L hLx' m x hm hx hm1 hxx hm2
    have hmx : m = x' * x⁻¹ := by
      calc m = m * x * x⁻¹ := by group
        _ = x' * x⁻¹ := by rw [e]
    rw [hmx]
    exact E.mul_mem hx'E (E.inv_mem (hI x hx).1)
  have hreach : ∀ J : Subgroup G, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ 𝒞 K ∧ Disconnected.dAdj (𝒞 K) M N) K J → Inv J := by
    intro J hJ
    induction hJ with
    | refl => exact hbase
    | tail _ hbc ih => exact hstep _ _ ih hbc.1 hbc.2
  have hconjE : ∀ g : G, g * z * g⁻¹ ∈ E := fun g =>
    ((hreach _ (hconn K (mem_conjClass_self K) _ ⟨g, rfl⟩)).2 _ (hz.conj g)).1
  have hNC : Subgroup.normalClosure ({z} : Set G) ≤ E := by
    refine (Subgroup.closure_le E).mpr ?_
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hay
    exact hconjE c
  have hcomm : ({z, w} : Set G).Pairwise Commute := by
    have hwz : Commute z w := (mul_comm_of_mem_centralizer hwC).symm
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Commute.refl _, hwz, hwz.symm, Commute.refl _]
  have hEc := Subgroup.isMulCommutative_closure hcomm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({z} : Set G)) with h | h
  · have hz1 : z ∈ Subgroup.normalClosure ({z} : Set G) :=
      Subgroup.subset_normalClosure (Set.mem_singleton z)
    rw [h, Subgroup.mem_bot] at hz1
    exact hz.isCentralInvolution.ne_one hz1
  · obtain ⟨x, y, hxy⟩ := hnab
    have hx : x ∈ E := hNC (by rw [h]; exact Subgroup.mem_top x)
    have hy : y ∈ E := hNC (by rw [h]; exact Subgroup.mem_top y)
    exact hxy (congrArg Subtype.val (isMulCommutative_iff.mp hEc ⟨x, hx⟩ ⟨y, hy⟩))

end NDBH

end CFSG.ClassicalInvolution.NDB

module

public import CFSG.ClassicalInvolution.SmallCases.NDBH3T5
import CFSG.ClassicalInvolution.SmallCases.NDBH1
import CFSG.ClassicalInvolution.SmallCases.NDBC1
import CFSG.ClassicalInvolution.Q3.StrongBalance
import CFSG.ClassicalInvolution.Asc77.WP3FrameStar
import CFSG.ClassicalInvolution.Balance.BootstrapAlphaDelta
import CFSG.ClassicalInvolution.Balance.PassTwo
import CFSG.ClassicalInvolution.Generic.StepQuasisimple
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
public import Certificates.Certificate3951
public import Certificates.Certificate3952
import CFSG.ClassicalInvolution.Q3.OddCoreCentral

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.ClassicalInvolution.RouteD (le_centralizer_of_isClassicalMember)

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime]

namespace NDBH3

variable {G : Type} [Group G] [Finite G]


theorem false_of_twin [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (hconn : DConnected (𝒞 K))
    (hno : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z)
    {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) (hT : HasTwin p f K z) : False := by
  set C := Cover.toXCtx hnab hp2 hq hz hBelow D with hCdef
  have hΩ : HypOmegaMod p f (𝒞 K) := C.hΩ
  have hall' : ∀ i, C.D.tag i = .PSL ∧ C.D.rank i = 2 := hall
  have hKz : IsUniqueInvolution K z := C.hKz
  have hz1 : z ≠ 1 := hKz.ne_one
  obtain ⟨T, hTΩ, hTK, hTz⟩ : ∃ T ∈ 𝒞 K, T ≠ K ∧ IsClassicalMember p f T z := hT
  obtain ⟨R, R', u, x, y, F⟩ := exists_twinA1Frame hp2 hq hΩ hz hTΩ hTK hTz hN hn hnz
  have hbal := F.rankThreeBalance hp2 hq hΩ hz hBelow D hall hN hn hnz
  set B := Subgroup.closure ({z, u, n} : Set G) with hB
  have hzB : z ∈ B := Subgroup.subset_closure (by simp)
  have huB : u ∈ B := Subgroup.subset_closure (by simp)
  have hnB : n ∈ B := Subgroup.subset_closure (by simp)
  have hnzB : n * z ∈ B := mul_mem hnB hzB
  have hnC : n ∈ Subgroup.centralizer ({z} : Set G) := C.involution_mem_centralizer hN hn
  have hnzc : n * z = z * n := Subgroup.mem_centralizer_singleton_iff.mp hnC
  have hn2 : n * n = 1 := hn.isCentralInvolution.sq
  have hz2 : z * z = 1 := hKz.sq
  have hnUn : IsUniqueInvolution N n :=
    ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hn
  have huniq : ∀ {L : Subgroup G} {a b : G}, IsClassicalMember p f L a →
      IsClassicalMember p f L b → a = b := fun ha hb =>
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq ha).eq
      (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hb)
  set S : Set (Subgroup G) :=
    insert K (insert N {M | M ∈ 𝒞 K ∧ IsClassicalMember p f M (n * z)}) with hS
  have hSall : ∀ w : G, (w = z ∨ w = n ∨ w = n * z) → w ∈ B ∧
      ∀ M ∈ 𝒞 K, IsClassicalMember p f M w → ∃ M' ∈ S, IsClassicalMember p f M' w := by
    rintro w (rfl | rfl | rfl)
    · exact ⟨hzB, fun _ _ _ => ⟨K, Set.mem_insert _ _, hz⟩⟩
    · exact ⟨hnB, fun _ _ _ => ⟨N, Set.mem_insert_of_mem _ (Set.mem_insert _ _), hn⟩⟩
    · exact ⟨hnzB, fun M hM hMw =>
        ⟨M, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨hM, hMw⟩), hMw⟩⟩
  have hc2 : ∀ {c : G}, c ∈ B → IsPGroup 2 (Subgroup.zpowers c) := fun hc =>
    isPGroup_zpowers_of_sq_eq_one (Lemma52Proof.mul_self_eq_one_of_mem hbal.elem hc)
  have hnK : n ∈ trivialOnQuot K := F.data.tq_t_K hp2 hq hΩ
  have hnT : n ∈ trivialOnQuot T := F.data.tq_t_K' hp2 hq hΩ
  have hzK : z ∈ trivialOnQuot K := trivialOnQuot_of_isUniqueInvolution hp2 hq hΩ C.hK hKz
  have hzT : z ∈ trivialOnQuot T := trivialOnQuot_of_isUniqueInvolution hp2 hq hΩ hTΩ
    (ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hTz)
  have hnN : n ∈ trivialOnQuot N := trivialOnQuot_of_isUniqueInvolution hp2 hq hΩ hN.1 hnUn
  have hcnz : ∀ r : G, r * n = n * r → r * z = z * r → r * (n * z) = n * z * r := by
    intro r h1 h2
    calc r * (n * z) = (r * n) * z := by group
      _ = (n * r) * z := by rw [h1]
      _ = n * (r * z) := by group
      _ = n * (z * r) := by rw [h2]
      _ = n * z * r := by group
  have hRz : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember hz
      (F.syl.1 hr))
  have hR'z : ∀ r ∈ R', r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mp (le_centralizer_of_isClassicalMember hTz
      (F.syl'.1 hr))
  have hnt := F.data.t_not_mem_closure hp2 hq hΩ
  have hzcl : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hucl : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
  have hvert : ∀ c : G, (c = n ∨ c = n * z) →
      c ∈ B ∧ c ≠ z ∧ u ≠ c ∧ c ∈ trivialOnQuot K ∧ c ∈ trivialOnQuot T ∧
        c ∈ trivialOnQuot N ∧ (∀ r ∈ R, r * c = c * r) ∧ (∀ r ∈ R', r * c = c * r) := by
    rintro c (hc | hc) <;> subst hc
    · refine ⟨hnB, hnz, fun h => hnt (h ▸ hucl), hnK, hnT, hnN, F.cen, F.cen'⟩
    · refine ⟨hnzB, fun h => hn.isCentralInvolution.ne_one (by
        calc n = n * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = 1 := by rw [h, hz2]), fun h => hnt (by
        have : n = u * z := by rw [h, mul_assoc, hz2, mul_one]
        rw [this]
        exact mul_mem hucl hzcl), mul_mem hnK hzK, mul_mem hnT hzT, mul_mem hnN hN.2,
        fun r hr => hcnz r (F.cen r hr) (hRz r hr), fun r hr => hcnz r (F.cen' r hr) (hR'z r hr)⟩
  have hconjg : ∀ {c : G} {L : Subgroup G}, L ∈ 𝒞 K → IsClassicalMember p f L c →
      ∃ g : G, g * z * g⁻¹ = c := by
    rintro c L ⟨g, rfl⟩ hL
    exact ⟨g, huniq (hz.conj g) hL⟩
  have hgenv : ∀ c : G, (c = n ∨ c = n * z) → ∀ {L : Subgroup G}, L ∈ 𝒞 K →
      IsClassicalMember p f L c → CentralizerGenerationStar (𝒞 K) B c := by
    intro c hcs L hL hLc
    obtain ⟨hcB, hcz, huc, hcK, hcT, hcN, hRc, hR'c⟩ := hvert c hcs
    obtain ⟨g, hgz⟩ := hconjg hL hLc
    have hc2' : IsPGroup 2 (Subgroup.zpowers c) := hc2 hcB
    have hKc : C.K ∈ tqMembers (𝒞 K) c := ⟨C.hK, hcK⟩
    have hTc : T ∈ tqMembers (𝒞 K) c := ⟨hTΩ, hcT⟩
    have hNc : N ∈ tqMembers (𝒞 K) c := ⟨hN.1, hcN⟩
    have hRs : IsSylow2In R (exactCore c C.K) :=
      (isSylow2In_exactCore_iff hΩ hc2' C.hK hcK).mpr ⟨F.syl, fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hRc r hr)⟩
    have hR's : IsSylow2In R' (exactCore c T) :=
      (isSylow2In_exactCore_iff hΩ hc2' hTΩ hcT).mpr ⟨F.syl', fun r hr =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hR'c r hr)⟩
    have hxc : x ∈ exactCore c C.K := hRs.1 F.hx
    have hyc : y ∈ exactCore c T := hR's.1 F.hy
    have hBY : B ≤ exactLayer (𝒞 K) c := by
      rw [hB, Subgroup.closure_le]
      rintro w (rfl | rfl | rfl)
      · exact exactCore_le_exactLayer hKc (mem_exactCore hz hc2' hcK)
      · rw [← F.hxy]
        exact mul_mem (exactCore_le_exactLayer hKc hxc) (exactCore_le_exactLayer hTc hyc)
      · exact exactCore_le_exactLayer hNc (mem_exactCore hn hc2' hcN)
    exact generation_vertex C hall' F hTz hgz hcB hcz huc hKc hTc hxc hyc hBY
  have hKtq : ∀ c : G, (c = n ∨ c = n * z) → K ∈ tqMembers (𝒞 K) c := fun c hcs =>
    ⟨C.hK, (hvert c hcs).2.2.2.1⟩
  have hlinkz : InvolutionLinkStar p f (𝒞 K) B S z := by
    refine linkStar C hno hall' (g := 1) (by group) hN hn hnz fun w hw => hSall w ?_
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hnzc.symm)
  have hlinkv : ∀ c : G, (c = n ∨ c = n * z) → ∀ {L : Subgroup G}, L ∈ 𝒞 K →
      IsClassicalMember p f L c → InvolutionLinkStar p f (𝒞 K) B S c := by
    intro c hcs L hL hLc
    obtain ⟨g, hgz⟩ := hconjg hL hLc
    have hcz := (hvert c hcs).2.1
    refine linkStar C hno hall' hgz (hKtq c hcs) hz (Ne.symm hcz) fun w hw => hSall w ?_
    rcases hcs with rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [mul_assoc, hz2, mul_one]))
  have hframe : FrameSideTwoStar p f (𝒞 K) B S :=
    { elem := hbal.elem
      card := by rw [hbal.card]
      subset := by
        rintro M (h | h | ⟨hM, -⟩)
        · rw [h]
          exact C.hK
        · rw [Set.mem_singleton_iff.mp h]
          exact hN.1
        · exact hM
      nonempty := ⟨K, Set.mem_insert _ _⟩
      involution := by
        rintro M (h | h | ⟨-, hM⟩)
        · rw [h]
          exact ⟨z, hzB, hz⟩
        · rw [Set.mem_singleton_iff.mp h]
          exact ⟨n, hnB, hn⟩
        · exact ⟨n * z, hnzB, hM⟩
      generation := by
        rintro a - ⟨M, (h | h | ⟨hMΩ, hMnz⟩), hMa⟩
        · rw [h] at hMa
          rw [huniq hMa hz]
          exact generation_z C hall' F hN hn hnz hTz
        · rw [Set.mem_singleton_iff.mp h] at hMa
          rw [huniq hMa hn]
          exact hgenv n (Or.inl rfl) hN.1 hn
        · rw [huniq hMa hMnz]
          exact hgenv (n * z) (Or.inr rfl) hMΩ hMnz
      link := by
        rintro a - ⟨M, (h | h | ⟨hMΩ, hMnz⟩), hMa⟩
        · rw [h] at hMa
          rw [huniq hMa hz]
          exact hlinkz
        · rw [Set.mem_singleton_iff.mp h] at hMa
          rw [huniq hMa hn]
          exact hlinkv n (Or.inl rfl) hN.1 hn
        · rw [huniq hMa hMnz]
          exact hlinkv (n * z) (Or.inr rfl) hMΩ hMnz }
  have hΩIn : InClass p f (𝒞 K) := inClass_conjugates hz
  have hgen := rankTwoSpan_eq_top_of_dConnected_star hp2 hq hΩIn hframe hconn
  have hΔ := deltaCore_eq_bot_of_rankThreeBalance hbal
    (componentClassificationOddCore_eq_bot_of_simple hnab) hgen
  have hSB := Q3.stronglyBalanced_of_weakBalanced hbal.elem (by rw [hbal.card]) hbal.weak hΔ
  have hOz : involutionOddCore z ≤ Subgroup.centralizer (B : Set G) := hSB z hzB hz1
  have hon : ∀ o ∈ involutionOddCore z, o * n = n * o := fun o ho =>
    ((Subgroup.mem_centralizer_iff.mp (hOz ho)) n hnB).symm
  have hoz : ∀ o ∈ involutionOddCore z, o * z = z * o := fun o ho =>
    NDBH.mul_comm_of_mem_involutionOddCore ho
  have hL : NDBH.LitO2 p f (𝒞 K) z := by
    intro M hM m hm o ho
    by_cases hmz : m = z
    · rw [hmz]
      exact hoz o ho
    have hmC := C.involution_mem_centralizer hM hm
    have hm2 : m * m = 1 := hm.isCentralInvolution.sq
    rcases NDBG.nbar_eq_or_mul_eq C hno hall' hM hN hm hn hmz hnz with h | h
    · rw [NDBH.eq_of_oddQuotMk_eq hmC hnC hm2 hn2 h hon]
      exact hon o ho
    · have hzn : z * n ∈ Subgroup.centralizer ({z} : Set G) := mul_mem (XCtx.hzC z) hnC
      have hzn2 : z * n * (z * n) = 1 := by
        calc z * n * (z * n) = z * (n * z) * n := by group
          _ = z * (z * n) * n := by rw [hnzc]
          _ = (z * z) * (n * n) := by group
          _ = 1 := by rw [hz2, hn2, one_mul]
      have hnn : oddQuotMk z ⟨n, hnC⟩ * oddQuotMk z ⟨n, hnC⟩ = 1 := by
        rw [← map_mul]
        have : (⟨n, hnC⟩ * ⟨n, hnC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = 1 :=
          Subtype.ext hn2
        rw [this, map_one]
      have heq : oddQuotMk z ⟨m, hmC⟩ = oddQuotMk z ⟨z * n, hzn⟩ := by
        have e : (⟨z * n, hzn⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
            ⟨z, XCtx.hzC z⟩ * ⟨n, hnC⟩ := rfl
        rw [e, map_mul, ← h, mul_assoc, hnn, mul_one]
      have hczn : ∀ o ∈ involutionOddCore z, o * (z * n) = z * n * o := by
        intro o ho
        calc o * (z * n) = (o * z) * n := by group
          _ = (z * o) * n := by rw [hoz o ho]
          _ = z * (o * n) := by group
          _ = z * (n * o) := by rw [hon o ho]
          _ = z * n * o := by group
      rw [NDBH.eq_of_oddQuotMk_eq hmC hzn hm2 hzn2 heq hczn]
      exact hczn o ho
  exact NDBH.false_of_litO2 hnab hp2 hq hz hBelow hconn hno D hall hL

end NDBH3

variable (p f) in
@[expose] def NoAllA1NarrowNT : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        (¬ HasTwin p f K z → (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m →
          m ≠ z → modOdd z (exactCore z M) = modOdd z (exactCore z N)) → False) ∧
        (¬ HasTwin p f K z → ∀ N' ∈ tqMembers (𝒞 K) z, ∀ n' : G, IsClassicalMember p f N' n' →
          n' ≠ z → modOdd z (exactCore z N') ≠ modOdd z (exactCore z N) →
          (∃ (h : n ∈ Subgroup.centralizer ({z} : Set G))
            (h' : n' ∈ Subgroup.centralizer ({z} : Set G)),
            oddQuotMk z ⟨n, h⟩ * oddQuotMk z ⟨n', h'⟩ = oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩) →
          (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
            modOdd z (exactCore z M) = modOdd z (exactCore z N) ∨
              modOdd z (exactCore z M) = modOdd z (exactCore z N')) → False)

theorem noAllA1Narrow_of_nt (h : NoAllA1NarrowNT p f) : NoAllA1Narrow p f := by
  intro G _ _ _ hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  obtain ⟨h₁, h₂⟩ := h G hnab hp2 hq K z hz hBelow hconn hno D hall N hN n hn hnz
  exact ⟨h₁, h₂, fun hT _ _ _ _ =>
    NDBH3.false_of_twin hnab hp2 hq hz hBelow hconn hno D hall hN hn hnz hT⟩

end CFSG.ClassicalInvolution.NDB

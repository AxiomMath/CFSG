module

public import CFSG.ClassicalInvolution.SmallCases.NDBH6
public import CFSG.ClassicalInvolution.SmallCases.NDBD4AEmpty
public import CFSG.ClassicalInvolution.SmallCases.NDBG0
public import CFSG.ClassicalInvolution.SmallCases.NDBC1
public import CFSG.ClassicalInvolution.SmallCases.NDBCRes
public import CFSG.ClassicalInvolution.Asc77.AscT8Setup
public import CFSG.ClassicalInvolution.Asc77.WP3LayerLie
public import CFSG.ClassicalInvolution.Asc77.WP3LayerConj
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
public import CFSG.ClassicalInvolution.AschTight.C195Wreath
public import CFSG.ClassicalInvolution.SmallCases.NDBH5

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3 CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen CFSG.ClassicalInvolution.Asc77.T8R
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T8R.Loc

section Data

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem exists_std8Core (hs : AscStandCore p f Ω K) (hnt : ∀ K' ∈ twinSet Ω K, K' = K)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    ∃ (S : Sylow 2 G) (R T W : Subgroup G), Std8Core p f Ω K J S R T W z t := by
  have hp : p ≠ 2 := hs.odd
  have hq : 5 ≤ p ^ f := hs.five
  have hΩ : HypOmegaMod p f Ω := hs.hyp
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := T3.isSylow2In_of_mem_RSet_of_le hp hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := T3.exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set G) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := (l6_9_proved p f hp hq G Ω hΩ S).1
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    le_normalizer_biSup_of_acts hηinv
  exact ⟨S, R, T, ⨆ U ∈ η, U,
    { stand := hs
      noTwins := hnt
      hz := hz
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hs.mem hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
        fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩ }⟩

theorem ShapeAt.conj (hΩ : ConjInvariant Ω) (hsh : ShapeAt p f Ω z J) (g : G) :
    ShapeAt p f Ω (g * z * g⁻¹) (conjSub g J) := by
  intro M hM m hm hmz
  rw [tqMembers_conj hΩ g z] at hM
  obtain ⟨M₀, hM₀, rfl⟩ := hM
  have hm₀ : IsClassicalMember p f M₀ (g⁻¹ * m * g) := by
    have h := hm.conj g⁻¹
    rwa [conjSub_inv_conjSub, inv_inv] at h
  have hne : g⁻¹ * m * g ≠ z := fun h => hmz (by rw [← h]; group)
  rw [exactCore_conjSub, exactCore_conjSub, ← map_oddQuotConj_modOdd, ← map_oddQuotConj_modOdd,
    hsh M₀ hM₀ _ hm₀ hne]

theorem shapeAt_symm (hs : Std8Core p f Ω K J S R T W z t) (hsh : ShapeAt p f Ω z J) :
    ShapeAt p f Ω t K := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨g, hg⟩ := hs.stand.trans J hs.hJ.1
  have htg : t = g * z * g⁻¹ := hs.ht.eq (hg ▸ hs.hz.conj g)
  have hshg := hsh.conj hΩ.conjInvariant g
  rw [← htg] at hshg
  have hKt : K ∈ tqMembers Ω t := mem_tqMembers_of_nbr hs.symm' hs.symm'.hJ
  have hKz : IsClassicalMember p f K z :=
    classical_of_unique hs.stand.odd hs.stand.five hΩ hs.stand.mem hs.hz
  have hK := hshg K hKt z hKz (ne_of_std8Core hs).symm
  intro M hM m hm hmt
  exact (hshg M hM m hm hmt).trans hK.symm

theorem false_of_shape [IsSimpleGroup G] (C : XCtx p f Ω z) (C' : XCtx p f Ω t)
    (hs : Std8Core p f Ω K J S R T W z t) (hsh : ShapeAt p f Ω z J) : False :=
  false_of_loc26 hs (loc26_of_shape C hs hsh) (loc26_of_shape C' hs.symm' (shapeAt_symm hs hsh))

end Data

end T8R.Loc

end CFSG.ClassicalInvolution.Asc77

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

local notation "𝒞" => Generic.CoreAssembly.conjClass

namespace NDBH

section KxN

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem false_of_KxN [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G} (hz : IsClassicalMember p f K z)
    (hBelow : CITBelowU p f (Nat.card G)) (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    (hall : ∀ i, D.tag i = .PSL ∧ D.rank i = 2) {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z)
    {n : G} (hn : IsClassicalMember p f N n) (hnz : n ≠ z) (hT : ¬ HasTwin p f K z)
    (hsh : ∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m → m ≠ z →
      modOdd z (exactCore z M) = modOdd z (exactCore z N)) : False := by
  have hΩ : Asc77.HypOmegaMod p f (𝒞 K) := Cover.hypOmegaMod hnab hp2 hq hz hBelow
  have hKz : IsUniqueInvolution K z := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hz
  have htag : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4 := fun i => by
    rw [(hall i).1]
    exact ⟨by decide, by decide⟩
  have hstand : Asc77.T8R.Loc.AscStandCore p f (𝒞 K) K :=
    ⟨hp2, hq, hΩ, D4.aEmpty_of_tags hp2 hq hΩ hz D htag hN hn hnz, mem_conjClass_self K,
      fun _ hJ => hJ⟩
  have hnt : ∀ K' ∈ Asc77.twinSet (𝒞 K) K, K' = K := by
    rintro K' ⟨hK'Ω, z', hz', hK'z'⟩
    obtain rfl : z = z' := hKz.eq hz'
    by_contra hne
    exact hT ⟨K', hK'Ω, hne, Asc77.T8R.Loc.classical_of_unique hp2 hq hΩ hK'Ω hK'z'⟩
  have hNn : IsUniqueInvolution N n := ConnectedA2.isUniqueInvolution_of_isClassicalMember hp2 hq hn
  have hJ : N ∈ Asc77.omegaNbr (𝒞 K) K :=
    NDBG.mem_omegaNbr_of_tq hp2 hq hΩ (mem_conjClass_self K) hKz hN hn hnz
  obtain ⟨S, R, T, W, hs⟩ := Asc77.T8R.Loc.exists_std8Core hstand hnt hKz hJ hNn
  obtain ⟨D'⟩ := lieSystemAt_exactFamily hΩ.conjInvariant hΩ.classical
    (isPGroup_zpowers_of_sq_eq_one hn.isCentralInvolution.sq) hBelow
    (singleton_not_subset_center hnab hn.isCentralInvolution.ne_one)
    ⟨N, mem_tqMembers_of_isClassicalMember hN.1 hn⟩
  exact Asc77.T8R.Loc.false_of_shape (Cover.toXCtx hnab hp2 hq hz hBelow D)
    ⟨N, hN.1, hNn, hΩ, hp2, hq, D'⟩ hs hsh

end KxN

section Narrow

variable (p f : ℕ) [Fact p.Prime]

@[expose] def NarrowKxN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    p ≠ 2 → 5 ≤ p ^ f → ∀ (K : Subgroup G) (z : G), IsClassicalMember p f K z →
      CITBelowU p f (Nat.card G) → Disconnected.DConnected (𝒞 K) →
      (∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A) →
      ∀ D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z, (∀ i, D.tag i = .PSL ∧ D.rank i = 2) →
      ∀ N ∈ tqMembers (𝒞 K) z, ∀ n : G, IsClassicalMember p f N n → n ≠ z →
        ¬ HasTwin p f K z → (∀ M ∈ tqMembers (𝒞 K) z, ∀ m : G, IsClassicalMember p f M m →
          m ≠ z → modOdd z (exactCore z M) = modOdd z (exactCore z N)) → False

variable {p f}

theorem narrowKxN_holds : NarrowKxN p f :=
  fun _ _ _ _ hnab hp2 hq _ _ hz hBelow _ _ D hall _ hN _ hn hnz hT hsh =>
    false_of_KxN hnab hp2 hq hz hBelow D hall hN hn hnz hT hsh

end Narrow

end NDBH

end CFSG.ClassicalInvolution.NDB

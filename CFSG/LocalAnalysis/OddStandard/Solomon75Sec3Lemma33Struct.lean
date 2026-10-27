module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33K0
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Core
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

section Struct33

variable {n : ℕ} {z : X} {Z : Subgroup X}

@[expose] def witnessSet (X : Type) [Group X] (n : ℕ) (z : X) (Z : Subgroup X) : Set X :=
  {u | u ∈ Z ∧ ∃ L : Subgroup X, IsIntrinsicIn X (centralizer ({z} : Set X)) L u ∧
    IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n}

@[expose] def EinfSet (X : Type) [Group X] (n : ℕ) (z : X) (Z : Subgroup X) : Set (Subgroup X) :=
  {E | ∃ L : Subgroup X, ((∃ u, IsIntrinsicIn X (centralizer ({z} : Set X)) L u) ∧
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) ∧ E = oTwoPrimeOf (L ⊓ centralizer (Z : Set X))}

theorem IsSec5Pair.exists_witness_mem (hp : IsSec5Pair X n z Z) {L : Subgroup X} {u₀ : X}
    (hL : IsIntrinsicIn X (centralizer ({z} : Set X)) L u₀)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    ∃ u ∈ Z, IsIntrinsicIn X (centralizer ({z} : Set X)) L u := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u₀ ∈ zStar (K0 X n (centralizer ({z} : Set X))) := hL.mem_zStar_K0 hLn
  have hu0' : u₀ ∈ Z ⊔ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) := by
    rw [sup_comm]; exact zStar_le_pPrimeCoreOf_sup hp.sylow hu0
  have hZK : Z ≤ K0 X n (centralizer ({z} : Set X)) := hp.sylow.1.trans inf_le_left
  have hZN : Z ≤ normalizer (pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) : Set X) :=
    fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hZK hx)
  have hOodd : Odd (Nat.card (pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))))) :=
    odd_card_oddCoreOf _
  have hu02 : u₀ ^ (2 ^ 1) = 1 := by
    have : u₀ ^ 2 = 1 := by rw [← hL.1]; exact pow_orderOf_eq_one u₀
    simpa using this
  obtain ⟨o, ho, ζ, hζ, -, hu0eq⟩ :=
    exists_conj_twoElt_of_mem_sup_odd_X hZN hOodd hu0' hu02
  refine ⟨ζ, hζ, ?_⟩
  have hoCz : o ∈ centralizer ({z} : Set X) := K0_le n _ (oddCoreOf_le _ ho)
  have hoL : o ∈ normalizer (L : Set X) :=
    pPrimeCoreOf_le_normalizer_of_isPCompIn hL.2.2.1 (pPrimeCoreOf_K0_le n _ ho)
  have := hL.conj_witness (g := o⁻¹) (Subgroup.inv_mem _ (Subgroup.le_normalizer hoCz))
    (Subgroup.inv_mem _ hoL)
  have hconj : o⁻¹ * u₀ * (o⁻¹)⁻¹ = ζ := by rw [hu0eq]; group
  rwa [hconj] at this

theorem IsSec5Pair.le_centralizerSection (hp : IsSec5Pair X n z Z) {L : Subgroup X} {u₀ : X}
    (hL : IsIntrinsicIn X (centralizer ({z} : Set X)) L u₀)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    Z ≤ centralizerSection L (pPrimeCoreOf 2 L) := by
  intro t ht
  have htA : t ∈ zStar (K0 X n (centralizer ({z} : Set X))) := hp.sylow.1 ht
  have htC : t ∈ centralizer ({z} : Set X) := hp.le_centralizer ht
  have hLK : L ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup ⟨⟨u₀, hL⟩, hLn⟩
  exact normalizes_isPCompIn_of_comm_mem hL.2.2.1 (Subgroup.le_normalizer htC) (fun l hl =>
    pPrimeCoreOf_K0_le n _ (htA.2.2.2 l (hLK hl)))

theorem IsSec5Pair.isIntrinsicIn_normalizer (hp : IsSec5Pair X n z Z) {L : Subgroup X} {u : X}
    (hu : u ∈ Z) (hL : IsIntrinsicIn X (centralizer ({z} : Set X)) L u)
    (hLn : IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n) :
    IsIntrinsicIn X (normalizer (Z : Set X)) (oTwoPrimeOf (L ⊓ centralizer (Z : Set X))) u ∧
      IsDoubleCoverOfAlt (↥(oTwoPrimeOf (L ⊓ centralizer (Z : Set X))) ⧸
          pPrimeCore 2 ↥(oTwoPrimeOf (L ⊓ centralizer (Z : Set X)))) n ∧
      L ≤ pPrimeCoreOf 2 L ⊔ oTwoPrimeOf (L ⊓ centralizer (Z : Set X)) := by
  have huT : u ∈ centralizer (Z : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (hp.isMulCommutative.is_comm.comm ⟨g, hg⟩ ⟨u, hu⟩)
  obtain ⟨h1, h2, h3⟩ := hL.descend hLn hp.isPGroup (hp.le_centralizerSection hL hLn) huT
  have hinf : centralizer ({z} : Set X) ⊓ centralizer (Z : Set X) = centralizer (Z : Set X) :=
    inf_eq_right.2 (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hp.mem))
  rw [hinf] at h1
  exact ⟨⟨h1.1, h1.2.1, isPCompIn_normalizer_of_centralizer h1.2.2.1, h1.2.2.2⟩, h2, h3⟩

theorem IsSec5Pair.K0_normalizer_le (hA : HypA X) (hn : IsMaxAhatDeg X n)
    (hp : IsSec5Pair X n z Z) :
    K0 X n (normalizer (Z : Set X)) ≤ K0 X n (centralizer ({z} : Set X)) := by
  refine sSup_le fun E hE => ?_
  obtain ⟨⟨u, hu⟩, hEn⟩ := hE
  have hENN : IsPCompIn 2 (normalizer (Z : Set X)) E := hu.2.2.1
  have hZN : Z ≤ normalizer (Z : Set X) := Subgroup.le_normalizer
  have hEC : E ≤ centralizer (Z : Set X) :=
    le_centralizer_of_isPCompIn_of_normal_pgroup hENN hZN le_rfl hp.isPGroup
  have hCz : centralizer (Z : Set X) ≤ centralizer ({z} : Set X) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hp.mem)
  have hEH' : E ≤ normalizer (Z : Set X) ⊓ centralizer ({z} : Set X) :=
    le_inf hENN.1 (hEC.trans hCz)
  have hu' : IsIntrinsicIn X (normalizer (Z : Set X) ⊓ centralizer ({z} : Set X)) E u :=
    ⟨hu.1, hu.2.1, ⟨hEH', isPComponent_subgroupOf_mono hEH' inf_le_left hENN.2⟩, hu.2.2.2⟩
  obtain ⟨M, hM, hMn, hEM⟩ :=
    exists_isIntrinsicIn_centralizer hA hn (s := z) hp.orderOf_z inf_le_right hu' hEn
  have hMK : M ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup ⟨⟨u, hM⟩, hMn⟩
  have hEeq : oTwoPrimeOf (E ⊓ centralizer ({u} : Set X)) ⊔ pPrimeCoreOf 2 E = E := by
    have := hu.2.2.2.1
    rw [oPrimeResidualOf_two_eq_oTwoPrimeOf] at this
    rw [sup_comm]; exact this.symm
  have hEuE : oTwoPrimeOf (E ⊓ centralizer ({u} : Set X)) ≤ E :=
    (oTwoPrimeOf_le _).trans inf_le_left
  exact le_of_covers_of_normalized hEuE ((covers_subgroupOf_iff hEuE).2 hEeq) hu.isTwoGenQuasi.1
    (hEM.trans hMK) (fun c hc => mem_normalizer_of_map_conj_eq
      (map_conj_K0 n (Subgroup.le_normalizer (hCz (hEC hc)))))

theorem IsSec5Pair.K0_centralizer_le_sup_E (hp : IsSec5Pair X n z Z) :
    K0 X n (centralizer ({z} : Set X)) ≤
      pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ⊔ sSup (EinfSet X n z Z) := by
  refine sSup_le fun L hL => ?_
  obtain ⟨⟨u₀, hu₀⟩, hLn⟩ := hL
  obtain ⟨u, huZ, hu⟩ := hp.exists_witness_mem hu₀ hLn
  obtain ⟨-, -, h3⟩ := hp.isIntrinsicIn_normalizer huZ hu hLn
  have hLK : L ≤ K0 X n (centralizer ({z} : Set X)) := le_sSup ⟨⟨u₀, hu₀⟩, hLn⟩
  have hOL : pPrimeCoreOf 2 L ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) :=
    pPrimeCoreOf_le_oddCoreOf hLK (isPComponent_two_iff.1 (hu₀.isPCompIn_K0 hLn).2).1
  exact h3.trans (sup_le_sup hOL (le_sSup ⟨L, ⟨⟨u₀, hu₀⟩, hLn⟩, rfl⟩))

theorem IsSec5Pair.sSup_E_le_K0 (hp : IsSec5Pair X n z Z) :
    sSup (EinfSet X n z Z) ≤ K0 X n (normalizer (Z : Set X)) := by
  refine sSup_le fun E hE => ?_
  obtain ⟨L, ⟨⟨u₀, hu₀⟩, hLn⟩, rfl⟩ := hE
  obtain ⟨u, huZ, hu⟩ := hp.exists_witness_mem hu₀ hLn
  obtain ⟨h1, h2, -⟩ := hp.isIntrinsicIn_normalizer huZ hu hLn
  exact le_sSup ⟨⟨u, h1⟩, h2⟩

theorem IsSec5Pair.K0_centralizer_le_sup (hp : IsSec5Pair X n z Z) :
    K0 X n (centralizer ({z} : Set X)) ≤ pPrimeCoreOf 2 (K0 X n (centralizer ({z} : Set X))) ⊔
      K0 X n (normalizer (Z : Set X)) :=
  hp.K0_centralizer_le_sup_E.trans (sup_le_sup_left hp.sSup_E_le_K0 _)

theorem IsSec5Pair.le_closure_witnessSet (hp : IsSec5Pair X n z Z) :
    Z ≤ Subgroup.closure (witnessSet X n z Z) := by
  have hW : ∀ L : Subgroup X, (∃ u, IsIntrinsicIn X (centralizer ({z} : Set X)) L u) →
      IsDoubleCoverOfAlt (↥L ⧸ pPrimeCore 2 ↥L) n →
        ∃ u ∈ (Z : Set X), IsIntrinsicIn X (centralizer ({z} : Set X)) L u := by
    rintro L ⟨u₀, hu₀⟩ hLn
    exact hp.exists_witness_mem hu₀ hLn
  have h1 := zStar_K0_le_sup_witnesses n (centralizer ({z} : Set X)) (Z : Set X) hW
  have hZK : Z ≤ K0 X n (centralizer ({z} : Set X)) := hp.sylow.1.trans inf_le_left
  have hC : Subgroup.closure (witnessSet X n z Z) ≤ Z :=
    (Subgroup.closure_le Z).2 fun u hu => hu.1
  exact le_of_le_sup_of_isPGroup hC hp.isPGroup (odd_card_oddCoreOf _)
    (fun x hx => mem_normalizer_pPrimeCoreOf_of_mem (hZK (hC hx))) (hp.sylow.1.trans h1)

theorem IsSec5Pair.witnessSet_subset (hp : IsSec5Pair X n z Z) :
    witnessSet X n z Z ⊆ K0 X n (normalizer (Z : Set X)) := by
  rintro u ⟨huZ, L, hu, hLn⟩
  obtain ⟨h1, h2, -⟩ := hp.isIntrinsicIn_normalizer huZ hu hLn
  exact (le_sSup ⟨⟨u, h1⟩, h2⟩ : _ ≤ K0 X n (normalizer (Z : Set X))) h1.2.1

theorem IsSec5Pair.le_K0_normalizer (hp : IsSec5Pair X n z Z) :
    Z ≤ K0 X n (normalizer (Z : Set X)) :=
  hp.le_closure_witnessSet.trans ((Subgroup.closure_le _).2 hp.witnessSet_subset)

end Struct33

end CFSG.OddStandard.Solomon75

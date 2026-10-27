module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcE6FourPerX
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcTriSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBExcEFinal
public import CFSG.RankThree.PartOne.KE.E6FourData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge TauCeti CFSG.RankThree.Chevalley
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
  CFSG.RankThree.LocalRank CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (weylMatrix weylMatrix_mulVec)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevIndexTwo)
open scoped Matrix MatrixGroups commutatorElement

section Torus

theorem eq_one_of_sq_eq_one_of_mem_torusGroup {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L) (h : y ^ 2 = 1) : y = 1 := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  have hb : b ^ 2 = 1 := by
    apply rootDiagUnit_injective (τ := τ) (K := L)
    have h1 : rootDiagUnit τ (b ^ 2) = rootDiagUnit τ b ^ 2 :=
      map_pow (rootDiagUnitHom τ L) b 2
    rw [h1, h]
    exact (map_one (rootDiagUnitHom τ L)).symm
  have hb1 : b = 1 := by
    funext i
    have hi : (b i) ^ 2 = 1 := congrFun hb i
    have hi' : ((b i : Lˣ) : L) ^ 2 = 1 := by
      have := congrArg Units.val hi
      simpa using this
    have h2 : (2 : L) = 0 := by exact_mod_cast CharP.cast_eq_zero L 2
    have h3 : (((b i : Lˣ) : L) - 1) ^ 2 = 0 := by
      linear_combination hi' + (1 - ((b i : Lˣ) : L)) * h2
    have h4 : ((b i : Lˣ) : L) - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h3
    exact Units.ext (sub_eq_zero.1 h4)
  rw [hb1]
  exact map_one (rootDiagUnitHom τ L)

end Torus

section Main


theorem oddPCoreInClosure_E6_four (K : Type) [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1) {x : adjointGroup .E6 K} (hx : orderOf x = p) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  let L := AlgebraicClosure K
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcm := canonicalRep_mem_monomialSubgroup L e6F4U
  have hπ : weylQuotientHom .E6 L ⟨canonicalRep (coxeterSystem .E6) L e6F4U, hcm⟩ = e6F4U :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6F4U)
  have hnW : ∀ u, weylQuotientHom .E6 L ⟨canonicalRep (coxeterSystem .E6) L e6F4U, hcm⟩ • u =
      (weylMatrix e6F4U) *ᵥ u := fun u => by rw [hπ, weylMatrix_mulVec]
  obtain ⟨-, hordq, hΦ, -⟩ := e6Four_data hp hp3 hpq
  obtain ⟨g0, hg0C, hg0, hperf, hT, hconj⟩ := e6_four_frame K hf hK hp hp3 hpq L _ hcm hnW
  have hpg : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := hconj _ hpg
  have hh := hc x (Subgroup.mem_zpowers x)
  obtain ⟨ψ, hψinj, -, hψ⟩ := e6_four_perx_odd K hf hK hp hp3 hordq hΦ L _ hcm hnW g0 hg0C hg0
    hperf hT hx c hh
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hh).1
  obtain ⟨hreg, hnon⟩ := hψ b hb.symm
  by_cases hSig : rootCharKernel b = ∅
  ·
    refine OddPCoreInClosure.of_odd_card ?_
    by_contra hnodd
    have h2 : 2 ∣ Nat.card (Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) :=
      (Nat.not_odd_iff_even.1 hnodd).two_dvd
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))) 2 h2
    have hψy : ψ y ^ 2 = 1 := by rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
    have h1 := eq_one_of_sq_eq_one_of_mem_torusGroup (hreg hSig y) hψy
    have hy1 : y = 1 := hψinj (by rw [h1, map_one])
    rw [hy1, orderOf_one] at hy
    omega
  · obtain ⟨Pt, hPtq, hcomm, hcent, Y₀, hY₀, hY₀o⟩ := hnon (Set.nonempty_iff_ne_empty.2 hSig)
    have hQD : Pt ≤ ψ.range := by
      rw [← hcomm, Subgroup.commutator_le]
      intro u hu v hv
      exact ψ.range.mul_mem (ψ.range.mul_mem (ψ.range.mul_mem hu hv) (ψ.range.inv_mem hu))
        (ψ.range.inv_mem hv)
    have hQn : ∀ c : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .E6 K))), ∀ q ∈ Pt,
        ψ c * q * (ψ c)⁻¹ ∈ Pt := by
      intro c q hq
      have h1 : ⁅ψ c, q⁆ ∈ Pt := by
        rw [← hcomm]
        exact Subgroup.commutator_mem_commutator ⟨c, rfl⟩ (hQD hq)
      have h2 : ψ c * q * (ψ c)⁻¹ = ⁅ψ c, q⁆ * q := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Pt.mul_mem h1 hq
    have hpQ : p ∣ Nat.card Pt := by
      have h1 : orderOf (⟨Y₀, hY₀⟩ : Pt) = p := by
        rw [← Subgroup.orderOf_coe]
        exact hY₀o
      rw [← h1]
      exact orderOf_dvd_natCard _
    haveI : Finite ψ.range := Finite.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
    have hfinW : Finite (ψ.range ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) :=
      Finite.of_injective (Subgroup.inclusion (inf_le_left : ψ.range ⊓ torusGroup .E6 L ≤ ψ.range))
        (Subgroup.inclusion_injective _)
    have hWodd : Odd (Nat.card (ψ.range ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L))) := by
      by_contra hnodd
      have h2 : 2 ∣ Nat.card (ψ.range ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L)) :=
        (Nat.not_odd_iff_even.1 hnodd).two_dvd
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
        (G := (ψ.range ⊓ torusGroup .E6 L : Subgroup (ModGL .E6 L))) 2 h2
      have hw2 : (w : ModGL .E6 L) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, ← hw, pow_orderOf_eq_one, Subgroup.coe_one]
      have h1 := eq_one_of_sq_eq_one_of_mem_torusGroup w.2.2 hw2
      have hw1 : w = 1 := Subtype.ext h1
      rw [hw1, orderOf_one] at hw
      omega
    refine oddPCoreInClosure_of_map_quasisimple hp ψ hψinj Pt hQD hQn hPtq hpQ
      (ψ.range ⊓ torusGroup .E6 L) ?_ hWodd
    intro c hc'
    exact ⟨⟨c, rfl⟩, hcent (ψ c) ⟨c, rfl⟩ fun u hu => hc' u hu⟩

end Main

section Final


theorem chevTwoPClosureOddE6Four_holds : ChevTwoPClosureOddE6Four := by
  intro p hp hp2 L _ _ hs hnab hrk hSE d hF hdi ⟨e⟩
  obtain ⟨d, hv⟩ := d
  cases d with
  | E6 q =>
    have hq2 : q.p = 2 := hdi
    have hord : orderOf ((q.card : ℕ) : ZMod p) = 4 := hF
    have hp3 : 3 < p := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hne : ((q.card : ℕ) : ZMod p) ≠ 0 := by
        intro h0
        rw [h0, orderOf_zero] at hord
        omega
      have hdvd := ZMod.orderOf_dvd_card_sub_one hne
      rw [hord] at hdvd
      have := Nat.le_of_dvd (by have := hp.two_le; omega) hdvd
      omega
    obtain ⟨K, _, _, hK, hchK, ⟨eK⟩⟩ :=
      exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
    haveI : CharP K 2 := hq2 ▸ hchK
    have hK2 : Nat.card K = 2 ^ q.exponent := by rw [hK, PrimePower.card_def, hq2]
    have hpq : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + 1 := by
      have h1 : p ∣ Nat.card K ^ 2 + 1 := by
        rw [hK]
        exact dvd_of_orderOf_four hp hord
      have h2 := Int.natCast_dvd_natCast.2 h1
      push_cast at h2
      exact h2
    let θ : L ≃* adjointGroup Tag.E6 K := e.trans eK
    refine PClosureOdd.of_mulEquiv θ.symm ?_
    intro d hd1 hdp
    haveI : Fact p.Prime := ⟨hp⟩
    exact oddPCoreInClosure_E6_four K q.exponent_pos hK2 hp hp3 hpq (orderOf_eq_prime hdp hd1)
  | A _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | twistedA _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | B _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | C _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | D _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | twistedD _ _ => exact absurd hF (by simp [LieFamilyE6Four])
  | E7 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | E8 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | F4 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | G2 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | twistedE6 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | trialityD4 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | suzuki _ => exact absurd hF (by simp [LieFamilyE6Four])
  | reeG2 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | reeF4 _ => exact absurd hF (by simp [LieFamilyE6Four])
  | tits => exact absurd hF (by simp [LieFamilyE6Four])

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

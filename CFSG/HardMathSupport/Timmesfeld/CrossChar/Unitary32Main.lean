module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryPlane
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryOuter
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Base
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Count
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Unitary32Rigid
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.HardMathSupport.Curtis.Proving.ToralCaseSplit
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLHatAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Polynomial Module CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryPlane CFSG.RankThree.PartOne.KCUnitaryExact
  CFSG.RankThree.PartOne.KCUnitaryOne CFSG.RankThree.PartOne.KCUnitaryFrame
  CFSG.RankThree.PartOne.KCUnitaryLines CFSG.RankThree.PartOne.KCUnitaryScalar
  CFSG.HardMathSupport.Timmesfeld.Balance

variable {ℓ f n : ℕ} {K : Type} [Field K]

section Lift

theorem noTorsion_of_not_dvd {p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) (h : UnitaryFieldData ℓ f K) :
    ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1 := by
  intro c _ hcn hcp
  have h1 : orderOf c ∣ Nat.gcd p n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcp) (orderOf_dvd_of_pow_eq_one hcn)
  rw [(Nat.Prime.coprime_iff_not_dvd hp).2 hpn, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact h1

theorem innerLift_injective_three_two (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hne : ¬(n = 3 ∧ ℓ ^ f = 2)) (hq : ℓ ^ f = 2) (h3n : ¬ 3 ∣ n) :
    Function.Injective (innerLift h n) := by
  intro x y hxy
  have h1 := (innerLift_eq_iff hn hne).1 hxy
  obtain ⟨c, hcN, hcn, hc⟩ := QuotientGroup.eq.1 h1
  have hc3 : c ^ 3 = 1 := by
    have := (pow_succ_eq_one_iff_norm h c).2 hcN
    rwa [hq] at this
  have hc1 : c = 1 := noTorsion_of_not_dvd Nat.prime_three h3n h c hcN hcn hc3
  subst hc1
  have : x⁻¹ * y = 1 := Subtype.ext (by simpa using hc)
  exact inv_mul_eq_one.1 this

end Lift

section Eigen

variable {p : ℕ} {h : UnitaryFieldData ℓ f K}

theorem exists_orthonormal_eigenbasis_of_elem (hp : p.Prime) (hpq : p ∣ ℓ ^ f + 1)
    (Ahat : Subgroup (gramSU h (idGram K n))) [IsElementaryAbelian p Ahat] :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), IsOrthonormalFamily h b ∧
      ∀ x ∈ Ahat, ∀ i, ∃ c : K, xlin h n x (b i) = c • b i := by
  obtain ⟨ζ, hζ⟩ := KCUnitaryPlane.exists_primitiveRoot_of_dvd h hp hpq
  have : NeZero p := ⟨hp.ne_zero⟩
  have := h.finite
  have : Finite ↥Ahat := inferInstance
  have hcomm : ∀ x y : ↥Ahat, Commute (act (planeRep h n Ahat) x) (act (planeRep h n Ahat) y) :=
    fun x y => by
      have hxy : x * y = y * x := (IsMulCommutative.is_comm (M := ↥Ahat)).comm x y
      change act (planeRep h n Ahat) x * act (planeRep h n Ahat) y =
        act (planeRep h n Ahat) y * act (planeRep h n Ahat) x
      rw [← act_mul, ← act_mul, hxy]
  have hpow : ∀ x : ↥Ahat, act (planeRep h n Ahat) x ^ p = 1 := fun x => by
    have hx : x ^ p = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x.1 x.2)
    rw [← act_pow, hx, act_one]
  have hiso : ∀ (x : ↥Ahat) (v w : Fin n → K),
      idForm h n (act (planeRep h n Ahat) x v) (act (planeRep h n Ahat) x w) =
        idForm h n v w := fun x v w => planeRep_mem Ahat x v w
  obtain ⟨b, μ, hbμ, hbo⟩ := exists_orthonormal_common_eigenbasis h hζ hpq
    (idForm_isSymm h n) (idForm_separatingLeft h n)
    (fun x : ↥Ahat => act (planeRep h n Ahat) x) hcomm hpow hiso
  refine ⟨b.reindex (finCongr (Module.finrank_fin_fun K)), fun i j => ?_, fun x hx i => ?_⟩
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, hbo]
    simp
  · rw [Module.Basis.reindex_apply]
    exact ⟨μ ⟨x, hx⟩ _, hbμ ⟨x, hx⟩ _⟩

end Eigen

section Main

private theorem isElemAbelian_comap' {M N : Type*} [Group M] [Group N] (φ : M →* N)
    (hφ : Function.Injective φ) {p : ℕ} {E : Subgroup N} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap φ) := CFSG.Open.IsElemAbelian.comap hE hφ

theorem localDeltaIn_eq_bot_three_two (h : UnitaryFieldData ℓ f K) (hq : ℓ ^ f = 2) (hn : 7 ≤ n)
    (h3n : ¬ 3 ∣ n)
    (D : Subgroup (MulAut (primeFormP h (idGram K n)))) (hD : IsElemAbelian 3 D)
    (hcard : Nat.card D = 27)
    (hDinn : D ≤ (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range)
    {H : Subgroup (MulAut (primeFormP h (idGram K n)))}
    (hH : (MulAut.conj : primeFormP h (idGram K n) →*
      MulAut (primeFormP h (idGram K n))).range ≤ H) :
    localDeltaIn 3 H D = ⊥ := by
  classical
  have := h.finite
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hn3 : 3 ≤ n := by omega
  have hne : ¬(n = 3 ∧ ℓ ^ f = 2) := fun h' => by omega
  have hℓ : ℓ = 2 := by
    have : ℓ ∣ 2 := hq ▸ dvd_pow_self ℓ (by have := h.one_le; omega)
    exact (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this
  have hpℓ : 3 ≠ ℓ := by omega
  have hpq : 3 ∣ ℓ ^ f + 1 := by rw [hq]
  have hZp := noTorsion_of_not_dvd hp3 h3n h
  have hinj := innerLift_injective_three_two h hn3 hne hq h3n
  set Dh : Subgroup (gramSU h (idGram K n)) := D.comap (innerLift h n) with hDh
  have hDrange : D ≤ (innerLift h n).range := by rw [range_innerLift_eq]; exact hDinn
  have hmap : Dh.map (innerLift h n) = D := Subgroup.map_comap_eq_self hDrange
  have hDhel : IsElemAbelian 3 Dh := isElemAbelian_comap' _ hinj hD
  have hDhc : Nat.card Dh = 27 := by
    rw [← Subgroup.card_map_of_injective hinj, hmap, hcard]
  have : IsElementaryAbelian 3 Dh :=
    { toIsMulCommutative := hDhel.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
        Subtype.ext (hDhel.2 x x.2) }
  have : Finite Dh := Nat.finite_of_card_ne_zero (by rw [hDhc]; norm_num)
  have hplane : ∀ x ∈ Dh, x ≠ 1 → ∃ A' : Subgroup (gramSU h (idGram K n)), A' ≤ Dh ∧ x ∈ A' ∧
      Nonempty (PlaneSetup h n 3 A') := by
    intro x hx hx1
    obtain ⟨E, hED, hxE, hEel, hEc⟩ := exists_plane_containing hDhel hDhc hx hx1
    have hEel' : IsElementaryAbelian 3 E :=
      { toIsMulCommutative := hEel.1
        exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
          Subtype.ext (hEel.2 x x.2) }
    exact ⟨E, hED, hxE, ⟨⟨hn3, hne, hp3, hpℓ, hZp, hEel', by rw [hEc]; norm_num⟩⟩⟩
  obtain ⟨b, hbON, hbeig⟩ := exists_orthonormal_eigenbasis_of_elem hp3 hpq Dh
  have hb0 : ∀ i, b i ≠ 0 := fun i => b.ne_zero i
  have hchar : ∀ i : Fin n, ∃ χ : ↥Dh →* Kˣ, ∀ x : ↥Dh,
      xlin h n x.1 (b i) = (χ x : K) • b i := fun i =>
    exists_charHom (planeRep h n Dh) (hb0 i) (fun x => hbeig x.1 x.2 i)
  choose c hc using hchar
  have hc3 : ∀ i (x : ↥Dh), c i x ^ 3 = 1 := fun i x => by
    have hx : x ^ 3 = 1 := Subtype.ext (hDhel.2 x.1 x.2)
    rw [← map_pow, hx, map_one]
  have : Fintype ↥Dh := Fintype.ofFinite _
  have hpair : ∀ i j : Fin n, i ≠ j → ∃ x ∈ Dh, x ≠ 1 ∧ ∃ μ : K, μ ^ 3 = 1 ∧
      xlin h n x (b i) = μ • b i ∧ xlin h n x (b j) = μ • b j ∧
      (Module.finrank K (primaryComponent (xlin h n x) (X - C μ)), ℓ ^ f) ∉
        ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
    intro i j hij
    obtain ⟨x, hx1, hxij, h4⟩ := exists_four_of_chars (G := ↥Dh) hDhc hn c hc3 i j hij
    refine ⟨x.1, x.2, fun h1 => hx1 (Subtype.ext h1), (c i x : K), ?_, hc i x, ?_, ?_⟩
    · rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    · rw [hc j x, ← hxij]
    · set W := primaryComponent (xlin h n x.1) (X - C (c i x : K)) with hW
      set S : Finset (Fin n) := Finset.univ.filter fun k => c k x = c i x with hS
      have hmem : ∀ k ∈ S, b k ∈ W := fun k hk => by
        rw [hW, mem_primaryComponent_X_sub_C, hc k x, (Finset.mem_filter.1 hk).2]
      let v : S → W := fun k => ⟨b k, hmem k k.2⟩
      have hv : LinearIndependent K v := by
        refine LinearIndependent.of_comp W.subtype ?_
        exact b.linearIndependent.comp (fun k : S => (k : Fin n)) Subtype.val_injective
      have h5 := hv.fintype_card_le_finrank
      rw [Fintype.card_coe] at h5
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, not_or, hq]
      omega
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  have hcent : ∀ x ∈ Dh, g * primeFormConjHom h (idGram K n) (liftUnitary x) =
      primeFormConjHom h (idGram K n) (liftUnitary x) * g := by
    intro x hx
    refine commute_of_mem_localDeltaIn hg ?_
    rw [← hmap, primeFormConjHom_liftUnitary]
    exact ⟨x, hx, (innerLift_apply x)⟩
  have hblock : ∀ x ∈ Dh, x ≠ 1 → ∀ i : GoodBlockIdx h x, ∀ y ∈ idSpecialBlock h x (i.1 : K[X]),
      g * primeFormConjHom h (idGram K n) y = primeFormConjHom h (idGram K n) y * g := by
    intro x hx hx1 i
    obtain ⟨A', hA'D, hxA', ⟨S⟩⟩ := hplane x hx hx1
    have hle : A'.map (innerLift h n) ≤ D := hmap ▸ Subgroup.map_mono hA'D
    have hgA := localDeltaIn_antitone H hle hg
    refine commute_block_of_mem_localDeltaIn S rfl hH hgA hxA' hx1 i ?_
    by_cases hne1 : (i.1 : K[X]) = X - C 1
    · have hmem : (X - C 1 : K[X]) ∈ primaryFactors (xlin h n x) := hne1 ▸ i.1.2
      have hm := i.2.1
      rw [hne1, primaryMultiplicity_X_sub_C_one] at hm
      rw [hne1]
      refine dvd_card_idSpecialBlock_X_sub_one (S.planeData hxA') hmem le_rfl hm ?_
      have e : ((ℓ ^ f : ℕ) : ℤ) ^ 2 - (-1) ^ 2 =
          (((ℓ ^ f : ℕ) : ℤ) - 1) * (((ℓ ^ f : ℕ) : ℤ) + 1) := by ring
      rw [e]
      exact Dvd.dvd.mul_left (by exact_mod_cast hpq) _
    · exact dvd_card_idSpecialBlock_of_ne (S.planeData hxA') i hne1
  exact rigidity_of_good_pairs hn3 hne Dh hpq (fun x hx hx1 => by
      obtain ⟨A', -, hxA', hS⟩ := hplane x hx hx1
      exact ⟨A', hS, hxA'⟩) b hbON hpair g hcent hblock

end Main

end CFSG.HardMathSupport.Timmesfeld.CrossChar

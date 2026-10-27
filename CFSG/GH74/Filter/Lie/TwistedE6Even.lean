module

public import CFSG.GH74.Filter.Lie.SepWitness
public import CFSG.GH74.Filter.Lie.ZModTwo
public import CFSG.GH74.Filter.ElemAbelian
public import CFSG.GH74.Filter.Statements
public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels

public section

namespace CFSG.GH74.Filter.Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits

@[expose] def e6five : SepWitness TwistTag.E6.tag 5 where
  word := ![([] : List (Fin 6)), ([3] : List (Fin 6)), ([4, 2, 3] : List (Fin 6)),
    ([3, 4, 2, 3] : List (Fin 6)), ([1, 3, 4, 5, 2, 3, 4, 1, 3, 2] : List (Fin 6))]
  simple := ![(1 : Fin 6), (1 : Fin 6), (1 : Fin 6), (1 : Fin 6), (0 : Fin 6)]
  sep := ![([1] : List (Fin 6)), ([1, 3] : List (Fin 6)), ([1, 3, 4, 2] : List (Fin 6)),
    ([1, 3, 4, 2, 3] : List (Fin 6)),
    ([5, 4, 3, 2, 1, 3, 4, 5, 0, 2, 3, 4, 1, 3, 2, 0] : List (Fin 6))]

theorem e6five_check : e6five.check = true := by decide +kernel

theorem e6five_vec_fixed_list : ∀ i : Fin 5,
    List.ofFn (permLattice TwistTag.E6.perm (e6five.vec i)) = List.ofFn (e6five.vec i) := by
  decide +kernel

theorem e6five_rootTwist
    (i : Fin 5) : rootTwist .E6 (e6five.root i) = e6five.root i :=
  Subtype.ext (by
    have h := List.ofFn_injective (e6five_vec_fixed_list i)
    rw [← RootWitness.root_val] at h
    exact h)

theorem five_le_pRank_commutator_twistFixed_E6_two
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (σ : K →+* K) (hσ : Function.Surjective σ) (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ}
    (hu : (u : K) ^ 2 ≠ 1) :
    5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (commutator (twistFixed .E6 K σ))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU := e6_U_le_twistDerived hσ hσ2 hu
  obtain ⟨hcomm, hinj⟩ := SepWitness.pi_data e6five_check (K := K)
  set Φ := MonoidHom.noncommPiCoprod
    (fun i : Fin 5 => rootHom (K := K) (e6five.root i)) hcomm with hΦ
  let ι : Multiplicative (ZMod 2) →* Multiplicative K :=
    (ZMod.castHom (dvd_refl 2) K).toAddMonoidHom.toMultiplicative
  have hι : Function.Injective ι := fun x y h =>
    Multiplicative.toAdd.injective ((ZMod.castHom_injective K) (Multiplicative.ofAdd.injective h))
  let π : (Fin 5 → Multiplicative (ZMod 2)) →* (Fin 5 → Multiplicative K) :=
    MonoidHom.pi fun i => ι.comp (Pi.evalMonoidHom (fun _ => Multiplicative (ZMod 2)) i)
  have hπ : Function.Injective π := fun x y h => funext fun i => hι (congrFun h i)
  have hroot : ∀ (i : Fin 5) (c : K), (c = 0 ∨ c = 1) →
      (rootOperatorFamily TwistTag.E6.tag).eltElement (e6five.root i) c ∈ twistDerived .E6 K σ := by
    intro i c hc
    rcases hc with rfl | rfl
    · rw [RootOperatorFamily.eltElement_zero]
      exact one_mem _
    · exact hU _ (RootGroupData.X_le_U (D := nativeData TwistTag.E6.tag K)
        (SepWitness.root_pos e6five_check i)
        ((rootOperatorFamily _).eltElement_mem_rootSubgroup _ _))
        (twistC_eltElement_one_charTwo σ (e6five_rootTwist i))
  have hmem : ∀ (i : Fin 5) (z : ZMod 2),
      rootHom (K := K) (e6five.root i) (ι (Multiplicative.ofAdd z)) ∈ twistDerived .E6 K σ := by
    intro i z
    show (rootOperatorFamily TwistTag.E6.tag).eltElement (e6five.root i)
      (ZMod.castHom (dvd_refl 2) K z) ∈ _
    rcases zmod_two_eq_zero_or_one z with rfl | rfl
    · exact hroot i _ (Or.inl (map_zero _))
    · exact hroot i _ (Or.inr (map_one _))
  have hrange : (Φ.comp π).range ≤ twistDerived .E6 K σ := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.comp_apply, hΦ, MonoidHom.noncommPiCoprod_apply]
    exact Subgroup.noncommProd_mem _ _ fun i _ => hmem i (Multiplicative.toAdd (a i))
  refine le_pRank_of_commutator (Ψ := Φ.comp π) (hinj.comp hπ) hrange (fun a b => mul_comm a b)
    (fun a => funext fun i => ?_) (card_pi_zmod_two 5)
  rw [Pi.pow_apply, Pi.one_apply]
  exact multiplicative_zmod_two_sq _

theorem five_le_pRank_of_twistedE6Model_two
    {S : Type} [Group S] [Finite S] {f : ℕ} (hf : 1 ≤ f)
    (h : TwistedChevalleyModel S .E6 (2 ^ f)) : 5 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    rw [hσc, hσc, ← pow_mul, show 2 ^ f * 2 ^ f = Nat.card K by
      rw [hK]; change _ = 2 ^ (f * 2); ring, hfr]
  have := Finite.of_equiv _ e.toEquiv
  rw [pRank_top_eq_of_mulEquiv (by norm_num) e,
    pRank_twistedDerivedQuotient σ hσ (e6_U_le_twistDerived hσ hσ2 hu)]
  exact five_le_pRank_commutator_twistFixed_E6_two σ hσ hσ2 hu

end CFSG.GH74.Filter.Lie

namespace CFSG.GH74.Filter

open CFSG.GH74.Filter.Lie
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank CFSG.LieType.Chevalley
  CFSG.LieType.BorelTits

theorem t_2E6_even
    : S_2E6_even := by
  intro G _ _ f h
  obtain ⟨⟨-, hf, -⟩, hm⟩ := h
  exact not_gen4_of_twoRank (five_le_pRank_of_twistedE6Model_two hf hm)

end CFSG.GH74.Filter

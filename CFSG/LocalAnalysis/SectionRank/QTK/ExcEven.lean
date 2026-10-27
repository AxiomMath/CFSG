module

public import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LocalAnalysis.SectionRank.QTK.Witness3

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SectionRank
open CFSG.LieType.BorelTits
open CFSG.Assembly.RankThreeEven (localRank)

theorem le_localRank_three_center_quotient {G : Type} [Group G] [Finite G] {n : ℕ}
    (Z A : Fin n → G) (h3 : ∀ i, Z i ^ 3 = 1) (h1 : ∀ i, ¬ Commute (Z i) (A i))
    (h2 : ∀ i, ¬ Commute (Z i ^ 2) (A i)) (hZA : ∀ i j, i ≠ j → Commute (Z j) (A i))
    (hZZ : ∀ i j, i ≠ j → Commute (Z i) (Z j)) {t : G} (ht : t ^ 2 = 1)
    (htc : t ∉ Subgroup.center G) (hZt : ∀ i, Commute (Z i) t) :
    n ≤ localRank 3 (G ⧸ Subgroup.center G) := by
  have h := le_localRank_of_witness_involution (H := ⊤)
    (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.ker_mk' _).le Z A h3 h1 h2 hZA hZZ
    ht htc hZt (fun _ => Subgroup.mem_top _) (Subgroup.mem_top _)
  rwa [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv Subgroup.topEquiv
    Nat.prime_three] at h


theorem three_le_localRank_of_rootWitness_two {τ : Tag} {W : RootWitness τ 4}
    (hW : W.check = true) (hO : W.orthoCheck = true) (nbr : Fin 4 → Fin τ.rank)
    (hnbr : ∀ i, τ.cartan (W.simple i) (nbr i) = -1) {K : Type} [Field K] [Finite K] [CharP K 2]
    [Finite (adjointGroup τ K)] :
    3 ≤ localRank 3 (AdjointQuotient τ K) := by
  obtain ⟨hf, hZA, hZZ⟩ := RootWitness.charTwo_facts hW hO nbr hnbr (K := K)
  have h11 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero K 2
  have ht : W.elemA K (Fin.last 3) ^ 2 = 1 := by
    rw [RootWitness.elemA, conj_pow, sq, ← (rootOperatorFamily _).eltElement_add, h11,
      (rootOperatorFamily _).eltElement_zero, mul_one, mul_inv_cancel]
  have htc : W.elemA K (Fin.last 3) ∉ Subgroup.center (adjointGroup τ K) := fun h =>
    (hf (Fin.last 3)).2.1 (Subgroup.mem_center_iff.1 h (W.elemZ K (Fin.last 3)))
  exact le_localRank_three_center_quotient (fun i : Fin 3 => W.elemZ K i.castSucc)
    (fun i : Fin 3 => W.elemA K i.castSucc) (fun i => (hf _).1) (fun i => (hf _).2.1)
    (fun i => (hf _).2.2) (fun i j hij => hZA _ _ fun h => hij (Fin.castSucc_injective _ h))
    (fun i j hij => hZZ _ _ fun h => hij (Fin.castSucc_injective _ h)) ht htc
    (fun i => hZA _ _ (Fin.castSucc_lt_last i).ne')

theorem three_le_localRank_of_untwistedModel_two {S : Type} [Group S] [Finite S] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {f : ℕ}
    (h : UntwistedChevalleyModel S τ (2 ^ f)) : 3 ≤ localRank 3 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  have : CharP K 2 := charP_of_natCard_eq_pow hK
  have : Finite (AdjointQuotient τ K) := Finite.of_equiv S e.toEquiv
  have : Finite (adjointGroup τ K) :=
    Finite.of_equiv S (e.trans (CFSG.RankThree.Chevalley.adjointQuotientEquiv τ K)).toEquiv
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  rcases hτ with rfl | rfl | rfl | rfl
  · exact three_le_localRank_of_rootWitness_two witnessF4_check witnessF4_orthoCheck
      ![(0 : Fin 4), (0 : Fin 4), (0 : Fin 4), (1 : Fin 4)] (by decide)
  · exact three_le_localRank_of_rootWitness_two witnessE6_check witnessE6_orthoCheck
      ![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] (by decide)
  · exact three_le_localRank_of_rootWitness_two witnessE7_check witnessE7_orthoCheck
      ![(5 : Fin 7), (3 : Fin 7), (0 : Fin 7), (3 : Fin 7)] (by decide)
  · exact three_le_localRank_of_rootWitness_two witnessE8_check witnessE8_orthoCheck
      ![(6 : Fin 8), (4 : Fin 8), (1 : Fin 8), (3 : Fin 8)] (by decide)

theorem three_le_localRank_of_twistedE6Model_two {S : Type} [Group S] [Finite S] {f : ℕ}
    (hf : 1 ≤ f) (h : TwistedChevalleyModel S .E6 (2 ^ f)) : 3 ≤ localRank 3 S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, _, σ, hK, hσ, hσc, hfr, ⟨u, hu⟩, ⟨e⟩⟩ := twistedModel_data hf h
  have hσ2 : ∀ c, σ (σ c) = c := fun c => by
    rw [hσc, hσc, ← pow_mul, show 2 ^ f * 2 ^ f = Nat.card K by
      rw [hK]; change _ = 2 ^ (f * 2); ring, hfr]
  set W := witnessE6'
  set Γ := twistFixed .E6 K σ
  let e' : S ≃* commutator Γ ⧸ Subgroup.center (commutator Γ) :=
    e.trans (derivedCentralQuotientEquiv _ (twistedFixedGroupEquiv .E6 K σ))
  have : Finite (commutator Γ ⧸ Subgroup.center (commutator Γ)) := Finite.of_equiv S e'.toEquiv
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e' Nat.prime_three]
  obtain ⟨hf4, hZA, hZZ⟩ := W.charTwo_facts witnessE6'_check witnessE6'_orthoCheck
    ![(1 : Fin 6), (0 : Fin 6), (2 : Fin 6), (2 : Fin 6)] (by decide) (K := K)
  have hW := witnessE6'_check
  have hO := witnessE6'_orthoCheck
  simp only [RootWitness.check, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hW
  simp only [RootWitness.orthoCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hO
  have hpos : ∀ i, 0 < height (W.root i).1 := fun i => by
    rw [RootWitness.root_val]; exact (hW i).1.1.1
  have hU := e6_U_le_twistDerived hσ hσ2 hu
  have hAΓ' : ∀ i, W.elemA K i ∈ twistDerived .E6 K σ := fun i => by
    rw [RootWitness.elemA_eq_charTwo]
    refine hU _ (RootGroupData.X_le_U (D := nativeData TwistTag.E6.tag K) (hpos i)
      ((rootOperatorFamily _).eltElement_mem_rootSubgroup _ _)) ?_
    exact twistC_eltElement_one_charTwo σ (witnessE6_rootTwist i)
  have hBΓ' : ∀ i, W.elemB K i ∈ twistDerived .E6 K σ := fun i => by
    set s := (coxeterSystem TwistTag.E6.tag).wordProd (W.sepWord i)
    have hs : s ∈ relWeylTwist .E6 := (mem_relWeylTwist _).2
      (weylTwist_wordProd_eq (t := .E6) (ω := W.sepWord i) (witnessE6_sepWord_fixed i))
    have hn := nrep_mem_twistFixed .E6 K σ hσ hs
    have hflip : s • W.root i = -W.root i := Subtype.ext (by
      rw [coe_smul_root, RootWitness.root_val, wordProd_smul, coe_neg_root,
        RootWitness.root_val]
      exact (hO i).1)
    have hconj : (nrep TwistTag.E6.tag K s)⁻¹ * W.elemA K i * (nrep TwistTag.E6.tag K s)⁻¹⁻¹ =
        W.elemB K i := by
      rw [RootWitness.elemA_eq_charTwo, RootWitness.elemB_eq_charTwo, inv_inv]
      have h := nrep_conj_eltElement_charTwo (K := K) s (-W.root i) 1
      rw [smul_neg_root, hflip, neg_neg] at h
      rw [← h]
      group
    rw [← hconj]
    exact conj_mem_twistDerived (Γ.inv_mem hn) (hAΓ' i)
  have hZΓ' : ∀ i, W.elemZ K i ∈ twistDerived .E6 K σ := fun i => by
    rw [RootWitness.elemZ_eq]
    exact (twistDerived .E6 K σ).mul_mem (hAΓ' i) (hBΓ' i)
  choose a ha haeq using hAΓ'
  choose z hz hzeq using hZΓ'
  let A' : Fin 4 → commutator Γ := fun i => ⟨a i, ha i⟩
  let Z' : Fin 4 → commutator Γ := fun i => ⟨z i, hz i⟩
  have hcoeA : ∀ i, ((A' i : Γ) : adjointGroup TwistTag.E6.tag K) = W.elemA K i := haeq
  have hcoeZ : ∀ i, ((Z' i : Γ) : adjointGroup TwistTag.E6.tag K) = W.elemZ K i := hzeq
  have hinj : Function.Injective
      fun g : commutator Γ => ((g : Γ) : adjointGroup TwistTag.E6.tag K) :=
    fun x y h => Subtype.ext (Subtype.ext h)
  have hcomm : ∀ x y : commutator Γ, Commute x y ↔
      Commute ((x : Γ) : adjointGroup TwistTag.E6.tag K)
        ((y : Γ) : adjointGroup TwistTag.E6.tag K) :=
    fun x y => ⟨fun h => h.map ((Γ.subtype).comp (commutator Γ).subtype),
      fun h => Subtype.ext (Subtype.ext h.eq)⟩
  have hpow : ∀ (x : commutator Γ) (m : ℕ),
      ((x ^ m : commutator Γ) : Γ).1 = ((x : Γ) : adjointGroup TwistTag.E6.tag K) ^ m :=
    fun x m => by simp
  have h11 : (1 : K) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharP.cast_eq_zero K 2
  have hA2 : W.elemA K (Fin.last 3) ^ 2 = 1 := by
    rw [RootWitness.elemA, conj_pow, sq, ← (rootOperatorFamily _).eltElement_add, h11,
      (rootOperatorFamily _).eltElement_zero, mul_one, mul_inv_cancel]
  have ht : A' (Fin.last 3) ^ 2 = 1 := hinj (by
    change ((A' (Fin.last 3) ^ 2 : commutator Γ) : Γ).1 = ((1 : commutator Γ) : Γ).1
    rw [hpow, hcoeA]
    exact hA2)
  have htc : A' (Fin.last 3) ∉ Subgroup.center (commutator Γ) := fun hc =>
    (hf4 (Fin.last 3)).2.1 (by
      rw [← hcoeZ, ← hcoeA]
      exact (hcomm _ _).1 (Subgroup.mem_center_iff.1 hc (Z' (Fin.last 3))))
  refine le_localRank_three_center_quotient (fun i : Fin 3 => Z' i.castSucc)
    (fun i : Fin 3 => A' i.castSucc) (fun i => hinj ?_) (fun i h => ?_) (fun i h => ?_)
    (fun i j hij => ?_) (fun i j hij => ?_) ht htc (fun i => ?_)
  · change ((Z' i.castSucc ^ 3 : commutator Γ) : Γ).1 = ((1 : commutator Γ) : Γ).1
    rw [hpow, hcoeZ]
    exact (hf4 i.castSucc).1
  · exact (hf4 i.castSucc).2.1 (by rw [← hcoeZ, ← hcoeA]; exact (hcomm _ _).1 h)
  · refine (hf4 i.castSucc).2.2 ?_
    have := (hcomm _ _).1 h
    rw [hpow, hcoeZ, hcoeA] at this
    exact this
  · exact (hcomm _ _).2 (by
      rw [hcoeZ, hcoeA]
      exact hZA _ _ fun h => hij (Fin.castSucc_injective _ h))
  · exact (hcomm _ _).2 (by
      rw [hcoeZ, hcoeZ]
      exact hZZ _ _ fun h => hij (Fin.castSucc_injective _ h))
  · exact (hcomm _ _).2 (by
      rw [hcoeZ, hcoeA]
      exact hZA _ _ (Fin.castSucc_lt_last i).ne')

end CFSG.SectionRank.QTK

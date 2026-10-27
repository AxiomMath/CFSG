module

public import CFSG.LieType.Chevalley.CharTwoRank

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.SectionRank

section CharTwo

variable {τ : Tag} {K : Type} [Field K] [CharP K 2]

theorem eq_one_of_sign_charTwo {ε : K} (hε : ε = 1 ∨ ε = -1) : ε = 1 := by
  rcases hε with h | h
  · exact h
  · rw [h, CharTwo.neg_eq]

theorem nrep_conj_eltElement_charTwo
    (w : WeylGroup τ) (α : Root τ) (c : K) :
    nrep τ K w * (rootOperatorFamily τ).eltElement α c * (nrep τ K w)⁻¹ =
      (rootOperatorFamily τ).eltElement (w • α) c := by
  obtain ⟨ε, hε, h⟩ := exists_conj_nrep (K := K) w α
  rw [h c, eq_one_of_sign_charTwo hε, one_mul]

theorem RootWitness.elemA_eq_charTwo
    {n : ℕ} (W : RootWitness τ n) (i : Fin n) :
    W.elemA K i = (rootOperatorFamily τ).eltElement (W.root i) 1 := by
  rw [RootWitness.elemA, nrep_conj_eltElement_charTwo, ← W.root_eq_smul i]

theorem RootWitness.elemB_eq_charTwo
    {n : ℕ} (W : RootWitness τ n) (i : Fin n) :
    W.elemB K i = (rootOperatorFamily τ).eltElement (-W.root i) 1 := by
  rw [RootWitness.elemB, nrep_conj_eltElement_charTwo, smul_neg_root, ← W.root_eq_smul i]

theorem twistC_eltElement_one_charTwo
    {t : TwistTag} (σ : K →+* K) {α : Root t.tag}
    (hα : rootTwist t α = α) :
    twistC t K σ ((rootOperatorFamily t.tag).eltElement α 1) =
      (rootOperatorFamily t.tag).eltElement α 1 := by
  obtain ⟨ε, hε, h⟩ := (rootOperatorFamily t.tag).exists_twistC_eltElement t K σ α
  rw [h 1, hα, map_one, mul_one]
  have : ((ε : ℤ) : K) = 1 := by
    rcases hε with rfl | rfl
    · simp
    · push_cast
      exact CharTwo.neg_eq 1
  rw [this]

end CharTwo

noncomputable abbrev witnessE6'
    : RootWitness TwistTag.E6.tag 4 := witnessE6

theorem witnessE6'_check
    : witnessE6'.check = true := witnessE6_check

theorem witnessE6'_orthoCheck
    : witnessE6'.orthoCheck = true := witnessE6_orthoCheck

theorem witnessE6_vec_fixed_list
    : ∀ i : Fin 4,
    List.ofFn (permLattice TwistTag.E6.perm (witnessE6'.vec i)) = List.ofFn (witnessE6'.vec i) := by
  decide +kernel

theorem witnessE6_vec_fixed
    (i : Fin 4) :
    permLattice TwistTag.E6.perm (witnessE6'.vec i) = witnessE6'.vec i :=
  List.ofFn_injective (witnessE6_vec_fixed_list i)

theorem witnessE6_sepWord_fixed
    : ∀ (i : Fin 4) (k : Fin TwistTag.E6.tag.rank),
    ((witnessE6'.sepWord i).map TwistTag.E6.perm).foldr (reflect TwistTag.E6.tag)
        (Pi.single k 1) =
      (witnessE6'.sepWord i).foldr (reflect TwistTag.E6.tag) (Pi.single k 1) := by
  decide +kernel

theorem witnessE6_rootTwist
    (i : Fin 4) :
    rootTwist .E6 (witnessE6'.root i) = witnessE6'.root i :=
  Subtype.ext (by
    have h := witnessE6_vec_fixed i
    rw [← RootWitness.root_val] at h
    exact h)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem four_le_pRank_three_commutator_center_E6
    (σ : K →+* K) (hσ : Function.Surjective σ)
    (hσ2 : ∀ c, σ (σ c) = c) {u : Kˣ} (hu : (u : K) ^ 2 ≠ 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (commutator (twistFixed .E6 K σ) ⧸
      Subgroup.center (commutator (twistFixed .E6 K σ)))) := by
  set W := witnessE6'
  set Γ := twistFixed .E6 K σ
  obtain ⟨hf, hZA, hZZ⟩ := W.charTwo_facts witnessE6'_check witnessE6'_orthoCheck
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
  refine le_pRank_three_center_quotient Z' A' (fun i => hinj ?_) (fun i h => ?_)
    (fun i h => ?_) (fun i j hij => ?_) (fun i j hij => ?_)
  · change ((Z' i ^ 3 : commutator Γ) : Γ).1 = ((1 : commutator Γ) : Γ).1
    rw [hpow, hcoeZ]
    exact (hf i).1
  · exact (hf i).2.1 (by rw [← hcoeZ, ← hcoeA]; exact (hcomm _ _).1 h)
  · refine (hf i).2.2 ?_
    have := (hcomm _ _).1 h
    rw [hpow, hcoeZ, hcoeA] at this
    exact this
  · exact (hcomm _ _).2 (by rw [hcoeZ, hcoeA]; exact hZA i j hij)
  · exact (hcomm _ _).2 (by rw [hcoeZ, hcoeZ]; exact hZZ i j hij)

end CFSG.LieType.Chevalley

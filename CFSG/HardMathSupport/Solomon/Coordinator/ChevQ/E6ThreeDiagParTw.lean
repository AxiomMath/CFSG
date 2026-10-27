module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagPar
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagParabolicTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootWeight
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.CTP
open scoped Pointwise

section Light

theorem prime_ringChar_and_eq_pow_of_card_sq (K : Type) [Field K] [Finite K] (q : ℕ)
    (hKq : Nat.card K = q ^ 2) (hq2 : 2 ≤ q) :
    (ringChar K).Prime ∧ ∃ f : ℕ, 1 ≤ f ∧ q = ringChar K ^ f := by
  letI : Fintype K := Fintype.ofFinite K
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  have hcard : q ^ 2 = ringChar K ^ (n : ℕ) := by rw [← hKq, Nat.card_eq_fintype_card, hn]
  have hdvd : q ∣ ringChar K ^ (n : ℕ) := hcard ▸ dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  refine ⟨hp, f, ?_, hf⟩
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · rw [h0, pow_zero] at hf
    omega
  · exact h0

theorem exists_radical_pair_of_map_conj {G : Type*} [Group G] {r : ℕ} {C A : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (C : Set G))
    (h : ∃ Q Q' : Subgroup G, Q ≤ C ∧ Q' ≤ C ∧ IsPGroup r Q ∧ IsPGroup r Q' ∧ C ≤ Q ⊔ Q' ∧
      A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (Q : Set G) ∧
      A.map (MulAut.conj x).toMonoidHom ≤ Subgroup.normalizer (Q' : Set G)) :
    ∃ Q Q' : Subgroup G, Q ≤ C ∧ Q' ≤ C ∧ IsPGroup r Q ∧ IsPGroup r Q' ∧ C ≤ Q ⊔ Q' ∧
      A ≤ Subgroup.normalizer (Q : Set G) ∧ A ≤ Subgroup.normalizer (Q' : Set G) := by
  obtain ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, hAQ, hAQ'⟩ := h
  have hCmap : C.map (MulAut.conj x⁻¹).toMonoidHom = C :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := C) (g := x⁻¹)).1 (inv_mem hx)
  have hAA : (A.map (MulAut.conj x).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom = A := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id A using 2
    ext z
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have hQxC : Q.map (MulAut.conj x⁻¹).toMonoidHom ≤ C := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hQC
    rwa [hCmap] at h
  have hQ'xC : Q'.map (MulAut.conj x⁻¹).toMonoidHom ≤ C := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hQ'C
    rwa [hCmap] at h
  have hQxp : IsPGroup r (Q.map (MulAut.conj x⁻¹).toMonoidHom) := IsPGroup.map hQp _
  have hQ'xp : IsPGroup r (Q'.map (MulAut.conj x⁻¹).toMonoidHom) := IsPGroup.map hQ'p _
  have hgen : C ≤ Q.map (MulAut.conj x⁻¹).toMonoidHom ⊔
      Q'.map (MulAut.conj x⁻¹).toMonoidHom := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hCQ
    rwa [Subgroup.map_sup, hCmap] at h
  have hnormQ : A ≤ Subgroup.normalizer
      (Q.map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hAQ
    rwa [hAA, Subgroup.map_equiv_normalizer_eq Q (MulAut.conj x⁻¹)] at h
  have hnormQ' : A ≤ Subgroup.normalizer
      (Q'.map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
    have h := Subgroup.map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hAQ'
    rwa [hAA, Subgroup.map_equiv_normalizer_eq Q' (MulAut.conj x⁻¹)] at h
  exact ⟨Q.map (MulAut.conj x⁻¹).toMonoidHom, Q'.map (MulAut.conj x⁻¹).toMonoidHom,
    hQxC, hQ'xC, hQxp, hQ'xp, hgen, hnormQ, hnormQ'⟩

end Light

section TwCore

theorem exists_radical_pair_of_levi_sup_torus (k : Type) [Field k] [Finite k]
    {r : ℕ} [Fact r.Prime] [CharP k r] (σ : k ≃+* k)
    (hσ : σ ^ TwistTag.E6.order = 1)
    [IsSimpleGroup (graphFixedRootGroup TwistTag.E6 k σ.toRingHom)]
    {J : Set (Fin TwistTag.E6.foldedTag.rank)} (hJ : J ≠ Set.univ)
    {A : Subgroup (ModGL (TwTag k σ hσ) k)}
    (hAL : A ≤ graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ⊔ twistedE6DiagGL k σ) :
    ∃ Q Q' : Subgroup (ModGL (TwTag k σ hσ) k),
      Q ≤ graphFixedRootGroup TwistTag.E6 k σ.toRingHom ∧
      Q' ≤ graphFixedRootGroup TwistTag.E6 k σ.toRingHom ∧ IsPGroup r Q ∧ IsPGroup r Q' ∧
      graphFixedRootGroup TwistTag.E6 k σ.toRingHom ≤ Q ⊔ Q' ∧
      A ≤ Subgroup.normalizer (Q : Set (ModGL (TwTag k σ hσ) k)) ∧
      A ≤ Subgroup.normalizer (Q' : Set (ModGL (TwTag k σ hσ) k)) := by
  have := finite_modGL (τ := TwTag k σ hσ) (K := k)
  have := finite_modGL (τ := TwistTag.E6.tag) (K := k)
  obtain ⟨w₀, δ, hmax, hδδ, hδ, hcomm⟩ := exists_longest_fixed_data TwistTag.E6
  have hw : w₀ ∈ relWeylTwist TwistTag.E6 :=
    mem_relWeylTwist_of_forall_length_le hmax
  obtain ⟨-, hR, hH⟩ := canonical_weyl_root_transport TwistTag.E6.tag k
  set C := graphFixedRootGroup TwistTag.E6 k σ.toRingHom
  have hnC : canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀ ∈ C :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  set n := canonicalRep (coxeterSystem TwistTag.E6.tag) k w₀
  have hpos : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_single TwistTag.E6.tag i), hδ]
  have hneg : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [hR w₀ _ (isRoot_neg_single TwistTag.E6.tag i), smul_neg, hδ, neg_neg]
  have hpos' : ∀ i, (rootSubgroup TwistTag.E6.tag k (Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (-Pi.single (δ i) 1)) n, hneg, hδδ]
  have hneg' : ∀ i, (rootSubgroup TwistTag.E6.tag k (-Pi.single i 1)).map (MulAut.conj
      n⁻¹).toMonoidHom =
      rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1) := fun i => by
    rw [← map_conj_inv_map_conj (rootSubgroup TwistTag.E6.tag k (Pi.single (δ i) 1)) n, hpos, hδδ]
  set J' := (fun i => TwistTag.E6.orbitIndex (δ i)) '' TwistTag.E6.orbitUnion J
  have hJJ' : δ '' TwistTag.E6.orbitUnion J = TwistTag.E6.orbitUnion J' := image_orbitUnion_eq
      hcomm J
  have hJ'J : δ '' TwistTag.E6.orbitUnion J' = TwistTag.E6.orbitUnion J := by
    rw [← hJJ', image_image_of_involutive hδδ]
  have hLn : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J :=
    map_conj_graphFixedParabolicLevi_le hnC (by
      rw [← hJ'J]
      exact map_conj_parabolicLevi_le_of_rootSubgroup (hH w₀) hpos hneg _)
  have hLn' : (graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J).map (MulAut.conj
      n⁻¹).toMonoidHom ≤
      graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J' :=
    map_conj_graphFixedParabolicLevi_le (inv_mem hnC) (by
      rw [← hJJ']
      exact map_conj_parabolicLevi_le_of_rootSubgroup (inv_mem (hH w₀)) hpos' hneg' _)
  set Q := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J
  set Q' := (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J').map (MulAut.conj
      n).toMonoidHom
  obtain ⟨-, -, -, -, -, -, -, -, hQP, hQnorm, hLP, -, -, -, -, -, hfin, hne⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J
  obtain ⟨-, -, -, -, -, -, -, -, hQP', hQnorm', hLP', -, -, -, -, -, hfin', -⟩ :=
    diagram_fixed_parabolic_root_radical_Levi_factors TwistTag.E6 k σ J'
  have hQp : IsPGroup r Q := hfin r
  have hQ'p : IsPGroup r Q' := (hfin' r).map _
  have hQ1 : Q ≠ ⊥ := hne hJ
  have hQC : Q ≤ C := hQP.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J)
  have hQ'C : Q' ≤ C := by
    rintro _ ⟨q, hq, rfl⟩
    exact mul_mem (mul_mem hnC ((hQP'.trans (graphFixedParabolic_le TwistTag.E6 k σ.toRingHom J'))
      hq))
      (inv_mem hnC)
  have hPQ : graphFixedParabolic TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).1 hQnorm
  have hPQ' : graphFixedParabolic TwistTag.E6 k σ.toRingHom J' ≤
      Subgroup.normalizer (graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J' : Set (ModGL
      TwistTag.E6.tag k)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP').1 hQnorm'
  have hLQ : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) := hLP.trans hPQ
  have hLQ' : graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J ≤
      Subgroup.normalizer (Q' : Set (ModGL TwistTag.E6.tag k)) := fun m hm => by
    have h := mem_normalizer_map_conj_inv (n := n⁻¹) (m := m)
      (H := graphFixedParabolicRadical TwistTag.E6 k σ.toRingHom J')
      (hPQ' (hLP' (hLn' (Subgroup.mem_map_of_mem _ hm))))
    rwa [inv_inv] at h
  have hgen : C ≤ Q ⊔ Q' ⊔ graphFixedParabolicLevi TwistTag.E6 k σ.toRingHom J := by
    refine sup_le ((graphFixedPosUnipotent_le_sup σ J).trans
      (sup_le (le_sup_left.trans le_sup_left) le_sup_right)) ?_
    rw [← map_conj_graphFixedPosUnipotent hmax]
    refine (Subgroup.map_mono (graphFixedPosUnipotent_le_sup σ J')).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le (le_sup_right.trans le_sup_left) (hLn.trans le_sup_right)
  have hXC : Q ⊔ Q' ≤ C := sup_le hQC hQ'C
  have hCX : C ≤ Q ⊔ Q' := by
    have hN : C ≤ Subgroup.normalizer ((Q ⊔ Q' : Subgroup (ModGL TwistTag.E6.tag k)) : Set (ModGL
      TwistTag.E6.tag k)) :=
      hgen.trans (sup_le Subgroup.le_normalizer fun m hm =>
        mem_normalizer_sup_of_mem (hLQ hm) (hLQ' hm))
    have : ((Q ⊔ Q').subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hXC).2 hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Q ⊔ Q').subgroupOf C) with h | h
    · exfalso
      apply hQ1
      have hdis := Subgroup.subgroupOf_eq_bot.1 h
      exact eq_bot_iff.2 fun q hq => (Subgroup.disjoint_def.1 hdis)
        (Subgroup.mem_sup_left hq) (hQC hq) ▸ Subgroup.mem_bot.2 rfl
    · exact Subgroup.subgroupOf_eq_top.1 h
  have hAQ : A ≤ Subgroup.normalizer (Q : Set (ModGL TwistTag.E6.tag k)) :=
    hAL.trans (sup_le hLQ (twistedE6DiagGL_le_normalizer_graphFixedParabolicRadical k σ J))
  have hAQ' : A ≤ Subgroup.normalizer (Q' : Set (ModGL TwistTag.E6.tag k)) :=
    hAL.trans (sup_le hLQ' (twistedE6DiagGL_le_normalizer_opposite k σ hw J'))
  exact ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCX, hAQ, hAQ'⟩

theorem exists_radical_pair_twE6Inndiag (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (f : ℕ) (hp : (ringChar K).Prime) (hf : 1 ≤ f)
    (hK3 : ringChar K ≠ 3) (hσq : ∀ c, σ c = c ^ (ringChar K ^ f))
    (hKq : Nat.card K = (ringChar K ^ f) ^ 2)
    (A : Subgroup (ModGL (TwTag K σ hσ) K)) (hAle : A ≤ twistedE6InndiagGL K σ)
    (hAp : IsPGroup 3 A)
    (R : Subgroup (ModGL (TwTag K σ hσ) K)) (hRC : R ≤ twistedE6RootGroup K σ)
    (hRp : IsPGroup (ringChar K) R) (hR1 : R ≠ ⊥)
    (hRn : A ≤ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K))) :
    ∃ Q Q' : Subgroup (ModGL (TwTag K σ hσ) K),
      Q ≤ twistedE6RootGroup K σ ∧ Q' ≤ twistedE6RootGroup K σ ∧
      IsPGroup (ringChar K) Q ∧ IsPGroup (ringChar K) Q' ∧
      (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) ≤ Q ⊔ Q' ∧
      A ≤ Subgroup.normalizer (Q : Set (ModGL (TwTag K σ hσ) K)) ∧
      A ≤ Subgroup.normalizer (Q' : Set (ModGL (TwTag K σ hσ) K)) := by
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := TwTag K σ hσ) (K := K)
  have hcardTw : Nat.card K = (ringChar K ^ f) ^ TwistTag.E6.order := hKq
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 hp hf K hcardTw σ.toRingHom hσq
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  obtain ⟨ψ⟩ := CFSG.LieType.SeitzGeneration.nonempty_derivedCentralQuotient_equiv _ _
    hperf.2.2.1 hZ
  haveI hSimple : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
    (CFSG.LieType.Simplicity.fam_2e6_simplicity
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) (ringChar K) f
      ⟨⟨hp, hf, rfl⟩, K, inferInstance, inferInstance, hcardTw, σ.toRingHom, hσq,
        ⟨ψ.symm⟩⟩).2
  obtain ⟨M, -, ⟨g₁, hg₁, l₁, hl₁, hgl₁⟩, -, F, hF, -, ⟨g₀, hg₀, l₀, hl₀, hl₀1, hgl₀⟩,
      hdom, hsemi⟩ :=
    RootWeightDatum.root_p_subgroup_optimal_parabolic_containment
      (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K)
      (ringChar K) R hRC hRp hR1
  obtain ⟨hJ, -, -, -, -⟩ := hdom g₀ hg₀ l₀ hl₀ hl₀1 hgl₀
  set J₀ : Set (Fin TwistTag.E6.foldedTag.rank) :=
    (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).face l₀ with hJ₀
  have hC0Inn : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ twistedE6InndiagGL K σ :=
    le_sup_left
  have hg₀I : g₀ ∈ twistedE6InndiagGL K σ := hC0Inn hg₀
  have hPh_le : graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ ≤
      twistedE6InndiagGL K σ :=
    sup_le ((graphFixedParabolic_le TwistTag.E6 K σ.toRingHom J₀).trans hC0Inn)
      (twistedE6DiagGL_le_twistedE6InndiagGL K σ)
  have hstabN : ∀ x : ModGL (TwTag K σ hσ) K, x ∈ twistedE6InndiagGL K σ →
      x ∈ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K)) →
      ∀ c : ℝ, (F c).map (x : Module.End K (RootModule (TwTag K σ hσ) K)) = F c := by
    intro x hx hxN c
    obtain ⟨c₀, hc₀, t₀, ht₀, rfl⟩ := mem_twistedE6InndiagGL_decompTw K σ hσ hx
    set s : RootModule (TwTag K σ hσ) K ≃ₗ[K] RootModule (TwTag K σ hσ) K :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (RootModule (TwTag K σ hσ) K) t₀
      with hs_def
    have hs_apply : ∀ v, s v = (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) v :=
      fun v => rfl
    have hs_symm : ∀ v, s.symm v =
        ((t₀⁻¹ : ModGL (TwTag K σ hσ) K) : Module.End K (RootModule (TwTag K σ hσ) K)) v := by
      intro v
      rw [LinearEquiv.symm_apply_eq, hs_apply, ← Module.End.mul_apply, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Module.End.one_eq_id, LinearMap.id_apply]
    have hs_eq : ∀ g : ModGL (TwTag K σ hσ) K, semilinearConjUnit s g = t₀ * g * t₀⁻¹ := by
      intro g
      apply Units.ext
      apply LinearMap.ext
      intro v
      rw [coe_semilinearConjUnit, semilinearConj_apply, hs_symm, hs_apply, Units.val_mul,
        Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hsC : ∀ g : ModGL (TwTag K σ hσ) K,
        semilinearConjUnit s g ∈
            (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group ↔
          g ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).group := by
      intro g
      rw [hs_eq]
      exact (Subgroup.mem_normalizer_iff.1 (twistedE6DiagGL_le_normalizer_C0 K σ ht₀) g).symm
    have hsW : ∀ χ ∈ (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weights,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace χ).map
          s.toLinearMap =
          (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).weightSpace
            ((LinearIsometryEquiv.refl ℝ
              (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).space) χ) := by
      intro χ _
      exact map_weightSpace_eq_of_mem_twistedE6DiagGL K σ hσ ht₀ χ
    have hQ' : ∀ x' : ModGL (TwTag K σ hσ) K, x' ∈ R ↔
        ∃ q ∈ R, c₀ * semilinearConjUnit s q * c₀⁻¹ = x' := by
      intro x'
      simp only [hs_eq]
      constructor
      · intro hx'
        refine ⟨(c₀ * t₀)⁻¹ * x' * (c₀ * t₀), ?_, ?_⟩
        · have h' := (Subgroup.mem_normalizer_iff.1 (inv_mem hxN) x').1 hx'
          rwa [inv_inv] at h'
        · group
      · rintro ⟨q, hq, rfl⟩
        have h' := (Subgroup.mem_normalizer_iff.1 hxN q).1 hq
        have e : c₀ * (t₀ * q * t₀⁻¹) * c₀⁻¹ = c₀ * t₀ * q * (c₀ * t₀)⁻¹ := by group
        rw [e]
        exact h'
    have hcov := hsemi (RingHom.id K) (RingHom.id K) s hsC (LinearIsometryEquiv.refl ℝ _)
      (by simp) hsW c₀ hc₀ R hQ'
    have h1 := hcov.2.2 g₁ hg₁ l₁ hl₁ hgl₁ c
    have h2 := hF g₁ hg₁ l₁ hl₁ hgl₁ c
    have e : (F c).map s.toLinearMap =
        (F c).map (t₀ : Module.End K (RootModule (TwTag K σ hσ) K)) := rfl
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, ← e]
    exact h1.symm.trans h2
  have hstabG : ∀ x ∈ A, g₀⁻¹ * x * g₀ ∈
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    intro x hx
    have hxI := hAle hx
    have hxN := hRn hx
    have hgI : g₀⁻¹ * x * g₀ ∈ twistedE6InndiagGL K σ :=
      mul_mem (mul_mem (inv_mem hg₀I) hxI) hg₀I
    have key : ∀ c : ℝ,
        ((RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c).map
          ((g₀⁻¹ * x * g₀ : ModGL (TwTag K σ hσ) K) :
            Module.End K (RootModule (TwTag K σ hσ) K)) =
        (RootWeightDatum.fixed TwistTag.E6 σ hσ : RootWeightDatum K).filtration l₀ c := by
      intro c
      have h1 := hF g₀ hg₀ l₀ hl₀1 hgl₀ c
      have h2 := hstabN x hxI hxN c
      rw [submodule_map_units_mul, submodule_map_units_mul, h1, h2, ← h1,
        ← submodule_map_units_mul, inv_mul_cancel, Units.val_one, Module.End.one_eq_id,
        Submodule.map_id]
    exact mem_twistedParabolic_sup_torus_of_stab K σ hσ hl₀ hgI key
  have hA0 : A.map (MulAut.conj g₀⁻¹).toMonoidHom ≤
      graphFixedParabolic TwistTag.E6 K σ.toRingHom J₀ ⊔ twistedE6DiagGL K σ := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hstabG x hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h
  have hA0p : IsPGroup 3 (A.map (MulAut.conj g₀⁻¹).toMonoidHom) := hAp.map _
  have hindex := not_three_dvd_index_graphFixed_sup K σ hK3 J₀
  obtain ⟨y, hyPh, hyA⟩ := exists_conj_le_of_not_dvd_index hA0 hA0p hindex
  set A₁ := (A.map (MulAut.conj g₀⁻¹).toMonoidHom).map (MulAut.conj y).toMonoidHom with hA₁
  obtain ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, hAQ, hAQ'⟩ :=
    exists_radical_pair_of_levi_sup_torus (k := K) (r := ringChar K) σ hσ hJ hyA
  have hyC : y * g₀⁻¹ ∈ Subgroup.normalizer
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom : Set (ModGL TwistTag.E6.tag K)) :=
    twistedE6InndiagGL_le_normalizer K σ (mul_mem (hPh_le hyPh) (inv_mem hg₀I))
  have hconjeq : A.map (MulAut.conj (y * g₀⁻¹)).toMonoidHom = A₁ := by
    have hfun : (MulAut.conj (y * g₀⁻¹)).toMonoidHom =
        (MulAut.conj y).toMonoidHom.comp (MulAut.conj g₀⁻¹).toMonoidHom := by
      refine MonoidHom.ext fun z => ?_
      show y * g₀⁻¹ * z * (y * g₀⁻¹)⁻¹ = y * (g₀⁻¹ * z * g₀⁻¹⁻¹) * y⁻¹
      group
    rw [hA₁, Subgroup.map_map, hfun]
  refine exists_radical_pair_of_map_conj (G := ModGL (TwTag K σ hσ) K) (r := ringChar K)
    (C := (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K))) (A := A)
    (x := (y * g₀⁻¹ : ModGL (TwTag K σ hσ) K)) hyC ?_
  exact hconjeq.symm ▸ ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, hAQ, hAQ'⟩

theorem twE6InndiagHyperplaneGeneration_aux (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (hσ : σ ^ TwistTag.E6.order = 1) (f : ℕ) (hp : (ringChar K).Prime) (hf : 1 ≤ f)
    (hK3 : ringChar K ≠ 3) (hσq : ∀ c, σ c = c ^ (ringChar K ^ f))
    (hKq : Nat.card K = (ringChar K ^ f) ^ 2)
    (A : Subgroup (ModGL (TwTag K σ hσ) K)) (hAle : A ≤ twistedE6InndiagGL K σ)
    (hAEA : CFSG.IsElementaryAbelian 3 A) (hA1 : A ≠ ⊥)
    (R : Subgroup (ModGL (TwTag K σ hσ) K)) (hRC : R ≤ twistedE6RootGroup K σ)
    (hRp : IsPGroup (ringChar K) R) (hR1 : R ≠ ⊥)
    (hRn : A ≤ Subgroup.normalizer (R : Set (ModGL (TwTag K σ hσ) K))) :
    (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) ≤
      ⨆ (B : Subgroup (ModGL (TwTag K σ hσ) K)) (_ : B ≤ A) (_ : B.relIndex A = 3),
        (twistedE6RootGroup K σ : Subgroup (ModGL (TwTag K σ hσ) K)) ⊓
          Subgroup.centralizer (B : Set (ModGL (TwTag K σ hσ) K)) := by
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_modGL (τ := TwTag K σ hσ) (K := K)
  haveI := hAEA
  obtain ⟨Q, Q', hQC, hQ'C, hQp, hQ'p, hCQ, hAQ, hAQ'⟩ :=
    exists_radical_pair_twE6Inndiag K σ hσ f hp hf hK3 hσq hKq A hAle
      (IsElementaryAbelian.isPGroup 3 A) R hRC hRp hR1 hRn
  haveI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).2 hA1
  exact hCQ.trans (sup_le
    (le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hK3 hQp) hAQ hQC)
    (le_iSup_hyper_of_coprime (not_dvd_card_of_isPGroup hK3 hQ'p) hAQ' hQ'C))

theorem twE6DiagParCubes_holds : E6ThreeDefs.TwE6DiagParCubes := by
  intro K _ _ σ q hK3 hσq hKq E hEab hcard hEd hnorm
  have hq2 : 2 ≤ q := by
    by_contra h
    have hq : q ≤ 1 := by omega
    have h1 : Nat.card K ≤ 1 := by
      rw [hKq]
      nlinarith [Nat.zero_le q]
    have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨hp, f, hf, rfl⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq hq2
  have hσ : σ ^ TwistTag.E6.order = 1 := by
    have hsq : σ ^ 2 = 1 := by
      refine RingEquiv.ext fun c => ?_
      have hσσ : σ (σ c) = c := by
        haveI := Fintype.ofFinite K
        rw [hσq (σ c), hσq c, ← pow_mul, ← sq, ← hKq, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card c
      simpa only [pow_two, RingAut.mul_apply, RingAut.one_apply] using hσσ
    exact hsq
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP K (ringChar K) := ringChar.charP K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj := twistedE6InndiagConj_injective hp hf hKq σ hσq
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    simp at hcard
  have hEr : E ≤ (twistedE6InndiagConj K σ).range := by
    rw [range_twistedE6InndiagConj]
    exact hEd
  obtain ⟨R, hR1, hRp, hRn⟩ := hnorm
  have hAEA := isElementaryAbelian_matrixPlane (twistedE6InndiagConj K σ) hinj hEab
  have hAD : (E.comap (twistedE6InndiagConj K σ)).map (twistedE6InndiagGL K σ).subtype ≤
      twistedE6InndiagGL K σ := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  refine seitzHyperGamma_eq_top_of_matrix (twistedE6InndiagConj K σ)
    (fun g s => twistedE6InndiagConj_apply g s) hinj E hEr ?_
  exact twE6InndiagHyperplaneGeneration_aux K σ hσ f hp hf hK3 hσq hKq _ hAD hAEA
    (matrixPlane_ne_bot (twistedE6InndiagConj K σ) hEr hE1)
    (R.map (twistedE6RootGroup K σ).subtype) (by rintro _ ⟨s, -, rfl⟩; exact s.2) (hRp.map _)
    (fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R
      (twistedE6RootGroup K σ).subtype_injective).1 h))
    (matrixPlane_le_normalizer (twistedE6InndiagConj K σ)
      (fun g s => twistedE6InndiagConj_apply g s) hRn)

end TwCore

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

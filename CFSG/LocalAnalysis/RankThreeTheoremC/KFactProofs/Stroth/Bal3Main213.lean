module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Lift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

section Reduced

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P : Sylow p X} {z : X} {D : Subgroup X}

theorem RedConfig.eq_of_normalized (h : RedConfig p P z D) (hQ : CFSG.pCore p X = ⊥)
    {K K' : Subgroup X} (hK : IsComponentOf K ⊤) (hK' : IsComponentOf K' ⊤)
    (hn : (P : Subgroup X) ≤ normalizer (K : Set X))
    (hn' : (P : Subgroup X) ≤ normalizer (K' : Set X)) : K' = K := by
  by_contra hne
  have hz := h.mem_component hK hn
  have hz' := h.mem_component hK' hn'
  have hc : ⁅K', K⁆ = ⊥ :=
    ComponentClassification.LocalComponents.commute_of_ne K' K hK' hK hne
  have hKC : K' ≤ centralizer (K : Set X) := commutator_eq_bot_iff_le_centralizer.mp hc
  have hzc : z ∈ centralizer (K : Set X) := hKC hz'
  have hzZ : (⟨z, hz⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    exact mem_centralizer_iff.1 hzc k k.2
  rw [center_eq_bot_of_isComponentOf h.prime h.core hQ hK, mem_bot] at hzZ
  have hz1 : z = 1 := congrArg Subtype.val hzZ
  have := h.ord
  rw [hz1, orderOf_one] at this
  exact h.prime.one_lt.ne this

theorem RedConfig.card_components_le (h : RedConfig p P z D) (S : Finset (Subgroup X))
    (hS : ∀ K ∈ S, IsComponentOf K ⊤) : S.card ≤ 3 := by
  have hA : IsElemAbelian p (⊥ : Subgroup X) :=
    ⟨inferInstance, fun x hx => by rw [mem_bot] at hx; rw [hx, one_pow]⟩
  have := card_add_le_pRank_of_components h.prime h.ne_two h.core S hS hA (a := 0) (by simp)
    (fun K _ => bot_le)
  rw [h.pRank_top] at this
  omega

theorem RedConfig.le_normalizer_component_of_five_le (h : RedConfig p P z D) (hp5 : 5 ≤ p)
    {K : Subgroup X} (hK : IsComponentOf K ⊤) : (P : Subgroup X) ≤ normalizer (K : Set X) :=
  le_normalizer_of_card_components_le h.prime (m := 3) (by omega) h.card_components_le
    P.isPGroup' hK

end Reduced

theorem kFactLemma213_of_inputs (h294 : Input29_4Rank3) (hperm : Bal3NoPermute) :
    KFactLemma213 := by
  intro p hp hodd H _ _ hcat hcon hQ P z D hconf hg hemb
  haveI : Fact p.Prime := ⟨hp⟩
  set O : Subgroup H := primeComplementCore (G := H) p with hOdef
  have hred := Lemma212Config.reduce hodd hconf
  obtain ⟨K, hK⟩ := exists_isComponentOf_of_not_hasPrimeConstraint hp hcon
  have hall : ∀ K' : Subgroup (H ⧸ O), IsComponentOf K' ⊤ →
      ((redSylow P : Sylow p (H ⧸ O)) : Subgroup (H ⧸ O)) ≤ normalizer (K' : Set (H ⧸ O)) := by
    intro K' hK'
    by_cases hp3 : p = 3
    · subst hp3
      rw [coe_redSylow]
      exact hperm H hcat P z D hconf hemb hcon hQ K' hK'
    · exact hred.le_normalizer_component_of_five_le (by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
        omega) hK'
  have huniq : ∀ K' : Subgroup (H ⧸ O), IsComponentOf K' ⊤ → K' = K := fun K' hK' =>
    hred.eq_of_normalized hQ hK hK' (hall K hK) (hall K' hK')
  haveI hKn : K.Normal :=
    Subgroup.Normal.of_conjugate_fixed (fun g => huniq _ (isComponentOf_conj_smul hK g))
  have hZ : center K = ⊥ := center_eq_bot_of_isComponentOf hp hred.core hQ hK
  have hsimple : IsSimpleGroup K := by
    have h1 : IsSimpleGroup (K ⧸ center K) := hK.2.2.2
    have e : (K ⧸ center K) ≃* K := (QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot
    haveI := h1
    exact MulEquiv.isSimpleGroup e.symm
  have hnonab : ∃ a b : K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K hK.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a', b', fun hcomm => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm]
  have hX : CatalogSimpleSections (H ⧸ O) := hcat.quotient _
  have hcatK : IsCatalogGroup K := hX.simple_subgroup K hsimple hnonab
  have hlayer : CFSG.layer (H ⧸ O) = K := by
    refine le_antisymm (?_) ?_
    · rw [CFSG.layer.eq_sSup]
      exact sSup_le fun L hL => (huniq L ((CFSG.isComponent_iff_open L).mp hL)).le
    · rw [CFSG.layer.eq_sSup]
      exact le_sSup ((CFSG.isComponent_iff_open K).mpr hK)
  have hcent : centralizer (K : Set (H ⧸ O)) = ⊥ := by
    have hF : CFSG.fittingSubgroup (H ⧸ O) = ⊥ := by
      rw [CFSG.Fitting_eq_pcore _ p hred.core, hQ]
    have hgf : CFSG.generalizedFitting (H ⧸ O) = K := by
      rw [CFSG.generalizedFitting, hF, hlayer, bot_sup_eq]
    have hle := CFSG.centralizer_generalizedFitting_le (H ⧸ O)
    rw [hgf] at hle
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hle hx
    have hxZ : (⟨x, hxK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      apply Subtype.ext
      exact mem_centralizer_iff.1 hx k k.2
    rw [hZ, mem_bot] at hxZ
    exact mem_bot.2 (congrArg Subtype.val hxZ)
  have hz1 : QuotientGroup.mk' O z ≠ 1 := by
    intro h1
    have := hred.ord
    rw [h1, orderOf_one] at this
    exact hp.one_lt.ne this
  have hgd : ∃ g, IsPlaneDiagonal p (D.map (QuotientGroup.mk' O)) (QuotientGroup.mk' O z) g := by
    obtain ⟨g, hg⟩ := hg
    exact ⟨_, isPlaneDiagonal_map O hg⟩
  have hres := h294 p hp hodd (H ⧸ O) K hsimple hnonab hcatK hcent hred.pRank_top _ _ hred.elem
    hred.card hred.mem hz1 hred.sylow hgd
  exact lift_conclusion hp (elementary_isPGroup p D hconf.elem) hconf.mem hres

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

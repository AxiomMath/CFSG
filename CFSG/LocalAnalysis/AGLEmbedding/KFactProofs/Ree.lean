module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeModel
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeAut
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
import CFSG.LieType.Ree.SmallReeFixedGroupSchreier
import CFSG.LieType.Steinberg.CentralExt.SmallReeThreeCover

public section

namespace CFSG.AGLEmbedding

open CFSG.LieType.Ree

theorem kFactReeOrder :
    KFactReeOrder := by
  intro L _ _ d hd h
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  rw [Nat.card_congr e.toEquiv, (ReeModel.std_facts hK).2.2.2, hfe, mul_right_comm]

theorem kFactReeBorelMaximal :
    KFactReeBorelMaximal := by
  intro L _ _ d hd h U
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, hNU, hco, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have h1 : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      ReeModel.stdB a (GaloisField 3 (2 * a + 1)) := by
    rw [Subgroup.map_equiv_normalizer_eq, he', hP, hNU]
  have h2 : Subgroup.normalizer ((U : Subgroup L) : Set L) =
      (ReeModel.stdB a (GaloisField 3 (2 * a + 1))).comap e'.toMonoidHom := by
    rw [← h1, Subgroup.comap_map_eq_self_of_injective e'.injective]
  rw [h2]
  exact (Subgroup.isCoatom_comap e').2 hco

theorem kFactReeOuterSolvable :
    KFactReeOuterSolvable := by
  intro L _ _ d hd h
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have := small_Ree_fixed_group_Schreier a ha (GaloisField 3 (2 * a + 1)) hK
  exact CFSG.ComponentClassification.OuterAutomorphisms.solvable_of_equiv e.symm


theorem kFactReeSchur :
    KFactReeSchur := by
  intro K _ _ d hd hq h3 h
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have : Group.IsPerfect K := ⟨hq.1⟩
  set η : K →* ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)) with hη
  have hker : η.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, hη, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hη' : Function.Surjective η :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have := CFSG.LieType.Steinberg.CentralExt.SmallReeClosed.smallRee_three_cover_trivial hK ha η
    hη' hker.le (by rw [hker]; exact h3)
  rwa [hker] at this

theorem kFactReeSylowCenterTorus :
    KFactReeSylowCenterTorus := by
  intro L _ _ d hd h U
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :=
    he'.trans hP
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :
        Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  rw [hfe]
  refine ⟨(e'.symm : _ →* L).comp (ReeModel.zHom hK), e'.symm.injective.comp
    (ReeModel.zHom_injective hK), ?_, fun μ => ?_⟩
  · ext x
    rw [ReeModel.mem_range_comp_symm, ReeModel.zHom_range hK, Subgroup.mem_inf, Subgroup.mem_inf,
      ← hU, ReeModel.mem_map_iff, ReeModel.mem_centralizer_map_iff]
  · obtain ⟨g, hg, hgc⟩ := ReeModel.exists_normalizer_mul hK μ
    refine ⟨e'.symm g, ?_, fun c => ?_⟩
    · rw [← hN] at hg
      exact (Subgroup.mem_map_equiv.1 hg)
    · have := congrArg e'.symm (hgc c)
      simpa using this


theorem kFactReeInvolution :
    KFactReeInvolution := by
  intro L _ _ d hd h U
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :=
    he'.trans hP
  have hN : (Subgroup.normalizer ((U : Subgroup L) : Set L)).map e'.toMonoidHom =
      Subgroup.normalizer ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :
        Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) : Set _) := by
    rw [Subgroup.map_equiv_normalizer_eq, hU]
  have hmemN : ∀ x : L, x ∈ Subgroup.normalizer ((U : Subgroup L) : Set L) ↔
      e' x ∈ Subgroup.normalizer ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :
        Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) : Set _) := fun x => by
    rw [← hN, ReeModel.mem_map_iff]
  have hC : ((U : Subgroup L) ⊓ Subgroup.centralizer ({e'.symm (ReeModel.jElt hK)} : Set L)).map
      e'.toMonoidHom = (ReeModel.xHom hK).range := by
    ext y
    rw [ReeModel.xHom_range hK, Subgroup.mem_inf]
    obtain ⟨x, rfl⟩ := e'.surjective y
    rw [ReeModel.mem_map_iff, Subgroup.mem_inf, ← hU, ReeModel.mem_map_iff]
    refine and_congr_right fun _ => ?_
    have := ReeModel.mem_centralizer_image_iff e' {e'.symm (ReeModel.jElt hK)} x
    rw [Set.image_singleton, MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨e'.symm (ReeModel.jElt hK), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmemN, MulEquiv.apply_symm_apply]
    exact ReeModel.jElt_mem_normalizer hK
  · rw [MulEquiv.orderOf_eq]
    exact ReeModel.orderOf_jElt hK
  · intro t ht ht2
    rw [hmemN] at ht
    obtain ⟨u₀, hu₀, hu⟩ := ReeModel.involution_conj_std hK (e' t) ht
      (by rw [MulEquiv.orderOf_eq]; exact ht2)
    refine ⟨e'.symm u₀, ?_, ?_⟩
    · rw [← hU] at hu₀
      obtain ⟨u, hu', rfl⟩ := hu₀
      have h1 : e'.symm (e'.toMonoidHom u) = u := e'.symm_apply_apply u
      rw [h1]
      exact hu'
    · apply e'.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      exact hu
  · rw [← ReeModel.isElemAbelian_map_iff e', hC]
    exact ReeModel.isElemAbelian_xHom_range hK
  · rw [← Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hC, hfe]
    exact ReeModel.card_xHom_range hK
  · intro hle
    refine ReeModel.not_centralizer_le_normalizer hK fun z hz => ?_
    have hz' : e'.symm z ∈ Subgroup.centralizer ({e'.symm (ReeModel.jElt hK)} : Set L) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      rw [← map_mul, hz, map_mul]
    have := (hmemN _).1 (hle hz')
    rwa [MulEquiv.apply_symm_apply] at this


theorem kFactReeSylowNormalizerSolvable :
    KFactReeSylowNormalizerSolvable := by
  intro L _ _ d hd h U A hA
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :=
    he'.trans hP
  have hO := small_Ree_fixed_group_Schreier a ha (GaloisField 3 (2 * a + 1)) hK
  have hB : Group.IsSolvable ↥(Subgroup.normalizer ((ReeModel.stdU a
      (GaloisField 3 (2 * a + 1)) : Subgroup ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1))
        a)) : Set ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a))) := by
    rw [hNU]
    exact ReeModel.isSolvable_stdB
  set f : MulAut L →* MulAut ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) :=
    (MulAut.congr e').toMonoidHom with hf
  have hinj : Function.Injective f := (MulAut.congr e').injective
  have hsolv := ReeModel.isSolvable_of_stabilizer _ hB hO (A.map f) (by
    rintro _ ⟨α, hα, rfl⟩
    have hcomm : (f α).toMonoidHom.comp e'.toMonoidHom = e'.toMonoidHom.comp α.toMonoidHom := by
      ext x
      simp [hf, MulAut.congr_apply]
    rw [← hU, Subgroup.map_map, hcomm, ← Subgroup.map_map, hA α hα])
  exact Group.isSolvable_of_isSolvable_injective
    (f := (A.equivMapOfInjective f hinj).toMonoidHom) (A.equivMapOfInjective f hinj).injective


theorem kFactReeAutPCard :
    KFactReeAutPCard := by
  intro L _ _ d hd h S hS
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : Nat.card (MulAut L) ∣
      Nat.card ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) * (2 * a + 1) := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact ReeModel.card_mulAut_dvd ha hK
  have h3 := (Subgroup.card_subgroup_dvd_card S).trans hA
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  rw [(ReeModel.std_facts hK).2.2.2, hk] at h3
  rw [hk, hfe]
  set q : ℕ := 3 ^ (2 * a + 1) with hq
  have hq3 : q ^ 3 = 3 ^ (3 * (2 * a + 1)) := by rw [hq, ← pow_mul, mul_comm]
  have h3q : 3 ∣ q := dvd_pow_self 3 (by omega)
  have hcop : Nat.Coprime (3 ^ k) ((q - 1) * (q ^ 3 + 1)) := by
    refine Nat.Coprime.pow_left _ ?_
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      have : 1 ≤ q := Nat.one_le_pow _ _ (by norm_num)
      omega
    · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      rw [Nat.dvd_add_right (dvd_pow h3q (by norm_num))]
      omega
  have e1 : q ^ 3 * (q - 1) * (q ^ 3 + 1) * (2 * a + 1) =
      (q ^ 3 * (2 * a + 1)) * ((q - 1) * (q ^ 3 + 1)) := by ring
  rw [e1] at h3
  rw [← hq3]
  exact hcop.dvd_of_dvd_mul_right h3


theorem kFactReeCenterCentralizer :
    KFactReeCenterCentralizer := by
  intro L _ _ d hd h U α hα
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  obtain ⟨⟨P, hP⟩, hNU, -, -⟩ := ReeModel.std_facts hK
  obtain ⟨e', he'⟩ := ReeModel.exists_equiv_map_eq e U P
  have hU : (U : Subgroup L).map e'.toMonoidHom = ReeModel.stdU a (GaloisField 3 (2 * a + 1)) :=
    he'.trans hP
  have hmem : ∀ x : L, x ∈ (U : Subgroup L) ⊓ Subgroup.centralizer ((U : Subgroup L) : Set L) ↔
      e' x ∈ ReeModel.stdU a (GaloisField 3 (2 * a + 1)) ⊓ Subgroup.centralizer
        ((ReeModel.stdU a (GaloisField 3 (2 * a + 1)) : Subgroup
          ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a)) : Set _) := fun x => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← hU, ReeModel.mem_map_iff,
      ReeModel.mem_centralizer_map_iff]
  have hcongr : ∀ y, (MulAut.congr e' α) y = e' (α (e'.symm y)) := fun y => rfl
  obtain ⟨u, hu, hαu⟩ := ReeModel.eq_conj_of_fixes_center ha hK (MulAut.congr e' α) (by
    intro z hz
    have h1 := hα (e'.symm z) ((hmem _).2 (by rwa [MulEquiv.apply_symm_apply]))
    rw [hcongr, h1, MulEquiv.apply_symm_apply])
  refine ⟨e'.symm u, ?_, ?_⟩
  · rw [← hU] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    have h1 : e'.symm (e'.toMonoidHom x) = x := e'.symm_apply_apply x
    rw [h1]
    exact hx
  · ext x
    have h1 := congrArg (fun β : MulAut ↥(ReeTag.G2.reeGamma (GaloisField 3 (2 * a + 1)) a) =>
      β (e' x)) hαu
    simp only [hcongr, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    have h2 := congrArg e'.symm h1
    rw [MulEquiv.symm_apply_apply] at h2
    rw [h2]
    simp [MulAut.conj_apply, map_mul, map_inv]


theorem kFactReeAutElemRank :
    KFactReeAutElemRank := by
  intro L _ _ d hd h E hE
  obtain ⟨a, ha, hfe, ⟨e⟩⟩ := ReeModel.exists_equiv_reeGamma hd h
  have hK : Nat.card (GaloisField 3 (2 * a + 1)) = 3 ^ (2 * a + 1) :=
    GaloisField.card 3 (2 * a + 1) (by omega)
  have hKR3 := kFactReeCenterCentralizer
  have := ReeModel.card_le_of_elemAbelian ha hK e (fun T α hα => hKR3 L d hd h T α hα) E hE
  rw [hfe, mul_comm, pow_mul]
  exact this

end CFSG.AGLEmbedding

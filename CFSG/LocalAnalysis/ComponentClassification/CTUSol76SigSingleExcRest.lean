module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExcOrbit
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleExc
public import CFSG.LieType.Chevalley.FixedRootCentralizerGeneration

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem orderOf_conj_eq_two {G : Type*} [Group G] (hZ : center G = ⊥) {c : G}
    (hc : orderOf c = 2) : orderOf (MulAut.conj c) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one]
  · intro h1
    have hcZ : c ∈ center G := by
      rw [mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut G => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * c = c * g * c⁻¹ * c := by rw [this]
        _ = c * g := by group
    rw [hZ, mem_bot] at hcZ
    rw [hcZ, orderOf_one] at hc
    exact absurd hc (by norm_num)

theorem ringEquiv_pow_eq_one_of_frobenius {K : Type} [Field K] [Finite K] {q m : ℕ}
    (hK : Nat.card K = q ^ m) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ q) : σ ^ m = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ n : ℕ, ∀ c, (σ ^ n) c = c ^ (q ^ n) := by
    intro n
    induction n with
    | zero => intro c; rw [pow_zero, pow_zero, pow_one, RingAut.one_apply]
    | succ n ih =>
      intro c
      rw [pow_succ σ n, RingAut.mul_apply, ih, hσ, ← pow_mul, ← pow_succ']
  exact RingEquiv.ext fun c => by
    rw [hpow, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card, RingAut.one_apply]

theorem centralizerGenerationAt_graphFixedRootGroup
    (t : TwistTag) (K : Type) [Field K] [Finite K] (hK2 : ringChar K ≠ 2) (σ : K ≃+* K)
    (hσ : σ ^ t.order = 1) [IsSimpleGroup (graphFixedRootGroup t K σ.toRingHom)] :
    CentralizerGenerationAt (ringChar K) (graphFixedRootGroup t K σ.toRingHom) := by
  intro A R hA hAc hRp hR1 hAR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 A := hA
  have : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  have hι : Function.Injective (graphFixedRootGroup t K σ.toRingHom).subtype :=
    (graphFixedRootGroup t K σ.toRingHom).subtype_injective
  have : CFSG.IsElementaryAbelian 2 (A.map (graphFixedRootGroup t K σ.toRingHom).subtype) :=
    CFSG.IsElementaryAbelian.map _
  have hgen := fixed_root_invariant_prime_subgroup_centralizer_generation t K (ringChar K) 2
    hK2 σ hσ (A.map (graphFixedRootGroup t K σ.toRingHom).subtype) (map_subtype_le A)
    (by rwa [card_map_of_injective hι]) (R.map (graphFixedRootGroup t K σ.toRingHom).subtype)
    (map_subtype_le R) (hRp.map _) (by rwa [Ne, map_eq_bot_iff_of_injective _ hι])
    ((map_mono hAR).trans (le_normalizer_map _))
  have hS : (⊤ : Subgroup (graphFixedRootGroup t K σ.toRingHom)).map
      (graphFixedRootGroup t K σ.toRingHom).subtype ≤
      (⨆ a ∈ A, ⨆ (_ : a ≠ 1), centralizer ({a} : Set (graphFixedRootGroup t K σ.toRingHom))).map
        (graphFixedRootGroup t K σ.toRingHom).subtype := by
    have h1 : (⊤ : Subgroup (graphFixedRootGroup t K σ.toRingHom)).map
        (graphFixedRootGroup t K σ.toRingHom).subtype = graphFixedRootGroup t K σ.toRingHom := by
      rw [← MonoidHom.range_eq_map, range_subtype]
    rw [h1]
    refine le_trans hgen.symm.le ?_
    refine iSup₂_le fun a' ha' => iSup_le fun ha'1 => ?_
    obtain ⟨a, ha, rfl⟩ := mem_map.1 ha'
    have ha1 : a ≠ 1 := fun h1 => ha'1 (by rw [h1, map_one])
    have hC : graphFixedRootGroup t K σ.toRingHom ⊓
        centralizer ({(graphFixedRootGroup t K σ.toRingHom).subtype a} : Set (ModGL t.tag K)) =
        (centralizer ({a} : Set (graphFixedRootGroup t K σ.toRingHom))).map
          (graphFixedRootGroup t K σ.toRingHom).subtype := by
      rw [map_centralizer_singleton_of_injective hι, range_subtype]
    rw [hC]
    exact map_mono (le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl))
  exact eq_top_iff.2 ((map_le_map_iff_of_injective hι).1 hS)

theorem singleComponentCleanAt_E7 :
    SingleComponentCleanAt (fun S _ => ∃ p f : ℕ, p ≠ 2 ∧ ChevalleyExceptionalModel S .E7 p f) := by
  refine singleComponentCleanAt_of_bigComponentUniqueAt fun T _ _ hT ⟨p, f, hp2, hm⟩ => ?_
  obtain ⟨⟨hp, hf, -⟩, hmod⟩ := hm
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ : UntwistedChevalleyModel T .E7 (p ^ f) := hmod
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (ModGL .E7 K) := finite_modGL
  let e' : T ≃* adjointGroup .E7 K := e.trans (RankThree.Chevalley.adjointQuotientEquiv .E7 K)
  have : IsSimpleGroup (adjointGroup .E7 K) := e'.symm.isSimpleGroup
  refine ⟨p, hp, bigComponentUniqueAt_of_mulEquiv e' (bigComponentUniqueAt_of_grp fun c hc => ?_),
    ?_⟩
  · obtain ⟨hαg, hαo⟩ := conj_innerDiag center_adjointGroup_eq_bot hc
    exact bigCompUniqueGrp_of_mulEquiv
      (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizer c).symm)
      (bigCompUniqueGrp_E7_innerDiag hp hp2 hK (MulAut.conj c) c 1 hαg hαo)
  · have := centralizerGenerationAt_of_mulEquiv e' (centralizerGenerationAt_adjointGroup .E7 K hK2)
    rwa [ringChar.eq K p] at this

theorem singleComponentCleanAt_twisted
    (t : StatedLieTag) (ht : t = .twistedE6 ∨ t = .trialityD4) :
    SingleComponentCleanAt (fun S _ => ∃ p f : ℕ, p ≠ 2 ∧ ChevalleyExceptionalModel S t p f) := by
  refine singleComponentCleanAt_of_bigComponentUniqueAt fun T _ _ hT ⟨p, f, hp2, hm⟩ => ?_
  have hadm : StatedLieAdmissible t 0 p f := hm.1
  obtain ⟨hp, hf, -⟩ := hm.1
  have htag : t ∈ chevalleyExceptionalTags := by
    rcases ht with rfl | rfl <;> decide
  have hLie : LieModel T t 0 p f := Or.inr (Or.inl ⟨rfl, htag, hm⟩)
  obtain ⟨tw, hmodel⟩ : ∃ tw : TwistTag, TwistedChevalleyModel T tw (p ^ f) := by
    rcases ht with rfl | rfl
    · exact ⟨.E6, hm.2⟩
    · exact ⟨.D4, hm.2⟩
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card tw hp hf hmodel
  have hσ1 : σ ^ tw.order = 1 := ringEquiv_pow_eq_one_of_frobenius hK σ hσ
  have hord : 1 ≤ tw.order := by cases tw <;> decide
  have : CharP K p := finite_field_prime_power_characteristic hp (Nat.mul_le_mul hf hord)
    (by rw [hK, ← pow_mul])
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : IsSimpleGroup (graphFixedRootGroup tw K σ.toRingHom) := e.symm.isSimpleGroup
  have hZ : center T = ⊥ := by
    have h := map_center_eq e
    rw [exceptional_fixed_center_trivial tw K σ] at h
    exact (map_eq_bot_iff_of_injective _ e.injective).1 h
  refine ⟨p, hp, bigComponentUniqueAt_of_grp fun c hc => ?_, ?_⟩
  · have hαo := orderOf_conj_eq_two hZ hc
    have hαi : MulAut.conj c ∈ (MulAut.conj : T →* MulAut T).range := ⟨c, rfl⟩
    refine bigCompUniqueGrp_of_mulEquiv
      (MulEquiv.subgroupCongr (fixedSubgroup_conj_eq_centralizer c).symm) ?_
    rcases ht with rfl | rfl
    · exact bigCompUniqueGrp_twistedE6_inner T p f hp hp2 hadm hLie _ hαo hαi
    · exact bigCompUniqueGrp_triality_inner T p f hp hp2 hadm hLie _ hαo hαi
  · have := centralizerGenerationAt_of_mulEquiv e
      (centralizerGenerationAt_graphFixedRootGroup tw K hK2 σ hσ1)
    rwa [ringChar.eq K p] at this

theorem singleComponentCleanAt_oddExcRest :
    SingleComponentCleanAt (fun S _ => OddExcRestRep S) := by
  intro T _ _ hT ⟨t, p, f, hp2, ht, hm⟩
  rcases ht with rfl | rfl | rfl
  · exact singleComponentCleanAt_E7 T hT ⟨p, f, hp2, hm⟩
  · exact singleComponentCleanAt_twisted _ (Or.inl rfl) T hT ⟨p, f, hp2, hm⟩
  · exact singleComponentCleanAt_twisted _ (Or.inr rfl) T hT ⟨p, f, hp2, hm⟩

theorem singleComponentCleanAt_oddExceptional :
    SingleComponentCleanAt (fun S _ => OddExceptionalRep S) :=
  singleComponentCleanAt_oddExceptional_of_rest singleComponentCleanAt_oddExcRest

end CFSG.ComponentClassification.Sol76.Sig

module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisA3
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisB2
public import CFSG.Quasithin.Background.A1aFStar

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.Quasithin.HSType

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_eq_of {X P : Subgroup G} (hPX : P ≤ X) (hn : (P.subgroupOf X).Normal)
    (hp : IsPGroup 2 P)
    (hmax : ∀ K : Subgroup ↥X, K.Normal → IsPGroup 2 K → K ≤ P.subgroupOf X) :
    CFSG.Open.pCoreOf 2 X = P := by
  have h1 : CFSG.Open.pCore 2 ↥X = P.subgroupOf X := by
    rw [CFSG.pCore_eq_iSup]
    apply le_antisymm
    · exact iSup_le fun K => iSup_le fun hK => iSup_le fun hK2 => hmax K hK hK2
    · exact le_iSup₂_of_le (P.subgroupOf X) hn
        (le_iSup_of_le (hp.comap_of_injective X.subtype X.subtype_injective) le_rfl)
  rw [CFSG.Open.pCoreOf, h1, subgroupOf_map_subtype, inf_of_le_left hPX]

namespace GHSylow

variable (D : GHSylow G)

theorem piM_mem_toMb_E_iff (hOM : pPrimeCore 2 ↥D.M = ⊥) (m : ↥D.M) :
    D.piM m ∈ D.toMb.E ↔ (m : G) ∈ D.E := by
  constructor
  · rintro ⟨e, he, heq⟩
    have h := D.piM_injective hOM (a₁ := ⟨D.toG e, D.S_le_M (D.toG_mem e)⟩) (a₂ := m) heq
    rw [← h]
    exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, hem⟩
    refine ⟨e, he, ?_⟩
    rw [D.toMb_toG]
    congr 1
    exact Subtype.ext hem


theorem exists_S5_M (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hA : ¬ D.caseB) :
    ∃ φ : ↥D.M →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
      φ.ker = D.E.subgroupOf D.M ∧ CFSG.Open.pCoreOf 2 D.M = D.E := by
  obtain ⟨φ, hφ, hker, hmax⟩ := D.toMb.exists_S5_A hC D.pPrimeCore_Mb D.z_comm_Mb hA
  have hEM : D.E ≤ D.M := D.E_le_S.trans D.S_le_M
  refine ⟨φ.comp D.piM, hφ.comp (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · ext m
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      D.piM_mem_toMb_E_iff hOM, mem_subgroupOf]
  · refine pCoreOf_eq_of hEM ⟨fun e he g => ?_⟩ (D.S.isPGroup'.to_le D.E_le_S)
      fun K hK hK2 => fun k hk => ?_
    · rw [mem_subgroupOf] at he ⊢
      have h := D.conj_mem_E_of_OM hC hOM (inv_mem g.2) he
      rwa [inv_inv] at h
    · have hKn : (K.map D.piM).Normal := hK.map _ (QuotientGroup.mk'_surjective _)
      have h := hmax (K.map D.piM) hKn (hK2.map _) ⟨k, hk, rfl⟩
      exact mem_subgroupOf.mpr ((D.piM_mem_toMb_E_iff hOM k).mp h)

theorem centralizer_E_le_A (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hA : ¬ D.caseB) : D.M ⊓ centralizer (D.E : Set G) ≤ D.E := by
  obtain ⟨-, hCE, -, -⟩ := D.toMb.prop38A_of hC D.pPrimeCore_Mb D.z_comm_Mb hA
  have hCY := D.toMb.centralizer_E_le_of hCE
  intro g hg
  obtain ⟨hgM, hgE⟩ := mem_inf.mp hg
  refine (D.piM_mem_toMb_E_iff hOM ⟨g, hgM⟩).mp (hCY (mem_centralizer_iff.mpr ?_))
  rintro _ ⟨e, he, rfl⟩
  rw [D.toMb_toG, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_iff.mp hgE _ ⟨e, he, rfl⟩)

theorem hsOne_A (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (hA : ¬ D.caseB) :
    CFSG.Open.quasithinGenFitting D.M = D.E ∧ HSOne D.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker, hpE⟩ := D.exists_S5_M hC hOM hA
  have hF : CFSG.Open.quasithinGenFitting D.M = D.E := by
    rw [(CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff D.M 2).mpr
      (by rw [hpE]; exact D.centralizer_E_le_A hC hOM hA), hpE]
  refine ⟨hF, ⟨?_, φ, hφ, ?_⟩⟩
  · obtain ⟨e⟩ := D.isZ4Q8Q8_E
    exact ⟨(MulEquiv.subgroupCongr hF).trans e⟩
  · change φ.ker = (CFSG.Open.quasithinGenFitting D.M).subgroupOf D.M
    rw [hF, hker]

@[expose] def z4CubeEquiv : Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ≃*
    Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4) :=
  (MulEquiv.prodMultiplicative (G := ZMod 4) (H := ZMod 4 × ZMod 4)).trans
    (MulEquiv.prodCongr (MulEquiv.refl _) (MulEquiv.prodMultiplicative (G := ZMod 4) (H := ZMod 4)))


theorem hsTwo (hC : GorensteinHaradaThmCInput) (hOM : pPrimeCore 2 ↥D.M = ⊥)
    (h10 : D.FusN 1 0) (h20 : D.FusN 2 0)
    (hle : D.V ≤ CFSG.Open.quasithinGenFitting (centralizer ({D.z} : Set G))) :
    HSTwo D.z D.V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ, hθ, hker⟩ := D.exists_GL32_normalizer_V hC hOM h10 h20
  have hQN : D.Q ≤ normalizer (D.V : Set G) :=
    D.centralizer_V_eq_Q hC hOM ▸ centralizer_le_normalizer D.V
  have hpQ : CFSG.Open.pCoreOf 2 (normalizer (D.V : Set G)) = D.Q := by
    refine pCoreOf_eq_of hQN (hker ▸ θ.normal_ker) (D.S.isPGroup'.to_le D.Q_le_S)
      fun K hK hK2 => ?_
    have hKn : (K.map θ).Normal := hK.map θ hθ
    rcases isSimpleGroup_GL32_gh.eq_bot_or_eq_top_of_normal (K.map θ) with hb | ht
    · rw [← hker]
      exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      have hp : IsPGroup 2 (K.map θ) := hK2.map θ
      rw [ht] at hp
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
      rw [card_top, card_GL32_gh] at hk
      have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 168)
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hCQ : normalizer (D.V : Set G) ⊓ centralizer (D.Q : Set G) ≤ D.Q := by
    intro g hg
    rw [← D.centralizer_V_eq_Q hC hOM]
    exact mem_centralizer_iff.mpr fun v hv =>
      mem_centralizer_iff.mp (mem_inf.mp hg).2 v (D.V_le_Q hv)
  have hF : CFSG.Open.quasithinGenFitting (normalizer (D.V : Set G)) = D.Q := by
    rw [(CFSG.Quasithin.quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr (by rw [hpQ]; exact hCQ),
      hpQ]
  refine ⟨hle, ?_, SL32EquivGL32.symm.toMonoidHom.comp θ, ?_, ?_⟩
  · exact ⟨((MulEquiv.subgroupCongr hF).trans
      ((SE.Qsub.equivMapOfInjective D.toG D.toG_injective).symm.trans SE.QsubEquiv)).trans
      z4CubeEquiv⟩
  · exact SL32EquivGL32.symm.surjective.comp hθ
  · rw [hF, ← hker]
    ext n
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]


theorem isTypeHS_A (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hA : ¬ D.caseB) (hOG : pPrimeCore 2 G = ⊥) : CFSG.Quasithin.HSType.IsTypeHS G := by
  have hOM := D.oddCore_M_eq_bot hC hidx hxa hOG
  obtain ⟨h10, h20⟩ := D.fusN_10_20 hC hidx hxa
  obtain ⟨hF, h1⟩ := D.hsOne_A hC hOM hA
  have hle : D.V ≤ CFSG.Open.quasithinGenFitting (centralizer ({D.z} : Set G)) := by
    change D.V ≤ CFSG.Open.quasithinGenFitting D.M
    rw [hF]
    intro v hv
    obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hv
    exact D.toG_mem_E_iff.mpr (SE.predE_predF_of_predV s hs).1
  exact ⟨D.z, D.V, orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one, D.isElemAbelian_V,
    D.card_V, h1, D.hsTwo hC hOM h10 h20 hle⟩

end GHSylow

end CFSG.ComponentClassification.GHarris

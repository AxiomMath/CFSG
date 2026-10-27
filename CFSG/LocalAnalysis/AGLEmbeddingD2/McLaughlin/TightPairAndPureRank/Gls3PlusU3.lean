module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusU3Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL34Aux
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.RankThree.PartOne.Census3
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem isoLie_twistedA2 (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedA 2 q) {Y : Type} [Group Y] (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) :
    IsoLie Y (.twistedA 2 q) := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  exact ⟨hv, ⟨e⟩⟩

theorem gls3PlusCase_lie_rankOne_U3 (q : TauCeti.PrimePower) (hq : q.p = 3)
    (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .twistedA 2 q) : Gls3PlusCase (.lie d) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP hΓ
  obtain ⟨e⟩ := hiso
  have hdU : IsUnitaryIndex 3 d := ⟨q, hq, hd⟩
  have hfe : d.1.fieldExponent = q.exponent := by rw [hd]; simp
  have hqcard : q.card = 3 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq]
  have hq1 : 1 ≤ q.exponent := q.exponent_pos
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨hti, hco, hNidx, J, hJc, hNJ⟩ := unitary_rankOne_data hdU ⟨e⟩ T
  obtain ⟨hcardT, hcomm, -, E, hET, hEel, hEcard⟩ :=
    kFactUnitarySylowStructure ↥K 3 d (by norm_num) hdU ⟨e⟩ T
  rw [hfe] at hNidx hcardT hEcard
  have hcardT' : Nat.card (T : Subgroup ↥K) = q.card ^ 3 := by
    rw [hcardT, hqcard, ← pow_mul, mul_comm]
  have hQcard : Nat.card ((P : Subgroup X) ⊓ K : Subgroup X) = q.card ^ 3 := by
    rw [← hTmap, Subgroup.card_map_of_injective K.subtype_injective, hcardT']
  have hqpos : 1 < q.card := by
    rw [hqcard]; exact Nat.one_lt_pow (by omega) (by norm_num)
  have hidx : ¬ 3 ∣ K.index := by
    refine not_three_dvd_index_of_rankOne P ?_ ?_ ?_ ?_ hΓ
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hQcard
      have : 1 < q.card ^ 3 := Nat.one_lt_pow (by norm_num) hqpos
      omega
    · intro k hk t ht ht1 hkt
      rw [← hTmap] at ht hkt
      obtain ⟨t', ht', rfl⟩ := ht
      obtain ⟨u', hu', hu'e⟩ := hkt
      have hconj : (⟨k, hk⟩ : ↥K) * t' * (⟨k, hk⟩ : ↥K)⁻¹ = u' := by
        apply Subtype.ext
        exact hu'e.symm
      have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [h]; rfl)
      have := hti t' ht' ht'1 ⟨k, hk⟩ (by rw [hconj]; exact hu')
      have h2 := (coe_mem_normalizer_map_iff (K := K) (T : Subgroup ↥K) ⟨k, hk⟩).mpr this
      rwa [hTmap] at h2
    · intro H hNH hHK
      have hN := map_normalizer_eq_inf hTmap
      rw [← hN] at hNH ⊢
      have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ H.subgroupOf K :=
        Subgroup.map_le_iff_le_comap.1 hNH
      by_cases heq : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) = H.subgroupOf K
      · left
        rw [← Subgroup.map_subgroupOf_eq_of_le hHK, ← heq]
      · right
        have htop := hco.2 _ (lt_of_le_of_ne hle heq)
        refine le_antisymm hHK fun x hx => ?_
        have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
        exact this
    · have hN := map_normalizer_eq_inf hTmap
      rw [← hN, Subgroup.relIndex, hQcard]
      have hsub : ((Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype).subgroupOf K =
          Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [hsub, hNidx, hqcard]
  have hPK : (P : Subgroup X) ≤ K := sylow_le_of_index P hidx
  have hPinf : (P : Subgroup X) ⊓ K = P := inf_eq_left.2 hPK
  have hTmapP : (T : Subgroup ↥K).map K.subtype = P := hTmap.trans hPinf
  have hdvdT : 3 ∣ Nat.card (T : Subgroup ↥K) := by
    rw [hcardT', hqcard, ← pow_mul]
    exact dvd_pow_self 3 (by omega)
  have hΓ : gammaCore 3 1 K (P : Subgroup X) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gammaCore_eq_map_normalizer
      hPK hTmapP hdvdT (fun t ht ht1 g hg => hti t ht ht1 g hg)
  have hΓ' : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype := by rw [hPinf]; exact hΓ
  refine ⟨?_, ?_, Or.inr (Or.inl ⟨q, hq, isoLie_twistedA2 d q hd e, hidx, ?_, ?_, ?_, ?_, ?_⟩)⟩
  · rw [hΓ']
    refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun h => ?_
    have h' : (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype =
        (⊤ : Subgroup ↥K).map K.subtype := by
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hco.1 (Subgroup.map_injective K.subtype_injective h')
  · intro H hlt hHK
    rw [hΓ'] at hlt
    have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ H.subgroupOf K :=
      Subgroup.map_le_iff_le_comap.1 hlt.le
    have hne : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≠ H.subgroupOf K := by
      intro h
      apply hlt.ne
      rw [h, Subgroup.map_subgroupOf_eq_of_le hHK]
    have htop := hco.2 _ (lt_of_le_of_ne hle hne)
    refine le_antisymm hHK fun x hx => ?_
    have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact this
  · rw [hΓ', hPinf, map_normalizer_eq_inf hTmapP]
  · refine ⟨J.map K.subtype, ?_, ?_⟩
    · exact isCyclic_of_surjective (K.subtype.subgroupMap J) (MonoidHom.subgroupMap_surjective _ _)
    · rw [hΓ', hNJ, Subgroup.map_sup, hTmapP, hPinf]
  ·
    rw [hPinf]
    intro hab
    have hTab : ⁅(T : Subgroup ↥K), (T : Subgroup ↥K)⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha b hb
      have := hab (a : X) (hTmapP ▸ ⟨a, ha, rfl⟩) (b : X) (hTmapP ▸ ⟨b, hb, rfl⟩)
      exact Subtype.ext this.symm
    have hZ : (T : Subgroup ↥K) ⊓ Subgroup.centralizer ((T : Subgroup ↥K) : Set ↥K) = ⊥ := by
      rw [← hcomm, hTab]
    have hTcomm : (T : Subgroup ↥K) ≤ Subgroup.centralizer ((T : Subgroup ↥K) : Set ↥K) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]; exact hTab
    have : (T : Subgroup ↥K) = ⊥ := by
      rw [← hZ]; exact (inf_eq_left.mpr hTcomm).symm
    rw [this, Subgroup.card_bot] at hcardT'
    have : 1 < q.card ^ 3 := Nat.one_lt_pow (by norm_num) hqpos
    omega
  · rw [hPinf, ← hTmapP, Subgroup.card_map_of_injective K.subtype_injective, hcardT']
  · refine ⟨E.map K.subtype, ?_, ?_, ?_⟩
    · rw [hPinf, ← hTmapP]
      exact Subgroup.map_mono hET
    · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel K.subtype
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard, hqcard, ← pow_mul, mul_comm]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

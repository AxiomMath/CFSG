module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusReeG2Model
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Gls3PlusL34Aux
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneIndex
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieSylowRee

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.AGLEmbedding CFSG.RankThree.PartOne.Census3
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem isoLie_reeG2 (d : TauCeti.ValidLieTypeIndex) (m : ℕ) (hd : d.1 = .reeG2 m) {Y : Type}
    [Group Y] (e : Y ≃* (TauCeti.CFSGIndex.lie d).Group) : IsoLie Y (.reeG2 m) := by
  obtain ⟨dd, hv⟩ := d
  simp only at hd
  subst hd
  exact ⟨hv, ⟨e⟩⟩

theorem gls3PlusCase_lie_reeG2 (m : ℕ) (d : TauCeti.ValidLieTypeIndex)
    (hd : d.1 = .reeG2 m) : Gls3PlusCase (.lie d) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP hΓ
  obtain ⟨e⟩ := hiso
  have hdR : IsReeGTwoIndex 3 d := ⟨rfl, m, hd⟩
  have hfe : d.1.fieldExponent = 2 * m + 1 := by rw [hd]; simp
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  obtain ⟨hti, hco, hNidx, ⟨J, hJc, hNJ⟩, E, hET, hEel, hEcard⟩ := ree_rankOne_data hdR ⟨e⟩ T
  obtain ⟨hcardT, -⟩ := KFactProofs.OneLieSylow.card_sylow_ree hdR ⟨e⟩ T
  rw [hfe] at hNidx hcardT hEcard
  have hQcard : Nat.card ((P : Subgroup X) ⊓ K : Subgroup X) = (3 ^ (2 * m + 1)) ^ 3 := by
    rw [← hTmap, Subgroup.card_map_of_injective K.subtype_injective, hcardT]
  have hqpos : 1 < (3 ^ (2 * m + 1)) ^ 3 :=
    Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by norm_num))
  have hidx : ¬ 3 ∣ K.index := by
    refine not_three_dvd_index_of_rankOne P ?_ ?_ ?_ ?_ hΓ
    · intro hbot
      rw [hbot, Subgroup.card_bot] at hQcard
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
      rw [hsub, hNidx]
  have hPK : (P : Subgroup X) ≤ K := sylow_le_of_index P hidx
  have hPinf : (P : Subgroup X) ⊓ K = P := inf_eq_left.2 hPK
  have hTmapP : (T : Subgroup ↥K).map K.subtype = P := hTmap.trans hPinf
  have hdvdT : 3 ∣ Nat.card (T : Subgroup ↥K) := by
    rw [hcardT, ← pow_mul]
    exact dvd_pow_self 3 (by omega)
  have hΓK : gammaCore 3 1 K (P : Subgroup X) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype :=
    CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.gammaCore_eq_map_normalizer
      hPK hTmapP hdvdT (fun t ht ht1 g hg => hti t ht ht1 g hg)
  have hΓ' : gammaCore 3 1 K ((P : Subgroup X) ⊓ K) =
      (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype := by
    rw [hPinf]; exact hΓK
  refine ⟨?_, ?_, Or.inr (Or.inr (Or.inl ⟨m, isoLie_reeG2 d m hd e, hidx, ?_, ?_, ?_⟩))⟩
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
  · refine ⟨E.map K.subtype, ?_, ?_, ?_⟩
    · rw [hPinf, ← hTmapP]
      exact Subgroup.map_mono hET
    · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hEel K.subtype
    · rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

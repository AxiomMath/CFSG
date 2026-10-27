module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneA1Index
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.RankOneIndex

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open CFSG.RankThree.PartOne.Census3 TauCeti CFSG.AGLEmbedding
open CFSG.AGLEmbedding.KFactProofs.NonUnitary

theorem gls3PlusCase_lie_rankOne_A1 (q : PrimePower) (hq : q.p = 3) (d : ValidLieTypeIndex)
    (hd : d.1 = .A 1 q) : Gls3PlusCase (.lie d) := by
  classical
  intro X _ _ _hK K hKn hsimp hnab hiso hC P hrk hΓ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e₀⟩ := hiso
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨d0, hv⟩ := d
  simp only at hd
  subst hd
  have hqcard : q.card = 3 ^ q.exponent := by rw [PrimePower.card_def, hq]
  have hn2 : 2 ≤ q.exponent := by
    by_contra h
    have h1 : q.exponent ≤ 1 := by omega
    have hv1 := ((LieTypeIndex.valid_iff _).1 hv).1
    have h4 : 4 ≤ q.card := (((LieTypeIndex.inStandardRange_iff _).1 hv1).2 rfl)
    rw [hqcard] at h4
    have : 3 ^ q.exponent ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hd' : IsLinTwoIndex 3 q.exponent ⟨.A 1 q, hv⟩ := ⟨q, rfl, hq, rfl⟩
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd'
  let e : ↥K ≃* PSL2GF 3 q.exponent := e₀.trans e₂
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal (G := X) (p := 3) P (N := K)
  have hTmap : (T : Subgroup ↥K).map K.subtype = (P : Subgroup X) ⊓ K := by
    rw [hT, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have D := smallRankOneData_of_isLinTwo hp2 hn2 hd' ⟨e₀⟩ T
  have hcardT : Nat.card (T : Subgroup ↥K) = 3 ^ q.exponent := by
    have hfs : Function.Surjective (e : ↥K →* PSL2GF 3 q.exponent) := e.surjective
    have := (psl2GF_sylow 3 q.exponent (by omega) (T.mapSurjective hfs)).2
    rw [Sylow.coe_mapSurjective hfs T, Subgroup.card_map_of_injective e.injective] at this
    exact this
  have hcardX : Nat.card ↥((P : Subgroup X) ⊓ K) = 3 ^ q.exponent := by
    rw [← hTmap, Subgroup.card_map_of_injective K.subtype_injective, hcardT]
  have hN : IsCoatom (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) := D.maximal
  have hNmap := map_normalizer_eq_inf hTmap
  have hidx : ¬ 3 ∣ K.index := by
    refine not_three_dvd_index_of_rankOne (K := K) P ?_ ?_ ?_ ?_ hΓ
    · intro h
      rw [h, Subgroup.card_bot] at hcardX
      have : 3 ^ 2 ≤ 3 ^ q.exponent := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    · intro k hk t ht ht1 hkt
      rw [← hTmap] at ht hkt
      obtain ⟨t0, ht0, rfl⟩ := ht
      obtain ⟨t1, ht1', hk1⟩ := hkt
      have h1 : (⟨k, hk⟩ : ↥K) * t0 * (⟨k, hk⟩ : ↥K)⁻¹ ∈ (T : Subgroup ↥K) := by
        have : t1 = (⟨k, hk⟩ : ↥K) * t0 * (⟨k, hk⟩ : ↥K)⁻¹ := Subtype.ext (by simpa using hk1)
        rwa [← this]
      have h0 : t0 ≠ 1 := fun h => ht1 (by simp [h])
      have := D.ti t0 ht0 h0 ⟨k, hk⟩ h1
      have h2 : k ∈ (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype :=
        ⟨⟨k, hk⟩, this, rfl⟩
      rw [hNmap] at h2
      exact h2.2
    · intro H hle hHK
      rw [← hNmap] at hle ⊢
      have hle' : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ H.subgroupOf K := by
        intro x hx
        exact hle ⟨x, hx, rfl⟩
      by_cases hne : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) = H.subgroupOf K
      · left
        rw [hne, Subgroup.map_subgroupOf_eq_of_le hHK]
      · right
        have htop := hN.2 _ (lt_of_le_of_ne hle' hne)
        refine le_antisymm hHK fun x hx => ?_
        have : (⟨x, hx⟩ : ↥K) ∈ H.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
        exact this
    · have hsub : ((Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype).subgroupOf K =
          Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      rw [← hNmap, Subgroup.relIndex, hsub, hcardX]
      exact index_normalizer_of_equiv hp2 (by omega) e T
  exact gls3ConclusionPlus_A1_of_index q hq ⟨.A 1 q, hv⟩ rfl e₀ hidx P

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

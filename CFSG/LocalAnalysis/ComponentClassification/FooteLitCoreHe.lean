module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreHeBase
public import CFSG.Sporadic.HeldB.AlmostSimple
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreResidual
public import CFSG.Sporadic.HeldB.AutModel
public import CFSG.Sporadic.HeldB.OuterCentQS
public import CFSG.Sporadic.HeldB.OuterFixedCore

public section

namespace CFSG.ComponentClassification.FooteLit.HeCore

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.FixedCommutingProduct

theorem index_inn_le_two
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (θ : S ≃* Blueprint.NativeSporadic.He) :
    (MulAut.conj : S →* MulAut S).range.index ≤ 2 := by
  obtain ⟨hs, hnc, ⟨θ'⟩⟩ := generalizedFitting_mulAut_he hna θ
  have h := index_generalizedFitting_le_two_of_outer Sporadic.Schreier.AT_He_Schreier.1 hs hnc θ'
  rwa [generalizedFitting_mulAut_eq_range hna] at h

theorem oddOuterInner_he
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (θ : S ≃* Blueprint.NativeSporadic.He) : OddOuterInner S := fun σ hσ => by
  obtain ⟨s, hs⟩ := mem_of_odd_of_index_le_two (index_inn_le_two hna θ) hσ
  exact ⟨s, hs.symm⟩

theorem commute_oddCore_he
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (θ : S ≃* Blueprint.NativeSporadic.He) (i : MulAut S) (hi : orderOf i = 2) :
    ∀ x y : ↥(pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S)))), x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center S = ⊥ := center_eq_bot_of_isSimpleGroup hna
  have hκ := mulAut_conj_injective hZ
  set Cᵢ := centralizer ({i} : Set (MulAut S)) with hCᵢ
  set N := (pPrimeCore 2 ↥Cᵢ).map Cᵢ.subtype with hNdef
  suffices hN : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a by
    intro x y
    exact Subtype.ext (Subtype.ext (hN _ ⟨x, x.2, rfl⟩ _ ⟨y, y.2, rfl⟩))
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, card_map_of_injective Cᵢ.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hNC : N ≤ Cᵢ := map_subtype_le _
  have hNinn : N ≤ (MulAut.conj : S →* MulAut S).range := fun n hn =>
    mem_of_odd_of_index_le_two (index_inn_le_two hna θ)
      (Odd.of_dvd_nat hNodd (N.orderOf_dvd_natCard hn))
  by_cases hinn : i ∈ (MulAut.conj : S →* MulAut S).range
  ·
    obtain ⟨hs, hnc, ⟨θ'⟩⟩ := generalizedFitting_mulAut_he hna θ
    have hbot : pPrimeCore 2 ↥Cᵢ = ⊥ := inner_pPrimeCore_eq_bot_of_outer
      Sporadic.Schreier.AT_He_Schreier.1 hs hnc θ'
      (by rw [generalizedFitting_mulAut_eq_range hna]; exact hinn) hi
    intro a ha b hb
    rw [hNdef, hbot, Subgroup.map_bot, mem_bot] at ha hb
    rw [ha, hb]
  set M := N.comap (MulAut.conj : S →* MulAut S) with hMdef
  have hMN : M.map MulAut.conj = N := map_comap_eq_self hNinn
  have hfix : ∀ s : S, MulAut.conj s ∈ Cᵢ ↔ i s = s := fun s => by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro h
      apply hκ
      rw [mulAut_conj_map, ← h, mul_inv_cancel_right]
    · intro h
      have h1 := mulAut_conj_map i s
      rw [h] at h1
      calc MulAut.conj s * i = i * MulAut.conj s * i⁻¹ * i := by rw [← h1]
        _ = i * MulAut.conj s := by group
  have hMfix : M ≤ fixedSubgroup i := fun s hs => (hfix s).mp (hNC hs)
  have hMn : ∀ f ∈ fixedSubgroup i, ∀ m ∈ M, f * m * f⁻¹ ∈ M := fun f hf m hm => by
    have hfC : MulAut.conj f ∈ Cᵢ := (hfix f).mpr hf
    obtain ⟨c, hc, hcm⟩ := hm
    show MulAut.conj (f * m * f⁻¹) ∈ N
    refine ⟨⟨MulAut.conj f, hfC⟩ * c * ⟨MulAut.conj f, hfC⟩⁻¹,
      (pPrimeCore_normal (p := 2) (G := ↥Cᵢ)).conj_mem c hc _, ?_⟩
    change MulAut.conj f * (c : MulAut S) * (MulAut.conj f)⁻¹ = MulAut.conj (f * m * f⁻¹)
    rw [show (c : MulAut S) = MulAut.conj m from hcm, map_mul, map_mul, map_inv]
  have hModd : Odd (Nat.card M) := by
    rw [← hMN, card_map_of_injective hκ] at hNodd
    exact hNodd
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  set e : S ≃* heP := θ.trans heEquivP with he
  obtain ⟨x, hx, hxP, hx2⟩ := exists_heConjR_eq hbij (MulAut.congr e i)
    (by rw [MulEquiv.orderOf_eq, hi]) (by rwa [congr_mem_range_conj_iff])
  obtain ⟨g, hg, hxg⟩ := exists_conj_heAutU x.2 hxP hx2
  let f : fixedSubgroup i ≃* (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup _) :=
    ((fixedSubgroupCongr e i).trans (MulEquiv.subgroupCongr (by rw [hx]))).trans
      (fixedSubgroupEquivOfConj x hg heAutU hxg)
  set φ : fixedSubgroup i →* Equiv.Perm (Fin 8330) :=
    (heP ⊓ Subgroup.centralizer {heAutU} : Subgroup _).subtype.comp f.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Subtype.coe_injective.comp f.injective
  obtain ⟨hDeq, -, hidx⟩ := ctbh_outer_centralizer_derived_quasisimple
  have hDC : heOuterD ≤ heOuterC := by
    rw [hDeq]
    exact Subgroup.commutator_le_self _
  have key := commute_of_odd_normal (N := (M.subgroupOf (fixedSubgroup i)).map φ) hDC hidx
    heOuterQuot_simple (by rw [card_heOuterD_quot]; decide) ?_ ?_ ?_
  · intro a ha b hb
    rw [← hMN] at ha hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    have h1 := key (φ ⟨s, hMfix hs⟩) ⟨⟨s, hMfix hs⟩, hs, rfl⟩ (φ ⟨t, hMfix ht⟩)
      ⟨⟨t, hMfix ht⟩, ht, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    have h2 : s * t = t * s := congrArg Subtype.val (hφ h1)
    rw [← map_mul, ← map_mul, h2]
  · rw [heOuterC_eq]
    rintro _ ⟨m, -, rfl⟩
    exact (f m).2
  · rw [heOuterC_eq]
    rintro c hc _ ⟨m, hm, rfl⟩
    have hφc : φ (f.symm ⟨c, hc⟩) = c := by
      show ((f (f.symm ⟨c, hc⟩) : ↥(heP ⊓ Subgroup.centralizer {heAutU})) :
        Equiv.Perm (Fin 8330)) = c
      rw [MulEquiv.apply_symm_apply]
    refine ⟨f.symm ⟨c, hc⟩ * m * (f.symm ⟨c, hc⟩)⁻¹, hMn _ (f.symm ⟨c, hc⟩).2 _ hm, ?_⟩
    rw [map_mul, map_mul, map_inv, hφc]
  · rw [card_map_of_injective hφ, Nat.card_congr (subgroupOfEquivOfLe hMfix).toEquiv]
    exact hModd

end CFSG.ComponentClassification.FooteLit.HeCore

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteCoreResidualInputNoHe : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SectionRank.IsKGroupCat K → ∀ a : K, orderOf a = 2 →
    ∀ Y : Subgroup K, IsPComponent 2 Y →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) →
    (¬ ∃ n : ℕ, Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* alternatingGroup (Fin n))) →
    ¬ (OddOuterInner (Y ⧸ Open.fusionZStar Y) ∧ UBalanced (Y ⧸ Open.fusionZStar Y)) →
    ¬ Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* Blueprint.NativeSporadic.He) →
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K

theorem footeCoreResidualInput_of_noHe
    (h : FooteCoreResidualInputNoHe) : FooteCoreResidualInput := by
  intro K _ _ hK a ha Y hY hL2 halt hb
  by_cases hHe : Nonempty ((Y ⧸ Open.fusionZStar Y) ≃* Blueprint.NativeSporadic.He)
  · obtain ⟨θ⟩ := hHe
    obtain ⟨hsimple, hna⟩ := zStarQuotient_simple hY
    have := hsimple
    exact core_commutator_le_of_localAbelianCore_of_oddOuterInner footeLBalanceInput_holds ha hY
      (HeCore.oddOuterInner_he hna θ) (HeCore.commute_oddCore_he hna θ)
  · exact h K hK a ha Y hY hL2 halt hb hHe

end CFSG.ComponentClassification.FooteLit

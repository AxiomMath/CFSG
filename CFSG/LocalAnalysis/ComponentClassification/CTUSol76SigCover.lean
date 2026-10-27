module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigBal
public import CFSG.LocalAnalysis.ComponentClassification.Sol76False316Cover
public import CFSG.LocalAnalysis.ComponentClassification.Sol76T13Props
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivBasic
public import CFSG.RankThree.PartOne.KF1514B.Sylow

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.Sol76T13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : Subgroup G}

theorem exists_conj_mem_of_sup_oddCoreIn {K M : Subgroup G} (hKM : K ≤ M)
    (hsup : K ⊔ oddCoreIn M = M) {s : G} (hsM : s ∈ M) (hs2 : orderOf s = 2) :
    ∃ m ∈ M, m⁻¹ * s * m ∈ K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKO : K ≤ normalizer (oddCoreIn M : Set G) := hKM.trans (le_normalizer_oddCoreIn M)
  have hprod := AS81.card_sup_mul_card_inf_of_le_normalizer_left hKO
  rw [hsup] at hprod
  set T := K.subgroupOf M with hT
  have hTcard : Nat.card T = Nat.card K := by
    rw [hT, ← Subgroup.card_map_of_injective M.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKM]
  have hidx := T.card_mul_index
  have hMcard : Nat.card (⊤ : Subgroup ↥M) = Nat.card M := Subgroup.card_top
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hdvd : T.index ∣ Nat.card (oddCoreIn M) := by
    refine ⟨Nat.card (K ⊓ oddCoreIn M : Subgroup G), ?_⟩
    have h1 : Nat.card K * T.index = Nat.card M := by
      rw [← hTcard, hidx]
    have h2 : Nat.card K * (T.index * Nat.card (K ⊓ oddCoreIn M : Subgroup G)) =
        Nat.card K * Nat.card (oddCoreIn M) := by
      rw [← mul_assoc, h1, hprod]
    exact (Nat.eq_of_mul_eq_mul_left hKpos h2).symm
  have hodd : ¬ 2 ∣ T.index := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp (coprime_card_oddCoreIn M) (h.trans hdvd)
  set s' : ↥M := ⟨s, hsM⟩ with hs'
  have hs'2 : orderOf s' = 2 := by rw [Subgroup.orderOf_mk]; exact hs2
  have hA : IsPGroup 2 (zpowers s') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs'2, pow_one])
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.KF1514B.exists_conj_le_of_not_dvd_index hodd hA
  refine ⟨(g⁻¹ : ↥M), (g⁻¹ : ↥M).2, ?_⟩
  have hmem : (MulAut.conj g).toMonoidHom s' ∈ T := hg ⟨s', mem_zpowers s', rfl⟩
  rw [hT, mem_subgroupOf] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem two_dvd_card_of_pos_pRank {X : Subgroup G} (hX : 0 < CFSG.Open.pRank 2 X) :
    2 ∣ Nat.card X := by
  set S := {k : ℕ | ∃ E : Subgroup G, E ≤ X ∧ CFSG.Open.IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k}
    with hS
  have hne : S.Nonempty := by
    by_contra hS'
    rw [Set.not_nonempty_iff_eq_empty] at hS'
    have h0 : CFSG.Open.pRank 2 X = 0 := by
      change sSup S = 0
      rw [hS', csSup_empty]
      rfl
    omega
  obtain ⟨k, ⟨E, hEX, -, hEc⟩, hk⟩ := exists_lt_of_lt_csSup hne hX
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hEX)
  rw [hEc]
  exact dvd_pow_self 2 (by omega)

theorem eq_of_le_sup_oddCoreIn {K K' M : Subgroup G} (hK : K ∈ kStarComponents N)
    (hK' : K' ∈ kStarComponents N) (hKM : K ≤ M) (hK'M : K' ≤ M)
    (hle : K ≤ K' ⊔ oddCoreIn M) : K = K' := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  set O := oddCoreIn M with hO
  have hMO : M ≤ normalizer (O : Set G) := le_normalizer_oddCoreIn M
  set C := ⁅K, K'⁆ with hC
  have hCN : C ≤ oddCoreIn N := FooteLit.commutator_le_oddCoreIn_of_ne hK.1 hK'.1 hne
  have hCM : C ≤ M := commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hKM ha) (hK'M hb)) (inv_mem (hKM ha))) (inv_mem (hK'M hb))
  have hKCO : K ≤ C ⊔ O := by
    rw [← GSThmB.commutator_eq_self_of_isPComponent hK.1.1 hK.1.2, commutator_le]
    intro a ha b hb
    have hb' : b ∈ ((K' ⊔ O : Subgroup G) : Set G) := hle hb
    rw [coe_mul_of_left_le_normalizer_right K' O (hK'M.trans hMO)] at hb'
    obtain ⟨k', hk', o, ho, rfl⟩ := hb'
    have e : ⁅a, k' * o⁆ = ⁅a, k'⁆ * (k' * ⁅a, o⁆ * k'⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine mul_mem (mem_sup_left (commutator_mem_commutator ha hk')) (mem_sup_right ?_)
    have hao : ⁅a, o⁆ ∈ O := by
      rw [commutatorElement_def]
      exact mul_mem ((mem_normalizer_iff.mp (hMO (hKM ha)) o).mp ho) (inv_mem ho)
    exact (mem_normalizer_iff.mp (hMO (hK'M hk')) _).mp hao
  have hCodd : Odd (Nat.card C) := Nat.coprime_two_left.mp
    (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hCN) (coprime_card_oddCoreIn N))
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn M)
  have hprod := AS81.card_sup_mul_card_inf_of_le_normalizer_left (hCM.trans hMO)
  have hCOodd : Odd (Nat.card (C ⊔ O : Subgroup G)) :=
    (Nat.odd_mul.mp (hprod ▸ hCodd.mul hOodd)).1
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat hCOodd (Subgroup.card_dvd_of_le hKCO)
  have h2 : 2 ∣ Nat.card K :=
    two_dvd_card_of_pos_pRank (by have := two_le_pRank_of_mem_solomonKStar hK.2; omega)
  exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr h2)

theorem false_of_cover (hq : QuasisimpleTwoPartInput) (hF : False316CoverFor simpleAmbient)
    (hG : SimpleAmbient G) (hN : IsSolomonChoice N) {H : Subgroup G}
    (hcov : ∀ K ∈ kStarComponents N, ∃ M ∈ kStarComponents H, K ≤ M ∧ K ⊔ oddCoreIn M = M)
    (hcent : ∀ K ∈ kStarComponents N, ∀ s ∈ K, orderOf s = 2 →
      centralizer ({s} : Set G) ≤ H) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N' := normalizer (solomonKStarOf H : Set G) with hN'
  choose! f hf using hcov
  have hinj : Set.InjOn f (kStarComponents N) := fun K hK K' hK' heq => by
    obtain ⟨-, hKf, -⟩ := hf K hK
    obtain ⟨-, hK'f, hsup'⟩ := hf K' hK'
    rw [← heq] at hK'f hsup'
    exact eq_of_le_sup_oddCoreIn hK hK' hKf hK'f (hKf.trans hsup'.ge)
  have hmaps : Set.MapsTo f (kStarComponents N) (kStarComponents H) := fun K hK => (hf K hK).1
  have hHcard : (kStarComponents N).ncard ≤ (kStarComponents H).ncard :=
    Set.ncard_le_ncard_of_injOn f hmaps hinj
  have hHN' : kStarComponents H ⊆ kStarComponents N' := fun M hM =>
    mem_kStarComponents_normalizer_solomonKStarOf hM
  have hN'le := ncard_kStarComponents_le_of_simple hq hG hN N'
  have hHle := Set.ncard_le_ncard hHN' (Set.toFinite _)
  have hHN'eq : kStarComponents N' = kStarComponents H :=
    (Set.eq_of_subset_of_ncard_le hHN' (by omega)).symm
  have himg : f '' kStarComponents N = kStarComponents H :=
    Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.mpr hmaps)
      (by rw [hinj.ncard_image]; omega)
  have hKstar : solomonKStarOf N' = solomonKStarOf H := by
    rw [solomonKStarOf_eq_sSup, solomonKStarOf_eq_sSup, hHN'eq]
  have hHN'le : H ≤ N' := le_normalizer_solomonKStarOf H
  refine hF G hG N hN N' (by rw [hKstar]) ?_ ?_ ?_
  · intro K hK
    exact ⟨f K, hHN'eq ▸ (hf K hK).1, (hf K hK).2.1, (hf K hK).2.2.ge⟩
  · intro M hM
    rw [hHN'eq, ← himg] at hM
    obtain ⟨K, hK, rfl⟩ := hM
    exact ⟨K, hK, (hf K hK).2.1⟩
  · intro M hM s hsM hs2
    rw [hHN'eq, ← himg] at hM
    obtain ⟨K, hK, rfl⟩ := hM
    obtain ⟨hfK, hKM, hsup⟩ := hf K hK
    obtain ⟨m, hmM, hmK⟩ := exists_conj_mem_of_sup_oddCoreIn hKM hsup hsM hs2
    have hs02 : orderOf (m⁻¹ * s * m) = 2 := by
      have := (MulAut.conj m⁻¹).orderOf_eq s
      simp only [MulAut.conj_apply, inv_inv] at this
      rw [this, hs2]
    have hC := hcent K hK _ hmK hs02
    have hmH : m ∈ H := hfK.1.1 hmM
    intro y hy
    have hy' : m⁻¹ * y * m ∈ centralizer ({m⁻¹ * s * m} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hy ⊢
      calc m⁻¹ * y * m * (m⁻¹ * s * m) = m⁻¹ * (y * s) * m := by group
        _ = m⁻¹ * (s * y) * m := by rw [hy]
        _ = m⁻¹ * s * m * (m⁻¹ * y * m) := by group
    have e : y = m * (m⁻¹ * y * m) * m⁻¹ := by group
    rw [e]
    exact hHN'le (mul_mem (mul_mem hmH (hC hy')) (inv_mem hmH))

end CFSG.ComponentClassification.Sol76.Sig

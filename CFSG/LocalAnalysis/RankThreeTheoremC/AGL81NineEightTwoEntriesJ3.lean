module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3OuterInvClosed
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import CFSG.Sporadic.Schreier.PairJ3Faithful

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open CFSG.AGLEmbedding
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner inner_normal)

private theorem isSimpleGroup_card_center_j3
    {K : Type} [Group K]
    [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) :
    IsSimpleGroup K ∧ Nat.card K = 50232960 ∧ Subgroup.center K = ⊥ := by
  obtain ⟨e⟩ := hK
  obtain ⟨β⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  have := CFSG.Sporadic.J3.isSimpleGroup_J3
  haveI hs : IsSimpleGroup K :=
    MulEquiv.isSimpleGroup (H := Blueprint.NativeSporadic.J3) (e.trans β.symm)
  have hcard : Nat.card K = 50232960 := by
    rw [Nat.card_congr (e.trans β.symm).toEquiv]
    exact CFSG.Sporadic.J3.card_J3
  refine ⟨hs, hcard, ?_⟩
  obtain ⟨a, b, hab⟩ := nonabelian_of_card_eq hcard
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · exact h
  · have hb : b ∈ Subgroup.center K := h ▸ Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

private theorem conj_injective_j3 {K : Type} [Group K] (hZ : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : x ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun y => by
    have h := congrArg (fun f : MulAut K => f y) hx
    change x * y * x⁻¹ = y at h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem centralizer_eq_sylow_j3
    {K : Type} [Group K]
    [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) (T : Sylow 3 K)
    {b : K} (hb : orderOf b = 3) (hTb : (T : Subgroup K) ≤ Subgroup.centralizer {b}) :
    Subgroup.centralizer {b} = T := by
  obtain ⟨-, hcard, -⟩ := isSimpleGroup_card_center_j3 hK
  obtain ⟨e⟩ := hK
  obtain ⟨β⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  let φ : K ≃* CFSG.Sporadic.Schreier.j3P :=
    e.trans (β.symm.trans CFSG.Sporadic.Schreier.j3PermEquiv)
  have hT := card_sylow_three_of_card_eq hcard T
  have hφo : orderOf ((φ b : CFSG.Sporadic.Schreier.j3P) : Equiv.Perm (Fin 6156)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact hb
  have hC := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv φ b
  have hdvd : Nat.card (T : Subgroup K) ∣ Nat.card (Subgroup.centralizer {b}) :=
    Subgroup.card_dvd_of_le hTb
  refine (Subgroup.eq_of_le_of_card_ge hTb ?_).symm
  rcases CFSG.RankThree.PartTwo.Sec21.Item228CensusProof.card_centralizer_j3P (φ b).2 hφo with
    h | h
  · rw [hC, h, hT] at hdvd
    norm_num at hdvd
  · rw [hC, h, hT]
    norm_num

theorem centralizer_inn_le_j3
    {K : Type} [Group K]
    [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) (T : Sylow 3 K) :
    Subgroup.centralizer (((T : Subgroup K).map (MulAut.conj : K →* MulAut K) :
      Subgroup (MulAut K)) : Set (MulAut K)) ≤
        (T : Subgroup K).map (MulAut.conj : K →* MulAut K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut K) := MulEquiv.finite_left
  obtain ⟨hs, hcard, hZ⟩ := isSimpleGroup_card_center_j3 hK
  haveI := hs
  have hinj := conj_injective_j3 hZ
  have hOR := kFactJ3OuterRank_closed CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨hOut, -⟩ := hOR K hK
  have hidx : ¬ 3 ∣ ((T : Subgroup K).map (MulAut.conj : K →* MulAut K)).index := by
    rw [Subgroup.index_map_of_injective _ hinj]
    change ¬ 3 ∣ (T : Subgroup K).index * Nat.card (Outer K)
    have hpos : 0 < Nat.card (Outer K) := Nat.card_pos
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · exact T.not_dvd_index h
    · have := Nat.le_of_dvd hpos h
      omega
  let T₁ : Sylow 3 (MulAut K) := (T.isPGroup'.map (MulAut.conj : K →* MulAut K)).toSylow hidx
  have hne : Subgroup.normalizer ((T₁ : Subgroup (MulAut K)) : Set (MulAut K)) ≠ ⊤ := by
    intro htop
    haveI : (T : Subgroup K).Normal := ⟨fun t ht k => by
      have hk : MulAut.conj k ∈ Subgroup.normalizer
          ((T₁ : Subgroup (MulAut K)) : Set (MulAut K)) := htop ▸ Subgroup.mem_top _
      have h := (Subgroup.mem_normalizer_iff.mp hk (MulAut.conj t)).mp ⟨t, ht, rfl⟩
      rw [← map_inv, ← map_mul, ← map_mul] at h
      exact (Subgroup.mem_map_iff_mem hinj).mp h⟩
    have hT := card_sylow_three_of_card_eq hcard T
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T : Subgroup K) with h | h
    · rw [h, Subgroup.card_bot] at hT
      norm_num at hT
    · rw [h, Subgroup.card_top, hcard] at hT
      norm_num at hT
  have hC : Subgroup.centralizer ((inner K : Subgroup (MulAut K)) : Set (MulAut K)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun x => ?_
    have hc : (α x)⁻¹ * x ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun g => by
      have h := congrArg (fun f : MulAut K => f (α.symm g))
        (Subgroup.mem_centralizer_iff.mp hα (MulAut.conj x) ⟨x, rfl⟩)
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply, map_mul,
        map_inv] at h
      calc g * ((α x)⁻¹ * x) = (α x)⁻¹ * (α x * g * (α x)⁻¹) * x := by group
        _ = (α x)⁻¹ * (x * g * x⁻¹) * x := by rw [h]
        _ = (α x)⁻¹ * x * g := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
    rw [MulAut.one_apply]
    exact hc
  have hIS := j3InSitu_of kFactJ3Sylow kFactJ3OuterInvolution hOR (inner_normal K)
    (hK.map fun e => (MonoidHom.ofInjective hinj).symm.trans e) hC T₁ le_rfl hne
  exact (Subgroup.centralizer_le fun x hx => hx.1).trans hIS.centralizer_center

theorem eq_bot_of_normalizes_j3
    {K : Type} [Group K] [Finite K] (hK : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .J3).Group))
    (T : Sylow 3 K) {V : Subgroup (MulAut K)} (hV : IsPGroup 2 V)
    (hTV : ∀ t ∈ (T : Subgroup K), MulAut.conj t ∈ Subgroup.normalizer (V : Set (MulAut K))) :
    V = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hZ⟩ := isSimpleGroup_card_center_j3 hK
  have hF := kFactJ3Sylow K hK T
  refine mulAut_eq_bot_of_sig hZ Nat.prime_three (T := T)
    (B := CFSG.Quasithin.centerOf (T : Subgroup K)) (Q := T) (fun b hb => hb.1) le_rfl
    hF.center_elem.1.2 (hF.center_elem.2.trans (by norm_num)) T.isPGroup'
    ?_ ?_ (centralizer_inn_le_j3 hK T) V
    (coprime_card_of_isPGroup Nat.prime_three Nat.prime_two (by norm_num) hV) hTV
  ·
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 t ht).symm
  ·
    intro b hb hb1
    have hTb : (T : Subgroup K) ≤ Subgroup.centralizer {b} := fun t ht =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb.2 t ht)
    rw [centralizer_eq_sylow_j3 hK T (orderOf_eq_prime (hF.center_elem.1.2 b hb) hb1) hTb]
    exact Subgroup.le_normalizer

theorem kFactNineThreeNoTwoAt_j3 :
    KFactNineThreeNoTwoAt 3 (.sporadic .J3) := by
  intro X _ _ K hK hiso _ T S hS hTS
  haveI := hK
  exact le_centralizer_of_aut (T := (T : Subgroup K).map K.subtype) (Subgroup.map_subtype_le _)
    (fun V hV hN => eq_bot_of_normalizes_j3 hiso T hV fun t ht => hN t ⟨t, ht, rfl⟩) hS hTS

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

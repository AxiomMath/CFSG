module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FinalSC
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimStage3
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimSC
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimP0
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGroup

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

namespace Claim2526

section Extract

variable {G : Type} [Group G]

theorem exists_S8Data {L : Subgroup G} {φ : ↥L ≃* alternatingGroup (Fin 8)} {t i : G} {a b : Fin 8}
    (hab : a ≠ b) (hind : InducesAut t L φ (MulAut.conjNormal (Equiv.swap a b)))
    (ht2 : t * t = 1) (hi2 : i * i = 1) (hti : t * i = i * t) (hi1 : i ≠ 1)
    (hiL : ∀ k ∈ L, i * k = k * i) :
    ∃ φ' : ↥L ≃* alternatingGroup (Fin 8), S8Data L φ' t i := by
  obtain ⟨ρ, hρ⟩ := exists_perm_conj_swap hab
  refine ⟨φ.trans (MulAut.conjNormal ρ⁻¹), ⟨ht2, hi2, hti, hi1, hind.1, hiL, ?_⟩⟩
  intro y y' hy
  have h1 := hind.2 y y' hy
  have h2 : (φ y' : Equiv.Perm (Fin 8)) =
      Equiv.swap a b * (φ y : Equiv.Perm (Fin 8)) * (Equiv.swap a b)⁻¹ := by
    have := congrArg Subtype.val h1
    simpa [MulAut.conjNormal_apply] using this
  apply Subtype.ext
  simp only [MulEquiv.trans_apply, MulAut.conjNormal_apply]
  rw [h2, ← hρ]
  group

end Extract

end Claim2526

open Claim2526

theorem lemma2526Claim : Lemma2526Claim := by
  intro G _ _ T M hs N t zK h hpR i hiSC hi1 hi2
  by_contra hnotcomp
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH : N.H ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [← hK0]; exact N.H_le_normalizer_K0
  have hf := h.facts2511
  have h254 := h.facts254
  have h258 := h.facts258
  have hsimple := h258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hS2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  have hT2 : IsPGroup 2 ↥T := hs.setting.sylow.isPGroup
  have hSCeq : N.SC = N.S ⊓ Subgroup.centralizer (N.K : Set G) := by
    unfold Notation25.SC; rw [hK0]
  have htSC : t ∈ N.SC := hf.t_mem
  have hiS : i ∈ N.S := N.SC_le_S hiSC
  have hit : i ≠ t := by
    rintro rfl
    exact hnotcomp h.concl2518.1
  have htZ : t ∈ centerOf N.S := by
    rw [hf.centerS_z]
    exact Subgroup.subset_closure (by simp)
  have hts : ∀ s ∈ N.S, t * s = s * t := fun s hs' =>
    (Subgroup.mem_centralizer_iff.mp htZ.2 s hs').symm
  obtain ⟨-, hCSi, Ki, hKi, hcases, h4⟩ :=
    h.concl2519 i (by rw [← hSCeq]; exact hiSC) hi1 hi2 hnotcomp
  rcases h4 with ⟨hzK, -⟩ | ⟨-, φ, a, b, hab, hind⟩
  ·
    exfalso
    have hzt := h.concl2525.2
    have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
    have htK : t ∈ N.K := by
      have : t = N.z * zK⁻¹ := by rw [hzt]; group
      rw [this]
      exact N.K.mul_mem hzK (N.K.inv_mem hzKK)
    have htc : ∀ y ∈ N.K, t * y = y * t := by
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer htSC) y (hK0 ▸ hy)
      exact this.symm
    exact hf.t_ne_one (hZK t htK htc)
  have htN : t ∈ Subgroup.normalizer (Ki : Set G) := hind.1
  have hKleKi : N.K ≤ Ki := by
    rcases hcases with ⟨hne, -⟩ | ⟨hKeq, -⟩
    · exfalso
      exact hne (BenderBranch.conjugate_eq_iff_mem_normalizer.mpr htN).symm
    · rw [hKeq]
      exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
  have hzK1 : zK ≠ 1 := by
    intro h1
    apply hf.not_conj 1
    have := h.concl2525.2
    rw [h1, mul_one] at this
    simpa using this
  have hKiC : Ki ≤ Subgroup.centralizer ({i} : Set G) := hKi.1
  have hiL : ∀ k ∈ Ki, i * k = k * i := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKiC hk)).symm
  have htmem : t ∈ N.S ⊓ Subgroup.centralizer ({i} : Set G) ⊓ (N.S ⊓ Subgroup.centralizer (N.K : Set G)) := by
    rw [hCSi]
    exact Subgroup.subset_closure (by simp)
  have hti : t * i = i * t := Subgroup.mem_centralizer_singleton_iff.mp htmem.1.2
  have ht2 : t * t = 1 := by rw [← sq]; exact hf.t_sq
  have hi2' : i * i = 1 := by rw [← sq]; exact hi2
  obtain ⟨φ', D8⟩ := exists_S8Data hab hind ht2 hi2' hti hi1 hiL
  have hU4 : Nat.card (Subgroup.closure ({t, i} : Set G)) = 4 :=
    card_closure_pair ht2 hi2' hti hf.t_ne_one hi1 hit.symm
  have hUexp : ∀ u ∈ Subgroup.closure ({t, i} : Set G), u ^ 2 = 1 := by
    intro u hu
    rw [sq]
    exact V0set_sq D8 (mem_closure_pair_of_involutions ht2 hi2' hti hu)
  set U := Subgroup.closure ({t, i} : Set G) with hU
  have hUSC : U ≤ N.SC := (Subgroup.closure_le _).mpr (by
    intro x hx
    rcases hx with rfl | hx
    · exact htSC
    · rw [Set.mem_singleton_iff.mp hx]; exact hiSC)
  have hC : N.SC ⊓ Subgroup.centralizer (U : Set G) ≤ U := by
    rintro x ⟨hxSC, hxC⟩
    rw [← hCSi]
    refine ⟨⟨N.SC_le_S hxSC, ?_⟩, by rw [← hSCeq]; exact hxSC⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hxC i (Subgroup.subset_closure (by simp))).symm
  have hSC2 : IsPGroup 2 ↥N.SC := hS2.to_le N.SC_le_S
  have hne : U ≠ N.SC := by
    intro hU'
    have hUsq : ∀ a : ↥N.SC, a * a = 1 := by
      intro a
      have hmem : (a : G) ∈ U := by rw [hU']; exact a.2
      apply Subtype.ext
      simpa [sq] using hUexp _ hmem
    have : Fact (IsPGroup 2 ↥N.SC) := ⟨hSC2⟩
    exact h.concl2524 (frattini_eq_bot_of_exponent_two (fun a b => comm_of_exponent_two hUsq a b)
      (fun y => by rw [sq]; exact hUsq y))
  have hSCx_le : CFSG.conjugate N.SC N.x ≤ N.S := h.concl255.2.1
  have hexp4 : ∀ s ∈ N.SC, s ^ 4 = 1 := by
    apply pow_four_of_conj (x := N.x)
    refine pow_four_eq_one D8 hS2 hSCx_le ?_ ?_ h.concl255.1
    · intro c hc
      have hcS := hSCx_le hc
      have hci : i * c = c * i := h.concl255.2.2 i hiSC c hc
      have hct : c * t = t * c := (hts c hcS).symm
      refine ⟨?_, hct⟩
      have hcC : c ∈ Subgroup.centralizer ({i} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]; exact hci.symm
      have hKic : IsComponentIn (CFSG.conjugate Ki c) (Subgroup.centralizer ({i} : Set G)) :=
        Unc25G2.isComponentIn_conjugate hKi hcC
      rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
      by_contra hne'
      have hcomm : ⁅Ki, CFSG.conjugate Ki c⁆ = ⊥ :=
        (BenderBranch.eq_or_commute_of_isComponentIn hKi hKic).resolve_left fun h' =>
          hne' h'.symm
      have hKc : CFSG.conjugate N.K c = N.K :=
        BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hKH (N.S_le_H hcS))
      have hKle : N.K ≤ CFSG.conjugate Ki c := by
        calc N.K = CFSG.conjugate N.K c := hKc.symm
          _ ≤ CFSG.conjugate Ki c := BenderBranch.conjugate_mono hKleKi c
      apply hzK1
      apply hZK zK hzKK
      intro y hy
      exact (BenderBranch.commute_of_commutator_eq_bot hcomm (hKleKi hy) (hKle hzKK)).symm
    · intro c hcS hcent
      rw [hSCeq]
      exact ⟨hcS, Subgroup.mem_centralizer_iff.mpr fun k hk => (hcent k (hKleKi hk)).symm⟩
  obtain ⟨e⟩ := sc_dihedral_four hSC2 hUSC hU4 hUexp hC hne hexp4
  have hcardSC : Nat.card N.SC = 8 := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  obtain ⟨D⟩ := exists_a6Datum N hKH h258 h.concl2521
  have hcardS : Nat.card N.S = 256 := by rw [D.card_S hK0, hcardSC]
  have htc : ∀ s ∈ N.SC, t * s = s * t := fun s hs' => hts s (N.SC_le_S hs')
  obtain ⟨v, hvSC, hv2, hv4, hCSC, hsqrt⟩ := exists_V e htSC hf.t_ne_one hf.t_sq htc
  have hHN : ∀ g : G, g * t = t * g → g ∈ Subgroup.normalizer (N.SC : Set G) := by
    intro g hg
    have hgH : g ∈ N.H := by
      rw [h.concl2522.2.1]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hg
    rw [h254.SC_eq]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N.H hgH
  have hVN := mem_normalizer_zpowers_of_sqrt hv2 hsqrt hHN hvSC
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  have hΦz : D.Φ N.z = zb := D.Φ_z hK0 h254 hzS
  have hzS' : ∀ s ∈ N.S, N.z * s = s * N.z := fun s hs' =>
    (Subgroup.mem_centralizer_iff.mp hzS.2 s hs').symm
  have hsq : ∀ w ∈ N.S, w ^ 4 = 1 → w ^ 2 ∈ N.SC ∨ ∃ s ∈ N.SC, w ^ 2 = N.z * s := by
    intro w hwS hw4
    have hwH := N.S_le_H hwS
    have hww : w ^ 2 ∈ N.S := N.S.pow_mem hwS 2
    have hΦ4 : (D.Φ w * D.Φ w) * (D.Φ w * D.Φ w) = 1 := by
      have h1 : D.Φ (w ^ 4) = D.Φ w ^ 4 := D.Φ_pow hwH 4
      rw [hw4, D.Φ_one] at h1
      calc D.Φ w * D.Φ w * (D.Φ w * D.Φ w) = D.Φ w ^ 2 * D.Φ w ^ 2 := by rw [sq]
        _ = D.Φ w ^ 4 := by rw [← pow_add]
        _ = 1 := h1.symm
    have hΦw2 : D.Φ (w ^ 2) = D.Φ w * D.Φ w := by rw [sq, D.mul w hwH w hwH]
    rcases P0_sq_eq_one_or_zb (D.S_mem w hwS) hΦ4 with h1 | h1
    · left
      exact D.mem_SC_of_Φ_eq_one hK0 hww (hΦw2.trans h1)
    · right
      refine ⟨N.z⁻¹ * w ^ 2, D.inv_mul_mem_SC hK0 hzS.1 hww (hΦz.trans (hΦw2.trans h1).symm), ?_⟩
      group
  have hCT : ∀ g ∈ T, g * t = t * g → g ∈ N.S := by
    intro g hgT hg
    have hX : (T ⊓ Subgroup.centralizer ({t} : Set G)) = N.S :=
      hf.sylow.eq_of_le (le_inf N.S_le_T hf.sylow.le) inf_le_right (hT2.to_le inf_le_left)
    have hmem : g ∈ T ⊓ Subgroup.centralizer ({t} : Set G) :=
      ⟨hgT, Subgroup.mem_centralizer_singleton_iff.mpr hg⟩
    rw [hX] at hmem
    exact hmem
  have hVS : Subgroup.zpowers v ≤ N.S := Subgroup.zpowers_le.mpr (N.SC_le_S hvSC)
  have hcases' : ∀ g ∈ T, g⁻¹ * t * g = t ∨ g⁻¹ * t * g = t * N.z := by
    intro g hgT
    refine t_conj_cases hT2 N.S_le_T N.SC_le_S hCT hv2 hv4 hf.t_ne_one hvSC hVN hCSC
      N.tuple.z_sq hzS' hf.not_conj hsq ?_
    intro y hy
    rw [BenderBranch.mem_conjugate_iff] at hy
    have hyT : g * y * g⁻¹ ∈ T := N.S_le_T (hVS hy)
    have e' : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [e']
    exact T.mul_mem (T.mul_mem (T.inv_mem hgT) hyT) hgT
  have hTle : Nat.card T ≤ 2 * Nat.card N.S := card_le_two_mul hCT hcases'
  have hTge : 2 * Nat.card N.S ≤ Nat.card T := by
    rw [← h.concl2513.1.1]
    exact Subgroup.card_le_of_le inf_le_left
  have hT512 : Nat.card T = 512 := by omega
  exact claim_final_contradiction hs.setting hs.noCharTwo D8 hKi hT512

end CFSG.QuasithinUnique

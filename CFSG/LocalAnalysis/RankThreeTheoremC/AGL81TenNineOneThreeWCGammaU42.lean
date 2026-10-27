module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCU42
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCCoreGamma
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenNineOneThreeWCGammaTools
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.Quasithin.Background.SimsF5Omega5
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62FrameScan
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Sp62LocalViso
public import Certificates.Certificate5169

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open CFSG.AGLEmbedding.KFactProofs.Sp62Local CFSG.KGroups.Sp6 CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem mulC_cA_cA : mulC cA cA = oneC := by decide

theorem aV_sq : elt cA * elt cA = 1 := by
  have r := rep_elt (genB_isoB genB_cA')
  exact (r.mul r).eq (by rw [mulC_cA_cA]; exact Rep.one)


theorem kFactTenNineWCGammaU42 :
    ∀ (B : Type) [Group B] [Finite B] (K : Subgroup B) [K.Normal],
      Nonempty (K ≃* V0) →
      ∀ (S : Sylow 3 (MulAut.conjNormal (H := K)).range)
        (A Y : Subgroup (MulAut.conjNormal (H := K)).range), Nat.card A = 3 →
        GammaZeroIn (S : Subgroup (MulAut.conjNormal (H := K)).range) Y →
        ¬ IsWClosedIn (S : Subgroup (MulAut.conjNormal (H := K)).range) A Y := by
  intro B _ _ K _ ⟨e⟩ S A Y hA3 hY hwc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZV : ∀ k : V0, (∀ x : V0, k * x = x * k) → k = 1 := by
    haveI := isSimpleGroup_V0
    have hc : Subgroup.center V0 = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center V0) with h | h
      · exact h
      · exfalso
        have hab : ¬ elt cA * elt cB = elt cB * elt cA := by
          rw [(rep_elt (genB_isoB genB_cA)).comm_iff (rep_elt (genB_isoB genB_cB))]
          intro h
          have := commB_cA_cB
          simp [commB, h] at this
        apply hab
        have := Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top
          (⟨elt cB, elt_mem_Hgen cB_mem_gensV⟩ : V0)) ⟨elt cA, elt_mem_Hgen cA_mem_gensV⟩
        exact congrArg Subtype.val this
    intro k hk
    have : k ∈ Subgroup.center V0 := Subgroup.mem_center_iff.mpr fun x => (hk x).symm
    rw [hc, Subgroup.mem_bot] at this
    exact this
  have hσT : elt cSg ∈ T0 := elt_mem_Hgen (by simp [gensT])
  have hσE : elt cSg ∈ E0 := elt_mem_Hgen (by simp [gensE])
  have hgT : ∀ c ∈ gensT, elt c ∈ T0 := fun c hc => elt_mem_Hgen hc
  set T0V : Subgroup V0 := T0.subgroupOf V0 with hT0V
  have hT0V81 : Nat.card T0V = 81 := by
    rw [hT0V, Nat.card_congr (Subgroup.subgroupOfEquivOfLe T0_le_V0).toEquiv, card_T0]
    norm_num
  have hT0Vidx : ¬ 3 ∣ T0V.index := by
    have h := T0V.card_mul_index
    rw [hT0V81, card_V0] at h
    have : T0V.index = 320 := by omega
    rw [this]
    norm_num
  refine false_of_fuse_gamma (fun k hk => e.injective (by
      rw [map_one]; exact hZV (e k) fun x => by
        have := congrArg e (hk (e.symm x)); simpa using this)) ?_ ?_ S A hA3 Y hY hwc
  ·
    intro _ φ hφ _
    obtain ⟨eP⟩ := nonempty_PSp43_mulEquiv_V0
    have hA : Nat.card (MulAut K) ≤ 51840 :=
      CFSG.Quasithin.SimsF5.card_mulAut_of_mulEquiv_PSp43 (e.trans eP.symm)
    have hK : Nat.card K = 25920 := by rw [Nat.card_congr e.toEquiv, card_V0]
    have hZK : ∀ k : K, (∀ x : K, k * x = x * k) → k = 1 := fun k hk => e.injective (by
      rw [map_one]; exact hZV (e k) fun x => by
        have := congrArg e (hk (e.symm x)); simpa using this)
    exact inner_of_card_le_two_mul hZK (by rw [hK]; omega) φ (m := 1) hφ
  ·
    intro T a haT hoa hcent
    refine gamma_of_fuse_sq haT hoa ?_
    obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow e
      (IsPGroup.of_card (by rw [hT0V81]; norm_num : Nat.card T0V = 3 ^ 4)) hT0Vidx T
    rw [hΦ] at haT hcent ⊢
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp haT
    have ha₀T : (a₀ : H6) ∈ T0 := Subgroup.mem_subgroupOf.mp ha₀
    have hc₀ : ∀ p ∈ T0, p * (a₀ : H6) = (a₀ : H6) * p := by
      intro p hp
      have h := hcent (Φ ⟨p, T0_le_V0 hp⟩) (Subgroup.mem_map_of_mem _
        (Subgroup.mem_subgroupOf.mpr hp))
      simp only [MulEquiv.coe_toMonoidHom] at h
      have h' : (⟨p, T0_le_V0 hp⟩ : V0) * a₀ = a₀ * ⟨p, T0_le_V0 hp⟩ := by
        apply Φ.injective
        rw [map_mul, map_mul]
        exact mul_inv_eq_iff_eq_mul.mp h
      exact congrArg Subtype.val h'
    have ha₀B : (a₀ : H6) ∈ B0 := centralizer_B0_le
      (Subgroup.mem_centralizer_iff.mpr fun p hp => hc₀ p (B0_le_T0 hp))
    obtain ⟨t, ht, hrep⟩ := Hgen_rep tabCheck_B ha₀B
    have hcomm : commB t cSg = true := by
      have h := hc₀ (elt cSg) hσT
      exact beq_iff_eq.2 ((hrep.comm_iff (rep_elt (genB_isoB genB_cSg))).1 h.symm)
    have hZt : inZ t = true := by
      have h := forall_of_allCheck Certificates.certificate5169 t ht
      simpa [hcomm] using h
    have ha₀z := mem_zpowers_z0 hrep hZt
    set y : H6 := elt cA * z0 * (elt cA)⁻¹ with hy
    have hyrep : Rep y (mulC (mulC (mulC (mulC cW0 cW0) cW1) cW2) cW2) :=
      conjC_cA_cZ ▸ rep_conj_elt genB_cA' rep_z0
    have hyT : y ∈ T0 := by
      have r0 := rep_elt (genB_isoB (c := cW0) (by decide))
      have r1 := rep_elt (genB_isoB (c := cW1) (by decide))
      have r2 := rep_elt (genB_isoB (c := cW2) (by decide))
      rw [hyrep.eq ((((r0.mul r0).mul r1).mul r2).mul r2)]
      exact T0.mul_mem (T0.mul_mem (T0.mul_mem (T0.mul_mem (hgT _ (by simp [gensT]))
        (hgT _ (by simp [gensT]))) (hgT _ (by simp [gensT]))) (hgT _ (by simp [gensT])))
        (hgT _ (by simp [gensT]))
    have hy1 : ¬ y ∈ Subgroup.zpowers z0 := by
      intro hm
      rcases zpowers_z0_cases hm with h | h | h
      · exact absurd ((hyrep.eq_iff Rep.one).1 h) (by intro h'; have hz := not_inZ_cAz; simp [inZ, h'] at hz)
      · exact absurd ((hyrep.eq_iff rep_z0).1 h) (by intro h'; have hz := not_inZ_cAz; simp [inZ, h'] at hz)
      · exact absurd ((hyrep.eq_iff rep_z0_sq).1 h) (by intro h'; have hz := not_inZ_cAz; simp [inZ, h'] at hz)
    have hy2 : ¬ y * y ∈ Subgroup.zpowers z0 := by
      intro hm
      have hr := hyrep.mul hyrep
      rcases zpowers_z0_cases hm with h | h | h
      · exact absurd ((hr.eq_iff Rep.one).1 h) (by intro h'; have hz := not_inZ_cAz2; simp [inZ, h'] at hz)
      · exact absurd ((hr.eq_iff rep_z0).1 h) (by intro h'; have hz := not_inZ_cAz2; simp [inZ, h'] at hz)
      · exact absurd ((hr.eq_iff rep_z0_sq).1 h) (by intro h'; have hz := not_inZ_cAz2; simp [inZ, h'] at hz)
    have ha₀ne : (a₀ : H6) ≠ 1 := by
      intro h1
      have : a₀ = 1 := Subtype.ext h1
      rw [this, MulEquiv.coe_toMonoidHom, map_one, orderOf_one] at hoa
      omega
    have hzp : ∀ w : V0, w ∈ Subgroup.zpowers a₀ → (w : H6) ∈ Subgroup.zpowers z0 := by
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      simp only [SubgroupClass.coe_zpow]
      exact Subgroup.zpow_mem _ ha₀z k
    have hsq : Φ aV * Φ aV = 1 := by
      rw [← map_mul, show aV * aV = 1 from Subtype.ext aV_sq, map_one]
    refine ⟨Φ aV, hsq, ?_, ?_⟩
    · refine ⟨aV * a₀ * aV⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · rcases zpowers_z0_cases ha₀z with h | h | h
        · exact absurd h ha₀ne
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, aV, h]
          exact hyT
        · simp only [Subgroup.coe_mul, Subgroup.coe_inv, aV, h]
          have : elt cA * (z0 * z0) * (elt cA)⁻¹ = y * y := by rw [hy]; group
          rw [this]
          exact T0.mul_mem hyT hyT
      · simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv]
    · intro hmem
      have hmem' : aV * a₀ * aV⁻¹ ∈ Subgroup.zpowers a₀ := by
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, Φ.injective ?_⟩
        rw [map_zpow, map_mul, map_mul, map_inv]
        simpa using hk
      have h := hzp _ hmem'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, aV] at h
      rcases zpowers_z0_cases ha₀z with h1 | h1 | h1
      · exact ha₀ne h1
      · rw [h1] at h; exact hy1 h
      · rw [h1] at h
        have : elt cA * (z0 * z0) * (elt cA)⁻¹ = y * y := by rw [hy]; group
        rw [this] at h
        exact hy2 h

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC

module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.L52Cases
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Leaf
public import CFSG.RankThree.PartTwo.Sec21.Hering214EK0Gen
public import CFSG.LieType.Steinberg.CentralExt.GriessClassical
public import TauCeti.GroupTheory.ExponentPrime
public import Certificates.Certificate725108
public import Certificates.Certificate725109

public section

namespace CFSG.SectionRank.QTK.Insp443.L52

open Equiv CFSG.Open CFSG.Certificates CFSG.Literature.GL52 CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit CFSG.SectionRank.QTK.Insp443.PermKit.Native
  CFSG.RankThree.PerfectCover


theorem chkOrb52_true : chkOrb52 () = true := Certificates.certificate725108

theorem chkP52_true : chkP52 () = true := Certificates.certificate725109

theorem conclK_five {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) {x : glCert.originalSubgroup}
    (hxT : Rep 31 x5T (x : Perm (Fin 31))) (hx : orderOf x = 5) {y t : glCert.originalSubgroup}
    (hy : y ∈ L) (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨-, -, -, -, -, -, hc5, -, ho5, -, -⟩ := orb_facts chkOrb52_true
  obtain ⟨ht2, hcomm⟩ := h.bad_facts hy ht hyt
  obtain ⟨cg, hcg, hU⟩ :=
    orbSub_mem_cands hn31 glCert_valid (by norm_num) hxT hx hc5 ho5 hyx ht2 hyt hcomm
  have hUV : orbSub y t ≤ V := orbSub_le (h.le_normalizer hy) ht
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem_candPerms hcg
  rw [length_cands5] at hk
  interval_cases k
  · exact conclK_e16cand chkP52_true h (z := 0) (by norm_num) hU hUV
  · exact conclK_e16cand chkP52_true h (z := 1) (by norm_num) hU hUV

theorem conclK_seven {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) {x : glCert.originalSubgroup}
    (hxT : Rep 31 x7T (x : Perm (Fin 31))) (hx : orderOf x = 7) {y t : glCert.originalSubgroup}
    (hy : y ∈ L) (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) :
    ConclK glCert.originalSubgroup L V MK := by
  obtain ⟨-, -, -, -, -, -, -, hc7, -, ho7, -⟩ := orb_facts chkOrb52_true
  obtain ⟨ht2, hcomm⟩ := h.bad_facts hy ht hyt
  obtain ⟨cg, hcg, hU⟩ :=
    orbSub_mem_cands hn31 glCert_valid (by norm_num) hxT hx hc7 ho7 hyx ht2 hyt hcomm
  have hUV : orbSub y t ≤ V := orbSub_le (h.le_normalizer hy) ht
  have hy1 : y ≠ 1 := fun h1 => hyt (by rw [h1, one_mul, inv_one, mul_one])
  have hxL : x ∈ L := by
    have h1 := TauCeti.zpowers_eq_zpowers_of_mem_zpowers (by norm_num : (7 : ℕ).Prime)
      (by rw [← hx]; exact pow_orderOf_eq_one x) hy1 hyx
    refine (Subgroup.zpowers_le.mpr hy) ?_
    rw [h1]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem_candPerms hcg
  rw [length_cands7] at hk
  obtain ⟨-, -, hcand, -, -⟩ := p_facts chkP52_true
  have hc := hcand k hk
  generalize hkd : kind7.getD k (3, 0, 0) = kd at hc
  obtain ⟨ty, z, w⟩ := kd
  simp only [candOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hz, hw⟩, (⟨rfl, hU0⟩ | ⟨⟨⟨⟨rfl, hl⟩, hsubZ⟩, hsubW⟩, hirr⟩) | ⟨⟨⟨rfl, hl⟩, hsubW⟩, hirr⟩⟩ :=
    hc
  · rw [hU0] at hU
    exact conclK_e16cand chkP52_true h hz hU hUV
  · exact conclK_typeB chkOrb52_true chkP52_true h hxT hxL hk hz hw hkd hl hsubZ hsubW hirr hU hUV
  · exact conclK_typeC chkOrb52_true chkP52_true h hxT hxL hk hw hkd hl hsubW hirr hU hUV

theorem false_thirtyone {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) {x : glCert.originalSubgroup}
    (hxT : Rep 31 x31T (x : Perm (Fin 31))) (hx : orderOf x = 31) {y t : glCert.originalSubgroup}
    (hy : y ∈ L) (hyx : y ∈ Subgroup.zpowers x) (ht : t ∈ V) (hyt : y * t * y⁻¹ ≠ t) : False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ho31⟩ := orb_facts chkOrb52_true
  obtain ⟨ht2, hcomm⟩ := h.bad_facts hy ht hyt
  obtain ⟨cg, hcg, -⟩ :=
    orbSub_mem_cands hn31 glCert_valid (by norm_num) hxT hx (cands := []) rfl ho31 hyx ht2 hyt hcomm
  simp [candPerms] at hcg

theorem conclK_l52 {L V MK : Subgroup glCert.originalSubgroup}
    (h : KConfig glCert.originalSubgroup L V MK) : ConclK glCert.originalSubgroup L V MK := by
  have hne : ⁅V, L⁆ ≠ ⊥ := by rw [← h.eq_commutator]; exact h.ne_bot
  obtain ⟨p, hp, hp5, y, hy, hyk, t, ht, hyt⟩ :=
    exists_pElement_not_comm h.perfect h.le_normalizer hne
  have hpd : p ∣ Nat.card glCert.originalSubgroup := by
    by_contra hpd
    apply hyt
    rw [eq_one_of_pow_of_not_dvd hp hpd hyk, one_mul, inv_one, mul_one]
  have hcard := card_glCert
  rw [hcard] at hpd
  obtain ⟨-, -, -, ho5, ho7, ho31, -⟩ := orb_facts chkOrb52_true
  rcases prime_eq_of_dvd hp hp5 hpd with rfl | rfl | rfl
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨x, hxT, hx⟩ := exists_elt chkOrb52_true List.mem_cons_self (by norm_num) ho5
    obtain ⟨σ, m, -, t₁, ht₁, hxL, hxt⟩ :=
      Alt.exists_conj_of_sylow hx (by rw [hcard]; norm_num) hy hyk ht hyt
    exact ConclK.of_map_mulEquiv σ h.elemAbelian h.le_normalizer
      (conclK_five (h.map_mulEquiv σ) hxT hx hxL (Subgroup.npow_mem_zpowers x m) ht₁ hxt)
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨x, hxT, hx⟩ :=
      exists_elt chkOrb52_true (List.mem_cons_of_mem _ List.mem_cons_self) (by norm_num) ho7
    obtain ⟨σ, m, -, t₁, ht₁, hxL, hxt⟩ :=
      Alt.exists_conj_of_sylow hx (by rw [hcard]; norm_num) hy hyk ht hyt
    exact ConclK.of_map_mulEquiv σ h.elemAbelian h.le_normalizer
      (conclK_seven (h.map_mulEquiv σ) hxT hx hxL (Subgroup.npow_mem_zpowers x m) ht₁ hxt)
  · have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    obtain ⟨x, hxT, hx⟩ := exists_elt chkOrb52_true
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by norm_num) ho31
    obtain ⟨σ, m, -, t₁, ht₁, hxL, hxt⟩ :=
      Alt.exists_conj_of_sylow hx (by rw [hcard]; norm_num) hy hyk ht hyt
    exact (false_thirtyone (h.map_mulEquiv σ) hxT hx hxL (Subgroup.npow_mem_zpowers x m) ht₁
      hxt).elim

theorem glCert_classicalModel : StatedClassicalModel ↥glCert.originalSubgroup .PSL 5 2 1 := by
  refine ⟨⟨Nat.prime_two, le_rfl, ?_⟩, ZMod 2, inferInstance, inferInstance, by simp, ⟨?_⟩⟩
  · show 2 ≤ 5 ∧ (5, 2 ^ 1) ≠ (2, 2) ∧ (5, 2 ^ 1) ≠ (2, 3)
    decide
  · exact (MulEquiv.subgroupCongr glCert_original).trans
      ((MonoidHom.ofInjective glPerm_injective).symm.trans
        (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo (by simp) 5).symm)


theorem card_hopfMultiplier_glCert : Nat.card (hopfMultiplier ↥glCert.originalSubgroup) = 1 := by
  rw [CFSG.RankThree.PartTwo.Sec21.Hering214Even.card_hopfMultiplier_of_row
    (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row glCert_classicalModel)]
  change Nat.gcd 5 (2 ^ 1 - 1) * 1 * (1 * 1) = 1
  norm_num

theorem forK_L52 : ForK (fun S _ => StatedClassicalModel S .PSL 5 2 1) := by
  refine ForK.mono (fun S _ hS => ?_) (forK_of_kConfig (X := ↥glCert.originalSubgroup)
    (by rw [card_hopfMultiplier_glCert]; exact one_dvd 2) fun _ _ _ h => conclK_l52 h)
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hS
  have hF2 : Nat.card F = 2 := by simpa using hF
  exact ⟨((e.trans (CFSG.GH74.Exceptional.statedProjStatedSLEquivOfCardTwo hF2 5)).trans
    (CFSG.GH74.Exceptional.glEquivZModTwoOfCardTwo hF2 5)).trans
    ((MonoidHom.ofInjective glPerm_injective).trans (MulEquiv.subgroupCongr glCert_original.symm))⟩

theorem for_L52 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    For (fun S _ => StatedClassicalModel S .PSL 5 2 1) :=
  For.of_forK h37 h38 h39 forK_L52

theorem for_itemChar2Rank3
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : For ItemChar2Rank3 :=
  Sp6.for_itemChar2Rank3_of_L52 h37 h38 h39 (for_L52 h37 h38 h39)

end CFSG.SectionRank.QTK.Insp443.L52

end

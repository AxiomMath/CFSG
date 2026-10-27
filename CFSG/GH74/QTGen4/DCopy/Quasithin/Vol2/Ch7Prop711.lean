module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsCh7S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch7Prop711Irr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch7Stmt326Lt
public import CFSG.Quasithin.Vol2.Ch7Prop711

public section
namespace CFSG.Quasithin.H13.Prop711

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L I : Subgroup G}

theorem rows_of_eq_F4
    (h325 : Stmt3_2_5_F4) (h329 : Stmt3_2_9C_F4) (h331 : Stmt3_3_1_F4) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (hyp : Hyp7_0_2 G T L I) (hL0 : L = fsuL0 T L) :
    ∃ _ : IsMulCommutative ↥(fsuV T I), Rows7_1_1 T L I := by
  have hL0' : fsuL0 T L = L := hL0.symm
  have hL0c : L = conjClosure L T := hL0
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    intro t ht
    have h := le_normalizer_conjClosure L T ht
    rwa [← hL0c] at h
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  obtain ⟨⟨hab, -⟩, -, hcases⟩ := h325 G T L I hyp.fsu hL0
  refine ⟨hab, ?_⟩
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [← hL0']
    exact le_sup_left.trans hN
  have hTV : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hLI : L ≤ Subgroup.normalizer (I : Set G) := by
    have h := hyp.fsu.irrPlus.2.2.1
    rwa [← hL0c] at h
  have hperfL : ⁅L, L⁆ = L := perfect_of_mem_cComp hyp.fsu.faithful.1.2.1
  have hperf := isPerfect_autOn hLV hperfL
  have hnt : autOn L (fsuV T I) ≠ ⊥ := by
    have hlt := hyp.fsu.irrPlus.2.2.2.2.1
    obtain ⟨i, hi, hiC⟩ := IsConcreteLE.exists_of_lt hlt
    rw [← hL0c] at hiC
    have hiC' : i ∉ Subgroup.centralizer (L : Set G) := fun h => hiC ⟨hi, h⟩
    rw [Subgroup.mem_centralizer_iff] at hiC'
    push Not at hiC'
    obtain ⟨l, hl, hli⟩ := hiC'
    intro hbot
    have hmem : A4.actionOn (fsuV T I) L hLV ⟨l, hl⟩ ∈ autOn L (fsuV T I) :=
      (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hli
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨i, le_fsuV I T hi⟩ : ↥(fsuV T I)) : G))
      hmem
    simp only [A4.actionOn_apply_coe] at h1
    calc l * i = (l * i * l⁻¹) * l := by group
      _ = i * l := by rw [h1]; rfl
  rcases hcases with ⟨hIV, -⟩ | ⟨hIV, -⟩ | ⟨hCI, hlist, ⟨t, ht, htn⟩, hall⟩
  rotate_left 2
  ·
    obtain ⟨-, hsum, hinf, hniso⟩ := hall t ht htn
    have htw := isTwistedPair_of ht hsum hinf hniso
    unfold Rows7_1_1
    rcases hlist with ⟨n, K, _, _, hK, ⟨e⟩, hcI, hnat⟩ | ⟨n, K, _, _, hK, ⟨e⟩, hcI, hnat⟩ |
      ⟨⟨e⟩, hcI, hnat⟩ | ⟨⟨e⟩, hcI, hnat⟩ | ⟨⟨e⟩, hcI, hnat⟩ | ⟨⟨e⟩, hcard⟩
    · iterate 11 right
      left
      exact ⟨n, row711SL3Pair_of hL0' htw hLV hLI hK e hnat⟩
    · iterate 12 right
      left
      exact row711Sp4Pair_of_sp4 hL0' htw hLV hLI hperf hK e hnat
    · iterate 12 right
      left
      exact row711Sp4Pair_of_alt hL0' htw hLV hLI e hnat
    · exact (false_of_lnPair hyp hL0' hV hLV hLI hTL hTV ht hsum hinf (Or.inl rfl) e hnat).elim
    · exact (false_of_lnPair hyp hL0' hV hLV hLI hTL hTV ht hsum hinf (Or.inr rfl) e hnat).elim
    · iterate 13 right
      left
      exact row711S7Pair_of hL0' htw hV hLI hCI hyp.fsu.irrPlus.2.1 hLV e hcard
  all_goals
    refine rows_of_irr_F4 h329 hyp hL0 hIV hV hTL hperf hnt fun U hU => ?_
    obtain ⟨H, hH⟩ := ((h331 G T hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
      hyp.fsu.sylow).2 L hyp.fsu.maximal hyp.fsu.quasisimple).2.2.1
    have hcen := centerOf_eq_bot_of_normal hC58 h317 h37 h38 h39 h3228 hyp hTL hH
    have hCV := fsuV_inf_centralizer_eq_bot hyp.fsu hV hN hcen
    have hCI : I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hCV]
      exact inf_le_inf_right _ (le_fsuV I T)
    have hirr := irr_of_inf_centralizer hyp.fsu hCI
    set J := U.map (fsuV T I).subtype with hJ
    have hJI : J ≤ I := fun x hx => by
      have h : x ∈ conjClosure I T := Subgroup.map_subtype_le U hx
      rw [← hIV] at h
      exact h
    have hJN : fsuL0 T L ≤ Subgroup.normalizer (J : Set G) := by
      rw [hL0']
      intro l hl
      refine mem_normalizer_of_conj_mem fun v hv => ?_
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      have h1 := hU (A4.actionOn (fsuV T I) L hLV ⟨l, hl⟩)
        ((A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩) u hu
      exact ⟨_, h1, A4.actionOn_apply_coe hLV ⟨l, hl⟩ u⟩
    rcases hirr J hJI hJN with h | h
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective _ (fsuV T I).subtype_injective).mp h
    · right
      rw [eq_top_iff]
      intro v _
      have hv : (v : G) ∈ J := by
        have h1 : (v : G) ∈ conjClosure I T := v.2
        rw [← hIV] at h1
        rw [h]
        exact h1
      obtain ⟨u, hu, huv⟩ := Subgroup.mem_map.mp hv
      rw [show v = u from Subtype.ext huv.symm]
      exact hu

theorem stmt7_1_1_of_F4
    (h325 : Stmt3_2_5_F4) (h326 : Stmt3_2_6Lt_F4) (h329 : Stmt3_2_9C_F4) (h331 : Stmt3_3_1_F4)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h3228 : Stmt3_2_2_eight) : Stmt7_1_1_F4 := by
  intro G _ _ T L I hyp
  rcases eq_or_lt_of_le (le_fsuL0 T L) with hL0 | hL0
  · exact rows_of_eq_F4 h325 h329 h331 hC58 h317 h37 h38 h39 h3228 hyp hL0
  · rcases h326 G T L I hyp.fsu hL0 with ⟨hab, -, -, hrows⟩ | h3
    · refine ⟨hab, ?_⟩
      unfold Rows7_1_1
      rcases hrows with h | h
      · iterate 15 right
        exact h
      · iterate 14 right
        left
        exact h
    · exact (hyp.notThree ⟨hL0, h3⟩).elim

end CFSG.Quasithin.H13.Prop711

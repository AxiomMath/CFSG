module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Producer134
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135A6
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135L3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S135U3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneLemma3

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem three_fsu_of_1332_F4 (h : Stmt13_3_2_F4) : Stmt13_3_2_three_fsu_F4 := by
  intro G _ _ T L hH K hK
  refine ⟨(h G T L hH K hK).2.2.1.1, fun V hV => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := (h G T L hH K hK).2.2.1.2 V hV
  exact ⟨h1, h2, h3⟩

theorem stmt13_3_5_of_F4
    (h1332 : Stmt13_3_2_F4) (h12213 : Stmt12_2_13_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : A5.Stmt13_2_7_F4) (h132A5 : Stmt13_3_2_three_A5_F4) : A6.Stmt13_3_5_F4 := by
  intro G _ _ T L V hH hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTL, hmax, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  have hA := autOn_ne_bot_of_not_le_centralizer hLV (not_le_centralizer_of_irr hV)
  refine ⟨fun h1 v hv hv1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  ·
    have hc : Nat.card (autOn L V) = 168 ∨ Nat.card (autOn L V) = 6048 := by
      rcases h1 with ⟨⟨e⟩⟩ | hu
      · exact Or.inl (by rw [Nat.card_congr e.toEquiv, HSType.card_SL_three_two])
      · exact Or.inr (card_of_lieModel_PSU_three_three hu)
    rcases hmod with ⟨⟨π, hπ, -⟩, -⟩ | ⟨⟨π, hπ, -⟩, -⟩ | ⟨-, -, ⟨π, hπ, -⟩⟩ | ⟨hlin, hnat, -⟩ |
        ⟨hu, -, -⟩
    · rw [card_autOn_of_alt (by norm_num) hA π hπ] at hc
      norm_num [Nat.factorial] at hc
    · rw [card_autOn_of_alt (by norm_num) hA π hπ] at hc
      norm_num [Nat.factorial] at hc
    · rw [card_autOn_of_alt (by norm_num) hA π hπ] at hc
      norm_num [Nat.factorial] at hc
    · exact l32_centralizer_not_le_F4 h12213 hH (hyp1281One_of_F4 h1332 hH hV hlin hnat) hv hv1
    · obtain ⟨z, hF⟩ := u3_frame_of_irrPlus_F4 h1332 hH hu hV
      exact u3_centralizer_not_le_F4 h1332 h12213 hH hu hV hF hv hv1
  ·
    have hA5 := a5Quot_of_autOn hLV h5 h2
    obtain ⟨V', ⟨S'⟩⟩ := A5.exists_setting_F4 (stmt13_3_2_two_of_stmt13_3_2_F4 h1332)
      (three_fsu_of_1332_F4 h1332) h132A5 hH hA5
    have hHZ : ∀ H : Subgroup G, IsHStar T (normalizer (L : Set G)) H →
        H ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
      fun H hH' => h1327 G T L V' S' H hH'
    refine ⟨hHZ, fun z hz hzM => ?_⟩
    obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
      (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hmax hfsu.quasisimple
    rw [(hyp1223_of_fsu hH hTL hmax hfsu hV).conjClosure_eq] at hHs
    apply hHs.2.1
    refine le_trans (fun x hx => ?_) hzM
    have hzZ : z ∈ quasithinOmegaOneCenter T := by
      have : z ∈ fsuV1 T V := hz ▸ mem_zpowers z
      exact this.2
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.1 (hHZ H hHs hx)) z hzZ).symm
  ·
    have h360 : Nat.card (autOn L V) = 360 := by
      obtain ⟨e⟩ := h3
      rw [Nat.card_congr e.toEquiv, A6.card_alt6]
    rcases hmod with ⟨⟨π, hπ, -⟩, -⟩ | ⟨hnat, hZV⟩ | ⟨-, hc2, -⟩ | ⟨hlin, -, -⟩ | ⟨hu, -, -⟩
    · rw [card_autOn_of_alt (by norm_num) hA π hπ] at h360
      norm_num [Nat.factorial] at h360
    · obtain ⟨S⟩ := setting4_of_case_b_F4 h1332 hH hV hZV hnat
      refine ⟨S.z, S.mem_V1_iff.2 (Or.inr rfl), fun hz => S.z_ne_one ?_,
        setting4_not_centralizer_le_F4 h12213 S⟩
      have h1 : S.z ∈ V ⊓ centralizer (L : Set G) := ⟨S.z_mem_V, hz⟩
      rw [hZV] at h1
      exact (mem_bot).1 h1
    · have hZV : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
        intro h
        rw [h, card_bot] at hc2
        norm_num at hc2
      obtain ⟨S⟩ := A6.exists_setting134_F4 h1332 hH hV hZV
      exact setting134_exists_v1_F4 h12213 S hc2
    · exact (not_five_dvd_card_autOn hlin hLV (by rw [h360]; norm_num)).elim
    · exact (not_five_dvd_card_autOn_U3 hu hLV (by rw [h360]; norm_num)).elim

theorem stmt13_3_6_of_F4
    (h1332 : Stmt13_3_2_F4) (h1222 : Stmt12_2_2_F4) (h12213 : Stmt12_2_13_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : A5.Stmt13_2_7_F4) (h132A5 : Stmt13_3_2_three_A5_F4) : A6.Stmt13_3_6_F4 := by
  intro G _ _ T L V hH hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h5, ⟨hTL, hmax, -, -⟩, ⟨-, hall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, -, hfsu, hab, hmod⟩ := hall V hV
  have hLV : L ≤ normalizer (V : Set G) := hV.2.2.1
  rcases hmod with ⟨hnat5, -⟩ | ⟨hnat, hZV⟩ | ⟨hc5, hc2, hreal⟩ | ⟨hlin, hnat, -⟩ | ⟨hu, -, -⟩
  ·
    left
    have hA5 := a5Quot_of_autOn hLV h5
      (A6.nonempty_mulEquiv_of_realizes (A6.altDn_faithful (by norm_num)) hnat5)
    obtain ⟨V', ⟨S'⟩⟩ := A5.exists_setting_F4 (stmt13_3_2_two_of_stmt13_3_2_F4 h1332)
      (three_fsu_of_1332_F4 h1332) h132A5 hH hA5
    obtain ⟨-, -, ⟨H, hHs⟩, -, -⟩ :=
      (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hmax hfsu.quasisimple
    rw [(hyp1223_of_fsu hH hTL hmax hfsu hV).conjClosure_eq] at hHs
    have hHZ := h1327 G T L V' S' H hHs
    intro hle
    apply hHs.2.1
    refine le_trans ?_ hle
    exact hHZ.trans ((centralizer_le (inf_le_right :
      fsuV1 T V ≤ quasithinOmegaOneCenter T)).trans (centralizer_le_normalizer _))
  ·
    left
    obtain ⟨S⟩ := setting4_of_case_b_F4 h1332 hH hV hZV hnat
    show ¬ normalizer (fsuV1 T V : Set G) ≤ normalizer (L : Set G)
    rw [S.normalizer_V1]
    exact setting4_not_centralizer_le_F4 h12213 S
  ·
    right
    refine ⟨fun h => ?_,
      A6.nonempty_mulEquiv_of_realizes (A6.altCoreModel_faithful (by norm_num)) hreal,
      hab, hc5, hreal⟩
    rw [h, card_bot] at hc2
    norm_num at hc2
  ·
    left
    have h := hyp1281One_of_F4 h1332 hH hV hlin hnat
    exact lemma12_8_3_four_F4 h12213 h (l32_isTSub_V1_F4 h1222 h)
  ·
    left
    exact u3_g1_not_le_F4 h1332 h12213 hH hu hV

end CFSG.Quasithin.H13.U3

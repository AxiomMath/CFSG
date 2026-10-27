module

public import CFSG.Quasithin.H13.L32A708a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk6

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem mem_l1_star_of_cube_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (hC : IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    {y : ↥H ⧸ CFSG.pCore 2 ↥H} (hy : y ∈ oTwoUpper ⊤) (hy3 : y ^ 3 = 1) :
    y ∈ modO2Image H (l1 T L V) := by
  have := hC
  rcases Nat.prime_three.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hy3) with h | h
  · rw [orderOf_eq_one_iff.mp h]
    exact one_mem _
  · have he : Subgroup.zpowers y = modO2Image H (l1 T L V) :=
      eq_of_le_isCyclic (Subgroup.zpowers_le.mpr hy)
        (modO2Image_oTwoUpper_le (Setting147.l1H' S))
        (by rw [Nat.card_zpowers, h, Setting147.card_l1_star_F4 S h1222 h1332 h1334 hHL])
    rw [← he]
    exact Subgroup.mem_zpowers y

theorem R1_le_O2H_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4)
    (hC : IsCyclic ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H))))
    (h3 : IsPGroup 3 ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) :
    pCoreOf 2 (l1 T L V ⊔ T) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hC
  have hHL := Setting147.H_le_N_l1_F4 S h1332 (Setting147.l1_star_normal S hC)
  have hR := Setting147.R1_star_eq_F4 S h1222 h1332 h1334 hHL
  have hTH := Setting147.TH' S
  have hRT := Setting147.R1_le_T S

  have hcent : ∀ r : ↥H, (r : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) →
      ∀ p ∈ oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)),
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) r * p * (QuotientGroup.mk' (CFSG.pCore 2 ↥H) r)⁻¹ =
          p := by
    intro r hr p hp
    have hrs : QuotientGroup.mk' (CFSG.pCore 2 ↥H) r ∈
        modO2Image H (pCoreOf 2 (l1 T L V ⊔ T)) := mem_modO2Image'.mpr ⟨r, hr, rfl⟩
    rw [hR] at hrs
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨r, hRT hr⟩
    have hk' : (r : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hkH : r ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
    refine comm_of_fix_three (fun a ha b hb => congrArg Subtype.val
      (mul_comm' (⟨a, ha⟩ : ↥(oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)))) ⟨b, hb⟩)) h3
      (fun z hz => normal_oTwoUpper_top.conj_mem z hz _) (m := k)
      (by rw [← map_pow, hkH, map_one]) (fun y hy hy3 => ?_) hp
    have hyl := Setting147.mem_l1_star_of_cube_F4 S h1222 h1332 h1334 hHL hC hy hy3
    have hc := Subgroup.mem_centralizer_iff.mp hrs.2 y hyl
    rw [← hc]
    group

  have hON : oTwoUpper H ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun r hr => ?_
    have hkH : k ∈ H := oTwoUpper_le H hk
    have hrH : r ∈ H := hTH (hRT hr)
    have hkP : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ ∈ oTwoUpper ⊤ :=
      modO2Image_oTwoUpper_le (X := H) (oTwoUpper_le H) (mem_modO2Image'.mpr ⟨⟨k, hkH⟩, hk, rfl⟩)
    have h1 := hcent ⟨r, hrH⟩ hr _ hkP
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ *
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ := by
      calc QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ =
          QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨k, hkH⟩ *
            (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩)⁻¹ *
            QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hrH⟩ := by group
        _ = _ := by rw [h1]
    have h3 := mem_O2H_of_commute ⟨k, hkH⟩ ⟨r, hrH⟩ h2
    rw [show k * r * k⁻¹ = (k * r * k⁻¹ * r⁻¹) * r by group]
    exact mul_mem (Setting147.O2H_le_R1 S h3) hr
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := fun t ht =>
    le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_right ht)
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) := by
    rw [← F112W.sup_oTwoUpper_eq_of_isSylowTwoOf
      (isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH)]
    exact sup_le hTN hON
  exact le_pCoreOf_of_le_normalizer 2 (hRT.trans hTH) hHN (pCoreOf_isPGroup 2 _)

theorem false_of_Uγ_le_F4 (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) (s : F8Setup T V L H γ γ' g)
    (hU : F8.Uγ V H (g : G) ≤ pCoreOf 2 H) : False := by
  refine not_le_of_gt (Dγ_lt_Uγ_F4 S hF h1222 h1332 h1334 hHL s) fun w hw => ?_
  obtain ⟨-, hN, hc⟩ := mem_centralizerMod.mp (hF.pCoreOf_eq_centralizerMod.le (hU hw))
  exact mem_centralizerMod.mpr ⟨hw, hN, hc⟩

end Setting147

theorem lemma14_7_8_of_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_8_F4 := by
  rintro G _ _ T L V H S ⟨hC, h3⟩
  have hF : HypF98 T V L (fsuV1 T V) V H :=
    Setting147.hypF98_F4 S (stmt13_3_2_two_of_F4 h1332) (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  exact Setting147.false_of_Uγ_le_F4 S hF h1222 h1332 h1334
    (Setting147.H_le_N_l1_F4 S h1332 (Setting147.l1_star_normal S hC)) s
    (Setting147.Uγ_le_O2H hF s (Setting147.R1_le_O2H_F4 S h1222 h1332 h1334 hC h3))

end CFSG.Quasithin.H13.L32A

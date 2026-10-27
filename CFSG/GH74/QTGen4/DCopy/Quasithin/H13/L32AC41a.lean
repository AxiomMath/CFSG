module

public import CFSG.Quasithin.H13.L32AC41a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC36g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem relIndex_T_l1T_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) : T.relIndex (l1 T L V ⊔ T) = 3 := by
  have h := relIndex_TK_F4 (K := ⊤) h1222 h1332 h1334 S le_top
  rwa [inf_top_eq] at h

theorem card_l1T_mod_dvd_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) : ∃ a : ℕ, Nat.card (modO2Image H (l1 T L V ⊔ T)) ∣ 3 * 2 ^ a := by
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  obtain ⟨a, ha⟩ := (S.hyp.fsu.sylow.1 : IsPGroup 2 ↥T).exists_card_eq
  refine ⟨a, ?_⟩
  have h1 : Nat.card (modO2Image H (l1 T L V ⊔ T)) ∣ Nat.card ↥(l1 T L V ⊔ T) := by
    have := Subgroup.card_map_dvd (H := (l1 T L V ⊔ T).subgroupOf H)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLTH).toEquiv] at this
  have h2 := Subgroup.relIndex_mul_card T (l1 T L V ⊔ T)
  rw [inf_eq_left.mpr (le_sup_right : T ≤ l1 T L V ⊔ T), relIndex_T_l1T_F4 h1222 h1332 h1334 S,
    ha] at h2
  rwa [h2]

theorem l1T_le_normalizer_szS1_F4 (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : l1 T L V ≤ K) :
    modO2Image H (l1 T L V ⊔ T) ≤
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  set S₁ := szS1 T H K with hS₁
  set Y₀ := modO2Image H (l1 T L V ⊔ T) ⊓ Kb with hY₀
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hS := isSylowIn_szS1_of S hK
  have hSY : S₁ ≤ Y₀ :=
    le_inf (inf_le_left.trans (Subgroup.map_mono fun x hx =>
      ((le_sup_right : T ≤ l1 T L V ⊔ T) hx : (x : G) ∈ l1 T L V ⊔ T))) inf_le_right
  have hYK : Y₀ ≤ Kb := inf_le_right

  have hodd : Odd (S₁.relIndex Y₀) := by
    have hmul := Subgroup.relIndex_mul_relIndex S₁ Y₀ Kb hSY hYK
    have h2 : ¬ 2 ∣ S₁.relIndex Kb := hS.not_dvd_relIndex
    refine Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun hd => h2 ?_)
    rw [← hmul]
    exact Dvd.dvd.mul_right hd _
  have hdvd : ∃ a : ℕ, S₁.relIndex Y₀ ∣ 3 * 2 ^ a := by
    obtain ⟨a, ha⟩ := card_l1T_mod_dvd_F4 h1222 h1332 h1334 S
    refine ⟨a, (Dvd.intro _ (Subgroup.relIndex_mul_card S₁ Y₀)).trans
      ((Subgroup.card_dvd_of_le inf_le_left).trans ha)⟩
  obtain ⟨a, ha⟩ := hdvd
  have hY0 : Y₀ ≤ Subgroup.normalizer (S₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rcases eq_one_or_three_of_odd_dvd hodd ha with h1 | h3
    · exact (Subgroup.relIndex_eq_one.mp h1).trans Subgroup.le_normalizer
    · obtain ⟨hqX, hoddX, hLieX⟩ := kst_props hK hq hLie
      have h := hN1 (↥Kb) n hn hqX hoddX hLieX (S₁.subgroupOf Kb) (Y₀.subgroupOf Kb)
        (isSylowTwoOf_subgroupOf hS) (fun x hx => hSY hx)
        (by rw [Subgroup.relIndex_subgroupOf hYK]; exact h3)
      intro y hy
      exact (mem_normalizer_subgroupOf_iff hS.le ⟨y, hYK hy⟩).mp
        (h (show (⟨y, hYK hy⟩ : ↥Kb) ∈ Y₀.subgroupOf Kb from hy))

  set P := ((Subgroup.normalizer (S₁ : Set (↥H ⧸ CFSG.pCore 2 ↥H))).comap
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype with hP
  have hl1P : l1 T L V ≤ P := fun y hy => Subgroup.mem_map.mpr ⟨⟨y, hl1H hy⟩,
    hY0 ⟨mem_modO2Image'.mpr ⟨⟨y, hl1H hy⟩, Subgroup.mem_sup_left hy, rfl⟩,
      mem_modO2Image'.mpr ⟨⟨y, hl1H hy⟩, hl1K hy, rfl⟩⟩, rfl⟩
  have hTP : T ≤ P := by
    intro r hr
    refine Subgroup.mem_map.mpr ⟨⟨r, hTH hr⟩, ?_, rfl⟩
    have hT : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨r, hTH hr⟩ ∈
        Subgroup.normalizer (modO2Image H T : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Subgroup.le_normalizer (mem_modO2Image'.mpr ⟨⟨r, hTH hr⟩, hr, rfl⟩)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hT, mk_mem_normalizer hKH (hKn (hTH hr))⟩
  intro z hz
  obtain ⟨w, hw, rfl⟩ := mem_modO2Image'.mp hz
  obtain ⟨w', hw', hww⟩ := Subgroup.mem_map.mp (sup_le hl1P hTP hw)
  have : w' = w := Subtype.ext hww
  rw [← this]
  exact hw'

end CFSG.Quasithin.H13.L32A.C

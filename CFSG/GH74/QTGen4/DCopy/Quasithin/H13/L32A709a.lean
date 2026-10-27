module

public import CFSG.Quasithin.H13.L32A709a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A74
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk5
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk6

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting147

variable {T L V H : Subgroup G}

theorem setting_Y0_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) {Y₀ : Subgroup G} (hY₀H : Y₀ ≤ H) (hl1Y₀ : l1 T L V ≤ Y₀)
    (hY₀M : ¬ Y₀ ≤ Subgroup.normalizer (L : Set G)) : Setting147 G T L V (Y₀ ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  have hH'H : Y₀ ⊔ T ≤ H := sup_le hY₀H (Setting147.TH' S)
  have hV1T : fsuV1 T V ≤ T := (inf_le_left : fsuV1 T V ≤ V).trans S14.VT_F4
  have hV1O : fsuV1 T V ≤ pCoreOf 2 (Y₀ ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hV1T.trans le_sup_right) (hH'H.trans S.hz.2.1)
      (S.hyp.fsu.sylow.1.to_le hV1T)
  refine ⟨S.hyp, ⟨⟨sup_le_sup_right hl1Y₀ T, fun h => ?_⟩, hH'H.trans S.hz.2.1,
    fun h => hY₀M (le_sup_left.trans h)⟩⟩
  have h0 : fsuV1 T V ≤ ⊥ := by
    rw [← h]
    exact hV1O
  have h2 := S14.card_V1_F4
  rw [le_bot_iff.mp h0, Subgroup.card_bot] at h2
  omega

theorem false_of_Y0_F4 (h78 : Lemma14_7_8_F4) (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {Y₀ : Subgroup G} (hY₀H : Y₀ ≤ H)
    (hl1Y₀ : l1 T L V ≤ Y₀) (hTY₀ : T ≤ Subgroup.normalizer (Y₀ : Set G))
    (e : ↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀ ≃* Multiplicative (ZMod 9))
    (hY₀M : ¬ Y₀ ≤ Subgroup.normalizer (L : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have S' := setting_Y0_F4 S h1222 h1332 h1334 hY₀H hl1Y₀ hY₀M

  have hO : pCoreOf 2 Y₀ ≤ pCoreOf 2 (Y₀ ⊔ T) := le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 Y₀).trans le_sup_left)
    (sup_le (le_normalizer_pCoreOf 2 Y₀) (hTY₀.trans (normalizer_le_normalizer_pCoreOf 2 Y₀)))
    (pCoreOf_isPGroup 2 Y₀)

  let φ : ↥Y₀ →* ↥(Y₀ ⊔ T) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ T) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ T))).comp (Subgroup.inclusion le_sup_left)
  have hker : (pCoreOf 2 Y₀).subgroupOf Y₀ ≤ φ.ker := by
    intro q hq
    rw [MonoidHom.mem_ker]
    simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf]
    exact hO (Subgroup.mem_subgroupOf.mp hq)
  let φ' := QuotientGroup.lift ((pCoreOf 2 Y₀).subgroupOf Y₀) φ hker

  have hle : oTwoUpper (⊤ : Subgroup (↥(Y₀ ⊔ T) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ T))) ≤ φ'.range := by
    have h1 : oTwoUpper (⊤ : Subgroup (↥(Y₀ ⊔ T) ⧸ CFSG.pCore 2 ↥(Y₀ ⊔ T))) =
        (oTwoUpper (⊤ : Subgroup ↥(Y₀ ⊔ T))).map
          (QuotientGroup.mk' (CFSG.pCore 2 ↥(Y₀ ⊔ T))) := by
      rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have h2 : (oTwoUpper (⊤ : Subgroup ↥(Y₀ ⊔ T))).map (Y₀ ⊔ T).subtype =
        oTwoUpper (Y₀ ⊔ T) := by
      rw [← oTwoUpper_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h3 : oTwoUpper (Y₀ ⊔ T) ≤ Y₀ := oTwoUpper_sup_le_two' S.hyp.fsu.sylow.1 hTY₀
    rw [h1]
    rintro _ ⟨h, hh, rfl⟩
    have hh' : (h : G) ∈ oTwoUpper (Y₀ ⊔ T) := by
      rw [← h2]
      exact ⟨h, hh, rfl⟩
    refine ⟨QuotientGroup.mk ⟨h, h3 hh'⟩, ?_⟩
    rw [QuotientGroup.lift_mk]
    rfl

  have hQc : IsCyclic (↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀) :=
    isCyclic_of_surjective e.symm e.symm.surjective
  have hQ3 : IsPGroup 3 (↥Y₀ ⧸ (pCoreOf 2 Y₀).subgroupOf Y₀) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    norm_num
  have hRc : IsCyclic ↥φ'.range :=
    isCyclic_of_surjective φ'.rangeRestrict φ'.rangeRestrict_surjective
  have hR3 : IsPGroup 3 ↥φ'.range :=
    hQ3.of_surjective φ'.rangeRestrict φ'.rangeRestrict_surjective
  exact h78 G T L V (Y₀ ⊔ T) S' ⟨Subgroup.isCyclic_of_le hle, hR3.to_le hle⟩

end Setting147

theorem lemma14_7_9_of_F4 (h520 : Lemma14_5_20_F4) (h78 : Lemma14_7_8_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_9_F4 := by
  intro G _ _ T L V H S Y p hp hYO hYH hHY hYp hlt
  rcases h520 G T L V H S Y p hp hYH hHY hYp with h | ⟨rfl, hl1Y, hcases⟩
  · exact absurd h.symm hlt.ne
  refine ⟨rfl, ?_⟩
  rcases hcases with ⟨hsup, hHl1⟩ | ⟨hP, h1, h2, hW⟩ | ⟨-, Y₀, hY₀H, hl1Y₀, hTY₀, ⟨e⟩, hY₀M⟩
  · refine Or.inl (le_antisymm ?_ hl1Y)
    calc Y = oTwoUpper Y := hYO.symm
      _ = oTwoUpper (l1 T L V ⊔ pCoreOf 2 Y) := by rw [hsup]
      _ ≤ l1 T L V := oTwoUpper_sup_le_two' (pCoreOf_isPGroup 2 Y)
          (((pCoreOf_le 2 Y).trans hYH).trans hHl1)
  · refine Or.inr ⟨hP, ?_, h1, hW, h2⟩
    rw [h1]
    exact oTwoUpper_sup_pCoreOf_eq (pCoreOf_le_o2z Y) fun k hk => hYp k (o2z_le Y hk)
  · exact (Setting147.false_of_Y0_F4 h78 S h1222 h1332 h1334 hY₀H hl1Y₀ hTY₀ e hY₀M).elim

end CFSG.Quasithin.H13.L32A

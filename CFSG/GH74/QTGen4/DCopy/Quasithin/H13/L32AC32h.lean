module

public import CFSG.Quasithin.H13.L32AC32h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L1332
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Idx

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem exists_TL_not_triv_F4 (h : Hyp147 G T L V) (h1332 : Stmt13_3_2_F4)
    (S14 : L32NSet14.Setting_F4 G T L V V₂) :
    ∃ t ∈ T, t ∈ L ∧ t ∉ L32NSet14.trivSub V (fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    refine L32A.normalizer_le_normalizer_L_F4 h (stmt13_3_2_two_of_F4 h1332) ?_ ?_
      (sup_le S14.LV_F4 S14.TV_F4)
    · intro hV
      have := S14.card_V_F4
      rw [hV, Subgroup.card_bot] at this
      omega
    · exact IsPGroup.of_card (n := 3) (by rw [S14.card_V_F4]; norm_num)
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨y, hyL, hy2, hyz, hya⟩ := S14.exists_swap_F4 hz ha haV hb hbV
  have hyX : y ∈ L32NSet14.nX T V := ⟨S14.LV_F4 hyL, S14.mem_g1_F4 hz hz1 hyz⟩
  have hy_not : y ∉ L32NSet14.trivSub V (fsuV1 T V) := fun h => by
    have h1 := h.2.2 a (S14.hV2.2.1 ha)
    rw [hya] at h1
    apply hbV
    have h2 := mul_mem (S14.hV2.1 h1) ha
    rwa [inv_mul_cancel_right] at h2
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y ^ 2 ^ m = 1 := by
    have hc : y ^ 2 ∈ pCoreOf 2 L := by
      rw [← S14.cent_eq_F4]
      exact ⟨L.pow_mem hyL 2, hy2⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hc⟩
    refine ⟨k + 1, ?_⟩
    have := congrArg Subtype.val hk
    rw [Subgroup.coe_pow] at this
    rw [pow_succ', pow_mul]
    exact this
  have hTp : IsPGroup 2 ↥(T.subgroupOf (L32NSet14.nX T V)) := by
    rintro ⟨t, ht⟩
    obtain ⟨k, hk⟩ := S14.hH.sylow.1 ⟨t, Subgroup.mem_subgroupOf.mp ht⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hTidx : ¬ 2 ∣ (T.subgroupOf (L32NSet14.nX T V)).index := by
    have h1 := Subgroup.relIndex_mul_index S14.T_le_X_F4
    intro h2
    apply S14.hH.sylow.2
    rw [← h1]
    exact Dvd.dvd.mul_right h2 _
  have hyp : IsPGroup 2 ↥(Subgroup.zpowers (⟨y, hyX⟩ : ↥(L32NSet14.nX T V))) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨m, Subtype.ext ?_⟩
    have hm' : (⟨y, hyX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ m = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hm)
    show ((⟨y, hyX⟩ : ↥(L32NSet14.nX T V)) ^ n) ^ 2 ^ m = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hm', one_zpow]
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(L32NSet14.nX T V) Q (hTp.toSylow hTidx)
  have hmem : g * ⟨y, hyX⟩ * g⁻¹ ∈ g • Q := L32NSet14.mem_smul_sylow.mpr (by
    rw [show g⁻¹ * (g * ⟨y, hyX⟩ * g⁻¹) * g = ⟨y, hyX⟩ by group]
    exact hQ (Subgroup.mem_zpowers _))
  rw [hg] at hmem
  have hmem' : g * ⟨y, hyX⟩ * g⁻¹ ∈ T.subgroupOf (L32NSet14.nX T V) := hmem
  refine ⟨(g : G) * y * (g : G)⁻¹, Subgroup.mem_subgroupOf.mp hmem',
    (Subgroup.mem_normalizer_iff.mp (hNL g.2.1) y).mp hyL, fun h => hy_not ?_⟩
  have := L32NSet14.conj_mem_trivSub (inv_mem g.2.1) (inv_mem g.2.2) h
  rwa [show (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G)⁻¹⁻¹ = y by group] at this

theorem comm_pow_two_F4 (S14 : L32NSet14.Setting_F4 G T L V V₂) {t w : G} (htL : t ∈ L)
    (htX : t ∈ L32NSet14.nX T V) (hwL : w ∈ Subgroup.normalizer (L : Set G))
    (hw : w ∈ L32NSet14.trivSub V (fsuV1 T V)) :
    ∃ m : ℕ, (t * w * t⁻¹ * w⁻¹) ^ 2 ^ m = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcL : t * w * t⁻¹ * w⁻¹ ∈ L := by
    have h1 : w * t⁻¹ * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwL _).mp (inv_mem htL)
    have e : t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem htL h1
  have hct : t * w * t⁻¹ * w⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) :=
    mul_mem (L32NSet14.conj_mem_trivSub htX.1 htX.2 hw) (inv_mem hw)
  have hc : (t * w * t⁻¹ * w⁻¹) ^ 2 ∈ pCoreOf 2 L := by
    rw [← S14.cent_eq_F4]
    exact ⟨L.pow_mem hcL 2, S14.sq_mem_cent_F4 hct⟩
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hc⟩
  refine ⟨k + 1, ?_⟩
  have := congrArg Subtype.val hk
  rw [Subgroup.coe_pow] at this
  rw [pow_succ', pow_mul]
  exact this

theorem comm_x_pow_two_F4 (S14 : L32NSet14.Setting_F4 G T L V V₂) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {t : G} (htT : t ∈ T)
    (htn : t ∉ L32NSet14.trivSub V (fsuV1 T V)) :
    ∃ m : ℕ, (t * x * t⁻¹ * x) ^ 2 ^ m = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4
  have htX := S14.T_le_X_F4 htT
  have hxX := S14.L1_le_X_F4 hxL
  have hψt : ψ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hψ _).mp h)
  have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S14.hH.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := by
    intro h
    have hxt := (hψ _).mp h
    have hle : V ≤ fsuV1 T V := fun v hv => hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
    have := Subgroup.card_le_of_le hle
    rw [S14.card_V_F4, S14.card_V1_F4] at this
    omega
  have hψx3 : ψ ⟨x, hxX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [this, map_one]
  have hkL : t * x * t⁻¹ * x ∈ L₁Of L (fsuV1 T V) :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (S14.T_Lp_F4 htT) x).mp hxL) hxL
  have hkt : t * x * t⁻¹ * x ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have e : (⟨t * x * t⁻¹ * x, S14.L1_le_X_F4 hkL⟩ : ↥(L32NSet14.nX T V)) =
        ⟨t, htX⟩ * ⟨x, hxX⟩ * ⟨t, htX⟩⁻¹ * ⟨x, hxX⟩ := rfl
    refine (hψ ⟨t * x * t⁻¹ * x, S14.L1_le_X_F4 hkL⟩).mp ?_
    rw [e, map_mul, map_mul, map_mul, map_inv]
    exact sl2_inv_conj _ _ hψt hψt2 hψx hψx3
  have hO := mem_pCoreOf_of_triv_F4 S14 hxL hfpf hkL hkt
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))) ⟨_, hO⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem pCoreOf_le_trivSub_F4 {H : Subgroup G} (S : Setting147 G T L V H)
    (S14 : L32NSet14.Setting_F4 G T L V V₂) :
    pCoreOf 2 H ≤ L32NSet14.trivSub V (fsuV1 T V) := by
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hTH : T ≤ H := Setting147.TH' S
  have hQT : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le S.hyp hTH
  have hLTH : L₁Of L (fsuV1 T V) ⊔ T ≤ H := by
    rw [hl1]
    exact sup_le (Setting147.l1H' S) hTH
  intro q hq
  exact S14.pCoreOf_L1T_le_F4 (C58.pCoreOf_inf_le hLTH ⟨hq, Subgroup.mem_sup_right (hQT hq)⟩)

end CFSG.Quasithin.H13.L32A.C

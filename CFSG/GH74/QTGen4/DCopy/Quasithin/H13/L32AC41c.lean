module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC32h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC33e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC41b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem lemma14_7_41_two_F4 (hN1 : LieSylowOver3) (hN2 : LieBorelInvert3) (h29 : Thm14_7_29_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : l1 T L V ≤ K) :
    IsPSL 2 2 2 (cStar K ⧸ Subgroup.center (cStar K)) ∨
      IsPSU 3 2 3 (cStar K ⧸ Subgroup.center (cStar K)) ∨
        IsPSL 3 2 2 (cStar K ⧸ Subgroup.center (cStar K)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Kb := modO2Image H K with hKb
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := Setting147.TH' S
  have hl1H : l1 T L V ≤ H := Setting147.l1H' S
  have hS := isSylowIn_szS1_of S hK
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨ψ, hψ⟩ := S14.exists_rep_F4
  obtain ⟨x, hxL, hx3, hfpf⟩ := exists_l1_fpf_F4 S.hyp hMod h1222 h1332 h1334
  obtain ⟨t, htT, htL, htn⟩ := exists_TL_not_triv_F4 S.hyp h1332 S14
  have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hx : x ∈ l1 T L V := hl1 ▸ hxL
  have hxH : x ∈ H := hl1H hx
  have htH : t ∈ H := hTH htT
  have hxX := S14.L1_le_X_F4 hxL
  have htX := S14.T_le_X_F4 htT
  have hKbN : Kb.Normal := by
    have : (K.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hKn
    exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)
  have hN1' := l1T_le_normalizer_szS1_F4 hN1 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
  have hsolv := isSolvable_szB1_l1T_F4 hN1 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K

  have hBL : ∀ β : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K →
      (β : G) ∈ Subgroup.normalizer (L : Set G) := fun β hβ =>
    mem_normalizer_L_of_solvable_F4 h29 S hsolv le_sup_right (Subgroup.mem_sup_left hβ)
  have hBX : ∀ β : ↥H, QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K →
      (β : G) ∈ L32NSet14.nX T V := fun β hβ => mem_nX_of_F4 h1332 h1334 S β.2 (hBL β hβ)
  have hyB : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈ szB1 T H K :=
    ⟨hN1' (mem_modO2Image'.mpr ⟨⟨x, hxH⟩, Subgroup.mem_sup_left hx, rfl⟩),
      mem_modO2Image'.mpr ⟨⟨x, hxH⟩, hl1K hx, rfl⟩⟩
  have htN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ ∈
      Subgroup.normalizer (szS1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    hN1' (mem_modO2Image'.mpr ⟨⟨t, htH⟩, Subgroup.mem_sup_right htT, rfl⟩)

  have hψmk : ∀ (a b : ↥H) (a' b' : ↥(L32NSet14.nX T V)), (a' : G) = a → (b' : G) = b →
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = QuotientGroup.mk' (CFSG.pCore 2 ↥H) b →
        ψ a' = ψ b' := by
    intro a b a' b' ha hb hab
    have h1 : (a : G)⁻¹ * b ∈ pCoreOf 2 H := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hab
      exact hab
    have h3 : ψ (a'⁻¹ * b') = 1 := (hψ _).mpr (by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ha, hb]
      exact pCoreOf_le_trivSub_F4 S S14 h1)
    rwa [map_mul, map_inv, inv_mul_eq_one] at h3

  set R := (T.subgroupOf (L32NSet14.nX T V)).map ψ with hR
  set E := (R.comap ψ).map (L32NSet14.nX T V).subtype with hE
  set D := szB1 T H K ⊓ modO2Image H E with hD
  have hRinv : ∀ s ∈ R, s ^ 2 = 1 := by
    rintro _ ⟨τ, hτ, rfl⟩
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨(τ : G), Subgroup.mem_subgroupOf.mp hτ⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : τ ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have htR : ψ ⟨t, htX⟩ ∈ R := ⟨⟨t, htX⟩, htT, rfl⟩
  have ht1 : ψ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hψ _).mp h)
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
  have hxR : ψ ⟨x, hxX⟩ ∉ R := fun h => hψx (by
    have h2 := hRinv _ h
    calc ψ ⟨x, hxX⟩ = ψ ⟨x, hxX⟩ ^ 3 * (ψ ⟨x, hxX⟩ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hψx3, h2, inv_one, one_mul])

  set Bt := (szB1 T H K).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hBt
  let ι : ↥Bt →* ↥(L32NSet14.nX T V) :=
    { toFun := fun b => ⟨((b : ↥H) : G), hBX b b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hcomap : (D.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).subgroupOf Bt =
      R.comap (ψ.comp ι) := by
    ext b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_comap, MonoidHom.comp_apply]
    constructor
    · rintro ⟨-, hb⟩
      obtain ⟨e, heE, hex⟩ := mem_modO2Image'.mp hb
      obtain ⟨e', he'R, he'e⟩ := Subgroup.mem_map.mp heE
      rw [← hψmk e b e' (ι b) he'e rfl hex]
      exact he'R
    · intro hb
      exact ⟨b.2, mem_modO2Image'.mpr ⟨(b : ↥H), Subgroup.mem_map.mpr ⟨ι b, hb, rfl⟩, rfl⟩⟩
  have hD3 : D.relIndex (szB1 T H K) = 3 := by
    have e1 : Bt.map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) = szB1 T H K :=
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    rw [← e1, ← Subgroup.relIndex_comap, Subgroup.relIndex, hcomap, Subgroup.index_comap]
    exact sl2_relIndex_eq_three ⟨⟨⟨x, hxH⟩, hyB⟩, rfl⟩ hψx hψx3 htR ht1 hRinv

  obtain ⟨hqX, hoddX, hLieX⟩ := kst_props hK hq hLie
  set SX := (szS1 T H K).subgroupOf Kb with hSX
  set α : MulAut ↥Kb := MulAut.conjNormal (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩)
    with hα
  have hα_apply : ∀ k : ↥Kb, ((α k : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩ * k *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t, htH⟩)⁻¹ := fun k => MulAut.conjNormal_apply _ _
  set yX : ↥Kb := ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩, hyB.2⟩ with hyX
  set DX := D.subgroupOf Kb with hDX
  have hα2 : ∃ k : ℕ, α ^ 2 ^ k = 1 := by
    obtain ⟨k, hk⟩ := S.hyp.fsu.sylow.1 ⟨t, htT⟩
    refine ⟨k, ?_⟩
    have h1 : (⟨t, htH⟩ : ↥H) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [hα, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hαS : SX.map α.toMonoidHom = SX := by
    have hle : SX.map α.toMonoidHom ≤ SX := by
      rintro _ ⟨s, hs, rfl⟩
      show ((α s : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szS1 T H K
      rw [hα_apply]
      exact (Subgroup.mem_normalizer_iff.mp htN _).mp hs
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective])
  have hyN : yX ∈ Subgroup.normalizer (SX : Set ↥Kb) :=
    (mem_normalizer_subgroupOf_iff hS.le yX).mpr hyB.1
  have hy3 : yX ^ 3 ∈ SX := by
    have : yX ^ 3 = 1 := Subtype.ext (by
      show (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩) ^ 3 = 1
      rw [← map_pow]
      have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [h1, map_one])
    rw [this]
    exact one_mem _
  have hαy : α yX * yX ∈ SX := by
    have hc : t * x * t⁻¹ * x ∈ l1 T L V :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp (Setting147.T_le_N_l1_F4 S h1332 htT) x).mp hx) hx
    obtain ⟨m, hm⟩ := comm_x_pow_two_F4 S14 hxL hx3 hfpf htT htn
    have hlT : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t * x * t⁻¹ * x, hl1H hc⟩ ∈
        modO2Image H T := by
      refine mk_mem_T_of_coprime_F4 h1222 h1332 h1334 S hc ?_
      have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t * x * t⁻¹ * x, hl1H hc⟩) ^ 2 ^ m = 1 := by
        rw [← map_pow]
        have : (⟨t * x * t⁻¹ * x, hl1H hc⟩ : ↥H) ^ 2 ^ m = 1 := Subtype.ext (by simpa using hm)
        rw [this, map_one]
      exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one h1)
        (Nat.Coprime.pow_right m (by norm_num))
    have e : ((α yX * yX : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t * x * t⁻¹ * x, hl1H hc⟩ := by
      rw [show (⟨t * x * t⁻¹ * x, hl1H hc⟩ : ↥H) =
        ⟨t, htH⟩ * ⟨x, hxH⟩ * ⟨t, htH⟩⁻¹ * ⟨x, hxH⟩ from rfl, map_mul, map_mul, map_mul, map_inv,
        Subgroup.coe_mul, hα_apply]
    show ((α yX * yX : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szS1 T H K
    exact ⟨e ▸ hlT, (α yX * yX).2⟩
  have hSD : SX ≤ DX := by
    intro s hs
    have hs' : (s : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szS1 T H K := hs
    refine ⟨⟨Subgroup.le_normalizer hs', s.2⟩, ?_⟩
    obtain ⟨τ, hτ, hτs⟩ := mem_modO2Image'.mp hs'.1
    exact mem_modO2Image'.mpr ⟨τ, Subgroup.mem_map.mpr ⟨⟨τ, S14.T_le_X_F4 hτ⟩,
      ⟨⟨τ, S14.T_le_X_F4 hτ⟩, hτ, rfl⟩, rfl⟩, hτs⟩
  have hDN : DX ≤ Subgroup.normalizer (SX : Set ↥Kb) := fun d hd =>
    (mem_normalizer_subgroupOf_iff hS.le d).mpr hd.1.1
  have hyD : yX ∉ DX := by
    intro h
    obtain ⟨e, heE, hex⟩ := mem_modO2Image'.mp h.2
    obtain ⟨e', he'R, he'e⟩ := Subgroup.mem_map.mp heE
    apply hxR
    rw [← hψmk e ⟨x, hxH⟩ e' ⟨x, hxX⟩ he'e rfl hex]
    exact he'R
  have hyS : yX ∉ SX := fun h => hyD (hSD h)
  have hDidx : DX.relIndex (Subgroup.normalizer (SX : Set ↥Kb)) = 3 := by
    rw [hSX, normalizer_subgroupOf_eq hS.le, hDX, Subgroup.relIndex_subgroupOf inf_le_right]
    exact hD3
  have hαD : ∀ d ∈ DX, α d * d⁻¹ ∈ SX := by
    intro d hd
    obtain ⟨β, hβE, hβd⟩ := mem_modO2Image'.mp hd.2
    have hβB : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ szB1 T H K := hβd ▸ hd.1
    have hβX := hBX β hβB
    have hβL := hBL β hβB
    obtain ⟨e', he'R, he'e⟩ := Subgroup.mem_map.mp hβE
    obtain ⟨τ', hτ'T, hτ'e⟩ := he'R
    have hτT : (τ' : G) ∈ T := hτ'T
    have hτ : ψ ⟨(τ' : G), S14.T_le_X_F4 hτT⟩ = ψ ⟨(β : G), hβX⟩ := by
      have h1 : e' = ⟨(β : G), hβX⟩ := Subtype.ext he'e
      rw [← h1, ← hτ'e]
    have hc := comm_mem_T_F4 S.hyp S14 hψ htT htL hβX hβL hτT hτ
    have e : ((α d * d⁻¹ : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t * β * t⁻¹ * (β : G)⁻¹, hTH hc⟩ := by
      rw [show (⟨t * β * t⁻¹ * (β : G)⁻¹, hTH hc⟩ : ↥H) = ⟨t, htH⟩ * β * ⟨t, htH⟩⁻¹ * β⁻¹ from
        rfl, map_mul, map_mul, map_mul, map_inv, map_inv, hβd, Subgroup.coe_mul, hα_apply,
        Subgroup.coe_inv]
      rfl
    show ((α d * d⁻¹ : ↥Kb) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ szS1 T H K
    exact ⟨e ▸ mem_modO2Image'.mpr ⟨_, hc, rfl⟩, (α d * d⁻¹).2⟩

  have h := hN2 (↥Kb) n hn hqX hoddX hLieX SX (isSylowTwoOf_subgroupOf hS) α hα2 hαS yX hyN
    hyS hy3 hαy DX hSD hDN hyD hDidx hαD
  obtain ⟨φ⟩ := nonempty_cStar_equiv_kst (H := H) hK
  rcases h with h | h | h
  · exact Or.inl (isPSL_congr (centerQuotEquiv φ).symm h)
  · exact Or.inr (Or.inl (isPSU_congr (centerQuotEquiv φ).symm h))
  · exact Or.inr (Or.inr (isPSL_congr (centerQuotEquiv φ).symm h))

end CFSG.Quasithin.H13.L32A.C

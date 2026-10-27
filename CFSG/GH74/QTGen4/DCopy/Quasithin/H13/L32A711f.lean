module

public import CFSG.Quasithin.H13.L32A711f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A711e

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx711_F4
open CFSG.Quasithin.H13.L32A.Ctx711_F4
open CFSG.Quasithin.H13.L32A.Ctx711 (es)

variable {T L V H V₂ H₂ : Subgroup G} {z a l p : G} (C : Ctx711_F4 T L V H V₂ H₂ z a l p)
include C

theorem V_le_H_F4 : V ≤ H := by
  have := C.V_comm_F4
  exact (Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2).VT_F4.trans C.TH_F4

theorem card_V_F4 : Nat.card V = 8 := by
  have := C.V_comm_F4
  exact (Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2).card_V_F4

theorem UH_le_U_F4 : conjClosure V H ≤ fsuU T V := conjClosure_mono le_rfl C.S.hz.2.1

theorem UH_le_O2H_F4 : conjClosure V H ≤ pCoreOf 2 H := by
  have := C.V_comm_F4
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have hUH : conjClosure V H ≤ H := conjClosure_le fun h hh v hv =>
    H.mul_mem (H.mul_mem hh (C.V_le_H_F4 hv)) (H.inv_mem hh)
  refine le_pCoreOf_of_le_normalizer 2 hUH (le_normalizer_conjClosure V H) fun u => ⟨1, ?_⟩
  rw [pow_one, sq]
  exact Subtype.ext (Setting147.sq_fsuU C.S (fun v hv => S14.mul_self_V_F4 hv) u (C.UH_le_U_F4 u.2))

theorem false_of_le_F4 (h : pCoreOf 2 H ≤ conjClosure V H) : False := by
  have hpU : p ∈ fsuU T V := C.UH_le_U_F4 (h (C.O2G1_le_O2H_F4 C.hp))
  have haU : a ∈ fsuU T V := C.UH_le_U_F4 (le_conjClosure V H (C.hV2.2.1 C.ha))
  have hc : p * a = a * p :=
    congrArg Subtype.val (@mul_comm' _ _ C.S.hyp.abelian (⟨p, hpU⟩ : ↥(fsuU T V)) ⟨a, haU⟩)
  apply C.hpa
  rw [hc]
  group

theorem card_T_eq_F4 : (pCoreOf 2 H).relIndex T * Nat.card (pCoreOf 2 H) = Nat.card T :=
  relIndex_card_mul (pCoreOf_le_of_le C.S.hyp C.TH_F4)

theorem z_central_F4 {g : G} (hg : g ∈ H) : g * z = z * g := by
  have := C.V_comm_F4
  have S14 := Hyp147.set14_F4 C.S.hyp C.h1222 C.h1332 C.h1334 C.hV2
  have hg' : g * z * g⁻¹ ∈ fsuV1 T V :=
    (Subgroup.mem_normalizer_iff.mp (C.S.hz.2.1 hg) z).mp C.hz
  rcases S14.eq_of_mem_V1_F4 C.hz C.hz1 hg' with h1 | h1
  · exfalso
    apply C.hz1
    have := congrArg (fun u => g⁻¹ * u * g) h1
    simpa [mul_assoc] using this
  · calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [h1]

theorem false_A3_F4 (hidx : ¬ T.relIndex H ∣ 9)
    (hiso : quasithinO2QuotientIso H (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    (hO : (pCoreOf 2 H).relIndex T = 8) : False := by
  have hD := L14413.isDSystemIn_A3_of (es T L H H₂ V₂) hiso C.d1_SL22_F4 C.LT_SL3_F4 (C.es_syl_F4 hidx)
    (C.es_T_F4 hidx) (C.es_X_F4 hidx) (C.es_dist_F4 hidx) (C.es_D4_F4 hidx)
  obtain ⟨e⟩ := L14413.nonempty_mulEquiv_SL_of_isDSystemIn hD
  have hE : Nat.card ↥(H ⊔ d1 T L H₂ V₂ ⊔ (L ⊔ T)) = 20160 := by
    have h1 := Nat.card_congr e.toEquiv
    have h2 := Nat.card_congr (L14413.slEquivGLn 4).toEquiv
    rw [A5.card_GL4] at h2
    change Nat.card ↥(H ⊔ d1 T L H₂ V₂ ⊔ (L ⊔ T)) = _ at h1
    rw [h1, h2]
  have hTE : T ≤ H ⊔ d1 T L H₂ V₂ ⊔ (L ⊔ T) := C.TH_F4.trans (le_sup_left.trans le_sup_left)
  have hdvd := Subgroup.card_dvd_of_le hTE
  rw [hE] at hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := C.T2_F4.exists_card_eq
  rw [hk, show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num] at hdvd
  have hT64 := le_of_pow_dvd (by decide) hdvd
  have hcard := C.card_T_eq_F4
  rw [hO, hk] at hcard
  have hO8 : Nat.card (pCoreOf 2 H) ≤ 8 := by
    have : 8 * Nat.card (pCoreOf 2 H) ≤ 2 ^ 6 := hcard ▸ hT64
    omega
  have hVO : V ≤ pCoreOf 2 H := (le_conjClosure V H).trans C.UH_le_O2H_F4
  have hEq : V = pCoreOf 2 H := Subgroup.eq_of_le_of_card_ge hVO (by rw [C.card_V_F4]; exact hO8)
  exact C.false_of_le_F4 (hEq ▸ le_conjClosure V H)

theorem false_C3_F4 (hidx : ¬ T.relIndex H ∣ 9)
    (hiso : quasithinO2QuotientIso H ↥(alternatingGroup (Fin 6)) ∨
      quasithinO2QuotientIso H (Equiv.Perm (Fin 6)))
    (hO : 8 ≤ (pCoreOf 2 H).relIndex T) (h5 : 5 ∣ (pCoreOf 2 H).relIndex H) : False := by
  have hD := isDSystemIn_C3_of (es T L H H₂ V₂) hiso C.d1_SL22_F4 C.LT_SL3_F4 (C.es_syl_F4 hidx)
    (C.es_T_F4 hidx) (C.es_X_F4 hidx) (C.es_dist_F4 hidx) (C.es_D4_F4 hidx) (Or.inl C.es_D5_F4)
  have hLie := (stmtI_5_1_holds _ .C3 _ hD.isDSystem).2 rfl
  obtain ⟨φ₀⟩ := nonempty_mulEquiv_symplecticGroup_of_lieModel hLie
  set E := H ⊔ d1 T L H₂ V₂ ⊔ (L ⊔ T) with hEdef
  let φ : ↥E ≃* Sp5.Sp := φ₀
  have hE : Nat.card ↥E = 1451520 := by
    rw [Nat.card_congr φ.toEquiv, card_symplecticGroup_three_two]
  have hHE : H ≤ E := le_sup_left.trans le_sup_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩

  have hdvd := Subgroup.card_dvd_of_le (C.TH_F4.trans hHE)
  rw [hE] at hdvd
  obtain ⟨k, hk⟩ := C.T2_F4.exists_card_eq
  rw [hk, show (1451520 : ℕ) = 2 ^ 9 * 2835 by norm_num] at hdvd
  have hT512 := le_of_pow_dvd (by decide) hdvd
  have hcard := C.card_T_eq_F4
  rw [hk] at hcard
  have hO64 : Nat.card (pCoreOf 2 H) ≤ 64 := by
    have h1 : 8 * Nat.card (pCoreOf 2 H) ≤ 2 ^ 9 :=
      (Nat.mul_le_mul_right _ hO).trans (hcard ▸ hT512)
    omega
  have hVO : V ≤ pCoreOf 2 H := (le_conjClosure V H).trans C.UH_le_O2H_F4
  have hO8 : 8 ≤ Nat.card (pCoreOf 2 H) := by
    rw [← C.card_V_F4]
    exact Subgroup.card_le_of_le hVO

  have h5H : 5 ∣ Nat.card H := by
    have := relIndex_card_mul (pCoreOf_le 2 H)
    rw [← this]
    exact Dvd.dvd.mul_right h5 _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 5 h5H
  have hxo : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx]
  have hx5 : (x : G) ^ 5 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
  have hxN : (x : G) ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H x.2

  set P := pCoreOf 2 H ⊓ Subgroup.centralizer ({(x : G)} : Set G) with hPdef
  have hPE : P ≤ E := inf_le_left.trans ((pCoreOf_le 2 H).trans hHE)
  have hP2 : Nat.card P ≤ 2 := by
    have hxE : (x : G) ∈ E := hHE x.2
    set P' := (P.subgroupOf E).map φ.toMonoidHom with hP'
    have hPp : IsPGroup 2 P := (pCoreOf_isPGroup 2 H).to_le inf_le_left
    have hP'2 : IsPGroup 2 P' :=
      (hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPE).symm).map φ.toMonoidHom
    have hord : orderOf (φ ⟨(x : G), hxE⟩) = 5 := by
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hxo
    have hP'C : P' ≤ Subgroup.centralizer ({φ ⟨(x : G), hxE⟩} : Set Sp5.Sp) := by
      rintro _ ⟨q, hq, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hqx : (q : G) * x = x * q :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hq).2
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hqx
    have h2 := Sp5.card_le_two_of_le_centralizer hord hP'2 hP'C
    rw [hP', Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPE).toEquiv] at h2
    exact h2

  have hzO : z ∈ pCoreOf 2 H := hVO (C.hV2.2.1 (C.hV2.1 C.hz))
  have hzC : z ∈ Subgroup.centralizer ({(x : G)} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (C.z_central_F4 x.2).symm
  have hcardP : Nat.card P = 2 := by
    have h1 : 1 < Nat.card P := (Subgroup.one_lt_card_iff_ne_bot P).mpr fun h => by
      have : z ∈ P := ⟨hzO, hzC⟩
      rw [h, Subgroup.mem_bot] at this
      exact C.hz1 this
    omega

  have hmod1 := card_modEq_card_inf_centralizer (p := 5) hx5 hxN
  rw [← hPdef, hcardP] at hmod1
  have hO32 := eq_32_of_modEq (card_pCoreOf_pow H) hO8 hO64 hmod1

  have hxU : (x : G) ∈ Subgroup.normalizer (conjClosure V H : Set G) :=
    le_normalizer_conjClosure V H x.2
  have hmod2 := card_modEq_card_inf_centralizer (p := 5) hx5 hxU
  have hUC : Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer ({(x : G)} : Set G)) = 2 := by
    have hle : conjClosure V H ⊓ Subgroup.centralizer ({(x : G)} : Set G) ≤ P :=
      inf_le_inf_right _ C.UH_le_O2H_F4
    have h1 := Subgroup.card_le_of_le hle
    have h2 : 1 < Nat.card ↥(conjClosure V H ⊓ Subgroup.centralizer ({(x : G)} : Set G)) :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => by
        have : z ∈ conjClosure V H ⊓ Subgroup.centralizer ({(x : G)} : Set G) :=
          ⟨le_conjClosure V H (C.hV2.2.1 (C.hV2.1 C.hz)), hzC⟩
        rw [h, Subgroup.mem_bot] at this
        exact C.hz1 this
    omega
  rw [hUC] at hmod2
  have hUpow : ∃ j : ℕ, Nat.card ↥(conjClosure V H) = 2 ^ j :=
    ((pCoreOf_isPGroup 2 H).to_le C.UH_le_O2H_F4).exists_card_eq
  have hU8 : 8 ≤ Nat.card ↥(conjClosure V H) := by
    rw [← C.card_V_F4]
    exact Subgroup.card_le_of_le (le_conjClosure V H)
  have hU64 : Nat.card ↥(conjClosure V H) ≤ 64 :=
    (Subgroup.card_le_of_le C.UH_le_O2H_F4).trans hO64
  have hU32 := eq_32_of_modEq hUpow hU8 hU64 hmod2
  have hEq : conjClosure V H = pCoreOf 2 H :=
    Subgroup.eq_of_le_of_card_ge C.UH_le_O2H_F4 (by rw [hU32, hO32])
  exact C.false_of_le_F4 hEq.ge

end Ctx711_F4

theorem mem_cent_of_fix_F4 {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]
    (S14 : L32NSet14.Setting_F4 G T L V V₂) {z a g : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (ha : a ∈ V₂) (haV : a ∉ fsuV1 T V) (hgz : g * z * g⁻¹ = z) (hga : g * a * g⁻¹ = a) :
    g ∈ Subgroup.centralizer (V₂ : Set G) := by
  have haa : a * a = 1 := S14.mul_self_V_F4 (S14.hV2.2.1 ha)
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hfix : g * v * g⁻¹ = v := by
    rcases S14.mem_V2_F4 ha haV hv with h | h
    · rcases S14.eq_of_mem_V1_F4 hz hz1 h with rfl | rfl
      · group
      · exact hgz
    · have hv' : v = a * (a * v) := by rw [← mul_assoc, haa, one_mul]
      have hav : g * (a * v) * g⁻¹ = a * v := by
        rcases S14.eq_of_mem_V1_F4 hz hz1 h with h' | h'
        · rw [h']; group
        · rw [h', hgz]
      rw [hv', show g * (a * (a * v)) * g⁻¹ = (g * a * g⁻¹) * (g * (a * v) * g⁻¹) by group, hga,
        hav]
  calc v * g = (g * v * g⁻¹) * g := by rw [hfix]
    _ = g * v := by group

theorem exists_ctx711_F4 {K : Type*} [Group K] [CFSG.GH74.QTGen4.Finite4 K] {P₀ X₁ X₂ : Subgroup K}
    (hM : ModelIdx K P₀ X₁ X₂) (hThm : Thm14_5_3_F4) (h4 : Lemma14_7_4_two_three_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4)
    {T L V H : Subgroup G} (S : Setting147 G T L V H) (hiso : quasithinO2QuotientIso H K) :
    ∃ (V₂ H₂ : Subgroup G) (z a l p : G), Ctx711_F4 T L V H V₂ H₂ z a l p ∧
      T.relIndex H = P₀.index ∧ (pCoreOf 2 H).relIndex T = Nat.card P₀ := by
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  obtain ⟨A₁, A₂, hT₁, hT₂, h₁X, h₂X, h₁₂, h₂₁, -, -, i₁, i₂, n₁, n₂, hidx, hO, hcls⟩ :=
    hM.transport hiso hsyl
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h1222
  have S14 := Hyp147.set14_F4 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis_F4
  obtain ⟨l, hl, hl3, hlz⟩ := exists_L2_cube_F4 S14 hz hz1 ha haV hb hbV
  have hTG : T ≤ A6.g1 T V := hTH.trans S.hz.2.1

  have hcomm := lemma14_7_4_one_F4 S.hyp (stmt13_3_2_two_of_F4 h1332) hMod h13314 hV2
  obtain ⟨p, hp, hpa⟩ : ∃ p ∈ pCoreOf 2 (A6.g1 T V), p * a * p⁻¹ ≠ a := by
    by_contra h
    push Not at h
    have hle : pCoreOf 2 (A6.g1 T V) ≤ Subgroup.centralizer (V₂ : Set G) := fun q hq =>
      mem_cent_of_fix_F4 S14 hz hz1 ha haV (conj_fsuV1 hz (pCoreOf_le_of_le S.hyp hTG hq)) (h q hq)
    have hbot : ⁅V₂, pCoreOf 2 (A6.g1 T V)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    rw [hcomm] at hbot
    have : z ∈ (⊥ : Subgroup G) := hbot ▸ hz
    exact hz1 this

  have hL1T : ¬ l1 T L V ≤ T := by
    have h3 := S14.Lp3_F4
    rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h3
    intro hle
    have hYp : l1 T L V ≤ pCoreOf 2 (l1 T L V) :=
      le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer
        (S.hyp.fsu.sylow.1.to_le hle)
    rw [Subgroup.relIndex_eq_one.mpr hYp] at h3
    omega
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    (h1332 G T L S.hyp.hyp.h13 L S.hyp.hyp.h13.faithful).2.1.1
  have hL1TM : l1 T L V ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)) hTL
  rcases hcls (l1 T L V ⊔ T) le_sup_right (sup_le hL1H hTH) with h | h | h | h
  · exact absurd (le_sup_left.trans h.le) hL1T
  · refine ⟨V₂, A₂, z, a, l, p, ⟨S, h1222, h1332, h1334, hThm, h4, hV2, hz, hz1, ha, haV, hl,
      hl3, hlz, hp, hpa, hT₂, h₂X, i₂, n₂, by rw [h]; exact h₂₁, by rw [h]; exact h₁₂,
      fun Y hTY hYH => ?_⟩, hidx, hO⟩
    rcases hcls Y hTY hYH with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl (h'.trans h.symm))
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inr (Or.inr h'))
  · refine ⟨V₂, A₁, z, a, l, p, ⟨S, h1222, h1332, h1334, hThm, h4, hV2, hz, hz1, ha, haV, hl,
      hl3, hlz, hp, hpa, hT₁, h₁X, i₁, n₁, by rw [h]; exact h₁₂, by rw [h]; exact h₂₁,
      fun Y hTY hYH => ?_⟩, hidx, hO⟩
    rcases hcls Y hTY hYH with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inr (Or.inl h'))
    · exact Or.inr (Or.inl (h'.trans h.symm))
    · exact Or.inr (Or.inr (Or.inr h'))
  · exact absurd (h ▸ hL1TM) S.hz.2.2

theorem finite4_of_quasithinO2QuotientIso_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {H : Subgroup G} {K : Type} [Group K] (hiso : quasithinO2QuotientIso H K) :
    CFSG.GH74.QTGen4.Finite4 K := by
  obtain ⟨φ, hsurj, -⟩ := hiso
  haveI : CFSG.GH74.QTGen4.Finite4 (↥H ⧸ φ.ker) :=
    CFSG.GH74.QTGen4.instFinite4Quotient ↥H φ.ker
  exact CFSG.GH74.QTGen4.Finite4.of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)

theorem lemma14_7_11_of_F4 (hThm : Thm14_5_3_F4) (h4 : Lemma14_7_4_two_three_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4) : Lemma14_7_11_F4 := by
  intro G _ _ T L V H S
  refine ⟨fun hiso => ?_, fun hiso => ?_, fun hiso => ?_⟩
  · haveI := finite4_of_quasithinO2QuotientIso_F4 hiso
    obtain ⟨V₂, H₂, z, a, l, p, C, hidx, hO⟩ :=
      exists_ctx711_F4 modelIdx_SL3 hThm h4 h1222 h1332 h1334 h13314 S hiso
    rw [index_P0_SL3] at hidx
    rw [SL3.card_P0] at hO
    exact C.false_A3_F4 (by rw [hidx]; norm_num) hiso hO
  · haveI := finite4_of_quasithinO2QuotientIso_F4 hiso
    obtain ⟨V₂, H₂, z, a, l, p, C, hidx, hO⟩ :=
      exists_ctx711_F4 modelIdx_A6 hThm h4 h1222 h1332 h1334 h13314 S hiso
    rw [index_QA6] at hidx
    rw [card_QA6_A6] at hO
    refine C.false_C3_F4 (by rw [hidx]; norm_num) (Or.inl hiso) hO.ge ?_
    rw [U3.relIndex_pCoreOf_of_quot hiso, card_A6]
    norm_num
  · haveI := finite4_of_quasithinO2QuotientIso_F4 hiso
    obtain ⟨V₂, H₂, z, a, l, p, C, hidx, hO⟩ :=
      exists_ctx711_F4 modelIdx_S6 hThm h4 h1222 h1332 h1334 h13314 S hiso
    rw [index_D6] at hidx
    rw [card_D6sub] at hO
    refine C.false_C3_F4 (by rw [hidx]; norm_num) (Or.inr hiso) (by rw [hO]; norm_num) ?_
    rw [U3.relIndex_pCoreOf_of_quot hiso, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide

end CFSG.Quasithin.H13.L32A

module

public import CFSG.Quasithin.H13.L32A758b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A758a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A769c

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

theorem false_of_cent_F4 (h : Hyp147 G T L V) (hMod : StmtL32NModule_F4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h13314 : A6.Stmt13_3_14_F4) {z' : G} (hz'U : z' ∈ fsuU T V)
    (hcentV : ∀ c ∈ pCoreOf 2 (hz T V), c * z' = z' * c → ∀ v ∈ V, c * v = v * c) : False := by
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz_F4 hMod h
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hUQ : fsuU T V ≤ pCoreOf 2 (hz T V) := by
    rw [hUeq]
    exact hF.conjClosure_Vp_le_pCoreOf
  have hUH : fsuU T V ≤ hz T V := hUQ.trans (pCoreOf_le 2 _)
  have hQC : ∀ q ∈ pCoreOf 2 (hz T V), ∀ u ∈ fsuU T V, q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro q hq u hu
    have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
      rw [← hF.pCoreOf_eq_centralizerMod]
      exact hq
    exact hqC.2.2 u (hUeq ▸ hu)
  have hV1c : ∀ v ∈ fsuV1 T V, ∀ g ∈ hz T V, v * g = g * v := fun v hv g hg =>
    (Subgroup.mem_centralizer_iff.mp hg v hv)

  have hβmul : ∀ q ∈ pCoreOf 2 (hz T V), ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V,
      q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by
    intro q hq a ha b hb
    have h1 := hV1c _ (hQC q hq b hb) a (hUH ha)
    calc q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹)) *
          a⁻¹ := by group
      _ = (q * a * q⁻¹ * a⁻¹) * ((q * b * q⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [h1]
      _ = _ := by group

  obtain ⟨v₁, hv₁, hv₁1, hV1cases⟩ : ∃ v₁ ∈ fsuV1 T V, v₁ ≠ 1 ∧
      ∀ y ∈ fsuV1 T V, y = 1 ∨ y = v₁ := by
    obtain ⟨⟨v₁, hv₁⟩, hv₁1, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hF.card_V₁
    refine ⟨v₁, hv₁, fun e => hv₁1 (Subtype.ext e), fun y hy => ?_⟩
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (congrArg Subtype.val (hu ⟨y, hy⟩ fun e => hy1 (congrArg Subtype.val e)))
  have hcommiff : ∀ q ∈ pCoreOf 2 (hz T V), ∀ u ∈ fsuU T V,
      q * u = u * q ↔ q * u * q⁻¹ * u⁻¹ = 1 := fun q _ u _ => by
    constructor
    · intro e; rw [e]; group
    · intro e
      have := congrArg (· * u) e
      simp only [inv_mul_cancel_right, one_mul] at this
      calc q * u = q * u * q⁻¹ * q := by group
        _ = u * q := by rw [this]

  set H₀ := V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hH₀
  have hidx : ∀ a ∈ V, a ∉ H₀ → ∀ b ∈ V, b ∉ H₀ → a * b ∈ H₀ := by
    intro a ha haH b hb hbH

    obtain ⟨q₁, hq₁, hq₁a⟩ : ∃ q₁ ∈ pCoreOf 2 (hz T V), q₁ * a ≠ a * q₁ := by
      by_contra hcon
      push Not at hcon
      exact haH ⟨ha, Subgroup.mem_centralizer_iff.mpr fun q hq => hcon q hq⟩
    have hq₁z : ¬ q₁ * z' = z' * q₁ := fun e => hq₁a (hcentV q₁ hq₁ e a ha)

    have hdiv : ∀ q ∈ pCoreOf 2 (hz T V), ¬ q * z' = z' * q →
        q₁⁻¹ * q * z' = z' * (q₁⁻¹ * q) := by
      intro q hq hqz
      have hb1 := hQC q₁ hq₁ z' hz'U
      have hb2 := hQC q hq z' hz'U
      have e1 : q₁ * z' * q₁⁻¹ * z'⁻¹ = v₁ := (hV1cases _ hb1).resolve_left
        fun e => hq₁z ((hcommiff q₁ hq₁ z' hz'U).mpr e)
      have e2 : q * z' * q⁻¹ * z'⁻¹ = v₁ := (hV1cases _ hb2).resolve_left
        fun e => hqz ((hcommiff q hq z' hz'U).mpr e)
      have hqz' : q * z' * q⁻¹ = v₁ * z' := by rw [← e2]; group
      have hq₁z' : q₁ * z' * q₁⁻¹ = v₁ * z' := by rw [← e1]; group
      have hv₁q₁ := hV1c v₁ hv₁ q₁ (pCoreOf_le 2 _ hq₁)
      calc q₁⁻¹ * q * z' = q₁⁻¹ * (q * z' * q⁻¹) * q := by group
        _ = q₁⁻¹ * (q₁ * z' * q₁⁻¹) * q := by rw [hqz', hq₁z']
        _ = z' * (q₁⁻¹ * q) := by group
    refine ⟨mul_mem ha hb, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩

    have hq₁b : q₁ * b ≠ b * q₁ := by
      intro e
      apply hbH
      refine ⟨hb, Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_⟩
      by_cases hq'z : q' * z' = z' * q'
      · exact hcentV q' hq' hq'z b hb
      · have hc := hdiv q' hq' hq'z
        have hcb := hcentV _ (mul_mem (inv_mem hq₁) hq') hc b hb
        calc q' * b = q₁ * ((q₁⁻¹ * q') * b) := by group
          _ = q₁ * (b * (q₁⁻¹ * q')) := by rw [hcb]
          _ = (q₁ * b) * (q₁⁻¹ * q') := by group
          _ = (b * q₁) * (q₁⁻¹ * q') := by rw [e]
          _ = b * q' := by group

    have hq₁ab : q₁ * (a * b) = (a * b) * q₁ := by
      have ea : q₁ * a * q₁⁻¹ * a⁻¹ = v₁ := (hV1cases _ (hQC q₁ hq₁ a (hVU ha))).resolve_left
        fun e => hq₁a ((hcommiff q₁ hq₁ a (hVU ha)).mpr e)
      have eb : q₁ * b * q₁⁻¹ * b⁻¹ = v₁ := (hV1cases _ (hQC q₁ hq₁ b (hVU hb))).resolve_left
        fun e => hq₁b ((hcommiff q₁ hq₁ b (hVU hb)).mpr e)
      have hv₁2 : v₁ * v₁ = 1 := by
        have h1 := orderOf_dvd_natCard (⟨v₁, hv₁⟩ : ↥(fsuV1 T V))
        rw [hF.card_V₁] at h1
        have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
        have h3 : v₁ ^ 2 = 1 := by simpa using congrArg Subtype.val h2
        rwa [pow_two] at h3
      apply (hcommiff q₁ hq₁ (a * b) (mul_mem (hVU ha) (hVU hb))).mpr
      rw [hβmul q₁ hq₁ a (hVU ha) b (hVU hb), ea, eb, hv₁2]
    by_cases hqz : q * z' = z' * q
    · exact hcentV q hq hqz _ (mul_mem ha hb)
    · have hc := hdiv q hq hqz
      have hcab := hcentV _ (mul_mem (inv_mem hq₁) hq) hc _ (mul_mem ha hb)
      calc q * (a * b) = q₁ * ((q₁⁻¹ * q) * (a * b)) := by group
        _ = q₁ * ((a * b) * (q₁⁻¹ * q)) := by rw [hcab]
        _ = (q₁ * (a * b)) * (q₁⁻¹ * q) := by group
        _ = ((a * b) * q₁) * (q₁⁻¹ * q) := by rw [hq₁ab]
        _ = a * b * q := by group

  have hne : ¬ V ≤ H₀ := by
    intro hle
    have h13322 := stmt13_3_2_two_of_F4 h1332
    obtain ⟨V₂, hV2⟩ := h.exists_V2_F4 h13322 hMod h1222
    have h1 := lemma14_7_4_one_F4 h h13322 hMod h13314 hV2
    have hg1 : A6.g1 T V = hz T V := normalizer_eq_centralizer_of_card_eq_two hF.card_V₁
    rw [hg1] at h1
    have h2 : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv q hq
      have hc' : v ∈ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) :=
        (Subgroup.mem_inf.mp (hle (hV2.2.1 hv))).2
      rw [Subgroup.mem_bot, commutatorElement_def, ← Subgroup.mem_centralizer_iff.mp hc' q hq,
        mul_inv_cancel_right, mul_inv_cancel]
    rw [h1] at h2
    have hc := hF.card_V₁
    rw [h2, Subgroup.card_bot] at hc
    omega

  have hN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (H₀ : Set G) := by
    obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
    intro g hg
    have hgV : g ∈ Subgroup.normalizer (V : Set G) :=
      hLTV (sup_le_sup_right (L32NSet14.Setting.L1_le.trans inf_le_left) T hg)
    have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
      le_normalizer_pCoreOf 2 _ (hF.L₁T_le_H hg)
    rw [← conjSub_eq_self_iff, hH₀, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr hgV, conjSub_eq_self_iff.mpr hgQ]
  exact false_of_hyperplane_F4 h h1222 h1332 h1334 hF inf_le_left hne hidx hN

namespace Ctx753

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem cent_QH_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ∀ a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)) ⊓ pCoreOf 2 (hz T V),
      ∀ u ∈ conjClosure V (hz T V), a * u = u * a := by
  obtain ⟨δ, δ', k₂, h₀, y, N'', hyU, hyU'', -, -, -, hyV1''⟩ :=
    N.exists_sym_of_eq C (C.heq_of_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N)
  have hcomm := C.comm_D_eq_bot_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N''
  set x' := (h₀ : G) * k₂ with hx'
  have hZinv : conjSub y⁻¹ (fsuV1 T V) = conjSub x' (fsuV1 T V) := by
    calc conjSub y⁻¹ (fsuV1 T V) = conjSub y⁻¹ (conjSub y (conjSub x' (fsuV1 T V))) := by
          rw [hyV1'']
      _ = conjSub x' (fsuV1 T V) := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  rintro a ⟨haUα, haQ⟩ u hu
  have haH := pCoreOf_le 2 _ haQ

  have ha' : y⁻¹ * a * y ∈ conjClosure V (hz T V) := by
    rw [← hyU] at haUα
    exact mem_conjSub.1 haUα
  have hu' : y⁻¹ * u * y ∈ conjSub x' (conjClosure V (hz T V)) := by
    rw [← hyU''] at hu
    exact mem_conjSub.1 hu
  have haD : y⁻¹ * a * y ∈ centralizerMod (conjSub x' (fsuV1 T V)) (conjClosure V (hz T V))
      (conjSub x' (conjClosure V (hz T V))) := by
    refine ⟨ha', conjSub_le_normalizer C.hF98.H_normalizes_V₁ x' (N''.conjClosure_le_Gα C ha'),
      fun b hb => ?_⟩
    have hb'' : y * b * y⁻¹ ∈ conjClosure V (hz T V) := by
      rw [← hyU'']
      exact mul_mem_conjSub hb
    have h1 := C.comm_mem_V1_of_Q E haQ hb''
    rw [← hZinv, mem_conjSub, inv_inv]
    have e1 : y * (y⁻¹ * a * y * b * (y⁻¹ * a * y)⁻¹ * b⁻¹) * y⁻¹ =
        a * (y * b * y⁻¹) * a⁻¹ * (y * b * y⁻¹)⁻¹ := by group
    rw [e1]
    exact h1
  have h1 := Subgroup.commutator_mem_commutator haD hu'
  rw [hcomm, Subgroup.mem_bot, commutatorElement_def] at h1
  have e1 : a * u * a⁻¹ * u⁻¹ =
      y * (y⁻¹ * a * y * (y⁻¹ * u * y) * (y⁻¹ * a * y)⁻¹ * (y⁻¹ * u * y)⁻¹) * y⁻¹ := by group
  have h2 : a * u * a⁻¹ * u⁻¹ = 1 := by rw [e1, h1]; group
  calc a * u = (a * u * a⁻¹ * u⁻¹) * u * a := by group
    _ = u * a := by rw [h2, one_mul]

theorem zα_p0_false_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) {z : G}
    (hz1 : z ∈ fsuV1 T V) (hzne : z ≠ 1)
    (hZU : conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V))
    (hθ : C.θG e (((k : G) * g) * z * ((k : G) * g)⁻¹) = M755.ptQ 8) : False := by
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  set x := (k : G) * g with hx
  set zα := x * z * x⁻¹ with hzα
  have hzαU : zα ∈ conjClosure V (hz T V) := hZU (mul_mem_conjSub hz1)

  have hUαH := N.uα_le_hz C
  have hUαe : IsElemAbelian 2 (conjSub x (conjClosure V (hz T V))) :=
    F7.isElemAbelian_conjSub C.hF98.F911_3
  have hA1 : C.ΦX E (conjSub x (conjClosure V (hz T V))) ≠ ⊥ := by
    intro hA
    have hcard := C.card_ΦX E hUαH
    rw [hA, Subgroup.card_bot] at hcard
    exact absurd hcard.symm (ne_of_gt (N.one_lt_relIndex C))
  have hNα : ∀ h ∈ hz T V, h * zα = zα * h → ∀ u ∈ conjSub x (conjClosure V (hz T V)),
      h * u * h⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := by
    intro h hh hhz u hu
    have hGα := C.mem_Gα_of_comm (x := x) hz1 hzne hhz
    exact (Subgroup.mem_normalizer_iff.mp
      (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hGα) u).mp hu
  obtain ⟨-, hcl⟩ := C.class_p0_F4 E hG h13322 hMod h13314 h1222 hzαU hθ hUαH hUαe hA1 hNα
  have h4 : (4 : ℕ) ∈ idx (C.ΦX E (conjSub x (conjClosure V (hz T V)))) := by
    rcases hcl with h | h
    · exact (h 4).2 (by decide)
    · exact (h 4).2 (by decide)
  obtain ⟨b, hb, hbe⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 h4).2
  have hbH := hUαH hb

  have hl4 : ∀ d ∈ [8, 32, 40], d ∈ M755.lineB 4 ∧ d ≠ 0 := by decide
  have hl4' : ∀ d ∈ M755.lineB 4, d ≠ 0 → d ∈ [8, 32, 40] := by decide
  have hline : ∀ y ∈ conjSub 1 V, y ∉ fsuV1 T V →
      ∃ d ∈ M755.lineB 4, d ≠ 0 ∧ C.θG e y = M755.ptQ d := by
    intro y hy hy1
    rw [conjSub_one] at hy
    obtain ⟨d, hd, hθd⟩ := C.θG_V_F4 E hMod hVL hV₂ hy hy1
    exact ⟨d, (hl4 d hd).1, (hl4 d hd).2, hθd⟩
  have hcover : ∀ d ∈ M755.lineB 4, d ≠ 0 →
      ∃ y ∈ conjSub 1 V, y ∉ fsuV1 T V ∧ C.θG e y = M755.ptQ d := by
    intro d hd hd0
    obtain ⟨v, hv, hv1, hθv⟩ := C.exists_V_θG_F4 E hMod hVL hV₂ (hl4' d hd hd0)
    exact ⟨v, by rw [conjSub_one]; exact hv, hv1, hθv⟩
  have hUbV : ∀ u ∈ conjClosure V (hz T V), u * b * u⁻¹ * b⁻¹ ∈ V := fun u hu => by
    have h1 := C.comm_mem_line_F4 E h13322 hMod hVL hV₂ (b₀ := 4) (by decide) (h := 1) (one_mem _)
      hline hcover hbH hbe hu
    rwa [conjSub_one] at h1

  have hVdec : ∀ v ∈ V, ∃ u ∈ conjClosure V (hz T V), ∃ t ∈ fsuV1 T V,
      v = (u * b * u⁻¹ * b⁻¹) * t := by
    intro v hv
    by_cases hv1 : v ∈ fsuV1 T V
    · exact ⟨1, one_mem _, v, hv1, by group⟩
    obtain ⟨d, hd, hθd⟩ := C.θG_V_F4 E hMod hVL hV₂ hv hv1
    obtain ⟨c', hc', hc'e⟩ := M755.facts_B0_onto 4 (by decide) d (hl4 d hd).1
    obtain ⟨u, huU, hu⟩ := C.exists_θG e (M755.ptQ c')
    refine ⟨u, huU, (u * b * u⁻¹ * b⁻¹)⁻¹ * v, ?_, by group⟩
    have hcV := hUbV u huU
    have hbu : b * u⁻¹ * b⁻¹ ∈ conjClosure V (hz T V) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hbH) _).mp
        (inv_mem huU)
    have hθc : C.θG e (u * b * u⁻¹ * b⁻¹) = M755.ptQ d := by
      rw [show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group, C.θG_mul e huU hbu,
        C.θG_conj E hbH (inv_mem huU), C.θG_inv e huU, map_inv, hu, hbe,
        M755.g2QAct_sEltG_code (by norm_num) hc',
        show ∀ r : ModQ, r⁻¹ = r from fun r => inv_eq_of_mul_eq_one_right (M755.mul_self_Q r),
        ← M755.ptQ_xor hc' (M755.actC_mem _ (by decide) c' hc'), Nat.xor_comm, hc'e]
    have hcU : u * b * u⁻¹ * b⁻¹ ∈ conjClosure V (hz T V) := le_conjClosure V _ hcV
    have hmem : (u * b * u⁻¹ * b⁻¹)⁻¹ * v ∈ V := mul_mem (inv_mem hcV) hv
    by_contra hnot
    obtain ⟨d', hd', hθd'⟩ := C.θG_V_F4 E hMod hVL hV₂ hmem hnot
    rw [C.θG_mul e (inv_mem hcU) (le_conjClosure V _ hv), C.θG_inv e hcU, hθc, hθd,
      inv_mul_cancel] at hθd'
    have hd'p : d' ∈ M755.ptsQ := by
      have key : ∀ d ∈ [8, 32, 40], d ∈ M755.ptsQ := by decide
      exact key d' hd'
    exact M755.ptQ_ne_one hd'p hθd'.symm

  have hV1c : ∀ v ∈ fsuV1 T V, ∀ g ∈ hz T V, v * g = g * v := fun v hv g hg =>
    (Subgroup.mem_centralizer_iff.mp hg v hv)
  have hcent := C.cent_QH_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N
  have hUH : conjClosure V (hz T V) ≤ hz T V :=
    C.hF98.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hcentV : ∀ q ∈ pCoreOf 2 (hz T V), q * zα = zα * q → ∀ v ∈ V, q * v = v * q := by
    intro q hq hqz v hv
    have hqH := pCoreOf_le 2 _ hq
    obtain ⟨u, huU, t, ht, rfl⟩ := hVdec v hv
    have hGα := C.mem_Gα_of_comm (x := x) hz1 hzne hqz
    have hqb : q * b * q⁻¹ ∈ conjSub x (conjClosure V (hz T V)) :=
      (Subgroup.mem_normalizer_iff.mp
        (conjSub_le_normalizer (le_normalizer_conjClosure V (hz T V)) x hGα) b).mp hb
    set c := b⁻¹ * (q * b * q⁻¹) with hc
    have hcUα : c ∈ conjSub x (conjClosure V (hz T V)) := mul_mem (inv_mem hb) hqb
    have hcQ : c ∈ pCoreOf 2 (hz T V) := by
      rw [hc, show b⁻¹ * (q * b * q⁻¹) = (b⁻¹ * q * b) * q⁻¹ by group]
      exact mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (inv_mem hbH))
        q).mp hq |> fun h' => by simpa using h') (inv_mem hq)
    set s := q * u * q⁻¹ * u⁻¹ with hs
    have hsV := C.comm_mem_V1_of_Q E hq huU
    have hqu : q * u * q⁻¹ = s * u := by rw [hs]; group
    have hqb' : q * b * q⁻¹ = b * c := by rw [hc]; group
    have hcu : c * u⁻¹ = u⁻¹ * c := hcent c ⟨hcUα, hcQ⟩ u⁻¹ (inv_mem huU)
    have hcH := pCoreOf_le 2 _ hcQ
    have hX : u * b * c * u⁻¹ ∈ hz T V :=
      mul_mem (mul_mem (mul_mem (hUH huU) hbH) hcH) (inv_mem (hUH huU))
    have hsX := hV1c s hsV _ hX
    have hcomm1 : q * (u * b * u⁻¹ * b⁻¹) * q⁻¹ = u * b * u⁻¹ * b⁻¹ := by
      calc q * (u * b * u⁻¹ * b⁻¹) * q⁻¹ =
          (q * u * q⁻¹) * (q * b * q⁻¹) * (q * u * q⁻¹)⁻¹ * (q * b * q⁻¹)⁻¹ := by group
        _ = (s * u) * (b * c) * (s * u)⁻¹ * (b * c)⁻¹ := by rw [hqu, hqb']
        _ = s * (u * b * c * u⁻¹) * s⁻¹ * c⁻¹ * b⁻¹ := by group
        _ = (u * b * c * u⁻¹) * c⁻¹ * b⁻¹ := by rw [hsX]; group
        _ = u * b * (c * u⁻¹) * c⁻¹ * b⁻¹ := by group
        _ = u * b * (u⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [hcu]
        _ = u * b * u⁻¹ * b⁻¹ := by group
    have hqt : q * t * q⁻¹ = t := by
      rw [← hV1c t ht q hqH, mul_inv_cancel_right]
    calc q * ((u * b * u⁻¹ * b⁻¹) * t) =
        (q * (u * b * u⁻¹ * b⁻¹) * q⁻¹) * (q * t * q⁻¹) * q := by group
      _ = (u * b * u⁻¹ * b⁻¹) * t * q := by rw [hcomm1, hqt]
  have hUeq : conjClosure V (hz T V) = fsuU T V := C.conjClosure_eq
  exact false_of_cent_F4 C.hyp hMod C.hF98 h1222 h1332 h1334 h13314 (hUeq ▸ hzαU) hcentV

theorem not_zα_le_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ¬ conjSub ((k : G) * g) (fsuV1 T V) ≤ conjClosure V (hz T V) := by
  intro hZU
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨z, hz1, hzne⟩ := C.exists_V1_ne
  obtain ⟨v, hv, hv1, hθv⟩ := C.θ_zα_mem_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N hz1 hzne hZU
  obtain ⟨l, hlL, hlH, hlθ⟩ := C.exists_l_of_V_F4 E h13322 hMod hVL hV₂ hv hv1
  have N' := N.mul_left C.hF98 (inv_mem hlL) (inv_mem hlH)
  have hx' : ((⟨l⁻¹, Subgroup.mem_sup_left (Subgroup.mem_sup_left (inv_mem hlL))⟩ * k :
      ↥((L ⊔ T) ⊔ hz T V)) : G) * g = l⁻¹ * ((k : G) * g) := by
    rw [Subgroup.coe_mul, mul_assoc]
  have hHU : conjSub l⁻¹ (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ (inv_mem hlH))
  refine C.zα_p0_false_F4 E hG h1332 h1334 hVL hV₂ h13314 h1222 N' hz1 hzne ?_ ?_
  · rw [hx', conjSub_mul, ← hHU]
    exact conjSub_mono _ hZU
  · rw [hx', show l⁻¹ * ((k : G) * g) * z * (l⁻¹ * ((k : G) * g))⁻¹ =
      l⁻¹ * (((k : G) * g) * z * ((k : G) * g)⁻¹) * l⁻¹⁻¹ by group,
      C.θG_conj E (inv_mem hlH) (hZU (mul_mem_conjSub hz1)), hθv, ← hlθ, C.ΦG_inv E hlH,
      map_inv, MulAut.inv_apply_self]

theorem not_V1_le_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ¬ fsuV1 T V ≤ conjSub ((k : G) * g) (conjClosure V (hz T V)) := by
  intro hle
  have h13322 := stmt13_3_2_two_of_F4 h1332
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨δ, δ', k₂, h₀, y, N'', hyU, -, -, -, -, hyV1''⟩ :=
    N.exists_sym_of_eq C (C.heq_of_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N)
  apply C.not_zα_le_F4 E hG h1332 h1334 hVL hV₂ h13314 h1222 N''
  have h1 : conjSub y⁻¹ (fsuV1 T V) = conjSub ((h₀ : G) * k₂) (fsuV1 T V) := by
    calc conjSub y⁻¹ (fsuV1 T V) =
        conjSub y⁻¹ (conjSub y (conjSub ((h₀ : G) * k₂) (fsuV1 T V))) := by rw [hyV1'']
      _ = conjSub ((h₀ : G) * k₂) (fsuV1 T V) := by
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  have h2 : conjSub y⁻¹ (conjSub ((k : G) * g) (conjClosure V (hz T V))) =
      conjClosure V (hz T V) := by
    calc conjSub y⁻¹ (conjSub ((k : G) * g) (conjClosure V (hz T V))) =
        conjSub y⁻¹ (conjSub y (conjClosure V (hz T V))) := by rw [hyU]
      _ = conjClosure V (hz T V) := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  rw [← h1, ← h2]
  exact conjSub_mono _ hle

end Ctx753

end CFSG.Quasithin.H13.L32A

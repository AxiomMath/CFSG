module

public import CFSG.Quasithin.H13.L32A758d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A753j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A756d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem exists_w_F4
    (C : Ctx753 T L V K) {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ}
    (E : Coord C e) (h38 : Lemma14_7_38_F4) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k)
    (hA0 : ∀ i, i ∈ idx (C.ΦX E (conjSub ((k : G) * g) (conjClosure V (hz T V)))) ↔
      i ∈ [0, 2, 4, 6, 8, 10, 12, 14])
    (hV1 : ¬ fsuV1 T V ≤ conjSub ((k : G) * g) (conjClosure V (hz T V)))
    {c : ℕ} (hc : c ∈ [2, 4, 6]) {h : G} (hhH : h ∈ hz T V)
    (hline : ∀ y ∈ conjSub h V, y ∉ fsuV1 T V →
      ∃ d ∈ M755.lineB c, d ≠ 0 ∧ C.θG e y = M755.ptQ d)
    (hcover : ∀ d ∈ M755.lineB c, d ≠ 0 →
      ∃ y ∈ conjSub h V, y ∉ fsuV1 T V ∧ C.θG e y = M755.ptQ d) :
    ∃ w ∈ conjClosure V (hz T V),
      (∀ a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)), a * w * a⁻¹ * w⁻¹ ∈ conjSub h V) ∧
      ∀ f ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
        ∃ a ∈ conjSub ((k : G) * g) (conjClosure V (hz T V)), a * w * a⁻¹ * w⁻¹ = f := by
  set x := (k : G) * g with hx
  have hUαH := N.uα_le_hz C
  have hAS := C.ΦX_le_sSubG E (N.uα_le_T C)
  obtain ⟨hqQ, hqO, hqline, hqonto, hqO7⟩ := M755.qc_facts c hc
  have hcA0 : c ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega
  have hc64 : c < 64 := (M755.a0_lt c hcA0).1
  obtain ⟨b, hb, hbe⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 ((hA0 c).2 hcA0)).2
  have hbH := hUαH hb
  have hNU : ∀ {g' : G}, g' ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      g' * a * g'⁻¹ ∈ conjClosure V (hz T V) := fun {g'} hg' {a} ha =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hg') a).mp ha
  have hV1h := C.V1_le_conj hhH
  have hinv : ∀ r : ModQ, r⁻¹ = r := fun r => inv_eq_of_mul_eq_one_right (M755.mul_self_Q r)

  have hθaw : ∀ {w : G}, w ∈ conjClosure V (hz T V) → C.θG e w = M755.ptQ (M755.qc c) →
      ∀ a ∈ conjSub x (conjClosure V (hz T V)), ∃ i ∈ [0, 2, 4, 6, 8, 10, 12, 14],
        C.ΦG E a = sEltG i ∧
          C.θG e (a * w * a⁻¹ * w⁻¹) = M755.ptQ (M755.actC i (M755.qc c) ^^^ M755.qc c) := by
    intro w hwU hw a ha
    obtain ⟨i, hi, hie⟩ := C.exists_idx E hUαH hAS ha
    have hiA := (hA0 i).1 hi
    refine ⟨i, hiA, hie, ?_⟩
    rw [C.θG_comm E (hUαH ha) hwU, hie, hw, M755.g2QAct_sEltG_code (M755.a0_lt i hiA).1 hqQ,
      hinv, M755.ptQ_xor (M755.actC_mem _ (M755.a0_lt i hiA).2 _ hqQ) hqQ]

  have hV1α : ∀ t ∈ fsuV1 T V, t ∈ conjSub x (conjClosure V (hz T V)) → t = 1 := by
    intro t ht htα
    by_contra ht1
    apply hV1
    intro v hv
    rcases M755.eq_one_or_eq_of_card_two C.card_V1 ht ht1 hv with rfl | rfl
    · exact one_mem _
    · exact htα

  have hinj : ∀ f₁ ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)),
      ∀ f₂ ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)),
        C.θG e f₁ = C.θG e f₂ → f₁ = f₂ := by
    rintro f₁ ⟨hf₁h, hf₁α⟩ f₂ ⟨hf₂h, hf₂α⟩ hθ
    have hV'U : ∀ {y}, y ∈ conjSub h V → y ∈ conjClosure V (hz T V) := fun {y} hy => by
      obtain ⟨v, hv, rfl⟩ := hy
      exact hNU hhH (le_conjClosure V _ hv)
    have hmem : f₁⁻¹ * f₂ ∈ conjSub h V := mul_mem (inv_mem hf₁h) hf₂h
    have h1 : C.θG e (f₁⁻¹ * f₂) = 1 := by
      rw [C.θG_mul e (inv_mem (hV'U hf₁h)) (hV'U hf₂h), C.θG_inv e (hV'U hf₁h), hθ,
        inv_mul_cancel]
    have hV1m : f₁⁻¹ * f₂ ∈ fsuV1 T V := by
      by_contra hnot
      obtain ⟨d, hd, hd0, hθd⟩ := hline _ hmem hnot
      rw [h1] at hθd
      exact M755.ptQ_ne_one (M755.line_facts.2.2.1 c hc d hd hd0) hθd.symm
    have := hV1α _ hV1m (mul_mem (inv_mem hf₁α) hf₂α)
    rw [inv_mul_eq_one] at this
    exact this

  have hfirst : ∃ w ∈ conjClosure V (hz T V), C.θG e w = M755.ptQ (M755.qc c) ∧
      ∀ a ∈ conjSub x (conjClosure V (hz T V)), a * w * a⁻¹ * w⁻¹ ∈ conjSub h V := by
    rcases C.lemma14_7_54_F4 h38 with ⟨hfix0, -⟩ | ⟨hcard, -, hW⟩
    ·
      have hker : ∀ u ∈ conjClosure V (hz T V), C.θG e u = 1 → u ∈ fsuV1 T V := by
        intro u hu h1
        rw [C.θG_eq e hu, C.θ_eq_one_iff e, hfix0, Subgroup.mem_bot] at h1
        exact (C.modMk_eq_one_iff' hu).1 h1
      obtain ⟨w, hwU, hw⟩ := C.exists_θG e (M755.ptQ (M755.qc c))
      refine ⟨w, hwU, hw, fun a ha => ?_⟩
      obtain ⟨i, hi, -, hθ⟩ := hθaw hwU hw a ha
      have hawU : a * w * a⁻¹ * w⁻¹ ∈ conjClosure V (hz T V) :=
        mul_mem (hNU (hUαH ha) hwU) (inv_mem hwU)
      by_cases hd0 : M755.actC i (M755.qc c) ^^^ M755.qc c = 0
      · rw [hd0, M755.ptQ_zero] at hθ
        exact hV1h (hker _ hawU hθ)
      · obtain ⟨t, ht, -, hθt⟩ := hcover _ (hqline i hi) hd0
        have htU : t ∈ conjClosure V (hz T V) := by
          obtain ⟨v, hv, rfl⟩ := ht
          exact hNU hhH (le_conjClosure V _ hv)
        have h1 : C.θG e (a * w * a⁻¹ * w⁻¹ * t⁻¹) = 1 := by
          rw [C.θG_mul e hawU (inv_mem htU), C.θG_inv e htU, hθ, hθt, mul_inv_cancel]
        have h2 := hker _ (mul_mem hawU (inv_mem htU)) h1
        have e1 : a * w * a⁻¹ * w⁻¹ = (a * w * a⁻¹ * w⁻¹ * t⁻¹) * t := by group
        rw [e1]
        exact mul_mem (hV1h h2) ht
    ·
      obtain ⟨ψ, hψ⟩ := M755.exists_equiv_of_g2WeylDerived hW
      obtain ⟨g₀, hg₀, hg₀θ⟩ := C.exists_g0 E hcard hψ

      have hψmk : ∀ y : ModO, ∃ u, ∃ hu : u ∈ conjClosure V (hz T V),
          ψ (modMk C.U_le_normalizer u hu) = y := by
        intro y
        obtain ⟨m, hm⟩ := ψ.surjective y
        obtain ⟨⟨u, huU⟩, hu⟩ := tildeHom_surjective C.U_le_normalizer m
        exact ⟨u, huU, by rw [← hm, ← hu]; rfl⟩

      have hcommO : ∀ {a : G} (ha : a ∈ hz T V) {i : ℕ}, i < 64 → C.ΦG E a = sEltG i →
          ∀ {u : G} (hu : u ∈ conjClosure V (hz T V)) {y : ℕ}, y ∈ o0Codes →
          ψ (modMk C.U_le_normalizer u hu) = g2OAct (ZMod 2) g₀ (M755.ptO y) →
          ψ (modMk C.U_le_normalizer (a * u * a⁻¹ * u⁻¹) (mul_mem (hNU ha hu) (inv_mem hu))) =
            g2OAct (ZMod 2) g₀ (M755.ptO (mact (sM i) y ^^^ y)) := by
        intro a ha i hi hai u hu y hy hψu
        have hm : mact (sM i) y ∈ o0Codes := by
          rw [← matCode_sEltG hi]
          exact mact_mem_o0Codes (sEltG i).2 hy
        have e1 : ψ (modMk C.U_le_normalizer (a * u * a⁻¹ * u⁻¹)
            (mul_mem (hNU ha hu) (inv_mem hu))) =
            ψ (modMk C.U_le_normalizer (a * u * a⁻¹) (hNU ha hu)) *
              (ψ (modMk C.U_le_normalizer u hu))⁻¹ := by
          rw [← map_inv, ← map_mul, ← modMk_inv C.U_le_normalizer hu,
            ← modMk_mul C.U_le_normalizer (hNU ha hu) (inv_mem hu)]
        have e2 : ψ (modMk C.U_le_normalizer (a * u * a⁻¹) (hNU ha hu)) =
            g2OAct (ZMod 2) (g₀ * sEltG i * g₀⁻¹) (ψ (modMk C.U_le_normalizer u hu)) := by
          have h1 := C.ψ_conj hψ ⟨a, ha⟩ hu
          rw [hg₀, ← C.ΦG_eq E ha, hai] at h1
          exact h1
        have e3 : g2OAct (ZMod 2) (g₀ * sEltG i * g₀⁻¹) (g2OAct (ZMod 2) g₀ (M755.ptO y)) =
            g2OAct (ZMod 2) g₀ (M755.ptO (mact (sM i) y)) := by
          rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv,
            MulAut.inv_apply_self, M755.g2OAct_ptO _ hy, matCode_sEltG hi]
        have e4 : (g2OAct (ZMod 2) g₀ (M755.ptO y))⁻¹ = g2OAct (ZMod 2) g₀ (M755.ptO y) := by
          rw [← map_inv, M755.ptO_inv]
        rw [e1, e2, hψu, e3, e4, ← map_mul, M755.ptO_mul hm hy]
      obtain ⟨w, hwU, hψw⟩ := hψmk (g2OAct (ZMod 2) g₀ (M755.ptO (M755.qc c)))
      have hθw : C.θG e w = M755.ptQ (M755.qc c) := by
        have h1 : g2QAct (ZMod 2) g₀ (C.θ e ⟨w, hwU⟩) =
            M755.projOQ (ψ (modMk C.U_le_normalizer w hwU)) := hg₀θ ⟨w, hwU⟩
        rw [hψw, M755.projOQ_act, M755.projOQ_ptO] at h1
        rw [C.θG_eq e hwU]
        exact (g2QAct (ZMod 2) g₀).injective h1
      refine ⟨w, hwU, hθw, fun a ha => ?_⟩
      obtain ⟨i, hi, hie⟩ := C.exists_idx E hUαH hAS ha
      have hiA := (hA0 i).1 hi
      have hi64 := (M755.a0_lt i hiA).1
      obtain ⟨y, hy, hyeq⟩ := hqO7 i hiA
      obtain ⟨u, huU, hψu⟩ := hψmk (g2OAct (ZMod 2) g₀ (M755.ptO y))
      have h1 := hcommO (hUαH ha) hi64 hie hwU hqO hψw
      have h2 := hcommO hbH hc64 hbe huU hy hψu
      rw [hyeq, ← h2] at h1
      have h3 := ψ.injective h1
      have h4 : (b * u * b⁻¹ * u⁻¹)⁻¹ * (a * w * a⁻¹ * w⁻¹) ∈ fsuV1 T V :=
        secMk_eq_secMk_iff.mp (congrArg Subtype.val h3.symm)
      have hbu : b * u * b⁻¹ * u⁻¹ ∈ conjSub h V := by
        have h5 := C.comm_mem_line_F4 E h13322 hMod hVL hV₂ hc hhH hline hcover hbH hbe huU
        have e : b * u * b⁻¹ * u⁻¹ = (u * b * u⁻¹ * b⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem h5
      have e : a * w * a⁻¹ * w⁻¹ =
          (b * u * b⁻¹ * u⁻¹) * ((b * u * b⁻¹ * u⁻¹)⁻¹ * (a * w * a⁻¹ * w⁻¹)) := by group
      rw [e]
      exact mul_mem hbu (hV1h h4)
  obtain ⟨w, hwU, hw, hw1⟩ := hfirst
  refine ⟨w, hwU, hw1, fun f hf => ?_⟩
  obtain ⟨hfh, hfα⟩ := hf
  by_cases hf1 : f ∈ fsuV1 T V
  · refine ⟨1, one_mem _, ?_⟩
    rw [hV1α f hf1 hfα]
    group
  obtain ⟨d, hd, -, hθf⟩ := hline f hfh hf1
  obtain ⟨i, hiA, hid⟩ := hqonto d hd
  obtain ⟨a, ha, hae⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 ((hA0 i).2 hiA)).2
  refine ⟨a, ha, hinj _ ⟨hw1 a ha, ?_⟩ _ ⟨hfh, hfα⟩ ?_⟩
  · have hwα : w * a⁻¹ * w⁻¹ ∈ conjSub x (conjClosure V (hz T V)) :=
      (Subgroup.mem_normalizer_iff.mp (conjSub_le_normalizer (le_normalizer_conjClosure V
        (hz T V)) x (N.conjClosure_le_Gα C hwU)) _).mp (inv_mem ha)
    rw [show a * w * a⁻¹ * w⁻¹ = a * (w * a⁻¹ * w⁻¹) by group]
    exact mul_mem ha hwα
  · rw [hθf, C.θG_comm E (hUαH ha) hwU, hae, hw,
      M755.g2QAct_sEltG_code (M755.a0_lt i hiA).1 hqQ, hinv,
      ← M755.ptQ_xor (M755.actC_mem _ (M755.a0_lt i hiA).2 _ hqQ) hqQ, hid]

end Ctx753

end CFSG.Quasithin.H13.L32A

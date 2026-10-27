module

public import CFSG.Quasithin.H13.L32A758e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A758a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A758d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem F_facts_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
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
    (∀ t ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)), t = 1 ∨
      ∃ d ∈ M755.lineB c, d ≠ 0 ∧ C.θG e t = M755.ptQ d) ∧
    (∀ t₁ ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
      ∀ t₂ ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
        C.θG e t₁ = C.θG e t₂ → t₁ = t₂) ∧
    ∀ d ∈ M755.lineB c, ∃ t ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
      C.θG e t = M755.ptQ d := by
  set x := (k : G) * g with hx
  have hUαH := N.uα_le_hz C
  have hNU : ∀ {g' : G}, g' ∈ hz T V → ∀ {a : G}, a ∈ conjClosure V (hz T V) →
      g' * a * g'⁻¹ ∈ conjClosure V (hz T V) := fun {g'} hg' {a} ha =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hg') a).mp ha
  have hV'U : ∀ {y}, y ∈ conjSub h V → y ∈ conjClosure V (hz T V) := fun {y} hy => by
    obtain ⟨v, hv, rfl⟩ := hy
    exact hNU hhH (le_conjClosure V _ hv)
  have hV1α : ∀ t ∈ fsuV1 T V, t ∈ conjSub x (conjClosure V (hz T V)) → t = 1 := by
    intro t ht htα
    by_contra ht1
    apply hV1
    intro v hv
    rcases M755.eq_one_or_eq_of_card_two C.card_V1 ht ht1 hv with rfl | rfl
    · exact one_mem _
    · exact htα
  refine ⟨fun t ht => ?_, ?_, fun d hd => ?_⟩
  · by_cases ht1 : t ∈ fsuV1 T V
    · exact Or.inl (hV1α t ht1 ht.2)
    · exact Or.inr (hline t ht.1 ht1)
  · rintro f₁ ⟨hf₁h, hf₁α⟩ f₂ ⟨hf₂h, hf₂α⟩ hθ
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
  ·
    have hcA0 : c ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; omega
    have hc64 : c < 64 := (M755.a0_lt c hcA0).1
    obtain ⟨b, hb, hbe⟩ := (C.mem_ΦX E hUαH).1 (mem_idx.1 ((hA0 c).2 hcA0)).2
    have hbH := hUαH hb
    obtain ⟨c', hc', hc'e⟩ := M755.facts_B0_onto c hc d hd
    obtain ⟨u, huU, hu⟩ := C.exists_θG e (M755.ptQ c')
    refine ⟨u * b * u⁻¹ * b⁻¹, Subgroup.mem_inf.mpr ⟨C.comm_mem_line_F4 E h13322 hMod hVL hV₂ hc
      hhH hline hcover hbH hbe huU, ?_⟩, ?_⟩
    · have hub : u * b * u⁻¹ ∈ conjSub x (conjClosure V (hz T V)) :=
        (Subgroup.mem_normalizer_iff.mp (conjSub_le_normalizer (le_normalizer_conjClosure V
          (hz T V)) x (N.conjClosure_le_Gα C huU)) _).mp hb
      exact mul_mem hub (inv_mem hb)
    · have hbu : b * u⁻¹ * b⁻¹ ∈ conjClosure V (hz T V) := hNU hbH (inv_mem huU)
      rw [show u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) by group, C.θG_mul e huU hbu,
        C.θG_conj E hbH (inv_mem huU), C.θG_inv e huU, map_inv, hu, hbe,
        M755.g2QAct_sEltG_code hc64 hc',
        show ∀ r : ModQ, r⁻¹ = r from fun r => inv_eq_of_mul_eq_one_right (M755.mul_self_Q r),
        ← M755.ptQ_xor hc' (M755.actC_mem _ (M755.a0_lt c hcA0).2 c' hc'), Nat.xor_comm, hc'e]

theorem exists_A0'_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hG : M755.G2Facts) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    (h13314 : A6.Stmt13_3_14_F4) (h1222 : Stmt12_2_2_F4) {γ γ' : F8.Geom T L (hz T V)}
    {g k : ↥((L ⊔ T) ⊔ hz T V)} (N : Not1471 T L V (hz T V) γ γ' g k) :
    ∃ l ∈ L, l ∈ hz T V ∧ ∃ k' : ↥((L ⊔ T) ⊔ hz T V), (k' : G) = l * k ∧
      Not1471 T L V (hz T V) γ γ' g k' ∧
      ∀ i, i ∈ idx (C.ΦX E (conjSub ((k' : G) * g) (conjClosure V (hz T V)))) ↔
        i ∈ [0, 2, 4, 6, 8, 10, 12, 14] := by
  obtain ⟨l, hlL, hlH, hidx⟩ := C.exists_A0_F4 E hG h13322 hMod hVL hV₂ h13314 h1222 N
  refine ⟨l, hlL, hlH, ⟨l, Subgroup.mem_sup_left (Subgroup.mem_sup_left hlL)⟩ * k, rfl,
    N.mul_left C.hF98 hlL hlH, fun i => ?_⟩
  rw [Subgroup.coe_mul, mul_assoc]
  exact hidx i

theorem lineData_F4
    (C : Ctx753 T L V K) {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ}
    (E : Coord C e) (h38 : Lemma14_7_38_F4) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k)
    (hA0 : ∀ i, i ∈ idx (C.ΦX E (conjSub ((k : G) * g) (conjClosure V (hz T V)))) ↔
      i ∈ [0, 2, 4, 6, 8, 10, 12, 14])
    (hV1 : ¬ fsuV1 T V ≤ conjSub ((k : G) * g) (conjClosure V (hz T V)))
    {δ δ' : F8.Geom T L (hz T V)} {g₂ k₂ : ↥((L ⊔ T) ⊔ hz T V)}
    (N₂ : Not1471 T L V (hz T V) δ δ' g₂ k₂)
    (hA0₂ : ∀ i, i ∈ idx (C.ΦX E (conjSub ((k₂ : G) * g₂) (conjClosure V (hz T V)))) ↔
      i ∈ [0, 2, 4, 6, 8, 10, 12, 14])
    (hV1₂ : ¬ fsuV1 T V ≤ conjSub ((k₂ : G) * g₂) (conjClosure V (hz T V))) {y : G}
    (hyU : conjSub y (conjClosure V (hz T V)) = conjSub ((k : G) * g) (conjClosure V (hz T V)))
    (hyU₂ : conjSub y (conjSub ((k₂ : G) * g₂) (conjClosure V (hz T V))) = conjClosure V (hz T V))
    {c : ℕ} (hc : c ∈ [2, 4, 6]) :
    ∃ h ∈ hz T V, conjSub h V₂ = V₂ ∧
      (∀ t ∈ conjSub h V, t ∉ fsuV1 T V →
        ∃ d ∈ M755.lineB c, d ≠ 0 ∧ C.θG e t = M755.ptQ d) ∧
      ∃ f ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
        C.θG e f = M755.ptQ 8 ∧
      ∃ g' ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
        C.θG e g' = M755.ptQ (M755.dc c) ∧
      (∀ t ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
        t = 1 ∨ t = f ∨ t = g' ∨ t = f * g') ∧
      ∃ c' ∈ [2, 4, 6], ∃ h' ∈ hz T V, conjSub h' V₂ = V₂ ∧
        (∀ t ∈ conjSub h' V, t ∉ fsuV1 T V →
          ∃ d ∈ M755.lineB c', d ≠ 0 ∧ C.θG e t = M755.ptQ d) ∧
        (∀ d ∈ M755.lineB c', d ≠ 0 →
          ∃ t ∈ conjSub h' V, t ∉ fsuV1 T V ∧ C.θG e t = M755.ptQ d) ∧
        ∀ t ∈ conjSub h V ⊓ conjSub ((k : G) * g) (conjClosure V (hz T V)),
          y⁻¹ * t * y ∈ conjSub h' V := by
  set x := (k : G) * g with hx
  obtain ⟨h, hhK, hhV₂, hline, hcover⟩ := C.exists_line_F4 E hMod hVL hV₂ hc
  have hhH := C.le_hz hhK
  obtain ⟨himg, hinj, hsurj⟩ :=
    C.F_facts_F4 E h13322 hMod hVL hV₂ N hA0 hV1 hc hhH hline hcover
  obtain ⟨hdc, hdc0, hdc8, hdcl, hdc8l⟩ := M755.dc_facts c hc
  have h8l : (8 : ℕ) ∈ M755.lineB c := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> decide
  obtain ⟨f, hf, hθf⟩ := hsurj 8 h8l
  obtain ⟨g', hg', hθg'⟩ := hsurj _ hdc
  have hV'U : ∀ {t}, t ∈ conjSub h V → t ∈ conjClosure V (hz T V) := fun {t} ht => by
    obtain ⟨v, hv, rfl⟩ := ht
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) hhH) v).mp
      (le_conjClosure V _ hv)

  have hstr : ∀ t ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)),
      t = 1 ∨ t = f ∨ t = g' ∨ t = f * g' := by
    intro t ht
    rcases himg t ht with h1 | ⟨d, hd, hd0, hθt⟩
    · exact Or.inl h1
    have h8 : (8 : ℕ) ∈ o0Codes := by decide
    have hdcO : M755.dc c ∈ o0Codes := (M755.qCodes_mem _ (M755.line_facts.2.2.2 c hc _ hdc)).1
    rcases hdcl d hd with rfl | rfl | rfl | rfl
    · exact absurd rfl hd0
    · exact Or.inr (Or.inl (hinj t ht f hf (hθt.trans hθf.symm)))
    · exact Or.inr (Or.inr (Or.inl (hinj t ht g' hg' (hθt.trans hθg'.symm))))
    · refine Or.inr (Or.inr (Or.inr (hinj t ht _ (mul_mem hf hg') ?_)))
      rw [hθt, C.θG_mul e (hV'U hf.1) (hV'U hg'.1), hθf, hθg', M755.ptQ_mul h8 hdcO]

  obtain ⟨w, hwU, hw1, hw2⟩ :=
    C.exists_w_F4 E h38 h13322 hMod hVL hV₂ N hA0 hV1 hc hhH hline hcover

  have hw' : y⁻¹ * w * y ∈ conjSub ((k₂ : G) * g₂) (conjClosure V (hz T V)) := by
    rw [← hyU₂] at hwU
    exact mem_conjSub.1 hwU
  have hconjU : ∀ {a}, a ∈ conjSub x (conjClosure V (hz T V)) →
      y⁻¹ * a * y ∈ conjClosure V (hz T V) := fun {a} ha => by
    rw [← hyU] at ha
    exact mem_conjSub.1 ha
  have hconjα : ∀ {u}, u ∈ conjClosure V (hz T V) →
      y * u * y⁻¹ ∈ conjSub x (conjClosure V (hz T V)) := fun {u} hu => by
    rw [← hyU]
    exact mul_mem_conjSub hu
  have hcommw : ∀ u ∈ conjClosure V (hz T V), u * (y⁻¹ * w * y) * u⁻¹ * (y⁻¹ * w * y)⁻¹ =
      y⁻¹ * ((y * u * y⁻¹) * w * (y * u * y⁻¹)⁻¹ * w⁻¹) * y := by
    intro u _
    group
  have hFα : ∀ {a}, a ∈ conjSub x (conjClosure V (hz T V)) →
      a * w * a⁻¹ * w⁻¹ ∈ conjSub h V ⊓ conjSub x (conjClosure V (hz T V)) := fun {a} ha => by
    refine ⟨hw1 a ha, ?_⟩
    have hwα : w * a⁻¹ * w⁻¹ ∈ conjSub x (conjClosure V (hz T V)) :=
      (Subgroup.mem_normalizer_iff.mp (conjSub_le_normalizer (le_normalizer_conjClosure V
        (hz T V)) x (N.conjClosure_le_Gα C hwU)) _).mp (inv_mem ha)
    rw [show a * w * a⁻¹ * w⁻¹ = a * (w * a⁻¹ * w⁻¹) by group]
    exact mul_mem ha hwα

  obtain ⟨c', hc', hΦw'⟩ := C.B0_of_small E N₂ hA0₂ hV1₂ hw' (hconjU hf.2) (hconjU hg'.2)
    (fun u hu => by
      rw [hcommw u hu]
      rcases hstr _ (hFα (hconjα hu)) with h1 | h1 | h1 | h1 <;> rw [h1]
      · left; group
      · right; left; rfl
      · right; right; left; rfl
      · right; right; right; group)
    (by
      obtain ⟨a₀, ha₀, ha₀e⟩ := hw2 f hf
      refine ⟨y⁻¹ * a₀ * y, hconjU ha₀, fun h1 => ?_⟩
      rw [hcommw _ (hconjU ha₀), show y * (y⁻¹ * a₀ * y) * y⁻¹ = a₀ by group, ha₀e] at h1
      have hf1 : f = 1 := by
        have := congrArg (fun t => y * t * y⁻¹) h1
        simpa [mul_assoc] using this
      rw [hf1, C.θG_V1 e (one_mem _)] at hθf
      exact M755.ptQ_ne_one (by decide) hθf.symm)
  obtain ⟨h', hh'K, hh'V₂, hline', hcover'⟩ := C.exists_line_F4 E hMod hVL hV₂ hc'
  have hh'H := C.le_hz hh'K
  refine ⟨h, hhH, hhV₂, hline, f, hf, hθf, g', hg', hθg', hstr, c', hc', h', hh'H, hh'V₂, hline',
    hcover', fun t ht => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hw2 t ht
  have hu := hconjU ha
  have h1 := C.comm_mem_line_F4 E h13322 hMod hVL hV₂ hc' hh'H hline' hcover'
    ((N₂.uα_le_hz C) hw') hΦw' hu
  rw [hcommw _ hu, show y * (y⁻¹ * a * y) * y⁻¹ = a by group] at h1
  exact h1

end Ctx753

end CFSG.Quasithin.H13.L32A

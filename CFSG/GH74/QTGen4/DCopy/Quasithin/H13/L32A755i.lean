module

public import CFSG.Quasithin.H13.L32A755i
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A755e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ARuOne

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit

namespace Ctx753

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

theorem exists_hz_of_V_F4 (C : Ctx753 T L V K) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    {g : G} (hg : fsuV1 T V ≤ conjSub g V) : ∃ c ∈ hz T V, conjSub g V = conjSub c V := by
  have h1281 := C.hyp.hyp1281One_F4 h13322 hMod
  obtain ⟨-, hV8, hLTV, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨z, hz1, hzne⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra h
    push Not at h
    have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot] at hV1
    omega
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hz1
  have hz' : g⁻¹ * z * g ∈ V := mem_conjSub.1 (hg hz1)
  have hz'1 : g⁻¹ * z * g ≠ 1 := fun h => hzne (by
    have := congrArg (fun x => g * x * g⁻¹) h
    simpa [mul_assoc] using this)

  obtain ⟨l, hlL, hlz⟩ : ∃ l ∈ L, l * z * l⁻¹ = g⁻¹ * z * g := by
    by_cases he : z = g⁻¹ * z * g
    · exact ⟨1, L.one_mem, by rw [← he]; group⟩
    · obtain ⟨a, haV, ha1, haz⟩ : ∃ a ∈ V, a ≠ 1 ∧ a ≠ z := by
        by_contra h
        push Not at h
        have : V ≤ fsuV1 T V := fun a ha => by
          by_cases ha1 : a = 1
          · rw [ha1]; exact Subgroup.one_mem _
          · rw [h a ha ha1]; exact hz1
        have := Subgroup.card_le_of_le this
        omega
      obtain ⟨b, hbV, hb1, hbz⟩ : ∃ b ∈ V, b ≠ 1 ∧ b ≠ g⁻¹ * z * g := by
        by_contra h
        push Not at h
        have : V ≤ Subgroup.zpowers (g⁻¹ * z * g) := fun b hb => by
          by_cases hb1 : b = 1
          · rw [hb1]; exact Subgroup.one_mem _
          · rw [h b hb hb1]; exact Subgroup.mem_zpowers _
        have h2 := Subgroup.card_le_of_le this
        rw [Nat.card_zpowers] at h2
        have : orderOf (g⁻¹ * z * g) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (by
          have := (hMod G T L V C.hyp.hyp C.hyp.fsu).1.2 _ hz'
          exact this)
        omega
      obtain ⟨l, hl, h1, -⟩ := exists_conj_eq_pair h1281 hzV haV hz' hbV hzne ha1 hz'1 hb1
        (Ne.symm haz) (Ne.symm hbz)
      exact ⟨l, hl, h1⟩
  refine ⟨g * l, C.mem_hz_of_comm hz1 hzne ?_, ?_⟩
  · calc g * l * z * (g * l)⁻¹ = g * (l * z * l⁻¹) * g⁻¹ := by group
      _ = z := by rw [hlz]; group
  · have hlV : conjSub l V = V :=
      conjSub_eq_self_iff.2 ((le_sup_left : L ≤ L ⊔ T).trans hLTV hlL)
    rw [conjSub_mul, hlV]

theorem exists_hz_of_V2_F4 (C : Ctx753 T L V K) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {g : G} (hg : fsuV1 T V ≤ conjSub g V₂) :
    ∃ c ∈ hz T V, conjSub g V₂ = conjSub c V₂ := by
  have h1281 := C.hyp.hyp1281One_F4 h13322 hMod
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨hV₁V₂, hV₂V, -, hV₂4⟩ := hV₂
  obtain ⟨z, hz1, hzne⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra h
    push Not at h
    have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
    rw [this, Subgroup.card_bot] at hV1
    omega
  have hzV₂ : z ∈ V₂ := hV₁V₂ hz1
  have hz' : g⁻¹ * z * g ∈ V₂ := mem_conjSub.1 (hg hz1)
  have hz'1 : g⁻¹ * z * g ≠ 1 := fun h => hzne (by
    have := congrArg (fun x => g * x * g⁻¹) h
    simpa [mul_assoc] using this)

  have hother : ∀ x ∈ V₂, x ≠ 1 → ∃ a ∈ V₂, a ≠ 1 ∧ a ≠ x := by
    intro x hx hx1
    by_contra h
    push Not at h
    have : V₂ ≤ Subgroup.zpowers x := fun b hb => by
      by_cases hb1 : b = 1
      · rw [hb1]; exact Subgroup.one_mem _
      · rw [h b hb hb1]; exact Subgroup.mem_zpowers _
    have h2 := Subgroup.card_le_of_le this
    rw [Nat.card_zpowers] at h2
    have : orderOf x ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) (hVe.2 _ (hV₂V hx))
    omega
  obtain ⟨a, haV₂, ha1, haz⟩ := hother z hzV₂ hzne
  obtain ⟨b, hbV₂, hb1, hbz⟩ := hother _ hz' hz'1
  obtain ⟨l, hl, h1, h2⟩ := exists_conj_eq_pair h1281 (hV₂V hzV₂) (hV₂V haV₂) (hV₂V hz')
    (hV₂V hbV₂) hzne ha1 hz'1 hb1 (Ne.symm haz) (Ne.symm hbz)

  have hlV : l ∈ Subgroup.normalizer (V : Set G) := (le_sup_left : L ≤ L ⊔ T).trans hLTV hl
  have hV₂cl : ∀ x ∈ V₂, x = 1 ∨ x = z ∨ x = a ∨ x = z * a := by
    intro x hx
    have hcomm : ∀ u ∈ V, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
      have := hVe.1
      exact setLike_mul_comm hu hv
    have haV1 : a ∉ fsuV1 T V := fun h => by
      rcases M755.eq_one_or_eq_of_card_two hV1 hz1 hzne h with h' | h'
      · exact ha1 h'
      · exact haz h'
    by_cases hxV1 : x ∈ fsuV1 T V
    · rcases M755.eq_one_or_eq_of_card_two hV1 hz1 hzne hxV1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · have hax := inv_mul_mem_of_two hV₁V₂ (by rw [hV1, hV₂4]) haV₂ hx haV1 hxV1
      rcases M755.eq_one_or_eq_of_card_two hV1 hz1 hzne hax with h' | h'
      · right; right; left
        rw [inv_mul_eq_one] at h'
        exact h'.symm
      · right; right; right
        have e : x = a * z := by rw [← h']; group
        rw [e, hcomm a (hV₂V haV₂) z (hV₂V hzV₂)]
  have hlV₂ : conjSub l V₂ = V₂ := by
    have hle : conjSub l V₂ ≤ V₂ := by
      rintro _ ⟨x, hx, rfl⟩
      change l * x * l⁻¹ ∈ V₂
      rcases hV₂cl x hx with rfl | rfl | rfl | rfl
      · simp
      · rw [h1]; exact hz'
      · rw [h2]; exact hbV₂
      · have e : l * (z * a) * l⁻¹ = (l * z * l⁻¹) * (l * a * l⁻¹) := by group
        rw [e, h1, h2]
        exact V₂.mul_mem hz' hbV₂
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [show Nat.card ↥(conjSub l V₂) = Nat.card V₂ from
      Subgroup.card_map_of_injective (MulAut.conj l).injective]
  refine ⟨g * l, C.mem_hz_of_comm hz1 hzne ?_, ?_⟩
  · calc g * l * z * (g * l)⁻¹ = g * (l * z * l⁻¹) * g⁻¹ := by group
      _ = z := by rw [h1]; group
  · rw [conjSub_mul, hlV₂]

theorem conjSub_V2_eq_F4 (C : Ctx753 T L V K) (hMod : StmtL32NModule_F4) {V₂ : Subgroup G}
    (hV₂ : A6.IsV2 T V V₂) {k w : G} (hk : k ∈ hz T V) (hw : w ∈ V₂) (hw1 : w ∉ fsuV1 T V)
    (hkw : w⁻¹ * (k * w * k⁻¹) ∈ fsuV1 T V) : conjSub k V₂ = V₂ := by
  obtain ⟨hV₁V₂, hV₂V, -, hV₂4⟩ := hV₂
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  have hcen : ∀ v ∈ fsuV1 T V, k * v * k⁻¹ = v := fun v hv => by
    rw [← Subgroup.mem_centralizer_iff.mp hk v hv, mul_inv_cancel_right]
  have hle : conjSub k V₂ ≤ V₂ := by
    rintro _ ⟨x, hx, rfl⟩
    change k * x * k⁻¹ ∈ V₂
    by_cases hx1 : x ∈ fsuV1 T V
    · rw [hcen x hx1]; exact hx
    · have hwx := inv_mul_mem_of_two hV₁V₂ (by rw [hV1, hV₂4]) hw hx hw1 hx1
      have e : k * x * k⁻¹ = (k * w * k⁻¹) * (k * (w⁻¹ * x) * k⁻¹) := by group
      rw [e, hcen _ hwx]
      have h1 : k * w * k⁻¹ ∈ V₂ := by
        have e2 : k * w * k⁻¹ = w * (w⁻¹ * (k * w * k⁻¹)) := by group
        rw [e2]
        exact V₂.mul_mem hw (hV₁V₂ hkw)
      exact V₂.mul_mem h1 (hV₁V₂ hwx)
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [show Nat.card ↥(conjSub k V₂) = Nat.card V₂ from
      Subgroup.card_map_of_injective (MulAut.conj k).injective])

theorem exists_pt_F4 (C : Ctx753 T L V K) (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {X : Subgroup G} {g : G} (hX : X = conjSub g V₂)
    (hZ : fsuV1 T V ≤ X) : ∃ c ∈ hz T V, X = conjSub c V₂ ∧ ∃ x ∈ X, x ∉ fsuV1 T V := by
  subst hX
  obtain ⟨c, hc, hgc⟩ := C.exists_hz_of_V2_F4 h13322 hMod hV₂ hZ
  obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ V₂, w ∉ fsuV1 T V := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (show V₂ ≤ fsuV1 T V from h)
    rw [hV1, hV₂.2.2.2] at this
    omega
  refine ⟨c, hc, hgc, c * w * c⁻¹, hgc ▸ mul_mem_conjSub hw, fun h => hw1 ?_⟩
  have := C.conj_V1 (inv_mem hc) h
  rw [show c⁻¹ * (c * w * c⁻¹) * c⁻¹⁻¹ = w by group] at this
  rw [this]
  exact h

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem θG_V2_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {w : G} (hw : w ∈ V₂) (hw1 : w ∉ fsuV1 T V) : C.θG e w = M755.ptQ 8 := by
  rw [C.θG_eq e (le_conjClosure V (hz T V) (hV₂.2.1 hw))]
  exact C.coord_V2_F4 hMod hVL E.mem_T hV₂ hw hw1

theorem θG_V_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {v : G} (hv : v ∈ V) (hv1 : v ∉ fsuV1 T V) :
    ∃ d ∈ [8, 32, 40], C.θG e v = M755.ptQ d := by
  by_cases hv2 : v ∈ V₂
  · exact ⟨8, by simp, C.θG_V2_F4 E hMod hVL hV₂ hv2 hv1⟩
  · rw [C.θG_eq e (le_conjClosure V (hz T V) hv)]
    rcases C.coord_V_F4 hMod hVL E.mem_T hV₂ hv hv2 with h | h
    · exact ⟨32, by simp, h⟩
    · exact ⟨40, by simp, h⟩

theorem θG_pt_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {c x : G} (hc : c ∈ hz T V) (hx : x ∈ conjSub c V₂) (hx1 : x ∉ fsuV1 T V) :
    C.θG e x = g2QAct (ZMod 2) (C.ΦG E c) (M755.ptQ 8) := by
  obtain ⟨w, hw, hw1, rfl⟩ := C.exists_of_mem_conjSub hc hx hx1
  rw [C.θG_conj E hc (le_conjClosure V (hz T V) (hV₂.2.1 hw)), C.θG_V2_F4 E hMod hVL hV₂ hw hw1]

theorem θG_ln_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {c y : G} (hc : c ∈ hz T V) (hy : y ∈ conjSub c V) (hy1 : y ∉ fsuV1 T V) :
    ∃ d ∈ [8, 32, 40], C.θG e y = g2QAct (ZMod 2) (C.ΦG E c) (M755.ptQ d) := by
  obtain ⟨v, hv, hv1, rfl⟩ := C.exists_of_mem_conjSub hc hy hy1
  obtain ⟨d, hd, hθ⟩ := C.θG_V_F4 E hMod hVL hV₂ hv hv1
  exact ⟨d, hd, by rw [C.θG_conj E hc (le_conjClosure V (hz T V) hv), hθ]⟩

theorem coll_ln_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {c y y' : G} (hc : c ∈ hz T V) (hy : y ∈ conjSub c V) (hy1 : y ∉ fsuV1 T V)
    (hy' : y' ∈ conjSub c V) (hy'1 : y' ∉ fsuV1 T V) (hne : C.θG e y ≠ C.θG e y') :
    M755.CollQ (C.θG e y) (C.θG e y') := by
  obtain ⟨d, hd, hθ⟩ := C.θG_ln_F4 E hMod hVL hV₂ hc hy hy1
  obtain ⟨d', hd', hθ'⟩ := C.θG_ln_F4 E hMod hVL hV₂ hc hy' hy'1
  rw [hθ, hθ', M755.collQ_act]
  have hdd : d ≠ d' := fun h => hne (by rw [hθ, hθ', h])
  have key : ∀ d ∈ [8, 32, 40], ∀ d' ∈ [8, 32, 40], d ≠ d' →
      d ∈ M755.ptsQ ∧ d' ∈ M755.ptsQ ∧ M755.collT d d' = true := by decide
  obtain ⟨h1, h2, h3⟩ := key d hd d' hd' hdd
  exact (M755.collQ_ptQ h1 h2).2 h3

theorem eq_of_θG_pt_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆) {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂)
    {c c' x x' : G} (hc : c ∈ hz T V) (hc' : c' ∈ hz T V) (hx : x ∈ conjSub c V₂)
    (hx1 : x ∉ fsuV1 T V) (hx' : x' ∈ conjSub c' V₂) (hx'1 : x' ∉ fsuV1 T V)
    (h : C.θG e x = C.θG e x') : conjSub c V₂ = conjSub c' V₂ := by
  obtain ⟨w, hw, hw1, rfl⟩ := C.exists_of_mem_conjSub hc hx hx1
  have hwU := le_conjClosure V (hz T V) (hV₂.2.1 hw)
  have hk : c'⁻¹ * c ∈ hz T V := mul_mem (inv_mem hc') hc
  have hθ : C.θG e ((c'⁻¹ * c) * w * (c'⁻¹ * c)⁻¹) = C.θG e w := by
    rw [C.θG_conj E hk hwU, C.ΦG_mul E (inv_mem hc') hc, C.ΦG_inv E hc', map_mul,
      MulAut.mul_apply, ← C.θG_conj E hc hwU, h, C.θG_pt_F4 E hMod hVL hV₂ hc' hx' hx'1,
      ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply,
      C.θG_V2_F4 E hMod hVL hV₂ hw hw1]
  have hkw := C.mem_V1_of_θG E hk hwU hθ
  have hV₂k := C.conjSub_V2_eq_F4 hMod hV₂ hk hw hw1 hkw
  calc conjSub c V₂ = conjSub (c' * (c'⁻¹ * c)) V₂ := by rw [mul_inv_cancel_left]
    _ = conjSub c' V₂ := by rw [conjSub_mul, hV₂k]

theorem no_four_cycle₀_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Subgroup G}
    {g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ : G} (hX₁ : X₁ = conjSub g₁ V₂) (hX₂ : X₂ = conjSub g₂ V₂)
    (hX₃ : X₃ = conjSub g₃ V₂) (hX₄ : X₄ = conjSub g₄ V₂) (hY₁ : Y₁ = conjSub k₁ V)
    (hY₂ : Y₂ = conjSub k₂ V) (hY₃ : Y₃ = conjSub k₃ V) (hY₄ : Y₄ = conjSub k₄ V)
    (hZ₁ : fsuV1 T V ≤ X₁) (hZ₂ : fsuV1 T V ≤ X₂) (hZ₃ : fsuV1 T V ≤ X₃)
    (hZ₄ : fsuV1 T V ≤ X₄) (h11 : X₁ ≤ Y₁) (h21 : X₂ ≤ Y₁) (h22 : X₂ ≤ Y₂) (h32 : X₃ ≤ Y₂)
    (h33 : X₃ ≤ Y₃) (h43 : X₄ ≤ Y₃) (h44 : X₄ ≤ Y₄) (h14 : X₁ ≤ Y₄) (hne13 : X₁ ≠ X₃)
    (hne24 : X₂ ≠ X₄) (hne12 : X₁ ≠ X₂) (hne23 : X₂ ≠ X₃) (hne34 : X₃ ≠ X₄)
    (hne41 : X₄ ≠ X₁) : False := by
  obtain ⟨c₁, hc₁, hX₁c, x₁, hx₁, hx₁1⟩ := C.exists_pt_F4 h13322 hMod hV₂ hX₁ hZ₁
  obtain ⟨c₂, hc₂, hX₂c, x₂, hx₂, hx₂1⟩ := C.exists_pt_F4 h13322 hMod hV₂ hX₂ hZ₂
  obtain ⟨c₃, hc₃, hX₃c, x₃, hx₃, hx₃1⟩ := C.exists_pt_F4 h13322 hMod hV₂ hX₃ hZ₃
  obtain ⟨c₄, hc₄, hX₄c, x₄, hx₄, hx₄1⟩ := C.exists_pt_F4 h13322 hMod hV₂ hX₄ hZ₄
  obtain ⟨d₁, hd₁, hY₁d⟩ := C.exists_hz_of_V_F4 h13322 hMod (hY₁ ▸ hZ₁.trans h11)
  obtain ⟨d₂, hd₂, hY₂d⟩ := C.exists_hz_of_V_F4 h13322 hMod (hY₂ ▸ hZ₂.trans h22)
  obtain ⟨d₃, hd₃, hY₃d⟩ := C.exists_hz_of_V_F4 h13322 hMod (hY₃ ▸ hZ₃.trans h33)
  obtain ⟨d₄, hd₄, hY₄d⟩ := C.exists_hz_of_V_F4 h13322 hMod (hY₄ ▸ hZ₄.trans h44)
  rw [hY₁, hY₁d] at h11 h21
  rw [hY₂, hY₂d] at h22 h32
  rw [hY₃, hY₃d] at h33 h43
  rw [hY₄, hY₄d] at h44 h14

  have hne : ∀ {X X' : Subgroup G} {c c' x x' : G}, c ∈ hz T V → c' ∈ hz T V →
      X = conjSub c V₂ → X' = conjSub c' V₂ → x ∈ X → x ∉ fsuV1 T V → x' ∈ X' →
      x' ∉ fsuV1 T V → X ≠ X' → C.θG e x ≠ C.θG e x' := by
    intro X X' c c' x x' hc hc' hXc hX'c hx hx1 hx' hx'1 hXX' hθ
    apply hXX'
    rw [hXc, hX'c]
    exact C.eq_of_θG_pt_F4 E hMod hVL hV₂ hc hc' (hXc ▸ hx) hx1 (hX'c ▸ hx') hx'1 hθ
  have p12 := C.coll_ln_F4 E hMod hVL hV₂ hd₁ (h11 hx₁) hx₁1 (h21 hx₂) hx₂1
    (hne hc₁ hc₂ hX₁c hX₂c hx₁ hx₁1 hx₂ hx₂1 hne12)
  have p32 := C.coll_ln_F4 E hMod hVL hV₂ hd₂ (h32 hx₃) hx₃1 (h22 hx₂) hx₂1
    (hne hc₃ hc₂ hX₃c hX₂c hx₃ hx₃1 hx₂ hx₂1 hne23.symm)
  have p34 := C.coll_ln_F4 E hMod hVL hV₂ hd₃ (h33 hx₃) hx₃1 (h43 hx₄) hx₄1
    (hne hc₃ hc₄ hX₃c hX₄c hx₃ hx₃1 hx₄ hx₄1 hne34)
  have p14 := C.coll_ln_F4 E hMod hVL hV₂ hd₄ (h14 hx₁) hx₁1 (h44 hx₄) hx₄1
    (hne hc₁ hc₄ hX₁c hX₄c hx₁ hx₁1 hx₄ hx₄1 hne41.symm)
  exact hne hc₂ hc₄ hX₂c hX₄c hx₂ hx₂1 hx₄ hx₄1 hne24
    (M755.collQ_common (hne hc₁ hc₃ hX₁c hX₃c hx₁ hx₁1 hx₃ hx₃1 hne13) p12 p32 p14 p34)

theorem no_four_cycle_F4 (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two_F4) (hMod : StmtL32NModule_F4) (hVL : V ≤ ⁅V, l1 T L V⁆)
    {V₂ : Subgroup G} (hV₂ : A6.IsV2 T V V₂) (l : G) {X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Y₄ : Subgroup G}
    {g₁ g₂ g₃ g₄ k₁ k₂ k₃ k₄ : G} (hX₁ : X₁ = conjSub g₁ V₂) (hX₂ : X₂ = conjSub g₂ V₂)
    (hX₃ : X₃ = conjSub g₃ V₂) (hX₄ : X₄ = conjSub g₄ V₂) (hY₁ : Y₁ = conjSub k₁ V)
    (hY₂ : Y₂ = conjSub k₂ V) (hY₃ : Y₃ = conjSub k₃ V) (hY₄ : Y₄ = conjSub k₄ V)
    (hZ₁ : conjSub l (fsuV1 T V) ≤ X₁) (hZ₂ : conjSub l (fsuV1 T V) ≤ X₂)
    (hZ₃ : conjSub l (fsuV1 T V) ≤ X₃) (hZ₄ : conjSub l (fsuV1 T V) ≤ X₄) (h11 : X₁ ≤ Y₁)
    (h21 : X₂ ≤ Y₁) (h22 : X₂ ≤ Y₂) (h32 : X₃ ≤ Y₂) (h33 : X₃ ≤ Y₃) (h43 : X₄ ≤ Y₃)
    (h44 : X₄ ≤ Y₄) (h14 : X₁ ≤ Y₄) (hne13 : X₁ ≠ X₃) (hne24 : X₂ ≠ X₄) (hne12 : X₁ ≠ X₂)
    (hne23 : X₂ ≠ X₃) (hne34 : X₃ ≠ X₄) (hne41 : X₄ ≠ X₁) : False := by
  have hZ : ∀ {X : Subgroup G}, conjSub l (fsuV1 T V) ≤ X → fsuV1 T V ≤ conjSub l⁻¹ X :=
    fun h => (conjSub_conjSub_inv l (fsuV1 T V)) ▸ conjSub_mono l⁻¹ h
  have hne : ∀ {X X' : Subgroup G}, X ≠ X' → conjSub l⁻¹ X ≠ conjSub l⁻¹ X' :=
    fun h h' => h ((conjSub_inj l⁻¹).1 h')
  exact C.no_four_cycle₀_F4 E h13322 hMod hVL hV₂ (g₁ := l⁻¹ * g₁) (g₂ := l⁻¹ * g₂)
    (g₃ := l⁻¹ * g₃) (g₄ := l⁻¹ * g₄) (k₁ := l⁻¹ * k₁) (k₂ := l⁻¹ * k₂) (k₃ := l⁻¹ * k₃)
    (k₄ := l⁻¹ * k₄) (by rw [hX₁, conjSub_mul]) (by rw [hX₂, conjSub_mul])
    (by rw [hX₃, conjSub_mul]) (by rw [hX₄, conjSub_mul]) (by rw [hY₁, conjSub_mul])
    (by rw [hY₂, conjSub_mul]) (by rw [hY₃, conjSub_mul]) (by rw [hY₄, conjSub_mul])
    (hZ hZ₁) (hZ hZ₂) (hZ hZ₃) (hZ hZ₄) (conjSub_mono _ h11) (conjSub_mono _ h21)
    (conjSub_mono _ h22) (conjSub_mono _ h32) (conjSub_mono _ h33) (conjSub_mono _ h43)
    (conjSub_mono _ h44) (conjSub_mono _ h14) (hne hne13) (hne hne24) (hne hne12) (hne hne23)
    (hne hne34) (hne hne41)

end Ctx753

end CFSG.Quasithin.H13.L32A

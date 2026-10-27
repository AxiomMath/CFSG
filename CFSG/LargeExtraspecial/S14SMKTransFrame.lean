module

public import CFSG.LargeExtraspecial.S14SMKTransFp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Fischer.Native Matrix

section Frame


theorem exists_smul_of_piSU_fix (g : SU0) {x : ℕ} (hx : x < 693)
    (h : piSU g ⟨x, hx⟩ = ⟨x, hx⟩) :
    ∃ c : F4, c ≠ 0 ∧ ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ uVec x = c • uVec x := by
  set M := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hv := uVec_ne_zero ptsFacts hx
  have hw : M *ᵥ uVec x ≠ 0 := by
    intro h0
    apply hv
    have := congrArg (fun w => ((g⁻¹ : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ w) h0
    simpa [M, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  have hiso : hermStd (M *ᵥ uVec x) (M *ᵥ uVec x) = 0 := by
    have e := (SU0_le_GU0 g.2 : IsIsom M) (uVec x) (uVec x)
    rw [herm_eq_std, herm_eq_std] at e
    rw [e]
    exact uVec_iso ptsFacts hx
  have e1 : ptIdx (M *ᵥ uVec x) = x := by
    have := piSU_apply g ⟨x, hx⟩
    rw [h] at this
    exact this.symm
  obtain ⟨c, hc, hn⟩ := normV_eq_smul hw
  have e2 : uVec x = c • (M *ᵥ uVec x) := by
    conv_lhs => rw [← e1]
    rw [uVec_ptIdx ptsFacts hw hiso, hn]
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  calc M *ᵥ uVec x = c⁻¹ • (c • M *ᵥ uVec x) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = c⁻¹ • uVec x := by rw [← e2]

theorem smul_add_smul_eq_zero {x y : ℕ} (hx : x < 693) (hy : y < 693) (hxy : x ≠ y) {a b : F4}
    (h : a • uVec x + b • uVec y = 0) : a = 0 ∧ b = 0 := by
  have hvx := uVec_ne_zero ptsFacts hx
  have hvy := uVec_ne_zero ptsFacts hy
  by_cases ha : a = 0
  · rw [ha, zero_smul, zero_add, smul_eq_zero] at h
    exact ⟨ha, h.resolve_right hvy⟩
  · exfalso
    by_cases hb : b = 0
    · rw [hb, zero_smul, add_zero, smul_eq_zero] at h
      exact hvx (h.resolve_left ha)
    · have e : uVec x = (-(a⁻¹ * b)) • uVec y := by
        have := congrArg (fun w => a⁻¹ • w) h
        simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul, smul_zero] at this
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact this
      have hc : -(a⁻¹ * b) ≠ 0 := neg_ne_zero.2 (mul_ne_zero (inv_ne_zero ha) hb)
      apply hxy
      rw [← ptIdx_uVec ptsFacts hx, ← ptIdx_uVec ptsFacts hy, e, ptIdx_smul hc]


theorem eq_one_of_frame {ρ : Equiv.Perm (Fin 693)} (hρ : ρ ∈ T46) {fx : List ℕ}
    (hlt : ∀ x ∈ fx, x < 693) (hnd : fx.Nodup) (hne : fx ≠ [])
    (hfix : ∀ x (hx : x ∈ fx), ρ ⟨x, hlt x hx⟩ = ⟨x, hlt x hx⟩)
    (hline : ∀ k, k + 1 < fx.length → ∃ m ≤ k, ∃ n < fx.length, ∃ l u : F4, l ≠ 0 ∧ u ≠ 0 ∧
      uVec (fx.getD n 0) = l • uVec (fx.getD m 0) + u • uVec (fx.getD (k + 1) 0))
    (hspan : ∀ y : Fin 6 → F4, y ∈ Submodule.span F4 {v | ∃ x ∈ fx, v = uVec x}) : ρ = 1 := by
  have hρ' : ρ ∈ piSU.range := by rw [range_piSU]; exact hρ
  obtain ⟨g, rfl⟩ := hρ'
  set M := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hmem : ∀ k < fx.length, fx.getD k 0 ∈ fx := fun k hk => by
    rw [List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem hk
  have heig : ∀ k < fx.length, ∃ c : F4, c ≠ 0 ∧
      M *ᵥ uVec (fx.getD k 0) = c • uVec (fx.getD k 0) := fun k hk =>
    exists_smul_of_piSU_fix g (hlt _ (hmem k hk)) (hfix _ (hmem k hk))
  have h0 : 0 < fx.length := List.length_pos_iff.2 hne
  obtain ⟨c₀, hc₀, e₀⟩ := heig 0 h0
  have hall : ∀ k < fx.length, M *ᵥ uVec (fx.getD k 0) = c₀ • uVec (fx.getD k 0) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      cases k with
      | zero => exact e₀
      | succ k =>
        obtain ⟨m, hm, n, hn, l, u, hl, hu, e⟩ := hline k hk
        obtain ⟨cn, -, en⟩ := heig n hn
        obtain ⟨ck, -, ek⟩ := heig (k + 1) hk
        have em := ih m (by omega) (by omega)
        have h1 : M *ᵥ uVec (fx.getD n 0) =
            l • (c₀ • uVec (fx.getD m 0)) + u • (ck • uVec (fx.getD (k + 1) 0)) := by
          rw [e, mulVec_add, mulVec_smul, mulVec_smul, em, ek]
        rw [en, e] at h1
        have h2 : ((cn - c₀) * l) • uVec (fx.getD m 0) +
            ((cn - ck) * u) • uVec (fx.getD (k + 1) 0) = 0 := by
          have h3 : cn • (l • uVec (fx.getD m 0) + u • uVec (fx.getD (k + 1) 0)) -
              (l • (c₀ • uVec (fx.getD m 0)) + u • (ck • uVec (fx.getD (k + 1) 0))) = 0 := by
            rw [h1, sub_self]
          rw [← h3]
          module
        have hd : fx.getD m 0 ≠ fx.getD (k + 1) 0 := by
          rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
          intro he
          have := (List.Nodup.getElem_inj_iff hnd).1 he
          omega
        obtain ⟨h3, h4⟩ := smul_add_smul_eq_zero (hlt _ (hmem m (by omega))) (hlt _ (hmem _ hk))
          hd h2
        have e3 : cn = c₀ := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hl)
        have e4 : cn = ck := sub_eq_zero.1 ((mul_eq_zero.1 h4).resolve_right hu)
        rw [ek, ← e4, e3]
  have hlin : ∀ y ∈ Submodule.span F4 {v | ∃ x ∈ fx, v = uVec x}, M *ᵥ y = c₀ • y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
      rw [← List.getD_eq_getElem _ 0 hk]
      exact hall k hk
    | zero => rw [mulVec_zero, smul_zero]
    | add a b _ _ ha hb => rw [mulVec_add, ha, hb, smul_add]
    | smul a z _ hz => rw [mulVec_smul, hz, smul_comm]
  refine Equiv.ext fun i => Fin.ext ?_
  rw [piSU_apply, hlin _ (hspan _), ptIdx_smul hc₀, ptIdx_uVec ptsFacts i.2]
  rfl

end Frame

theorem decode_two_pow_smk (t : Fin 20) : decode (2 ^ t.val) = fun j => if t = j then 1 else 0 := by
  funext j
  rw [decode_apply, Nat.testBit_two_pow]
  by_cases h : t = j
  · simp [h]
  · simp [h, Fin.val_ne_of_ne h]

theorem span_eq_top_of_units_smk {ws : List ℕ} (h : ∀ t < 20, ∃ m, xorSel ws m = 2 ^ t) :
    Submodule.span (ZMod 2) {u | ∃ w ∈ ws, u = decode w} = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
  obtain ⟨m, hm⟩ := h t.val t.2
  rw [← decode_two_pow_smk, ← hm]
  refine decode_xorSel_mem ws (fun w hw => ?_) m
  have hw' : decode w ∈ {u : CFSG.LargeExtraspecial.SMod20.V | ∃ w' ∈ ws, u = decode w'} := ⟨w, hw, rfl⟩
  exact Submodule.subset_span hw'

variable
  {A : SMod20.V ≃ₗ[ZMod 2] SMod20.V} {π : Equiv.Perm (Fin 693)}

theorem fp_of_frame (h : InvHyp A π) {bs : List ℕ} (hbs : bs.length ≤ 8) {pl : List (ℕ × ℕ)}
    (hpl : ∀ q ∈ pl, q.1 < 891 ∧ q.2 < 891 ∧ ⇑π '' wPlane q.1 = wPlane q.2 ∧
      ∃ m, xorSel bs m = wtArr[q.2]! ^^^ wtArr[q.1]!)
    (hum : ∀ t < 20, ∃ m, xorSel (pl.map fun q => wtArr[q.1]!) m = 2 ^ t)
    {fx : List ℕ} (hfx : ∀ q, q ∈ fx ↔ ∃ hq : q < 693, π ⟨q, hq⟩ = ⟨q, hq⟩) (hnd : fx.Nodup)
    (hodd : fx.length % 2 = 1)
    (horb : ∀ Q : ℕ → Prop, Q (fx.getD 0 0) → (∀ g ∈ fx, ∀ u ∈ fx, ∀ (hg : g < 693)
      (hu : u < 693), Q u → Q (tvP ⟨g, hg⟩ ⟨u, hu⟩).val) → ∀ v ∈ fx, Q v)
    (hfr : ∀ ρ ∈ T46, (∀ x (hx : x < 693), x ∈ fx → ρ ⟨x, hx⟩ = ⟨x, hx⟩) → ρ = 1) :
    finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π := by
  have hπ : IsPolarAut π := isPolarAut_of_mem_normalizer h.norm
  have hlt : ∀ q ∈ fx, q < 693 := fun q hq => ((hfx q).1 hq).1
  set S := Submodule.span (ZMod 2) {u | ∃ v ∈ bs, u = decode v}
  have hsub : ∀ v, A v - v ∈ S := by
    intro v
    have hv : v ∈ Submodule.span (ZMod 2)
        {u | ∃ w ∈ pl.map (fun q => wtArr[q.1]!), u = decode w} := by
      rw [span_eq_top_of_units_smk hum]
      trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
      obtain ⟨hi, hi', himg, m, hm⟩ := hpl q hq
      have e : A (decode wtArr[q.1]!) - decode wtArr[q.1]! = decode (wtArr[q.2]! ^^^ wtArr[q.1]!) := by
        rw [decode_xor, sub_eq_add_V, wtArr_get hi, wtArr_get hi']
        change A (wtV q.1) + wtV q.1 = wtV q.2 + wtV q.1
        rw [h.wtV_eq hi hi' himg]
      rw [e, ← hm]
      refine decode_xorSel_mem bs (fun v hv => ?_) m
      have hv' : decode v ∈ {u : CFSG.LargeExtraspecial.SMod20.V | ∃ w' ∈ bs, u = decode w'} := ⟨v, hv, rfl⟩
      exact Submodule.subset_span hv'
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add, show A x + A y - (x + y) = (A x - x) + (A y - y) by abel]
      exact S.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, ← smul_sub]
      exact S.smul_mem a hx
  have hYle : commSpace A ≤ S := by
    rintro _ ⟨v, rfl⟩
    exact hsub v
  refine ⟨(Submodule.finrank_mono hYle).trans ((finrank_span_decode_le bs).trans hbs), ?_⟩
  intro R hRT hRp hRc hRn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction R {x : Fin 693 // π x = x} :=
    { smul := fun r x => ⟨(r : Equiv.Perm (Fin 693)) x.1, by
        have e := hRc r.1 r.2
        calc π ((r : Equiv.Perm (Fin 693)) x.1) = (π * (r : Equiv.Perm (Fin 693))) x.1 := rfl
          _ = ((r : Equiv.Perm (Fin 693)) * π) x.1 := by rw [e]
          _ = (r : Equiv.Perm (Fin 693)) x.1 := by
            change (r : Equiv.Perm (Fin 693)) (π x.1) = _
            rw [x.2]⟩
      one_smul := fun x => Subtype.ext rfl
      mul_smul := fun r s x => Subtype.ext rfl }
  have hcard : Nat.card {x : Fin 693 // π x = x} = fx.length := by
    have e : {x : Fin 693 | π x = x} = {p : Fin 693 | p.val ∈ fx} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [hfx]
      exact ⟨fun hx => ⟨x.2, hx⟩, fun ⟨_, hx⟩ => hx⟩
    change Nat.card ↥{x : Fin 693 | π x = x} = _
    rw [Nat.card_coe_set_eq, e, ncard_setOf_mem_list hnd hlt]
  have hX : ¬ 2 ∣ Nat.card {x : Fin 693 // π x = x} := by
    rw [hcard]
    omega
  obtain ⟨x₀, hx₀⟩ := hRp.nonempty_fixed_point_of_prime_not_dvd_card
    {x : Fin 693 // π x = x} hX
  let P : Fin 693 → Prop := fun v => ∀ r ∈ R, r v = v
  have hP : ∀ p ∈ fx, ∀ (hp : p < 693) (u : Fin 693), P u → P (tvP ⟨p, hp⟩ u) := by
    intro p hpf hp u hu r hr
    have hpfix : π ⟨p, hp⟩ = ⟨p, hp⟩ := by
      obtain ⟨_, h1⟩ := (hfx p).1 hpf
      exact h1
    have hr' := hRn _ hpfix r hr
    rw [tvP_inv] at hr'
    have h1 := hu _ hr'
    simp only [Equiv.Perm.mul_apply] at h1
    have h2 := congrArg (tvP ⟨p, hp⟩) h1
    rw [← Equiv.Perm.mul_apply, tvP_mul_self] at h2
    simpa using h2
  have hne : fx ≠ [] := by
    intro he
    rw [he] at hodd
    simp at hodd
  have hq₀ : fx.getD 0 0 ∈ fx := by
    rw [List.getD_eq_getElem _ _ (List.length_pos_iff.2 hne)]
    exact List.getElem_mem _
  have hq₀' := hlt _ hq₀
  have hiff := horb (fun n => ∀ hn : n < 693, (P ⟨fx.getD 0 0, hq₀'⟩ ↔ P ⟨n, hn⟩))
    (fun _ => Iff.rfl)
    (fun q hq u hu hq' hu' hQ hn => by
      have hback : tvP ⟨q, hq'⟩ ⟨(tvP ⟨q, hq'⟩ ⟨u, hu'⟩).val, hn⟩ = ⟨u, hu'⟩ := by
        rw [Fin.eta, ← Equiv.Perm.mul_apply, tvP_mul_self]
        rfl
      rw [hQ hu']
      constructor
      · intro h1
        rw [Fin.eta]
        exact hP _ hq hq' _ h1
      · intro h1
        rw [← hback]
        exact hP _ hq hq' _ h1)
  have hP0 : P ⟨fx.getD 0 0, hq₀'⟩ := by
    have h1 := hiff x₀.1.val ((hfx _).2 ⟨x₀.1.2, x₀.2⟩) x₀.1.2
    exact h1.2 (fun r hr => congrArg Subtype.val (hx₀ ⟨r, hr⟩))
  rw [eq_bot_iff]
  intro r hr
  rw [mem_bot]
  refine hfr r (hRT hr) fun x hx hxf => ?_
  exact ((hiff x hxf hx).1 hP0) r hr

end CFSG.LargeExtraspecial.S14.SMK

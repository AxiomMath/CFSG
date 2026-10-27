module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3YFacts
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp2
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DHyp4
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3DNorm

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaD
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] {L : Subgroup G}
  {e : L ≃* T46} {t : G}

theorem toG_span_le {c N : ChainData} (hc : c.GensOK) {pre : List (List ℕ)} {r : List ℕ}
    {vs : List (List ℕ)} (hgens : ∀ w ∈ c.gens, w ∈ pre ∨ w ∈ vs.map fun v => cjW v r)
    (hvs : ∀ v ∈ vs, ∀ k ∈ v, k < 18 ∧ [k] ∈ N.gens) {B : Subgroup G}
    (hpre : ∀ w ∈ pre, gw e w ∈ B) (hN : toG e N.grp ≤ normalizer (B : Set G))
    (hrB : gw e r ∈ B) : toG e c.grp ≤ B := by
  refine toG_le_of_gens hc fun w hw => ?_
  rcases hgens w hw with h | h
  · exact hpre w h
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
    rw [gw_cjW fun k hk => (hvs v hv k hk).1]
    exact (mem_normalizer_iff.1 (hN (gw_mem_ch (hvs v hv))) _).1 hrB

theorem gw_mem_of_cjW {N : ChainData} {q r : List ℕ} (hq : ∀ k ∈ q, k < 18 ∧ [k] ∈ N.gens)
    {B : Subgroup G} (hN : toG e N.grp ≤ normalizer (B : Set G)) (h : gw e (cjW q r) ∈ B) :
    gw e r ∈ B := by
  rw [gw_cjW fun k hk => (hq k hk).1] at h
  have hn := hN (gw_mem_ch hq)
  have := (mem_normalizer_iff.1 (inv_mem hn) _).1 h
  simpa [mul_assoc] using this

theorem a2Tab_K2 : ∀ p ∈ a2Tab, p.2 < 3 ∧ ∀ k ∈ p.1, k < 18 ∧ [k] ∈ chK2.gens := by
  decide +kernel

theorem finite_of_le_L (e : L ≃* T46) {A : Subgroup G} (h : A ≤ L) : Finite A := by
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  exact Finite.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

theorem eq_of_card_toG_le {c : ChainData} (hc : c.GensOK) {A B : Subgroup G} (hAL : A ≤ L)
    (hBA : B ≤ A) (hcard : Nat.card A ≤ Nat.card c.grp) (hle : toG e c.grp ≤ B) : B = A := by
  have := finite_of_le_L e hAL
  have : Finite B := finite_of_le_L e (hBA.trans hAL)
  exact Subgroup.eq_of_le_of_card_ge hBA (hcard.trans ((card_toG_ch hc).symm.le.trans
    (Subgroup.card_le_of_le hle)))

theorem d_A₂_irred : ∀ B : Subgroup G, B ≤ (sec3DData e t).A₂ →
    (sec3DData e t).K₂ ≤ normalizer (B : Set G) → B = ⊥ ∨ B = (sec3DData e t).A₂ := by
  intro B hBA hN
  by_cases hB : B = ⊥
  · exact Or.inl hB
  right
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 (hBA hb)
  have hg1 : (g : Equiv.Perm (Fin 693)) ≠ 1 := fun h =>
    hb1' (by rw [show g = 1 from Subtype.ext h, map_one])
  obtain ⟨p, hp, hpg⟩ := a2Orb_spec _ hg hg1
  obtain ⟨hp2, hq⟩ := a2Tab_K2 p hp
  have hbB : gw e (cjW p.1 a2Reps[p.2]!) ∈ B := by
    rw [gw_eq _ (a2Tab_lt p hp), show tw (cjW p.1 a2Reps[p.2]!) (a2Tab_lt p hp) = g from
      Subtype.ext hpg]
    exact hb
  have hK : toG e chK2.grp ≤ normalizer (B : Set G) := hN
  have hrB := gw_mem_of_cjW hq hK hbB
  have hA : Nat.card (sec3DData e t).A₂ = 512 := by rw [d_card_A₂]; norm_num
  have h3 : p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2 := by omega
  rcases h3 with h | h | h <;> rw [h] at hrB
  · exact eq_of_card_toG_le gensOK_chA2s0 (toG_le_L _) hBA (by rw [hA, card_chA2s0])
      (toG_span_le (pre := []) (vs := a2Vs0) gensOK_chA2s0 (by decide) (by decide) (by simp) hK
        hrB)
  · exact eq_of_card_toG_le gensOK_chA2s1 (toG_le_L _) hBA (by rw [hA, card_chA2s1])
      (toG_span_le (pre := []) (vs := a2Vs1) gensOK_chA2s1 (by decide) (by decide) (by simp) hK
        hrB)
  · exact eq_of_card_toG_le gensOK_chA2s2 (toG_le_L _) hBA (by rw [hA, card_chA2s2])
      (toG_span_le (pre := []) (vs := a2Vs2) gensOK_chA2s2 (by decide) (by decide) (by simp) hK
        hrB)

theorem a1Tab_K1 : ∀ p ∈ a1Tab, p.2 < 2 ∧ ∀ k ∈ p.1, k < 18 ∧ [k] ∈ chK1.gens := by
  decide +kernel

theorem d_A₁_orb {a : G} (ha : a ∈ (sec3DData e t).A₁) (haz : a ∉ zpowers (sec3DData e t).z) :
    ∃ p ∈ a1Tab, gw e (cjW p.1 a1Reps[p.2]!) = a ∨
      gw e (cjW p.1 a1Reps[p.2]!) * (sec3DData e t).z = a := by
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
  have hgz : (g : Equiv.Perm (Fin 693)) ∉ chZ.grp := fun h => haz (by
    rw [show zpowers (sec3DData e t).z = toG e chZ.grp from toG_chZ.symm]
    exact iotaG_mem_toG.2 h)
  obtain ⟨p, hp, hpg⟩ := a1Orb_spec _ hg hgz
  refine ⟨p, hp, ?_⟩
  rcases hpg with h | h
  · left
    rw [gw_eq _ (a1Tab_lt p hp)]
    exact congrArg (iotaG e) (Subtype.ext h)
  · right
    show gw e (cjW p.1 a1Reps[p.2]!) * gw e [14] = _
    rw [← gw_append, gw_eq _ (fun k hk => (List.mem_append.1 hk).elim (a1Tab_lt p hp k)
      (fun h' => by simp at h'; omega))]
    refine congrArg (iotaG e) (Subtype.ext ?_)
    show wP (cjW p.1 a1Reps[p.2]! ++ [14]) = g
    rw [wP_append, wP_single]
    exact h

theorem d_A₁_irred : ∀ B : Subgroup G, zpowers (sec3DData e t).z ≤ B →
    B ≤ (sec3DData e t).A₁ → (sec3DData e t).K₁ ≤ normalizer (B : Set G) →
      B = zpowers (sec3DData e t).z ∨ B = (sec3DData e t).A₁ := by
  intro B hzB hBA hN
  by_cases hB : B ≤ zpowers (sec3DData e t).z
  · exact Or.inl (le_antisymm hB hzB)
  right
  obtain ⟨b, hb, hbz⟩ := Set.not_subset.1 hB
  obtain ⟨p, hp, hpb⟩ := d_A₁_orb (hBA hb) hbz
  obtain ⟨hp2, hq⟩ := a1Tab_K1 p hp
  have hz : (sec3DData e t).z ∈ B := hzB (mem_zpowers _)
  have hbB : gw e (cjW p.1 a1Reps[p.2]!) ∈ B := by
    rcases hpb with h | h
    · rw [h]; exact hb
    · have : gw e (cjW p.1 a1Reps[p.2]!) = b * (sec3DData e t).z⁻¹ := by rw [← h]; group
      rw [this]
      exact mul_mem hb (inv_mem hz)
  have hK : toG e chK1.grp ≤ normalizer (B : Set G) := hN
  have hrB := gw_mem_of_cjW hq hK hbB
  have hA : Nat.card (sec3DData e t).A₁ = 512 := by rw [d_card_A₁]; norm_num
  have hpre : ∀ w ∈ [[14]], gw e w ∈ B := fun w hw => by
    rw [List.mem_singleton.1 hw]; exact hz
  have h2 : p.2 = 0 ∨ p.2 = 1 := by omega
  rcases h2 with h | h <;> rw [h] at hrB
  · exact eq_of_card_toG_le gensOK_chA1s0 (toG_le_L _) hBA (by rw [hA, card_chA1s0])
      (toG_span_le (pre := [[14]]) (vs := a1Vs0) gensOK_chA1s0 (by decide) (by decide) hpre hK
        hrB)
  · exact eq_of_card_toG_le gensOK_chA1s1 (toG_le_L _) hBA (by rw [hA, card_chA1s1])
      (toG_span_le (pre := [[14]]) (vs := a1Vs1) gensOK_chA1s1 (by decide) (by decide) hpre hK
        hrB)

theorem d_z_comm_A₁ {a : G} (ha : a ∈ (sec3DData e t).A₁) :
    a * (sec3DData e t).z = (sec3DData e t).z * a := by
  have h := toG_le_centralizer (e := e) xComm_spec.2.2.2.2.2.2.2 ha
  rw [toG_chZ] at h
  exact (mem_centralizer_iff.1 h _ (mem_zpowers _)).symm

theorem d_z_sq : (sec3DData e t).z * (sec3DData e t).z = 1 := by
  show gw e [14] * gw e [14] = 1
  rw [← gw_append, gw_eq_xId (b := []) (by decide) (by decide) (by decide), gw_nil]

theorem d_rep_sq {p : List ℕ × ℕ} (hp : p ∈ a1Tab) :
    (p.2 = 0 → gw e (cjW p.1 a1Reps[p.2]!) * gw e (cjW p.1 a1Reps[p.2]!) = 1) ∧
    (p.2 = 1 → gw e (cjW p.1 a1Reps[p.2]!) * gw e (cjW p.1 a1Reps[p.2]!) =
      (sec3DData e t).z) := by
  obtain ⟨hp2, hq⟩ := a1Tab_K1 p hp
  have hqK : gw e p.1 ∈ (sec3DData e t).K₁ := gw_mem_ch hq
  have hqlt : ∀ k ∈ p.1, k < 18 := fun k hk => (hq k hk).1
  rw [gw_cjW hqlt]
  have e1 : gw e p.1 * gw e a1Reps[p.2]! * (gw e p.1)⁻¹ *
      (gw e p.1 * gw e a1Reps[p.2]! * (gw e p.1)⁻¹) =
      gw e p.1 * (gw e a1Reps[p.2]! * gw e a1Reps[p.2]!) * (gw e p.1)⁻¹ := by group
  rw [e1, ← gw_append]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, gw_eq_gw (b := []) (by decide) (by decide) a1Reps_sq.1, gw_nil]
    group
  · rw [h, gw_eq_gw (b := [14]) (by decide) (by decide) (a1Reps_sq.2.trans (wP_single 14).symm)]
    have hc := mem_centralizer_singleton_iff.1 (d_K₁_cent_z (e := e) (t := t) hqK)
    show gw e p.1 * (sec3DData e t).z * (gw e p.1)⁻¹ = (sec3DData e t).z
    rw [hc, mul_inv_cancel_right]

theorem d_K₁_trans_aux {a : G} (ha : a ∈ (sec3DData e t).A₁) (hsq : a * a = 1)
    (haz : a ∉ zpowers (sec3DData e t).z) : ∃ q : List ℕ, (∀ k ∈ q, k < 18 ∧ [k] ∈ chK1.gens) ∧
      (gw e (cjW q a1Reps[0]!))⁻¹ * a ∈ zpowers (sec3DData e t).z := by
  obtain ⟨p, hp, hpa⟩ := d_A₁_orb ha haz
  obtain ⟨hp2, hq⟩ := a1Tab_K1 p hp
  have hT := d_rep_sq (e := e) (t := t) hp
  have hTA : gw e (cjW p.1 a1Reps[p.2]!) ∈ (sec3DData e t).A₁ := by
    rcases hpa with h | h
    · rw [h]; exact ha
    · have : gw e (cjW p.1 a1Reps[p.2]!) = a * (sec3DData e t).z⁻¹ := by rw [← h]; group
      rw [this]
      exact mul_mem ha (inv_mem d_z_mem_A₁)
  have h0 : p.2 = 0 := by
    by_contra hne
    have hT := hT.2 (by omega)
    apply d_z_ne_one (e := e) (t := t)
    rcases hpa with h | h
    · rw [← hT, h, hsq]
    · have hzc := d_z_comm_A₁ (e := e) (t := t) hTA
      set T := gw e (cjW p.1 a1Reps[p.2]!)
      have h2 : a * a = (sec3DData e t).z := by
        rw [← h]
        calc T * (sec3DData e t).z * (T * (sec3DData e t).z) =
            T * (T * (sec3DData e t).z) * (sec3DData e t).z := by
              rw [mul_assoc T (sec3DData e t).z, ← mul_assoc (sec3DData e t).z T, ← hzc]; group
          _ = T * T * ((sec3DData e t).z * (sec3DData e t).z) := by group
          _ = (sec3DData e t).z := by rw [hT, d_z_sq, mul_one]
      rw [hsq] at h2
      exact h2.symm
  refine ⟨p.1, hq, ?_⟩
  rw [← h0]
  rcases hpa with h | h
  · rw [h, inv_mul_cancel]; exact one_mem _
  · rw [← h, inv_mul_cancel_left]; exact mem_zpowers _

theorem d_K₁_trans : ∀ a ∈ (sec3DData e t).A₁, a * a = 1 → a ∉ zpowers (sec3DData e t).z →
    ∀ b ∈ (sec3DData e t).A₁, b * b = 1 → b ∉ zpowers (sec3DData e t).z →
      ∃ k ∈ (sec3DData e t).K₁, (k * a * k⁻¹)⁻¹ * b ∈ zpowers (sec3DData e t).z := by
  intro a ha ha2 haz b hb hb2 hbz
  obtain ⟨qa, hqa, ha'⟩ := d_K₁_trans_aux ha ha2 haz
  obtain ⟨qb, hqb, hb'⟩ := d_K₁_trans_aux hb hb2 hbz
  have hqaK : gw e qa ∈ (sec3DData e t).K₁ := gw_mem_ch hqa
  have hqbK : gw e qb ∈ (sec3DData e t).K₁ := gw_mem_ch hqb
  set k := gw e qb * (gw e qa)⁻¹ with hk
  refine ⟨k, mul_mem hqbK (inv_mem hqaK), ?_⟩
  obtain ⟨m, hm⟩ := ha'
  obtain ⟨n, hn⟩ := hb'
  rw [gw_cjW (fun k hk => (hqa k hk).1)] at hm
  rw [gw_cjW (fun k hk => (hqb k hk).1)] at hn
  have hkz : k * (sec3DData e t).z ^ m = (sec3DData e t).z ^ m * k :=
    (Commute.zpow_right (mem_centralizer_singleton_iff.1 (d_K₁_cent_z (e := e) (t := t)
      (mul_mem hqbK (inv_mem hqaK)))) m).eq
  have hm' : (sec3DData e t).z ^ m = (gw e qa * gw e a1Reps[0]! * (gw e qa)⁻¹)⁻¹ * a := hm
  have hn' : (sec3DData e t).z ^ n = (gw e qb * gw e a1Reps[0]! * (gw e qb)⁻¹)⁻¹ * b := hn
  have eA : a = gw e qa * gw e a1Reps[0]! * (gw e qa)⁻¹ * (sec3DData e t).z ^ m := by
    rw [hm']; group
  have eB : b = gw e qb * gw e a1Reps[0]! * (gw e qb)⁻¹ * (sec3DData e t).z ^ n := by
    rw [hn']; group
  refine ⟨n - m, ?_⟩
  show (sec3DData e t).z ^ (n - m) = _
  rw [eA, eB, zpow_sub]
  have e2 : k * (gw e qa * gw e a1Reps[0]! * (gw e qa)⁻¹ * (sec3DData e t).z ^ m) * k⁻¹ =
      gw e qb * gw e a1Reps[0]! * (gw e qb)⁻¹ * (sec3DData e t).z ^ m := by
    rw [show k * (gw e qa * gw e a1Reps[0]! * (gw e qa)⁻¹ * (sec3DData e t).z ^ m) * k⁻¹ =
      (k * (gw e qa * gw e a1Reps[0]! * (gw e qa)⁻¹) * k⁻¹) * (k * (sec3DData e t).z ^ m * k⁻¹)
        by group, hkz, mul_inv_cancel_right, hk]
    group
  rw [e2]
  group

theorem a3Tab_N : ∀ p ∈ a3Tab, p.2 < 5 ∧ ∀ k ∈ p.1, k < 18 ∧ [k] ∈ chP2.gens := by
  decide +kernel

theorem d_P2_le_NLA₃ : toG e chP2.grp ≤ (sec3DData e t).NLA₃ :=
  le_inf (toG_le_L _) (toG_le_normalizer (grp_le_T46 gensOK_chP2) (grp_le_T46 gensOK_chA3)
    chP2_le_normalizer)

theorem d_A₃_irred : ∀ B : Subgroup G, (sec3DData e t).A₄ ≤ B → B ≤ (sec3DData e t).A₃ →
    (sec3DData e t).NLA₃ ≤ normalizer (B : Set G) →
      B = (sec3DData e t).A₄ ∨ B = (sec3DData e t).A₃ := by
  intro B hAB hBA hN
  by_cases hB : B ≤ (sec3DData e t).A₄
  · exact Or.inl (le_antisymm hB hAB)
  right
  obtain ⟨b, hb, hb4⟩ := Set.not_subset.1 hB
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 (hBA hb)
  have hg4 : (g : Equiv.Perm (Fin 693)) ∉ chA4.grp := fun h => hb4 (iotaG_mem_toG.2 h)
  obtain ⟨p, hp, hpg⟩ := a3Orb_spec _ hg hg4
  obtain ⟨hp5, hq⟩ := a3Tab_N p hp
  have hT : gw e (cjW p.1 a3Reps[p.2]!) ∈ B := by
    have h1 : (gw e (cjW p.1 a3Reps[p.2]!))⁻¹ * iotaG e g ∈ (sec3DData e t).A₄ := by
      rw [gw_eq _ (a3Tab_lt p hp), ← map_inv, ← map_mul]
      exact iotaG_mem_toG.2 hpg
    have e1 : gw e (cjW p.1 a3Reps[p.2]!) =
        iotaG e g * ((gw e (cjW p.1 a3Reps[p.2]!))⁻¹ * iotaG e g)⁻¹ := by group
    rw [e1]
    exact mul_mem hb (inv_mem (hAB h1))
  have hK : toG e chP2.grp ≤ normalizer (B : Set G) := d_P2_le_NLA₃.trans hN
  have hrB := gw_mem_of_cjW hq hK hT
  have hA : Nat.card (sec3DData e t).A₃ = 4096 := by rw [d_card_A₃]; norm_num
  have hpre : ∀ w ∈ [[11], [12], [13], [14]], gw e w ∈ B := fun w hw => by
    have h4 : ∀ w ∈ [[11], [12], [13], [14]], ∀ k ∈ w, k < 18 ∧ [k] ∈ chA4.gens := by decide
    exact hAB (gw_mem_ch (h4 w hw))
  have h5 : p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2 ∨ p.2 = 3 ∨ p.2 = 4 := by omega
  rcases h5 with h | h | h | h | h <;> rw [h] at hrB
  · exact eq_of_card_toG_le gensOK_chA3s0 (toG_le_L _) hBA (by rw [hA, card_chA3s0])
      (toG_span_le (vs := a3Vs0) gensOK_chA3s0 (by decide) (by decide) hpre hK hrB)
  · exact eq_of_card_toG_le gensOK_chA3s1 (toG_le_L _) hBA (by rw [hA, card_chA3s1])
      (toG_span_le (vs := a3Vs1) gensOK_chA3s1 (by decide) (by decide) hpre hK hrB)
  · exact eq_of_card_toG_le gensOK_chA3s2 (toG_le_L _) hBA (by rw [hA, card_chA3s2])
      (toG_span_le (vs := a3Vs2) gensOK_chA3s2 (by decide) (by decide) hpre hK hrB)
  · exact eq_of_card_toG_le gensOK_chA3s3 (toG_le_L _) hBA (by rw [hA, card_chA3s3])
      (toG_span_le (vs := a3Vs3) gensOK_chA3s3 (by decide) (by decide) hpre hK hrB)
  · exact eq_of_card_toG_le gensOK_chA3s4 (toG_le_L _) hBA (by rw [hA, card_chA3s4])
      (toG_span_le (vs := a3Vs4) gensOK_chA3s4 (by decide) (by decide) hpre hK hrB)

theorem chK2_conj_zCls : ∀ x ∈ chK2.grp, ∀ c ∈ zCls, ∃ c' ∈ zCls, x * wP c * x⁻¹ = wP c' := by
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact fun c hc => ⟨c, hc, by group⟩
  | mul_left a ha y _ ih =>
    intro c hc
    obtain ⟨w, hw, rfl⟩ := ha
    obtain ⟨c', hc', h⟩ := ih c hc
    obtain ⟨c'', hc'', h'⟩ := zCls_spec.1 w hw c' hc'
    exact ⟨c'', hc'', by rw [← h', ← h]; group⟩
  | inv_mul_cancel a ha y _ ih =>
    intro c hc
    obtain ⟨w, hw, rfl⟩ := ha
    have hlen : ∀ w ∈ chK2.gens, w.length = 1 := by decide
    obtain ⟨k, rfl⟩ := List.length_eq_one_iff.1 (hlen w hw)
    have hk : k < 18 := by simpa using gensOK_chK2 _ hw
    obtain ⟨c', hc', h⟩ := ih c hc
    obtain ⟨c'', hc'', h'⟩ := zCls_spec.1 [k] hw c' hc'
    refine ⟨c'', hc'', ?_⟩
    have hinv : (wP [k])⁻¹ = wP [k] := by rw [wP_single, gP_inv hk]
    rw [hinv, ← h', ← h]
    group

theorem zCls_zero : zCls[0]! = [14] := rfl

theorem d_conj_z_mem {k : G} (hk : k ∈ (sec3DData e t).K₂) :
    ∃ j < 21, k * (sec3DData e t).z * k⁻¹ = gw e zCls[j]! := by
  obtain ⟨g, hg, rfl⟩ := mem_toG.1 hk
  obtain ⟨c, hc, h⟩ := chK2_conj_zCls _ hg [14] (by decide)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hc
  refine ⟨j, hj, ?_⟩
  rw [getElem!_pos zCls j hj, gw_eq _ (zCls_lt _ (List.getElem_mem hj)),
    show (sec3DData e t).z = iotaG e (tw [14] (by decide)) from gw_eq [14] (by decide),
    ← map_inv, ← map_mul, ← map_mul]
  exact congrArg (iotaG e) (Subtype.ext (by simpa [tw, wP_single] using h))

theorem d_zMs {j : ℕ} (hj : j < 20) :
    gw e zMs[j]! ∈ (sec3DData e t).K₂ ∧
      gw e zMs[j]! * (sec3DData e t).z = (sec3DData e t).z * gw e zMs[j]! ∧
      gw e zMs[j]! * gw e zCls[1]! * (gw e zMs[j]!)⁻¹ = gw e zCls[j + 1]! := by
  have hl := zMs_lt j hj
  obtain ⟨h1, h2⟩ := zCls_spec.2 j hj
  refine ⟨gw_mem_ch hl, ?_, ?_⟩
  · show gw e zMs[j]! * gw e [14] = gw e [14] * gw e zMs[j]!
    rw [← gw_append, ← gw_append]
    refine gw_eq_gw ?_ ?_ (by rw [wP_append, wP_append, wP_single]; exact h1)
    · intro k hk
      rcases List.mem_append.1 hk with h | h
      · exact (hl k h).1
      · simp at h; omega
    · intro k hk
      rcases List.mem_append.1 hk with h | h
      · simp at h; omega
      · exact (hl k h).1
  · rw [← gw_cjW fun k hk => (hl k hk).1]
    refine gw_eq_gw ?_ (zCls_lt _ (by interval_cases j <;> decide)) h2
    intro k hk
    simp only [cjW, List.mem_append, List.mem_reverse] at hk
    rcases hk with (h | h) | h
    · exact (hl k h).1
    · exact zCls_lt _ (by decide) k h
    · exact (hl k h).1

theorem d_K₂_trans : ∀ k ∈ (sec3DData e t).K₂, ∀ k' ∈ (sec3DData e t).K₂,
    k * (sec3DData e t).z * k⁻¹ ≠ (sec3DData e t).z →
    k' * (sec3DData e t).z * k'⁻¹ ≠ (sec3DData e t).z →
      ∃ m ∈ (sec3DData e t).K₂, m * (sec3DData e t).z = (sec3DData e t).z * m ∧
        m * (k * (sec3DData e t).z * k⁻¹) * m⁻¹ = k' * (sec3DData e t).z * k'⁻¹ := by
  intro k hk k' hk' hne hne'
  obtain ⟨j, hj, hkj⟩ := d_conj_z_mem hk
  obtain ⟨j', hj', hkj'⟩ := d_conj_z_mem hk'
  have hj0 : j ≠ 0 := fun h => hne (by rw [hkj, h, zCls_zero]; rfl)
  have hj0' : j' ≠ 0 := fun h => hne' (by rw [hkj', h, zCls_zero]; rfl)
  obtain ⟨hmK, hmz, hmc⟩ := d_zMs (e := e) (t := t) (show j - 1 < 20 by omega)
  obtain ⟨hmK', hmz', hmc'⟩ := d_zMs (e := e) (t := t) (show j' - 1 < 20 by omega)
  rw [show j - 1 + 1 = j by omega] at hmc
  rw [show j' - 1 + 1 = j' by omega] at hmc'
  refine ⟨gw e zMs[j' - 1]! * (gw e zMs[j - 1]!)⁻¹, mul_mem hmK' (inv_mem hmK), ?_, ?_⟩
  · have hc : Commute (gw e zMs[j - 1]!) (sec3DData e t).z := hmz
    have hmz_inv : (gw e zMs[j - 1]!)⁻¹ * (sec3DData e t).z =
        (sec3DData e t).z * (gw e zMs[j - 1]!)⁻¹ := hc.inv_left.eq
    rw [mul_assoc, hmz_inv, ← mul_assoc, hmz', mul_assoc]
  · rw [hkj, hkj', ← hmc, ← hmc']
    group

theorem gw_injective {a b : List ℕ} (ha : ∀ k ∈ a, k < 18) (hb : ∀ k ∈ b, k < 18)
    (h : gw e a = gw e b) : wP a = wP b := by
  rw [gw_eq a ha, gw_eq b hb] at h
  exact congrArg Subtype.val (iotaG_injective h)

theorem d_card_sing : {S : Set G | ∃ a ∈ (sec3DData e t).A₁, a * a = 1 ∧
    S = a • (zpowers (sec3DData e t).z : Set G)}.ncard = 136 := by
  set Z := zpowers (sec3DData e t).z with hZ
  set f : Fin singReps.length → Set G := fun i => gw e singReps[i] • (Z : Set G) with hf
  have hlt : ∀ i : Fin singReps.length, ∀ k ∈ singReps[i], k < 18 :=
    fun i => singReps_lt _ (List.getElem_mem i.2)
  have hz2 : (sec3DData e t).z ^ 2 = 1 := by rw [pow_two]; exact d_z_sq
  have hzgw : (sec3DData e t).z = gw e [14] := rfl
  have hset : {S : Set G | ∃ a ∈ (sec3DData e t).A₁, a * a = 1 ∧ S = a • (Z : Set G)} =
      Set.range f := by
    ext S
    constructor
    · rintro ⟨a, ha, ha2, rfl⟩
      obtain ⟨g, hg, rfl⟩ := mem_toG.1 ha
      have hg2 : (g : Equiv.Perm (Fin 693)) * g = 1 := by
        have h1 : iotaG e (g * g) = iotaG e 1 := by rw [map_mul, ha2, map_one]
        exact congrArg Subtype.val (iotaG_injective h1)
      obtain ⟨s, hs, hsg⟩ := sing_spec.2.2 _ hg hg2
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hs
      refine ⟨⟨i, hi⟩, ?_⟩
      show gw e singReps[i] • (Z : Set G) = iotaG e g • (Z : Set G)
      rw [leftCoset_eq_iff]
      have hgs : gw e singReps[i] = iotaG e (tw _ (singReps_lt _ hs)) := gw_eq _ _
      rcases hsg with h | h
      · rw [hgs, show tw _ (singReps_lt _ hs) = g from Subtype.ext h, inv_mul_cancel]
        exact one_mem Z
      · have e1 : iotaG e g = gw e singReps[i] * (sec3DData e t).z := by
          rw [hgs, hzgw, gw_eq [14] (by decide), ← map_mul]
          exact congrArg (iotaG e) (Subtype.ext (by
            show (g : Equiv.Perm (Fin 693)) = wP singReps[i] * wP [14]
            rw [wP_single]; exact h.symm))
        rw [e1, inv_mul_cancel_left]
        exact mem_zpowers _
    · rintro ⟨i, rfl⟩
      refine ⟨gw e singReps[i], ?_, ?_, rfl⟩
      · exact (gw_mem_toG (hlt i)).2 (sing_spec.1 _ (List.getElem_mem i.2)).1
      · rw [← gw_append, gw_eq_gw (b := []) (fun k hk => (List.mem_append.1 hk).elim (hlt i k)
          (hlt i k)) (by decide) (by rw [wP_append]; exact (sing_spec.1 _
            (List.getElem_mem i.2)).2), gw_nil]
  have hinj : Function.Injective f := by
    intro i j hij
    simp only [hf, leftCoset_eq_iff] at hij
    by_contra hne
    have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
    obtain ⟨h1, h2⟩ := sing_spec.2.1 i.val i.2 j.val j.2 hne'
    rcases Yamada.eq_one_or_eq_of_mem_zpowers hz2 hij with h | h
    · rw [inv_mul_eq_one] at h
      exact h1 (gw_injective (hlt i) (hlt j) h)
    · have e1 : gw e singReps[j] = gw e singReps[i] * gw e [14] := by
        rw [← hzgw, ← h, mul_inv_cancel_left]
      rw [← gw_append] at e1
      have := gw_injective (hlt j) (fun k hk => (List.mem_append.1 hk).elim (hlt i k)
        (fun h' => by simp at h'; omega)) e1
      rw [wP_append, wP_single] at this
      exact h2 this.symm
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3

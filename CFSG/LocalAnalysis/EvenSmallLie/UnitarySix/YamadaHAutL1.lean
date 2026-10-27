module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3EInput
public import CFSG.Certificates.Kernel.RankThree.F2Perm
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaHAutCheck

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaHAut

open CFSG.Fischer Subgroup CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.EvenSmallLie.UnitarySix.YamadaSec3


theorem chP2_le_normalizer_A4 : chP2.grp ≤ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
  refine chP2_le.trans (sup_le (sup_le xNorm_spec.1 ?_) ?_)
  · exact xComm_spec.2.2.2.1.trans (centralizer_le_normalizer _)
  · exact xComm_spec.2.1.trans (centralizer_le_normalizer _)

theorem l1Words_lt : ∀ w ∈ l1Words, ∀ k ∈ w, k < 18 := by decide +kernel

theorem qF_lt : ∀ q ∈ qF, ∀ k ∈ q, k < 18 := by decide

theorem l1_spec : ∀ a ∈ chA4.grp, a = 1 ∨ (∃ q ∈ qF, a = (wP q)⁻¹ * gP 14 * wP q) ∨
    ∀ p : Fin 693, ∃ w ∈ l1Words, wP w * a = a * wP w ∧ wP w p ≠ p := by
  intro x hx
  obtain ⟨a, hX, h⟩ := l1_check x hx
  unfold l1At at h
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true] at h
  rcases h with (h | ⟨k, hk, hv, h⟩) | h
  · exact Or.inl (eq_of_eqA hX rep_idA h)
  · refine Or.inr (Or.inl ⟨qF[k]!, ?_, ?_⟩)
    · rw [getElem!_pos qF k (by rw [show qF.length = 5 from rfl]; exact hk)]
      exact List.getElem_mem _
    · have hq := rep_wA tabs_check qF[k]! (qF_lt _ (by
        rw [getElem!_pos qF k (by rw [show qF.length = 5 from rfl]; exact hk)]
        exact List.getElem_mem _))
      have hc := rep_conjInvA hv (rep_gA tabs_check (by norm_num : 14 < 18))
      rw [permOfArr_eq_of_rep hq] at hc
      exact eq_of_eqA hX hc h
  · refine Or.inr (Or.inr fun p => ?_)
    unfold noCommonFix at h
    have h1 := allLt_spec h p.2
    simp only [List.any_eq_true, List.mem_filter] at h1
    obtain ⟨y, ⟨hy, hcomm⟩, hp⟩ := h1
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
    have hrep := rep_wA tabs_check w (l1Words_lt w hw)
    refine ⟨w, hw, eq_of_eqA (rep_compA hrep hX) (rep_compA hX hrep) hcomm, fun he => ?_⟩
    rw [bne_iff_ne, ne_eq, hrep p, he] at hp
    exact hp rfl

theorem labA4_inv : ∀ y ∈ chA4.grp, ∀ p : Fin 693, labA4[(y p : ℕ)]! = labA4[(p : ℕ)]! := by
  have h := labA4_check
  unfold labA4Check at h
  simp only [Bool.and_eq_true] at h
  let H : Subgroup (Equiv.Perm (Fin 693)) :=
    { carrier := {y | ∀ p : Fin 693, labA4[(y p : ℕ)]! = labA4[(p : ℕ)]!}
      mul_mem' := fun {a b} ha hb p => by rw [Equiv.Perm.mul_apply, ha, hb]
      one_mem' := fun p => rfl
      inv_mem' := fun {a} ha p => by rw [← ha (a⁻¹ p), perm_apply_inv'] }
  have hle : chA4.grp ≤ H := grp_le fun w hw p => by
    have h3 := allLt_spec (all_O_spec h.2 w hw) p.2
    rw [beq_iff_eq, (rep_wA_gens gensOK_chA4 hw) p] at h3
    exact h3
  exact fun y hy => hle hy

theorem p4_spec : ∀ k ∈ chK1.grp, (∀ w ∈ chA4.gens, k * wP w * k⁻¹ ∈ chA4.grp) →
    k ∈ chP2.grp := by
  intro x hx hn
  obtain ⟨a, hX, h⟩ := p4_check x hx
  have hv := CFSG.RankThree.Native.F2.validA_of_rep hX
  unfold p4At at h
  have hT : (chA4.O.all fun s => labA4[a[s[1]!]!]! == labA4[a[1]!]!) = true :=
    all_O_of_forall fun w hw => by
      rw [beq_iff_eq, (rep_wA_gens gensOK_chA4 hw).apply (by norm_num), hX.apply (Fin.isLt _),
        hX.apply (by norm_num)]
      have := labA4_inv _ (hn w hw) (x 1)
      simp only [Equiv.Perm.mul_apply, perm_inv_apply'] at this
      simpa using this
  have hall : (chA4.O.all fun s => siftA 693 lvA4 chA4.B 0 (conjA 693 a s)) = true :=
    all_O_of_forall fun w hw =>
      (mem_chA4_iff (rep_conj hv hX (rep_wA_gens gensOK_chA4 hw))).1 (hn w hw)
  rw [hT, hall] at h
  simp only [Bool.not_true, Bool.false_or] at h
  exact (mem_chP2_iff hX).2 h

theorem gP14_ne_one : gP 14 ≠ 1 := by
  intro h
  have h1 := card_chZ
  have h2 : chZ.grp = ⊥ := by
    rw [eq_bot_iff]
    refine (closure_le _).2 ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' : w = [14] := by simpa [chZ] using hw
    subst hw'
    rw [wP_single, h]
    exact one_mem _
  rw [h2, card_bot] at h1
  exact absurd h1 (by decide)


theorem fix_of_comm_conj_z {g y : Equiv.Perm (Fin 693)} (hT : g ∈ T46) (hy : y ∈ T46)
    (hc : y * (g * gP 14 * g⁻¹) = (g * gP 14 * g⁻¹) * y) : y (g 0) = g 0 := by
  have hc' : (g⁻¹ * y * g) * gP 14 = gP 14 * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * gP 14 = g⁻¹ * (y * (g * gP 14 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * gP 14 * g⁻¹) * y) * g := by rw [hc]
      _ = gP 14 * (g⁻¹ * y * g) := by group
  have hmem : g⁻¹ * y * g ∈ T46 := mul_mem (mul_mem (inv_mem hT) hy) hT
  have h0 := K1A1_fix _ (centralizer_gP14_le hmem hc')
  have h1 : g⁻¹ (y (g 0)) = 0 := by simpa [Equiv.Perm.mul_apply] using h0
  calc y (g 0) = g (g⁻¹ (y (g 0))) := by simp
    _ = g 0 := by rw [h1]

theorem normalizer_chA4_le {g : Equiv.Perm (Fin 693)} (hT : g ∈ T46)
    (hg : g ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) : g ∈ chP2.grp := by
  have hz : gP 14 ∈ chA4.grp := by
    rw [← wP_single]
    exact wP_mem_grp (by decide)
  have ha : g * gP 14 * g⁻¹ ∈ chA4.grp := (mem_normalizer_iff.1 hg _).1 hz
  rcases l1_spec _ ha with h1 | ⟨q, hq, h2⟩ | h3
  · exfalso
    apply gP14_ne_one
    calc gP 14 = g⁻¹ * (g * gP 14 * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · have hqT : wP q ∈ T46 := wP_mem_T46 q (qF_lt q hq)
    have hqP : wP q ∈ chP2.grp := by
      refine wP_mem_of_letters q fun k hk => ?_
      have : ∀ q ∈ qF, ∀ k ∈ q, [k] ∈ chP2.gens := by decide
      exact this q hq k hk
    have hc : (wP q * g) * gP 14 = gP 14 * (wP q * g) := by
      calc (wP q * g) * gP 14 = wP q * (g * gP 14 * g⁻¹) * g := by group
        _ = wP q * ((wP q)⁻¹ * gP 14 * wP q) * g := by rw [h2]
        _ = gP 14 * (wP q * g) := by group
    have hK := centralizer_gP14_le (mul_mem hqT hT) hc
    rw [chK1A1_eq] at hK
    have hx2 : wP q * g ∈ ((chK1.grp ⊔ chA1.grp : Subgroup _) : Set (Equiv.Perm (Fin 693))) := hK
    rw [coe_mul_of_left_le_normalizer_right _ _ chK1_le_normalizer_A1] at hx2
    obtain ⟨k, hk, a, ha', hka⟩ := hx2
    replace hka : k * a = wP q * g := hka
    have haP : a ∈ chP2.grp := chA1_le_chP2 ha'
    have hkN : k ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693))) := by
      have e1 : k = wP q * g * a⁻¹ := by rw [← hka]; group
      rw [e1]
      exact mul_mem (mul_mem (chP2_le_normalizer_A4 hqP) hg)
        (inv_mem (chP2_le_normalizer_A4 haP))
    have hkP := p4_spec k hk fun w hw => (mem_normalizer_iff.1 hkN _).1 (wP_mem_grp hw)
    have e2 : g = (wP q)⁻¹ * (k * a) := by rw [hka]; group
    rw [e2]
    exact mul_mem (inv_mem hqP) (mul_mem hkP haP)
  · exfalso
    obtain ⟨w, hw, hc, hp⟩ := h3 (g 0)
    exact hp (fix_of_comm_conj_z hT (wP_mem_T46 w (l1Words_lt w hw)) hc)

theorem normalizer_chA4_le_normalizer_A3 {g : Equiv.Perm (Fin 693)} (hT : g ∈ T46)
    (hg : g ∈ normalizer (chA4.grp : Set (Equiv.Perm (Fin 693)))) :
    g ∈ normalizer (chA3.grp : Set (Equiv.Perm (Fin 693))) :=
  chP2_le_normalizer (normalizer_chA4_le hT hg)

end CFSG.EvenSmallLie.UnitarySix.YamadaHAut

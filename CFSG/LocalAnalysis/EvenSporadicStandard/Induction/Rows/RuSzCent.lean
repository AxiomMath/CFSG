module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.RuSzNormal

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.RuSz

open Subgroup CFSG.Blueprint CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.RuSchreier CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen
  CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Sporadic.Th (Rep)

section Base


theorem eq_one_of_fix_base {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (h : ∀ x : Fin 4060, x.val < 4 → g x = x) : g = 1 := by
  have hQ : ValidSchreier ruChainJoin := ruChain_valid ruChainJoin_check.1
  obtain ⟨hlev, hterm, -⟩ := RawSchreierDatum.schreier_chain_order ruChainJoin hQ
  have h1 := hlev ruChainJoin.baseCount le_rfl
  rw [hterm] at h1
  have e : ruChainJoin.base.toList = ruFinList 4060 (by decide) ruJoinBase :=
    RawSchreierDatum.ofArrays_base_toList
  have hmem : g ∈ ruChainJoin.originalSubgroup ⊓ fixingSubgroup (Equiv.Perm (Fin 4060))
      {b | b ∈ ruChainJoin.base.toList.take ruChainJoin.baseCount} := by
    rw [Subgroup.mem_inf]
    refine ⟨by rw [ruChainJoin_sub, ← ruP_eq_sup]; exact hg, ?_⟩
    rw [mem_fixingSubgroup_iff]
    intro b hb
    have hb' : b ∈ ruChainJoin.base.toList := List.mem_of_mem_take hb
    rw [e] at hb'
    have hlt : b.val < 4 := by
      simp only [ruFinList, ruJoinBase, List.mem_map, List.mem_cons, List.not_mem_nil,
        or_false] at hb'
      obtain ⟨x, hx, rfl⟩ := hb'
      rcases hx with rfl | rfl | rfl | rfl <;> simp
    exact h b hlt
  rw [← h1] at hmem
  exact Subgroup.mem_bot.1 hmem

end Base

section Cent


@[expose] def DK : Subgroup (Equiv.Perm (Fin 4060)) :=
  ruP ⊓ Subgroup.centralizer (K0 : Set (Equiv.Perm (Fin 4060)))

theorem mem_DK {g : Equiv.Perm (Fin 4060)} :
    g ∈ DK ↔ g ∈ ruP ∧ ∀ k ∈ K0, k * g = g * k := by
  rw [DK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem ap_kTab (w : String) (x : Fin 4060) : ap (kTab w) x.val = (kG w x).val := by
  have h := rep_kTab w x.val x.2
  rw [CFSG.Sporadic.Th.idx_of_lt _ x.2] at h
  simpa using h

theorem kG_zero {w : String} (hw : w ∈ hWords) :
    kG w ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
  have h := szChecks.2.2.2.2.2.1
  simp only [ruSzFixOK, Bool.and_eq_true, beq_iff_eq] at h
  have := List.all_eq_true.1 h.1 (kTab w) (List.mem_map_of_mem hw)
  have h2 := ap_kTab w ⟨0, by norm_num⟩
  rw [beq_iff_eq] at this
  exact Fin.ext (by rw [← h2]; exact this)

theorem kG_pt {j : ℕ} {w : String} (hw : (j, w) ∈ ptWords) :
    (kG w ⟨0, by norm_num⟩).val = j := by
  have h := szChecks.2.2.2.2.2.2
  simp only [ruSzPtsOK, List.all_eq_true, beq_iff_eq] at h
  rw [← ap_kTab w ⟨0, by norm_num⟩]
  exact h (j, w) hw

theorem image_mem_fix {g : Equiv.Perm (Fin 4060)} (hg : g ∈ DK) :
    (g ⟨0, by norm_num⟩).val ∈ [0, 1, 3645, 3692] := by
  have h := szChecks.2.2.2.2.2.1
  simp only [ruSzFixOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, hlist⟩ := h
  obtain ⟨-, hcomm⟩ := mem_DK.1 hg
  set x := g ⟨0, by norm_num⟩ with hx
  have hfix : ∀ w ∈ hWords, kG w x = x := by
    intro w hw
    have hk := kG_mem w
    calc kG w (g ⟨0, by norm_num⟩) = (kG w * g) ⟨0, by norm_num⟩ := rfl
      _ = (g * kG w) ⟨0, by norm_num⟩ := by rw [hcomm (kG w) hk]
      _ = g (kG w ⟨0, by norm_num⟩) := rfl
      _ = g ⟨0, by norm_num⟩ := by rw [kG_zero hw]
  have hmem : x.val ∈ (List.range 4060).filter
      (fun y => (hWords.map kTab).all fun T => ap T y == y) := by
    rw [List.mem_filter]
    refine ⟨List.mem_range.2 x.2, ?_⟩
    simp only [List.all_eq_true, List.mem_map]
    rintro _ ⟨w, hw, rfl⟩
    rw [beq_iff_eq, ap_kTab, hfix w hw]
  rw [hlist] at hmem
  exact hmem

theorem card_DK_le : Nat.card DK ≤ 4 := by
  classical
  let T : Finset (Fin 4060) :=
    {⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨3645, by norm_num⟩, ⟨3692, by norm_num⟩}
  have hT : T.card = 4 := by decide
  have hmapsto : ∀ g : DK, (g : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ ∈ T := by
    intro g
    have h := image_mem_fix g.2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    simp only [T, Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  let f : DK → T := fun g => ⟨(g : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩, hmapsto g⟩
  have hinj : Function.Injective f := by
    intro g₁ g₂ h12
    have h0 : (g₁ : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ =
        (g₂ : Equiv.Perm (Fin 4060)) ⟨0, by norm_num⟩ := congrArg Subtype.val h12
    set g : Equiv.Perm (Fin 4060) := (g₁ : Equiv.Perm (Fin 4060))⁻¹ * g₂ with hg
    have hgD : g ∈ DK := DK.mul_mem (DK.inv_mem g₁.2) g₂.2
    have hg0 : g ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
      rw [hg, Equiv.Perm.mul_apply, ← h0]
      exact Equiv.symm_apply_apply _ _
    obtain ⟨hgP, hcomm⟩ := mem_DK.1 hgD
    have hpt : ∀ {j : ℕ} {w : String}, (j, w) ∈ ptWords → ∀ hj : j < 4060,
        g ⟨j, hj⟩ = ⟨j, hj⟩ := by
      intro j w hw hj
      have hk := kG_mem w
      have h1 := kG_pt hw
      have h2 : kG w ⟨0, by norm_num⟩ = ⟨j, hj⟩ := Fin.ext h1
      calc g ⟨j, hj⟩ = g (kG w ⟨0, by norm_num⟩) := by rw [h2]
        _ = (g * kG w) ⟨0, by norm_num⟩ := rfl
        _ = (kG w * g) ⟨0, by norm_num⟩ := by rw [hcomm (kG w) hk]
        _ = kG w (g ⟨0, by norm_num⟩) := rfl
        _ = ⟨j, hj⟩ := by rw [hg0, h2]
    have hg1 : g = 1 := by
      refine eq_one_of_fix_base hgP fun x hx => ?_
      obtain ⟨xv, hxv⟩ := x
      simp only at hx
      interval_cases xv
      · exact hg0
      · exact hpt (j := 1) (w := "bbabaBabaBaBabaBabab") (by simp [ptWords]) _
      · exact hpt (j := 2) (w := "abbabaBabbaBababbaBa") (by simp [ptWords]) _
      · exact hpt (j := 3) (w := "BabbaBabaBaBabaBabaBaB") (by simp [ptWords]) _
    have : (g₁ : Equiv.Perm (Fin 4060)) = g₂ := by
      have := congrArg (fun y => (g₁ : Equiv.Perm (Fin 4060)) * y) hg1
      simpa [hg] using this.symm
    exact Subtype.ext this
  calc Nat.card DK ≤ Nat.card T := Nat.card_le_card_of_injective f hinj
    _ = 4 := by rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT]

theorem ruA0_mem_DK : ruA0 ∈ DK :=
  mem_DK.2 ⟨ruA0_mem, fun k hk => (ruA0_comm_K0 k hk).symm⟩

theorem bG_mem_DK : bG ∈ DK :=
  mem_DK.2 ⟨ruL_le rep_b.2, fun k hk => (bG_comm_K0 k hk).symm⟩

theorem card_DK_ge : 4 ≤ Nat.card DK := by
  classical
  have h2 : orderOf ruA0 = 2 := orderOf_ruA0
  have ha1 : ruA0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h2
    omega
  have haa : ruA0 * ruA0 = 1 := by
    rw [← pow_two]
    exact h2 ▸ pow_orderOf_eq_one ruA0
  have hb1 := bG_ne_one
  have hba := bG_ne_a0
  let a : DK := ⟨ruA0, ruA0_mem_DK⟩
  let b : DK := ⟨bG, bG_mem_DK⟩
  have h1a : (1 : DK) ≠ a := fun h => ha1 (congrArg Subtype.val h).symm
  have h1b : (1 : DK) ≠ b := fun h => hb1 (congrArg Subtype.val h).symm
  have hab : a ≠ b := fun h => hba (congrArg Subtype.val h).symm
  have h1ab : (1 : DK) ≠ a * b := by
    intro h
    have h' : (1 : Equiv.Perm (Fin 4060)) = ruA0 * bG := congrArg Subtype.val h
    apply hba
    calc bG = ruA0 * (ruA0 * bG) := by rw [← mul_assoc, haa, one_mul]
      _ = ruA0 := by rw [← h', mul_one]
  have haab : a ≠ a * b := by
    intro h
    have h' : ruA0 = ruA0 * bG := congrArg Subtype.val h
    apply hb1
    have := mul_left_cancel (a := ruA0) (b := 1) (c := bG) (by rw [mul_one]; exact h')
    exact this.symm
  have hbab : b ≠ a * b := by
    intro h
    have h' : bG = ruA0 * bG := congrArg Subtype.val h
    apply ha1
    have := mul_right_cancel (a := 1) (b := bG) (c := ruA0) (by rw [one_mul]; exact h')
    exact this.symm
  have : Finite DK := inferInstance
  let _ : Fintype DK := Fintype.ofFinite DK
  have hs : ({1, a, b, a * b} : Finset DK).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hbab]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, haab⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h1a, h1b, h1ab⟩
  have := Finset.card_le_univ ({1, a, b, a * b} : Finset DK)
  rw [hs] at this
  rw [Nat.card_eq_fintype_card]
  exact this

theorem card_DK : Nat.card DK = 4 := le_antisymm card_DK_le card_DK_ge

end Cent

end CFSG.EvenSporadicStandard.Induction.RuSz

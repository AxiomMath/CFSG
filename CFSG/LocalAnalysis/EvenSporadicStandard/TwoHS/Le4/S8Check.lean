module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix Finset

@[expose] def rpow2 (k : ℕ) (a : R4) : R4 := (fun b => rmul b b)^[k] a

theorem ofR4_rpow2 (k : ℕ) (a : R4) : ofR4 (rpow2 k a) = ofR4 a ^ (2 ^ k) := by
  induction k with
  | zero => simp [rpow2]
  | succ k ih =>
    rw [rpow2, Function.iterate_succ_apply', ← rpow2, ofR4_rmul, ih, ← pow_add, ← two_mul,
      ← pow_succ']

@[expose] def allVR : List RV :=
  (List.range 256).map fun n => ⟨n % 4, n / 4 % 4, n / 16 % 4, n / 64 % 4⟩

@[expose] def imCardR (c : R4) : ℕ := ((allVR.map fun v => rmv (rsub1 c) v).dedup).length

@[expose] def invPairsR (tr : List R4) : List (R4 × R4) :=
  tr.flatMap fun a => (tr.filter fun b => rmul a b == R4.one).map fun b => (a, b)

@[expose] def conjR (ip : List (R4 × R4)) (b : R4) : List R4 :=
  (ip.map fun p => rmul (rmul p.1 b) p.2).dedup

@[expose] def TRaw (sr tr : List R4) (ip : List (R4 × R4)) : Prop :=
  (∀ a ∈ sr, a.wf) ∧ (∀ a ∈ tr, a.wf) ∧
  (∀ p ∈ ip, p.1 ∈ tr ∧ p.2 ∈ tr ∧ rmul p.1 p.2 = R4.one) ∧
  R4.one ∈ tr ∧
  (∀ a ∈ tr, ∀ b ∈ tr, rmul a b ∈ tr) ∧
  (∀ a ∈ tr, ∃ b ∈ tr, rmul a b = R4.one) ∧
  (∀ a ∈ tr, a ∈ sr) ∧
  (∀ s ∈ shatR, s ∈ tr) ∧
  (∀ a ∈ tr, rpow2 7 a = R4.one) ∧
  (∀ b ∈ tr, b ≠ R4.one → rmul b b = R4.one →
    5 ≤ (conjR ip b).length ∨ 5 ≤ ((conjR ip b).map imCardR).sum) ∧
  (∀ v ∈ fR, (tr.map fun a => rmv a v).dedup.length ≤ 4) ∧
  (∀ v ∈ fR, 4 < (tr.map fun a => rmv a (radd tRV v)).dedup.length) ∧
  (∀ v ∈ fR, ∃ a ∈ tr, rmv a tRV = radd tRV v) ∧
  (∀ a ∈ tr, (∀ v ∈ fR, rmv a v = v) → rmul a a = R4.one) ∧
  (∀ a ∈ tr, (∀ v ∈ omR, rmv a v = v) → a = R4.one ∨ a = R4.negOne) ∧
  (∀ a ∈ tr, rmv a tRV = tRV → a ∈ shatR) ∧
  (∀ b ∈ sr, b ∈ tr ∨ ∃ a ∈ tr, ∀ a' ∈ tr, rmul b a ≠ rmul a' b)

instance (sr tr : List R4) (ip : List (R4 × R4)) : Decidable (TRaw sr tr ip) := by
  unfold TRaw; infer_instance

@[expose] def tfR (a : R4) : Bool :=
  let sr := sListR a
  let tr := tListR a
  decide (TRaw sr tr (invPairsR tr))

theorem card_toFinset_map_le {α β : Type*} [DecidableEq α] [DecidableEq β] (l : List α)
    (f : α → β) : ((l.map f).toFinset).card ≤ l.dedup.length := by
  have h : (l.map f).toFinset = (l.dedup.map f).toFinset := by
    ext y
    simp [List.mem_dedup]
  rw [h]
  exact (List.toFinset_card_le _).trans (by simp)

theorem length_dedup_le_card_toFinset_map {l : List RV} (hl : ∀ v ∈ l, v.wf) :
    l.dedup.length ≤ ((l.map ofRV).toFinset).card := by
  have h : (l.map ofRV).toFinset = (l.dedup.map ofRV).toFinset := by
    ext y
    simp [List.mem_dedup]
  rw [h]
  have hnd : (l.dedup.map ofRV).Nodup := by
    refine List.Nodup.map_on ?_ (List.nodup_dedup l)
    intro x hx y hy hxy
    exact ofRV_inj (hl x (List.mem_dedup.1 hx)) (hl y (List.mem_dedup.1 hy)) hxy
  rw [List.toFinset_card_of_nodup hnd, List.length_map]

theorem imCardR_le {c : R4} (hc : c.wf) : imCardR c ≤ (imSet (ofR4 c)).card := by
  unfold imCardR
  have hwf : ∀ v ∈ (allVR.map fun v => rmv (rsub1 c) v), v.wf := by
    intro v hv
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hv
    exact wf_rmv _ _
  refine (length_dedup_le_card_toFinset_map hwf).trans ?_
  apply Finset.card_le_card
  intro y hy
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  simp only [imSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨ofRV w, by rw [ofRV_rmv, ofR4_rsub1 hc]⟩

theorem imSet_card_pos (B : M4) : 1 ≤ (imSet B).card :=
  Finset.card_pos.2 ⟨0, Finset.mem_image.2 ⟨0, Finset.mem_univ _, by simp⟩⟩

theorem TRaw.star {tr : List R4} {ip : List (R4 × R4)}
    (hip : ∀ p ∈ ip, p.1 ∈ tr ∧ p.2 ∈ tr ∧ rmul p.1 p.2 = R4.one)
    (hstar : ∀ b ∈ tr, b ≠ R4.one → rmul b b = R4.one →
      5 ≤ (conjR ip b).length ∨ 5 ≤ ((conjR ip b).map imCardR).sum) :
    ∀ B ∈ tr.map ofR4, B ≠ 1 → B * B = 1 →
      5 ≤ ∑ B' ∈ clSet (tr.map ofR4) B, (imSet B').card := by
  intro B hB hB1 hBB
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
  have hb1 : b ≠ R4.one := fun h => hB1 (by rw [h, ofR4_one])
  have hbb : rmul b b = R4.one := by
    apply ofR4_inj (wf_rmul _ _) wf_one
    rw [ofR4_rmul, ofR4_one]
    exact hBB
  have hclwf : ∀ c ∈ conjR ip b, c.wf := by
    intro c hc
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hc)
    exact wf_rmul _ _
  have hsub : ((conjR ip b).map ofR4).toFinset ⊆ clSet (tr.map ofR4) (ofR4 b) := by
    intro B' hB'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hB')
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hc)
    obtain ⟨hp1, hp2, hp12⟩ := hip p hp
    refine mem_clSet.2 ⟨(ofR4 p.1, ofR4 p.2), ?_, ?_⟩
    · refine mem_invPairs_iff.2 ⟨List.mem_map.2 ⟨_, hp1, rfl⟩, List.mem_map.2 ⟨_, hp2, rfl⟩, ?_⟩
      show ofR4 p.1 * ofR4 p.2 = 1
      rw [← ofR4_rmul, hp12, ofR4_one]
    · show ofR4 p.1 * ofR4 b * ofR4 p.2 = ofR4 (rmul (rmul p.1 b) p.2)
      rw [ofR4_rmul, ofR4_rmul]
  have hnd : ((conjR ip b).map ofR4).Nodup :=
    List.Nodup.map_on (fun x hx y hy hxy => ofR4_inj (hclwf x hx) (hclwf y hy) hxy)
      (List.nodup_dedup _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset hsub)
  rw [List.sum_toFinset _ hnd]
  rcases hstar b hb hb1 hbb with h5 | h5
  · calc 5 ≤ (conjR ip b).length := h5
      _ = (((conjR ip b).map ofR4).map fun B' => (imSet B').card).length := by simp
      _ ≤ _ := List.length_le_sum_of_one_le _ (by
          intro i hi
          obtain ⟨B', -, rfl⟩ := List.mem_map.1 hi
          exact imSet_card_pos _)
  · refine le_trans h5 ?_
    rw [List.map_map]
    refine List.sum_le_sum ?_
    intro c hc
    simp only [Function.comp_apply]
    exact imCardR_le (hclwf c hc)

theorem TRaw.sound {sr tr : List R4} {ip : List (R4 × R4)} (h : TRaw sr tr ip)
    (hom : ∀ v ∈ omList, v + v = 0) : TFactsOf (sr.map ofR4) (tr.map ofR4) := by
  obtain ⟨hsw, htw, hip, hone, hmul, hinv, hsub, hshat, hpow, hstar, hfs, htl, hft, hcf, hkk, hst,
    hnorm⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, TRaw.star hip hstar, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_map.2 ⟨R4.one, hone, ofR4_one⟩
  · intro A hA B hB
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
    exact List.mem_map.2 ⟨rmul a b, hmul a ha b hb, ofR4_rmul a b⟩
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    obtain ⟨b, hb, hab⟩ := hinv a ha
    exact ⟨ofR4 b, List.mem_map.2 ⟨b, hb, rfl⟩, by rw [← ofR4_rmul, hab, ofR4_one]⟩
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    exact List.mem_map.2 ⟨a, hsub a ha, rfl⟩
  · intro s hs
    exact List.mem_map.2 ⟨toR4 s, hshat _ (List.mem_map.2 ⟨s, hs, rfl⟩), ofR4_toR4 s⟩
  · intro A hA
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    calc ofR4 a ^ 128 = ofR4 a ^ 2 ^ 7 := rfl
      _ = ofR4 (rpow2 7 a) := (ofR4_rpow2 7 a).symm
      _ = 1 := by rw [hpow a ha, ofR4_one]
  · intro v hv
    have h1 := hfs _ (List.mem_map.2 ⟨v, hv, rfl⟩)
    have heq : ((tr.map ofR4).map fun A => A *ᵥ v) =
        (tr.map fun a => rmv a (toRV v)).map ofRV := by
      simp only [List.map_map, Function.comp_def, ofRV_rmv, ofRV_toRV]
    rw [heq]
    exact (card_toFinset_map_le _ _).trans h1
  · intro v hv
    have h1 := htl _ (List.mem_map.2 ⟨v, hv, rfl⟩)
    have heq : ((tr.map ofR4).map fun A => A *ᵥ (tVec + v)) =
        (tr.map fun a => rmv a (radd tRV (toRV v))).map ofRV := by
      simp only [List.map_map, Function.comp_def, ofRV_rmv, ofRV_radd, ofRV_toRV, tRV]
    rw [heq]
    refine lt_of_lt_of_le h1 (length_dedup_le_card_toFinset_map ?_)
    intro w hw
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
    exact wf_rmv _ _
  · intro v hv
    obtain ⟨a, ha, hav⟩ := hft _ (List.mem_map.2 ⟨v, hv, rfl⟩)
    refine ⟨ofR4 a, List.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
    have := congrArg ofRV hav
    rw [ofRV_rmv, ofRV_radd] at this
    simpa [tRV, ofRV_toRV] using this
  · intro A hA hfix
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    have : ∀ w ∈ fR, rmv a w = w := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      apply ofRV_inj (wf_rmv _ _) (wf_toRV _)
      rw [ofRV_rmv, ofRV_toRV]
      exact hfix v hv
    rw [← ofR4_rmul, hcf a ha this, ofR4_one]
  · intro A hA hker
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    have : ∀ w ∈ omR, rmv a w = w := by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
      apply ofRV_inj (wf_rmv _ _) (wf_toRV _)
      rw [ofRV_rmv, ofRV_toRV]
      exact hker v (hom v hv)
    rcases hkk a ha this with h | h
    · left
      rw [h, ofR4_one]
    · right
      rw [h, ofR4_negOne]
  · intro A hA hAt
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hA
    have h1 : rmv a tRV = tRV := by
      apply ofRV_inj (wf_rmv _ _) (wf_toRV _)
      rw [ofRV_rmv]
      simp only [tRV, ofRV_toRV]
      exact hAt
    obtain ⟨s, hs, hsa⟩ := List.mem_map.1 (hst a ha h1)
    rw [← hsa, ofR4_toR4]
    exact hs
  · intro B hB hBn
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hB
    rcases hnorm b hb with h | ⟨a, ha, h⟩
    · exact absurd (List.mem_map.2 ⟨b, h, rfl⟩) hBn
    · refine ⟨ofR4 a, List.mem_map.2 ⟨a, ha, rfl⟩, ?_⟩
      intro A' hA' heq
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 hA'
      apply h a' ha'
      apply ofR4_inj (wf_rmul _ _) (wf_rmul _ _)
      rw [ofR4_rmul, ofR4_rmul]
      exact heq

theorem tfacts_of_check (α : M4) (hom : ∀ v ∈ omList, v + v = 0) (h : tfR (toR4 α) = true) :
    TFacts α := by
  simp only [tfR, decide_eq_true_eq] at h
  rw [TFacts, sList_eq]
  exact h.sound hom

end CFSG.EvenSporadicStandard.TwoHS

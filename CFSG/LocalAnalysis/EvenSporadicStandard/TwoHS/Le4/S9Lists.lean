module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S8Fin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Data

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Matrix

@[expose] def vecAll : List RV :=
  (List.range 256).map fun k => ⟨k / 64 % 4, k / 16 % 4, k / 4 % 4, k % 4⟩

theorem mem_vecAll {w : RV} (hw : w.wf) : w ∈ vecAll := by
  rcases w with ⟨v0, v1, v2, v3⟩
  simp only [RV.wf] at hw
  obtain ⟨h0, h1, h2, h3⟩ := hw
  refine List.mem_map.2 ⟨64 * v0 + 16 * v1 + 4 * v2 + v3, List.mem_range.2 (by omega), ?_⟩
  simp only [RV.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem wf_of_mem_vecAll {w : RV} (hw : w ∈ vecAll) : w.wf := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hw
  simp only [RV.wf]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem nodup_vecAll : vecAll.Nodup := by
  unfold vecAll
  refine (List.nodup_range).map_on ?_
  intro a ha b hb h
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  simp only [RV.mk.injEq] at h
  omega

theorem card_filter_V4_eq (P : V4 → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card = (vecAll.filter fun w => decide (P (ofRV w))).length := by
  rw [← List.toFinset_card_of_nodup (nodup_vecAll.filter _)]
  refine Finset.card_bij (fun v _ => toRV v) ?_ ?_ ?_
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    refine ⟨mem_vecAll (wf_toRV v), ?_⟩
    rw [ofRV_toRV]
    exact hv
  · intro v _ w _ h
    have := congrArg ofRV h
    rwa [ofRV_toRV, ofRV_toRV] at this
  · intro w hw
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw
    refine ⟨ofRV w, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hw.2
    · exact toRV_ofRV (wf_of_mem_vecAll hw.1)

@[expose] def closureStep (gens : List R4) (L : List R4) : List R4 :=
  (L ++ L.flatMap fun a => gens.map (rmul a)).dedup

@[expose] def closureR (gens : List R4) : ℕ → List R4 → List R4
  | 0, L => L
  | n + 1, L => closureR gens n (closureStep gens L)

theorem closureR_sound {R : Set M4} (hmul : ∀ A ∈ R, ∀ B ∈ R, A * B ∈ R) {gens : List R4}
    (hg : ∀ g ∈ gens, ofR4 g ∈ R) :
    ∀ (n : ℕ) (L : List R4), (∀ a ∈ L, ofR4 a ∈ R) → ∀ a ∈ closureR gens n L, ofR4 a ∈ R := by
  intro n
  induction n with
  | zero => intro L hL a ha; exact hL a ha
  | succ n ih =>
    intro L hL a ha
    refine ih (closureStep gens L) ?_ a ha
    intro b hb
    simp only [closureStep, List.mem_dedup, List.mem_append, List.mem_flatMap,
      List.mem_map] at hb
    rcases hb with hb | ⟨c, hc, g, hg', rfl⟩
    · exact hL b hb
    · rw [ofR4_rmul]
      exact hmul _ (hL c hc) _ (hg g hg')

@[expose] def genR : List R4 := [toR4 gamma1Mat, toR4 gamma2Mat]

@[expose] def closureSet : List R4 := closureR genR 40 [R4.one]

@[expose] def fixListNum (S : List R4) : ℕ :=
  (vecAll.filter fun w => S.all fun a => rmv a w == w).length

@[expose] def subCheck (S : List R4) : Bool :=
  !(S.all fun a => S.all fun b => S.contains (rmul a b)) || !S.contains R4.one ||
    !(S.any fun a => a != R4.one) || decide (S.length * fixListNum S < 256)

@[expose] def listCheck : Bool :=
  q0R.length == 336 && decide q0R.Nodup && q0R.all (fun a => closureSet.contains a) &&
  shatR.length == 16 && decide shatR.Nodup && shatR.contains R4.one &&
  shatR.all (fun a => shatR.all fun b => shatR.contains (rmul a b)) &&
  shatR.all (fun a => shatR.any fun b => rmul a b == R4.one && rmul b a == R4.one) &&
  shatR.any (fun a => a.a22 == 3) && shatR.sublists.all subCheck

structure ListFacts : Prop where
  q0_nodup : q0List.Nodup
  q0_len : q0List.length = 336
  closure : ∀ R : Set M4, (∀ A ∈ R, ∀ B ∈ R, A * B ∈ R) → (1 : M4) ∈ R → gamma1Mat ∈ R →
    gamma2Mat ∈ R → ∀ A ∈ q0List, A ∈ R
  shat_nd : shatList.Nodup
  shat_len : shatList.length = 16
  shat_one : (1 : M4) ∈ shatList
  shat_mul : ∀ A ∈ shatList, ∀ B ∈ shatList, A * B ∈ shatList
  shat_inv : ∀ A ∈ shatList, ∃ B ∈ shatList, A * B = 1 ∧ B * A = 1
  shat_neg : ∃ A ∈ shatList, A 2 2 = 3
  Sub : ∀ T : Finset M4, (∀ A ∈ T, A ∈ shatList) → (∀ A ∈ T, ∀ B ∈ T, A * B ∈ T) →
    (1 : M4) ∈ T → (∃ A ∈ T, A ≠ 1) →
    T.card * (Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v).card < 256

theorem mem_shatR {a : R4} (h : a ∈ shatR) : ∃ A ∈ shatList, toR4 A = a := by
  simpa [shatR] using h

theorem toR4_mem_shatR {A : M4} (h : A ∈ shatList) : toR4 A ∈ shatR :=
  List.mem_map.2 ⟨A, h, rfl⟩

theorem wf_of_mem_shatR {a : R4} (h : a ∈ shatR) : a.wf := by
  obtain ⟨A, -, rfl⟩ := mem_shatR h
  exact wf_toR4 A

theorem fix_iff {a : R4} {A : M4} (hA : ofR4 a = A) {w : RV} (hw : w.wf) :
    (A *ᵥ ofRV w = ofRV w) ↔ rmv a w = w := by
  have h1 : A *ᵥ ofRV w = ofRV (rmv a w) := by rw [ofRV_rmv, hA]
  rw [h1]
  exact ⟨fun h => ofRV_inj (wf_rmv _ _) hw h, fun h => by rw [h]⟩

theorem toR4_one : toR4 (1 : M4) = R4.one := by
  rw [← ofR4_one, toR4_ofR4 wf_one]

theorem card_fix_list_eq (S : List M4) :
    (Finset.univ.filter fun v : V4 => ∀ A ∈ S, A *ᵥ v = v).card = fixListNum (S.map toR4) := by
  rw [card_filter_V4_eq]
  unfold fixListNum
  congr 1
  apply List.filter_congr
  intro w hw
  have hwf := wf_of_mem_vecAll hw
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, beq_iff_eq, List.mem_map]
  constructor
  · rintro h a ⟨A, hA, rfl⟩
    exact (fix_iff (ofR4_toR4 A) hwf).1 (h A hA)
  · intro h A hA
    exact (fix_iff (ofR4_toR4 A) hwf).2 (h _ ⟨A, hA, rfl⟩)

theorem sub_of_check (hnd0 : shatList.Nodup) (h : ∀ x ∈ shatR.sublists, subCheck x = true) :
    ∀ T : Finset M4, (∀ A ∈ T, A ∈ shatList) → (∀ A ∈ T, ∀ B ∈ T, A * B ∈ T) →
      (1 : M4) ∈ T → (∃ A ∈ T, A ≠ 1) →
      T.card * (Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v).card < 256 := by
  intro T hT hmul h1 ⟨A₀, hA₀, hA₀1⟩
  set S : List M4 := shatList.filter (fun A => A ∈ T) with hS
  have hSmem : ∀ A, A ∈ S ↔ A ∈ T := by
    intro A
    simp only [hS, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hT A h, h⟩⟩
  have hsub : List.Sublist (S.map toR4) shatR := List.Sublist.map toR4 List.filter_sublist
  have hS' := h _ (List.mem_sublists.2 hsub)
  have hnd : S.Nodup := hnd0.filter _
  have hcard : S.length = T.card := by
    rw [← List.toFinset_card_of_nodup hnd]
    congr 1
    ext A
    simp [hSmem]
  have hF : (Finset.univ.filter fun v : V4 => ∀ A ∈ T, A *ᵥ v = v) =
      (Finset.univ.filter fun v : V4 => ∀ A ∈ S, A *ᵥ v = v) := by
    apply Finset.filter_congr
    intro v _
    constructor
    · intro h A hA
      exact h A ((hSmem A).1 hA)
    · intro h A hA
      exact h A ((hSmem A).2 hA)
  rw [hF, card_fix_list_eq, ← hcard]
  unfold subCheck at hS'
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, List.length_map] at hS'
  rcases hS' with ((hc | hone) | hnon) | hlt
  · exfalso
    have : ((List.map toR4 S).all fun a => (List.map toR4 S).all fun b =>
        (List.map toR4 S).contains (rmul a b)) = true := by
      simp only [List.all_eq_true, List.contains_iff_mem, List.mem_map]
      rintro a ⟨A, hA, rfl⟩ b ⟨B, hB, rfl⟩
      refine ⟨A * B, (hSmem _).2 (hmul A ((hSmem A).1 hA) B ((hSmem B).1 hB)), ?_⟩
      rw [← toR4_ofR4 (wf_rmul (toR4 A) (toR4 B)), ofR4_rmul, ofR4_toR4, ofR4_toR4]
    rw [this] at hc
    exact Bool.noConfusion hc
  · exfalso
    have : (List.map toR4 S).contains R4.one = true := by
      rw [List.contains_iff_mem]
      exact List.mem_map.2 ⟨1, (hSmem 1).2 h1, toR4_one⟩
    rw [this] at hone
    exact Bool.noConfusion hone
  · exfalso
    have : ((List.map toR4 S).any fun a => a != R4.one) = true := by
      rw [List.any_eq_true]
      refine ⟨toR4 A₀, List.mem_map.2 ⟨A₀, (hSmem _).2 hA₀, rfl⟩, ?_⟩
      rw [bne_iff_ne]
      intro h
      apply hA₀1
      rw [← ofR4_toR4 A₀, h, ofR4_one]
    rw [this] at hnon
    exact Bool.noConfusion hnon
  · exact hlt


theorem listFacts_of_check (h : listCheck = true) : ListFacts := by
  simp only [listCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true, List.contains_iff_mem] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hone : ∀ A ∈ shatList, toR4 A = R4.one → A = 1 := fun A _ hA => by
    rw [← ofR4_toR4 A, hA, ofR4_one]
  refine ⟨List.Nodup.of_map toR4 h2, by simpa [q0R] using h1, ?_, List.Nodup.of_map toR4 h5,
    by simpa [shatR] using h4, ?_, ?_, ?_, ?_, sub_of_check (List.Nodup.of_map toR4 h5) h10⟩
  · intro R hmul h1R hg1 hg2 A hA
    have hgens : ∀ g ∈ genR, ofR4 g ∈ R := by
      intro g hg
      simp only [genR, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · rw [ofR4_toR4]; exact hg1
      · rw [ofR4_toR4]; exact hg2
    have hinit : ∀ a ∈ [R4.one], ofR4 a ∈ R := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      rw [ofR4_one]
      exact h1R
    have := closureR_sound hmul hgens 40 [R4.one] hinit (toR4 A)
      (h3 (toR4 A) (List.mem_map.2 ⟨A, hA, rfl⟩))
    rwa [ofR4_toR4] at this
  · obtain ⟨A, hA, hA1⟩ := mem_shatR h6
    rw [← hone A hA hA1]
    exact hA
  · intro A hA B hB
    obtain ⟨C, hC, hCe⟩ := mem_shatR (h7 _ (toR4_mem_shatR hA) _ (toR4_mem_shatR hB))
    have : A * B = C := by
      rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, ← hCe, ofR4_toR4]
    rw [this]
    exact hC
  · intro A hA
    obtain ⟨b, hb, hb1, hb2⟩ := h8 _ (toR4_mem_shatR hA)
    obtain ⟨B, hB, rfl⟩ := mem_shatR hb
    refine ⟨B, hB, ?_, ?_⟩
    · rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, hb1, ofR4_one]
    · rw [← ofR4_toR4 A, ← ofR4_toR4 B, ← ofR4_rmul, hb2, ofR4_one]
  · obtain ⟨a, ha, ha3⟩ := h9
    obtain ⟨A, hA, rfl⟩ := mem_shatR ha
    refine ⟨A, hA, ?_⟩
    have : (A 2 2).val = 3 := ha3
    rw [← ZMod.natCast_zmod_val (A 2 2), this]
    rfl

end CFSG.EvenSporadicStandard.TwoHS

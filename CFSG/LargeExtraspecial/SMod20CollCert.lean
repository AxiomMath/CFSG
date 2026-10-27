
module


public import Certificates.Certificate21264

public section

namespace CFSG.LargeExtraspecial.SMod20

open CFSG.Fischer CFSG.SmithE CFSG.F4.Native CFSG.Fischer.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native

theorem collCheck_holds : chkColl () = true :=
  Certificates.certificate21264

theorem collFacts : CollFacts := by
  have h := collCheck_holds
  unfold chkColl at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, fun k hk => (allIn_eq_true.1 h3) k (Nat.zero_le _) hk, h4, ?_⟩
  unfold collI
  exact h5

theorem collCon_eq {s : Array ℕ} (hs : collAdm s = true)
    (hinv : ∀ k < 21, s[s[k]!]! = k) :
    collCon (collMeet collS2) #[s[0]!, s[1]!, s[4]!, s[10]!, s[3]!] = s := by
  obtain ⟨hsz, -, -, -⟩ := collAdm_parts hs
  obtain ⟨i0, i1, i4, i10, i3, isz⟩ := collInit_get #[s[0]!, s[1]!, s[4]!, s[10]!, s[3]!]
  have hK : ∀ k ∈ collBase.toList, k < 21 ∧
      (collInit #[s[0]!, s[1]!, s[4]!, s[10]!, s[3]!])[k]! = s[k]! := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 4 ∨ k = 10 ∨ k = 3 := by
      simpa [collBase] using hk
    rcases hk' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by norm_num, i0⟩
    · exact ⟨by norm_num, i1⟩
    · exact ⟨by norm_num, i4⟩
    · exact ⟨by norm_num, i10⟩
    · exact ⟨by norm_num, i3⟩
  obtain ⟨H1, H2⟩ := foldl_collStep hs hinv collSteps collBase.toList _ collFacts.valid isz hK
  exact array_ext_getElem! H1 hsz fun k hk =>
    H2 k (List.contains_iff_mem.1 (collFacts.cover k hk))

theorem collFrame_adm {s : Array ℕ} (hs : collAdm s = true)
    (hinv : ∀ k < 21, s[s[k]!]! = k) : collFrame collS2 s[0]! s[1]! s[4]! s[10]! s[3]! = true := by
  obtain ⟨-, -, hinj, -⟩ := collAdm_parts hs
  have h := collFacts.frame
  unfold collFrame at h ⊢
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true'] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, -⟩, h8⟩, h9⟩ := h
  have nf : ∀ {z a b : ℕ}, z < 21 → a < 21 → b < 21 → collP collS2 z a b = false →
      collP collS2 s[z]! s[a]! s[b]! = false := fun hz ha hb h => by
    rw [Bool.eq_false_iff] at h ⊢
    exact fun h' => h ((collP_adm_iff hs hinv hz ha hb).1 h')
  refine ⟨⟨⟨⟨⟨⟨⟨⟨fun e => absurd (hinj 0 (by norm_num) 1 (by norm_num) e) (by norm_num),
    nf (by norm_num) (by norm_num) (by norm_num) h2⟩,
    nf (by norm_num) (by norm_num) (by norm_num) h3⟩,
    nf (by norm_num) (by norm_num) (by norm_num) h4⟩,
    nf (by norm_num) (by norm_num) (by norm_num) h5⟩,
    fun e => absurd (hinj 3 (by norm_num) 0 (by norm_num) e) (by norm_num)⟩,
    fun e => absurd (hinj 3 (by norm_num) 1 (by norm_num) e) (by norm_num)⟩,
    collOn_adm hs (by norm_num) (by norm_num) (by norm_num) h8⟩,
    nf (by norm_num) (by norm_num) (by norm_num) h9⟩

theorem mem_collI {s : Array ℕ} (hs : collAdm s = true)
    (hinv : collComp s s = collId) (hne : s ≠ collId) : s ∈ collI := by
  have hinv' := collComp_eq_collId.1 hinv
  obtain ⟨-, hlt, -, -⟩ := collAdm_parts hs
  unfold collI collInvs
  rw [List.mem_toArray, List.mem_filterMap]
  refine ⟨_, mem_collDom (hlt 0 (by norm_num)) (hlt 1 (by norm_num)) (hlt 4 (by norm_num))
    (hlt 10 (by norm_num)) (hlt 3 (by norm_num)) (collFrame_adm hs hinv'), ?_⟩
  have hb : (s != collId) = true := bne_iff_ne.2 hne
  simp only [collCon_eq hs hinv', hinv, hs, beq_self_eq_true, hb, Bool.and_self, ite_true]

theorem collBound_parts :
    (∀ i < collI.size, (List.range 512).countP (fun a => ((collFixTab collI)[i]!)[a]!) ≤ 64) ∧
      ∀ i < collI.size, ∀ j < collI.size, i ≠ j → ((collCommTab collI)[i]!)[j]! = true →
        (List.range 512).countP (fun a => ((collFixTab collI)[i]!)[a]! &&
          ((collFixTab collI)[j]!)[a]!) ≤ 16 ∧
        (List.range collI.size).countP (fun k => ((collCommTab collI)[i]!)[k]! &&
          ((collCommTab collI)[j]!)[k]!) ≤ 27 := by
  have h := collFacts.bound
  unfold collBoundOK at h
  rw [Bool.and_eq_true] at h
  refine ⟨fun i hi => of_decide_eq_true ((allIn_eq_true.1 h.1) i (Nat.zero_le _) hi),
    fun i hi j hj hij hc => ?_⟩
  have := (allIn_eq_true.1 ((allIn_eq_true.1 h.2) i (Nat.zero_le _) hi)) j (Nat.zero_le _) hj
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.and_eq_true,
    decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · exact absurd h1 hij
  · rw [hc] at h1
    exact absurd h1 (by decide)
  · exact h1

theorem card_fix_le {s : Array ℕ} (hs : s ∈ collI) :
    ((Finset.range 512).filter fun a => collAmat s a = a).card ≤ 64 := by
  obtain ⟨i, hi, rfl⟩ := exists_idx_collI hs
  have h := collBound_parts.1 i hi
  rw [countP_range_eq_card] at h
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun a ha => ?_))) h
  rw [collFixTab_get hi (Finset.mem_range.1 ha), beq_iff_eq]

theorem card_fix₂_le {s t : Array ℕ} (hs : s ∈ collI)
    (ht : t ∈ collI) (hst : s ≠ t) (hc : collComp s t = collComp t s) :
    ((Finset.range 512).filter fun a => collAmat s a = a ∧ collAmat t a = a).card ≤ 16 := by
  obtain ⟨i, hi, rfl⟩ := exists_idx_collI hs
  obtain ⟨j, hj, rfl⟩ := exists_idx_collI ht
  have h := (collBound_parts.2 i hi j hj (fun e => hst (by rw [e]))
    (by rw [collCommTab_get hi hj, hc, beq_self_eq_true])).1
  rw [countP_range_eq_card] at h
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun a ha => ?_))) h
  rw [Bool.and_eq_true, collFixTab_get hi (Finset.mem_range.1 ha),
    collFixTab_get hj (Finset.mem_range.1 ha), beq_iff_eq, beq_iff_eq]

theorem card_comm_le {s t : Array ℕ} (hs : s ∈ collI)
    (ht : t ∈ collI) (hst : s ≠ t) (hc : collComp s t = collComp t s) :
    ((Finset.range collI.size).filter fun k =>
      collComp s collI[k]! = collComp collI[k]! s ∧
        collComp t collI[k]! = collComp collI[k]! t).card ≤ 27 := by
  obtain ⟨i, hi, rfl⟩ := exists_idx_collI hs
  obtain ⟨j, hj, rfl⟩ := exists_idx_collI ht
  have h := (collBound_parts.2 i hi j hj (fun e => hst (by rw [e]))
    (by rw [collCommTab_get hi hj, hc, beq_self_eq_true])).2
  rw [countP_range_eq_card] at h
  refine le_trans (le_of_eq (congrArg Finset.card (Finset.filter_congr fun k hk => ?_))) h
  rw [Bool.and_eq_true, collCommTab_get hi (Finset.mem_range.1 hk),
    collCommTab_get hj (Finset.mem_range.1 hk), beq_iff_eq, beq_iff_eq]

end CFSG.LargeExtraspecial.SMod20

module

public import Certificates.Certificate38840
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.GF2Type.SmithTypeE.E8

open CFSG.SmithE8M CFSG.Blueprint.Chevalley

theorem card_le_length_of_forall_mem {S : Finset ℕ} {P : List ℕ} (h : ∀ s ∈ S, s ∈ P) :
    S.card ≤ P.length :=
  (Finset.card_le_card (fun s hs => List.mem_toFinset.mpr (h s hs))).trans
    (List.toFinset_card_le P)

theorem e8mNoIndep_sound (cf : ℕ → ℕ → Bool) :
    ∀ (fuel : ℕ) (P : List ℕ) (k : ℕ), e8mNoIndep cf fuel P k = true →
      ∀ S : Finset ℕ, (∀ s ∈ S, s ∈ P) → (∀ a ∈ S, ∀ b ∈ S, a ≠ b → cf a b = false) →
        S.card < k := by
  intro fuel
  induction fuel with
  | zero =>
    intro P k h
    simp [e8mNoIndep] at h
  | succ n ih =>
    intro P k h S hSP hSi
    unfold e8mNoIndep at h
    by_cases hk : k = 0
    · simp [hk] at h
    by_cases hP : P.length < k
    · exact lt_of_le_of_lt (card_le_length_of_forall_mem hSP) hP
    by_cases hd : (e8mPick cf P).2 = 0
    · simp [hk, hP, hd] at h
    rw [if_neg hk, if_neg hP, if_neg hd, Bool.and_eq_true] at h
    obtain ⟨hA, hB⟩ := h
    obtain ⟨v, hv⟩ : ∃ v, v = (e8mPick cf P).1 := ⟨_, rfl⟩
    rw [← hv] at hA hB
    by_cases hvS : v ∈ S
    · have hS' : (S.erase v).card < k - 1 := by
        refine ih _ (k - 1) hB (S.erase v) (fun s hs => ?_) (fun a ha b hb hab =>
          hSi a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
        have hsS := Finset.mem_of_mem_erase hs
        have hsv : s ≠ v := Finset.ne_of_mem_erase hs
        have hcf : cf v s = false := hSi v hvS s hsS (Ne.symm hsv)
        rw [List.mem_filter]
        exact ⟨hSP s hsS, by simp [hsv, hcf]⟩
      have := Finset.card_erase_of_mem hvS
      have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨v, hvS⟩
      omega
    · refine ih _ k hA S (fun s hs => ?_) hSi
      have hsv : s ≠ v := fun h' => hvS (h' ▸ hs)
      exact (List.mem_erase_of_ne hsv).mpr (hSP s hs)

theorem e8mConfA_iff {A : Array (Fin (Tag.rank .E7) → ℤ)} (hA : ∀ k < 126, A[k]! = e8mRoot k)
    {a b : ℕ} (ha : a < 126) (hb : b < 126) :
    e8mConfA A a b = true ↔ ∃ m < 126, e8mRoot m = fun i => e8mRoot a i + e8mRoot b i := by
  unfold e8mConfA
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [← hA m hm, h, hA a ha, hA b hb]
  · rintro ⟨m, hm, h⟩
    refine ⟨m, hm, ?_⟩
    rw [hA m hm, h, hA a ha, hA b hb]


theorem tabCheck_holds : e8mTabOK () = true :=
  Certificates.certificate38840.1

theorem raCheck_holds : e8mRACheck () = true :=
  Certificates.certificate38840.2.1

theorem abelCheck_holds : e8mAbelCheck () = true :=
  Certificates.certificate38840.2.2

theorem tab_facts :
    (∀ k < 126, (e8mRootArr ())[k]! = e8mRoot k) ∧
      ∀ a < 126, ∀ b < 126,
        e8mCf (e8mConfTab (e8mRootArr ())) a b = e8mConfA (e8mRootArr ()) a b := by
  have h := tabCheck_holds
  unfold e8mTabOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h

theorem e8mRoot_isRoot {k : ℕ} (hk : k < 126) : IsRoot .E7 (e8mRoot k) := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  exact RootCertificate.isRoot_root (Tag.rootCertificate_check .E7) k (by omega)

theorem exists_e8mRoot_eq {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) :
    ∃ k < 126, e8mRoot k = α := by
  have hlen : (Tag.rootCertificate .E7).roots.length = 126 := Tag.rootCertificate_length .E7
  obtain ⟨k, hk, hkα⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E7) hα
  exact ⟨k, by omega, hkα⟩

theorem e8m_abelian27_idx (T : Finset ℕ)
    (hT : ∀ k ∈ T, k < 126 ∧ 0 < height (e8mRoot k))
    (hab : ∀ a ∈ T, ∀ b ∈ T, ¬ IsRoot .E7 (fun i => e8mRoot a i + e8mRoot b i)) :
    T.card ≤ 27 ∧ (T.card = 27 → ∀ k ∈ T, e8mRoot k ⟨6, by decide⟩ = 1) := by
  obtain ⟨hA, hTab⟩ := tab_facts
  have hAbel := abelCheck_holds
  unfold e8mAbelCheck at hAbel
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, Bool.not_eq_true',
    and_imp] at hAbel
  obtain ⟨h28, h26⟩ := hAbel
  have hTP : ∀ s ∈ T, s ∈ e8mPos () := fun s hs => by
    unfold e8mPos
    rw [List.mem_filter]
    exact ⟨List.mem_range.mpr (hT s hs).1, by simpa [e8mIsPos] using (hT s hs).2⟩
  have hTi : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → e8mCf (e8mConfTab (e8mRootArr ())) a b = false := by
    intro a ha b hb _
    rw [hTab a (hT a ha).1 b (hT b hb).1]
    by_contra hc
    obtain ⟨m, hm, hmab⟩ := (e8mConfA_iff hA (hT a ha).1 (hT b hb).1).mp (by simpa using hc)
    exact hab a ha b hb (hmab ▸ e8mRoot_isRoot hm)
  have hlt : T.card < 28 := e8mNoIndep_sound _ 1000 _ 28 h28 T hTP hTi
  refine ⟨by omega, fun hc k hk => ?_⟩
  by_contra hRA
  have hnRA : e8mIsRA k = false := by simpa [e8mIsRA] using hRA
  have hk26 := h26 k (hTP k hk) (by simpa using hnRA)
  have hsub := e8mNoIndep_sound _ 1000 _ 26 hk26 (T.erase k) (fun s hs => by
      have hsT := Finset.mem_of_mem_erase hs
      have hsk : s ≠ k := Finset.ne_of_mem_erase hs
      rw [List.mem_filter]
      refine ⟨hTP s hsT, ?_⟩
      have hcf : e8mCf (e8mConfTab (e8mRootArr ())) k s = false := hTi k hk s hsT (Ne.symm hsk)
      simp [hsk, hcf])
    (fun a ha b hb hab => hTi a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab)
  have := Finset.card_erase_of_mem hk
  omega

theorem e8m_abelian27 (S : Finset (Fin (Tag.rank .E7) → ℤ))
    (hS : ∀ α ∈ S, IsRoot .E7 α ∧ 0 < height α)
    (hab : ∀ α ∈ S, ∀ β ∈ S, ¬ IsRoot .E7 (α + β)) :
    S.card ≤ 27 ∧ (S.card = 27 → ∀ α ∈ S, α ⟨6, by decide⟩ = 1) := by
  classical
  set T : Finset ℕ := (Finset.range 126).filter fun k => e8mRoot k ∈ S with hTdef
  have hTmem : ∀ k, k ∈ T ↔ k < 126 ∧ e8mRoot k ∈ S := fun k => by
    rw [hTdef, Finset.mem_filter, Finset.mem_range]
  have hsurj : Set.SurjOn e8mRoot (T : Set ℕ) (S : Set (Fin (Tag.rank .E7) → ℤ)) := by
    intro α hα
    obtain ⟨k, hk, hkα⟩ := exists_e8mRoot_eq (hS α hα).1
    exact ⟨k, (hTmem k).mpr ⟨hk, hkα ▸ hα⟩, hkα⟩
  have hST : S.card ≤ T.card := Finset.card_le_card_of_surjOn e8mRoot hsurj
  have hTrue := e8m_abelian27_idx T
    (fun k hk => ⟨((hTmem k).mp hk).1, (hS _ ((hTmem k).mp hk).2).2⟩)
    (fun a ha b hb => hab _ ((hTmem a).mp ha).2 _ ((hTmem b).mp hb).2)
  refine ⟨hST.trans hTrue.1, fun hc α hα => ?_⟩
  obtain ⟨k, hk, hkα⟩ := exists_e8mRoot_eq (hS α hα).1
  have hkT : k ∈ T := (hTmem k).mpr ⟨hk, hkα ▸ hα⟩
  rw [← hkα]
  exact hTrue.2 (le_antisymm hTrue.1 (hc ▸ hST)) k hkT

theorem e8m_RA_facts :
    ∀ a < 126, e8mRoot a ⟨6, by decide⟩ = 1 → 0 < height (e8mRoot a) ∧
      ∀ b < 126, e8mRoot b ⟨6, by decide⟩ = 1 → e8mConfA (e8mRootArr ()) a b = false := by
  have h := raCheck_holds
  unfold e8mRACheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, List.mem_range, and_imp,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨-, hpos⟩, hconf⟩ := h
  intro a ha ha7
  refine ⟨?_, fun b hb hb7 => ?_⟩
  · simpa [e8mIsPos] using hpos a ha (by simpa [e8mIsRA] using ha7)
  · exact hconf a ha (by simpa [e8mIsRA] using ha7) b hb (by simpa [e8mIsRA] using hb7)

theorem e8m_RA_pos {α : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hα7 : α ⟨6, by decide⟩ = 1) : 0 < height α := by
  obtain ⟨a, ha, rfl⟩ := exists_e8mRoot_eq hα
  exact (e8m_RA_facts a ha hα7).1

theorem e8m_RA_abelian {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hα7 : α ⟨6, by decide⟩ = 1) (hβ : IsRoot .E7 β)
    (hβ7 : β ⟨6, by decide⟩ = 1) : ¬ IsRoot .E7 (α + β) := by
  obtain ⟨hA, -⟩ := tab_facts
  obtain ⟨a, ha, rfl⟩ := exists_e8mRoot_eq hα
  obtain ⟨b, hb, rfl⟩ := exists_e8mRoot_eq hβ
  intro hroot
  obtain ⟨m, hm, hmab⟩ := exists_e8mRoot_eq hroot
  have hc := (e8m_RA_facts a ha hα7).2 b hb hβ7
  have : e8mConfA (e8mRootArr ()) a b = true := (e8mConfA_iff hA ha hb).mpr ⟨m, hm, hmab⟩
  rw [hc] at this
  exact absurd this (by decide)

end CFSG.GF2Type.SmithTypeE.E8

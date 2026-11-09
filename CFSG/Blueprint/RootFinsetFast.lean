module

public import CFSG.Blueprint.ChevalleyRoots
public import CFSG.Permutation.FinPack

public section

namespace CFSG.Blueprint.Chevalley

open CFSG.Permutation.FinPack

theorem mem_rootFinset_iff_exists {τ : Tag} {v : Fin τ.rank → ℤ} :
    v ∈ rootFinset τ ↔ ∃ c ∈ τ.rootCertificate.roots, decodeVec c = v := by
  simp only [rootFinset, List.mem_toFinset, List.mem_map, List.mem_range, RootCertificate.root]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.getElem_mem hk, by rw [List.getD_eq_getElem _ _ hk]⟩
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
    exact ⟨k, hk, by rw [List.getD_eq_getElem _ _ hk]⟩

theorem forall_mem_rootFinset_iff {τ : Tag} {P : (Fin τ.rank → ℤ) → Prop} :
    (∀ γ ∈ rootFinset τ, P γ) ↔ ∀ c ∈ τ.rootCertificate.roots, P (decodeVec c) := by
  constructor
  · exact fun h c hc => h _ (mem_rootFinset_iff_exists.2 ⟨c, hc, rfl⟩)
  · intro h γ hγ
    obtain ⟨c, hc, rfl⟩ := mem_rootFinset_iff_exists.1 hγ
    exact h c hc

@[expose] noncomputable def rootCodeV {τ : Tag} (v : Fin τ.rank → ℤ) : ℕ :=
  encF (fun i => if h : i < τ.rank then (v ⟨i, h⟩ + 8).toNat else 0) τ.rank

@[expose] noncomputable def inRangeV {τ : Tag} (v : Fin τ.rank → ℤ) : Bool :=
  (List.finRange τ.rank).all fun i => decide (-8 ≤ v i) && decide (v i ≤ 7)

@[expose] noncomputable def rootsCanon (τ : Tag) : Bool :=
  τ.rootCertificate.roots.all fun c => Nat.beq (encF (rd c) τ.rank) c

@[expose] noncomputable def rootMemK {τ : Tag} (v : Fin τ.rank → ℤ) : Bool :=
  inRangeV v && memK (rootCodeV v) τ.rootCertificate.roots

theorem rootCodeV_decodeVec {τ : Tag} (c : ℕ) :
    rootCodeV (decodeVec (τ := τ) c) = encF (rd c) τ.rank := by
  unfold rootCodeV
  refine encF_congr fun i hi => ?_
  rw [dif_pos hi, rd_eq]
  simp only [decodeVec, sub_add_cancel, Int.toNat_natCast]

theorem decodeVec_rootCodeV {τ : Tag} {v : Fin τ.rank → ℤ} (hv : inRangeV v = true) :
    decodeVec (rootCodeV v) = v := by
  simp only [inRangeV, List.all_eq_true, List.mem_finRange, true_implies, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  funext j
  have h16 : ∀ i < τ.rank, (if h : i < τ.rank then (v ⟨i, h⟩ + 8).toNat else 0) < 16 := by
    intro i hi
    rw [dif_pos hi]
    have := hv ⟨i, hi⟩
    omega
  have hd := rd_encF h16 j.isLt
  rw [rd_eq, dif_pos j.isLt] at hd
  simp only [decodeVec, rootCodeV]
  rw [hd]
  have := hv j
  simp only [Fin.eta]
  omega

theorem inRangeV_decodeVec {τ : Tag} (c : ℕ) : inRangeV (decodeVec (τ := τ) c) = true := by
  rw [inRangeV, List.all_eq_true]
  intro i _
  have hlt := Nat.mod_lt (c / 16 ^ (i : ℕ)) (show 16 > 0 by norm_num)
  have h1 : -8 ≤ decodeVec (τ := τ) c i := by
    simp only [decodeVec]; generalize c / 16 ^ (i : ℕ) % 16 = d at hlt ⊢; omega
  have h2 : decodeVec (τ := τ) c i ≤ 7 := by
    simp only [decodeVec]; generalize c / 16 ^ (i : ℕ) % 16 = d at hlt ⊢; omega
  simp only [h1, h2, decide_true, Bool.and_self]

theorem rootMemK_iff {τ : Tag} (hc : rootsCanon τ = true) (v : Fin τ.rank → ℤ) :
    rootMemK v = true ↔ v ∈ rootFinset τ := by
  rw [mem_rootFinset_iff_exists, rootMemK, Bool.and_eq_true, memK_iff]
  simp only [rootsCanon, List.all_eq_true, Nat.beq_eq] at hc
  constructor
  · rintro ⟨hr, hm⟩
    exact ⟨_, hm, decodeVec_rootCodeV hr⟩
  · rintro ⟨c, hcm, rfl⟩
    refine ⟨?_, ?_⟩
    · exact inRangeV_decodeVec c
    · rw [rootCodeV_decodeVec, hc c hcm]
      exact hcm

theorem decide_mem_rootFinset {τ : Tag} (hc : rootsCanon τ = true) (v : Fin τ.rank → ℤ) :
    decide (v ∈ rootFinset τ) = rootMemK v := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, rootMemK_iff hc]

theorem card_filter_rootFinset (τ : Tag) (p : (Fin τ.rank → ℤ) → Prop) [DecidablePred p] :
    ((rootFinset τ).filter p).card =
      τ.rootCertificate.roots.countP (fun c => decide (p (decodeVec c))) := by
  have hnd : ((List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root).Nodup := by
    have h := τ.rootCertificate_checkNodup
    simp only [RootCertificate.checkNodup, decide_eq_true_eq] at h
    exact List.Nodup.of_map (fun v => List.ofFn v) (by rw [List.map_map]; exact h)
  have hL : (List.range τ.rootCertificate.roots.length).map τ.rootCertificate.root =
      τ.rootCertificate.roots.map decodeVec := by
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range, RootCertificate.root]
    rw [List.getD_eq_getElem _ _ (by simpa using h1)]
  show Multiset.card (Multiset.filter p (List.toFinset _).val) = _
  rw [List.toFinset_val, hnd.dedup, Multiset.filter_coe, Multiset.coe_card, hL, List.filter_map,
    List.length_map, List.countP_eq_length_filter]
  rfl

theorem rootsCanon_F4 : rootsCanon .F4 = true := by decide +kernel

theorem rootsCanon_E6 : rootsCanon .E6 = true := by decide +kernel

theorem rootsCanon_E7 : rootsCanon .E7 = true := by decide +kernel

theorem rootsCanon_E8 : rootsCanon .E8 = true := by decide +kernel

end CFSG.Blueprint.Chevalley

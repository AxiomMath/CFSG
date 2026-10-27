
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowBase

public import Certificates.Certificate22203
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsLocalBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four Subgroup

theorem sylowParts : SylowParts := by
  have h := Certificates.certificate22203
  simp only [Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem tg_injective {k l : ℕ} (hk : k < 64) (hl : l < 64)
    (h : wordPerm (tg k) = wordPerm (tg l)) : k = l := by
  by_contra hne
  have ht : wordTab (tg k) = wordTab (tg l) := (tabRep_wordTab _).tab_eq (h ▸ tabRep_wordTab _)
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact coverParts.distinct l hl k h' ht.symm
  · exact coverParts.distinct k hk l h' ht

section Parts

theorem enumerates_U1 : Enumerates U1 (enumBFS 42 (wordTabs wU₁) 16).tabs.toList :=
  enumerates_wordClosure sylowParts.ok₁

theorem enumerates_U2 : Enumerates U2 (enumBFS 42 (wordTabs wU₂) 16).tabs.toList :=
  enumerates_wordClosure sylowParts.ok₂

theorem card_U1 : Nat.card U1 = 16 := by
  rw [enumerates_U1.card, Array.length_toList, sylowParts.size₁]

theorem card_U2 : Nat.card U2 = 16 := by
  rw [enumerates_U2.card, Array.length_toList, sylowParts.size₂]

theorem tg_mem_U1 {k : ℕ} (hk : k < 16) : wordPerm (tg k) ∈ U1 :=
  mem_of_found_enum enumerates_U1 (tabRep_tgT k) (sylowParts.mem₁ k hk)

theorem tg_mem_U2 {k : ℕ} (hk : k < 16) : wordPerm (tg (4 * k)) ∈ U2 :=
  mem_of_found_enum enumerates_U2 (tabRep_tgT (4 * k)) (sylowParts.mem₂ k hk)

theorem mem_U1_iff {t : Equiv.Perm (Fin 42)} : t ∈ U1 ↔ ∃ k < 16, wordPerm (tg k) = t := by
  constructor
  · intro ht
    let f : Fin 16 → U1 := fun k => ⟨wordPerm (tg k), tg_mem_U1 k.2⟩
    have hinj : Function.Injective f := fun a b hab =>
      Fin.ext (tg_injective (by omega) (by omega) (congrArg Subtype.val hab))
    have hbij := hinj.bijective_of_nat_card_le (by rw [card_U1, Nat.card_eq_fintype_card,
      Fintype.card_fin])
    obtain ⟨k, hk⟩ := hbij.2 ⟨t, ht⟩
    exact ⟨k, k.2, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact tg_mem_U1 hk

theorem mem_U2_iff {t : Equiv.Perm (Fin 42)} :
    t ∈ U2 ↔ ∃ k < 16, wordPerm (tg (4 * k)) = t := by
  constructor
  · intro ht
    let f : Fin 16 → U2 := fun k => ⟨wordPerm (tg (4 * k)), tg_mem_U2 k.2⟩
    have hinj : Function.Injective f := fun a b hab => by
      have := tg_injective (by omega) (by omega) (congrArg Subtype.val hab)
      exact Fin.ext (by omega)
    have hbij := hinj.bijective_of_nat_card_le (by rw [card_U2, Nat.card_eq_fintype_card,
      Fintype.card_fin])
    obtain ⟨k, hk⟩ := hbij.2 ⟨t, ht⟩
    exact ⟨k, k.2, congrArg Subtype.val hk⟩
  · rintro ⟨k, hk, rfl⟩
    exact tg_mem_U2 hk

theorem U1_le_T0 : U1 ≤ T0 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := mem_U1_iff.1 ht
  exact tg_mem_T0 k (by omega)

theorem U2_le_T0 : U2 ≤ T0 := fun t ht => by
  obtain ⟨k, hk, rfl⟩ := mem_U2_iff.1 ht
  exact tg_mem_T0 (4 * k) (by omega)

end Parts

section Parts2

theorem P1_le_normalizer_U1 : P1 ≤ normalizer (U1 : Set (Equiv.Perm (Fin 42))) :=
  le_normalizer_of_normalOK enumerates_U1 sylowParts.normal₁

theorem P2_le_normalizer_U2 : P2 ≤ normalizer (U2 : Set (Equiv.Perm (Fin 42))) :=
  le_normalizer_of_normalOK enumerates_U2 sylowParts.normal₂

theorem normalizer_T0_le
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S) (hn : ∀ t ∈ T0, s * t * s⁻¹ ∈ T0) : s ∈ B0 := by
  obtain ⟨i, hi, hrep⟩ := enumerates_S.exists_pos hs
  have h := sylowParts.normT0
  simp only [normT0OK, Bool.and_eq_true, allBelow_eq_true, Bool.or_eq_true,
    anyBelow_eq_true] at h
  obtain ⟨hinv, hcase⟩ := h.2 i hi
  rcases hcase with hf | ⟨j, hj, hnot⟩
  · exact mem_of_found_enum enumerates_B0 hrep hf
  · exfalso
    have hj' : j < wT₀.length := by rwa [size_wordTabs] at hj
    have hirep := tabRep_invTab_of_invOK hinv hrep
    have hc := hrep.conjTab (tabRep_wordTabs wT₀ hj') hirep
    exact not_mem_of_notInOK enumerates_T0 hnot hc
      (hn _ (subset_closure ⟨wT₀[j], List.getElem_mem hj', rfl⟩))

theorem mem_center_T0
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ T0) (hc : ∀ t' ∈ T0, t * t' = t' * t) :
    ∃ k ∈ [0, 4, 8, 12], wordPerm (tg k) = t := by
  obtain ⟨k, hk, rfl⟩ := exists_tg ht
  have h := sylowParts.center
  simp only [centerT0OK, allBelow_eq_true] at h
  have hk' := h k hk
  have hall : allBelow (wordTabs wT₀).size (fun j => comp 42 (tgT k) (wordTabs wT₀)[j]! ==
      comp 42 (wordTabs wT₀)[j]! (tgT k)) = true := by
    rw [allBelow_eq_true]
    intro j hj
    have hj' : j < wT₀.length := by rwa [size_wordTabs] at hj
    exact ((tabRep_tgT k).comp (tabRep_wordTabs wT₀ hj')).beq_iff
      ((tabRep_wordTabs wT₀ hj').comp (tabRep_tgT k)) |>.2
      (hc _ (subset_closure ⟨wT₀[j], List.getElem_mem hj', rfl⟩))
  rw [hall, Bool.true_beq] at hk'
  exact ⟨k, List.elem_iff.mp hk', rfl⟩

theorem T0_le_centralizer_tg {k : ℕ} (hk : k ∈ [0, 4, 8, 12]) :
    T0 ≤ centralizer ({wordPerm (tg k)} : Set (Equiv.Perm (Fin 42))) := by
  have hk64 : k < 64 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    omega
  have h := sylowParts.center
  simp only [centerT0OK, allBelow_eq_true] at h
  have hk' := h k hk64
  have hc : ([0, 4, 8, 12] : List ℕ).contains k = true := List.elem_iff.mpr hk
  rw [hc, beq_iff_eq, allBelow_eq_true] at hk'
  rw [T0, closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_wordSet_iff.1 hg
  have hj' : j < (wordTabs wT₀).size := by rw [size_wordTabs]; exact hj
  have hrep := tabRep_wordTabs wT₀ hj
  rw [← getElem!_pos wT₀ j hj] at hrep
  rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
  exact (((tabRep_tgT k).comp hrep).beq_iff (hrep.comp (tabRep_tgT k))).1 (hk' j hj') |>.symm

theorem tg4_mul_tg8 : wordPerm (tg 4) * wordPerm (tg 8) = wordPerm (tg 12) := by
  have h := sylowParts.prod
  simp only [prodOK, prodData, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    beq_iff_eq] at h
  exact (((tabRep_tgT 4).comp (tabRep_tgT 8)).eq_iff (tabRep_tgT 12)).1 h.1

end Parts2

end CFSG.ComponentClassification.GrSLit.L34Facts

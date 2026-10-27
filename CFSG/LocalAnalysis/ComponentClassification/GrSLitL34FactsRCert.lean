module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Cert
public import Certificates.Certificate22207
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsWords

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit

structure RCertParts : Prop where
  outSq : outSqOK enumR.tabs enumS.tabs = true
  field : centOK enumR.tabs r₂T (centS r₂T) = true
  graph : centOK enumR.tabs r₃T (centS r₃T) = true
  inner : innerOddOK enumR.tabs (centS r₁T) = true
  four : fourOK enumR.tabs = true

theorem rCertParts : RCertParts := by
  have h := Certificates.certificate22207
  simp only [rCertOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem tabRep_powTab {t : Tab} {g : Equiv.Perm (Fin 42)} (ht : TabRep t g) (n : ℕ) :
    TabRep (powTab t n) (g ^ n) := by
  induction n with
  | zero => exact TabRep.idTab
  | succ n ih => rw [pow_succ]; exact ih.comp ht

theorem commT_iff {t s : Tab} {g h : Equiv.Perm (Fin 42)} (ht : TabRep t g) (hs : TabRep s h) :
    commT t s = true ↔ g * h = h * g :=
  (ht.comp hs).beq_iff (hs.comp ht)

theorem exists_tabRep_topInv {s : Tab} {g : Equiv.Perm (Fin 42)} (hs : TabRep s g) (n : ℕ) :
    ∃ j : ℕ, TabRep (topInv s n) (g ^ 2 ^ j) := by
  induction n generalizing s g with
  | zero => exact ⟨0, by simpa [topInv] using hs⟩
  | succ n ih =>
    unfold topInv
    split_ifs
    · exact ⟨0, by simpa using hs⟩
    · obtain ⟨j, hj⟩ := ih (hs.comp hs)
      refine ⟨j + 1, ?_⟩
      rwa [pow_succ', pow_mul, pow_two]


theorem sq_mem_S_of_pow_two {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (h2 : g ^ 2 ^ 8 = 1) :
    g * g ∈ S := by
  obtain ⟨k, hk, hrep⟩ := enumerates_R.exists_pos hg
  have h := rCertParts.outSq
  simp only [outSqOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h k hk with h' | h'
  · have := ((tabRep_powTwoTab hrep 8).beq_iff TabRep.idTab).2 h2
    rw [this] at h'
    exact Bool.noConfusion h'
  · exact mem_of_found_enum enumerates_S (hrep.comp hrep) h'

theorem eq_of_centOK {r : Equiv.Perm (Fin 42)} {rT : Tab} (hr : TabRep rT r)
    (hok : centOK enumR.tabs rT (centS rT) = true) {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (hgr : g * r = r * g) (hgC : ∀ c ∈ centralizer {r} ⊓ S, g * c = c * g) : g = 1 ∨ g = r := by
  obtain ⟨k, hk, hrep⟩ := enumerates_R.exists_pos hg
  simp only [centOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff] at hok
  rcases hok k hk with (h' | h') | h' | h'
  · exact absurd ((commT_iff hrep hr).2 hgr) (by rw [h']; decide)
  · exfalso
    have hall : allBelow (centS rT).size (fun i => commT enumR.tabs[k]! (centS rT)[i]!) = true := by
      rw [allBelow_eq_true]
      intro i hi
      obtain ⟨c, hc, hrepc⟩ := (enumerates_cent hr).exists_elt hi
      exact (commT_iff hrep hrepc).2 (hgC c hc)
    rw [hall] at h'
    exact Bool.noConfusion h'
  · exact Or.inl ((hrep.beq_iff TabRep.idTab).1 h')
  · exact Or.inr ((hrep.beq_iff hr).1 h')

theorem eq_of_commute_C₂ {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (hgr : g * r₂ = r₂ * g)
    (hgC : ∀ c ∈ C₂, g * c = c * g) : g = 1 ∨ g = r₂ :=
  eq_of_centOK tabRep_r₂ rCertParts.field hg hgr hgC

theorem eq_of_commute_C₃ {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (hgr : g * r₃ = r₃ * g)
    (hgC : ∀ c ∈ C₃, g * c = c * g) : g = 1 ∨ g = r₃ :=
  eq_of_centOK tabRep_r₃ rCertParts.graph hg hgr hgC

theorem card_le_four_of_odd {g : Equiv.Perm (Fin 42)} (hg : g ∈ R)
    (hgr : g * r₁ = r₁ * g)
    (h945 : g ^ 945 = 1) (hg1 : g ≠ 1) {H : Subgroup (Equiv.Perm (Fin 42))} (hH : H ≤ C₁)
    (hc : ∀ h ∈ H, g * h = h * g) : Nat.card H ≤ 4 := by
  classical
  obtain ⟨k, hk, hrep⟩ := enumerates_R.exists_pos hg
  have h := rCertParts.inner
  simp only [innerOddOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_true_eq] at h
  have hcount :
      countBelow (centS r₁T).size (fun i => commT enumR.tabs[k]! (centS r₁T)[i]!) ≤ 4 := by
    rcases h k hk with ((h' | h') | h') | h'
    · exact absurd ((commT_iff hrep tabRep_r₁).2 hgr) (by rw [h']; decide)
    · exact absurd ((tabRep_powTab hrep 945).beq_iff TabRep.idTab |>.2 h945) (by rw [h']; decide)
    · simp only [Bool.not_eq_false'] at h'
      exact absurd ((hrep.beq_iff TabRep.idTab).1 h') hg1
    · exact h'
  rw [countBelow_eq] at hcount
  have hidx : ∀ x : H, ∃ i < (centS r₁T).size, TabRep (centS r₁T)[i]! (x : Equiv.Perm (Fin 42)) :=
    fun x => enumerates_C₁.exists_pos (hH x.2)
  choose f hf hfr using hidx
  have hinj : Function.Injective
      (fun x : H => (⟨f x, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hf x),
        (commT_iff hrep (hfr x)).2 (hc x x.2)⟩⟩ :
        ((Finset.range (centS r₁T).size).filter
          fun i => commT enumR.tabs[k]! (centS r₁T)[i]! = true))) := by
    intro x y hxy
    have h1 : f x = f y := congrArg Subtype.val hxy
    have h2 := hfr x
    rw [h1] at h2
    exact Subtype.ext ((hfr y).perm_eq h2).symm
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at this
  omega

theorem exists_four {u v : Equiv.Perm (Fin 42)} (hu : u ∈ R)
    (hv : v ∈ R)
    (hur : u * r₄ = r₄ * u) (hvr : v * r₄ = r₄ * v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u * v ≠ v * u) (h2 : (u * v) ^ 2 ^ 8 = 1) :
    ∃ j : ℕ, (u * v) ^ 2 ^ j * (u * v) ^ 2 ^ j = 1 ∧ (u * v) ^ 2 ^ j ≠ 1 ∧
      (u * v) ^ 2 ^ j * u = u * (u * v) ^ 2 ^ j ∧ (u * v) ^ 2 ^ j ≠ r₄ ∧
      (u * v) ^ 2 ^ j ≠ r₄ * u ∧ (u * v) ^ 2 ^ j ≠ u := by
  obtain ⟨k, hk, hrepu⟩ := enumerates_R.exists_pos hu
  obtain ⟨l, hl, hrepv⟩ := enumerates_R.exists_pos hv
  have hinv : ∀ {w : Equiv.Perm (Fin 42)} {m : ℕ}, m < enumR.tabs.size →
      TabRep enumR.tabs[m]! w → w * r₄ = r₄ * w → w * w = 1 → w ≠ 1 →
      ∃ i < (invs₄ enumR.tabs).size, TabRep (invs₄ enumR.tabs)[i]! w := by
    intro w m hm hrep hwr hw2 hw1
    have hmem : enumR.tabs[m]! ∈ (invs₄ enumR.tabs).toList := by
      rw [invs₄, Array.toList_filter, List.mem_filter]
      refine ⟨getElem!_mem hm, ?_⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨⟨(commT_iff hrep tabRep_r₄).2 hwr, ((hrep.comp hrep).beq_iff TabRep.idTab).2 hw2⟩,
        ?_⟩
      cases h : (enumR.tabs[m]! == idTab 42)
      · rfl
      · exact absurd ((hrep.beq_iff TabRep.idTab).1 h) hw1
    obtain ⟨i, hi, he⟩ := exists_getElem!_of_mem hmem
    exact ⟨i, hi, he ▸ hrep⟩
  obtain ⟨i, hi, hri⟩ := hinv hk hrepu hur hu2 hu1
  obtain ⟨j, hj, hrj⟩ := hinv hl hrepv hvr hv2 hv1
  have h := rCertParts.four
  simp only [fourOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
  obtain ⟨m, hm⟩ := exists_tabRep_topInv (hri.comp hrj) 8
  rcases h i hi j hj with (h' | h') | h'
  · exact absurd ((commT_iff hri hrj).1 h') huv
  · exact absurd (((tabRep_powTwoTab (hri.comp hrj) 8).beq_iff TabRep.idTab).2 h2)
      (by rw [h']; decide)
  · obtain ⟨⟨⟨⟨⟨h1, h2'⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h'
    refine ⟨m, ((hm.comp hm).beq_iff TabRep.idTab).1 h1, fun he => ?_, (commT_iff hm hri).1 h3,
      fun he => ?_, fun he => ?_, fun he => ?_⟩
    · exact absurd ((hm.beq_iff TabRep.idTab).2 he) (by rw [h2']; decide)
    · exact absurd ((hm.beq_iff tabRep_r₄).2 he) (by rw [h4]; decide)
    · exact absurd ((hm.beq_iff (tabRep_r₄.comp hri)).2 he) (by rw [h5]; decide)
    · exact absurd ((hm.beq_iff hri).2 he) (by rw [h6]; decide)

end CFSG.ComponentClassification.GrSLit.L34Facts

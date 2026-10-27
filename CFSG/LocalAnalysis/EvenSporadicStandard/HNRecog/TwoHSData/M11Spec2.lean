module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.M11Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeVSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem m11K_eq_closure :
    m11K = closure ({elemW y0Word, elemW vWord} : Set (Equiv.Perm (Fin 1408))) := by
  unfold m11K
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨y0Word, Or.inl rfl, rfl⟩
    · exact ⟨vWord, Or.inr rfl, rfl⟩

theorem m11GroupOK_spec (h : m11GroupOK (subgroupList invCap [y0Word, vWord]) = true) :
    gensOK = true ∧ Nat.card ↥m11K = 7920 ∧
      IsEnumSet 1408 (subgroupList invCap [y0Word, vWord])
        (m11K : Set (Equiv.Perm (Fin 1408))) ∧
      orderOf (elemW y0Word) = 11 ∧ orderOf (elemW vWord) = 11 ∧
      elemW y0Word * elemW vWord ≠ elemW vWord * elemW y0Word ∧
      (∀ w ∈ m11Relators, CFSG.Sporadic.Bridge.wordProd (fun i => if i = 0 then elemW y0Word else
        if i = 1 then elemW vWord else 1) w = 1) ∧
      (∀ g ∈ m11K, TwoHSData.M11Order (orderOf g)) ∧
      orderOf (elemW i0Word) = 2 ∧ elemW i0Word ∈ m11K ∧
      closure ({elemW y0Word, elemW i0Word} : Set (Equiv.Perm (Fin 1408))) = m11K := by
  simp only [m11GroupOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hpy⟩, hpv⟩, hnc⟩, hiy⟩, hiv⟩, hrel⟩, hord⟩, hwi⟩, hp2⟩, hmem⟩, h2⟩ := h
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hg, hws⟩ := enumW_gens_words h1
  obtain ⟨hcard, hL0⟩ := enumW_spec h1
  have hwy : wordOK y0Word = true := List.all_eq_true.1 hws y0Word (by simp)
  have hwv : wordOK vWord = true := List.all_eq_true.1 hws vWord (by simp)
  have hry : Rep 1408 (tabW y0Word) (elemW y0Word) := rep_elemW_of_gensOK hg hwy
  have hrv : Rep 1408 (tabW vWord) (elemW vWord) := rep_elemW_of_gensOK hg hwv
  have hri : Rep 1408 (tabW i0Word) (elemW i0Word) := rep_elemW_of_gensOK hg hwi
  have hid : Rep 1408 (idT 1408) (1 : Equiv.Perm (Fin 1408)) := Rep.idT (by norm_num)
  have hiy' := Rep.inv_of_invOK hry hiy
  have hiv' := Rep.inv_of_invOK hrv hiv
  have hi0K : elemW i0Word ∈ m11K :=
    (hL0.memT_iff hri).1 (List.all_eq_true.1 hmem i0Word (by simp))
  obtain ⟨hcard2, -⟩ := enumW_spec h2
  have hcardK : Nat.card ↥m11K = 7920 := hcard
  haveI : Finite ↥m11K := Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  refine ⟨hg, hcard, hL0, orderOf_eq_of_primeOrderOK hry hpy, orderOf_eq_of_primeOrderOK hrv hpv,
    fun hcon => ?_, fun w hw => ?_, (ordAllOK_iff hid hL0).1 hord,
    orderOf_eq_of_primeOrderOK hri hp2, hi0K, ?_⟩
  · have := (commTT_iff hry hrv).2 hcon
    rw [this] at hnc
    exact absurd hnc (by decide)
  · exact (tblEq_iff_eq (rep_relTab hry hrv hiy' hiv' w) hid).1
      (List.all_eq_true.1 hrel w hw)
  · have hle : closure (elemW '' {w | w ∈ [y0Word, i0Word]}) ≤ m11K := by
      rw [closure_le]
      rintro _ ⟨w, hw, rfl⟩
      simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact subset_closure ⟨y0Word, by simp, rfl⟩
      · exact hi0K
    have heq : closure (elemW '' {w | w ∈ [y0Word, i0Word]}) = m11K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2, hcardK])
    rw [← heq]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨y0Word, Or.inl rfl, rfl⟩
      · exact ⟨i0Word, Or.inr rfl, rfl⟩
    · rintro ⟨w, (rfl | rfl), rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl

theorem m11ClassesOK_spec (hg : gensOK = true) {L0 : Array Table}
    (hL0 : IsEnumSet 1408 L0 (m11K : Set (Equiv.Perm (Fin 1408))))
    {Sz Saz : Set (Equiv.Perm (Fin 1408))}
    (hLz : IsEnumSet 1408 (classList invCap classz.rep) Sz)
    (hLaz : IsEnumSet 1408 (classList invCap classaz.rep) Saz) (h : m11ClassesOK L0 = true) :
    elemW n1Word * elemW y0Word * (elemW n1Word)⁻¹ = elemW y0Word ^ 7 ∧
      (∀ g ∈ Sz, m11Prop g) ∧ ∀ g ∈ Saz, m11Prop g := by
  simp only [m11ClassesOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨hwn, hinv⟩ := conjEqOK_parts h1
  have hry : Rep 1408 (tabW y0Word) (elemW y0Word) := rep_elemW_of_gensOK hg (by decide)
  have hrn : Rep 1408 (tabW n1Word) (elemW n1Word) := rep_elemW_of_gensOK hg hwn
  have hrni := Rep.inv_of_invOK hrn hinv
  have hid : Rep 1408 (idT 1408) (1 : Equiv.Perm (Fin 1408)) := Rep.idT (by norm_num)
  obtain ⟨hsz, hys⟩ := rep_powsT hry
  exact ⟨conjEqOK_spec hg hry (Rep.powT (by norm_num) hry 7) h1,
    (m11ClassOK_iff hid hrn hrni hys hsz hL0 hLz).1 h2,
    (m11ClassOK_iff hid hrn hrni hys hsz hL0 hLaz).1 h3⟩

theorem m11FiveOK_spec (hg : gensOK = true) {L0 : Array Table}
    (hL0 : IsEnumSet 1408 L0 (m11K : Set (Equiv.Perm (Fin 1408)))) (h : m11FiveOK L0 = true) :
    orderOf (elemW rho0Word) = 5 ∧ elemW rho0Word ∈ m11K ∧
      (∀ k : ℕ, 0 < k → k < 5 → ∃ c ∈ m11K, c * elemW rho0Word * c⁻¹ = elemW rho0Word ^ k) ∧
      elemW cBWord * elemW rho0Word * (elemW cBWord)⁻¹ = elemW fix5B.rep := by
  simp only [m11FiveOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hB, h5⟩, hin⟩, h2⟩, h3⟩, h4⟩, hcB⟩ := h
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrr : Rep 1408 (tabW rho0Word) (elemW rho0Word) := rep_elemW_of_gensOK hg (by decide)
  have hrB : Rep 1408 (tabW fix5B.rep) (elemW fix5B.rep) := rep_elemW_of_gensOK hg hB
  have hmem : ∀ w ∈ [rho0Word, ck2Word, ck3Word, ck4Word], elemW w ∈ m11K := by
    intro w hw
    have hwo : wordOK w = true := by
      have hw' := hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl | rfl | rfl <;> decide
    exact (hL0.memT_iff (rep_elemW_of_gensOK hg hwo)).1 (List.all_eq_true.1 hin w hw)
  refine ⟨orderOf_eq_of_primeOrderOK hrr h5, hmem _ (by simp), ?_,
    conjEqOK_spec hg hrr hrB hcB⟩
  intro k hk0 hk5
  interval_cases k
  · exact ⟨1, one_mem _, by simp⟩
  · exact ⟨elemW ck2Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 2) h2⟩
  · exact ⟨elemW ck3Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 3) h3⟩
  · exact ⟨elemW ck4Word, hmem _ (by simp),
      conjEqOK_spec hg hrr (Rep.powT (by norm_num) hrr 4) h4⟩

end CFSG.EvenSporadicStandard.HNRecog

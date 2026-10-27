module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversCycle
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Schreier.M23
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversBasic
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM11
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversCycle
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23DataInputs
public import Certificates.Certificate4086
public import Certificates.Certificate9214
public meta import CFSG.Sporadic.Bridge.M11CheckInputs

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers

open CFSG.Sporadic.Schreier CFSG.Blueprint TauCeti
open scoped Pointwise

@[expose] def m23RL : List (List (ℕ × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true), (1, true)],
   (List.replicate 23 [(0, true), (1, true)]).flatten,
   (List.replicate 6 [(0, true), (1, true), (1, true)]).flatten,
   (List.replicate 6 [(0, false), (1, false), (0, true), (1, true)]).flatten,
   (List.replicate 4 [(0, true), (1, true), (0, true), (1, false), (0, true), (1, true),
     (1, true)]).flatten,
   [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false),
     (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true),
     (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true),
     (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, false)],
   (List.replicate 6 [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
     (1, true)]).flatten,
   [(0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true),
     (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true),
     (1, true), (1, true), (0, true), (1, false), (0, true), (1, true), (1, true), (0, true),
     (1, false), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true),
     (0, true), (1, false), (0, true), (1, true), (1, true)]]


theorem m23_relatorLetters_aux : Sporadic.m23Presentation.relatorLetters = m23RL := by
  rw [GroupPresentation.relatorLetters_def, GroupPresentation.relators_def]
  simp [Sporadic.m23Presentation_transcribed, m23RL]
  decide

theorem m23R_map : m23R.map (List.map natLetter) = m23RL := by
  unfold m23R m23RL m23R1 m23R2 m23R3 m23R4 m23R5 m23R6 m23R7 m23R8 m23R9 natLetter
  decide

theorem m23_relatorLetters :
    Sporadic.m23Presentation.relatorLetters = m23R.map (List.map natLetter) := by
  rw [m23R_map]
  exact m23_relatorLetters_aux

theorem gM_img (i : Fin 2) :
    CFSG.Sporadic.Bridge.TwoGen.img2 m23GenA m23GenB⁻¹ i.val = gM i := by
  fin_cases i <;> simp [CFSG.Sporadic.Bridge.TwoGen.img2, gM]

theorem m23_rel : ∀ w ∈ m23R, wordVal gM w = 1 := by
  intro w hw
  have h := CFSG.Sporadic.Bridge.M23.relators_eval (w.map natLetter)
    (by rw [m23_relatorLetters]; exact List.mem_map_of_mem hw)
  rwa [wordProd_map_natLetter _ gM gM_img] at h

theorem m23_rel_i (i : Fin 9) : wordVal gM (m23Rw i) = 1 := by
  apply m23_rel
  unfold m23Rw
  have : i.val < m23R.length := by simp [m23R]
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem this

theorem closure_gM : Subgroup.closure (Set.range gM) = ⊤ := by
  have h := CFSG.Sporadic.Bridge.M23.closure_gen
  have : Set.range gM = {m23GenA, m23GenB⁻¹} := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [this]
  exact h

theorem yM_rel1 : wordVal yM m11R1 = 1 :=
  Certificates.certificate4086.1

theorem yM_rel2 : wordVal yM m11R2 = 1 :=
  Certificates.certificate4086.2.1

theorem yM_ne_one : yM 0 ≠ 1 :=
  Certificates.certificate4086.2.2.1

theorem alphaG_fix : alphaG • D23 = D23 :=
  Certificates.certificate4086.2.2.2.1

theorem betaG_fix : betaG • D23 = D23 :=
  Certificates.certificate4086.2.2.2.2.1

theorem mem_bfs_orbit : ∀ (n : ℕ) (s : Finset (Fin 23)), s ∈ bfs n → InOrbit M23g D23 s := by
  intro n
  induction n with
  | zero =>
    intro s hs
    simp only [bfs, Function.iterate_zero, id_eq, Finset.mem_singleton] at hs
    subst hs
    exact ⟨1, one_smul _ _⟩
  | succ n ih =>
    intro s hs
    rw [bfs, Function.iterate_succ_apply'] at hs
    simp only [vstep, Finset.mem_union, Finset.mem_image] at hs
    rcases hs with (hs | ⟨t, ht, rfl⟩) | ⟨t, ht, rfl⟩
    · exact ih s hs
    · exact (ih t ht).smul _
    · exact (ih t ht).smul _

theorem orbitCheck_eq : orbitCheck = true :=
  Certificates.certificate4086.2.2.2.2.2.1

theorem bfs_card : (bfs 22).card = 1288 := by
  have h := orbitCheck_eq
  unfold orbitCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem cellsIn_bfs : cellsIn (bfs 22) = true := by
  have h := orbitCheck_eq
  unfold orbitCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem cycKeys_even :
    (List.finRange 7).all (fun k => allEven (cycKeys k)) = true :=
  Certificates.certificate4086.2.2.2.2.2.2

theorem cyc_orbit (k : Fin 7) : ∀ c ∈ cycWords k, InOrbit M23g D23 c.1 := by
  intro c hc
  unfold cycWords at hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
  have h := cellsIn_bfs
  unfold cellsIn at h
  rw [List.all_eq_true] at h
  have h1 := h k (List.mem_finRange k)
  rw [List.all_eq_true] at h1
  have h2 := h1 p hp
  exact mem_bfs_orbit 22 _ (of_decide_eq_true h2)

theorem cyc_even (k : Fin 7) :
    ∀ e ∈ (cycWords k).flatMap (fun c => wordKeys gM c.2 c.1),
      Even (((cycWords k).flatMap (fun c => wordKeys gM c.2 c.1)).count e) := by
  have h := cycKeys_even
  rw [List.all_eq_true] at h
  have h1 := h k (List.mem_finRange k)
  unfold allEven at h1
  rw [List.all_eq_true] at h1
  intro e he
  exact of_decide_eq_true (h1 e he)

end CFSG.QuasithinUnique.Vol2Native.L239.Covers

module

public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Model
public meta import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.Model
public import CFSG.LocalAnalysis.EvenSmallLie.FFourTwo.NativeInputs
public import Certificates.Certificate3087

public section

namespace CFSG.EvenSmallLie.FFourTwo

theorem smallCheck_eq : smallCheck = true :=
  Certificates.certificate3087.1

theorem witCheck_eq : witCheck = true :=
  Certificates.certificate3087.2.1

theorem genCheck_eq : genCheck = true :=
  Certificates.certificate3087.2.2.1

theorem cenCheck_eq : cenCheck = true :=
  Certificates.certificate3087.2.2.2.1

theorem chainsCheck_eq : chainsCheck = true :=
  Certificates.certificate3087.2.2.2.2.1

theorem bigCheck_eq :
    (∀ c < 8, (Pc.preSq cmF 25 22).toList.countP (fun p => mulU p p == c * 2 ^ 22) =
        sqCounts.getD c 0) ∧
      ∃ d : ℕ → ℕ, ∀ p ∈ invCosets (Pc.preSq cmF 25 22), p ∈ compReps ∨
        ∃ m ∈ rMoves, mvOK m p = true ∧ mv m p % 2 ^ 22 ≠ 0 ∧ d (mv m p % 2 ^ 22) + 1 = d p :=
  Certificates.certificate3087.2.2.2.2.2

noncomputable def bfsD (p : ℕ) : ℕ :=
  Classical.choose bigCheck_eq.2 p

theorem sqCount_spec {c : ℕ} (hc : c < 8) :
    (Pc.preSq cmF 25 22).toList.countP (fun p => mulU p p == c * 2 ^ 22) =
      sqCounts.getD c 0 :=
  bigCheck_eq.1 c hc

theorem bfs_spec {p : ℕ} (hp : p ∈ invCosets (Pc.preSq cmF 25 22)) :
    p ∈ compReps ∨ ∃ m ∈ rMoves, mvOK m p = true ∧ mv m p % 2 ^ 22 ≠ 0 ∧
      bfsD (mv m p % 2 ^ 22) + 1 = bfsD p :=
  Classical.choose_spec bigCheck_eq.2 p hp

theorem chains_spec {c z : ℕ} (hc : c < 34) (hz : z < 8) :
    chainOK (compReps.getD c 0 + z * 2 ^ 22) (digits (chainData.getD (8 * c + z) "")) = true := by
  have h := chainsCheck_eq
  simp only [chainsCheck, List.all_eq_true, List.mem_range] at h
  exact h c hc z hz

theorem cen_spec : Pc.preCen cmF 25 25 =
    #[0, 2 ^ 24, 2 ^ 23, 2 ^ 23 + 2 ^ 24, 2 ^ 22,
    2 ^ 22 + 2 ^ 24, 2 ^ 22 + 2 ^ 23, 2 ^ 22 + 2 ^ 23 + 2 ^ 24] := by
  have h := cenCheck_eq
  simp only [cenCheck, beq_iff_eq] at h
  exact h

theorem wit_spec :
    witOK (2 ^ 22 + 2 ^ 23) [(3, 2), (21, 2), (4, 1), (17, 1)] = true ∧
    witOK (2 ^ 22 + 2 ^ 23 + 2 ^ 24) [(3, 2), (14, 2), (7, 1), (6, 2), (8, 1)] = true ∧
    witOK (2 ^ 17 + 2 ^ 20) [(5, 3), (8, 3), (5, 0), (12, 0)] = true ∧
    witOK (2 ^ 17 + 2 ^ 20 + 2 ^ 24) [(7, 3), (9, 3), (12, 0), (13, 0)] = true := by
  have h := witCheck_eq
  simp only [witCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem gen_spec :
    genOK (2 ^ 23) wordsL = true ∧ genOK (2 ^ 23 + 2 ^ 24) wordsL = true ∧
    genOK (2 ^ 22) wordsS = true ∧ genOK (2 ^ 22 + 2 ^ 24) wordsS = true := by
  have h := genCheck_eq
  simp only [genCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem small_spec :
    (weylU 1 (2 ^ 22) = 2 ^ 22 ∧ weylU 1 (2 ^ 23) = 2 ^ 23 ∧ weylU 2 (2 ^ 22) = 2 ^ 22 ∧
      weylU 2 (2 ^ 23) = 2 ^ 23) ∧
    (∀ i < 25, mulU (2 ^ 22) (2 ^ i) = mulU (2 ^ i) (2 ^ 22) ∧
      mulU (2 ^ 23) (2 ^ i) = mulU (2 ^ i) (2 ^ 23)) ∧
    (∀ c < 8, mulU (c * 2 ^ 22) (c * 2 ^ 22) = 0) ∧ mulU (3 * 2 ^ 22) (7 * 2 ^ 22) = 2 ^ 24 ∧
    Pc.mulList cmF 25 0 [1, 2, 8] = mulU (Pc.mulList cmF 25 0 [2, 1, 5]) (2 ^ 24) := by
  have h := smallCheck_eq
  simp only [smallCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, k⟩ := h
  exact ⟨⟨a, b, c, d⟩, e, f, g, k⟩

end CFSG.EvenSmallLie.FFourTwo

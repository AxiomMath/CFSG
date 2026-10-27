module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaListLiftsAlg
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaSound
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
public import CFSG.Sporadic.Bridge.J3Surj
public import CFSG.Sporadic.Presentation.McLExact
public import Certificates.Certificate9597
public import Certificates.Certificate9591

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding CFSG.AGLEmbedding.R3 CFSG.SectionRank CFSG.SectionRank.Native
  CFSG.RankThree.Asc83Table.Native CFSG.Blueprint CFSG.AGLEmbedding.R3.AlphaJ3
  CFSG.AGLEmbedding.R3.AlphaMcL

@[expose] def finWord (l : List ℕ) {k : ℕ} (h : ∀ n ∈ l, n < k := by decide) : List (Fin k) :=
  l.pmap (fun n hn => (⟨n, hn⟩ : Fin k)) h

section Generic

variable {M V : Type} [Inhabited M] {O : Ops M V} {p d : ℕ} {sA sB : String}

theorem hasLiftableTriple_of_modCheckE (Sp : OpsSpec O p d) {nregs : ℕ} {prog : List Op} {m : NMod}
    {tops : List Pc} {gs : List NGrp} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheckE O sA sB nregs prog 3 m tops gs cf ci ct = true)
    (v : Fin 3 → (Fin m.basis.length → ZMod 3))
    (hv : ∀ a b c : ZMod 3, a • v 0 + b • v 1 + c • v 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (winv : Fin 3 → List (Fin m.acts.length))
    (hinv : ∀ i, ((winv i).map fun j => actMatN 3 m.basis.length (m.acts.get j)).prod.mulVec
      (v i) = -v i)
    (wsw : Fin 3 → Fin 3 → List (Fin m.acts.length))
    (hsw : ∀ i j, i < j →
      ((wsw i j).map fun l => actMatN 3 m.basis.length (m.acts.get l)).prod.mulVec (v i) = v j ∧
      ((wsw i j).map fun l => actMatN 3 m.basis.length (m.acts.get l)).prod.mulVec (v j) = v i) :
    HasLiftableTriple (NativeSporadic.seedMonoid p d 1 sA sB)ˣ := by
  let C : MCert := ⟨nregs, prog, m.modFactsE 3 tops gs⟩
  have hCw : mcertCheck O sA sB C = true ∧ m.wf 3 = true := by
    revert h
    simp only [modCheckE, Bool.and_eq_true, decide_eq_true_eq]
    tauto
  obtain ⟨hC', hw⟩ := hCw
  have hf : ∀ f ∈ m.facts 3, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFactsE 3 tops gs
    simp only [NMod.modFactsE, List.mem_append]
    exact Or.inl (Or.inl hf)
  exact HasLiftableTriple.of_moduleSpec (NMod.spec Sp hC' m hf hw) v hv winv hinv wsw hsw

theorem hasLiftableTriple_of_modCheck (Sp : OpsSpec O p d) {nregs : ℕ} {prog : List Op} {m : NMod}
    {tops : List Pc} {tests : List NTest} {cf : ℕ → ℕ → ℕ → ℤ}
    {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ} {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : modCheck O sA sB nregs prog 3 m tops tests cf ci ct = true)
    (v : Fin 3 → (Fin m.basis.length → ZMod 3))
    (hv : ∀ a b c : ZMod 3, a • v 0 + b • v 1 + c • v 2 = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (winv : Fin 3 → List (Fin m.acts.length))
    (hinv : ∀ i, ((winv i).map fun j => actMatN 3 m.basis.length (m.acts.get j)).prod.mulVec
      (v i) = -v i)
    (wsw : Fin 3 → Fin 3 → List (Fin m.acts.length))
    (hsw : ∀ i j, i < j →
      ((wsw i j).map fun l => actMatN 3 m.basis.length (m.acts.get l)).prod.mulVec (v i) = v j ∧
      ((wsw i j).map fun l => actMatN 3 m.basis.length (m.acts.get l)).prod.mulVec (v j) = v i) :
    HasLiftableTriple (NativeSporadic.seedMonoid p d 1 sA sB)ˣ := by
  let C : MCert := ⟨nregs, prog, m.modFacts 3 tops tests⟩
  have hCw : mcertCheck O sA sB C = true ∧ m.wf 3 = true := by
    revert h
    simp only [modCheck, Bool.and_eq_true, decide_eq_true_eq]
    tauto
  obtain ⟨hC', hw⟩ := hCw
  have hf : ∀ f ∈ m.facts 3, f ∈ C.facts := by
    intro f hf
    show f ∈ m.modFacts 3 tops tests
    simp only [NMod.modFacts, List.mem_append]
    exact Or.inl (Or.inl hf)
  exact HasLiftableTriple.of_moduleSpec (NMod.spec Sp hC' m hf hw) v hv winv hinv wsw hsw

end Generic

theorem j3_hasLiftableTriple : HasLiftableTriple NativeSporadic.J3 :=
  hasLiftableTriple_of_modCheckE (spec2 80) Certificates.certificate9597
    (m := j3Mod) (v := ![![0, 0, 1], ![0, 1, 1], ![1, 2, 1]]) (by decide)
    (winv := ![finWord [1, 9], finWord [7, 9], finWord [9]]) (by decide)
    (wsw := ![![finWord [], finWord [5, 9, 9, 9, 9], finWord [8, 9, 9, 9, 9]],
      ![finWord [], finWord [], finWord [6, 9, 9, 9, 9]], ![finWord [], finWord [], finWord []]])
    (by decide)

theorem hasLiftableTriple_sporadic (s : TauCeti.SporadicName)
    (e : NativeSporadic.Carrier s ≃* s.Group) (h : HasLiftableTriple (NativeSporadic.Carrier s)) :
    HasLiftableTriple (TauCeti.CFSGIndex.sporadic s).Group :=
  HasLiftableTriple.of_mulEquiv e h

theorem hasLiftableTriple_J3 :
    HasLiftableTriple (TauCeti.CFSGIndex.sporadic .J3).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  exact hasLiftableTriple_sporadic .J3 e j3_hasLiftableTriple

theorem mcl_hasLiftableTriple :
    HasLiftableTriple NativeSporadic.McL :=
  hasLiftableTriple_of_modCheck (spec3 21) Certificates.certificate9591
    (m := mclMod) (v := ![![1, 0, 1, 0], ![1, 1, 0, 0], ![1, 1, 2, 0]]) (by decide)
    (winv := ![finWord [0, 2], finWord [2], finWord [3, 3]]) (by decide)
    (wsw := ![![finWord [], finWord [2, 1, 2], finWord [0, 2, 2]],
      ![finWord [], finWord [], finWord [1, 2, 2]], ![finWord [], finWord [], finWord []]])
    (by decide)

theorem hasLiftableTriple_McL :
    HasLiftableTriple (TauCeti.CFSGIndex.sporadic .McL).Group := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  exact hasLiftableTriple_sporadic .McL e mcl_hasLiftableTriple

end CFSG.LocalAnalysis.RankThreeTheoremC

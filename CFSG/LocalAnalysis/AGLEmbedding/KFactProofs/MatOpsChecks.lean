module

public import CFSG.RankThree.Asc83Table.MatOps
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TcGenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CoverPointDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.AlphaOrbDefs

public section

namespace CFSG.AGLEmbedding.R3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table CFSG.RankThree.Asc83Table.Native
  CFSG.Blueprint

variable {p d : ℕ} {sA sB : String} {n : ℕ} {prog : List Op}

theorem tcCheck_matOps {D : TSpec} (m : ℕ)
    (h₁ : 2 ≤ n ∧ prog.all (Op.lt n) = true ∧ D.wf = true ∧ D.rA < n ∧ D.rB < n ∧
      slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog D.rA =
        NativeSporadic.decode p d 1 sA ∧
      slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog D.rB =
        NativeSporadic.decode p d 1 sB ∧
      ∀ f ∈ D.facts.take m, f.Holds
        (slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog) n)
    (h₂ : ∀ f ∈ D.facts.drop m, f.Holds
      (slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog) n) :
    tcCheck (matOps p d) sA sB n prog D = true := by
  obtain ⟨hn, hp, hwf, hA, hB, eA, eB, hf⟩ := h₁
  have hc := mcertCheck_matOps (p := p) (d := d) (sA := sA) (sB := sB) (facts := D.facts) hn hp
    fun f hf' => by
      rw [← List.take_append_drop m D.facts, List.mem_append] at hf'
      exact hf'.elim (hf f) (h₂ f)
  unfold tcCheck
  rw [hc, eq_seed_matOps hp hA eA, eq_seed_matOps hp hB eB, hwf, decide_eq_true hA,
    decide_eq_true hB]
  rfl

theorem cpCheck_matOps {D : CpSpec}
    (h : 2 ≤ n ∧ prog.all (Op.lt n) = true ∧ D.wf = true ∧ D.rA < n ∧ D.rB < n ∧
      slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog D.rA =
        NativeSporadic.decode p d 1 sA ∧
      slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog D.rB =
        NativeSporadic.decode p d 1 sB ∧
      ∀ f ∈ D.facts, f.Holds
        (slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog) n) :
    cpCheck (matOps p d) sA sB n prog D = true := by
  obtain ⟨hn, hp, hwf, hA, hB, eA, eB, hf⟩ := h
  unfold cpCheck
  rw [mcertCheck_matOps hn hp hf, eq_seed_matOps hp hA eA, eq_seed_matOps hp hB eB, hwf,
    decide_eq_true hA, decide_eq_true hB]
  rfl

theorem modCheckV_matOps {q : ℕ} {m : NMod} {tops : List Pc} {tidx : List ℕ} {s : ℕ}
    {orb : List (ℕ × ℕ)} {cf : ℕ → ℕ → ℕ → ℤ} {ci : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ}
    {ct : ℕ → ℕ → ℕ → ℕ → ℤ}
    (h : 2 ≤ n ∧ prog.all (Op.lt n) = true ∧
      (∀ f ∈ m.modFactsW q tops, f.Holds
        (slpRegs (NativeSporadic.decode p d 1 sA) (NativeSporadic.decode p d 1 sB) prog) n) ∧
      m.wfO q orb = true ∧ pcWf (tops ++ m.basisPc q) = true ∧
      tops.all (fun g => m.acts.any (·.reg == g.reg)) = true ∧ m.wOK q tops tidx s = true ∧
      q ≤ m.basis.length ∧ m.funOK q cf = true ∧ m.altOK q ci ct tgtAlt = true) :
    modCheckV (matOps p d) sA sB n prog q m tops tidx s orb cf ci ct = true := by
  obtain ⟨hn, hp, hf, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold modCheckV
  rw [mcertCheck_matOps hn hp hf, h1, h2, h3, h4, decide_eq_true h5, h6, h7]
  rfl

end CFSG.AGLEmbedding.R3

end

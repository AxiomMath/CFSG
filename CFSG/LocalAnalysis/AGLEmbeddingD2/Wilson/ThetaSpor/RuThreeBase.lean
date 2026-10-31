
module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.RuThreeData
public import CFSG.Sporadic.Schreier.RuLocalFacts
public import CFSG.Assembly.Defs

@[expose] public section

namespace CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.Sporadic.RuSchreier CFSG.Certificates.Native CFSG.Certificates

section Stage1

noncomputable def ruXperm : Equiv.Perm (Fin 4060) := permOfArr 4060 ruX

theorem ruChainJoin_arrays :
    ChainArrays ruChainJoin ((ruField4060 3).extract 0 4) (ruField4060 3)
      (ruBaseArr 4060 ruJoinBase) (ruWordsArr 4 18 ruJoinDerivations) :=
  ruChain_arrays ruChainJoin_check.1

theorem ruChainJoin_sub_ruP :
    ruChainJoin.originalSubgroup = ruP := by
  rw [ruChainJoin_sub, ← ruP_eq_sup]

theorem mem_ruP_of_sift
    {t : Array ℕ} {g : Equiv.Perm (Fin 4060)} (ht : Rep 4060 t g)
    (h : siftA 4060 (rawLevels 4060 ruS ruBase) ruBase 0 t = true) : g ∈ ruP := by
  rw [← ruChainJoin_sub_ruP]
  exact (ruChain_sift ruChainJoin_check.1 ht).1 h

end Stage1

section Stage2

noncomputable def ruSylowSub : Subgroup (Equiv.Perm (Fin 4060)) :=
  Subgroup.closure (permsA 4060 ruSylGs)

end Stage2

section Stage3

def ruCAct (σ : Equiv.Perm (Fin 4060)) (n : ℕ) : ℕ :=
  if h : n < 4060 then (σ ⟨n, h⟩ : ℕ) else n

theorem ruCAct_eq (σ : Equiv.Perm (Fin 4060)) {n : ℕ} (hn : n < 4060) :
    ruCAct σ n = (σ ⟨n, hn⟩ : ℕ) := by
  simp [ruCAct, hn]

theorem rep_ruCAct {t : Array ℕ} {σ : Equiv.Perm (Fin 4060)} (h : Rep 4060 t σ) {n : ℕ}
    (hn : n < 4060) : t[n]! = ruCAct σ n := by
  rw [h.apply hn, ruCAct_eq σ hn]

theorem ruCAct_lt (σ : Equiv.Perm (Fin 4060)) {n : ℕ} (hn : n < 4060) : ruCAct σ n < 4060 := by
  rw [ruCAct_eq σ hn]
  exact (σ _).2

theorem ruCAct_mul (σ τ : Equiv.Perm (Fin 4060)) {n : ℕ} (hn : n < 4060) :
    ruCAct (σ * τ) n = ruCAct σ (ruCAct τ n) := by
  have h2 := ruCAct_lt τ hn
  rw [ruCAct_eq (σ * τ) hn, ruCAct_eq τ hn, ruCAct_eq σ (by rwa [ruCAct_eq τ hn] at h2)]
  rfl

theorem ruCAct_one (n : ℕ) : ruCAct 1 n = n := by
  unfold ruCAct
  split_ifs <;> rfl

theorem ruF_lt : ∀ x ∈ ruF, x < 4060 := by decide

theorem ruF_length : ruF.length = 10 := by decide

theorem ruF_idx_getElem : ∀ k < 10, ruF.idxOf ruF[k]! = k := by decide

theorem ruF_getElem_idx : ∀ q ∈ ruF, ruF[ruF.idxOf q]! = q := by decide

theorem ruF_idx_lt {q : ℕ} (hq : q ∈ ruF) : ruF.idxOf q < 10 := by
  have := List.idxOf_lt_length_iff.2 hq
  rwa [ruF_length] at this

end Stage3

section Stage4

def RuComm (σ : Equiv.Perm (Fin 4060)) : Prop := ruXperm * σ = σ * ruXperm

theorem ruCAct_comm_fixed {X σ : Equiv.Perm (Fin 4060)} (hσ : X * σ = σ * X) {p : ℕ}
    (hp : p < 4060) (hfix : ruCAct X p = p) : ruCAct X (ruCAct σ p) = ruCAct σ p := by
  have h := congrArg (fun f : Equiv.Perm (Fin 4060) => ((f ⟨p, hp⟩ : Fin 4060) : ℕ)) hσ
  simp only [Equiv.Perm.mul_apply] at h
  rw [ruCAct_eq X hp] at hfix
  have e : X ⟨p, hp⟩ = ⟨p, hp⟩ := Fin.ext hfix
  rw [e] at h
  rw [ruCAct_eq σ hp, ruCAct_eq X (σ ⟨p, hp⟩).2]
  exact h

def ruActNat (σ : Equiv.Perm (Fin 4060)) (k : ℕ) : ℕ := ruF.idxOf (ruCAct σ ruF[k]!)

theorem ruF_getElem_mem {k : ℕ} (hk : k < 10) : ruF[k]! ∈ ruF := by
  revert k; decide

theorem ruActNat_one {k : ℕ} (hk : k < 10) : ruActNat 1 k = k := by
  unfold ruActNat
  rw [ruCAct_one]
  exact ruF_idx_getElem k hk

end Stage4

section Stage5

theorem ruGs_mem_closure {k : ℕ} (hk : k < 2) :
    permOfArr 4060 ruGs[k]! ∈ Subgroup.closure (permsA 4060 ruGs) :=
  Subgroup.subset_closure (mem_permsA (by simpa [ruGs] using hk))

end Stage5

end CFSG.AGLEmbeddingD2.Wilson.ThetaSpor

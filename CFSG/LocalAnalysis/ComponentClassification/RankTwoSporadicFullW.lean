module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1Full
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCheckW

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.Cert

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

@[expose] def pairOKW (n : ℕ) (ps : List ℕ) (nodes : Array FNode) (x y : Array ℕ) : Bool :=
  enumOK n #[x, y] ps (maskCert n #[x, y]) && (List.range nodes.size).any fun k =>
    allLt nodes[k]!.basis.size fun j => memA n (maskCert n #[x, y]) nodes[k]!.basis[j]!

@[expose] def fCensusOKW (n : ℕ) (ps : List ℕ) (inX : Array ℕ → Bool)
    (xGens sGens : Array (Array ℕ)) (nodes : Array FNode) (cS : ArrCert) : Bool :=
  enumOK n sGens ps cS && (allLt xGens.size fun k => validA n xGens[k]!) &&
    (allLt nodes.size fun k => fullOK n inX xGens nodes[k]!) &&
    allLt cS.pts.size fun i => allLt cS.pts.size fun j =>
      !(eqA n (compA n cS.pts[i]! cS.pts[i]!) (idA n)) || eqA n cS.pts[i]! (idA n) ||
        eqA n cS.pts[j]! (idA n) || eqA n cS.pts[i]! cS.pts[j]! ||
        !(commA n cS.pts[i]! cS.pts[j]!) || pairOKW n ps nodes cS.pts[i]! cS.pts[j]!

section Soundness

variable {n : ℕ} {X : Subgroup (Equiv.Perm (Fin n))} {inX : Array ℕ → Bool}

theorem fWitness_of_fCensusOKW {ps : List ℕ} {xGens sGens : Array (Array ℕ)}
    {nodes : Array FNode} {cS : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (hin : ∀ a, validA n a = true → inX a = true → permOfArr n a ∈ X)
    (hX : X ≤ closure (permsA n xGens))
    (h : fCensusOKW n ps inX xGens sGens nodes cS = true)
    {E : Subgroup (Equiv.Perm (Fin n))} (hES : E ≤ closure (permsA n sGens))
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) : FWitness X E := by
  simp only [fCensusOKW, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hS, hxv⟩, hnodes⟩, hpairs⟩ := h
  obtain ⟨hSmem, -, hSval⟩ := enumOK_spec hps hS
  have hxv' : ∀ k < xGens.size, validA n xGens[k]! = true := fun k hk => allLt_spec hxv hk
  obtain ⟨x, hxE, y, hyE, hx1, hy1, hxy⟩ := exists_pair_of_four_le hE hE4
  obtain ⟨i, hi, rfl⟩ := (hSmem _).1 (hES hxE)
  obtain ⟨j, hj, rfl⟩ := (hSmem _).1 (hES hyE)
  have hri := rep_of_validA (hSval i hi)
  have hrj := rep_of_validA (hSval j hj)
  have hfalse : ∀ {a b : Array ℕ} {g h : Equiv.Perm (Fin n)}, Rep n a g → Rep n b h → g ≠ h →
      eqA n a b = false := by
    intro a b g h ha hb hgh
    by_contra hc
    exact hgh (eq_of_eqA ha hb (by simpa using hc))
  have h1 : eqA n (compA n cS.pts[i]! cS.pts[i]!) (idA n) = true := by
    rw [eqA_iff (rep_compA hri hri) rep_idA, ← sq]
    exact hE.2 _ hxE
  have h2 : commA n cS.pts[i]! cS.pts[j]! = true :=
    (commA_iff hri hrj).2 (congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hxE⟩ ⟨_, hyE⟩))
  have hp : pairOKW n ps nodes cS.pts[i]! cS.pts[j]! = true := by
    have hp := allLt_spec (allLt_spec hpairs hi) hj
    rw [h1, hfalse hri rep_idA hx1, hfalse hrj rep_idA hy1, hfalse hri hrj hxy, h2] at hp
    simpa using hp
  simp only [pairOKW, Bool.and_eq_true, List.any_eq_true, List.mem_range] at hp
  obtain ⟨hc, k, hk, hkb⟩ := hp
  have hnk := allLt_spec hnodes hk
  have hbv : ∀ l < nodes[k]!.basis.size, validA n nodes[k]!.basis[l]! = true := by
    have := hnk
    simp only [fullOK, Bool.and_eq_true] at this
    exact fun l hl => allLt_spec this.1.1.1 hl
  have hxyE : closure (permsA n #[cS.pts[i]!, cS.pts[j]!]) ≤ E := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl2 : l < 2 := hl
    interval_cases l
    · exact hxE
    · exact hyE
  have hkE : closure (permsA n nodes[k]!.basis) ≤ E := by
    refine le_trans ?_ hxyE
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact enumOK_mem_of_any hps hc (rep_of_validA (hbv l hl)) (allLt_spec hkb hl)
  exact hX.trans ((le_nE_of_fullOK hin hxv' hnk).trans (nE_mono X hkE))

end Soundness

end CFSG.ComponentClassification.RankTwoSporadic.Cert

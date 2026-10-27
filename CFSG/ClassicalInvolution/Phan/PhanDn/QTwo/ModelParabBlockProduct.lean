module

public import CFSG.ClassicalInvolution.Phan.Frames.BlockStab
public import CFSG.HardMathSupport.Cooperstein.Proving.PairSwapEvenSub

public section

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open CFSG.LieType.Steinberg

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

private noncomputable def qTwo_blockFactors {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k b : ι → ℕ) (hbk : ∀ a, b a + k a ≤ n)
    (u : ∀ a, Su K 2 1 (k a)) : ι → Su K 2 1 n :=
  fun a => blockEmb K 2 1 n (k a) (b a) (hbk a) (u a)

private theorem qTwo_blockFactors_comm {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k b : ι → ℕ) (hbk : ∀ a, b a + k a ≤ n)
    (hdisj : ∀ a c, a ≠ c → b a + k a ≤ b c ∨ b c + k c ≤ b a)
    (u : ∀ a, Su K 2 1 (k a)) :
    ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun Commute (qTwo_blockFactors (K := K) n k b hbk u)) := by
  intro a _ c _ hac
  exact blockEmb_comm (K := K) (p := 2) (f := 1) (m := n)
    (k := k a) (l := k c) (i := b a) (j := b c)
    (hbk a) (hbk c) (hdisj a c hac) (u a) (u c)

noncomputable def qTwo_blockProduct {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k b : ι → ℕ) (hbk : ∀ a, b a + k a ≤ n)
    (hdisj : ∀ a c, a ≠ c → b a + k a ≤ b c ∨ b c + k c ≤ b a)
    (u : ∀ a, Su K 2 1 (k a)) : Su K 2 1 n :=
  Finset.univ.noncommProd (qTwo_blockFactors (K := K) n k b hbk u)
    (qTwo_blockFactors_comm (K := K) n k b hbk hdisj u)

theorem qTwo_blockProduct_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k b : ι → ℕ) (hbk : ∀ a, b a + k a ≤ n)
    (hdisj : ∀ a c, a ≠ c → b a + k a ≤ b c ∨ b c + k c ≤ b a)
    (u : ∀ a, Su K 2 1 (k a))
    {G : Type} [Group G] (φ : Su K 2 1 n →* G) (H : Subgroup G)
    (h : ∀ a, φ (blockEmb K 2 1 n (k a) (b a) (hbk a) (u a)) ∈ H) :
    φ (qTwo_blockProduct n k b hbk hdisj u) ∈ H := by
  change qTwo_blockProduct n k b hbk hdisj u ∈ H.comap φ
  rw [qTwo_blockProduct]
  exact Subgroup.noncommProd_mem (H.comap φ)
    (qTwo_blockFactors_comm (K := K) n k b hbk hdisj u)
    (fun a _ => h a)

theorem qTwo_blockProduct_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (k b : ι → ℕ) (hbk : ∀ a, b a + k a ≤ n)
    (hdisj : ∀ a c, a ≠ c → b a + k a ≤ b c ∨ b c + k c ≤ b a)
    (u : ∀ a, Su K 2 1 (k a)) (a : ι) (j : Fin n)
    (hj : b a ≤ j.val ∧ j.val < b a + k a) :
    qTwo_blockProduct n k b hbk hdisj u •
        (Pi.single j (1 : K) : Fin n → K) =
      blockEmb K 2 1 n (k a) (b a) (hbk a) (u a) •
        (Pi.single j (1 : K) : Fin n → K) := by
  classical
  let F : ι → Su K 2 1 n := qTwo_blockFactors (K := K) n k b hbk u
  let hcommF := qTwo_blockFactors_comm (K := K) n k b hbk hdisj u
  let f : ι → Equiv.Perm (Fin n → K) :=
    fun c => MulAction.toPermHom (Su K 2 1 n) (Fin n → K) (F c)
  have hcommf : ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute f) := by
    intro c _ d _ hcd
    exact (hcommF (Finset.mem_univ c) (Finset.mem_univ d) hcd).map
      (MulAction.toPermHom (Su K 2 1 n) (Fin n → K))
  have hfix : ∀ c, c ≠ a → f c (Pi.single j (1 : K) : Fin n → K) =
      (Pi.single j (1 : K) : Fin n → K) := by
    intro c hc
    have hnot : ¬ (b c ≤ j.val ∧ j.val < b c + k c) := by
      rcases hdisj a c (Ne.symm hc) with hle | hle
      · omega
      · omega
    have hsingle := blockEmb_smul_single_of_not_mem (K := K) (p := 2) (f := 1) (m := n)
      (k := k c) (i := b c) (hbk c) (u c) (l := j) hnot
    simpa [f, F, qTwo_blockFactors, MulAction.toPermHom_apply] using hsingle
  have hsingle := CFSG.HardMathSupport.Cooperstein.Proving.noncommProd_univ_apply
    (f := f) hcommf a (Pi.single j (1 : K) : Fin n → K) hfix
  have hmap := Finset.map_noncommProd (s := (Finset.univ : Finset ι)) (f := F)
    (comm := hcommF) (g := MulAction.toPermHom (Su K 2 1 n) (Fin n → K))
  have hprod : (Finset.univ.noncommProd f hcommf) (Pi.single j (1 : K) : Fin n → K) =
      qTwo_blockProduct n k b hbk hdisj u • (Pi.single j (1 : K) : Fin n → K) := by
    have hfun := congrArg (fun e : Equiv.Perm (Fin n → K) =>
      e (Pi.single j (1 : K) : Fin n → K)) hmap
    simpa [qTwo_blockProduct, F, f, hcommF, MulAction.toPermHom_apply] using hfun.symm
  calc
    qTwo_blockProduct n k b hbk hdisj u • (Pi.single j (1 : K) : Fin n → K)
        = (Finset.univ.noncommProd f hcommf) (Pi.single j (1 : K) : Fin n → K) :=
          hprod.symm
    _ = f a (Pi.single j (1 : K) : Fin n → K) := hsingle
    _ = blockEmb K 2 1 n (k a) (b a) (hbk a) (u a) •
          (Pi.single j (1 : K) : Fin n → K) := by
          simp [f, F, qTwo_blockFactors, MulAction.toPermHom_apply]


end CFSG.ClassicalInvolution.PhanDn.QTwo

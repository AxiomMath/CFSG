module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.Open.QuasithinDefs

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G]

theorem mem_quasithinOmegaOneCenter_iff {S : Subgroup G} {z : G} :
    z ∈ quasithinOmegaOneCenter S ↔
      z ∈ S ∧ z ∈ Subgroup.centralizer (S : Set G) ∧ z ^ 2 = 1 := by
  constructor
  · intro hz
    unfold quasithinOmegaOneCenter at hz
    induction hz using Subgroup.closure_induction with
    | mem x hx => exact ⟨hx.1.1, hx.1.2, hx.2⟩
    | one => exact ⟨S.one_mem, Subgroup.one_mem _, one_pow 2⟩
    | mul x y hx hy ihx ihy =>
      refine ⟨S.mul_mem ihx.1 ihy.1, Subgroup.mul_mem _ ihx.2.1 ihy.2.1, ?_⟩
      have hcomm : x * y = y * x := by
        have := Subgroup.mem_centralizer_iff.mp ihx.2.1 y ihy.1
        exact this.symm
      rw [Commute.mul_pow hcomm 2, ihx.2.2, ihy.2.2, mul_one]
    | inv x hx ih =>
      exact ⟨S.inv_mem ih.1, Subgroup.inv_mem _ ih.2.1, by rw [inv_pow, ih.2.2, inv_one]⟩
  · rintro ⟨hzS, hzC, hz2⟩
    exact Subgroup.subset_closure ⟨⟨hzS, hzC⟩, hz2⟩

structure Lemma115Hyp (H S M : Subgroup G) (z : G) : Prop where
  pCore_ne_bot : pCoreOf 2 H ≠ ⊥
  sylow : IsSylowTwoOf S H
  charTwo : CharTwo M
  pCore_M_ne_bot : pCoreOf 2 M ≠ ⊥
  le : S ≤ M
  centralizer_le : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H
  centralizer_z_le : Subgroup.centralizer ({z} : Set G) ≤ M
  z_ne_one : z ≠ 1
  z_mem : z ∈ S
  z_central : z ∈ Subgroup.centralizer (S : Set G)
  z_sq : z ^ 2 = 1

namespace Lemma115Hyp

variable {H S M : Subgroup G} {z : G}

theorem mem_omegaOneCenter (h : Lemma115Hyp H S M z) : z ∈ quasithinOmegaOneCenter S :=
  mem_quasithinOmegaOneCenter_iff.mpr ⟨h.z_mem, h.z_central, h.z_sq⟩

theorem z_mem_H (h : Lemma115Hyp H S M z) : z ∈ H := h.sylow.1 h.z_mem

theorem S_le_inf (h : Lemma115Hyp H S M z) : S ≤ H ⊓ M := le_inf h.sylow.1 h.le

theorem of_mem_omegaOneCenter (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hM : CharTwo M)
    (hM' : pCoreOf 2 M ≠ ⊥) (hSM : S ≤ M)
    (hC : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 (H ⊓ M) : Set G) ≤ H)
    (hz : Subgroup.centralizer ({z} : Set G) ≤ M) (hz1 : z ≠ 1)
    (hzS : z ∈ quasithinOmegaOneCenter S) : Lemma115Hyp H S M z :=
  let h := mem_quasithinOmegaOneCenter_iff.mp hzS
  ⟨hH, hS, hM, hM', hSM, hC, hz, hz1, h.1, h.2.1, h.2.2⟩

end Lemma115Hyp

end CFSG.QuasithinUnique

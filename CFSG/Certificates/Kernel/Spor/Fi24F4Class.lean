module

public import CFSG.Certificates.Kernel.Spor.Fi24F4Sound
public import Certificates.Data.Kernel.Spor.ConjTree
public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow

public section

namespace CFSG.KS.Fi24F4

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.ConjTree
open CFSG.KS.Raw.Orb (PRep)

theorem prep_pconj {n w G X GI : Nat} {g x : Equiv.Perm (Fin n)} (hn : n < 2 ^ 32)
    (hG : PRep n w G g) (hX : PRep n w X x) (hGI : PRep n w GI g⁻¹) :
    PRep n w (pconj n w G X GI) (g * x * g⁻¹) := by
  unfold pconj
  rw [mul_assoc]
  exact prep_mul hn hG (prep_mul hn hX hGI)

theorem pconj_shr {n w G X GI : Nat} (hn : n < 2 ^ 32) (hw : 0 < w) :
    pconj n w G X GI >>> (n * w) = 0 := pcomp_shr' hn hw

theorem prep_unique {n w P : Nat} {g h : Equiv.Perm (Fin n)} (hg : PRep n w P g)
    (hh : PRep n w P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

theorem card_eq_mul_of_tree {n w r m wt wp TF : Nat} (hn : n < 2 ^ 32) (hw : 0 < w)
    (H : Subgroup (Equiv.Perm (Fin n))) {g : ℕ → Equiv.Perm (Fin n)}
    (hgen : H = Subgroup.closure (g '' {l | l < r})) {GS GSI T PA : ℕ → ℕ} {y : Equiv.Perm (Fin n)}
    (hg : ∀ l < r, PRep n w (GS l) (g l) ∧ PRep n w (GSI l) (g l)⁻¹)
    (h0 : PRep n w (T 0) y) (hc0 : T 0 >>> (n * w) = 0) (hm : 0 < m)
    (hS : ∀ i < m - 1, pg wt (mask wt) TF i / r < i + 1 ∧
      T (i + 1) = pconj n w (GS (pg wt (mask wt) TF i % r)) (T (pg wt (mask wt) TF i / r))
        (GSI (pg wt (mask wt) TF i % r)))
    (hr : 0 < r)
    (hA : ∀ j < m, ∀ l < r, pg wp (mask wp) (PA l) j < m ∧
      pconj n w (GS l) (T j) (GSI l) = T (pg wp (mask wp) (PA l) j))
    (hD : ∀ j < m, ∀ k < j, Nat.beq (T j) (T k) = false) :
    Nat.card H = m * Nat.card ↥(H ⊓ Subgroup.centralizer ({y} : Set (Equiv.Perm (Fin n)))) := by
  classical
  have hgH : ∀ l < r, g l ∈ H := fun l hl => by
    rw [hgen]
    exact Subgroup.subset_closure ⟨l, hl, rfl⟩
  have hmem : ∀ i < m, (∃ x, PRep n w (T i) x ∧ x ∈ CFSG.Sporadic.SmallOddCore.conjClass H y) ∧
      T i >>> (n * w) = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨⟨y, h0, CFSG.Sporadic.SmallOddCore.self_mem_conjClass H y⟩, hc0⟩
      · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
        obtain ⟨hlt, hstep⟩ := hS k (by omega)
        set t := pg wt (mask wt) TF k
        have hl : t % r < r := Nat.mod_lt _ hr
        obtain ⟨⟨x, hx, c, hc, rfl⟩, -⟩ := ih (t / r) hlt (by omega)
        refine ⟨⟨g (t % r) * (c * y * c⁻¹) * (g (t % r))⁻¹, ?_, g (t % r) * c,
          H.mul_mem (hgH _ hl) hc, by group⟩, ?_⟩
        · rw [hstep]
          exact prep_pconj hn (hg _ hl).1 hx (hg _ hl).2
        · rw [hstep]
          exact pconj_shr hn hw
  choose e he using fun i : Fin m => (hmem i.val i.isLt).1
  have hinj : Function.Injective e := by
    intro j k hjk
    by_contra hne
    have hne' : j.val ≠ k.val := fun h => hne (Fin.ext h)
    have heq : T j.val = T k.val := by
      refine CFSG.KS.PF.eq_of_fields hw (hmem _ j.isLt).2 (hmem _ k.isLt).2 fun i hi => ?_
      rw [(he j).1 ⟨i, hi⟩, (he k).1 ⟨i, hi⟩, hjk]
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · have := hD k.val k.isLt j.val h
      rw [heq, Nat.beq_refl] at this
      exact Bool.noConfusion this
    · have := hD j.val j.isLt k.val h
      rw [heq, Nat.beq_refl] at this
      exact Bool.noConfusion this
  have hy0 : y ∈ Set.range e := ⟨⟨0, hm⟩, prep_unique (he ⟨0, hm⟩).1 h0⟩
  have hgens : ∀ s ∈ Set.range e, ∀ x ∈ g '' {l | l < r}, x * s * x⁻¹ ∈ Set.range e := by
    rintro _ ⟨j, rfl⟩ _ ⟨l, hl, rfl⟩
    obtain ⟨hj', heq⟩ := hA j.val j.isLt l hl
    refine ⟨⟨_, hj'⟩, prep_unique (he _).1 ?_⟩
    rw [← heq]
    exact prep_pconj hn (hg l hl).1 (he j).1 (hg l hl).2
  have hcls : CFSG.Sporadic.SmallOddCore.conjClass H y = Set.range e := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      rw [hgen] at hd
      exact CFSG.EvenSporadicStandard.Induction.AutBound.conj_mem_of_closed _ _ hgens d hd y hy0
    · rintro ⟨j, rfl⟩
      exact (he j).2
  have hos := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card H y
  rw [hcls, Set.ncard_range_of_injective hinj, Nat.card_fin] at hos
  exact hos.symm

end CFSG.KS.Fi24F4

end

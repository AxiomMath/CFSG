module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.SylowFour
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
open CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.SmallOddCore (tp rep_tp rep_invT enum_spec commTT_iff tblEq_iff_eq
  tblEq_idT_iff permOK commTT)

@[expose] def sylowCenterOK (n capS : ℕ) (memK : Table → Bool) (cg sg : Array Table)
    (sylowOrder : ℕ) (t : Table) : Bool :=
  let syl := mulClosureH n sg capS
  cg.all (fun x => permOK n x && invOK n x (invT n x) && memK x) &&
    sg.all (fun x => permOK n x && invOK n x (invT n x) && memK x) && permOK n t &&
    mulTreeOK n sg syl.1 syl.2.1 syl.2.2 && closedOKH n (sg ++ sg.map (invT n)) syl.1 &&
    hkeysDistinct n syl.1.toList && syl.1.size == sylowOrder &&
    syl.1.all (fun s => !tblEq n (compT n s s) (idT n) || !cg.all (fun c => commTT n s c) ||
      tblEq n s (idT n) || tblEq n s t)

theorem centerInv_of_sylowCenterOK {n : ℕ} (hn : n < 2 ^ 32)
    {K : Subgroup (Equiv.Perm (Fin n))} {memK : Table → Bool}
    (hmem : ∀ (T : Table) (g : Equiv.Perm (Fin n)), Rep n T g → memK T = true → g ∈ K)
    {capS : ℕ} {cg sg : Array Table} {sylowOrder : ℕ} {t : Table} {τ : Equiv.Perm (Fin n)}
    (hτ : Rep n t τ) (hsyl : sylowOrder = 2 ^ (Nat.card K).factorization 2)
    (h : sylowCenterOK n capS memK cg sg sylowOrder t = true) :
    ∀ z ∈ K, z * z = 1 → (∀ y ∈ K, y * z = z * y) → z = 1 ∨ z = τ := by
  simp only [sylowCenterOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hcg, hsg⟩, ht⟩, htree⟩, hclosed⟩, hdist⟩, hsize⟩, hall⟩ := h
  rw [Array.all_eq_true'] at hcg hsg hall
  simp only [Bool.and_eq_true] at hcg hsg
  have hsgA : ∀ x ∈ sg, permOK n x = true := fun x hx => (hsg x hx).1.1
  have hsginv : ∀ x ∈ sg, invOK n x (invT n x) = true := fun x hx => (hsg x hx).1.2
  obtain ⟨-, hcov, hcard⟩ := enum_spec hn hsgA hsginv htree (closedOK_of_closedOKH hclosed) hdist
  set S := closure (tp n '' {x | x ∈ sg})
  have hSK : S ≤ K := by
    rw [closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hmem x _ (rep_tp (hsgA x hx)) (hsg x hx).2
  have hScard : Nat.card S = 2 ^ (Nat.card K).factorization 2 := by rw [hcard, hsize, hsyl]
  intro z hzK hzz hzc
  have hz4 : z ^ 4 = 1 := by
    calc z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [sq z, hzz, one_pow]
  obtain ⟨c, hcK, hcS⟩ := exists_conj_mem_of_card_pow_four hSK hScard hzK hz4
  have hzS : z ∈ S := by
    have : c⁻¹ * z * c = z := by
      have := hzc c hcK
      calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
        _ = c⁻¹ * (c * z) := by rw [this]
        _ = z := by group
    rwa [this] at hcS
  obtain ⟨k, hk, hkrep⟩ := hcov z hzS
  have hkmem := CFSG.Sporadic.SmallOddCore.getElem!_mem_array hk
  have h5 := hall _ hkmem
  have hsq : tblEq n (compT n (mulClosureH n sg capS).1[k]! (mulClosureH n sg capS).1[k]!)
      (idT n) = true :=
    (tblEq_idT_iff hn (Rep.compT hkrep hkrep)).2 hzz
  have hcomm : cg.all (fun c => commTT n (mulClosureH n sg capS).1[k]! c) = true := by
    rw [Array.all_eq_true']
    intro c hc
    have hcperm := (hcg c hc).1.1
    have hcrep := rep_tp hcperm
    have hcK' : tp n c ∈ K := hmem c _ hcrep (hcg c hc).2
    exact (commTT_iff hkrep hcrep).2 (hzc _ hcK').symm
  rw [hsq, hcomm] at h5
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at h5
  rcases h5 with h6 | h6
  · exact Or.inl ((tblEq_idT_iff hn hkrep).1 h6)
  · exact Or.inr ((tblEq_iff_eq hkrep hτ).1 h6)

end CFSG.EvenSporadicStandard.Solomon78

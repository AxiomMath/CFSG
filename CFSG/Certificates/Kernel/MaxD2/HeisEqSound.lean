module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSFiveSound
public import CFSG.Certificates.Kernel.MaxD2.BlockSound

public section

namespace CFSG.AGLEmbedding.MaxD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open Certificates.MaxD2Perm Certificates.MaxD2Heis

section Perm

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}
  (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
  (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹)

include hgs hgi

theorem cover_of_dcoset_check (hcard : Nat.card (Gsub S) = D.gOrder) (hN : checkN D = true)
    (hfp : fpOK D.fpPts (nEnum D).tabs = true) (hinvs : invsOK D.n (repT D) (repI D) = true)
    (hsum : dcSum D.n D.nOrder D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = D.gOrder)
    (hdisj : dcDisjoint D.n D.fpPts (indexOf ((nEnum D).tabs.map (fpTab D.fpPts)))
      ((nEnum D).tabs.map (fpTab D.fpPts)) (nEnum D).tabs (repT D) (repI D) = true) :
    ∀ y ∈ Gsub S, ∃ i ≤ D.repW.length, y ∈ dcoset (Nsub D S) ((repElts D S).getD i 1) := by
  have hN' := enum_N hgs hgi hN
  simp only [dcDisjoint, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hdisj
  have hrsz : (repT D).size = D.repW.length + 1 := by simp [repT]
  have hrisz : (repI D).size = D.repW.length + 1 := by simp [repI, repT]
  have hrepT := repT_rep hgs hgi
  have hrepI := repI_rep hgs hgi hinvs
  have hlenE : (repElts D S).length = D.repW.length + 1 := by simp [repElts]
  have hxT : ∀ i, i < D.repW.length + 1 → TabRep (repT D)[i]! ((repElts D S).getD i 1) := by
    intro i hi
    have := hrepT i
    rwa [show (repT D).getD i (idTab D.n) = (repT D)[i]! by simp [hrsz, hi]] at this
  have hxI : ∀ i, i < D.repW.length + 1 → TabRep (repI D)[i]! ((repElts D S).getD i 1)⁻¹ := by
    intro i hi
    have := hrepI i
    rwa [show (repI D).getD i (idTab D.n) = (repI D)[i]! by simp [hrisz, hi]] at this
  refine exists_dcoset_of_sum Nsub_le_Gsub (fun i => (repElts D S).getD i 1) D.repW.length
    (fun i hi => repElts_mem (getD_mem_of_lt (by omega) 1))
    (by rw [sum_eq hgs hgi hN hfp hinvs hsum, hcard]) ?_
  intro i hi j hj hij a ha hmem
  obtain ⟨k, hk, hka⟩ := hN'.exists_pos ha
  rcases hdisj i (by omega) j (by omega) with h | h
  · exact h hij
  · have hy := ((hxI i (by omega)).comp hka).comp (hxT j (by omega))
    have hmemT := (mem_enum_iff hN' hy).2 hmem
    have := (memFp_iff hfp _).2 hmemT
    rw [h k hk] at this
    exact Bool.noConfusion this

theorem normalizer_center_le_of_reps (hp : D.p.Prime) (hR : checkHR D = true)
    (hNorm : checkHNormal D = true) (hZ : checkHZ D = true) (hExp : checkHExp D = true)
    {z : Equiv.Perm (Fin D.n)}
    (hzZ : z ∈ Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))))
    (hz1 : z ≠ 1) (g : ℕ → Equiv.Perm (Fin D.n)) (r : ℕ) (hg0 : g 0 = 1)
    (hcover : ∀ y ∈ Gsub S, ∃ i ≤ r, y ∈ dcoset (Nsub D S) (g i)) (m : ℕ) (hm : D.p = m + 1)
    (hmv : ∀ i, 1 ≤ i → i ≤ r → ∀ k < m, g i * z * (g i)⁻¹ ≠ z ^ (k + 1)) :
    Subgroup.normalizer ((Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) :
      Subgroup (Equiv.Perm (Fin D.n))) : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S ≤ Nsub D S := by
  obtain ⟨hZx, -⟩ := zpowers_eq_of_card_prime hp (card_Z hgs hgi hR hZ) hzZ hz1
  have hpow : z ^ (m + 1) = 1 := by
    rw [← hm]
    exact exp_R hgs hgi hR hExp z hzZ.1
  rw [← hZx]
  refine CFSG.KS.MaxD2.normalizer_inf_le_of_reps g r hg0 ?_ hcover fun i h1 h2 =>
    CFSG.KS.MaxD2.not_mem_normalizer_zpowers hz1 hpow (hmv i h1 h2)
  intro x hx
  have := mem_normalizer_inf_centralizer (N_le_normalizer_H hgs hgi hR hNorm hx)
  rwa [← hZx] at this

theorem heisDataEq_of_parts (hp : D.p.Prime)
    (hsolv : ∃ a b : ℕ, D.nOrder = D.p ^ 3 * (2 ^ a * 3 ^ b)) (hR : checkHR D = true)
    (hN : checkN D = true) (hNorm : checkHNormal D = true) (hZ : checkHZ D = true)
    (hExp : checkHExp D = true) (hComm : checkHComm D = true) (hTorus : checkHTorus D = true)
    (hCent : checkHCent D = true)
    (hle : Subgroup.normalizer ((Rsub D S ⊓
      Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) :
        Subgroup (Equiv.Perm (Fin D.n))) : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S ≤ Nsub D S) :
    HeisDataEq D.p D.tm D.tlam D.te (Gsub S) (Rsub D S) ∧
      Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S = Nsub D S := by
  have hN1 : Nsub D S ≤ Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S :=
    le_inf (N_le_normalizer_H hgs hgi hR hNorm) Nsub_le_Gsub
  have hN2 : Subgroup.normalizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S ≤
      Subgroup.normalizer ((Rsub D S ⊓
        Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) :
          Subgroup (Equiv.Perm (Fin D.n))) : Set (Equiv.Perm (Fin D.n))) ⊓ Gsub S :=
    inf_le_inf_right _ fun g hg => mem_normalizer_inf_centralizer hg
  have hNeq := le_antisymm (hN2.trans hle) hN1
  refine ⟨⟨Rsub_le_Gsub, card_RH hgs hgi hR, centralizer_le_Eq hgs hgi hNeq hR hN hCent,
    card_Z hgs hgi hR hZ, commutator_eq hgs hgi hp hR hZ hComm, exp_R hgs hgi hR hExp, ?_, ?_⟩,
    hNeq⟩
  · rw [hNeq]
    obtain ⟨a, b, hab⟩ := hsolv
    refine isSolvable_of_normal_pow (k := 3) (a := a) (b := b) hp ?_
      (N_le_normalizer_H hgs hgi hR hNorm) (card_RH hgs hgi hR) (by rw [card_N hgs hgi hN, hab])
    rw [← hNeq]
    exact le_inf Subgroup.le_normalizer Rsub_le_Gsub
  · obtain ⟨t, htN, h1, h2, h3⟩ := torus_data_H hgs hgi hp hR hN hZ hExp hTorus
    exact ⟨t, by rw [hNeq]; exact htN, h1, h2, h3⟩

end Perm

end CFSG.AGLEmbedding.MaxD2

end

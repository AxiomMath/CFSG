module

public import Certificates.Data.Kernel.Gen6125
public import CFSG.Certificates.Kernel.BalanceSC.TableSound
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec4GenPerm
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.Gen6125.Sound

open CFSG.KC.Gen6125 CFSG.KC.BalanceSC CFSG.KC.BalanceSC.SylowEq CFSG.KC.BalanceSC.TableSound
open CFSG.KC.Enum (pg pcomp pidn strictB)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.BfsPin (PP)
open CFSG.KC.LQT.P (allN)
open CFSG.KC.Misc.ArrEnum (permB allNP_iff pp_of_permB)
open CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.AhatData
open Equiv Equiv.Perm

structure GenChecks (n N : ℕ) (PT : ℕ → ℕ) (jmode : Bool) (GG IA IB IC OC OP OL : List ℕ) :
    Prop where
  swG : (genGSw n).all (fun sw => swOK n sw true) = true
  lenG : (genGSw n).length = 3
  bindG : ((List.range 3).all fun j => (List.range n).all fun i =>
    Nat.beq ((swapsA n (genGSw n)[j]!)[i]!) (pg 4 15 (getL 0 GG j) i)) = true
  ats : atsK n N PT jmode GG IA IB IC = true
  word : wordK n GG (genWord n) = true
  pairs : pairK n GG OC OP OL = true

variable {n N : ℕ} {G PT : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ} {PS : List ℕ}
  {jmode : Bool} {GG IA IB IC OC OP OL : List ℕ}

theorem allN_true {m : ℕ} {f : ℕ → Bool} (h : allN m f = true) {i : ℕ} (hi : i < m) :
    f i = true :=
  allNP_iff.1 h i hi

theorem rep_wordP {g : ℕ → Perm (Fin n)} (hG : ∀ j < 3, PP n 4 (getL 0 GG j) ∧
      Rep n (unpack n 4 (getL 0 GG j)) (g j)) :
    ∀ (w : List ℕ), (∀ j ∈ w, j < 3) → ∀ (t : ℕ) (τ : Perm (Fin n)), PP n 4 t →
      Rep n (unpack n 4 t) τ →
      PP n 4 (wordP n GG w t) ∧
        Rep n (unpack n 4 (wordP n GG w t)) (w.foldl (fun σ j => σ * g j) τ) := by
  intro w
  induction w with
  | nil => intro _ t τ ht hr; exact ⟨ht, hr⟩
  | cons j w ih =>
    intro hw t τ ht hr
    have hj := hG j (hw j List.mem_cons_self)
    have h1 := rep_mulA hr hj.2
    rw [mulA_u ht hj.1] at h1
    exact ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)) _ _ (pp_mul ht hj.1) h1

theorem genGood_of_checks [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11)
    (C : Checks n N G PT E PAR LAB PS) (D : GenChecks n N PT jmode GG IA IB IC OC OP OL) :
    GenGood n (P0 n) jmode := by
  classical
  have hsz := C.sz
  let g : ℕ → Perm (Fin n) := fun j => swapsPerm n (genGSw n)[j]!
  have hmemG : ∀ j < 3, (genGSw n)[j]! ∈ genGSw n := fun j hj => by
    rw [getElem!_pos _ j (D.lenG ▸ hj)]
    exact List.getElem_mem _
  have hGok : ∀ j < 3, (∀ p ∈ (genGSw n)[j]!, p.1 < n ∧ p.2 < n ∧ p.1 ≠ p.2) ∧
      Even (genGSw n)[j]!.length := fun j hj => by
    have h := swOK_spec (List.all_eq_true.1 D.swG _ (hmemG j hj))
    exact ⟨h.1, h.2 rfl⟩
  have hAt : ∀ j < 3, atK n N PT jmode GG IA IB IC (pidn n 4) j = true := fun j hj => by
    have h := D.ats
    rw [atsK, strictB_eq] at h
    exact allN_true h hj
  have hGrep : ∀ j < 3, PP n 4 (getL 0 GG j) ∧ Rep n (unpack n 4 (getL 0 GG j)) (g j) := by
    intro j hj
    have h := hAt j hj
    rw [atK, strictB_eq, strictB_eq] at h
    simp only [bAnd_eq, Bool.and_eq_true] at h
    refine ⟨pp_of_permB hsz h.2.1, ?_⟩
    have hrep := rep_swapsA (n := n) _ fun p hp =>
      ⟨((hGok j hj).1 p hp).1, ((hGok j hj).1 p hp).2.1⟩
    refine rep_of_eqA_left hrep ?_
    have hb := List.all_eq_true.1 D.bindG j (List.mem_range.2 hj)
    rw [eqA, nat_all_iff]
    intro i hi
    rw [CFSG.KS.Raw.Orb.unpack_get hi, beq_iff_eq]
    exact Nat.eq_of_beq_eq_true (List.all_eq_true.1 hb i (List.mem_range.2 hi))
  have hA : ∀ j < 3, ∃ σ : Perm (Fin n), σ ∈ P0 n ∧ IsoI σ ∧ σ * g j = g j * σ ∧
      (jmode = true → ∃ E : Subgroup (Perm (Fin n)), E ≤ P0 n ∧ Nat.card E = 8 ∧
        (∀ e ∈ E, e = 1 ∨ IsoI e) ∧ σ ∈ E) := by
    intro j hj
    have h := hAt j hj
    rw [atK, strictB_eq, strictB_eq] at h
    simp only [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨hia, -, hiso, hcomm, hj8⟩ := h
    have hiaN := Nat.blt_eq.mp hia
    obtain ⟨σ, hσ, hrep⟩ := pt_mem C hn hn' hiaN
    have hpa := (point_facts C hiaN).1
    have hGj := hGrep j hj
    refine ⟨σ, hσ, (isoA_iff hrep).1 (by rw [isoA_u hsz hpa]; exact hiso),
      (commA_iff hrep hGj.2).1 (by rw [commA_u hpa hGj.1]; exact hcomm), fun hjm => ?_⟩
    rw [hjm] at hj8
    change (strictB _ fun b => _) = true at hj8
    rw [strictB_eq, strictB_eq, strictB_eq] at hj8
    simp only [bAnd_eq, Bool.and_eq_true] at hj8
    obtain ⟨hib, hic, hisb, hisc, hisab, hisac, hisbc, hisabc, h8⟩ := hj8
    have hibN := Nat.blt_eq.mp hib
    have hicN := Nat.blt_eq.mp hic
    obtain ⟨σb, hσb, hrb⟩ := pt_mem C hn hn' hibN
    obtain ⟨σc, hσc, hrc⟩ := pt_mem C hn hn' hicN
    have hpb := (point_facts C hibN).1
    have hpc := (point_facts C hicN).1
    have hpab := pp_mul hpa hpb
    have hrab : Rep n (unpack n 4 (pcomp n 4 15 (PT (getL 0 IA j)) (PT (getL 0 IB j))))
        (σ * σb) := by
      have := rep_mulA hrep hrb
      rwa [mulA_u hpa hpb] at this
    have hrac : Rep n (unpack n 4 (pcomp n 4 15 (PT (getL 0 IA j)) (PT (getL 0 IC j))))
        (σ * σc) := by
      have := rep_mulA hrep hrc
      rwa [mulA_u hpa hpc] at this
    have hrbc : Rep n (unpack n 4 (pcomp n 4 15 (PT (getL 0 IB j)) (PT (getL 0 IC j))))
        (σb * σc) := by
      have := rep_mulA hrb hrc
      rwa [mulA_u hpb hpc] at this
    have hrabc : Rep n (unpack n 4 (pcomp n 4 15 (pcomp n 4 15 (PT (getL 0 IA j))
        (PT (getL 0 IB j))) (PT (getL 0 IC j)))) (σ * σb * σc) := by
      have := rep_mulA hrab hrc
      rwa [mulA_u hpab hpc] at this
    have iso : ∀ {x : ℕ} {τ : Perm (Fin n)}, PP n 4 x → Rep n (unpack n 4 x) τ →
        isoK n (pidn n 4) x = true → IsoI τ := fun hx hr hk =>
      (isoA_iff hr).1 (by rw [isoA_u hsz hx]; exact hk)
    obtain ⟨E8, hEQ, hE8, hEi, haE, -, -⟩ := exists_eightSub' hrep hrb hrc hσ hσb hσc
      (iso hpa hrep hiso) (iso hpb hrb hisb) (iso hpc hrc hisc) (iso hpab hrab hisab)
      (iso (pp_mul hpa hpc) hrac hisac) (iso (pp_mul hpb hpc) hrbc hisbc)
      (iso (pp_mul hpab hpc) hrabc hisabc) (by rw [eightSub_u hsz hpa hpb hpc]; exact h8)
    exact ⟨E8, hEQ, hE8, hEi, haE⟩
  choose! a ha using hA
  let l : List (Perm (Fin n) × Perm (Fin n)) := (List.range 3).map fun j => (a j, g j)
  set S : Set (Perm (Fin n)) := {x | ∃ p ∈ l, p.2 = x} with hS
  have hgS : ∀ j < 3, g j ∈ Subgroup.closure S := fun j hj =>
    Subgroup.subset_closure ⟨(a j, g j), List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩, rfl⟩
  have hn2 : 2 ≤ n := by omega
  have hP := D.pairs
  rw [pairK, bAnd_eq, bAnd_eq, strictB_eq, Bool.and_eq_true, Bool.and_eq_true] at hP
  obtain ⟨h0, hstep, hcov⟩ := hP
  have hreach : ∀ k < OC.length, ∃ h ∈ Subgroup.closure S,
      ∃ (hx : getL 0 OC k % 16 < n) (hy : getL 0 OC k / 16 < n),
        h ⟨0, by omega⟩ = ⟨getL 0 OC k % 16, hx⟩ ∧ h ⟨1, by omega⟩ = ⟨getL 0 OC k / 16, hy⟩ := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have hc0 : getL 0 OC 0 = 16 := Nat.eq_of_beq_eq_true h0
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · refine ⟨1, Subgroup.one_mem _, by rw [hc0]; omega, by rw [hc0]; omega, ?_, ?_⟩
        · exact Fin.ext (by simp [hc0])
        · exact Fin.ext (by simp [hc0])
      · have h := allN_true hstep hk
        rw [bIf_true_eq, Bool.or_eq_true, stepK, strictB_eq, strictB_eq] at h
        rcases h with h | h
        · exact absurd (Nat.eq_of_beq_eq_true h) hk0.ne'
        simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h
        obtain ⟨hpk, hlk, hck⟩ := h
        have hck : getL 0 OC k =
            pg 4 15 (getL 0 GG (getL 0 OL k)) (getL 0 OC (getL 0 OP k) % 16) +
              16 * pg 4 15 (getL 0 GG (getL 0 OL k)) (getL 0 OC (getL 0 OP k) / 16) :=
          Nat.eq_of_beq_eq_true hck
        obtain ⟨h', hh', hx', hy', e1, e2⟩ := ih _ hpk (by omega)
        have hGl := hGrep _ hlk
        have hgx := hGl.2.apply hx'
        have hgy := hGl.2.apply hy'
        rw [CFSG.KS.Raw.Orb.unpack_get hx'] at hgx
        rw [CFSG.KS.Raw.Orb.unpack_get hy'] at hgy
        have hgx' : pg 4 15 (getL 0 GG (getL 0 OL k)) (getL 0 OC (getL 0 OP k) % 16) =
            (g (getL 0 OL k) ⟨_, hx'⟩ : ℕ) := hgx
        have hgy' : pg 4 15 (getL 0 GG (getL 0 OL k)) (getL 0 OC (getL 0 OP k) / 16) =
            (g (getL 0 OL k) ⟨_, hy'⟩ : ℕ) := hgy
        rw [hgx', hgy'] at hck
        have b1 := (g (getL 0 OL k) ⟨_, hx'⟩).2
        have b2 := (g (getL 0 OL k) ⟨_, hy'⟩).2
        have hm : getL 0 OC k % 16 = (g (getL 0 OL k) ⟨_, hx'⟩ : ℕ) := by omega
        have hd : getL 0 OC k / 16 = (g (getL 0 OL k) ⟨_, hy'⟩ : ℕ) := by omega
        refine ⟨g (getL 0 OL k) * h', Subgroup.mul_mem _ (hgS _ hlk) hh', by omega, by omega,
          ?_, ?_⟩
        · apply Fin.ext
          rw [Perm.mul_apply, e1]
          exact hm.symm
        · apply Fin.ext
          rw [Perm.mul_apply, e2]
          exact hd.symm
  have hpairs : ∀ x y : Fin n, x ≠ y → ∃ h ∈ Subgroup.closure S,
      h ⟨0, by omega⟩ = x ∧ h ⟨1, by omega⟩ = y := by
    intro x y hxy
    have h := allN_true (allN_true hcov x.2) y.2
    rw [bIf_true_eq, Bool.or_eq_true] at h
    rcases h with h | h
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true h)) hxy
    rw [memL_iff] at h
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.1 h
    obtain ⟨h', hh', hx', hy', e1, e2⟩ := hreach k hk
    have hc : getL 0 OC k = x.1 + 16 * y.1 := by
      rw [getL_eq, getElem!_pos OC k hk, hkx]
      rfl
    refine ⟨h', hh', ?_, ?_⟩
    · rw [e1]
      exact Fin.ext (by simp only [hc]; omega)
    · rw [e2]
      exact Fin.ext (by simp only [hc]; omega)
  have hW := D.word
  rw [wordK, bAnd_eq, Bool.and_eq_true, allL_eq, List.all_eq_true] at hW
  obtain ⟨hw3, hmov⟩ := hW
  have hw3' : ∀ j ∈ genWord n, j < 3 := fun j hj => Nat.blt_eq.mp (hw3 j hj)
  have hc : ∃ c ∈ Subgroup.closure S, c.IsThreeCycle := by
    refine ⟨(genWord n).foldl (fun σ j => σ * g j) 1, ?_, ?_⟩
    · have key : ∀ (w : List ℕ), (∀ j ∈ w, j < 3) → ∀ σ ∈ Subgroup.closure S,
          w.foldl (fun σ j => σ * g j) σ ∈ Subgroup.closure S := by
        intro w
        induction w with
        | nil => intro _ σ hσ; exact hσ
        | cons j w ih =>
          intro hw σ hσ
          exact ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)) _
            (Subgroup.mul_mem _ hσ (hgS j (hw j List.mem_cons_self)))
      exact key _ hw3' 1 (Subgroup.one_mem _)
    · have hid : Rep n (unpack n 4 (pidn n 4)) 1 := by
        rw [← idA_u hsz]
        exact rep_idA
      obtain ⟨-, hrep⟩ := rep_wordP hGrep (genWord n) hw3' _ 1
        (CFSG.KC.BfsPin.PP.id hsz) hid
      have h3 := suppA_eq hrep
      rw [suppA_u, Nat.eq_of_beq_eq_true hmov] at h3
      exact card_support_eq_three_iff.1 h3.symm
  have hgen : alternatingGroup (Fin n) ≤ Subgroup.closure S :=
    alt_le_closure_of_two_transitive (p := ⟨0, by omega⟩) (q := ⟨1, by omega⟩)
      (by simp [Fin.ext_iff]) hpairs hc
  refine ⟨⟨l, ?_, hgen⟩⟩
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hp
  have hj' := List.mem_range.1 hj
  obtain ⟨h1, h2, h3, h4⟩ := ha j hj'
  refine ⟨h1, h2, ?_, h3.symm, h4⟩
  rw [Perm.mem_alternatingGroup]
  exact sign_swapsPerm _ (hGok j hj').1 (hGok j hj').2

end CFSG.KC.Gen6125.Sound

end

module

public import CFSG.Certificates.Kernel.SporSch.ChainKReps
public import Certificates.Data.Kernel.SporSch.NoLayer
import CFSG.Sporadic.Recognition.LyonsAmalgamInv
import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Certificates.Kernel.SporSch.ChainKOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentMathNoLayerCheck

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KS.MEnum
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu CFSG.QuasithinUnique.Id2519.MathNoLayer

variable {n w : Nat}

theorem memL_iff (x : Nat) : ∀ E : List Nat, memL x E = true ↔ x ∈ E
  | [] => by simp [memL]
  | y :: E => by
    change bIf(Nat.beq x y, true, memL x E) = true ↔ _
    rw [Orb.bIf_eq, beq_dec, List.mem_cons, ← memL_iff x E]
    by_cases h : x = y <;> simp [h]

theorem allL_iff (f : Nat → Bool) : ∀ E : List Nat, allL f E = true ↔ ∀ y ∈ E, f y = true
  | [] => by simp [allL]
  | y :: E => by
    change bAnd(f y, allL f E) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, allL_iff f E, List.forall_mem_cons]

theorem bindLs_spec (n w : Nat) : ∀ (E : List (List Nat)) (EP : List Nat), bindLs n w E EP = true →
    E.length = EP.length ∧ ∀ i (h1 : i < E.length) (h2 : i < EP.length),
      bindListK n w EP[i] E[i] = true
  | [], [], _ => ⟨rfl, fun i h1 => absurd h1 (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => by simp [bindLs] at h
  | _ :: _, [], h => by simp [bindLs] at h
  | l :: E, P :: EP, h => by
    change bAnd(bindListK n w P l, bindLs n w E EP) = true at h
    rw [bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := bindLs_spec n w E EP h.2
    refine ⟨by simp [h1], fun i hi1 hi2 => ?_⟩
    rcases i with _ | i
    · exact h.1
    · exact h2 i (by simpa using hi1) (by simpa using hi2)

theorem table_eq_toTable {g : Equiv.Perm (Fin n)} {l : List Nat} (h : l = imageList g) :
    (l.map UInt32.ofNat).toArray = toTable g := by
  subst h
  rw [toTable, imageList, List.map_ofFn, Array.ofFn, List.toArray_ofFn]
  rfl

variable {gens : List (Equiv.Perm (Fin n))} {words : List (List Int)} {k : Nat}
  {bv : Vector (Fin n) k} {PS PSI LR TR TRI : Nat → Nat} {kS BP NS CH : Nat}

theorem originalSubgroup_certificate (hn : 1 ≤ n) (hbs : bv.toList.Nodup) :
    (certificate hn gens words bv hbs).originalSubgroup =
      Subgroup.closure {g | g ∈ gens} := by
  simp [RawSchreierDatum.originalSubgroup, certificate]

section Chain

variable (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH) (hn : 1 ≤ n)
  (hbs : bv.toList.Nodup)
include hQ hn hbs

theorem chainK_noLayer' {E : List (List Nat)} {EP : List Nat} (hb : bindLs n w E EP = true)
    (hid : memL (pidn n w) EP = true)
    (hE : nlE n w (mask w) (n * w) (pidn n w) LR TRI BP k PS PSI gens.length EP EP = true)
    {NB B : Nat} (hN : ordK LR k ≤ NB * B)
    (hK : ∀ s < NB, nlK n w (mask w) (n * w) (pidn n w) LR TR k EP (s * B) B = true) :
    noLayerOK n (E.map fun r => (r.map UInt32.ofNat).toArray)
      (allTables (certificate hn gens words bv hbs)) = true := by
  set Q := certificate hn gens words bv hbs
  set N := ordK LR k
  have h32 := chainK_h32 hQ
  have hsz := chainK_szOK hQ
  have hf := szOK_facts hsz
  have hw0 := PF.w_pos hf.2
  have hwn : n < 2 ^ w := by omega
  have pid := prep_pidn hf.1 hf.2
  have hV := chainK_valid hQ hn hbs
  have hA := forall₂_allTables h32 Q
  obtain ⟨hlen, hbind⟩ := bindLs_spec n w E EP hb
  rw [nlE, allL_iff] at hE
  have hcode : ∀ e ∈ EP, canonK n w (mask w) (n * w) e = true ∧
      siftK n w (mask w) (n * w) (pidn n w) LR TRI BP k 0 e = true ∧
      permOK n w (mask w) (n * w) e (pinvS n w (mask w) e) = true ∧
      pinvS n w (mask w) e ∈ EP ∧
      pcomp n w (mask w) (pcomp n w (mask w) e e) (pcomp n w (mask w) e e) = pidn n w ∧
      (∀ f ∈ EP, pcomp n w (mask w) e f ∈ EP) ∧
      ∀ j < gens.length, conjK n w (mask w) (PS j) (PSI j) e ∈ EP := by
    intro e he
    have h := hE e he
    simp only [bAnd_eq, Orb.strictB_eq, Bool.and_eq_true, memL_iff, allL_iff, allN_iff,
      beq_dec, decide_eq_true_eq] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  set pe : Nat → Equiv.Perm (Fin n) := fun e => CFSG.Monster.B.Co2.permOfArr n (unpack n w e)
  have hpe : ∀ e ∈ EP, PRep n w e (pe e) := fun e he =>
    prep_of_rep (CFSG.Monster.B.Co2.rep_permOfArr (isInvA_unpack (hcode e he).2.2.1)).1
  have hshr : ∀ e ∈ EP, e >>> (n * w) = 0 := fun e he => (PF.canon_facts (hcode e he).1).2.2.1
  set ET := E.map fun r => (r.map UInt32.ofNat).toArray
  have hET : ∀ T ∈ ET, ∃ e ∈ EP, T = toTable (pe e) := by
    intro T hT
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hT
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hl
    have hi' : i < EP.length := hlen ▸ hi
    have hmem := List.getElem_mem hi'
    refine ⟨EP[i], hmem, table_eq_toTable ?_⟩
    rw [imageList_of_prep (hpe _ hmem), ← toArray_eq_of_bindListK (hbind i hi hi')]
  have hEP : ∀ e ∈ EP, toTable (pe e) ∈ ET := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i < E.length := hlen ▸ hi
    refine List.mem_map.2 ⟨E[i], List.getElem_mem hi', table_eq_toTable ?_⟩
    rw [imageList_of_prep (hpe _ he), ← toArray_eq_of_bindListK (hbind i hi' hi)]
  have hmemT : ∀ (L : List Table) (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g →
      (∃ T ∈ L, ∃ h, Rep n T h ∧ h = g) → memT n x L = true := by
    rintro L x g hx ⟨T, hT, h, hTh, rfl⟩
    simp only [memT, List.any_eq_true]
    exact ⟨T, hT, (CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hx hTh).2 rfl⟩
  have hinE : ∀ (x : Table) (g : Equiv.Perm (Fin n)), Rep n x g →
      (∃ e ∈ EP, pe e = g) → memT n x ET = true := by
    rintro x g hx ⟨e, he, rfl⟩
    exact hmemT ET x _ hx ⟨_, hEP e he, _, rep_toTable h32 _, rfl⟩
  have hcodeP : ∀ (X : Nat) (g : Equiv.Perm (Fin n)), PRep n w X g → X ∈ EP → ∃ e ∈ EP, pe e = g :=
    fun X g hX hm => ⟨X, hm, prep_unique (hpe X hm) hX⟩
  have hinQ : ∀ e ∈ EP, pe e ∈ Q.originalSubgroup := by
    intro e he
    have hs := chainK_sift hn hbs hQ (imageList_of_prep (hpe e he)) (hcode e he).1
      (hcode e he).2.1
    exact (Q.sift_eq_true_iff_mem_original hV _).1 hs
  have hKT : ∀ q ∈ Q.originalSubgroup, ∃ T ∈ allTables Q, Rep n T q := fun q hq => by
    have : q ∈ (enumeration Q).reverse := by
      rw [List.mem_reverse]
      exact (mem_enumeration_iff Q hV q).2 hq
    exact exists_mem_of_forall₂_left hA q this
  have hTK : ∀ T ∈ allTables Q, ∃ q ∈ Q.originalSubgroup, Rep n T q := fun T hT => by
    obtain ⟨q, hq, hTq⟩ := exists_mem_of_forall₂_right hA T hT
    exact ⟨q, (mem_enumeration_iff Q hV q).1 (List.mem_reverse.1 hq), hTq⟩
  set F : Set (Equiv.Perm (Fin n)) := {g | ∃ e ∈ EP, pe e = g}
  have hFconj : ∀ q ∈ Q.originalSubgroup, ∀ z ∈ F, q * z * q⁻¹ ∈ F := by
    rw [originalSubgroup_certificate hn hbs]
    refine CFSG.KS.SporSch.ClsSpec.conj_closed fun g hg z hz => ?_
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (Set.mem_ofPred_eq ▸ hg)
    obtain ⟨e, he, rfl⟩ := hz
    obtain ⟨pS, pSI⟩ := prep_gens hQ hj
    rw [List.getD_eq_getElem _ _ hj] at pS pSI
    exact hcodeP _ _ (prep_conjK h32 pS pSI (hpe e he)) ((hcode e he).2.2.2.2.2.2 j hj)
  simp only [noLayerOK, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  ·
    rw [memL_iff] at hid
    exact hinE _ 1 (Rep.idT h32) (hcodeP _ _ pid hid)
  ·
    intro T hT
    obtain ⟨e, he, rfl⟩ := hET T hT
    obtain ⟨T', hT', hR'⟩ := hKT _ (hinQ e he)
    exact hmemT _ _ _ (rep_toTable h32 _) ⟨T', hT', _, hR', rfl⟩
  ·
    intro T hT
    obtain ⟨e, he, rfl⟩ := hET T hT
    have hR := rep_toTable h32 (pe e)
    have hinv := invOK_invT_of_rep h32 hR
    refine ⟨⟨hinv, hinE _ _ (Rep.inv_of_invOK hR hinv)
      (hcodeP _ _ (prep_pinvS hwn (hpe e he)).1 (hcode e he).2.2.2.1)⟩, fun T' hT' => ?_⟩
    obtain ⟨f, hf', rfl⟩ := hET T' hT'
    exact hinE _ _ (Rep.compT hR (rep_toTable h32 _))
      (hcodeP _ _ (prep_pcomp h32 (hpe e he) (hpe f hf')) ((hcode e he).2.2.2.2.2.1 f hf'))
  ·
    intro T hT
    obtain ⟨q, hq, hTq⟩ := hTK T hT
    have hinv := invOK_invT_of_rep h32 hTq
    refine ⟨hinv, fun T' hT' => ?_⟩
    obtain ⟨e, he, rfl⟩ := hET T' hT'
    exact hinE _ _ (Rep.compT (Rep.compT hTq (rep_toTable h32 _)) (Rep.inv_of_invOK hTq hinv))
      (hFconj q hq _ ⟨e, he, rfl⟩)
  ·
    intro T hT
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    have hlenT := (forall₂_allTables_elem hQ hn hbs).length_eq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hT
    have hiN : i < N := by
      rw [hlenT] at hi
      simpa using hi
    set j := N - 1 - i
    have hj : j < N := by omega
    have hRi : Rep n (allTables Q)[i] (elemP n w LR TR k j) := by
      have := (forall₂_allTables_elem hQ hn hbs).get hi (by simpa [← hlenT] using hi)
      simp only [List.get_eq_getElem, List.getElem_reverse, List.getElem_map, List.getElem_range,
        List.length_map, List.length_range] at this
      convert this using 2
    by_cases hc : ∀ T' ∈ ET, commT n (allTables Q)[i] T' = true
    · right
      have hblk := of_blocks hQ hN (f := fun j => strictB (elemK n w (mask w) (n * w) (pidn n w)
        LR TR k j) (fun q => bIf(allL (fun e => Nat.beq (pcomp n w (mask w) q e)
          (pcomp n w (mask w) e q)) EP, memL q EP, true))) hK j hj
      simp only [Orb.strictB_eq, Orb.bIf_eq] at hblk
      have pq := prep_elemK hQ j
      have hall : allL (fun e => Nat.beq (pcomp n w (mask w) (elemK n w (mask w) (n * w)
          (pidn n w) LR TR k j) e) (pcomp n w (mask w) e (elemK n w (mask w) (n * w) (pidn n w)
            LR TR k j))) EP = true := by
        rw [allL_iff]
        intro e he
        rw [beq_pcomp_iff h32 hw0 pq (hpe e he) (hpe e he) pq, decide_eq_true_eq]
        have := hc _ (hEP e he)
        rwa [commT_eq hRi (rep_toTable h32 _), decide_eq_true_eq] at this
      simp only [hall, ↓reduceIte, memL_iff] at hblk
      exact hinE _ _ hRi (hcodeP _ _ pq hblk)
    · left
      rw [Bool.eq_false_iff]
      intro h
      rw [List.all_eq_true] at h
      exact hc h
  ·
    intro T hT
    obtain ⟨e, he, rfl⟩ := hET T hT
    have hR := Rep.powT h32 (rep_toTable h32 (pe e)) 4
    rw [CFSG.Sporadic.SmallOddCore.tblEq_iff_eq hR (Rep.idT h32)]
    have h2 := prep_pcomp h32 (hpe e he) (hpe e he)
    have h4 := prep_pcomp h32 h2 h2
    rw [(hcode e he).2.2.2.2.1] at h4
    have := prep_unique h4 pid
    rw [← this, pow_succ, pow_succ, pow_succ, pow_one, mul_assoc (pe e * pe e)]

end Chain

end CFSG.KS.SporSch.MOC

end

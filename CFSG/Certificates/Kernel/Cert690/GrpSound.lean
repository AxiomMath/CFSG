module

public import CFSG.Certificates.Kernel.Cert690.EnumSound
public import CFSG.Certificates.Kernel.Cert690.CBaseSound
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Main
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFE
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB7a

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

theorem invGo_code_pow {gens E : List ℕ} (hE : EnumCert gens E) {g : V₀ ≃ₗ[ZMod 2] V₀}
    (hg : g ∈ codeSubgroup gens) : ∀ (fuel k : ℕ), (∃ j ≤ fuel, g ^ (k + j + 1) = 1) →
      invGo (hE.code g) fuel (hE.code (g ^ k)) = hE.code g⁻¹
  | 0, k, ⟨j, hj, hp⟩ => by
    obtain rfl : j = 0 := by omega
    have e : g ^ k = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hp)
    rw [e]
    rfl
  | f + 1, k, ⟨j, hj, hp⟩ => by
    have hk := Subgroup.pow_mem (codeSubgroup gens) hg k
    rw [invGo_succ, ← hE.code_mul hk hg, ← pow_succ]
    by_cases hc : hE.code (g ^ (k + 1)) = Code.one
    · rw [if_pos hc]
      have h1 : g ^ (k + 1) = 1 :=
        hE.eq_of_code_eq (Subgroup.pow_mem _ hg _) (Subgroup.one_mem _) (by rw [hc, hE.code_one])
      have e : g ^ k = g⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact h1)
      rw [e]
    · rw [if_neg hc]
      have hj0 : j ≠ 0 := by
        rintro rfl
        apply hc
        rw [Nat.add_zero] at hp
        rw [hp, hE.code_one]
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      refine invGo_code_pow hE hg f (k + 1) ⟨j', by omega, ?_⟩
      rw [show k + 1 + j' + 1 = k + j'.succ + 1 by omega]
      exact hp

theorem invGo_eq_of_mul {gens E : List ℕ} (hE : EnumCert gens E) {x c : ℕ} (hx : x ∈ E)
    (hc : c ∈ E) (hmul : mulF x c = oneF) : invGo x E.length x = c := by
  have hg := hE.elem_mem hx
  have hcx : hE.code (hE.elem x) = x := hE.code_elem hx
  have hinv : hE.code (hE.elem x)⁻¹ = c :=
    hE.code_inv_of_mul_eq_one hg hc (by rw [hcx, mul_eq_mulF, one_eq_oneF]; exact hmul)
  have hd := orderOf_dvd_natCard (⟨hE.elem x, hg⟩ : codeSubgroup gens)
  have hgm := pow_orderOf_eq_one (⟨hE.elem x, hg⟩ : codeSubgroup gens)
  generalize orderOf (⟨hE.elem x, hg⟩ : codeSubgroup gens) = m at hd hgm
  rw [hE.natCard] at hd
  have hgm' : hE.elem x ^ m = 1 := by simpa using congrArg Subtype.val hgm
  have hpos : 0 < E.length := List.length_pos_of_mem hx
  have hm0 : 0 < m := Nat.pos_of_dvd_of_pos hd hpos
  have hmn : m ≤ E.length := Nat.le_of_dvd hpos hd
  have key : ∃ j ≤ E.length, hE.elem x ^ (1 + j + 1) = 1 := by
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · refine ⟨0, Nat.zero_le _, ?_⟩
      obtain rfl : m = 1 := by omega
      rw [pow_one] at hgm'
      rw [hgm', one_pow]
    · refine ⟨m - 2, by omega, ?_⟩
      rw [show 1 + (m - 2) + 1 = m by omega]
      exact hgm'
  have e := invGo_code_pow hE hg E.length 1 key
  rwa [pow_one, hcx, hinv] at e

theorem invI_of {E C inv : List ℕ} {T : IT} {gens : List ℕ} (hE : EnumCert gens E)
    (hT : ∀ c, T.find c E.length = E.idxOf c) (h : invK T E.length E C inv = true) :
    (invArr E.toArray).map (fun c => (idxMapOf E.toArray).getD c E.toArray.size) =
      inv.toArray := by
  obtain ⟨hr, hl, hm⟩ := invK_spec T E.length E C inv h
  have hC : E.map (fun x => invGo x E.length x) = C := by
    apply List.ext_getElem (by rw [List.length_map, hl])
    intro i h1 h2
    have hi : i < E.length := by rw [← hl]; exact h2
    have hp := hm (E[i], C[i]) (by
      rw [← List.getElem_zip (l := E) (l' := C) (i := i) (h := by simp [hi, h2])]
      exact List.getElem_mem _)
    rw [hT] at hp
    rw [List.getElem_map]
    exact invGo_eq_of_mul hE (List.getElem_mem hi) (List.idxOf_lt_length_iff.1 hp.1) hp.2
  rw [hr, ← hC]
  unfold invArr
  rw [List.map_toArray, List.map_toArray, List.size_toArray, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, codeInv_eq, idxMapOf_getD hE.nodup, hT]

structure GrpChecks (minus : Bool) (O : List ℕ) (par S : List (ℕ × ℕ)) (Om : List ℕ)
    (omPar Sm : List (ℕ × ℕ)) (inv invC : List ℕ) : Prop where
  lenO : O.length = if minus then 51840 else 40320
  lenOm : Om.length = if minus then 25920 else 20160
  ixO : ixOK S O = true
  ixOm : ixOK Sm Om = true
  bfsO : bfsOK (fun y => (idxT S).find y O.length) (oGensC minus) O par = true
  bfsOm : bfsOK (fun y => (idxT Sm).find y Om.length) (omegaGensC minus) Om omPar = true
  invO : invK (idxT S) O.length O invC inv = true
  head : O.head? = some oneF
  headm : Om.head? = some oneF
  invGO : enumInvK (oGensC minus) O = true
  invGOm : enumInvK (omegaGensC minus) Om = true

namespace GrpChecks

variable {minus : Bool} {O : List ℕ} {par S : List (ℕ × ℕ)} {Om : List ℕ}
  {omPar Sm : List (ℕ × ℕ)} {inv invC : List ℕ} (h : GrpChecks minus O par S Om omPar Sm inv invC)
include h

theorem len_le : O.length ≤ 65535 := by rw [h.lenO]; cases minus <;> decide

theorem len_le_m : Om.length ≤ 65535 := by rw [h.lenOm]; cases minus <;> decide

theorem ix : O.Nodup ∧ ∀ c, (idxT S).find c O.length = O.idxOf c := find_idxT_eq_idxOf h.ixO

theorem ixm : Om.Nodup ∧ ∀ c, (idxT Sm).find c Om.length = Om.idxOf c :=
  find_idxT_eq_idxOf h.ixOm

theorem enumO : enumData (oGensC minus) = (O.toArray, par.toArray) :=
  enumData_of_bfsOK h.ix.2 h.bfsO (by rw [h.lenO]; cases minus <;> decide)

theorem enumOm : enumData (omegaGensC minus) = (Om.toArray, omPar.toArray) :=
  enumData_of_bfsOK h.ixm.2 h.bfsOm (by rw [h.lenOm]; cases minus <;> decide)

theorem grp_O : (grpData minus ()).O = O.toArray := by
  unfold grpData
  rw [h.enumO]

theorem grp_par : (grpData minus ()).par = par.toArray := by
  unfold grpData
  rw [h.enumO]

theorem grp_Om : (grpData minus ()).Om = Om.toArray := by
  unfold grpData
  rw [h.enumOm]

theorem grp_OmPar : (grpData minus ()).OmPar = omPar.toArray := by
  unfold grpData
  rw [h.enumOm]

theorem grp_idx (c : ℕ) :
    (grpData minus ()).idx.getD c O.length = (idxT S).find c O.length := by
  have e : (grpData minus ()).idx = idxMapOf O.toArray := by
    unfold grpData
    rw [h.enumO]
  rw [e, idxMapOf_getD h.ix.1, h.ix.2]

theorem enumCert : EnumCert (oGensC minus) O := by
  simpa using enumOK_sound (enumOK_of_bfs h.ixO h.head h.bfsO h.invGO)

theorem grp_invI : (grpData minus ()).invI = inv.toArray := by
  have e : (grpData minus ()).invI =
      (invArr O.toArray).map fun c => (idxMapOf O.toArray).getD c O.toArray.size := by
    unfold grpData
    rw [h.enumO]
  rw [e]
  exact invI_of h.enumCert h.ix.2 h.invO

theorem lenInv : inv.length = O.length := by
  obtain ⟨hr, hl, _⟩ := invK_spec _ _ O invC inv h.invO
  rw [hr, List.length_map, hl]

theorem invPos_mul (i : ℕ) (hi : i < O.length) (hj : i < inv.length) :
    ∃ hlt : inv[i] < O.length, mulF O[i] O[inv[i]] = oneF := by
  obtain ⟨hr, hl, hm⟩ := invK_spec _ _ O invC inv h.invO
  have hi2 : i < invC.length := by rw [hl]; exact hi
  have hp := hm (O[i], invC[i]) (by
    rw [← List.getElem_zip (l := O) (l' := invC) (i := i) (h := by simp [hi, hi2])]
    exact List.getElem_mem _)
  rw [h.ix.2] at hp
  have e : inv[i] = O.idxOf invC[i] := by
    simp only [hr, List.getElem_map, h.ix.2]
  have hlt' : inv[i] < O.length := by rw [e]; exact hp.1
  refine ⟨hlt', ?_⟩
  have e2 : O[inv[i]] = invC[i] := by
    simp only [e, List.getElem_idxOf]
  rw [e2]
  exact hp.2

theorem getO_eq (i : ℕ) : (posT O).find i 0 = O[i]! := by
  rw [find_posT h.len_le, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rfl

theorem getInv_eq (i : ℕ) : (posT inv).find i 0 = inv[i]! := by
  rw [find_posT (by rw [h.lenInv]; exact h.len_le), List.getElem!_eq_getElem?_getD,
    List.getD_eq_getElem?_getD]
  rfl

theorem rel : GRel (grpData minus ()) (gkOf O S inv O.length) where
  size := by rw [h.grp_O, List.size_toArray]; rfl
  get i := by rw [h.grp_O, List.getElem!_toArray]; exact (h.getO_eq i).symm
  idx c := h.grp_idx c
  inv i := by rw [h.grp_invI, List.getElem!_toArray]; exact (h.getInv_eq i).symm

theorem groupOK : CFSG.GF2Type.Smith1979W3.Cert690.groupOK minus (grpData minus ()) = true := by
  have e1 : enumOK (oGensC minus) (grpData minus ()).O (grpData minus ()).par = true := by
    rw [h.grp_O, h.grp_par]
    exact enumOK_of_bfs h.ixO h.head h.bfsO h.invGO
  have e2 : enumOK (omegaGensC minus) (grpData minus ()).Om (grpData minus ()).OmPar = true := by
    rw [h.grp_Om, h.grp_OmPar]
    exact enumOK_of_bfs h.ixOm h.headm h.bfsOm h.invGOm
  have R := h.rel
  have hidx : idxOK (grpData minus ()) = true := by
    unfold idxOK
    rw [List.all_eq_true]
    intro i hi
    rw [List.mem_range, R.size] at hi
    rw [R.size, R.get, R.idx, beq_iff_eq]
    show (idxT S).find ((posT O).find i 0) O.length = i
    rw [h.ix.2, h.getO_eq, getElem!_pos O i hi]
    exact h.ix.1.idxOf_getElem i _
  have hinv : invArrOK (grpData minus ()) = true := by
    have hl := h.lenInv
    unfold invArrOK
    rw [h.grp_invI, h.grp_O]
    simp only [List.all_toArray]
    simp only [List.size_toArray, hl, beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      List.all_eq_true, decide_eq_true_eq, List.mem_range, List.getElem!_toArray, beq_iff_eq]
    refine ⟨fun j hj => ?_, fun i hi => ?_⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hj
      exact (h.invPos_mul k (by rw [← hl]; exact hk) hk).fst
    · have hj : i < inv.length := by rw [hl]; exact hi
      obtain ⟨hlt, this⟩ := h.invPos_mul i hi hj
      rw [getElem!_pos O i hi, getElem!_pos inv i hj, getElem!_pos O _ hlt, mul_eq_mulF,
        one_eq_oneF]
      exact this
  unfold CFSG.GF2Type.Smith1979W3.Cert690.groupOK
  rw [e1, e2, hidx, hinv, h.grp_O, h.grp_Om, List.size_toArray, List.size_toArray, h.lenO,
    h.lenOm]
  cases minus <;> rfl

end GrpChecks

theorem censusBase_of {minus : Bool} {O : List ℕ} {par S : List (ℕ × ℕ)} {Om : List ℕ}
    {omPar Sm : List (ℕ × ℕ)} {inv invC : List ℕ}
    (h : GrpChecks minus O par S Om omPar Sm inv invC)
    (htr : transK (gkOf O S inv O.length) (singL minus) (b0Of minus)
      (transWitK (gkOf O S inv O.length) (singL minus) (b0Of minus)) = true)
    (hls : censusLsK (gkOf O S inv O.length) minus (ldata minus ()) = true) :
    censusBase minus () = true := by
  unfold censusBase
  rw [censusBaseOf_eq h.rel, h.groupOK, htr, hls]
  rfl

end CFSG.KC.C690

end

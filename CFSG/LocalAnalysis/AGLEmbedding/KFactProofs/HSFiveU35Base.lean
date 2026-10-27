
module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.HSOverDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.MaxD2HeisSound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.RankThree.Native.HSMcLSmall
public import Certificates.Certificate19830
public import Certificates.Certificate19851
public import Certificates.Certificate19852

@[expose] public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.AGLEmbedding.FusD2
open CFSG.AGLEmbedding.MaxD2 CFSG.RankThree.Native Certificates.MaxD2Perm Certificates.MaxD2Heis
open Certificates.HSOver Certificates.HSU35
open scoped commutatorElement

theorem hs_u35_check_heis : checkHeis dataU = true :=
  Certificates.certificate19851

theorem hs_u35_check_elements : check19852 = true :=
  Certificates.certificate19852

theorem hsU35_tab_a :
    TabRep hsTabA hs100A := by
  have h0 := Certificates.certificate19830
  have h := rep_hs100A
  rw [h0.1] at h
  exact ⟨h0.2.2.2.1, fun i => h i⟩

theorem hsU35_tab_b :
    TabRep hsTabB hs100B := by
  have h0 := Certificates.certificate19830
  have h := rep_hs100B
  rw [h0.2.1] at h
  exact ⟨h0.2.2.2.2.1, fun i => h i⟩

theorem hsU35_two {a b : Tab} {A B : Equiv.Perm (Fin 100)} (ha : TabRep a A) (hb : TabRep b B) :
    ∀ j, TabRep ((#[a, b] : Array Tab).getD j (idTab 100)) ([A, B].getD j 1) :=
  rep_getD_of_forall (L := [a, b]) (P := [A, B]) rfl (by
    intro i hi
    have hi' : i < 2 := hi
    interval_cases i
    · exact ha
    · exact hb)

theorem hsU35_gs :
    ∀ j, TabRep (hsFiveDataP.gT.getD j (idTab 100)) (hsOAB.getD j 1) :=
  hsU35_two hsU35_tab_a hsU35_tab_b

theorem hsU35_parts :
    checkInv hsFiveDataP = true ∧ checkOrders = true ∧ checkIdent = true ∧ checkTCent = true ∧
      checkW = true ∧ checkKernel = true ∧ checkE9 e9Enum = true ∧ checkUA = true := by
  have h := hs_u35_check_elements
  simp only [check19852, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem hsU35_parts_heis :
    checkInv dataU = true ∧ checkHR dataU = true ∧ checkN dataU = true ∧
      checkHNormal dataU = true ∧ checkHMoves dataU = true ∧ checkHZ dataU = true ∧
      checkHExp dataU = true ∧ checkHComm dataU = true ∧ checkHTorus dataU = true ∧
      checkHCent dataU = true ∧ checkMax dataU = true := by
  have h := hs_u35_check_heis
  simp only [checkHeis, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

theorem hsU35_gi :
    ∀ j, TabRep ((giT hsFiveDataP).getD j (idTab 100)) (hsOAB.getD j 1)⁻¹ :=
  giT_rep hsU35_gs hsU35_parts.1

theorem hsU35_wT
    (w : List ℤ) : TabRep (wT hsFiveDataP w) (wordVal hsOAB w) :=
  wT_rep hsU35_gs hsU35_gi w

@[expose] noncomputable def hsU35S : List (Equiv.Perm (Fin 100)) := uWords.map (wordVal hsOAB)

theorem hsU35S_eq : hsU35S = [hsOX, hsOY] := rfl

theorem hsU35_gsU :
    ∀ j, TabRep (dataU.gT.getD j (idTab dataU.n)) (hsU35S.getD j 1) :=
  rep_map_words hsOAB hsFiveDataP.gT (giT hsFiveDataP) hsU35_gs hsU35_gi uWords

theorem hsU35_giU :
    ∀ j, TabRep ((giT dataU).getD j (idTab dataU.n)) (hsU35S.getD j 1)⁻¹ :=
  giT_rep hsU35_gsU hsU35_parts_heis.1

theorem hsU35_word_eq
    {w w' : List ℤ}
    (h : (wT dataU w == wT hsFiveDataP w') = true) : wordVal hsU35S w = wordVal hsOAB w' :=
  ((wT_rep hsU35_gsU hsU35_giU w).eq_iff (hsU35_wT w')).1 (beq_iff_eq.1 h)

theorem hsU35_Gsub : Gsub (D := dataU) hsU35S = hsOUA := by
  show Subgroup.closure {g : Equiv.Perm (Fin 100) | g ∈ hsU35S} = hsOUA
  unfold hsOUA
  congr 1
  ext g
  simp [hsU35S_eq]

theorem hsU35_ident_parts :
    (wT dataU xyU0W == wT hsFiveDataP hsFiveUW) = true ∧
      (wT dataU xyV0W == wT hsFiveDataP hsFiveVW) = true ∧
      (wT dataU xyTW == wT hsFiveDataP hsOverTW) = true ∧
      (wT dataU xyWW == wT hsFiveDataP hsOverWW) = true ∧
      (wT dataU xyCW == wT hsFiveDataP hsOverCW) = true ∧
      (wT dataU xyE1W == wT hsFiveDataP hsOverE1W) = true ∧
      (wT dataU xyE2W == wT hsFiveDataP hsOverE2W) = true := by
  have h := hsU35_parts.2.2.1
  simp only [checkIdent, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

section Elements

theorem hsU35_u0 : wordVal hsU35S xyU0W = hsOU0 := hsU35_word_eq hsU35_ident_parts.1

theorem hsU35_v0 : wordVal hsU35S xyV0W = hsOV0 := hsU35_word_eq hsU35_ident_parts.2.1

theorem hsU35_t : wordVal hsU35S xyTW = hsOT := hsU35_word_eq hsU35_ident_parts.2.2.1

theorem hsU35_w : wordVal hsU35S xyWW = hsOW := hsU35_word_eq hsU35_ident_parts.2.2.2.1

theorem hsU35_c : wordVal hsU35S xyCW = hsOC := hsU35_word_eq hsU35_ident_parts.2.2.2.2.1

theorem hsU35_e1 : wordVal hsU35S xyE1W = hsOE1 := hsU35_word_eq hsU35_ident_parts.2.2.2.2.2.1

theorem hsU35_e2 : wordVal hsU35S xyE2W = hsOE2 := hsU35_word_eq hsU35_ident_parts.2.2.2.2.2.2

theorem hsU35_Rsub : Rsub dataU hsU35S = hsOR0 := by
  show Subgroup.closure {g : Equiv.Perm (Fin 100) |
    g ∈ [wordVal hsU35S xyU0W, wordVal hsU35S xyV0W]} = hsOR0
  rw [hsU35_u0, hsU35_v0]
  unfold hsOR0
  congr 1
  ext g
  simp

theorem hsU35_Nsub : Nsub dataU hsU35S = hsONU := by
  show Subgroup.closure {g : Equiv.Perm (Fin 100) |
    g ∈ [wordVal hsU35S xyU0W, wordVal hsU35S xyV0W, wordVal hsU35S xyTW]} = hsONU
  rw [hsU35_u0, hsU35_v0, hsU35_t]
  unfold hsONU
  congr 1
  ext g
  simp

end Elements

theorem hsU35_len : hsU35S.length = dataU.gT.size := rfl

theorem card_hsOR0 :
    Nat.card hsOR0 = 125 := by
  rw [← hsU35_Rsub, card_RH hsU35_gsU hsU35_giU hsU35_parts_heis.2.1]
  norm_num [dataU]

theorem hsOR0_le_UA :
    hsOR0 ≤ hsOUA := by
  rw [← hsU35_Rsub, ← hsU35_Gsub]
  exact Rsub_le_Gsub

theorem hsONU_le_UA :
    hsONU ≤ hsOUA := by
  rw [← hsU35_Nsub, ← hsU35_Gsub]
  exact Nsub_le_Gsub

theorem card_hsONU :
    Nat.card hsONU = 1000 := by
  rw [← hsU35_Nsub, card_N hsU35_gsU hsU35_giU hsU35_parts_heis.2.2.1]

theorem hsU35_commutator :
    ⁅hsOR0, hsOR0⁆ = hsOR0 ⊓ Subgroup.centralizer (hsOR0 : Set (Equiv.Perm (Fin 100))) ∧
      Nat.card (hsOR0 ⊓ Subgroup.centralizer (hsOR0 : Set (Equiv.Perm (Fin 100))) :
        Subgroup (Equiv.Perm (Fin 100))) = 5 := by
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have hp : dataU.p.Prime := by
    show Nat.Prime 5
    norm_num
  have h1 := commutator_eq hsU35_gsU hsU35_giU hp hR hZ hComm
  have h2 := card_Z hsU35_gsU hsU35_giU hR hZ
  rw [hsU35_Rsub] at h1 h2
  exact ⟨h1, h2⟩

theorem card_commutator_hsOR0 :
    Nat.card ↥⁅hsOR0, hsOR0⁆ = 5 := by
  rw [hsU35_commutator.1]
  exact hsU35_commutator.2

theorem commutator_hsOR0_le_centralizer :
    ⁅hsOR0, hsOR0⁆ ≤ Subgroup.centralizer (hsOR0 : Set (Equiv.Perm (Fin 100))) := by
  rw [hsU35_commutator.1]
  exact inf_le_right

theorem hsU35_orders_aux :
    hsOX ^ 8 = 1 ∧ hsOX ^ 4 ≠ 1 ∧ hsOY ^ 3 = 1 ∧ hsOY ≠ 1 ∧ (hsOX * hsOY) ^ 7 = 1 ∧
      hsOX * hsOY ≠ 1 ∧ hsOT ^ 8 = 1 ∧ hsOT ^ 4 ≠ 1 := by
  have h := hsU35_parts.2.1
  simp only [checkOrders, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hx8, hx4⟩, hy3⟩, hy1⟩, hxy7⟩, hxy1⟩, ht8⟩, ht4⟩ := h
  have hX : TabRep tabX hsOX := hsU35_wT hsOverXW
  have hY : TabRep tabY hsOY := hsU35_wT hsOverYW
  have hT : TabRep tabT hsOT := hsU35_wT hsOverTW
  have hXY := hX.comp hY
  exact ⟨((powT_rep hX 8).eq_iff TabRep.idTab).1 hx8,
    fun h => hx4 (((powT_rep hX 4).eq_iff TabRep.idTab).2 h),
    ((powT_rep hY 3).eq_iff TabRep.idTab).1 hy3,
    fun h => hy1 ((hY.eq_iff TabRep.idTab).2 h),
    ((powT_rep hXY 7).eq_iff TabRep.idTab).1 hxy7,
    fun h => hxy1 ((hXY.eq_iff TabRep.idTab).2 h),
    ((powT_rep hT 8).eq_iff TabRep.idTab).1 ht8,
    fun h => ht4 (((powT_rep hT 4).eq_iff TabRep.idTab).2 h)⟩

theorem orderOf_hsOT :
    orderOf hsOT = 8 := by
  obtain ⟨-, -, -, -, -, -, h8, h4⟩ := hsU35_orders_aux
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := hsOT) (by simpa using h4)
    (by simpa using h8)
  simpa using this

theorem hsU35_orderOf_x :
    orderOf hsOX = 8 := by
  obtain ⟨h8, h4, -⟩ := hsU35_orders_aux
  have := orderOf_eq_prime_pow (p := 2) (n := 2) (x := hsOX) (by simpa using h4)
    (by simpa using h8)
  simpa using this

theorem hsU35_orderOf_y :
    orderOf hsOY = 3 := by
  obtain ⟨-, -, h3, h1, -⟩ := hsU35_orders_aux
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime h3 h1

theorem hsU35_orderOf_xy :
    orderOf (hsOX * hsOY) = 7 := by
  obtain ⟨-, -, -, -, h7, h1, -⟩ := hsU35_orders_aux
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime h7 h1

theorem hsU35_t_mem_N :
    hsOT ∈ Nsub dataU hsU35S := by
  rw [← hsU35_t]
  exact Subgroup.subset_closure (List.mem_map.2 ⟨xyTW, by simp, rfl⟩)

theorem hsOT_mem_normalizer :
    hsOT ∈ Subgroup.normalizer (hsOR0 : Set (Equiv.Perm (Fin 100))) := by
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have h := N_le_normalizer_H hsU35_gsU hsU35_giU hR hNorm hsU35_t_mem_N
  rw [hsU35_Rsub] at h
  exact h

theorem hsOT_commute_R0 :
    ∀ r ∈ hsOR0, hsOT * r = r * hsOT → r = 1 := by
  intro r hr hcomm
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have hR' := enum_RH hsU35_gsU hsU35_giU hR
  rw [hsU35_Rsub] at hR'
  obtain ⟨k, hk, hkr⟩ := hR'.exists_pos hr
  have hT : TabRep tabT hsOT := hsU35_wT hsOverTW
  have hscan := hsU35_parts.2.2.2.1
  simp only [checkTCent, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at hscan
  rcases hscan k hk with h | h
  · exact absurd (((hT.comp hkr).eq_iff (hkr.comp hT)).2 hcomm) h
  · exact (hkr.eq_iff TabRep.idTab).1 h

section Torus

variable {D : Data} {S : List (Equiv.Perm (Fin D.n))}

theorem hsU35_torus_irred (hgs : ∀ j, TabRep (D.gT.getD j (idTab D.n)) (S.getD j 1))
    (hgi : ∀ j, TabRep ((giT D).getD j (idTab D.n)) (S.getD j 1)⁻¹) (hp : D.p.Prime)
    (hR : checkHR D = true) (hZ : checkHZ D = true) (hexp : checkHExp D = true)
    (hT : checkHTorus D = true) :
    ∀ k : ℕ, 0 < k → k < D.tm → ∀ F : Subgroup (Equiv.Perm (Fin D.n)),
      Rsub D S ⊓ Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) ≤ F →
        F ≤ Rsub D S → F.relIndex (Rsub D S) = D.p →
          wordVal S D.tW ^ k ∉ Subgroup.normalizer (F : Set (Equiv.Perm (Fin D.n))) := by
  have htrep := wT_rep hgs hgi D.tW
  have hR' := enum_RH hgs hgi hR
  have hZ' := enum_Z hgs hgi hR
  have hZc := card_Z hgs hgi hR hZ
  simp only [checkHTorus, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true, anyBelow_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at hT
  obtain ⟨⟨⟨⟨⟨hsz, hinv⟩, hfound⟩, hm⟩, he⟩, hk⟩ := hT
  have hti := htrep.inv hsz hinv
  intro k hk0 hkm F hZF hFR hidx hnorm
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hcardR := card_RH hgs hgi hR
  have hF : Nat.card F = D.p ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := F) (K := Rsub D S)
    rw [hidx, inf_eq_left.2 hFR, hcardR] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h]; ring)
  obtain ⟨x, hxF, hxZ⟩ : ∃ x ∈ F, x ∉ Rsub D S ⊓
      Subgroup.centralizer (Rsub D S : Set (Equiv.Perm (Fin D.n))) := by
    refine IsConcreteLE.not_le_iff_exists.1 fun hle => ?_
    have := Subgroup.card_le_of_le hle
    rw [hF, hZc] at this
    have h2 := hp.two_le
    nlinarith
  have hxR := hFR hxF
  obtain ⟨i, hi, hix⟩ := hR'.exists_pos hxR
  have hyF : wordVal S D.tW ^ (k' + 1) * x * (wordVal S D.tW ^ (k' + 1))⁻¹ ∈ F :=
    (Subgroup.mem_normalizer_iff.1 hnorm x).1 hxF
  obtain ⟨j, hj, z, hz, hyjz⟩ := exists_pow_mul_of_mem hp hZc hZF hF hxF hxZ
    (exp_R hgs hgi hR hexp x hxR) hyF
  obtain ⟨l, hl, hzl⟩ := hZ'.exists_pos hz
  rcases hk k' (by omega) i hi with hcont | hall
  · apply hxZ
    have hmem : (hrEnum D).tabs[i]! ∈ (zTabs D).toList := by
      simpa using hcont
    exact (mem_enum_iff hZ' hix).1 hmem
  · refine hall j hj l hl ?_
    have hy := ((powT_rep htrep (k' + 1)).comp hix).comp (powT_rep hti (k' + 1))
    have hy2 := (powT_rep hix j).comp hzl
    refine (hy.eq_iff hy2).2 ?_
    rw [inv_pow]
    exact hyjz

end Torus

theorem hsOT_irreducible :
    ∀ Y : Subgroup (Equiv.Perm (Fin 100)), ⁅hsOR0, hsOR0⁆ ≤ Y → Y ≤ hsOR0 →
      hsOT ∈ Subgroup.normalizer (Y : Set (Equiv.Perm (Fin 100))) →
        Y = ⁅hsOR0, hsOR0⁆ ∨ Y = hsOR0 := by
  intro Y hZY hYR hnorm
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have hp : dataU.p.Prime := by
    show Nat.Prime 5
    norm_num
  have hirr := hsU35_torus_irred hsU35_gsU hsU35_giU hp hR hZ hExp hTorus 1 one_pos
    (by show 1 < 2; norm_num)
  rw [hsU35_Rsub, hsU35_t, pow_one] at hirr
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have h5 : 5 ∣ Nat.card Y := by
    have := Subgroup.card_dvd_of_le hZY
    rwa [card_commutator_hsOR0] at this
  have h125 : Nat.card Y ∣ 5 ^ 3 := by
    have := Subgroup.card_dvd_of_le hYR
    rwa [card_hsOR0] at this
  obtain ⟨i, hi3, hiY⟩ := (Nat.dvd_prime_pow Nat.prime_five).1 h125
  interval_cases i
  · rw [pow_zero] at hiY
    rw [hiY] at h5
    omega
  · exact hne1 (Subgroup.eq_of_le_of_card_ge hZY
      (by rw [card_commutator_hsOR0, hiY]; simp)).symm
  · refine hirr Y (by rw [← hsU35_commutator.1]; exact hZY) hYR ?_ hnorm
    have h := Subgroup.relIndex_mul_card (H := Y) (K := hsOR0)
    rw [inf_eq_left.2 hYR, card_hsOR0, hiY] at h
    show Y.relIndex hsOR0 = 5
    omega
  · exact hne2 (Subgroup.eq_of_le_of_card_ge hYR (by rw [card_hsOR0, hiY]; simp))

theorem hsU35_mem_U :
    hsOT ∈ hsOUA ∧ hsOW ∈ hsOUA ∧ hsOC ∈ hsOUA ∧ hsOE1 ∈ hsOUA ∧ hsOE2 ∈ hsOUA := by
  rw [← hsU35_Gsub, ← hsU35_t, ← hsU35_w, ← hsU35_c, ← hsU35_e1, ← hsU35_e2]
  exact ⟨wordVal_mem_Gsub xyTW, wordVal_mem_Gsub xyWW, wordVal_mem_Gsub xyCW,
    wordVal_mem_Gsub xyE1W, wordVal_mem_Gsub xyE2W⟩

theorem hsOW_mem :
    hsOW ∈ hsOUA :=
  hsU35_mem_U.2.1

theorem hsU35_w_facts :
    hsOW ∉ hsONU ∧ hsOW * hsOT * hsOW⁻¹ ∈ Subgroup.zpowers hsOT := by
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have h := hsU35_parts.2.2.2.2.1
  simp only [checkW, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', anyBelow_eq_true] at h
  obtain ⟨⟨⟨hsz, hinv⟩, hfound⟩, j, hj, hjeq⟩ := h
  have hW : TabRep tabW hsOW := hsU35_wT hsOverWW
  have hT : TabRep tabT hsOT := hsU35_wT hsOverTW
  have hWi := hW.inv hsz hinv
  refine ⟨?_, ?_⟩
  · intro hmem
    rw [← hsU35_Nsub] at hmem
    have hN' := enum_N hsU35_gsU hsU35_giU hN
    have hNok : enumOK dataU.n (nGens dataU) (nEnum dataU) = true := by
      simp only [checkN, Bool.and_eq_true] at hN
      exact hN.1
    have := (found_iff_mem hNok hN' hW).2 hmem
    rw [hfound] at this
    exact Bool.noConfusion this
  · have := (((hW.comp hT).comp hWi).eq_iff (powT_rep hT j)).1 hjeq
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j

theorem hsOW_not_mem :
    hsOW ∉ hsONU :=
  hsU35_w_facts.1

theorem hsOW_conj_mem :
    hsOW * hsOT * hsOW⁻¹ ∈ Subgroup.zpowers hsOT :=
  hsU35_w_facts.2

@[expose] noncomputable def hsU35UA : List (Equiv.Perm (Fin 100)) := uaWords.map (wordVal hsOAB)

theorem hsU35_ua_words :
    wordVal hsU35UA uaXW = hsOX ∧ wordVal hsU35UA uaYW = hsOY := by
  obtain ⟨hInv, hOrd, hId, hTC, hW, hK, hE9, hUA⟩ := hsU35_parts
  simp only [checkUA, Bool.and_eq_true, beq_iff_eq] at hUA
  obtain ⟨⟨hinvs, hx⟩, hy⟩ := hUA
  have hgs5 : ∀ j, TabRep (uaGens.getD j (idTab 100)) (hsU35UA.getD j 1) :=
    rep_map_words hsOAB hsFiveDataP.gT (giT hsFiveDataP) hsU35_gs hsU35_gi uaWords
  have hgi5 : ∀ j, TabRep ((uaGens.map (invTab 100)).getD j (idTab 100)) (hsU35UA.getD j 1)⁻¹ := by
    simp only [invsOK, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hinvs
    obtain ⟨hsz, hinv⟩ := hinvs
    exact inv_rep_of_check hgs5 hsz hinv
  have hX : TabRep tabX hsOX := hsU35_wT hsOverXW
  have hY : TabRep tabY hsOY := hsU35_wT hsOverYW
  exact ⟨(wordT_rep hsU35UA uaGens _ hgs5 hgi5 uaXW).perm_eq (hx ▸ hX),
    (wordT_rep hsU35UA uaGens _ hgs5 hgi5 uaYW).perm_eq (hy ▸ hY)⟩

theorem hsOUA_le_UA2 :
    hsOUA ≤ hsOUA2 := by
  obtain ⟨hx, hy⟩ := hsU35_ua_words
  have hS : ∀ g ∈ hsU35UA, g ∈ hsOUA2 := by
    intro g hg
    simp only [hsU35UA, uaWords, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    unfold hsOUA2
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact Subgroup.subset_closure (by simp [hsOU0,
      hsOV0, hsOT0, hsOS0, hsOGA])
  have hxm : hsOX ∈ hsOUA2 := hx ▸ wordVal_mem hsU35UA hsOUA2 hS uaXW
  have hym : hsOY ∈ hsOUA2 := hy ▸ wordVal_mem hsU35UA hsOUA2 hS uaYW
  unfold hsOUA
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact hxm
  · exact hym

theorem hsOUA_E9 :
    ∃ E : Subgroup (Equiv.Perm (Fin 100)), E ≤ hsOUA ∧ CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 3 ^ 2 := by
  obtain ⟨hInv, hOrd, hId, hTC, hW, hK, hE9, hUA⟩ := hsU35_parts
  simp only [checkE9, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hE9
  obtain ⟨⟨⟨hok, hsize⟩, hcomm⟩, hexp⟩ := hE9
  have h := enumerates_of_words hsOAB hsFiveDataP.gT (giT hsFiveDataP) hsU35_gs hsU35_gi e9Words
    hok
  have e : {g : Equiv.Perm (Fin 100) | g ∈ e9Words.map (wordVal hsOAB)} = {hsOE1, hsOE2} := by
    ext g
    rw [show e9Words.map (wordVal hsOAB) = [hsOE1, hsOE2] from rfl]
    simp
  rw [e] at h
  refine ⟨Subgroup.closure {hsOE1, hsOE2}, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · rw [Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hsU35_mem_U.2.2.2.1
    · exact hsU35_mem_U.2.2.2.2
  · obtain ⟨i, hi, hia⟩ := h.exists_pos a.2
    obtain ⟨j, hj, hjb⟩ := h.exists_pos b.2
    apply Subtype.ext
    exact ((hia.comp hjb).eq_iff (hjb.comp hia)).1 (hcomm i hi j hj)
  · obtain ⟨i, hi, hix⟩ := h.exists_pos hx
    exact ((powT_rep hix 3).eq_iff TabRep.idTab).1 (hexp i hi)
  · rw [h.card, Array.length_toList, hsize]
    norm_num

theorem hsU35_kernel :
    ∀ g ∈ hsONU, hsOW⁻¹ * g * hsOW ∈ hsONU → hsOC⁻¹ * g * hsOC ∈ hsONU → g = 1 := by
  intro g hg hw hc
  obtain ⟨hInv, hR, hN, hNorm, hMoves, hZ, hExp, hComm, hTorus, hCent, hMax⟩ := hsU35_parts_heis
  have hN' := enum_N hsU35_gsU hsU35_giU hN
  rw [← hsU35_Nsub] at hg hw hc
  obtain ⟨k, hk, hkg⟩ := hN'.exists_pos hg
  have hNok : enumOK dataU.n (nGens dataU) (nEnum dataU) = true := by
    simp only [checkN, Bool.and_eq_true] at hN
    exact hN.1
  have hscan := hsU35_parts.2.2.2.2.2.1
  simp only [checkKernel, Bool.and_eq_true, beq_iff_eq, allBelow_eq_true] at hscan
  obtain ⟨⟨⟨⟨hwsz, hwinv⟩, hcsz⟩, hcinv⟩, hall⟩ := hscan
  have hW : TabRep tabW hsOW := hsU35_wT hsOverWW
  have hC : TabRep tabC hsOC := hsU35_wT hsOverCW
  have hWi := hW.inv hwsz hwinv
  have hCi := hC.inv hcsz hcinv
  have hA := (found_iff_mem hNok hN' ((hWi.comp hkg).comp hW)).2 hw
  have hB := (found_iff_mem hNok hN' ((hCi.comp hkg).comp hC)).2 hc
  have h := hall k hk
  rw [hA, hB] at h
  simp at h
  exact (hkg.eq_iff TabRep.idTab).1 h

end CFSG.AGLEmbeddingD2

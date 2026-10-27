module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.HeRef
public import CFSG.Quasithin.Vol2.KGFactC31HeChains
public import CFSG.Quasithin.Vol2.KGFactC31HeSet
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31Concl
public import CFSG.Quasithin.Vol2.KGFactC31HeR
public import CFSG.Quasithin.Vol2.KGFactC31HeScan
public import CFSG.Quasithin.Vol2.KGFactC31Ident
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.HeldB.InnerClass

public section

namespace CFSG.SectionRank.QTK.Insp443.He

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 CFSG.Sporadic.HeldB
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31.Native
  CFSG.Quasithin.KGC31.He CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.Ch1.SporLat.He _root_.Certificates

private theorem l7S_size : l7S.size = l7GenW.length + l7Der.length := by
  rw [l7S, size_foldl_push]
  simp

private theorem l7S_get {i : ℕ} (hi : i < l7GenW.length) : l7S[i]! = wA (l7GenW.getD i []) := by
  rw [l7S, getElem!_foldl_push _ _ _ (by simpa using hi)]
  exact getElem!_wA_toArray l7GenW hi

private theorem letters_l7GenW : l7GenW.all (lettersOK 2) = true := by
  have h := k_he_letters
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hx, hc⟩ := h
  rw [l7GenW]
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hx, lettersOK_append (lettersOK_append hc hx) (lettersOK_invW hc)⟩

private theorem permOfArr_l7S {i : ℕ}
    (hi : i < l7GenW.length) : permOfArr 8330 l7S[i]! = elt (l7GenW.getD i []) := by
  have hF := chainCheckFacts k_he_chain
  have hj : i < l7S.size := by rw [l7S_size]; omega
  have h := hF.strong_inv i hj
  rw [rawInvs, map_getElem! _ _ hj] at h
  have hl : lettersOK 2 (l7GenW.getD i []) = true :=
    List.all_eq_true.1 letters_l7GenW _
      (by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  exact (rep_permOfArr h).1.unique
    (by rw [l7S_get hi]; exact rep_wA (lettersOK_mono (by norm_num) hl))

@[expose] noncomputable def chainL7 : RawSchreierDatum 8330 :=
  arrChain (by norm_num) l7S l7GenW.length (by rw [l7S_size]; omega) l7B (by decide) l7Wd

theorem card_L7 : Nat.card chainL7.originalSubgroup = 21504 := by
  rw [chainL7, card_arrChain _ _ _ (by norm_num) k_he_chain, k_he_ord]

theorem L7_eq :
    chainL7.originalSubgroup = Subgroup.closure {g | ∃ w ∈ l7GenW, elt w = g} := by
  rw [chainL7, arrChain_originalSubgroup]
  congr 1
  ext g
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [permOfArr_l7S hi]
    exact ⟨_, by rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    exact ⟨i, hi, by rw [permOfArr_l7S hi, List.getD_eq_getElem _ _ hi]⟩

theorem elt_l7Gen :
    elt (c7W ++ x7W ++ invW c7W) = elt c7W * elt x7W * (elt c7W)⁻¹ := by
  have h := k_he_letters
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact elt_conjW (lettersOK_mono (by norm_num) h.2) (lettersOK_mono (by norm_num) h.1)

theorem orderOf_x7 :
    orderOf (elt x7W) = 7 := by
  have h := k_he_letters
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hr : RepW 8330 [wA x7W] (elt x7W) :=
    RepW.single (rep_wA (lettersOK_mono (by norm_num) h.1))
  have hm := elt_mem_heP h.1
  apply orderOf_eq_prime
  · exact (fixB_iff_eq_one baseFaithful_heP hbs hr hm 7).1 k_he_x7a
  · intro h1
    have := (fixB_iff_eq_one baseFaithful_heP hbs hr hm 1).2 (by rw [pow_one, h1])
    rw [k_he_x7b] at this
    exact absurd this (by decide)

theorem x7_mem :
    elt x7W ∈ heP ⊓ eNorm basis_Q := by
  have h := k_he_letters
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact ⟨elt_mem_heP h.1, elt_mem_eNorm_Q h.1 k_he_normX⟩

theorem c7_mem :
    elt c7W ∈ heP ⊓ eNorm basis_Q := by
  have h := k_he_letters
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  exact ⟨elt_mem_heP h.2, elt_mem_eNorm_Q h.2 k_he_normC⟩

private theorem row_of_le
    {X Y : Subgroup ↥heP} (hXY : X ≤ Y)
    (hX : 1024 ∣ Nat.card X) (hY : Y ≠ ⊤) :
    ∃ m ∈ heMems, Nat.card Y = m.order ∧ Nat.card (pCoreOf 2 Y) = m.o2 := by
  have hYdvd : 1024 ∣ Nat.card Y := hX.trans (Subgroup.card_dvd_of_le hXY)
  obtain ⟨T, hT, hTY⟩ := exists_sylow_le_he (X := ↥heP) card_heP hYdvd
  rcases he_overgroups (X := ↥heP) ⟨heEquivP.symm⟩ hT hTY with h | ⟨m, hm, h1, h2, -⟩
  · exact absurd h hY
  · exact ⟨m, hm, h1, h2⟩

private theorem subgroupOf_inf_eNorm_ne_top
    {k : ℕ} {v : Fin k → Equiv.Perm (Fin 8330)} (hv : EBasis v)
    (hP : eSub hv ≤ heP) (h1 : 1 < 2 ^ k) (h2 : 2 ^ k < 4030387200) :
    (heP ⊓ eNorm hv).subgroupOf heP ≠ ⊤ := by
  intro htop
  have hle : heP ≤ eNorm hv := fun x hx => by
    have hx' : (⟨x, hx⟩ : ↥heP) ∈ (heP ⊓ eNorm hv).subgroupOf heP := by
      rw [htop]; exact trivial
    exact (Subgroup.mem_subgroupOf.mp hx').2
  have hN : ((eSub hv).subgroupOf heP).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hP).mpr hle
  have hcard : Nat.card ((eSub hv).subgroupOf heP) = 2 ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, card_eSub]
  haveI : IsSimpleGroup ↥heP := heP_simple
  haveI := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((eSub hv).subgroupOf heP) with hbot | htop'
  · rw [hbot, Subgroup.card_bot] at hcard
    omega
  · rw [htop', Subgroup.card_top, card_heP] at hcard
    omega

private theorem order_eq_of_dvd_138240 {m : Mem} (hm : m ∈ heMems) (h : 138240 ∣ m.order) :
    m.order = 138240 := by
  simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rfl
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem order_eq_of_dvd_21504 {m : Mem} (hm : m ∈ heMems) (h : 21504 ∣ m.order) :
    m.order = 21504 := by
  simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem o2_eq_of_order_21504 {m : Mem} (hm : m ∈ heMems) (h : m.order = 21504) :
    m.o2 = 128 := by
  simp only [heMems, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · norm_num at h
  · rfl
  · norm_num at h
  · norm_num at h
  · norm_num at h

private theorem card_inf_eNorm_E :
    Nat.card ↥(heP ⊓ eNorm basis_E) = 138240 := by
  have hYne := subgroupOf_inf_eNorm_ne_top basis_E E_le_heP (by norm_num) (by norm_num)
  have hsub : nsGrp.subgroupOf heP ≤
      (heP ⊓ eNorm basis_E).subgroupOf heP := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (Ns_le (Subgroup.mem_subgroupOf.mp hx))
  have hcardX : Nat.card (nsGrp.subgroupOf heP) = 138240 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ns_le.trans inf_le_left)).toEquiv, card_Ns]
  obtain ⟨m, hm, h1, h2⟩ := row_of_le hsub (by rw [hcardX]; norm_num) hYne
  have hdvd' : 138240 ∣ m.order := by
    rw [← h1, ← hcardX]
    exact Subgroup.card_dvd_of_le hsub
  have hord : m.order = 138240 := order_eq_of_dvd_138240 hm hdvd'
  have hcardY : Nat.card ((heP ⊓ eNorm basis_E).subgroupOf heP) = 138240 := h1.trans hord
  rw [← hcardY]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : heP ⊓ eNorm basis_E ≤ heP)).toEquiv).symm

private theorem card_inf_eNorm_Q :
    Nat.card ↥(heP ⊓ eNorm basis_Q) = 21504 := by
  have hYne := subgroupOf_inf_eNorm_ne_top basis_Q Q_le_heP (by norm_num) (by norm_num)
  have hsub : n7Grp.subgroupOf heP ≤
      (heP ⊓ eNorm basis_Q).subgroupOf heP := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (N7_le (Subgroup.mem_subgroupOf.mp hx))
  have hcardX : Nat.card (n7Grp.subgroupOf heP) = 21504 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (N7_le.trans inf_le_left)).toEquiv, card_N7]
  obtain ⟨m, hm, h1, h2⟩ := row_of_le hsub (by rw [hcardX]; norm_num) hYne
  have hdvd' : 21504 ∣ m.order := by
    rw [← h1, ← hcardX]
    exact Subgroup.card_dvd_of_le hsub
  have hord : m.order = 21504 := order_eq_of_dvd_21504 hm hdvd'
  have hcardY : Nat.card ((heP ⊓ eNorm basis_Q).subgroupOf heP) = 21504 := h1.trans hord
  rw [← hcardY]
  exact (Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : heP ⊓ eNorm basis_Q ≤ heP)).toEquiv).symm

private theorem card_pCoreOf_inf_eNorm_Q :
    Nat.card (pCoreOf 2 (heP ⊓ eNorm basis_Q)) = 128 := by
  have hYne := subgroupOf_inf_eNorm_ne_top basis_Q Q_le_heP (by norm_num) (by norm_num)
  have hsub : n7Grp.subgroupOf heP ≤
      (heP ⊓ eNorm basis_Q).subgroupOf heP := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (N7_le (Subgroup.mem_subgroupOf.mp hx))
  have hcardX : Nat.card (n7Grp.subgroupOf heP) = 21504 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (N7_le.trans inf_le_left)).toEquiv, card_N7]
  obtain ⟨m, hm, h1, h2⟩ := row_of_le hsub (by rw [hcardX]; norm_num) hYne
  have hdvd' : 21504 ∣ m.order := by
    rw [← h1, ← hcardX]
    exact Subgroup.card_dvd_of_le hsub
  have hord : m.order = 21504 := order_eq_of_dvd_21504 hm hdvd'
  have hp : Nat.card (pCoreOf 2 ((heP ⊓ eNorm basis_Q).subgroupOf heP)) = 128 := by
    rw [h2, o2_eq_of_order_21504 hm hord]
  have hmap : (pCoreOf 2 ((heP ⊓ eNorm basis_Q).subgroupOf heP)).map heP.subtype =
      pCoreOf 2 (heP ⊓ eNorm basis_Q) := by
    rw [pCoreOf_map_subtype', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  rw [← hmap, Subgroup.card_map_of_injective heP.subtype_injective]
  exact hp

theorem heP_inf_eNorm_E :
    heP ⊓ eNorm basis_E = nsGrp := by
  have hcard := card_inf_eNorm_E
  exact (Subgroup.eq_of_le_of_card_ge Ns_le (by rw [hcard, card_Ns])).symm

theorem heP_inf_eNorm_Q :
    heP ⊓ eNorm basis_Q = n7Grp := by
  have hcard := card_inf_eNorm_Q
  exact (Subgroup.eq_of_le_of_card_ge N7_le (by rw [hcard, card_N7])).symm

theorem card_pCoreOf_N7 :
    Nat.card ↥(pCoreOf 2 n7Grp) = 128 := by
  rw [← heP_inf_eNorm_Q]
  exact card_pCoreOf_inf_eNorm_Q

theorem L7_eq_N7 :
    chainL7.originalSubgroup = n7Grp := by
  have hL : chainL7.originalSubgroup ≤ heP ⊓ eNorm basis_Q := by
    rw [L7_eq, Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    simp only [l7GenW, List.mem_cons, List.not_mem_nil, List.mem_singleton, or_false] at hw
    rcases hw with hw | hw
    · rw [hw]
      exact x7_mem
    · rw [hw, elt_l7Gen]
      exact (heP ⊓ eNorm basis_Q).mul_mem
        ((heP ⊓ eNorm basis_Q).mul_mem c7_mem x7_mem) ((heP ⊓ eNorm basis_Q).inv_mem c7_mem)
  rw [heP_inf_eNorm_Q] at hL
  exact Subgroup.eq_of_le_of_card_ge hL (by rw [card_L7, card_N7])

end CFSG.SectionRank.QTK.Insp443.He

end

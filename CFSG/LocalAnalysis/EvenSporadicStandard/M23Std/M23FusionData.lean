module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.NOne
public import CFSG.LocalAnalysis.EvenSporadicStandard.Wong77.M23Sylow
public import Certificates.Certificate24160
public import Certificates.Certificate24470
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2FinM2Abs
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.EvenSporadicStandard.M23Std

open CFSG.EvenSporadicStandard.Wong77 CFSG.EvenSporadicStandard.Wong77.M23Sylow
  CFSG.EvenSporadicStandard.M23Std.FusionCheck
  CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.QuasithinUnique.Unc25G2.M2x

theorem wordElt_mem {H : Subgroup (Carrier .M23)} {ls : List (Carrier .M23)} {w : List Nat}
    (hw : ∀ j ∈ w, ls.getD j 1 ∈ H) : wordElt ls w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons i w ih =>
    exact H.mul_mem (hw i (List.mem_cons_self ..)) (ih fun j hj => hw j (List.mem_cons_of_mem _ hj))

theorem getD_mem {H : Subgroup (Carrier .M23)} {ls : List (Carrier .M23)}
    (hls : ∀ g ∈ ls, g ∈ H) (j : Nat) : ls.getD j 1 ∈ H := by
  by_cases hj : j < ls.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hls _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (not_lt.1 hj)]
    exact H.one_mem

theorem mem_iff_of_contains {E : Subgroup (Carrier .M23)} (hc : Nat.card E = 16) (k : Fin 2)
    (hk : ∀ x ∈ invs16 k, x ∈ E) : ∀ x, x ∈ E ↔ x = 1 ∨ x ∈ invs16 k := by
  classical
  obtain ⟨hlen, hnd, hall⟩ := invs16_spec k
  have : Fintype (Carrier .M23) := Fintype.ofFinite _
  intro x
  constructor
  · intro hx
    by_contra hcon
    push Not at hcon
    let U : Finset (Carrier .M23) := insert 1 (invs16 k).toFinset
    have hU : U.card = 16 := by
      rw [Finset.card_insert_of_notMem, List.toFinset_card_of_nodup hnd, hlen]
      simp only [List.mem_toFinset]
      intro h1
      exact (hall 1 h1).1 rfl
    let Ef : Finset (Carrier .M23) := Finset.univ.filter (· ∈ E)
    have hEf : Ef.card = 16 := by
      rw [← hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hUE : insert x U ⊆ Ef := by
      intro y hy
      simp only [Finset.mem_insert, List.mem_toFinset, U] at hy
      simp only [Ef, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with rfl | rfl | hy
      · exact hx
      · exact E.one_mem
      · exact hk y hy
    have hcard : (insert x U).card = 17 := by
      rw [Finset.card_insert_of_notMem, hU]
      simp only [Finset.mem_insert, List.mem_toFinset, U, not_or]
      exact ⟨hcon.1, hcon.2⟩
    have := Finset.card_le_card hUE
    omega
  · rintro (rfl | hx)
    · exact E.one_mem
    · exact hk x hx

section Bridge

theorem tab_getD (l : List (Carrier .M23)) (j : Nat) :
    tab (l.getD j 1) = (l.map tab).getD j idTab := by
  by_cases hj : j < l.length
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj),
      List.getElem_map]
  · rw [List.getD_eq_default _ _ (not_lt.1 hj),
      List.getD_eq_default _ _ (by simpa using not_lt.1 hj), tab_one]

theorem tab_letters : [genA, genB, genBi].map tab = letterTabs := by
  simp only [List.map_cons, List.map_nil, tab_genA, tab_genB, tab_genBi, letterTabs]

@[expose] def tEl : Carrier .M23 := wordElt sylowGens tWordS

@[expose] def mEl : Carrier .M23 := wordElt [genA, genB, genBi] mWord

@[expose] def bEl (i : Nat) : Carrier .M23 := wordElt [genA, genB, genBi] (bWords.getD i [])

theorem tab_tEl : tab tEl = tTab := by
  rw [tEl, tab_wordElt, tab_sylowGens]
  rfl

theorem tab_mEl : tab mEl = mTab := by
  rw [mEl, tab_wordElt, tab_letters]
  rfl

theorem tab_bEl (i : Nat) : tab (bEl i) = bTab i := by
  rw [bEl, tab_wordElt, tab_letters]
  rfl

theorem fusionCheck_spec :
    (isInv tTab = true ∧ (∀ g ∈ gensTab, comm tTab g = true) ∧
      (∀ y ∈ span gensTab, (∀ g ∈ gensTab, comm y g = true) → y = idTab ∨ y = tTab)) ∧
    (invWords.length = 7 ∧ ∀ i : Fin 7, (∀ j ∈ invWords.getD i [],
      isInv ((span gensTab).getD j idTab) = true) ∧
      wordTab (span gensTab) (invWords.getD i []) = gensTab.getD i idTab) ∧
    (∀ k : Fin 2, (∀ g ∈ gensTab, normOK (elemTabs k) g = true) ∧ tTab ∈ elemTabs k ∧
      normOK (elemTabs k) mTab = true) ∧
    comm mTab tTab = false ∧
    (bWords.length = 15 ∧ ∀ i : Fin 15, normOK (elemTabs 1) (bTab i) = true ∧
      tmul (bTab i) tTab = tmul ((elemTabs 1).getD i idTab) (bTab i)) := by
  have h := Certificates.certificate24470
  simp only [fusionCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem conj_mem_of_normOK {k : Fin 2} {g : Carrier .M23} (h : normOK (elemTabs k) (tab g) = true) :
    ∀ x ∈ invs16 k, ∃ y ∈ invs16 k, g * x * g⁻¹ = y := by
  intro x hx
  unfold normOK at h
  simp only [List.all_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  have hxt : tab x ∈ elemTabs k := by
    rw [← tab_invs16]
    exact List.mem_map_of_mem hx
  obtain ⟨yt, hyt, hxy⟩ := h _ hxt
  rw [← tab_invs16] at hyt
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hyt
  refine ⟨y, hy, ?_⟩
  have : g * x = y * g := tab_injective (by rw [tab_mul, tab_mul]; exact hxy)
  rw [this]
  group

theorem normalizes_of_normOK {k : Fin 2} {E : Subgroup (Carrier .M23)}
    (hE : ∀ x, x ∈ E ↔ x = 1 ∨ x ∈ invs16 k) {g : Carrier .M23}
    (h : normOK (elemTabs k) (tab g) = true) : ∀ x, x ∈ E ↔ g * x * g⁻¹ ∈ E := by
  apply forall_mem_iff_of_forall_mem
  intro x hx
  rcases (hE x).1 hx with rfl | hx'
  · simp
  · obtain ⟨y, hy, hxy⟩ := conj_mem_of_normOK h x hx'
    rw [hxy, hE]
    exact Or.inr hy

theorem exists_pair (h2E : TwoEAt sylowS) :
    ∃ F1 F2 : Subgroup (Carrier .M23), F1 ≤ sylowS ∧ F2 ≤ sylowS ∧ F1 ≠ F2 ∧ ElemAb F1 ∧
      ElemAb F2 ∧ Nat.card F1 = 16 ∧ Nat.card F2 = 16 ∧
      (∀ F : Subgroup (Carrier .M23), F ≤ sylowS → ElemAb F → Nat.card F = 16 →
        F = F1 ∨ F = F2) ∧
      (∀ x, (∀ e ∈ F1, x * e = e * x) → x ∈ F1) ∧
      (∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) ∧ (∀ x, x ∈ F2 ↔ x = 1 ∨ x ∈ invs16 0) := by
  have hS := (Certificates.certificate24160).1
  have hE := (Certificates.certificate24160).2
  obtain ⟨Ea, Eb, ga, gb, hEaS, hEbS, hne, hea, heb, hca, hcb, hcl, hcena, hcenb, -, -⟩ := h2E
  obtain ⟨ka, hka⟩ := exists_k_of_le hS hE hea.2 (by rw [hca]; norm_num) hEaS
  obtain ⟨kb, hkb⟩ := exists_k_of_le hS hE heb.2 (by rw [hcb]; norm_num) hEbS
  have hmema := mem_iff_of_contains hca ka hka
  have hmemb := mem_iff_of_contains hcb kb hkb
  have hk : ka ≠ kb := by
    intro h
    apply hne
    ext x
    rw [hmema, hmemb, h]
  have hdis : ∀ a b : Fin 2, a ≠ b → (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by decide
  rcases hdis ka kb hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1] at hmema
    rw [h2] at hmemb
    exact ⟨Ea, Eb, hEaS, hEbS, hne, hea, heb, hca, hcb, hcl, hcena, hmema, hmemb⟩
  · rw [h1] at hmema
    rw [h2] at hmemb
    exact ⟨Eb, Ea, hEbS, hEaS, hne.symm, heb, hea, hcb, hca,
      fun F hF hFe hFc => (hcl F hF hFe hFc).symm, hcenb, hmemb, hmema⟩

theorem closure_involutions :
    Subgroup.closure {a : Carrier .M23 | a ∈ sylowS ∧ a * a = 1} = sylowS := by
  have hS := (Certificates.certificate24160).1
  obtain ⟨-, ⟨hlen, hInv⟩, -, -, -⟩ := fusionCheck_spec
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun a ha => ha.1
  · refine (Subgroup.closure_le _).2 fun g hg => ?_
    have hglen : sylowGens.length = 7 := by simp [sylowGens, sylowWords]
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
    have hi7 : i < 7 := hglen ▸ hi
    obtain ⟨hinv, hword⟩ := hInv ⟨i, hi7⟩
    let H : Subgroup (Carrier .M23) := Subgroup.closure {a : Carrier .M23 | a ∈ sylowS ∧ a * a = 1}
    have htabspan : ∀ j, tab ((spanE sylowGens).getD j 1) = (span gensTab).getD j idTab := by
      intro j
      rw [tab_getD, tab_spanE, tab_sylowGens]
    have hspanS : ∀ j, (spanE sylowGens).getD j 1 ∈ sylowS := by
      intro j
      refine getD_mem (fun x hx => ?_) j
      exact (mem_sylowS_iff hS x).2 hx
    have hmemH : ∀ j ∈ invWords.getD i [], (spanE sylowGens).getD j 1 ∈ H := by
      intro j hj
      apply Subgroup.subset_closure
      refine ⟨hspanS j, ?_⟩
      have h1 := hinv j hj
      rw [← htabspan] at h1
      unfold isInv at h1
      have h2 := of_decide_eq_true h1
      exact tab_injective (by rw [tab_mul, tab_one]; exact h2.2)
    have heq : wordElt (spanE sylowGens) (invWords.getD i []) = sylowGens.getD i 1 := by
      apply tab_injective
      rw [tab_wordElt, tab_spanE, tab_sylowGens, hword, tab_getD, tab_sylowGens]
    have hmain := wordElt_mem hmemH
    rw [heq, List.getD_eq_getElem _ _ hi] at hmain
    exact hmain

theorem exists_conj_tEl {F1 : Subgroup (Carrier .M23)}
    (hmem1 : ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1) :
    ∀ g ∈ invs16 1, ∃ b : Carrier .M23, (∀ x, x ∈ F1 ↔ b * x * b⁻¹ ∈ F1) ∧ b * tEl * b⁻¹ = g := by
  obtain ⟨-, -, -, -, hb⟩ := fusionCheck_spec
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have hi15 : i < 15 := by simpa [(invs16_spec 1).1] using hi
  obtain ⟨hbn, hbc⟩ := hb.2 ⟨i, hi15⟩
  refine ⟨bEl i, normalizes_of_normOK hmem1 (by rw [tab_bEl]; exact hbn), ?_⟩
  have hgt : (elemTabs 1).getD i idTab = tab ((invs16 1)[i]) := by
    rw [← tab_invs16 1, ← tab_one, List.getD_map, List.getD_eq_getElem _ _ hi]
    rfl
  have : bEl i * tEl = (invs16 1)[i] * bEl i :=
    tab_injective (by rw [tab_mul, tab_mul, tab_bEl, tab_tEl, ← hgt]; exact hbc)
  rw [this]
  group
  rfl

theorem tEl_involution : tEl * tEl = 1 ∧ tEl ≠ 1 := by
  obtain ⟨⟨hZt, -, -⟩, -⟩ := fusionCheck_spec
  unfold isInv at hZt
  have h := of_decide_eq_true hZt
  exact ⟨tab_injective (by rw [tab_mul, tab_one, tab_tEl]; exact h.2),
    fun h1 => h.1 (by rw [← tab_tEl, h1, tab_one])⟩

theorem sylowS_index_odd :
    ¬ 2 ∣ sylowS.index := by
  have hS := (Certificates.certificate24160).1
  have h1 := Subgroup.card_mul_index sylowS
  have hM : Nat.card (Carrier .M23) = 10200960 := CFSG.Sporadic.Schreier.m23_card
  rw [card_sylowS hS, hM] at h1
  norm_num at h1
  omega

theorem m23_fusionData_pinned
    (h2E : TwoEAt sylowS) :
    ∃ F1 F2 : Subgroup (Carrier .M23),
      FusionData (⊤ : Subgroup (Carrier .M23)) tEl sylowS F1 F2 mEl ∧
        NData (⊤ : Subgroup (Carrier .M23)) F1 ∧ ∀ x, x ∈ F1 ↔ x = 1 ∨ x ∈ invs16 1 := by
  have hS := (Certificates.certificate24160).1
  obtain ⟨⟨hZt, hZc, hZe⟩, -, hN, hm, hb⟩ := fusionCheck_spec
  obtain ⟨F1, F2, hF1S, hF2S, hne, hea1, hea2, hc1, hc2, honly, hself1, hmem1, hmem2⟩ :=
    exists_pair h2E
  have hgens : ∀ g ∈ sylowGens, g ∈ sylowS := fun g hg => sylowGens_mem hg
  have htabgen : ∀ g ∈ sylowGens, tab g ∈ gensTab := fun g hg => by
    rw [← tab_sylowGens]
    exact List.mem_map_of_mem hg
  have hP2 : IsPGroup 2 sylowS := IsPGroup.of_card (card_sylowS hS)
  have hidx : ¬ 2 ∣ (sylowS.relIndex ⊤) := by
    rw [Subgroup.relIndex_top_right]
    exact sylowS_index_odd
  have htS : tEl ∈ sylowS := wordElt_mem fun j _ => getD_mem hgens j
  have hcommt : ∀ g ∈ sylowGens, tEl * g = g * tEl := by
    intro g hg
    have := of_decide_eq_true (hZc _ (htabgen g hg))
    exact tab_injective (by rw [tab_mul, tab_mul, tab_tEl]; exact this)
  have htcent : ∀ x ∈ sylowS, tEl * x = x * tEl := by
    intro x hx
    have hle : sylowS ≤ Subgroup.centralizer ({tEl} : Set (Carrier .M23)) := by
      refine (Subgroup.closure_le _).2 fun g hg => ?_
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcommt g hg).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm
  have hsylow_norm : ∀ k : Fin 2, ∀ E : Subgroup (Carrier .M23),
      (∀ x, x ∈ E ↔ x = 1 ∨ x ∈ invs16 k) →
      sylowS ≤ Subgroup.normalizer (E : Set (Carrier .M23)) := by
    intro k E hE
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    exact Subgroup.mem_normalizer_iff.2
      (normalizes_of_normOK hE ((hN k).1 _ (htabgen g hg)))
  have htF : ∀ k : Fin 2, ∀ E : Subgroup (Carrier .M23),
      (∀ x, x ∈ E ↔ x = 1 ∨ x ∈ invs16 k) → tEl ∈ E := by
    intro k E hE
    have h1 := (hN k).2.1
    rw [← tab_invs16] at h1
    obtain ⟨x, hx, hxt⟩ := List.mem_map.1 h1
    have : x = tEl := tab_injective (by rw [hxt, tab_tEl])
    rw [(hE tEl)]
    exact Or.inr (this ▸ hx)
  refine ⟨F1, F2, ⟨le_top, hP2, hidx, htS, htcent, ?_, closure_involutions, hF1S, hF2S, hea1.1,
    hea2.1, hea1.2, hea2.2, hc1, hc2, hne,
    fun F hF hc hs hcard => honly F hF ⟨hc, hs⟩ hcard, htF 1 F1 hmem1, htF 0 F2 hmem2,
    Subgroup.mem_top _, ?_, ?_, ?_⟩, ?_, hmem1⟩
  · intro x hx hxc
    have hxt : tab x ∈ span gensTab := tab_mem_span_of_mem_sylowS hS hx
    have := hZe _ hxt (fun g hg => by
      obtain ⟨g', hg', rfl⟩ := List.mem_map.1 (tab_sylowGens ▸ hg)
      exact decide_eq_true (by rw [← tab_mul, ← tab_mul, hxc g' (hgens g' hg')]))
    rcases this with h | h
    · left
      exact tab_injective (by rw [h, tab_one])
    · right
      exact tab_injective (by rw [h, tab_tEl])
  · exact normalizes_of_normOK hmem1 (by rw [tab_mEl]; exact (hN 1).2.2)
  · exact normalizes_of_normOK hmem2 (by rw [tab_mEl]; exact (hN 0).2.2)
  · intro hcon
    have h1 : mEl * tEl = tEl * mEl := by
      have : mEl * tEl = mEl * tEl * mEl⁻¹ * mEl := by group
      rw [this, hcon]
    have := congrArg tab h1
    rw [tab_mul, tab_mul, tab_mEl, tab_tEl] at this
    have h2 : M23Sylow.comm mTab tTab = true := by
      unfold M23Sylow.comm
      exact decide_eq_true this
    rw [hm] at h2
    exact Bool.false_ne_true h2
  · refine ⟨le_top, hea1.1, hea1.2, hc1, fun x _ hx => hself1 x hx, ?_, ?_⟩
    · have hle : sylowS ≤ Subgroup.normalizer (F1 : Set (Carrier .M23)) ⊓ ⊤ :=
        le_inf (hsylow_norm 1 F1 hmem1) le_top
      have := Subgroup.card_dvd_of_le hle
      rwa [card_sylowS hS] at this
    · intro f hf hf1 f' hf' hf'1
      have hfm : f ∈ invs16 1 := ((hmem1 f).1 hf).resolve_left hf1
      have hf'm : f' ∈ invs16 1 := ((hmem1 f').1 hf').resolve_left hf'1
      have key := exists_conj_tEl hmem1
      obtain ⟨b1, hb1n, hb1⟩ := key f hfm
      obtain ⟨b2, hb2n, hb2⟩ := key f' hf'm
      refine ⟨b2 * b1⁻¹, Subgroup.mem_top _, ?_, ?_⟩
      · have hn1 : b1 ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
          Subgroup.mem_normalizer_iff.2 hb1n
        have hn2 : b2 ∈ Subgroup.normalizer (F1 : Set (Carrier .M23)) :=
          Subgroup.mem_normalizer_iff.2 hb2n
        exact Subgroup.mem_normalizer_iff.1
          (Subgroup.mul_mem _ hn2 (Subgroup.inv_mem _ hn1))
      · calc b2 * b1⁻¹ * f * (b2 * b1⁻¹)⁻¹ = b2 * (b1⁻¹ * f * b1) * b2⁻¹ := by group
          _ = b2 * tEl * b2⁻¹ := by rw [show b1⁻¹ * f * b1 = tEl by rw [← hb1]; group]
          _ = f' := hb2

end Bridge

end CFSG.EvenSporadicStandard.M23Std

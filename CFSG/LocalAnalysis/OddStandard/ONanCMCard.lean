module

public import CFSG.LocalAnalysis.OddStandard.ONanDefs
public import Certificates.Certificate6145
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.OddStandard.ONanRec

open CFSG.CosetTable

namespace CM

theorem ap_ofFn {m : ℕ} (f : Fin m → ℕ) {i : ℕ} (hi : i < m) :
    ap (Array.ofFn f) i = f ⟨i, hi⟩ := by
  rw [ap, getElem!_pos (Array.ofFn f) i (by simpa using hi), Array.getElem_ofFn]

theorem compTab_ap {n : ℕ} (s t : Tab) {i : ℕ} (hi : i < n) :
    ap (compTab n s t) i = ap s (ap t i) := by
  rw [compTab, ap_ofFn _ hi]

theorem idTab_ap {n i : ℕ} (hi : i < n) : ap (idTab n) i = i := by
  rw [idTab, ap_ofFn _ hi]

@[expose] def Rep (t : Tab) (g : Equiv.Perm (Fin 480)) : Prop :=
  ∀ x : Fin 480, ap t x = g x

theorem Rep.comp {t u : Tab} {g h : Equiv.Perm (Fin 480)} (ht : Rep t g) (hu : Rep u h) :
    Rep (compTab 480 t u) (g * h) := fun x => by
  rw [compTab_ap t u x.2, hu x, ht (h x), Equiv.Perm.mul_apply]

theorem rep_id : Rep (idTab 480) 1 := fun x => by
  rw [idTab_ap x.2]
  rfl

theorem Rep.unique {t : Tab} {g h : Equiv.Perm (Fin 480)} (hg : Rep t g) (hh : Rep t h) :
    g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

open scoped Classical in
@[expose] noncomputable def tabPerm (t : Tab) : Equiv.Perm (Fin 480) :=
  if h : (∀ i < 480, ap t i < 480) ∧ ∀ i < 480, ∀ j < 480, ap t i = ap t j → i = j then
    Equiv.ofBijective (fun i : Fin 480 => (⟨ap t i, h.1 i i.2⟩ : Fin 480))
      (Finite.injective_iff_bijective.1 fun i j hij =>
        Fin.ext (h.2 i i.2 j j.2 (congrArg Fin.val hij)))
  else 1

theorem rep_tabPerm {t u : Tab} (h1 : ∀ i < 480, ap t i < 480)
    (h2 : ∀ i < 480, ap u (ap t i) = i) : Rep t (tabPerm t) := by
  have hc : (∀ i < 480, ap t i < 480) ∧ ∀ i < 480, ∀ j < 480, ap t i = ap t j → i = j :=
    ⟨h1, fun i hi j hj hij => by rw [← h2 i hi, ← h2 j hj, hij]⟩
  intro x
  rw [tabPerm, dite_eq_left hc]
  rfl

theorem letters_lt (h : cmLettersOK = true) {c : ℕ} (hc : c < 12) {p : ℕ} (hp : p < 480) :
    ap cmLetters[c]! p < 480 := by
  unfold cmLettersOK at h
  rw [Bool.and_eq_true] at h
  have h1 := h.1
  rw [List.all_eq_true] at h1
  have h2 := h1 c (List.mem_range.2 hc)
  simp only [allBelow, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h2
  exact h2 p hp

theorem letters_comp (h : cmLettersOK = true) {i : ℕ} (hi : i < 6) :
    compTab 480 cmLetters[2 * i + 1]! cmLetters[2 * i]! = idTab 480 ∧
      compTab 480 cmLetters[2 * i]! cmLetters[2 * i + 1]! = idTab 480 := by
  unfold cmLettersOK at h
  rw [Bool.and_eq_true] at h
  have h1 := h.2
  rw [List.all_eq_true] at h1
  have h2 := h1 i (List.mem_range.2 hi)
  simpa only [Bool.and_eq_true, beq_iff_eq] using h2

theorem letters_inv (h : cmLettersOK = true) {i : ℕ} (hi : i < 6) {p : ℕ} (hp : p < 480) :
    ap cmLetters[2 * i + 1]! (ap cmLetters[2 * i]! p) = p ∧
      ap cmLetters[2 * i]! (ap cmLetters[2 * i + 1]! p) = p := by
  obtain ⟨h1, h2⟩ := letters_comp h hi
  refine ⟨?_, ?_⟩
  · have := congrArg (fun T => ap T p) h1
    rwa [compTab_ap _ _ hp, idTab_ap hp] at this
  · have := congrArg (fun T => ap T p) h2
    rwa [compTab_ap _ _ hp, idTab_ap hp] at this

@[expose] noncomputable def letterPerm (c : ℕ) : Equiv.Perm (Fin 480) := tabPerm cmLetters[c]!

theorem rep_letter (h : cmLettersOK = true) {c : ℕ} (hc : c < 12) :
    Rep cmLetters[c]! (letterPerm c) := by
  obtain ⟨i, hi, hci⟩ : ∃ i < 6, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega, by omega⟩
  rcases hci with rfl | rfl
  · exact rep_tabPerm (fun p hp => letters_lt h hc hp) (fun p hp => (letters_inv h hi hp).1)
  · exact rep_tabPerm (fun p hp => letters_lt h hc hp) (fun p hp => (letters_inv h hi hp).2)

theorem letterPerm_odd (h : cmLettersOK = true) {i : ℕ} (hi : i < 6) :
    letterPerm (2 * i + 1) = (letterPerm (2 * i))⁻¹ := by
  have h1 := (rep_letter h (c := 2 * i + 1) (by omega)).comp (rep_letter h (c := 2 * i) (by omega))
  rw [(letters_comp h hi).1] at h1
  exact eq_inv_of_mul_eq_one_left (h1.unique rep_id)

@[expose] noncomputable def wordPerm (w : List ℕ) : Equiv.Perm (Fin 480) := (w.map letterPerm).prod

theorem rep_wordTab (h : cmLettersOK = true) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 12) → Rep (wordTab 480 cmLetters w) (wordPerm w)
  | [], _ => by
    simpa [wordTab, wordPerm] using rep_id
  | c :: w, hw => by
    have h1 := (rep_letter h (hw c List.mem_cons_self)).comp
      (rep_wordTab h w fun d hd => hw d (List.mem_cons_of_mem _ hd))
    simpa [wordTab, wordPerm, List.foldr_cons] using h1

@[expose] noncomputable def genPerm (i : Fin 6) : Equiv.Perm (Fin 480) := letterPerm (2 * i)

@[expose] noncomputable def M480 : Subgroup (Equiv.Perm (Fin 480)) :=
  Subgroup.closure (Set.range genPerm)

theorem letterPerm_mem (h : cmLettersOK = true) {c : ℕ} (hc : c < 12) : letterPerm c ∈ M480 := by
  obtain ⟨i, hi, hci⟩ : ∃ i < 6, c = 2 * i ∨ c = 2 * i + 1 := ⟨c / 2, by omega, by omega⟩
  have hg : letterPerm (2 * i) ∈ M480 := Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
  rcases hci with rfl | rfl
  · exact hg
  · rw [letterPerm_odd h hi]
    exact inv_mem hg

theorem wordPerm_mem (h : cmLettersOK = true) :
    ∀ w : List ℕ, (∀ c ∈ w, c < 12) → wordPerm w ∈ M480
  | [], _ => by simp [wordPerm, one_mem]
  | c :: w, hw => by
    have h1 := letterPerm_mem h (hw c List.mem_cons_self)
    have h2 := wordPerm_mem h w fun d hd => hw d (List.mem_cons_of_mem _ hd)
    simpa [wordPerm] using mul_mem h1 h2

set_option maxRecDepth 20000 in
theorem relsM_eq : relsM = {r | r ∈ cmRelWords.map FreeGroup.mk} := by
  have hl : cmRelWords.map FreeGroup.mk =
      (let a := FreeGroup.of (0 : Fin 6); let b := FreeGroup.of (1 : Fin 6)
      let c := FreeGroup.of (2 : Fin 6); let d := FreeGroup.of (3 : Fin 6)
      let f := FreeGroup.of (4 : Fin 6); let g := FreeGroup.of (5 : Fin 6)
      [a ^ 2, b ^ 2, c ^ 2, d ^ 2, f ^ 2, (a * b) ^ 3, (b * c) ^ 3, (c * d) ^ 8, (a * c) ^ 2,
        (a * d) ^ 2, (a * f) ^ 2, (b * d) ^ 2, (b * f) ^ 2, (c * f) ^ 2, (d * f) ^ 2, g ^ 4,
        (a * f)⁻¹ * g ^ 2, (a * f)⁻¹ * (c * d) ^ 4,
        c * ((d * g * d * g)⁻¹ * c * (d * g * d * g)),
        d * ((c * g * c * g)⁻¹ * d * (c * g * c * g)), (b * c * d * g) ^ 5,
        g * b * (c⁻¹ * g * c) * (b⁻¹ * g * b) * (c⁻¹ * g * c), f⁻¹ * (d * g) ^ 4]) := by
    decide
  rw [hl]
  ext r
  simp only [relsM, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons,
    List.not_mem_nil, or_false]

@[expose] def code (l : Fin 6 × Bool) : ℕ := 2 * l.1.val + if l.2 then 0 else 1

theorem code_lt (l : Fin 6 × Bool) : code l < 12 := by
  have := l.1.2
  unfold code
  split <;> omega

theorem lift_mk_eq (h : cmLettersOK = true) (w : List (Fin 6 × Bool)) :
    FreeGroup.lift genPerm (FreeGroup.mk w) = wordPerm (w.map code) := by
  rw [FreeGroup.lift_mk, wordPerm, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun l _ => ?_)
  obtain ⟨i, b⟩ := l
  cases b
  · show (genPerm i)⁻¹ = letterPerm (2 * i.val + 1)
    rw [letterPerm_odd h i.2]
    rfl
  · rfl

theorem rels_ok (h1 : cmLettersOK = true) (h2 : cmRelOK = true) :
    ∀ r ∈ relsM, FreeGroup.lift genPerm r = 1 := by
  rw [relsM_eq]
  rintro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [lift_mk_eq h1]
  have hrel := List.all_eq_true.1 h2 (w.map code) (List.mem_map_of_mem (f := fun w =>
    w.map fun l => 2 * l.1.val + (if l.2 then 0 else 1)) hw)
  rw [beq_iff_eq] at hrel
  have hc : ∀ c ∈ w.map code, c < 12 := by
    intro c hc
    obtain ⟨l, -, rfl⟩ := List.mem_map.1 hc
    exact code_lt l
  have hr := rep_wordTab h1 _ hc
  change Rep (wordTab 480 cmLetters (w.map code)) _ at hr
  rw [show wordTab 480 cmLetters (w.map code) = idTab 480 from hrel] at hr
  exact hr.unique rep_id

@[expose] noncomputable def toM480 (h1 : cmLettersOK = true) (h2 : cmRelOK = true) :
    CModel →* Equiv.Perm (Fin 480) :=
  PresentedGroup.toGroup (rels_ok h1 h2)

theorem range_toM480 (h1 : cmLettersOK = true) (h2 : cmRelOK = true) :
    (toM480 h1 h2).range = M480 := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, M480]
  rfl

theorem chain_sound (h : cmLettersOK = true) :
    ∀ (Ls : List ChainLevel) (prev : List ℕ), chainOK cmLetters prev Ls = true →
      (∀ L ∈ Ls, L.base < 480) →
      ∃ S : Finset (Equiv.Perm (Fin 480)), S.card = chainProd Ls ∧
        ∀ g ∈ S, g ∈ M480 ∧ ∀ b ∈ prev, ∀ hb : b < 480, g ⟨b, hb⟩ = ⟨b, hb⟩
  | [], prev, _, _ => ⟨{1}, by simp [chainProd], fun g hg => by
      rw [Finset.mem_singleton] at hg
      subst hg
      exact ⟨one_mem _, fun _ _ _ => rfl⟩⟩
  | L :: rest, prev, hc, hb => by
    classical
    rw [chainOK, Bool.and_eq_true] at hc
    obtain ⟨hL, hrest⟩ := hc
    obtain ⟨S', hS'card, hS'⟩ := chain_sound h rest (prev ++ [L.base]) hrest
      (fun L' hL' => hb L' (List.mem_cons_of_mem _ hL'))
    have hbase : L.base < 480 := hb L List.mem_cons_self
    unfold levelOK at hL
    rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hL
    obtain ⟨hw, hnd⟩ := hL
    have hwf : ∀ qw ∈ L.words, (∀ c ∈ qw.2, c < 12) ∧
        (∀ b ∈ prev, ∀ hb : b < 480, wordPerm qw.2 ⟨b, hb⟩ = ⟨b, hb⟩) ∧
        ((wordPerm qw.2 ⟨L.base, hbase⟩ : Fin 480) : ℕ) = qw.1 := by
      intro qw hqw
      have h1 := hw qw hqw
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨hfix, hbq⟩, hlt⟩ := h1
      have hrep := rep_wordTab h qw.2 hlt
      refine ⟨hlt, fun b hbp hb' => Fin.ext ?_, ?_⟩
      · rw [← hrep ⟨b, hb'⟩]
        exact hfix b hbp
      · rw [← hrep ⟨L.base, hbase⟩]
        exact hbq
    have hndw : L.words.Nodup := hnd.of_map _
    let f : (ℕ × List ℕ) × Equiv.Perm (Fin 480) → Equiv.Perm (Fin 480) :=
      fun p => wordPerm p.1.2 * p.2
    have hinj : Set.InjOn f ↑(L.words.toFinset ×ˢ S') := by
      rintro ⟨qw, s⟩ hp ⟨qw', s'⟩ hp' hfe
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, List.mem_toFinset] at hp hp'
      have hfe' : wordPerm qw.2 * s = wordPerm qw'.2 * s' := hfe
      have hsb : s ⟨L.base, hbase⟩ = ⟨L.base, hbase⟩ :=
        (hS' s hp.2).2 L.base (List.mem_append_right _ List.mem_cons_self) hbase
      have hsb' : s' ⟨L.base, hbase⟩ = ⟨L.base, hbase⟩ :=
        (hS' s' hp'.2).2 L.base (List.mem_append_right _ List.mem_cons_self) hbase
      have hq : qw.1 = qw'.1 := by
        have := congrArg (fun g : Equiv.Perm (Fin 480) => ((g ⟨L.base, hbase⟩ : Fin 480) : ℕ)) hfe'
        simp only [Equiv.Perm.mul_apply, hsb, hsb'] at this
        rw [← (hwf qw hp.1).2.2, ← (hwf qw' hp'.1).2.2]
        exact this
      have hqw : qw = qw' := List.inj_on_of_nodup_map hnd hp.1 hp'.1 hq
      subst hqw
      have hs : s = s' := mul_left_cancel hfe'
      rw [hs]
    refine ⟨(L.words.toFinset ×ˢ S').image f, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn hinj, Finset.card_product, List.toFinset_card_of_nodup hndw,
        hS'card]
      simp [chainProd]
    · intro g hg
      obtain ⟨⟨qw, s⟩, hp, rfl⟩ := Finset.mem_image.1 hg
      simp only [Finset.mem_product, List.mem_toFinset] at hp
      obtain ⟨hlt, hfix, -⟩ := hwf qw hp.1
      refine ⟨mul_mem (wordPerm_mem h qw.2 hlt) (hS' s hp.2).1, fun b hbp hb' => ?_⟩
      show wordPerm qw.2 (s ⟨b, hb'⟩) = ⟨b, hb'⟩
      rw [(hS' s hp.2).2 b (List.mem_append_left _ hbp) hb', hfix b hbp hb']

@[expose] noncomputable def chainPerms : List ChainLevel → List (Equiv.Perm (Fin 480))
  | [] => [1]
  | L :: rest => L.words.flatMap fun qw => (chainPerms rest).map (wordPerm qw.2 * ·)

theorem chainPerms_sound (h : cmLettersOK = true) :
    ∀ (Ls : List ChainLevel) (prev : List ℕ), chainOK cmLetters prev Ls = true →
      (∀ L ∈ Ls, L.base < 480) →
      (chainPerms Ls).Nodup ∧ (chainPerms Ls).length = chainProd Ls ∧
        ∀ g ∈ chainPerms Ls, g ∈ M480 ∧ ∀ b ∈ prev, ∀ hb : b < 480, g ⟨b, hb⟩ = ⟨b, hb⟩
  | [], prev, _, _ => ⟨List.nodup_singleton 1, rfl, fun g hg => by
      rw [chainPerms, List.mem_singleton] at hg
      subst hg
      exact ⟨one_mem _, fun _ _ _ => rfl⟩⟩
  | L :: rest, prev, hc, hb => by
    rw [chainOK, Bool.and_eq_true] at hc
    obtain ⟨hL, hrest⟩ := hc
    obtain ⟨hnd', hlen', hS'⟩ := chainPerms_sound h rest (prev ++ [L.base]) hrest
      (fun L' hL' => hb L' (List.mem_cons_of_mem _ hL'))
    have hbase : L.base < 480 := hb L List.mem_cons_self
    unfold levelOK at hL
    rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hL
    obtain ⟨hw, hnd⟩ := hL
    have hwf : ∀ qw ∈ L.words, (∀ c ∈ qw.2, c < 12) ∧
        (∀ b ∈ prev, ∀ hb : b < 480, wordPerm qw.2 ⟨b, hb⟩ = ⟨b, hb⟩) ∧
        ((wordPerm qw.2 ⟨L.base, hbase⟩ : Fin 480) : ℕ) = qw.1 := by
      intro qw hqw
      have h1 := hw qw hqw
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨hfix, hbq⟩, hlt⟩ := h1
      have hrep := rep_wordTab h qw.2 hlt
      refine ⟨hlt, fun b hbp hb' => Fin.ext ?_, ?_⟩
      · rw [← hrep ⟨b, hb'⟩]
        exact hfix b hbp
      · rw [← hrep ⟨L.base, hbase⟩]
        exact hbq
    have hval : ∀ qw ∈ L.words, ∀ g ∈ (chainPerms rest).map (wordPerm qw.2 * ·),
        ((g ⟨L.base, hbase⟩ : Fin 480) : ℕ) = qw.1 := by
      intro qw hqw g hg
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      have hsb := (hS' s hs).2 L.base (List.mem_append_right _ List.mem_cons_self) hbase
      show ((wordPerm qw.2 (s ⟨L.base, hbase⟩) : Fin 480) : ℕ) = qw.1
      rw [hsb]
      exact (hwf qw hqw).2.2
    refine ⟨?_, ?_, ?_⟩
    · rw [chainPerms, List.nodup_flatMap]
      refine ⟨fun qw _ => hnd'.map (mul_right_injective _), ?_⟩
      have hpw : L.words.Pairwise (fun a b => a.1 ≠ b.1) := List.pairwise_map.1 hnd
      refine hpw.imp_of_mem fun {a b} ha hb' hab g hga hgb => hab ?_
      rw [← hval a ha g hga, ← hval b hb' g hgb]
    · rw [chainPerms, List.length_flatMap]
      simp only [List.length_map, hlen', List.map_const', List.sum_replicate, smul_eq_mul,
        chainProd, List.map_cons, List.prod_cons]
    · intro g hg
      rw [chainPerms, List.mem_flatMap] at hg
      obtain ⟨qw, hqw, hg⟩ := hg
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
      obtain ⟨hlt, hfix, -⟩ := hwf qw hqw
      refine ⟨mul_mem (wordPerm_mem h qw.2 hlt) (hS' s hs).1, fun b hbp hb' => ?_⟩
      show wordPerm qw.2 (s ⟨b, hb'⟩) = ⟨b, hb'⟩
      rw [(hS' s hs).2 b (List.mem_append_left _ hbp) hb', hfix b hbp hb']

theorem le_card_M480 (h : cmModelCheck = true) : 161280 ≤ Nat.card M480 := by
  simp only [cmModelCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, -⟩, hch⟩, hprod⟩ := h
  obtain ⟨S, hS, hSM⟩ := chain_sound h1 cmChain [] hch (by decide)
  have hsub : (S : Set (Equiv.Perm (Fin 480))) ⊆ (M480 : Set (Equiv.Perm (Fin 480))) :=
    fun g hg => (hSM g hg).1
  calc 161280 = S.card := by rw [hS, hprod]
    _ = (S : Set (Equiv.Perm (Fin 480))).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ (M480 : Set (Equiv.Perm (Fin 480))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card M480 := (Nat.card_coe_set_eq _).symm

abbrev CMBound : Prop := Finite (PG 6 cmRelWords) ∧ Nat.card (PG 6 cmRelWords) ≤ 161280

theorem card_CModel_le (h : CMBound) :
    Finite CModel ∧ Nat.card CModel ≤ 161280 := by
  have e : CModel = PG 6 cmRelWords := by
    show PresentedGroup relsM = _
    rw [relsM_eq]
  rw [e]
  exact h

theorem lettersOK_of (hM : cmModelCheck = true) : cmLettersOK = true := by
  simp only [cmModelCheck, Bool.and_eq_true] at hM
  exact hM.1.1.1

theorem relOK_of (hM : cmModelCheck = true) : cmRelOK = true := by
  simp only [cmModelCheck, Bool.and_eq_true] at hM
  exact hM.1.1.2

theorem card_CModel (hB : CMBound) (hM : cmModelCheck = true) :
    Nat.card CModel = 161280 := by
  obtain ⟨hfin, hle⟩ := card_CModel_le hB
  have h1 := lettersOK_of hM
  have h2 := relOK_of hM
  have hr := le_card_M480 hM
  rw [← range_toM480 h1 h2] at hr
  have hrc : Nat.card (toM480 h1 h2).range ≤ Nat.card CModel :=
    Nat.card_le_card_of_surjective _ (toM480 h1 h2).rangeRestrict_surjective
  omega

theorem toM480_injective (hB : CMBound) (hM : cmModelCheck = true) :
    Function.Injective (toM480 (lettersOK_of hM) (relOK_of hM)) := by
  have hc := card_CModel hB hM
  obtain ⟨hfin, -⟩ := card_CModel_le hB
  have hr : 161280 ≤ Nat.card (toM480 (lettersOK_of hM) (relOK_of hM)).range := by
    rw [range_toM480]
    exact le_card_M480 hM
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  have h1 := Subgroup.card_mul_index (toM480 (lettersOK_of hM) (relOK_of hM)).ker
  rw [Subgroup.index_ker, hc] at h1
  have hpos : 0 < Nat.card (toM480 (lettersOK_of hM) (relOK_of hM)).ker := Nat.card_pos
  generalize Nat.card (toM480 (lettersOK_of hM) (relOK_of hM)).ker = k at h1 hpos ⊢
  generalize Nat.card (toM480 (lettersOK_of hM) (relOK_of hM)).range = r at h1 hr
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have h3 : 2 * 161280 ≤ k * r := Nat.mul_le_mul hk2 hr
  rw [h1] at h3
  norm_num at h3

@[expose] noncomputable def equivM480 (hB : CMBound) (hM : cmModelCheck = true) :
    CModel ≃* M480 :=
  (MonoidHom.ofInjective (toM480_injective hB hM)).trans
    (MulEquiv.subgroupCongr (range_toM480 (lettersOK_of hM) (relOK_of hM)))

theorem equivM480_of (hB : CMBound) (hM : cmModelCheck = true) (i : Fin 6) :
    ((equivM480 hB hM (PresentedGroup.of i) : M480) : Equiv.Perm (Fin 480)) = genPerm i := by
  show (toM480 (lettersOK_of hM) (relOK_of hM)) (PresentedGroup.of i) = genPerm i
  exact PresentedGroup.toGroup.of _

theorem card_M480 (hB : CMBound) (hM : cmModelCheck = true) :
    Nat.card M480 = 161280 := by
  rw [← Nat.card_congr (equivM480 hB hM).toEquiv, card_CModel hB hM]

theorem mem_chainPerms (hB : CMBound) (hM : cmModelCheck = true)
    {g : Equiv.Perm (Fin 480)} (hg : g ∈ M480) : g ∈ chainPerms cmChain := by
  classical
  have hM' := hM
  simp only [cmModelCheck, Bool.and_eq_true, beq_iff_eq] at hM'
  obtain ⟨⟨⟨h1, -⟩, hch⟩, hprod⟩ := hM'
  obtain ⟨hnd, hlen, hsub⟩ := chainPerms_sound h1 cmChain [] hch (by decide)
  set F := (chainPerms cmChain).toFinset with hF
  have hFc : F.card = 161280 := by rw [hF, List.toFinset_card_of_nodup hnd, hlen, hprod]
  have hFs : (F : Set (Equiv.Perm (Fin 480))) ⊆ (M480 : Set (Equiv.Perm (Fin 480))) := by
    intro x hx
    rw [hF, Finset.mem_coe, List.mem_toFinset] at hx
    exact (hsub x hx).1
  have heq : (F : Set (Equiv.Perm (Fin 480))) = (M480 : Set (Equiv.Perm (Fin 480))) := by
    refine Set.eq_of_subset_of_ncard_le hFs ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, hFc, ← Nat.card_coe_set_eq, ← card_M480 hB hM]
    rfl
  have : g ∈ (F : Set (Equiv.Perm (Fin 480))) := by
    rw [heq]
    exact hg
  rw [hF, Finset.mem_coe, List.mem_toFinset] at this
  exact this

theorem cmModelCheck_of
    (h : cmLettersOK = true ∧ cmRelOK = true ∧ chainOK cmLetters [] cmChain = true ∧
      chainProd cmChain = 161280) : cmModelCheck = true := by
  simp only [cmModelCheck, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩

theorem cmBoundCheck_cert : CMBound :=
  Certificates.certificate6145.1

theorem cmModelCheck_cert : cmModelCheck = true :=
  cmModelCheck_of Certificates.certificate6145.2

theorem card_CModel_cert : Nat.card CModel = 161280 :=
  card_CModel cmBoundCheck_cert cmModelCheck_cert

@[expose] noncomputable def equivM480_cert : CModel ≃* M480 :=
  equivM480 cmBoundCheck_cert cmModelCheck_cert

end CM

end CFSG.OddStandard.ONanRec

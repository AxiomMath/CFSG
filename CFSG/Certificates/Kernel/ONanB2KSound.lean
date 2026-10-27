
module

public import Certificates.Data.Kernel.ONanB2K
public import CFSG.Certificates.Kernel.ONanCMKSound
public import CFSG.LocalAnalysis.OddStandard.ONanB2Facts

public section

namespace CFSG.OddStandard.ONanRec.B2K

open CFSG.OddStandard.ONanRec.CM CFSG.OddStandard.ONanRec.CMK

structure Hyp : Prop where
  letters : lettersK = true
  bound : CMBound
  model : cmModelCheck = true
  base : b2Base = cmChain.map ChainLevel.base

theorem ptK_eq (hL : lettersK = true) {w : List ℕ} (hw : ∀ c ∈ w, c < 12) {x : ℕ}
    (hx : x < 480) : ptK w x = (wordPerm w ⟨x, hx⟩ : ℕ) := by
  rw [← (wordTab_ap hL w hw hx).1]
  exact rep_wordTab (cmLettersOK_of hL) w hw ⟨x, hx⟩

theorem wordPerm_nil : wordPerm [] = 1 := by simp [wordPerm]

theorem chainPerms_eq_of_base (h : cmLettersOK = true) :
    ∀ (Ls : List ChainLevel) (prev : List ℕ), chainOK cmLetters prev Ls = true →
      (∀ L ∈ Ls, L.base < 480) → ∀ g ∈ chainPerms Ls, ∀ g' ∈ chainPerms Ls,
      (∀ L ∈ Ls, ∀ hb : L.base < 480, g ⟨L.base, hb⟩ = g' ⟨L.base, hb⟩) → g = g'
  | [], _, _, _, g, hg, g', hg', _ => by
    rw [chainPerms, List.mem_singleton] at hg hg'
    rw [hg, hg']
  | L :: rest, prev, hc, hb, g, hg, g', hg', hgb => by
    rw [chainOK, Bool.and_eq_true] at hc
    obtain ⟨hL, hrest⟩ := hc
    have hrb : ∀ L' ∈ rest, L'.base < 480 := fun L' hL' => hb L' (List.mem_cons_of_mem _ hL')
    obtain ⟨-, -, hS'⟩ := chainPerms_sound h rest (prev ++ [L.base]) hrest hrb
    have hbase : L.base < 480 := hb L List.mem_cons_self
    unfold levelOK at hL
    rw [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hL
    obtain ⟨hw, hnd⟩ := hL
    have htarget : ∀ qw ∈ L.words, ((wordPerm qw.2 ⟨L.base, hbase⟩ : Fin 480) : ℕ) = qw.1 := by
      intro qw hqw
      have h1 := hw qw hqw
      simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
      obtain ⟨⟨-, hbq⟩, hlt⟩ := h1
      rw [← rep_wordTab h qw.2 hlt ⟨L.base, hbase⟩]
      exact hbq
    rw [chainPerms, List.mem_flatMap] at hg hg'
    obtain ⟨qw, hqw, hg⟩ := hg
    obtain ⟨qw', hqw', hg'⟩ := hg'
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
    obtain ⟨s', hs', rfl⟩ := List.mem_map.1 hg'
    have hsb := (hS' s hs).2 L.base (List.mem_append_right _ List.mem_cons_self) hbase
    have hsb' := (hS' s' hs').2 L.base (List.mem_append_right _ List.mem_cons_self) hbase
    have e0 := hgb L List.mem_cons_self hbase
    simp only [Equiv.Perm.mul_apply, hsb, hsb'] at e0
    have hq1 : qw.1 = qw'.1 := by rw [← htarget qw hqw, ← htarget qw' hqw', e0]
    have hqq : qw = qw' := List.inj_on_of_nodup_map hnd hqw hqw' hq1
    subst hqq
    have hss : s = s' := chainPerms_eq_of_base h rest (prev ++ [L.base]) hrest hrb s hs s' hs'
      fun L' hL' hb' => by
        have e1 := hgb L' (List.mem_cons_of_mem _ hL') hb'
        simp only [Equiv.Perm.mul_apply] at e1
        exact (wordPerm qw.2).injective e1
    rw [hss]

theorem eq_of_base (H : Hyp) {g g' : Equiv.Perm (Fin 480)} (hg : g ∈ M480) (hg' : g' ∈ M480)
    (hb : ∀ b ∈ b2Base, ∀ hb : b < 480, g ⟨b, hb⟩ = g' ⟨b, hb⟩) : g = g' := by
  have hM' := H.model
  simp only [cmModelCheck, Bool.and_eq_true, beq_iff_eq] at hM'
  obtain ⟨⟨⟨h1, -⟩, hch⟩, -⟩ := hM'
  refine chainPerms_eq_of_base h1 cmChain [] hch (by decide) g (mem_chainPerms H.bound H.model hg)
    g' (mem_chainPerms H.bound H.model hg') fun L hL hb' => hb L.base ?_ hb'
  rw [H.base]
  exact List.mem_map_of_mem hL

theorem lt480_of_mem_base {b : ℕ} (hb : b ∈ b2Base) : b < 480 := by
  have : b = 0 ∨ b = 56 ∨ b = 2 := by simpa [b2Base] using hb
  omega

theorem eqB_iff (H : Hyp) {u v : List ℕ} (hu : ∀ c ∈ u, c < 12) (hv : ∀ c ∈ v, c < 12) :
    eqB u v = true ↔ wordPerm u = wordPerm v := by
  have hl := cmLettersOK_of H.letters
  unfold eqB
  rw [List.all_eq_true]
  constructor
  · intro he
    refine eq_of_base H (wordPerm_mem hl u hu) (wordPerm_mem hl v hv) fun b hb hb' => Fin.ext ?_
    have e := he b hb
    rwa [beq_iff_eq, ptK_eq H.letters hu hb', ptK_eq H.letters hv hb'] at e
  · intro he b hb
    have hb' := lt480_of_mem_base hb
    rw [beq_iff_eq, ptK_eq H.letters hu hb', ptK_eq H.letters hv hb', he]

theorem eqB_eq (H : Hyp) {u v : List ℕ} (hu : ∀ c ∈ u, c < 12) (hv : ∀ c ∈ v, c < 12)
    (h : eqB u v = true) : wordPerm u = wordPerm v :=
  (eqB_iff H hu hv).1 h

theorem eqB_ne (H : Hyp) {u v : List ℕ} (hu : ∀ c ∈ u, c < 12) (hv : ∀ c ∈ v, c < 12)
    (h : eqB u v = false) : wordPerm u ≠ wordPerm v := fun e => by
  rw [(eqB_iff H hu hv).2 e] at h
  exact Bool.noConfusion h

theorem allNeB_sound (H : Hyp) : ∀ ws : List (List ℕ), (∀ w ∈ ws, ∀ c ∈ w, c < 12) →
    allNeB ws = true → (ws.map wordPerm).Nodup
  | [], _, _ => List.nodup_nil
  | u :: us, hws, h => by
    rw [allNeB, Bool.and_eq_true, List.all_eq_true] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, allNeB_sound H us (fun w hw => hws w (List.mem_cons_of_mem _ hw)) h.2⟩
    obtain ⟨v, hv, he⟩ := List.mem_map.1 hm
    have h1 := h.1 v hv
    rw [Bool.not_eq_true'] at h1
    exact eqB_ne H (hws u List.mem_cons_self) (hws v (List.mem_cons_of_mem _ hv)) h1 he.symm

theorem incK_pairwise : ∀ l : List ℕ, incK l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [a], _ => List.pairwise_singleton _ a
  | a :: b :: l, h => by
    simp only [incK, Bool.and_eq_true, Nat.blt_eq] at h
    have ih := incK_pairwise (b :: l) h.2
    refine List.Pairwise.cons (fun c hc => ?_) ih
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons ih hc)

@[expose] noncomputable def centW (rs : List (List ℕ)) : Subgroup (Equiv.Perm (Fin 480)) where
  carrier := {m | m ∈ M480 ∧ ∀ r ∈ rs, m * wordPerm r = wordPerm r * m}
  one_mem' := ⟨one_mem _, fun r _ => by simp⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨mul_mem ha.1 hb.1, fun r hr =>
      (Commute.mul_left (ha.2 r hr : Commute a (wordPerm r)) (hb.2 r hr)).eq⟩
  inv_mem' := fun {a} ha => ⟨inv_mem ha.1, fun r hr => (Commute.inv_left (ha.2 r hr :
    Commute a (wordPerm r))).eq⟩

theorem mem_centW {rs : List (List ℕ)} {m : Equiv.Perm (Fin 480)} :
    m ∈ centW rs ↔ m ∈ M480 ∧ ∀ r ∈ rs, m * wordPerm r = wordPerm r * m :=
  Iff.rfl

@[expose] noncomputable def keyP (rs : List (List ℕ)) (ps : List (ℕ × ℕ))
    (g : Equiv.Perm (Fin 480)) : ℕ :=
  ps.foldl (fun acc cp => acc * 480 +
    ((g * wordPerm (rs.getD cp.1 []) * g⁻¹) ⟨cp.2 % 480, Nat.mod_lt _ (by norm_num)⟩ : ℕ)) 0

theorem lt12_getD {rs : List (List ℕ)} (hrs : ∀ r ∈ rs, ∀ c ∈ r, c < 12) (i : ℕ) :
    ∀ c ∈ rs.getD i [], c < 12 := by
  by_cases hi : i < rs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hrs _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

theorem orbKey_eq (H : Hyp) {rs : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hrs : ∀ r ∈ rs, ∀ c ∈ r, c < 12) (hps : ∀ cp ∈ ps, cp.2 < 480) {w : List ℕ}
    (hw : ∀ c ∈ w, c < 12) : orbKey rs ps w = keyP rs ps (wordPerm w) := by
  have hl := cmLettersOK_of H.letters
  unfold orbKey keyP
  refine List.foldl_ext _ _ _ fun acc cp hcp => ?_
  have hp := hps cp hcp
  have hu : ∀ c ∈ w ++ rs.getD cp.1 [] ++ invWord w, c < 12 :=
    lt12_append (lt12_append hw (lt12_getD hrs cp.1)) (invWord_lt hw)
  have e : (⟨cp.2 % 480, Nat.mod_lt _ (by norm_num)⟩ : Fin 480) = ⟨cp.2, hp⟩ :=
    Fin.ext (Nat.mod_eq_of_lt hp)
  rw [ptK_eq H.letters hu hp, wordPerm_append, wordPerm_append, wordPerm_inv hl hw, e]

theorem keyP_eq {rs : List (List ℕ)} (ps : List (ℕ × ℕ)) {g g' : Equiv.Perm (Fin 480)}
    (hm : g⁻¹ * g' ∈ centW rs) : keyP rs ps g = keyP rs ps g' := by
  have hX : ∀ c, g⁻¹ * g' * wordPerm (rs.getD c []) = wordPerm (rs.getD c []) * (g⁻¹ * g') := by
    intro c
    by_cases hc : c < rs.length
    · rw [List.getD_eq_getElem _ _ hc]
      exact (mem_centW.1 hm).2 _ (List.getElem_mem hc)
    · rw [List.getD_eq_default _ _ (by omega), wordPerm_nil, mul_one, one_mul]
  have hc : ∀ c, g * wordPerm (rs.getD c []) * g⁻¹ = g' * wordPerm (rs.getD c []) * g'⁻¹ := by
    intro c
    have e := hX c
    calc g * wordPerm (rs.getD c []) * g⁻¹
        = g * (wordPerm (rs.getD c []) * (g⁻¹ * g')) * g'⁻¹ := by group
      _ = g * (g⁻¹ * g' * wordPerm (rs.getD c [])) * g'⁻¹ := by rw [e]
      _ = g' * wordPerm (rs.getD c []) * g'⁻¹ := by group
  unfold keyP
  simp only [hc]

theorem orbK_card (H : Hyp) {rs : List (List ℕ)} {ps : List (ℕ × ℕ)} {n : ℕ}
    {ws : List (List ℕ)} (hrs : ∀ r ∈ rs, ∀ c ∈ r, c < 12) (hps : ∀ cp ∈ ps, cp.2 < 480)
    (h : orbK rs ps n ws = true) : n * Nat.card (centW rs) ≤ 161280 := by
  classical
  have hl := cmLettersOK_of H.letters
  simp only [orbK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨hlen, hws⟩, hinc⟩ := h
  have hnd : (ws.map (orbKey rs ps)).Nodup := (incK_pairwise _ hinc).imp ne_of_lt
  let K : Subgroup M480 := (centW rs).subgroupOf M480
  let f : Fin ws.length → M480 ⧸ K := fun i =>
    QuotientGroup.mk ⟨wordPerm ws[i.val], wordPerm_mem hl _ (hws _ (List.getElem_mem i.2))⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := QuotientGroup.eq.1 hij
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hij'
    have hk : keyP rs ps (wordPerm ws[i.val]) = keyP rs ps (wordPerm ws[j.val]) :=
      keyP_eq ps hij'
    rw [← orbKey_eq H hrs hps (hws _ (List.getElem_mem i.2)),
      ← orbKey_eq H hrs hps (hws _ (List.getElem_mem j.2))] at hk
    have hk' : (ws.map (orbKey rs ps))[i.val]'(by simp) =
        (ws.map (orbKey rs ps))[j.val]'(by simp) := by
      simpa using hk
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).1 hk')
  have hfin : Finite (M480 ⧸ K) := Quotient.finite _
  have h1 := Nat.card_le_card_of_injective f hf
  have h2 := K.card_mul_index
  rw [card_M480 H.bound H.model] at h2
  have h3 : Nat.card K = Nat.card (centW rs) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fun _ hx => (mem_centW.1 hx).1)).toEquiv
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hlen] at h1
  rw [h3, Subgroup.index] at h2
  calc n * Nat.card (centW rs) ≤ Nat.card (M480 ⧸ K) * Nat.card (centW rs) :=
        Nat.mul_le_mul_right _ h1
    _ = 161280 := by rw [mul_comm]; exact h2

theorem mem_of_card_le {G : Type*} [Group G] [Finite G] {C : Subgroup G} {L : List G}
    (hnd : L.Nodup) (hsub : ∀ x ∈ L, x ∈ C) (hcard : Nat.card C ≤ L.length) {g : G}
    (hg : g ∈ C) : g ∈ L := by
  classical
  have h1 : (↑L.toFinset : Set G) ⊆ (C : Set G) := fun x hx => hsub x (List.mem_toFinset.1 hx)
  have h2 : (C : Set G).ncard ≤ (↑L.toFinset : Set G).ncard := by
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
    calc (C : Set G).ncard = Nat.card C := (Nat.card_coe_set_eq _).symm
      _ ≤ L.length := hcard
  have he := Set.eq_of_subset_of_ncard_le h1 h2 (Set.toFinite _)
  have hg' : g ∈ (↑L.toFinset : Set G) := by
    rw [he]
    exact hg
  exact List.mem_toFinset.1 hg'

structure Checks : Prop where
  fz : fzK = true
  r : rK = true
  irred : irredK = true
  s : sK = true
  t : tK = true
  tcent : tCentK = true
  y : yK = true
  orbR : ∃ ws, orbK [r1W] ptsR 2240 ws = true
  orbS : ∃ ws, orbK [zW, dW] ptsS 2240 ws = true
  rs : allNeB rsWords = true
  cs : allNeB csWords = true
  cent : centK = true
  ord : ordK = true

theorem lt12_gen (i : ℕ) (hi : i < 6) : ∀ c ∈ [2 * i], c < 12 := by
  intro c hc
  rw [List.mem_singleton] at hc
  omega

theorem lt12_genInv (i : ℕ) (hi : i < 6) : ∀ c ∈ [2 * i + 1], c < 12 := by
  intro c hc
  rw [List.mem_singleton] at hc
  omega

theorem lt12_nil : ∀ c ∈ ([] : List ℕ), c < 12 := by simp

theorem lt12_csWords : ∀ w ∈ csWords, ∀ c ∈ w, c < 12 := by
  intro w hw
  simp only [csWords, List.mem_flatMap, List.mem_map] at hw
  obtain ⟨i, -, j, -, k, -, l, -, rfl⟩ := hw
  exact lt12_append (lt12_append (lt12_rW i j) (lt12_wpow lt12_yW k)) (lt12_wpow lt12_fW l)

theorem wordPerm_conj (h : cmLettersOK = true) {s r : List ℕ} (hs : ∀ c ∈ s, c < 12) :
    wordPerm (s ++ r ++ invWord s) = wordPerm s * wordPerm r * (wordPerm s)⁻¹ := by
  rw [wordPerm_append, wordPerm_append, wordPerm_inv h hs]

theorem wordPerm_conj' (h : cmLettersOK = true) {s r : List ℕ} (hs : ∀ c ∈ s, c < 12) :
    wordPerm (invWord s ++ r ++ s) = (wordPerm s)⁻¹ * wordPerm r * wordPerm s := by
  rw [wordPerm_append, wordPerm_append, wordPerm_inv h hs]

theorem exists_rW_of_any (H : Hyp) {u : List ℕ} (hu : ∀ c ∈ u, c < 12)
    (h : rWords.any (eqB u) = true) : ∃ i j, i < 3 ∧ j < 3 ∧ wordPerm u = r1P ^ i * r2P ^ j := by
  rw [List.any_eq_true] at h
  obtain ⟨w, hw, he⟩ := h
  have e := eqB_eq H hu (lt12_rWords w hw) he
  simp only [rWords, List.mem_flatMap, List.mem_map, List.mem_range] at hw
  obtain ⟨i, hi, j, hj, rfl⟩ := hw
  exact ⟨i, j, hi, hj, by rw [e, wordPerm_rW]⟩

theorem b2Facts_of (H : Hyp) (K : Checks) : B2Facts := by
  have hl := cmLettersOK_of H.letters
  have hfz := K.fz
  have hr := K.r
  have hirr := K.irred
  have hs := K.s
  have ht := K.t
  have htc := K.tcent
  have hy := K.y
  simp only [fzK, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hfz
  obtain ⟨⟨hf, hz2⟩, hzc⟩ := hfz
  simp only [rK, Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨hr1, hr2⟩, hrc⟩, hnd⟩, hy1⟩, hy2⟩ := hr
  simp only [sK, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hzr1, hzr2⟩, hdr1⟩, hdr2⟩, hz4⟩, hz2'⟩, hd2⟩, hdz⟩, hdk⟩ := hs
  simp only [yK, Bool.and_eq_true, Bool.not_eq_true'] at hy
  obtain ⟨⟨⟨hy4, hy2'⟩, -⟩, -⟩ := hy
  simp only [tK, Bool.and_eq_true, List.all_eq_true] at ht
  obtain ⟨⟨htnd, hcl⟩, hnorm⟩ := ht
  simp only [tCentK, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    at htc
  obtain ⟨hc, hq⟩ := htc
  have ey : ∀ r : List ℕ, wordPerm (yW ++ r ++ invWord yW) = yP * wordPerm r * yP⁻¹ :=
    fun r => wordPerm_conj hl lt12_yW
  have hgen : ∀ i : Fin 6, wordPerm [2 * i.val] = genPerm i := fun i => (wordPerm_genCode hl i).1
  refine
    { fP_comm := fun i => ?_
      zP_sq := ?_
      conj_zP := fun i => ?_
      r1P_cube := ?_
      r2P_cube := ?_
      r_comm := ?_
      r_inj := fun i j i' j' hi hj hi' hj' he => ?_
      y_r1 := ?_
      y_r2 := ?_
      irred := fun i j hi hj hne => ?_
      z_r1 := ?_
      z_r2 := ?_
      d_r1 := ?_
      d_r2 := ?_
      zP_four := ?_
      zP_sq_ne := ?_
      dP_sq := ?_
      d_z := ?_
      d_notin := fun k hk => ?_
      t_nodup := ?_
      t_closed := fun l hl' s hs' => ?_
      t_norm := fun s hs' r hr' => ?_
      t_cent := fun l hl' hz hd => ?_
      t_quot := fun w hw l hl' hsq => ?_
      yP_four := ?_
      yP_sq_ne := ?_ }
  · have e := eqB_eq H (lt12_append (lt12_gen i i.2) lt12_fW)
      (lt12_append lt12_fW (lt12_gen i i.2)) (hf i i.2)
    rwa [wordPerm_append, wordPerm_append, hgen] at e
  · have e := eqB_eq H (lt12_append lt12_zW lt12_zW) lt12_fW hz2
    rwa [wordPerm_append] at e
  · have hw : ∀ c ∈ [2 * i.val] ++ zW ++ [2 * i.val + 1], c < 12 :=
      lt12_append (lt12_append (lt12_gen i i.2) lt12_zW) (lt12_genInv i i.2)
    have e : wordPerm ([2 * i.val] ++ zW ++ [2 * i.val + 1]) =
        genPerm i * zP * (genPerm i)⁻¹ := by
      rw [wordPerm_append, wordPerm_append, (wordPerm_genCode hl i).1, (wordPerm_genCode hl i).2]
      rfl
    rcases hzc i i.2 with h1 | h1
    · left
      rw [← e]
      exact eqB_eq H hw lt12_zW h1
    · right
      rw [← e, show zP⁻¹ = wordPerm (invWord zW) from (wordPerm_inv hl lt12_zW).symm]
      exact eqB_eq H hw (invWord_lt lt12_zW) h1
  · have e := eqB_eq H (lt12_wpow lt12_r1W 3) lt12_nil hr1
    rwa [wordPerm_wpow, wordPerm_nil] at e
  · have e := eqB_eq H (lt12_wpow lt12_r2W 3) lt12_nil hr2
    rwa [wordPerm_wpow, wordPerm_nil] at e
  · have e := eqB_eq H (lt12_append lt12_r1W lt12_r2W) (lt12_append lt12_r2W lt12_r1W) hrc
    rwa [wordPerm_append, wordPerm_append] at e
  · have hn := allNeB_sound H rWords lt12_rWords hnd
    have ew : wordPerm (rW i j) = wordPerm (rW i' j') := by rw [wordPerm_rW, wordPerm_rW, he]
    exact rW_inj hi hj hi' hj'
      (List.inj_on_of_nodup_map hn (mem_rWords hi hj) (mem_rWords hi' hj') ew)
  · have e := eqB_eq H (lt12_append (lt12_append lt12_yW lt12_r1W) (invWord_lt lt12_yW))
      (lt12_rW 0 2) hy1
    rw [ey, wordPerm_rW] at e
    change yP * wordPerm r1W * yP⁻¹ = r2P ^ 2
    simpa using e
  · have e := eqB_eq H (lt12_append (lt12_append lt12_yW lt12_r2W) (invWord_lt lt12_yW))
      (lt12_rW 1 0) hy2
    rw [ey, wordPerm_rW] at e
    change yP * wordPerm r2W * yP⁻¹ = r1P
    simpa using e
  · simp only [irredK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, Bool.not_eq_true'] at hirr
    rcases hirr i hi j hj with h0 | ⟨⟨h1, h2⟩, h3⟩
    · exact absurd h0 hne
    have hw : ∀ c ∈ yW ++ rW i j ++ invWord yW, c < 12 :=
      lt12_append (lt12_append lt12_yW (lt12_rW i j)) (invWord_lt lt12_yW)
    have e : wordPerm (yW ++ rW i j ++ invWord yW) = yP * (r1P ^ i * r2P ^ j) * yP⁻¹ := by
      rw [ey, wordPerm_rW]
    refine ⟨fun he => ?_, fun he => ?_, fun he => ?_⟩
    · exact eqB_ne H hw lt12_nil h1 (by rw [e, he, wordPerm_nil])
    · exact eqB_ne H hw (lt12_rW i j) h2 (by rw [e, he, wordPerm_rW])
    · exact eqB_ne H hw (lt12_append (lt12_rW i j) (lt12_rW i j)) h3
        (by rw [e, he, wordPerm_append, wordPerm_rW])
  · have e := eqB_eq H (lt12_append lt12_zW lt12_r1W) (lt12_append lt12_r1W lt12_zW) hzr1
    rwa [wordPerm_append, wordPerm_append] at e
  · have e := eqB_eq H (lt12_append lt12_zW lt12_r2W) (lt12_append lt12_r2W lt12_zW) hzr2
    rwa [wordPerm_append, wordPerm_append] at e
  · have e := eqB_eq H (lt12_append lt12_dW lt12_r1W) (lt12_append lt12_r1W lt12_dW) hdr1
    rwa [wordPerm_append, wordPerm_append] at e
  · have e := eqB_eq H (lt12_append lt12_dW lt12_r2W) (lt12_append lt12_r2W lt12_dW) hdr2
    rwa [wordPerm_append, wordPerm_append] at e
  · have e := eqB_eq H (lt12_wpow lt12_zW 4) lt12_nil hz4
    rwa [wordPerm_wpow, wordPerm_nil] at e
  · intro he
    exact eqB_ne H (lt12_append lt12_zW lt12_zW) lt12_nil hz2'
      (by rw [wordPerm_append, wordPerm_nil]; exact he)
  · have e := eqB_eq H (lt12_append lt12_dW lt12_dW) lt12_nil hd2
    rwa [wordPerm_append, wordPerm_nil] at e
  · have e := eqB_eq H (lt12_append (lt12_append lt12_dW lt12_zW) lt12_dW) (invWord_lt lt12_zW) hdz
    rwa [wordPerm_append, wordPerm_append, wordPerm_inv hl lt12_zW] at e
  · exact fun he => eqB_ne H lt12_dW (lt12_wpow lt12_zW k) (Bool.of_not_eq_true (hdk k hk))
      (by rw [wordPerm_wpow]; exact he)
  · have hn := allNeB_sound H (tIdx.map tWord)
      (fun w hw => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hw
        exact lt12_tWord l) htnd
    rw [List.map_map] at hn
    exact hn
  · have hcl' := hcl l hl' s hs'
    rw [List.any_eq_true] at hcl'
    obtain ⟨l'', hl'', he⟩ := hcl'
    refine ⟨l'', hl'', ?_⟩
    have e := eqB_eq H (lt12_append (lt12_tWord l) (lt12_tGens' s hs')) (lt12_tWord l'') he
    rwa [wordPerm_append] at e
  · have hr12 : ∀ c ∈ r, c < 12 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact lt12_r1W
      · exact lt12_r2W
    have hs12 := lt12_tGens' s hs'
    have hc' := hnorm s hs' r hr'
    obtain ⟨i, j, hi, hj, e1⟩ :=
      exists_rW_of_any H (lt12_append (lt12_append hs12 hr12) (invWord_lt hs12)) hc'.1
    obtain ⟨i', j', hi', hj', e2⟩ :=
      exists_rW_of_any H (lt12_append (lt12_append (invWord_lt hs12) hr12) hs12) hc'.2
    rw [wordPerm_conj hl hs12] at e1
    rw [wordPerm_conj' hl hs12] at e2
    exact ⟨⟨i, j, hi, hj, e1⟩, ⟨i', j', hi', hj', e2⟩⟩
  · have hT := lt12_tWord l
    rcases hc l hl' with h1 | h1
    · exfalso
      rw [Bool.and_eq_false_iff] at h1
      rcases h1 with h1 | h1
      · exact eqB_ne H (lt12_append hT lt12_zW) (lt12_append lt12_zW hT) h1
          (by rw [wordPerm_append, wordPerm_append]; exact hz)
      · exact eqB_ne H (lt12_append hT lt12_dW) (lt12_append lt12_dW hT) h1
          (by rw [wordPerm_append, wordPerm_append]; exact hd)
    · rw [List.any_eq_true] at h1
      obtain ⟨v, hv, he⟩ := h1
      have e := eqB_eq H hT (lt12_qWords v hv) he
      simp only [qWords, List.mem_flatMap, List.mem_map, List.mem_range] at hv
      obtain ⟨k, hk, m, hm, rfl⟩ := hv
      refine ⟨k, m, hk, hm, ?_⟩
      rw [tPerm, e, wordPerm_append, wordPerm_wpow, wordPerm_wpow]
      rfl
  · have hw12 : ∀ c ∈ w, c < 12 := by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact lt12_yW
      · exact lt12_append lt12_yW lt12_fW
    have hT := lt12_tWord l
    obtain ⟨m, hm, hsq⟩ := hsq
    rcases hq w hw l hl' with h1 | h1
    · exfalso
      rw [List.any_eq_false] at h1
      refine h1 (wpow w m) (List.mem_map_of_mem (List.mem_range.2 hm)) ?_
      rw [eqB_iff H (lt12_append hT hT) (lt12_wpow hw12 m), wordPerm_append, wordPerm_wpow]
      exact hsq
    · rw [List.any_eq_true] at h1
      obtain ⟨v, hv, he⟩ := h1
      have e := eqB_eq H hT (lt12_swWords hw12 v hv) he
      simp only [swWords, List.mem_flatMap, List.mem_map, List.mem_range] at hv
      obtain ⟨k, hk, n, hn, m', hm', rfl⟩ := hv
      refine ⟨k, n, m', hk, hn, hm', ?_⟩
      rw [tPerm, e, wordPerm_append, wordPerm_sW, wordPerm_wpow]
  · have e := eqB_eq H (lt12_wpow lt12_yW 4) lt12_nil hy4
    rwa [wordPerm_wpow, wordPerm_nil] at e
  · intro he
    exact eqB_ne H (lt12_append lt12_yW lt12_yW) lt12_nil hy2'
      (by rw [wordPerm_append, wordPerm_nil]; exact he)

theorem comm_of_gens {x : Equiv.Perm (Fin 480)} (hx : ∀ i : Fin 6, genPerm i * x = x * genPerm i)
    {m : Equiv.Perm (Fin 480)} (hm : m ∈ M480) : m * x = x * m := by
  have hle : M480 ≤ Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin 480))) :=
    (Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun i =>
      Subgroup.mem_centralizer_singleton_iff.2 (hx i))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hm)

theorem card_centW_le (H : Hyp) {rs : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hrs : ∀ r ∈ rs, ∀ c ∈ r, c < 12) (hps : ∀ cp ∈ ps, cp.2 < 480)
    (h : ∃ ws, orbK rs ps 2240 ws = true) : Nat.card (centW rs) ≤ 72 := by
  obtain ⟨ws, hws⟩ := h
  have := orbK_card H hrs hps hws
  omega

theorem b2Chain_of (H : Hyp) (K : Checks) : B2Chain := by
  have hl := cmLettersOK_of H.letters
  have F := b2Facts_of H K
  have hfc : ∀ m ∈ M480, m * fP = fP * m := fun m hm => comm_of_gens F.fP_comm hm
  have hgen' : ∀ a (ha : a < 6), wordPerm [2 * a] = genPerm ⟨a, ha⟩ :=
    fun a ha => (wordPerm_genCode hl ⟨a, ha⟩).1
  have hC1 := card_centW_le H (rs := [r1W]) (by decide) (by decide) K.orbR
  have hC2 := card_centW_le H (rs := [zW, dW]) (by decide) (by decide) K.orbS
  have hyz : yP * zP = zP * yP := by
    have hy := K.y
    simp only [yK, Bool.and_eq_true] at hy
    have e := eqB_eq H (lt12_append lt12_yW lt12_zW) (lt12_append lt12_zW lt12_yW) hy.1.2
    rwa [wordPerm_append, wordPerm_append] at e
  have hyd : yP * dP = dP * yP := by
    have hy := K.y
    simp only [yK, Bool.and_eq_true] at hy
    have e := eqB_eq H (lt12_append lt12_yW lt12_dW) (lt12_append lt12_dW lt12_yW) hy.2
    rwa [wordPerm_append, wordPerm_append] at e
  have hR : ∀ g ∈ M480, g * r1P = r1P * g →
      ∃ i j k l, i < 3 ∧ j < 3 ∧ k < 4 ∧ l < 2 ∧ g = r1P ^ i * r2P ^ j * (zP ^ k * dP ^ l) := by
    intro g hg h1
    have hmem : g ∈ rsWords.map wordPerm := by
      refine mem_of_card_le (C := centW [r1W]) (allNeB_sound H rsWords lt12_rsWords K.rs)
        (fun x hx => ?_) (by rw [List.length_map]; exact hC1) (mem_centW.2 ⟨hg, fun r hr => ?_⟩)
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        refine mem_centW.2 ⟨wordPerm_mem hl w (lt12_rsWords w hw), fun r hr => ?_⟩
        rw [List.mem_singleton] at hr
        subst hr
        simp only [rsWords, List.mem_flatMap, List.mem_map, List.mem_range] at hw
        obtain ⟨i, -, j, -, k, -, l, -, rfl⟩ := hw
        rw [wordPerm_append, wordPerm_rW, wordPerm_sW]
        have c1 : Commute r1P r1P := Commute.refl _
        have c2 : Commute r2P r1P := (F.r_comm : Commute r1P r2P).symm
        have c3 : Commute zP r1P := F.z_r1
        have c4 : Commute dP r1P := F.d_r1
        exact (((c1.pow_left i).mul_left (c2.pow_left j)).mul_left
          ((c3.pow_left k).mul_left (c4.pow_left l))).eq
      · rw [List.mem_singleton] at hr
        subst hr
        exact h1
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hmem
    simp only [rsWords, List.mem_flatMap, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, j, hj, k, hk, l, hl', rfl⟩ := hw
    exact ⟨i, j, k, l, hi, hj, hk, hl', by rw [wordPerm_append, wordPerm_rW, wordPerm_sW]⟩
  intro g hg
  refine ⟨fun hcomm => ?_, fun h1 _ => hR g hg h1, fun h1 h2 h4 h2' => ?_⟩
  · have h1 : g * r1P = r1P * g := (comm_of_gens hcomm (mem_M480_wordPerm hl lt12_r1W)).symm
    obtain ⟨i, j, k, l, hi, hj, hk, hl', rfl⟩ := hR g hg h1
    have hcent := K.cent
    simp only [centK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, List.any_eq_true, Bool.not_eq_true'] at hcent
    rcases hcent i hi j hj k hk l hl' with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hk02⟩ | ⟨a, ha, hne⟩
    · rcases hk02 with rfl | rfl
      · left
        simp
      · right
        simp only [pow_zero, one_mul, mul_one]
        rw [sq]
        exact F.zP_sq
    · exfalso
      have hu := lt12_append (lt12_rW i j) (lt12_sW k l)
      refine eqB_ne H (lt12_append hu (lt12_gen a ha)) (lt12_append (lt12_gen a ha) hu) hne ?_
      simp only [wordPerm_append, wordPerm_rW, wordPerm_sW, hgen' a ha]
      exact (hcomm ⟨a, ha⟩).symm
  · have hmem : g ∈ csWords.map wordPerm := by
      refine mem_of_card_le (C := centW [zW, dW]) (allNeB_sound H csWords lt12_csWords K.cs)
        (fun x hx => ?_) (by rw [List.length_map]; exact hC2) (mem_centW.2 ⟨hg, fun r hr => ?_⟩)
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        refine mem_centW.2 ⟨wordPerm_mem hl w (lt12_csWords w hw), fun r hr => ?_⟩
        simp only [csWords, List.mem_flatMap, List.mem_map, List.mem_range] at hw
        obtain ⟨i, -, j, -, k, -, l, -, rfl⟩ := hw
        rw [wordPerm_append, wordPerm_append, wordPerm_rW, wordPerm_wpow, wordPerm_wpow]
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · have c1 : Commute r1P zP := F.z_r1.symm
          have c2 : Commute r2P zP := F.z_r2.symm
          have c3 : Commute yP zP := hyz
          have c4 : Commute (wordPerm fW) zP := (hfc zP (mem_M480_wordPerm hl lt12_zW)).symm
          exact (((c1.pow_left i).mul_left (c2.pow_left j)).mul_left (c3.pow_left k)).mul_left
            (c4.pow_left l) |>.eq
        · have c1 : Commute r1P dP := F.d_r1.symm
          have c2 : Commute r2P dP := F.d_r2.symm
          have c3 : Commute yP dP := hyd
          have c4 : Commute (wordPerm fW) dP := (hfc dP (mem_M480_wordPerm hl lt12_dW)).symm
          exact (((c1.pow_left i).mul_left (c2.pow_left j)).mul_left (c3.pow_left k)).mul_left
            (c4.pow_left l) |>.eq
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl
        · exact h1
        · exact h2
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hmem
    simp only [csWords, List.mem_flatMap, List.mem_map, List.mem_range] at hw
    obtain ⟨i, hi, j, hj, k, hk, l, hl', rfl⟩ := hw
    have hu : ∀ c ∈ cW i j k l, c < 12 :=
      lt12_append (lt12_append (lt12_rW i j) (lt12_wpow lt12_yW k)) (lt12_wpow lt12_fW l)
    have hodd : k = 1 ∨ k = 3 := by
      by_contra hk'
      have hk02 : k = 0 ∨ k = 2 := by omega
      have hord := K.ord
      simp only [ordK, List.all_eq_true, List.mem_range, List.mem_cons, List.mem_nil_iff,
        or_false, Bool.or_eq_true, Bool.not_eq_true'] at hord
      rcases hord i hi j hj k hk02 l hl' with h5 | h5
      · refine eqB_ne H (lt12_wpow hu 4) lt12_nil h5 ?_
        have e4 : ∀ x : Equiv.Perm (Fin 480), x ^ 4 = x * x * (x * x) := fun x => by
          rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
        rw [wordPerm_wpow, wordPerm_nil, e4]
        exact h4
      · have e := eqB_eq H (lt12_append hu hu) lt12_nil h5
        rw [wordPerm_append, wordPerm_nil] at e
        exact h2' e
    refine ⟨i, j, k, l, hi, hj, hodd, hl', ?_⟩
    rw [wordPerm_append, wordPerm_append, wordPerm_rW, wordPerm_wpow, wordPerm_wpow]
    rfl

end CFSG.OddStandard.ONanRec.B2K

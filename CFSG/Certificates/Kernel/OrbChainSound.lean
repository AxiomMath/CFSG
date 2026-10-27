module

public import Certificates.Data.Kernel.OrbChain
public import CFSG.Certificates.Kernel.Census.BaseSound
public import CFSG.Monster.B.Gen.OrbitChain

public section

universe u

namespace CFSG.KC.OrbChain

open CFSG.KC.Census CFSG.KC.Census.Base

theorem letN_eq {α : Sort u} (y : Nat) (k : Nat → α) : letN y k = k y := by
  cases y <;> rfl

theorem forceW_eq {α : Sort u} : ∀ (l : List Nat) (k : List Nat → α), forceW l k = k l
  | [], _ => rfl
  | a :: l, k => by
    rw [forceW, letN_eq, forceW_eq l]

theorem forceWs_eq {α : Sort u} :
    ∀ (ls : List (List Nat)) (k : List (List Nat) → α), forceWs ls k = k ls
  | [], _ => rfl
  | x :: l, k => by
    rw [forceWs, forceW_eq, forceWs_eq l]

theorem testBit_lor_shift (m q r : Nat) :
    Nat.testBit (Nat.lor m (Nat.shiftLeft 1 q)) r = (Nat.testBit m r || decide (q = r)) := by
  have e : Nat.lor m (Nat.shiftLeft 1 q) = m ||| 2 ^ q := by
    change m ||| 1 <<< q = m ||| 2 ^ q
    rw [Nat.shiftLeft_eq, one_mul]
  rw [e, Nat.testBit_or, Nat.testBit_two_pow]

theorem testBit_shift (q r : Nat) : Nat.testBit (Nat.shiftLeft 1 q) r = decide (q = r) := by
  change Nat.testBit (1 <<< q) r = _
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]

theorem chainProd_eq (w : Nat) (L : Nat → Nat) (ws : List (List Nat)) (bs : List Nat)
    (fuel : Nat) : ∀ k, chainProd w L ws bs fuel k =
      ∏ i ∈ Finset.range k, lvlCnt w L ws bs fuel i
  | 0 => rfl
  | k + 1 => by
    rw [Finset.prod_range_succ, ← chainProd_eq w L ws bs fuel k]
    rfl

variable {n w h : ℕ} {L : ℕ → ℕ} {ℓ : ℕ → Equiv.Perm (Fin n)}

@[expose] def Good (Γ : Subgroup (Equiv.Perm (Fin n))) (b : ℕ → Fin n) (i q : ℕ) : Prop :=
  ∃ hq : q < n, ∃ g ∈ Γ, (∀ k < i, g (b k) = b k) ∧ g (b i) = ⟨q, hq⟩

section Sound

variable (H : Letters n w h L ℓ) {Γ : Subgroup (Equiv.Perm (Fin n))} (hℓ : ∀ k < 2 * h, ℓ k ∈ Γ)
  {b : ℕ → Fin n} {i : ℕ}
include H hℓ

theorem orbCnt_sound {S : List (List ℕ)}
    (hS : ∀ x ∈ S, WordOK h x ∧ ∀ k < i, wordPerm ℓ x (b k) = b k) :
    ∀ (es : List (ℕ × ℕ × ℕ)) (m c : ℕ), (∀ q, Nat.testBit m q = true → Good Γ b i q) →
      orbCnt w L S m es c ≠ 0 → ∃ l : List ℕ, l.Nodup ∧
        (∀ q ∈ l, Nat.testBit m q = false ∧ Good Γ b i q) ∧ orbCnt w L S m es c = c + l.length
  | [], m, c, _, _ => ⟨[], List.nodup_nil, by simp, by simp [orbCnt]⟩
  | (q, p, j) :: es, m, c, hm, hne => by
    simp only [orbCnt] at hne ⊢
    cases hck : (Nat.testBit m p && !Nat.testBit m q &&
        Nat.beq (wPt w L (S.getD j []) p) q)
    · rw [hck] at hne
      simp at hne
    · rw [hck, cond_true, letN_eq] at hne
      rw [cond_true, letN_eq]
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hck
      obtain ⟨⟨hp, hq⟩, he⟩ := hck
      have he' := Nat.eq_of_beq_eq_true he
      set x := S.getD j [] with hxdef
      have hx : WordOK h x ∧ ∀ k < i, wordPerm ℓ x (b k) = b k := by
        rcases lt_or_ge j S.length with hj | hj
        · have hmem : x ∈ S := by
            rw [hxdef, List.getD_eq_getElem _ _ hj]
            exact List.getElem_mem hj
          exact hS x hmem
        · have e : x = [] := by
            rw [hxdef]
            exact List.getD_eq_default _ _ hj
          rw [e]
          exact ⟨fun k hk => by simp at hk, fun k _ => by simp [wordPerm]⟩
      obtain ⟨hpn, g, hg, hgfix, hgp⟩ := hm p hp
      have hwq := wPt_eq H x hx.1 p hpn
      rw [he'] at hwq
      have hqn : q < n := by
        rw [hwq]
        exact Fin.isLt _
      have hgood : Good Γ b i q := by
        refine ⟨hqn, wordPerm ℓ x * g, Γ.mul_mem (wordPerm_mem H hℓ hx.1) hg, fun k hk => ?_, ?_⟩
        · rw [Equiv.Perm.mul_apply, hgfix k hk, hx.2 k hk]
        · rw [Equiv.Perm.mul_apply, hgp]
          exact Fin.ext hwq.symm
      have hm' : ∀ r, Nat.testBit (Nat.lor m (Nat.shiftLeft 1 q)) r = true → Good Γ b i r := by
        intro r hr
        rw [testBit_lor_shift, Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with hr | rfl
        · exact hm r hr
        · exact hgood
      obtain ⟨l, hnd, hl, heq⟩ := orbCnt_sound hS es _ (c + 1) hm' hne
      refine ⟨q :: l, List.nodup_cons.2 ⟨fun hql => ?_, hnd⟩, fun r hr => ?_, ?_⟩
      · have h1 := (hl q hql).1
        rw [testBit_lor_shift] at h1
        simp at h1
      · rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨hq, hgood⟩
        · refine ⟨?_, (hl r hr).2⟩
          have h1 := (hl r hr).1
          rw [testBit_lor_shift, Bool.or_eq_false_iff] at h1
          exact h1.1
      · rw [heq, List.length_cons]
        omega

theorem lvlCnt_sound {ws : List (List ℕ)} {bs : List ℕ} (fuel : ℕ)
    (hws : ∀ x ∈ ws, WordOK h x) (hbs : ∀ c ∈ bs, c < n)
    (hb : ∀ k < bs.length, (b k : ℕ) = bs.getD k 0) (hi : i < bs.length) :
    ∃ P : Finset (Fin n), lvlCnt w L ws bs fuel i ≤ P.card ∧ ∀ x ∈ P, Good Γ b i x := by
  classical
  unfold lvlCnt
  rw [forceWs_eq]
  set S := lvlGens w L ws bs i with hSdef
  have hS : ∀ x ∈ S, WordOK h x ∧ ∀ k < i, wordPerm ℓ x (b k) = b k := by
    intro x hx
    rw [hSdef, lvlGens, List.mem_filter, List.all_eq_true] at hx
    obtain ⟨hxw, hfix⟩ := hx
    refine ⟨hws x hxw, fun k hk => ?_⟩
    have hkl : k < bs.length := by omega
    have hmem : bs.getD k 0 ∈ bs.take i := by
      rw [List.getD_eq_getElem _ _ hkl]
      exact List.mem_iff_getElem.2 ⟨k, by simp; omega, by simp⟩
    have hcn : bs.getD k 0 < n := hbs _ (List.mem_of_mem_take hmem)
    have e := Nat.eq_of_beq_eq_true (hfix _ hmem)
    rw [wPt_eq H x (hws x hxw) _ hcn] at e
    apply Fin.ext
    have hbk : b k = ⟨bs.getD k 0, hcn⟩ := Fin.ext (hb k hkl)
    rw [hbk]
    exact e
  set bi := bs.getD i 0 with hbi
  have hbin : bi < n := hbs _ (by rw [hbi, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi)
  have hbeq : b i = ⟨bi, hbin⟩ := Fin.ext (hb i hi)
  have hm : ∀ q, Nat.testBit (Nat.shiftLeft 1 bi) q = true → Good Γ b i q := by
    intro q hq
    rw [testBit_shift, decide_eq_true_eq] at hq
    subst hq
    exact ⟨hbin, 1, Γ.one_mem, fun _ _ => rfl, by rw [Equiv.Perm.one_apply, hbeq]⟩
  by_cases h0 : orbCnt w L S (Nat.shiftLeft 1 bi) (orbBfs w L S bi fuel) 1 = 0
  · exact ⟨∅, by rw [h0]; exact Nat.zero_le _, by simp⟩
  obtain ⟨l, hnd, hl, heq⟩ := orbCnt_sound H hℓ hS _ _ 1 hm h0
  have hgood : ∀ r ∈ bi :: l, Good Γ b i r := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact hm _ (by rw [testBit_shift]; simp)
    · exact (hl r hr).2
  have hnd' : (bi :: l).Nodup := by
    refine List.nodup_cons.2 ⟨fun hbl => ?_, hnd⟩
    have h1 := (hl bi hbl).1
    rw [testBit_shift] at h1
    simp at h1
  refine ⟨Finset.univ.filter fun x : Fin n => (x : ℕ) ∈ bi :: l, ?_, fun x hx => ?_⟩
  · rw [heq]
    have hsub : (bi :: l).toFinset ⊆
        (Finset.univ.filter fun x : Fin n => (x : ℕ) ∈ bi :: l).image Fin.val := by
      intro r hr
      rw [List.mem_toFinset] at hr
      obtain ⟨hrn, -⟩ := hgood r hr
      exact Finset.mem_image.2 ⟨⟨r, hrn⟩, by simpa using hr, rfl⟩
    have hc := (Finset.card_le_card hsub).trans Finset.card_image_le
    rw [List.toFinset_card_of_nodup hnd', List.length_cons] at hc
    omega
  · have hx' : (x : ℕ) ∈ bi :: l := (Finset.mem_filter.1 hx).2
    exact hgood _ hx'

theorem le_card_of_chainOK {ws : List (List ℕ)} {bs : List ℕ} {fuel B : ℕ}
    (hc : chainOK w L n h ws bs fuel B = true) : B ≤ Nat.card Γ := by
  classical
  unfold chainOK at hc
  simp only [Bool.and_eq_true, List.all_eq_true, Nat.blt_eq, Nat.ble_eq] at hc
  obtain ⟨⟨hbs, hws⟩, hB⟩ := hc
  rw [chainProd_eq] at hB
  have hcard : 0 < Nat.card Γ := Nat.card_pos
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hnil : bs = [] := by
      rcases bs with _ | ⟨c, bs⟩
      · rfl
      · have := hbs c List.mem_cons_self
        omega
    subst hnil
    simp only [List.length_nil, Finset.range_zero, Finset.prod_empty] at hB
    omega
  let b : ℕ → Fin n := fun k => if hk : bs.getD k 0 < n then ⟨_, hk⟩ else ⟨0, hn⟩
  have hb : ∀ k < bs.length, (b k : ℕ) = bs.getD k 0 := by
    intro k hk
    have hkn : bs.getD k 0 < n :=
      hbs _ (by rw [List.getD_eq_getElem _ _ hk]; exact List.getElem_mem hk)
    simp only [b, dif_pos hkn]
  have hws' : ∀ x ∈ ws, WordOK h x := hws
  have hex : ∀ i, ∃ P : Finset (Fin n), i < bs.length →
      lvlCnt w L ws bs fuel i ≤ P.card ∧ ∀ x ∈ P, Good Γ b i x := by
    intro i
    by_cases hi : i < bs.length
    · obtain ⟨P, hP⟩ := lvlCnt_sound H hℓ (b := b) fuel hws' hbs hb hi
      exact ⟨P, fun _ => hP⟩
    · exact ⟨∅, fun h' => absurd h' hi⟩
  choose P hP using hex
  have hchain := CFSG.Monster.B.card_ge_prod_of_chain (G := Γ) b P bs.length
    (fun i hi p hp => by
      obtain ⟨_hq, g, hg, hfix, hgp⟩ := (hP i hi).2 p hp
      refine ⟨⟨g, hg⟩, fun k hk => ?_, ?_⟩
      · rw [Subgroup.mk_smul, Equiv.Perm.smul_def]
        exact hfix k hk
      · rw [Subgroup.mk_smul, Equiv.Perm.smul_def, hgp])
  calc B ≤ ∏ i ∈ Finset.range bs.length, lvlCnt w L ws bs fuel i := hB
    _ ≤ ∏ i ∈ Finset.range bs.length, (P i).card :=
        Finset.prod_le_prod fun i hi => (hP i (Finset.mem_range.1 hi)).1
    _ ≤ Nat.card Γ := hchain

end Sound

end CFSG.KC.OrbChain

end

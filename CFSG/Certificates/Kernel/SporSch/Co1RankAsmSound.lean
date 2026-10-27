module

public import CFSG.Certificates.Kernel.SporSch.Co1RankSpanSound
public import CFSG.Certificates.Kernel.SporSch.Co1RankExtSound
public import Certificates.Data.Kernel.SporSch.Co1RankRec
public import Mathlib.Data.ZMod.QuotientGroup

public section

namespace CFSG.KS.SporSch.Co1Rank

open CFSG.KC.Loop CFSG.KC.Co1RankCoord

theorem land15 (w : ℕ) : Nat.land w 15 = w % 16 := Nat.and_two_pow_sub_one_eq_mod w 4

theorem shr4 (w : ℕ) : Nat.shiftRight w 4 = w / 16 := Nat.shiftRight_eq_div_pow w 4

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem beq_false {l : ℕ} (h : l ≠ 0) : Nat.beq l 0 = false := by
  cases hb : Nat.beq l 0
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

@[expose] noncomputable def walkPn (P : List ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, k => k
  | n + 1, w, k =>
    if w % 16 = 0 then k else walkPn P n (w / 16) (fld(getL P (w % 16 - 1), Nat.mul 12 k, 4095))

theorem walkP_eq' (P : List ℕ) : ∀ n w k, Nat.rec (motive := fun _ => Nat → Nat → Nat)
    (fun _ k => k) (fun _ ih w k => strictN (Nat.land w 15) fun l =>
      nIf(Nat.beq l 0, k, strictN (fld(getL P (Nat.sub l 1), Nat.mul 12 k, 4095)) fun k' =>
        ih (Nat.shiftRight w 4) k')) n w k = walkPn P n w k
  | 0, _, _ => rfl
  | n + 1, w, k => by
    change strictN (Nat.land w 15) _ = _
    rw [strictN_eq, land15, walkPn]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw, hw]
      rfl
    · rw [if_neg hw, beq_false hw]
      change strictN _ _ = _
      rw [strictN_eq, shr4, walkP_eq' P n]
      rfl

theorem walkP_eq (P : List ℕ) (w k : ℕ) : CFSG.KC.Co1RankRec.walkP P w k = walkPn P 8 w k :=
  walkP_eq' P 8 w k

@[expose] def wordOKn (nG : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, w => if w % 16 = 0 then true else (decide (w % 16 ≤ nG) && wordOKn nG n (w / 16))

theorem wordOK_eq' (nG : ℕ) : ∀ n w, Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih w => strictB (Nat.land w 15) fun l =>
      bIf(Nat.beq l 0, true, bAnd(Nat.ble l nG, ih (Nat.shiftRight w 4)))) n w = wordOKn nG n w
  | 0, _ => rfl
  | n + 1, w => by
    change strictB (Nat.land w 15) _ = _
    rw [strictB_eq', land15, wordOKn]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw, hw]
      rfl
    · rw [if_neg hw, beq_false hw]
      change Bool.rec (motive := fun _ => Bool) false _ (Nat.ble (w % 16) nG) = _
      rw [shr4, wordOK_eq' nG n]
      cases hb : Nat.ble (w % 16) nG
      · have : ¬ w % 16 ≤ nG := fun h => by rw [Nat.ble_eq_true_of_le h] at hb; cases hb
        simp [this]
      · simp [Nat.le_of_ble_eq_true hb]

theorem wordOK_eq (nG w : ℕ) : CFSG.KC.Co1RankRec.wordOK nG w = wordOKn nG 8 w :=
  wordOK_eq' nG 8 w

variable {G : Type*} [Group G]

@[expose] def sWn (gg : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | n + 1, w => if w % 16 = 0 then 1 else sWn gg n (w / 16) * gg (w % 16 - 1)

theorem sWn_mem {gg : ℕ → G} {nG : ℕ} {S : Subgroup G} (hgg : ∀ g < nG, gg g ∈ S) :
    ∀ n w, wordOKn nG n w = true → sWn gg n w ∈ S
  | 0, _, _ => S.one_mem
  | n + 1, w, h => by
    rw [wordOKn] at h
    rw [sWn]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw]
      exact S.one_mem
    · rw [if_neg hw] at h ⊢
      obtain ⟨hl, h⟩ := Bool.and_eq_true_iff.1 h
      have := of_decide_eq_true hl
      exact S.mul_mem (sWn_mem hgg n _ h) (hgg _ (by omega))

theorem walkPn_conj {f : ℕ → G} {Pl : List ℕ} {gg : ℕ → G} {nG nU : ℕ}
    (hP : ∀ g < nG, ∀ u < nU, fld(getL Pl g, Nat.mul 12 u, 4095) < nU ∧
      f (fld(getL Pl g, Nat.mul 12 u, 4095)) = gg g * f u * (gg g)⁻¹) :
    ∀ n w k, k < nU → wordOKn nG n w = true →
      walkPn Pl n w k < nU ∧ f (walkPn Pl n w k) = sWn gg n w * f k * (sWn gg n w)⁻¹
  | 0, _, k, hk, _ => ⟨hk, by simp [walkPn, sWn]⟩
  | n + 1, w, k, hk, h => by
    rw [wordOKn] at h
    rw [walkPn, sWn]
    by_cases hw : w % 16 = 0
    · rw [if_pos hw, if_pos hw]
      exact ⟨hk, by simp⟩
    · rw [if_neg hw] at h ⊢
      rw [if_neg hw]
      obtain ⟨hl, h⟩ := Bool.and_eq_true_iff.1 h
      have := of_decide_eq_true hl
      obtain ⟨h1, h2⟩ := hP (w % 16 - 1) (by omega) k hk
      obtain ⟨h3, h4⟩ := walkPn_conj hP n (w / 16) _ h1 h
      refine ⟨h3, ?_⟩
      rw [h4]
      change _ * f (fld(getL Pl (w % 16 - 1), Nat.mul 12 k, 4095)) * _ = _
      rw [h2]
      group

variable [Finite G]

structure RepOK (C : Dat) (b w : ℕ → G) (tA : ℕ → Prop) (U : ℕ → ℕ) (nU nG : ℕ) (Pl : List ℕ)
    (n : ℕ → ℕ) (gs St : ℕ → ℕ → List ℕ) (r a : ℕ) : Prop where
  len : (gs r a).length = r
  lt : ∀ g ∈ gs r a, g < 2 ^ (C.d + 7)
  comm : ∀ g ∈ gs r a, ∀ h ∈ gs r a, mulC C g h = mulC C h g
  sq : ∀ g ∈ gs r a, mulC C g g = 0
  slen : (St r a).length = 2 ^ r - 1
  shead : 0 ∈ St r a
  snodup : (St r a).Nodup
  smem : ∀ k ∈ St r a, k < nU ∧ U k ∈ spanL C (gs r a)
  cand : ∀ x < 2 ^ (C.d + 7), mulC C x x = 0 → (∀ g ∈ gs r a, mulC C g x = mulC C x g) →
    x ∈ spanL C (gs r a) ∨ (∃ e ∈ spanL C (gs r a), tA (mulC C e x)) ∨
      ∃ u < nU, U u = x ∧ ∃ a' < n (r + 1), ∃ wd, wordOKn nG 8 wd = true ∧
        (∀ k ∈ St r a, ∃ k' ∈ St (r + 1) a', walkPn Pl 8 wd k' = k) ∧
        ∃ k' ∈ St (r + 1) a', walkPn Pl 8 wd k' = u

@[expose] def repSub (C : Dat) (b w : ℕ → G) (gs : List ℕ) : Subgroup G :=
  Subgroup.closure {x | x ∈ gs.map (el C.d b w)}

section Asm

variable {C : Dat} {b w : ℕ → G} (hM : Model C b w) (h0 : w 0 = 1)
  (hinj : ∀ x < 2 ^ (C.d + 7), ∀ y < 2 ^ (C.d + 7), el C.d b w x = el C.d b w y → x = y)
  {U : ℕ → ℕ} {nU : ℕ} (hU : ∀ u < nU, U u < 2 ^ (C.d + 7)) (hU0 : ∀ u < nU, U u ≠ 0)
  (hUinj : ∀ u < nU, ∀ v < nU, U u = U v → u = v)
include hM h0 hinj hU hU0 hUinj

theorem repSub_eq {tA : ℕ → Prop} {nG : ℕ} {Pl : List ℕ} {n : ℕ → ℕ} {gs St : ℕ → ℕ → List ℕ}
    {r a : ℕ} (hr : RepOK C b w tA U nU nG Pl n gs St r a) (hr1 : 1 ≤ r) :
    (repSub C b w (gs r a) : Set G) = el C.d b w '' {x | x ∈ 0 :: (St r a).map U} ∧
      Nat.card (repSub C b w (gs r a)) = 2 ^ r := by
  have hnd : (0 :: (St r a).map U).Nodup := by
    refine List.nodup_cons.2 ⟨fun h => ?_, ?_⟩
    · obtain ⟨k, hk, e⟩ := List.mem_map.1 h
      exact hU0 k (hr.smem k hk).1 e
    · exact List.Nodup.map_on (fun x hx y hy e => hUinj x (hr.smem x hx).1 y (hr.smem y hy).1 e)
        hr.snodup
  have hlen : (0 :: (St r a).map U).length = 2 ^ (gs r a).length := by
    rw [List.length_cons, List.length_map, hr.slen, hr.len]
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    omega
  have hmem : ∀ x ∈ 0 :: (St r a).map U, x ∈ spanL C (gs r a) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact zero_mem_spanL hM _
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact (hr.smem k hk).2
  obtain ⟨h1, h2⟩ := closure_el_eq hM h0 hinj hr.lt hr.comm hr.sq hnd hlen hmem
  exact ⟨h1, by rw [repSub, h2, hr.len]⟩

theorem mem_repSub {tA : ℕ → Prop} {nG : ℕ} {Pl : List ℕ} {n : ℕ → ℕ} {gs St : ℕ → ℕ → List ℕ}
    {r a : ℕ} (hr : RepOK C b w tA U nU nG Pl n gs St r a) (hr1 : 1 ≤ r) {z : G} :
    z ∈ repSub C b w (gs r a) ↔ z = 1 ∨ ∃ k ∈ St r a, el C.d b w (U k) = z := by
  have := (repSub_eq hM h0 hinj hU hU0 hUinj hr hr1).1
  rw [← SetLike.mem_coe, this]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl (el_zero _ _ _ h0)
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact Or.inr ⟨k, hk, rfl⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨0, List.mem_cons_self, el_zero _ _ _ h0⟩
    · exact ⟨U k, List.mem_cons_of_mem _ (List.mem_map_of_mem hk), rfl⟩

theorem ext_of_coords {tA : ℕ → Prop} {A : Set G}
    (hA2 : ∀ z < 2 ^ (C.d + 7), tA z → el C.d b w z * el C.d b w z = 1 → el C.d b w z ≠ 1 →
      el C.d b w z ∈ A)
    {Pl : List ℕ} {gg : ℕ → G} {nG : ℕ} (hgg : ∀ g < nG, gg g ∈ elSub hM h0)
    (hP : ∀ g < nG, ∀ u < nU, fld(getL Pl g, Nat.mul 12 u, 4095) < nU ∧
      el C.d b w (U (fld(getL Pl g, Nat.mul 12 u, 4095))) =
        gg g * el C.d b w (U u) * (gg g)⁻¹)
    {n : ℕ → ℕ} (hn5 : n 5 = 0) {gs St : ℕ → ℕ → List ℕ}
    (hrep : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, RepOK C b w tA U nU nG Pl n gs St r a)
    {r a : ℕ} (hr1 : 1 ≤ r) (hr4 : r ≤ 4) (ha : a < n r) {y : G} (hy : y ∈ elSub hM h0)
    (hyy : y * y = 1) (hyc : ∀ e ∈ repSub C b w (gs r a), e * y = y * e)
    (hyR : y ∉ repSub C b w (gs r a)) (hyA : ∀ e ∈ repSub C b w (gs r a), e * y ∉ A) :
    r < 4 ∧ ∃ a' < n (r + 1), ∃ s ∈ elSub hM h0,
      repSub C b w (gs r a) ≤ (repSub C b w (gs (r + 1) a')).map (MulAut.conj s).toMonoidHom ∧
      y ∈ (repSub C b w (gs (r + 1) a')).map (MulAut.conj s).toMonoidHom := by
  have hr := hrep r hr1 hr4 a ha
  obtain ⟨x, hx, rfl⟩ := hy
  have hmemG : ∀ g ∈ gs r a, el C.d b w g ∈ repSub C b w (gs r a) := fun g hg =>
    Subgroup.subset_closure (List.mem_map_of_mem hg)
  have hmemS : ∀ e ∈ spanL C (gs r a), el C.d b w e ∈ repSub C b w (gs r a) := by
    intro e he
    rw [← SetLike.mem_coe, repSub, closure_coe_eq hM h0 hr.lt hr.comm hr.sq]
    exact List.mem_map_of_mem he
  have hxx : mulC C x x = 0 :=
    hinj _ (mulC_lt C x x) _ (Nat.two_pow_pos _) (by rw [el_mulC hM hx hx, hyy, el_zero _ _ _ h0])
  have hxc : ∀ g ∈ gs r a, mulC C g x = mulC C x g := fun g hg =>
    hinj _ (mulC_lt C g x) _ (mulC_lt C x g) (by
      rw [el_mulC hM (hr.lt g hg) hx, el_mulC hM hx (hr.lt g hg), hyc _ (hmemG g hg)])
  rcases hr.cand x hx hxx hxc with hs | ⟨e, he, hte⟩ | ⟨u, hu, rfl, a', ha', wd, hwd, hsub, k', hk', hku⟩
  · exact absurd (hmemS x hs) hyR
  · exfalso
    have heR := hmemS e he
    have helt := spanL_lt hM hr.lt e he
    have hz := el_mulC hM helt hx
    have hcm := hyc _ heR
    refine hyA _ heR (hz ▸ hA2 _ (mulC_lt C e x) hte ?_ ?_)
    · rw [hz]
      have hee : el C.d b w e * el C.d b w e = 1 := by
        refine mul_self_of_mem_closure ?_ ?_ heR
        · intro _ hg' _ hh'
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
          obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hh'
          rw [← el_mulC hM (hr.lt g hg) (hr.lt h hh), ← el_mulC hM (hr.lt h hh) (hr.lt g hg),
            hr.comm g hg h hh]
        · intro _ hg'
          obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hg'
          rw [← el_mulC hM (hr.lt g hg) (hr.lt g hg), hr.sq g hg, el_zero _ _ _ h0]
      calc el C.d b w e * el C.d b w x * (el C.d b w e * el C.d b w x)
          = el C.d b w e * el C.d b w e * (el C.d b w x * el C.d b w x) := by
            rw [mul_assoc, ← mul_assoc (el C.d b w x), ← hcm]
            group
        _ = 1 := by rw [hee, hyy, one_mul]
    · rw [hz]
      intro h1
      refine hyR ?_
      rw [eq_inv_of_mul_eq_one_right h1]
      exact Subgroup.inv_mem _ heR
  · have hr4' : r < 4 := by
      rcases Nat.lt_or_ge r 4 with h | h
      · exact h
      · have : r = 4 := by omega
        subst this
        rw [hn5] at ha'
        exact absurd ha' (Nat.not_lt_zero _)
    have hr' := hrep (r + 1) (by omega) (by omega) a' ha'
    have hconj : ∀ k' ∈ St (r + 1) a', walkPn Pl 8 wd k' < nU ∧
        el C.d b w (U (walkPn Pl 8 wd k')) =
          sWn gg 8 wd * el C.d b w (U k') * (sWn gg 8 wd)⁻¹ := fun k' hk' =>
      walkPn_conj (f := fun u => el C.d b w (U u)) hP 8 wd k' (hr'.smem k' hk').1 hwd
    refine ⟨hr4', a', ha', sWn gg 8 wd, sWn_mem hgg 8 wd hwd, ?_, ?_⟩
    · intro z hz
      rw [mem_map_conj]
      rcases (mem_repSub hM h0 hinj hU hU0 hUinj hr hr1).1 hz with rfl | ⟨k, hk, rfl⟩
      · simp
      · obtain ⟨k'', hk'', rfl⟩ := hsub k hk
        rw [(hconj k'' hk'').2]
        refine (mem_repSub hM h0 hinj hU hU0 hUinj hr' (by omega)).2 (Or.inr ⟨k'', hk'', ?_⟩)
        group
    · rw [mem_map_conj, ← hku, (hconj k' hk').2]
      refine (mem_repSub hM h0 hinj hU hU0 hUinj hr' (by omega)).2 (Or.inr ⟨k', hk', ?_⟩)
      group

theorem card_le_of_coords {tA : ℕ → Prop} {A : Set G}
    (hA : ∀ s ∈ elSub hM h0, ∀ x, s * x * s⁻¹ ∈ A ↔ x ∈ A)
    (hA2 : ∀ z < 2 ^ (C.d + 7), tA z → el C.d b w z * el C.d b w z = 1 → el C.d b w z ≠ 1 →
      el C.d b w z ∈ A)
    {Pl : List ℕ} {gg : ℕ → G} {nG : ℕ} (hgg : ∀ g < nG, gg g ∈ elSub hM h0)
    (hP : ∀ g < nG, ∀ u < nU, fld(getL Pl g, Nat.mul 12 u, 4095) < nU ∧
      el C.d b w (U (fld(getL Pl g, Nat.mul 12 u, 4095))) =
        gg g * el C.d b w (U u) * (gg g)⁻¹)
    {n : ℕ → ℕ} (hn1 : 0 < n 1) (hn5 : n 5 = 0) {gs St : ℕ → ℕ → List ℕ}
    (hrep : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, RepOK C b w tA U nU nG Pl n gs St r a)
    {E : Subgroup G} (hE : Good (elSub hM h0) A E) (hcE : el C.d b w (U 0) ∈ E) :
    Nat.card E ≤ 16 := by
  have hR := fun r hr1 hr4 a ha => repSub_eq hM h0 hinj hU hU0 hUinj (hrep r hr1 hr4 a ha) hr1
  have hcR : ∀ r, 1 ≤ r → r ≤ 4 → ∀ a < n r, el C.d b w (U 0) ∈ repSub C b w (gs r a) :=
    fun r hr1 hr4 a ha => (mem_repSub hM h0 hinj hU hU0 hUinj (hrep r hr1 hr4 a ha) hr1).2
      (Or.inr ⟨0, (hrep r hr1 hr4 a ha).shead, rfl⟩)
  have hR1 : repSub C b w (gs 1 0) = Subgroup.zpowers (el C.d b w (U 0)) := by
    have hr := hrep 1 le_rfl (by omega) 0 hn1
    have hnU : 0 < nU := (hr.smem 0 hr.shead).1
    have hc1 : el C.d b w (U 0) ≠ 1 := fun h =>
      hU0 0 hnU (hinj _ (hU 0 hnU) _ (Nat.two_pow_pos _) (by rw [h, el_zero _ _ _ h0]))
    have hcard := (hR 1 le_rfl (by omega) 0 hn1).2
    have hle : Subgroup.zpowers (el C.d b w (U 0)) ≤ repSub C b w (gs 1 0) :=
      (Subgroup.zpowers_le).2 (hcR 1 le_rfl (by omega) 0 hn1)
    have : Finite (repSub C b w (gs 1 0)) := inferInstance
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hcard, Nat.card_zpowers]
    have hdvd : orderOf (el C.d b w (U 0)) ∣ 2 := by
      have := Subgroup.card_dvd_of_le hle
      rw [hcard, Nat.card_zpowers] at this
      simpa using this
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hc1
    · rw [h]
      norm_num
  refine card_le_of_ext hA (fun r a => repSub C b w (gs r a)) n hn1 hR1
    (fun r hr1 hr4 a ha => (hR r hr1 hr4 a ha).2) hcR ?_ hE hcE
  intro r hr1 hr4 a ha y hy hyy hyc hyR hyA
  exact ext_of_coords hM h0 hinj hU hU0 hUinj hA2 hgg hP hn5 hrep hr1 hr4 ha hy hyy hyc hyR hyA

end Asm

end CFSG.KS.SporSch.Co1Rank

end

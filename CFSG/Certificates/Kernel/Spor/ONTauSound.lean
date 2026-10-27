module

public import Certificates.Data.Kernel.Spor.ONTauK
public import CFSG.Certificates.Kernel.Spor.ONCSound

public section

namespace CFSG.KS.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KC.Ord CFSG.KS.Ord
open scoped Matrix

variable {G : Type*} [Group G] (φ : G →* Matrix (Fin 154) (Fin 154) (ZMod 3))

@[expose] def seedG (gA gB : G) (z : ℤ) : G :=
  if z = 1 then gA else if z = -1 then gA⁻¹ else if z = 2 then gB else gB⁻¹

@[expose] def Reps (X : Nat) (g : G) : Prop := Canon 3 154 11 X ∧ omat X = φ g

variable {φ}

theorem seedL_eq (a ai b bi : Nat) (z : ℤ) :
    seedL a ai b bi z = if z = 1 then a else if z = -1 then ai else if z = 2 then b else bi := by
  rcases z with (_ | _ | _ | n) | (_ | n)
  · rfl
  · rfl
  · rfl
  · rw [if_neg (by rw [Int.ofNat_eq_coe]; omega), if_neg (by rw [Int.ofNat_eq_coe]; omega),
      if_neg (by rw [Int.ofNat_eq_coe]; omega)]
    rfl
  · rw [if_neg (by decide), if_pos (by decide)]
    rfl
  · rw [if_neg (by rw [Int.negSucc_eq]; omega), if_neg (by rw [Int.negSucc_eq]; omega),
      if_neg (by rw [Int.negSucc_eq]; omega)]
    rfl

theorem seedL_reps {a ai b bi : Nat} {gA gB : G} (ha : Reps φ a gA) (hai : Reps φ ai gA⁻¹)
    (hb : Reps φ b gB) (hbi : Reps φ bi gB⁻¹) (z : ℤ) :
    Reps φ (seedL a ai b bi z) (seedG gA gB z) := by
  rw [seedL_eq]
  unfold seedG
  split_ifs
  · exact ha
  · exact hai
  · exact hb
  · exact hbi

theorem reps_mul {X Y : Nat} {g h : G} (hX : Reps φ X g) (hY : Reps φ Y h) :
    Reps φ (mul3 LL HH CM RM X Y) (g * h) := by
  obtain ⟨c, e⟩ := mul3_sound hX.1 hY.1
  exact ⟨c, by rw [e, hX.2, hY.2, map_mul]⟩

theorem reps_one : Reps φ ONE (1 : G) := ⟨one_canon.1, by rw [one_canon.2, map_one]⟩

theorem reps_inv {X Y : Nat} {g : G} (hX : Reps φ X g) (hY : Canon 3 154 11 Y)
    (h : mul3 LL HH CM RM X Y = ONE) : Reps φ Y g⁻¹ := by
  refine ⟨hY, ?_⟩
  have hm := (mul3_sound hX.1 hY).2
  rw [h, one_canon.2, hX.2] at hm
  calc omat Y = φ g⁻¹ * (φ g * omat Y) := by
        rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    _ = φ g⁻¹ := by rw [← hm, Matrix.mul_one]

theorem wordK_reps {L : Int → Nat} {gen : ℤ → G} (hL : ∀ z, Reps φ (L z) (gen z)) :
    ∀ (w : List Int) (acc : Nat) (x : G), Reps φ acc x →
      Reps φ (wordK (mul3 LL HH CM RM) L w acc) (x * CFSG.Sporadic.Th.wordG gen w)
  | [], acc, x, h => by
    have e : CFSG.Sporadic.Th.wordG gen [] = 1 := rfl
    rw [e, mul_one]
    exact h
  | z :: w, acc, x, h => by
    have e : wordK (mul3 LL HH CM RM) L (z :: w) acc =
        wordK (mul3 LL HH CM RM) L w (mul3 LL HH CM RM acc (L z)) := strictN_eq' _ _
    have e2 : CFSG.Sporadic.Th.wordG gen (z :: w) = gen z * CFSG.Sporadic.Th.wordG gen w := by
      simp [CFSG.Sporadic.Th.wordG]
    rw [e, e2, ← mul_assoc]
    exact wordK_reps hL w _ _ (reps_mul h (hL z))

theorem genK_reps {Gs : List Nat} {g : ℕ → G} (hG : ∀ i < Gs.length, Reps φ (Gs.getD i 0) (g i)) :
    ∀ (w : List Nat) (acc : Nat) (x : G), (∀ i ∈ w, i < Gs.length) → Reps φ acc x →
      Reps φ (genK (mul3 LL HH CM RM) Gs w acc) (x * (w.map g).prod)
  | [], acc, x, _, h => by
    have e : genK (mul3 LL HH CM RM) Gs [] acc = acc := rfl
    rw [e, List.map_nil, List.prod_nil, mul_one]
    exact h
  | i :: w, acc, x, hw, h => by
    have e : genK (mul3 LL HH CM RM) Gs (i :: w) acc =
        genK (mul3 LL HH CM RM) Gs w (mul3 LL HH CM RM acc (Gs.getD i 0)) := strictN_eq' _ _
    rw [e, List.map_cons, List.prod_cons, ← mul_assoc]
    exact genK_reps hG w _ _ (fun j hj => hw j (List.mem_cons_of_mem _ hj))
      (reps_mul h (hG i (hw i List.mem_cons_self)))

theorem gensK_eq (mul : Nat → Nat → Nat) (L : Int → Nat) (one : Nat) (gw : List (List Int))
    (k : List Nat → Bool) :
    gensK mul L one gw k = k (gw.map fun w => wordK mul L w one) := by
  unfold gensK
  suffices h : ∀ (gw : List (List Int)) (Gs : List Nat),
      List.rec (motive := fun _ => List Nat → Bool) (fun G => k G.reverse)
        (fun w _ ih G => strictB (wordK mul L w one) fun g => ih (g :: G)) gw Gs =
        k (Gs.reverse ++ gw.map fun w => wordK mul L w one) by
    simpa using h gw []
  intro gw
  induction gw with
  | nil => intro Gs; simp
  | cons w gw ih =>
    intro Gs
    change strictB (wordK mul L w one) (fun g => List.rec (motive := fun _ => List Nat → Bool)
      (fun G => k G.reverse) (fun w _ ih G => strictB (wordK mul L w one) fun g => ih (g :: G))
        gw (g :: Gs)) = _
    rw [strictB_eq', ih]
    simp

theorem pairsK_spec (mul : Nat → Nat → Nat) (one : Nat) (Gs : List Nat) :
    ∀ ps : List (List Nat × List Nat), pairsK mul one Gs ps = true →
      ∀ p ∈ ps, genK mul Gs p.1 one = genK mul Gs p.2 one
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: ps, h, p, hp => by
    have h' : bAnd(Nat.beq (genK mul Gs q.1 one) (genK mul Gs q.2 one), pairsK mul one Gs ps) =
      true := h
    rw [bAnd_iff'] at h'
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Nat.eq_of_beq_eq_true h'.1
    · exact pairsK_spec mul one Gs ps h'.2 p hp

theorem pairs_sound {a b bi : Nat} {gA gB : G} {gw : List (List Int)}
    {ps : List (List Nat × List Nat)} (ha : Reps φ a gA) (hb : Reps φ b gB)
    (h1 : mul3 LL HH CM RM a a = ONE) (hbi : Canon 3 154 11 bi) (h2 : mul3 LL HH CM RM b bi = ONE)
    (h3 : pairsK (mul3 LL HH CM RM) ONE
      (gw.map fun w => wordK (mul3 LL HH CM RM) (seedL a a b bi) w ONE) ps = true) :
    ∀ p ∈ ps, (∀ i ∈ p.1 ++ p.2, i < gw.length) →
      φ (p.1.map fun i => CFSG.Sporadic.Th.wordG (seedG gA gB) (gw.getD i [])).prod =
        φ (p.2.map fun i => CFSG.Sporadic.Th.wordG (seedG gA gB) (gw.getD i [])).prod := by
  have hL := seedL_reps ha (reps_inv ha ha.1 h1) hb (reps_inv hb hbi h2)
  have hG : ∀ i < (gw.map fun w => wordK (mul3 LL HH CM RM) (seedL a a b bi) w ONE).length,
      Reps φ ((gw.map fun w => wordK (mul3 LL HH CM RM) (seedL a a b bi) w ONE).getD i 0)
        (CFSG.Sporadic.Th.wordG (seedG gA gB) (gw.getD i [])) := by
    intro i hi
    rw [List.length_map] at hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
      Option.map_some, Option.getD_some]
    have := wordK_reps hL gw[i] ONE 1 reps_one
    rwa [one_mul] at this
  intro p hp hlt
  have hlen := List.length_map (as := gw) (f := fun w => wordK (mul3 LL HH CM RM) (seedL a a b bi) w ONE)
  have hl := genK_reps hG p.1 ONE 1 (fun i hi => hlen ▸ hlt i (List.mem_append_left _ hi)) reps_one
  have hr := genK_reps hG p.2 ONE 1 (fun i hi => hlen ▸ hlt i (List.mem_append_right _ hi)) reps_one
  rw [one_mul] at hl hr
  rw [← hl.2, ← hr.2, pairsK_spec _ _ _ ps h3 p hp]

theorem batK_reps {F : Nat → Nat} {g : G} (hF : ∀ c < 154, PV (F c))
    (hg : ∀ r c : Fin 154, φ g r c = vecK (F c.val) r) : Reps φ (batK CS DS F 0 154) g := by
  have hF' : ∀ c < 154, PV (F (0 + c)) := fun c hc => by rw [Nat.zero_add]; exact hF c hc
  refine ⟨batK_canon (le_refl 154) hF', ?_⟩
  ext r c
  rw [batK_omat (le_refl 154) hF', if_pos c.isLt, Nat.zero_add, hg]

theorem relsK_conj {mul : Nat → Nat → Nat → Nat → Nat → Nat → Nat}
    {bat : Nat → Nat → (Nat → Nat) → Nat → Nat → Nat} {cs₀ ds₀ L₀ H₀ cm₀ rm₀ one₀ a b bi : Nat}
    {FA FB : Nat → Nat} {gw : List (List Int)} {ps : List (List Nat × List Nat)}
    (ha : bat cs₀ ds₀ FA (nat_lit 0) (nat_lit 154) = a)
    (hb : bat cs₀ ds₀ FB (nat_lit 0) (nat_lit 154) = b)
    (hbi : mul L₀ H₀ cm₀ rm₀ (mul L₀ H₀ cm₀ rm₀ b b) b = bi)
    (h : (strictB cs₀ fun cs => strictB ds₀ fun ds => strictB L₀ fun L => strictB H₀ fun H =>
      strictB cm₀ fun cm => strictB rm₀ fun rm => strictB one₀ fun one =>
      strictB (bat cs ds FA (nat_lit 0) (nat_lit 154)) fun a =>
      strictB (bat cs ds FB (nat_lit 0) (nat_lit 154)) fun b =>
      strictB (mul L H cm rm (mul L H cm rm b b) b) fun bi =>
        bAnd(Nat.beq (mul L H cm rm a a) one, bAnd(Nat.beq (mul L H cm rm b bi) one,
          gensK (mul L H cm rm) (seedL a a b bi) one gw fun G =>
            pairsK (mul L H cm rm) one G ps))) = true) :
    mul L₀ H₀ cm₀ rm₀ a a = one₀ ∧ mul L₀ H₀ cm₀ rm₀ b bi = one₀ ∧
      pairsK (mul L₀ H₀ cm₀ rm₀) one₀
        (gw.map fun w => wordK (mul L₀ H₀ cm₀ rm₀) (seedL a a b bi) w one₀) ps = true := by
  subst ha hb hbi
  simp only [strictB_eq'] at h
  rw [bAnd_iff', bAnd_iff', gensK_eq] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, Nat.eq_of_beq_eq_true h.2.1, h.2.2⟩

theorem relsK_sound {FA FB : Nat → Nat} {gw : List (List Int)} {ps : List (List Nat × List Nat)}
    {gA gB : G} (h : relsK FA FB gw ps = true) (hFA : ∀ c < 154, PV (FA c))
    (hFB : ∀ c < 154, PV (FB c)) (hA : ∀ r c : Fin 154, φ gA r c = vecK (FA c.val) r)
    (hB : ∀ r c : Fin 154, φ gB r c = vecK (FB c.val) r) :
    ∀ p ∈ ps, (∀ i ∈ p.1 ++ p.2, i < gw.length) →
      φ (p.1.map fun i => CFSG.Sporadic.Th.wordG (seedG gA gB) (gw.getD i [])).prod =
        φ (p.2.map fun i => CFSG.Sporadic.Th.wordG (seedG gA gB) (gw.getD i [])).prod := by
  have ha := batK_reps (φ := φ) hFA hA
  have hb := batK_reps (φ := φ) hFB hB
  obtain ⟨h1, h2, h3⟩ := relsK_conj (mul := mul3) (bat := batK) (cs₀ := CS) (ds₀ := DS) (L₀ := LL)
    (H₀ := HH) (cm₀ := CM) (rm₀ := RM) (one₀ := ONE) (a := batK CS DS FA 0 154)
    (b := batK CS DS FB 0 154) rfl rfl rfl h
  exact pairs_sound ha hb h1 (mul3_sound (mul3_sound hb.1 hb.1).1 hb.1).1 h2 h3

end CFSG.KS.ONC

end

module

public import Certificates.Data.Kernel.HNFOrbK
public import CFSG.Certificates.Kernel.HNFFibSound

public section

namespace CFSG.KS.HNFOrb

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KC.HNFOrb
  CFSG.KS.HNF26720 CFSG.KS.HNF26729 CFSG.KS.HNFFib CFSG.KS.HNLocal CFSG.KC.LQT.SecS Matrix

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem tl_mem (P : Nat → Prop) : ∀ st : List Nat, (∀ x ∈ st, P x) → ∀ x ∈ tl st, P x
  | [], _, x, hx => absurd hx List.not_mem_nil
  | _ :: st, h, x, hx => h x (List.mem_cons_of_mem _ hx)

theorem nilB_true : ∀ {K : List Nat}, nilB K = true → K = []
  | [], _ => rfl
  | _ :: _, h => absurd h Bool.false_ne_true

theorem hdIs_true {k : Nat} {f : List Nat → Bool} :
    ∀ {K : List Nat}, hdIs k f K = true → ∃ K', K = k :: K' ∧ f K' = true
  | [], h => absurd h Bool.false_ne_true
  | k' :: K', h => by
    have e : hdIs k f (k' :: K') = andB (Nat.beq k k') (f K') := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := andB_true h
    exact ⟨K', by rw [Nat.eq_of_beq_eq_true h1], h2⟩

theorem emit_true {vec : Nat → Nat → Nat} {u x : Nat} {f : List Nat → Bool} {K : List Nat}
    (h : emit vec u x f K = true) : ∃ K', K = vec u x % keyM :: K' ∧ f K' = true := by
  have e : emit vec u x f K = hdIs (vec u x % keyM) f K :=
    CFSG.KS.HNF26720.strictB_eq (Nat.mod (vec u x) keyM) fun k => hdIs k f K
  rw [e] at h
  exact hdIs_true h

theorem walk_cons (mul vec : Nat → Nat → Nat) (b ONE u : Nat) (L : List (Nat × Nat)) (c : Nat)
    (ms st K : List Nat) : walk mul vec b ONE u L (c :: ms) st K =
      move mul vec b ONE u L c (walk mul vec b ONE u L ms) st K := rfl

theorem walk_sound (mul vec : Nat → Nat → Nat) (b ONE u : Nat) (L : List (Nat × Nat))
    (P : Nat → Prop) (Q : Nat × Nat → Prop) (hb : P b) (hd : Q (ONE, ONE)) (hL : ∀ p ∈ L, Q p)
    (hstep : ∀ x p, P x → Q p → P (mul (mul p.1 x) p.2)) :
    ∀ (ms st K : List Nat), (∀ x ∈ st, P x) → walk mul vec b ONE u L ms st K = true →
      ∀ k ∈ K, ∃ x, P x ∧ k = vec u x % keyM
  | [], st, K, _, h => by
    have e : walk mul vec b ONE u L [] st K = nilB K := rfl
    rw [e] at h
    rw [nilB_true h]
    exact fun k hk => absurd hk List.not_mem_nil
  | c :: ms, st, K, hst, h => by
    have ih := walk_sound mul vec b ONE u L P Q hb hd hL hstep ms
    rw [walk_cons] at h
    unfold move at h
    have htop : P (getN b st 0) := getN_mem P hb st hst 0
    cases h3 : Nat.beq c 3
    · rw [h3] at h
      cases h4 : Nat.beq c 4
      · rw [h4] at h
        have hx := hstep (getN b st 0) (getP (ONE, ONE) L (Nat.mod c 5)) htop
          (getP_mem Q hd L hL _)
        rw [CFSG.KS.HNF26720.strictB_eq] at h
        generalize mul (mul (getP (ONE, ONE) L (Nat.mod c 5)).1 (getN b st 0))
          (getP (ONE, ONE) L (Nat.mod c 5)).2 = x at hx h
        have hst' : ∀ y ∈ x :: st, P y := fun y hy => by
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hx
          · exact hst y hy
        cases h5 : Nat.blt c 3
        · rw [h5] at h
          exact ih _ K hst' h
        · rw [h5] at h
          obtain ⟨K', rfl, hK'⟩ := emit_true h
          intro k hk
          rcases List.mem_cons.1 hk with rfl | hk
          · exact ⟨x, hx, rfl⟩
          · exact ih _ K' hst' hK' k hk
      · rw [h4] at h
        obtain ⟨K', rfl, hK'⟩ := emit_true h
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact ⟨_, htop, rfl⟩
        · exact ih st K' hst hK' k hk
    · rw [h3] at h
      exact ih (tl st) K (tl_mem P st hst) h

theorem evO_getD (d : Nat) : ∀ (l : List Nat) (k : Nat),
    (evO l true).getD k d = l.getD (2 * k) d ∧ (evO l false).getD k d = l.getD (2 * k + 1) d
  | [], k => by simp [evO]
  | x :: l, k => by
    have e1 : evO (x :: l) true = x :: evO l false := rfl
    have e2 : evO (x :: l) false = evO l true := rfl
    rw [e1, e2]
    refine ⟨?_, ?_⟩
    · cases k with
      | zero => rfl
      | succ k =>
        rw [List.getD_cons_succ, (evO_getD d l k).2, Nat.mul_succ, List.getD_cons_succ]
    · rw [(evO_getD d l k).1, List.getD_cons_succ]

theorem evO_length : ∀ l : List Nat,
    (evO l true).length ≤ (l.length + 1) / 2 ∧ (evO l false).length ≤ l.length / 2
  | [] => by simp [evO]
  | x :: l => by
    have e1 : evO (x :: l) true = x :: evO l false := rfl
    have e2 : evO (x :: l) false = evO l true := rfl
    rw [e1, e2]
    have := evO_length l
    simp only [List.length_cons]
    omega

theorem getT_nd_succ (d : Nat) (l r : PT) (x j : Nat) :
    getT d (PT.nd l x r) (j + 1) =
      Bool.rec (motive := fun _ => Nat) (getT d r (j / 2)) (getT d l (j / 2)) (Nat.beq (j % 2) 1) :=
  rfl

theorem getT_ofT (d : Nat) : ∀ (n : Nat) (L : List Nat), L.length ≤ n →
    ∀ i, getT d (ofT n L) i = L.getD i d
  | 0, L, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    simp [ofT, getT]
  | n + 1, [], _, i => by simp [ofT, getT]
  | n + 1, x :: l, h, 0 => rfl
  | n + 1, x :: l, h, j + 1 => by
    have e : ofT (n + 1) (x :: l) = PT.nd (ofT n (evO l false)) x (ofT n (evO l true)) := rfl
    simp only [List.length_cons] at h
    have hl := evO_length l
    rw [e, getT_nd_succ, List.getD_cons_succ]
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · rw [hj]
      change getT d (ofT n (evO l true)) (j / 2) = _
      rw [getT_ofT d n _ (by omega), (evO_getD d l _).1]
      congr 1
      omega
    · rw [hj]
      change getT d (ofT n (evO l false)) (j / 2) = _
      rw [getT_ofT d n _ (by omega), (evO_getD d l _).2]
      congr 1
      omega

theorem lenF_eq : ∀ (l : List Nat) (a : Nat), lenF l a = a + l.length
  | [], a => rfl
  | x :: l, a => by
    have e : lenF (x :: l) a = lenF l (a + 1) := CFSG.KS.HNF26720.strictN_eq (a + 1) (lenF l)
    rw [e, lenF_eq l, List.length_cons]
    omega

theorem incrT_sound (T : PT) (n : Nat) :
    ∀ (ord : List Nat) (prev : Nat), incrT T n ord prev = true →
      (∀ i ∈ ord, i < n ∧ prev < getT 0 T i) ∧ (ord.map (getT 0 T)).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, prev, h => by
    have e1 : incrT T n (i :: ord) prev = andB (Nat.blt i n)
        (andB (Nat.blt prev (getT 0 T i)) (incrT T n ord (getT 0 T i))) :=
      congrArg (andB (Nat.blt i n)) (CFSG.KS.HNF26720.strictB_eq (getT 0 T i)
        fun x => andB (Nat.blt prev x) (incrT T n ord x))
    rw [e1] at h
    obtain ⟨h0, h⟩ := andB_true h
    obtain ⟨h1, h2⟩ := andB_true h
    have hlt : prev < getT 0 T i := Nat.blt_eq.mp h1
    obtain ⟨ih1, ih2⟩ := incrT_sound T n ord _ h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨Nat.blt_eq.mp h0, hlt⟩
      · exact ⟨(ih1 j hj).1, hlt.trans (ih1 j hj).2⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      exact (ih1 j hj).2

theorem distOK_sound {K ord : List Nat} {N : Nat} (h : distOK K ord N = true) :
    ∃ l : List Nat, l.Nodup ∧ l.length = N ∧ ∀ k ∈ l, k ∈ K := by
  unfold distOK at h
  obtain ⟨hN, h⟩ := andB_true h
  rw [CFSG.KS.HNF26720.strictB_eq, lenF_eq, Nat.zero_add] at h
  rw [lenF_eq, Nat.zero_add] at hN
  obtain ⟨h1, h2⟩ := incrT_sound _ _ ord 0 h
  refine ⟨ord.map (getT 0 (ofT K.length K)), h2.imp fun hab => Nat.ne_of_lt hab, ?_, ?_⟩
  · rw [List.length_map, Nat.eq_of_beq_eq_true hN]
  · intro k hk
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk
    rw [getT_ofT 0 _ K (Nat.le_refl _), List.getD_eq_getElem _ _ (h1 i hi).1]
    exact List.getElem_mem _

theorem flat_eq : ∀ L : List (List Nat), flat L = L.flatten
  | [] => rfl
  | l :: L => by
    have e : flat (l :: L) = l ++ flat L := rfl
    rw [e, flat_eq L, List.flatten_cons]

theorem getL_eq : ∀ (L : List (List Nat)) (j : Nat), getL L j = L.getD j []
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | x :: L, j + 1 => by
    have e : getL (x :: L) (j + 1) = getL L j := rfl
    rw [e, getL_eq L j, List.getD_cons_succ]

theorem card_le_keys {G : Type} [Group G] [Finite G]
    (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (S : Set G) (u : Nat) (keys : List Nat)
    (hnd : keys.Nodup)
    (hP : ∀ k ∈ keys, ∃ v, VCanon 5 133 13 v ∧ k = v % keyM ∧
      ∃ g ∈ S, toVec 5 133 13 v = toVec 5 133 13 u ᵥ* ρ g) :
    keys.length ≤ S.ncard := by
  classical
  have hsel : ∀ x : keys.toFinset, ∃ g : S, ∃ v, VCanon 5 133 13 v ∧ x.val = v % keyM ∧
      toVec 5 133 13 v = toVec 5 133 13 u ᵥ* ρ (g : G) := fun x => by
    obtain ⟨v, cv, ev, g, hg, e⟩ := hP x.val (List.mem_toFinset.1 x.2)
    exact ⟨⟨g, hg⟩, v, cv, ev, e⟩
  choose f hf using hsel
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨v1, c1, k1, e1⟩ := hf x
    obtain ⟨v2, c2, k2, e2⟩ := hf y
    have e : toVec 5 133 13 v1 = toVec 5 133 13 v2 := by rw [e1, e2, hxy]
    have ev := vec_inj (by norm_num) c1 c2 e
    exact Subtype.ext (by rw [k1, k2, ev])
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd,
    Nat.card_coe_set_eq] at h1

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem chunk_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 wi : List Int} {u : Nat} {ms K : List Nat}
    (h : chunk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 wi u ms K = true)
    {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (C : Subgroup G) (β : G)
    (eβ : ρ β = MW A B Bi (wi ++ 1 :: invW wi))
    (h1 : ∃ k ∈ C, ρ k = MW A B Bi w1 ∧ ρ k⁻¹ = MW A B Bi (invW w1))
    (h2 : ∃ k ∈ C, ρ k = MW A B Bi w2 ∧ ρ k⁻¹ = MW A B Bi (invW w2))
    (hA : ∃ k ∈ C, ρ k = OM A ∧ ρ k⁻¹ = OM A) :
    ∀ k ∈ K, ∃ v, VCanon 5 133 13 v ∧ k = v % keyM ∧
      ∃ g ∈ conjS C β, toVec 5 133 13 v = toVec 5 133 13 u ᵥ* ρ g := by
  unfold chunk at h
  obtain ⟨hu, h⟩ := andB_true h
  have cu : VCanon 5 133 13 u := CFSG.KS.J4Hub.validV_canon hc hu
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨c1, e1⟩ := wprod_sound hc cA cB cBi w1
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2, e2⟩ := wprod_sound hc cA cB cBi w2
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  obtain ⟨cbt, ebt⟩ := wprod_sound hc cA cB cBi (wi ++ 1 :: invW wi)
  obtain ⟨cONE, eONE⟩ := one_sound hc
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w1 = g1 at c1 e1 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1) = g1i at c1i e1i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w2 = g2 at c2 e2 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2) = g2i at c2i e2i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (wi ++ 1 :: invW wi) = bt
    at cbt ebt h
  have e1' : OM g1 = MW A B Bi w1 := e1
  have e1i' : OM g1i = MW A B Bi (invW w1) := e1i
  have e2' : OM g2 = MW A B Bi w2 := e2
  have e2i' : OM g2i = MW A B Bi (invW w2) := e2i
  have ebt' : OM bt = MW A B Bi (wi ++ 1 :: invW wi) := ebt
  let P : Nat → Prop := fun x => Canon 5 133 13 x ∧ ∃ g ∈ C, OM x = ρ (g * β * g⁻¹)
  let Q : Nat × Nat → Prop := fun p =>
    Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ C, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹
  have hPb : P bt := ⟨cbt, 1, C.one_mem, by rw [ebt', ← eβ, one_mul, inv_one, mul_one]⟩
  have hQd : Q (ONE, ONE) := by
    refine ⟨cONE, cONE, 1, C.one_mem, ?_, ?_⟩
    · change ordMat 5 133 13 1729 ONE = _
      rw [eONE, map_one]
    · change ordMat 5 133 13 1729 ONE = _
      rw [eONE, inv_one, map_one]
  have hQL : ∀ p ∈ [(g1, g1i), (g2, g2i), (A, A)], Q p := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · obtain ⟨k, hk, ek, eki⟩ := h1
      exact ⟨c1, c1i, k, hk, e1'.trans ek.symm, e1i'.trans eki.symm⟩
    · obtain ⟨k, hk, ek, eki⟩ := h2
      exact ⟨c2, c2i, k, hk, e2'.trans ek.symm, e2i'.trans eki.symm⟩
    · obtain ⟨k, hk, ek, eki⟩ := hA
      exact ⟨cA, cA, k, hk, ek.symm, eki.symm⟩
  have hstep : ∀ (x : Nat) (p : Nat × Nat), P x → Q p →
      P (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 x) p.2) := by
    rintro x p ⟨cx, k, hk, ex⟩ ⟨cp1, cp2, s, hs, es1, es2⟩
    obtain ⟨c3, e3⟩ := mul_sound hc cp1 cx
    obtain ⟨c4, e4⟩ := mul_sound hc c3 cp2
    refine ⟨c4, s * k, C.mul_mem hs hk, ?_⟩
    rw [e4, e3, es1, es2, ex]
    simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
  intro k hk
  obtain ⟨x, ⟨cx, g, hg, ex⟩, rfl⟩ := walk_sound _ _ bt ONE u _ P Q hPb hQd hQL hstep ms [] K
    (fun x hx => absurd hx List.not_mem_nil) h k hk
  obtain ⟨cv, ev⟩ := vecR_sound hc cu cx
  exact ⟨_, cv, rfl, g * β * g⁻¹, ⟨g, hg, rfl⟩, by rw [ev]; exact congrArg _ ex⟩

theorem orbit_bound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 wi : List Int} {u : Nat} {mv ks : List (List Nat)}
    {ord : List Nat} {N : Nat}
    (hch : ∀ j < ks.length, chunk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 wi u (getL mv j) (getL ks j) = true)
    (hd : distOK (flat ks) ord N = true)
    {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (C : Subgroup G) (β : G) (eβ : ρ β = MW A B Bi (wi ++ 1 :: invW wi))
    (h1 : ∃ k ∈ C, ρ k = MW A B Bi w1 ∧ ρ k⁻¹ = MW A B Bi (invW w1))
    (h2 : ∃ k ∈ C, ρ k = MW A B Bi w2 ∧ ρ k⁻¹ = MW A B Bi (invW w2))
    (hA : ∃ k ∈ C, ρ k = OM A ∧ ρ k⁻¹ = OM A) :
    N ≤ (conjS C β).ncard := by
  obtain ⟨l, hnd, hlen, hmem⟩ := distOK_sound hd
  rw [← hlen]
  refine card_le_keys ρ (conjS C β) u l hnd fun k hk => ?_
  have hk' := hmem k hk
  rw [flat_eq, List.mem_flatten] at hk'
  obtain ⟨K, hK, hkK⟩ := hk'
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hK
  have hc' := hch j hj
  rw [getL_eq ks, List.getD_eq_getElem _ _ hj] at hc'
  exact chunk_sound hc cA cB cBi hc' ρ C β eβ h1 h2 hA k hkK

end Sound

end CFSG.KS.HNFOrb

end

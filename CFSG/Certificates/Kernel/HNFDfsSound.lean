module

public import Certificates.Data.Kernel.HNFDfsK
public import CFSG.Certificates.Kernel.HNFFibSound

public section

namespace CFSG.KS.HNFDfs

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KC.HNFDfs
  CFSG.KS.HNF26720 CFSG.KS.HNF26729 CFSG.KS.HNFFib CFSG.KS.HNLocal CFSG.KC.LQT.SecS Matrix

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem tlN_eq (l : List Nat) : tlN l = l.tail := by
  cases l <;> rfl

theorem dropN_eq : ∀ (n : Nat) (l : List Nat), dropN n l = l.drop n
  | 0, l => rfl
  | n + 1, l => by
    have e : dropN (n + 1) l = dropN n (tlN l) := rfl
    rw [e, dropN_eq n, tlN_eq]
    cases l <;> simp

theorem mem_of_dropN {P : Nat → Prop} {l : List Nat} (h : ∀ x ∈ l, P x) (n : Nat) :
    ∀ x ∈ dropN n l, P x := by
  rw [dropN_eq]
  exact fun x hx => h x (List.mem_of_mem_drop hx)

theorem getN_zero (d : Nat) (l : List Nat) : getN d l 0 = l.headD d := by
  cases l <;> rfl

theorem keysC_nil : keysC [] = [] := rfl

theorem keysC_cons (e : Nat × Nat × Nat) (c : List (Nat × Nat × Nat)) :
    keysC (e :: c) = Bool.rec (motive := fun _ => List Nat) (keysC c) (e.2.2 :: keysC c)
      (Nat.blt e.2.1 4) := rfl

theorem appN_eq : ∀ l m : List Nat, appN l m = l ++ m
  | [], _ => rfl
  | x :: l, m => by
    have e : appN (x :: l) m = x :: appN l m := rfl
    rw [e, appN_eq l m, List.cons_append]

theorem getC_mem : ∀ (cs : List (List (Nat × Nat × Nat))) (i : Nat), i < cs.length →
    getC cs i ∈ cs
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | c :: _, 0, _ => List.mem_cons_self
  | c :: cs, i + 1, h => List.mem_cons_of_mem c
      (getC_mem cs i (by simp only [List.length_cons] at h; omega))

theorem mem_allK : ∀ (cs : List (List (Nat × Nat × Nat))) (k : Nat), k ∈ allK cs →
    ∃ i < cs.length, k ∈ keysC (getC cs i)
  | [], _, h => absurd h List.not_mem_nil
  | c :: cs, k, h => by
    have e : allK (c :: cs) = appN (keysC c) (allK cs) := rfl
    rw [e, appN_eq] at h
    rcases List.mem_append.1 h with h | h
    · exact ⟨0, by simp, h⟩
    · obtain ⟨i, hi, hk⟩ := mem_allK cs k h
      exact ⟨i + 1, by simp only [List.length_cons]; omega, hk⟩

theorem splitE_eq : ∀ (l : List Nat) (k : Nat),
    (splitE l).1.getD k 0 = l.getD (2 * k) 0 ∧ (splitE l).2.getD k 0 = l.getD (2 * k + 1) 0
  | [], k => by simp [splitE]
  | x :: l, k => by
    have e : splitE (x :: l) = (x :: (splitE l).2, (splitE l).1) := rfl
    rw [e]
    cases k with
    | zero =>
      refine ⟨by simp, ?_⟩
      rw [(splitE_eq l 0).1]
      simp
    | succ k =>
      have e2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
      refine ⟨?_, ?_⟩
      · rw [List.getD_cons_succ, (splitE_eq l k).2, e2, List.getD_cons_succ]
      · rw [List.getD_cons_succ, (splitE_eq l (k + 1)).1]

theorem splitE_length : ∀ l : List Nat,
    (splitE l).1.length ≤ (l.length + 1) / 2 ∧ (splitE l).2.length ≤ l.length / 2
  | [] => by simp [splitE]
  | x :: l => by
    have e : splitE (x :: l) = (x :: (splitE l).2, (splitE l).1) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := splitE_length l
    simp only [List.length_cons]
    omega

theorem getT_ofT : ∀ (n : Nat) (l : List Nat), l.length ≤ n → ∀ i, getT (ofT n l) i = l.getD i 0
  | 0, l, h, i => by
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 h)]
    rfl
  | n + 1, [], _, i => by simp only [List.getD_nil]; rfl
  | n + 1, x :: l, h, 0 => rfl
  | n + 1, x :: l, h, i + 1 => by
    simp only [List.length_cons] at h
    obtain ⟨hl1, hl2⟩ := splitE_length l
    have e : getT (ofT (n + 1) (x :: l)) (i + 1) =
        Bool.rec (motive := fun _ => Nat) (getT (ofT n (splitE l).2) (i / 2))
          (getT (ofT n (splitE l).1) (i / 2)) (Nat.beq (i % 2) 0) := rfl
    rw [e, List.getD_cons_succ]
    rcases Nat.mod_two_eq_zero_or_one i with hi | hi
    · have hb : Nat.beq (i % 2) 0 = true := by rw [hi]; rfl
      rw [hb]
      change getT (ofT n (splitE l).1) (i / 2) = _
      rw [getT_ofT n _ (by omega), (splitE_eq l _).1]
      congr 1
      omega
    · have hb : Nat.beq (i % 2) 0 = false := by rw [hi]; rfl
      rw [hb]
      change getT (ofT n (splitE l).2) (i / 2) = _
      rw [getT_ofT n _ (by omega), (splitE_eq l _).2]
      congr 1
      omega

theorem incT_sound (T : NT) (n : Nat) :
    ∀ (ord : List Nat) (prev : Nat), incT T n ord prev = true →
      (∀ i ∈ ord, i < n ∧ prev < getT T i) ∧ (ord.map (getT T)).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, prev, h => by
    have e1 : incT T n (i :: ord) prev =
        andB (Nat.blt i n) (andB (Nat.blt prev (getT T i)) (incT T n ord (getT T i))) := by
      change andB (Nat.blt i n) (strictB (getT T i) fun x => andB (Nat.blt prev x)
        (incT T n ord x)) = _
      rw [CFSG.KS.HNF26720.strictB_eq]
    rw [e1] at h
    obtain ⟨h0, h⟩ := andB_true h
    obtain ⟨h1, h2⟩ := andB_true h
    have hin : i < n := Nat.blt_eq.mp h0
    have hlt : prev < getT T i := Nat.blt_eq.mp h1
    obtain ⟨ih1, ih2⟩ := incT_sound T n ord _ h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact ⟨hin, hlt⟩
      · exact ⟨(ih1 j hj).1, hlt.trans (ih1 j hj).2⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact (ih1 j hj).2

theorem distL_sound {l ord : List Nat} (h : distL l ord = true) : ord.length ≤ l.toFinset.card := by
  classical
  unfold distL at h
  rw [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨hb, hpw⟩ := incT_sound _ _ ord 0 h
  have hnd : (ord.map (getT (ofT l.length l))).Nodup := hpw.imp fun hab => Nat.ne_of_lt hab
  have hsub : (ord.map (getT (ofT l.length l))).toFinset ⊆ l.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    rw [getT_ofT _ _ (Nat.le_refl _), List.getD_eq_getElem _ _ (hb i hi).1]
    exact List.mem_toFinset.2 (List.getElem_mem _)
  have := Finset.card_le_card hsub
  rwa [List.toFinset_card_of_nodup hnd, List.length_map] at this

theorem distK_sound {cs : List (List (Nat × Nat × Nat))} {M N : Nat} {ord : List Nat}
    (h : distK cs M ord N = true) : cs.length = M ∧ N ≤ (allK cs).toFinset.card := by
  unfold distK at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h3⟩ := andB_true h
  refine ⟨Nat.eq_of_beq_eq_true h1, ?_⟩
  rw [← Nat.eq_of_beq_eq_true h2]
  exact distL_sound h3

section Group

variable {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))

@[expose] def RealK (K : Subgroup G) (β : G) (u k : Nat) : Prop :=
  ∃ v, VCanon 5 133 13 v ∧ k = Nat.mod v PR ∧ ∃ g ∈ conjS K β, toVec 5 133 13 v = toVec 5 133 13 u ᵥ* ρ g

theorem card_le_of_real [Finite G] (K : Subgroup G) (β : G) (u : Nat) (l : List Nat)
    (hl : ∀ k ∈ l, RealK ρ K β u k) : l.toFinset.card ≤ (conjS K β).ncard := by
  classical
  have hsel : ∀ x : l.toFinset, ∃ v, VCanon 5 133 13 v ∧ x.val = Nat.mod v PR ∧
      ∃ g : conjS K β, toVec 5 133 13 v = toVec 5 133 13 u ᵥ* ρ (g : G) := fun x => by
    obtain ⟨v, cv, ev, g, hg, e⟩ := hl x.val (List.mem_toFinset.1 x.2)
    exact ⟨v, cv, ev, ⟨g, hg⟩, e⟩
  choose v cv ev f hf using hsel
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : toVec 5 133 13 (v x) = toVec 5 133 13 (v y) := by rw [hf x, hf y, hxy]
    have e2 : v x = v y := vec_inj (by norm_num) (cv x) (cv y) e
    exact Subtype.ext (by rw [ev x, ev y, e2])
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, Nat.card_coe_set_eq] at h1

end Group

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem walk_sound {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (K : Subgroup G) (β : G) {u b : Nat} (cu : VCanon 5 133 13 u) {Lr : List (Nat × Nat)}
    (P : Nat → Prop) (hP : ∀ x, P x ↔ Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹))
    (hb : P b)
    (hQ : ∀ p ∈ (ONE, ONE) :: Lr, Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧
      ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹) :
    ∀ (c : List (Nat × Nat × Nat)) (st : List Nat), (∀ x ∈ st, P x) →
      walk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) u b ONE Lr c st =
        true → ∀ k ∈ keysC c, RealK ρ K β u k
  | [], _, _, _, k, hk => absurd hk List.not_mem_nil
  | e :: c, st, hst, h, k, hk => by
    have e1 : walk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) u b ONE Lr
        (e :: c) st = stepW (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) u b
          ONE Lr e (walk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM) u b ONE
            Lr c) (dropN e.1 st) := rfl
    rw [e1] at h
    unfold stepW at h
    rw [CFSG.KS.HNF26720.strictB_eq] at h
    have hst' := mem_of_dropN hst e.1
    generalize dropN e.1 st = st' at h hst'
    have hpar : P (getN b st' 0) := getN_mem P hb st' hst' 0
    have hp : Canon 5 133 13 (getP (ONE, ONE) Lr e.2.1).1 ∧ Canon 5 133 13 (getP (ONE, ONE) Lr e.2.1).2 ∧
        ∃ k ∈ K, OM (getP (ONE, ONE) Lr e.2.1).1 = ρ k ∧ OM (getP (ONE, ONE) Lr e.2.1).2 = ρ k⁻¹ :=
      getP_mem _ (hQ _ List.mem_cons_self) Lr (fun p hp => hQ p (List.mem_cons_of_mem _ hp)) e.2.1
    generalize getP (ONE, ONE) Lr e.2.1 = p at h hp
    obtain ⟨cp1, cp2, s, hs, es1, es2⟩ := hp
    obtain ⟨cx, k0, hk0, ex⟩ := (hP _).1 hpar
    obtain ⟨c3, e3⟩ := mul_sound hc cp1 cx
    obtain ⟨c4, e4⟩ := mul_sound hc c3 cp2
    have hPx : P (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1
        (getN b st' 0)) p.2) := by
      refine (hP _).2 ⟨c4, s * k0, K.mul_mem hs hk0, ?_⟩
      rw [e4, e3, es1, es2, ex]
      simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
    have hRx : RealK ρ K β u (Nat.mod (vecR 5 13 1729 133 9 LV HV RM u (mulR 5 13 1729 133 9 L H
        CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 (getN b st' 0)) p.2)) PR) := by
      obtain ⟨cz, kz, hkz, ez⟩ := (hP _).1 hPx
      obtain ⟨c5, e5⟩ := vecR_sound hc cu cz
      exact ⟨_, c5, rfl, kz * β * kz⁻¹, ⟨kz, hkz, rfl⟩, by rw [e5]; exact congrArg _ ez⟩
    generalize mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1
      (getN b st' 0)) p.2 = x at h hPx hRx
    have hst2 : ∀ y ∈ x :: st', P y := fun y hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hPx
      · exact hst' y hy
    rw [keysC_cons] at hk
    generalize Nat.blt e.2.1 4 = bb at h hk
    cases bb with
    | false => exact walk_sound ρ K β cu P hP hb hQ c (x :: st') hst2 h k hk
    | true =>
      obtain ⟨h1, h2⟩ := andB_true h
      rcases List.mem_cons.1 hk with rfl | hk
      · rw [← Nat.eq_of_beq_eq_true h1]
        exact hRx
      · exact walk_sound ρ K β cu P hP hb hQ c (x :: st') hst2 h2 k hk

theorem chunk_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 w4 : List Int} {us : List (List Nat)} {u : Nat}
    {c : List (Nat × Nat × Nat)}
    (h : chunk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 w4 us u c = true)
    {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (K : Subgroup G) (β : G)
    (eβ : ρ β = MW A B Bi (w4 ++ 1 :: invW w4))
    (hK : ∀ w : List Int, (∀ l ∈ w, Valid3 l) → ∃ k ∈ K, ρ k = MS A B Bi w1 w2 w ∧
      ρ k⁻¹ = MS A B Bi w1 w2 (invW w)) :
    ∀ k ∈ keysC c, RealK ρ K β u k := by
  unfold chunk at h
  obtain ⟨hus, h⟩ := andB_true h
  obtain ⟨hu, h⟩ := andB_true h
  have vus : ∀ s ∈ us, ∀ l ∈ decW s, Valid3 l := fun s hs => okW_sound s (okWs_sound us hus s hs)
  have cu : VCanon 5 133 13 u := CFSG.KS.J4Hub.validV_canon hc hu
  simp only [CFSG.KS.HNF26720.strictB_eq, regs_eq] at h
  obtain ⟨c1, e1⟩ := wprod_sound hc cA cB cBi w1
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2, e2⟩ := wprod_sound hc cA cB cBi w2
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  obtain ⟨cb, eb⟩ := wprod_sound hc cA cB cBi (w4 ++ 1 :: invW w4)
  obtain ⟨cONE, eONE⟩ := one_sound hc
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w1 = g1 at c1 e1 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1) = g1i at c1i e1i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w2 = g2 at c2 e2 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2) = g2i at c2i e2i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (w4 ++ 1 :: invW w4) = b at cb eb h
  have eb' : OM b = ρ β := by rw [eβ]; exact eb
  have hS : ∀ w : List Int, (∀ l ∈ w, Valid3 l) →
      Canon 5 133 13 (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) w ONE) ∧
        OM (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) w ONE) =
          MS A B Bi w1 w2 w := by
    intro w hw
    obtain ⟨cs, es⟩ := wgoR_sound hc w (fun l hl => ltr3_canon cA c1 c1i c2 c2i (hw l hl)) ONE cONE
    refine ⟨cs, ?_⟩
    rw [es]
    change ordMat 5 133 13 1729 ONE * _ = _
    rw [eONE, one_mul, MS]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    rw [ltr3_map OM A g1 g1i g2 g2i (hw l hl), e1, e1i, e2, e2i]
    rfl
  refine walk_sound hc ρ K β cu
    (fun x => Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹)) (fun _ => Iff.rfl)
    ⟨cb, 1, K.one_mem, by rw [eb', one_mul, inv_one, mul_one]⟩ ?_ c [] (fun x hx => absurd hx List.not_mem_nil) h
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · refine ⟨cONE, cONE, 1, K.one_mem, ?_, ?_⟩
    · change ordMat 5 133 13 1729 ONE = _
      rw [eONE, map_one]
    · change ordMat 5 133 13 1729 ONE = _
      rw [eONE, inv_one, map_one]
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
    obtain ⟨cs, es⟩ := hS (decW s) (vus s hs)
    obtain ⟨csi, esi⟩ := hS (invW (decW s)) (valid3_invW (vus s hs))
    obtain ⟨k, hk, ek, eki⟩ := hK _ (vus s hs)
    exact ⟨cs, csi, k, hk, es.trans ek.symm, esi.trans eki.symm⟩

theorem dfs_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 w4 : List Int} {us : List (List Nat)} {u : Nat}
    {cs : List (List (Nat × Nat × Nat))} {M N : Nat} {ord : List Nat}
    (hall : ∀ i < M, chunk (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 w4 us u (getC cs i) = true)
    (hd : distK cs M ord N = true)
    {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
    (K : Subgroup G) (β : G) (eβ : ρ β = MW A B Bi (w4 ++ 1 :: invW w4))
    (hK : ∀ w : List Int, (∀ l ∈ w, Valid3 l) → ∃ k ∈ K, ρ k = MS A B Bi w1 w2 w ∧
      ρ k⁻¹ = MS A B Bi w1 w2 (invW w)) :
    N ≤ (conjS K β).ncard := by
  obtain ⟨hM, hN⟩ := distK_sound hd
  refine hN.trans (card_le_of_real ρ K β u _ fun k hk => ?_)
  obtain ⟨i, hi, hk⟩ := mem_allK cs k hk
  exact chunk_sound hc cA cB cBi (hall i (hM ▸ hi)) ρ K β eβ hK k hk

end Sound

end CFSG.KS.HNFDfs

end

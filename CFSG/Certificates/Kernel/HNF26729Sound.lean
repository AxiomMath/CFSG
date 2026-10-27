module

public import Certificates.Data.Kernel.HNF26729K
public import CFSG.Certificates.Kernel.HNF26720Sound
public import CFSG.Certificates.Kernel.J4Hub.BlockSound

public section

namespace CFSG.KS.HNF26729

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KS.HNF26720 CFSG.KS.HNLocal
open CFSG.KC.LQT.SecS Matrix

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

abbrev Valid3 (l : ℤ) : Prop := l ≠ 0 ∧ l.natAbs ≤ 3

@[expose] noncomputable def MW (A B Bi : Nat) (w : List Int) : Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  (w.map fun l => OM (ltr A B Bi l)).prod

@[expose] noncomputable def MS (A B Bi : Nat) (w1 w2 u : List Int) :
    Matrix (Fin 133) (Fin 133) (ZMod 5) :=
  (u.map (ltr3 (OM A) (MW A B Bi w1) (MW A B Bi (invW w1)) (MW A B Bi w2)
    (MW A B Bi (invW w2)))).prod

section Letters

variable {α : Type} (a g1 g1i g2 g2i : α)

theorem ltr3_one : ltr3 a g1 g1i g2 g2i 1 = a := rfl

theorem ltr3_two : ltr3 a g1 g1i g2 g2i 2 = g1 := rfl

theorem ltr3_three : ltr3 a g1 g1i g2 g2i 3 = g2 := rfl

theorem ltr3_neg_one : ltr3 a g1 g1i g2 g2i (-1) = a := rfl

theorem ltr3_neg_two : ltr3 a g1 g1i g2 g2i (-2) = g1i := rfl

theorem ltr3_neg_three : ltr3 a g1 g1i g2 g2i (-3) = g2i := rfl

end Letters

theorem ltr3_map {α β : Type} (f : α → β) (a g1 g1i g2 g2i : α) {l : ℤ} (hl : Valid3 l) :
    f (ltr3 a g1 g1i g2 g2i l) = ltr3 (f a) (f g1) (f g1i) (f g2) (f g2i) l := by
  have h6 : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = -1 ∨ l = -2 ∨ l = -3 := by omega
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem ltr3_canon {a g1 g1i g2 g2i : Nat} (ha : Canon 5 133 13 a) (h1 : Canon 5 133 13 g1)
    (h1i : Canon 5 133 13 g1i) (h2 : Canon 5 133 13 g2) (h2i : Canon 5 133 13 g2i) {l : ℤ}
    (hl : Valid3 l) : Canon 5 133 13 (ltr3 a g1 g1i g2 g2i l) := by
  have h6 : l = 1 ∨ l = 2 ∨ l = 3 ∨ l = -1 ∨ l = -2 ∨ l = -3 := by omega
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem getN_mem (P : Nat → Prop) {d : Nat} (hd : P d) :
    ∀ (l : List Nat), (∀ x ∈ l, P x) → ∀ i, P (getN d l i)
  | [], _, _ => hd
  | x :: l, h, 0 => h x List.mem_cons_self
  | x :: l, h, i + 1 => getN_mem P hd l (fun y hy => h y (List.mem_cons_of_mem x hy)) i

theorem go_sound (vec : Nat → Nat → Nat) (v S0 S1 : Nat) (P : Nat → Prop) (hv : P v)
    (hstep : ∀ u g, P u → P (vec u (nIf(Nat.beq g 0, S0, S1)))) :
    ∀ (t : List (Nat × Nat)) (acc : List Nat) (k : List Nat → Bool), (∀ x ∈ acc, P x) →
      go vec v S0 S1 t acc k = true → ∃ l : List Nat, (∀ x ∈ l, P x) ∧ k l = true
  | [], acc, k, hacc, h => ⟨acc, hacc, h⟩
  | e :: t, acc, k, hacc, h => by
    have e1 : go vec v S0 S1 (e :: t) acc k =
        go vec v S0 S1 t (vec (getN v acc e.1) (nIf(Nat.beq e.2 0, S0, S1)) :: acc) k :=
      CFSG.KS.HNF26720.strictB_eq (vec (getN v acc e.1) (nIf(Nat.beq e.2 0, S0, S1)))
        fun u => go vec v S0 S1 t (u :: acc) k
    rw [e1] at h
    refine go_sound vec v S0 S1 P hv hstep t _ k (fun x hx => ?_) h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hstep _ _ (getN_mem P hv acc hacc e.1)
    · exact hacc x hx

theorem incrK_sound (v : Nat) (l : List Nat) :
    ∀ (ord : List Nat) (prev : Nat), incrK v l ord prev = true →
      (∀ i ∈ ord, prev < getN v l i) ∧ (ord.map (getN v l)).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, prev, h => by
    have e1 : incrK v l (i :: ord) prev =
        andB (Nat.blt prev (getN v l i)) (incrK v l ord (getN v l i)) :=
      CFSG.KS.HNF26720.strictB_eq (getN v l i) fun x => andB (Nat.blt prev x) (incrK v l ord x)
    rw [e1] at h
    obtain ⟨h1, h2⟩ := andB_true h
    have hlt : prev < getN v l i := Nat.blt_eq.mp h1
    obtain ⟨ih1, ih2⟩ := incrK_sound v l ord (getN v l i) h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact hlt
      · exact hlt.trans (ih1 j hj)
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun b hb => ?_, ih2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
      exact ih1 j hj

section Group

variable {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))

theorem card_of_keys (K : Subgroup G) [Finite K] (v : Nat) (keys : List Nat) (hnd : keys.Nodup)
    (hP : ∀ x ∈ keys, VCanon 5 133 13 x ∧ ∃ h ∈ K, toVec 5 133 13 x = toVec 5 133 13 v ᵥ* ρ h) :
    keys.length ≤ Nat.card K := by
  classical
  have hsel : ∀ x : keys.toFinset, ∃ h : K,
      toVec 5 133 13 x.val = toVec 5 133 13 v ᵥ* ρ (h : G) := fun x => by
    obtain ⟨-, h, hh, e⟩ := hP x.val (List.mem_toFinset.1 x.2)
    exact ⟨⟨h, hh⟩, e⟩
  choose f hf using hsel
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : toVec 5 133 13 x.val = toVec 5 133 13 y.val := by
      rw [hf x, hf y, hxy]
    exact Subtype.ext (vec_inj (by norm_num) (hP x.val (List.mem_toFinset.1 x.2)).1
      (hP y.val (List.mem_toFinset.1 y.2)).1 e)
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd] at h1

variable {L H CM RM ONE LV HV : Nat}

theorem orbOK_sound (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true) (K : Subgroup G)
    [Finite K] {S0 S1 : Nat} {s0 s1 : G} (cS0 : Canon 5 133 13 S0) (cS1 : Canon 5 133 13 S1)
    (hs0 : s0 ∈ K) (hs1 : s1 ∈ K) (e0 : OM S0 = ρ s0) (e1 : OM S1 = ρ s1) {v N : Nat}
    {t : List (Nat × Nat)} {ord : List Nat}
    (h : orbOK (vecR 5 13 1729 133 9 LV HV RM) (validM 5 1729 LV HV) v S0 S1 N t ord = true) :
    N ≤ Nat.card K := by
  unfold orbOK at h
  obtain ⟨hv, h⟩ := andB_true h
  obtain ⟨hN, h⟩ := andB_true h
  have cv : VCanon 5 133 13 v := CFSG.KS.J4Hub.validV_canon hc hv
  let P : Nat → Prop := fun x =>
    VCanon 5 133 13 x ∧ ∃ g ∈ K, toVec 5 133 13 x = toVec 5 133 13 v ᵥ* ρ g
  have hPv : P v := ⟨cv, 1, K.one_mem, by rw [map_one, vecMul_one]⟩
  have hstep : ∀ u g, P u →
      P (vecR 5 13 1729 133 9 LV HV RM u (nIf(Nat.beq g 0, S0, S1))) := by
    intro u g hu
    obtain ⟨cu, x, hx, ex⟩ := hu
    have hS : Canon 5 133 13 (nIf(Nat.beq g 0, S0, S1)) ∧
        ∃ s ∈ K, OM (nIf(Nat.beq g 0, S0, S1)) = ρ s := by
      generalize Nat.beq g 0 = b
      cases b
      · exact ⟨cS1, s1, hs1, e1⟩
      · exact ⟨cS0, s0, hs0, e0⟩
    obtain ⟨cS, s, hs, es⟩ := hS
    obtain ⟨c2, e2⟩ := vecR_sound hc cu cS
    refine ⟨c2, x * s, K.mul_mem hx hs, ?_⟩
    rw [e2, ex, map_mul, ← vecMul_vecMul]
    exact congrArg _ es
  obtain ⟨l, hl, hk⟩ := go_sound _ v S0 S1 P hPv hstep t [v] _
    (fun x hx => by rw [List.mem_singleton.1 hx]; exact hPv) h
  obtain ⟨-, hpw⟩ := incrK_sound v l ord 0 hk
  have hnd : (ord.map (getN v l)).Nodup := hpw.imp fun hab => Nat.ne_of_lt hab
  have hcard := card_of_keys ρ K v _ hnd fun x hx => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact getN_mem P hPv l hl i
  rw [List.length_map, Nat.eq_of_beq_eq_true hN] at hcard
  exact hcard

end Group

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem wgoR_sound {R : Int → Nat} :
    ∀ (w : List Int), (∀ l ∈ w, Canon 5 133 13 (R l)) → ∀ (acc : Nat), Canon 5 133 13 acc →
      Canon 5 133 13 (wgoR (mulR 5 13 1729 133 9 L H CM RM) R w acc) ∧
        OM (wgoR (mulR 5 13 1729 133 9 L H CM RM) R w acc) = OM acc * (w.map fun l => OM (R l)).prod
  | [], _, acc, h => ⟨h, by rw [List.map_nil, List.prod_nil, mul_one]; rfl⟩
  | l :: w, hw, acc, h => by
    obtain ⟨h1, h2⟩ := mul_sound hc h (hw l List.mem_cons_self)
    have e : wgoR (mulR 5 13 1729 133 9 L H CM RM) R (l :: w) acc =
        wgoR (mulR 5 13 1729 133 9 L H CM RM) R w (mulR 5 13 1729 133 9 L H CM RM acc (R l)) :=
      strictN_eq _ _
    obtain ⟨h3, h4⟩ := wgoR_sound w (fun x hx => hw x (List.mem_cons_of_mem l hx)) _ h1
    rw [e]
    exact ⟨h3, by rw [h4, h2, List.map_cons, List.prod_cons, mul_assoc]⟩

theorem full_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 w8 u0 u1 : List Int} {v N : Nat} {t : List (Nat × Nat)}
    {ord : List Nat} (hu0 : ∀ l ∈ u0, Valid3 l) (hu1 : ∀ l ∈ u1, Valid3 l)
    (h : full (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 w8 u0 u1 v N t ord = true) :
    MS A B Bi w1 w2 u0 * MW A B Bi (w8 ++ 1 :: invW w8) =
        MW A B Bi (w8 ++ 1 :: invW w8) * MS A B Bi w1 w2 u0 ∧
      MS A B Bi w1 w2 u1 * MW A B Bi (w8 ++ 1 :: invW w8) =
        MW A B Bi (w8 ++ 1 :: invW w8) * MS A B Bi w1 w2 u1 ∧
      ∀ {G : Type} [Group G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (K : Subgroup G)
        [Finite K] {s0 s1 : G}, s0 ∈ K → s1 ∈ K → ρ s0 = MS A B Bi w1 w2 u0 →
          ρ s1 = MS A B Bi w1 w2 u1 → N ≤ Nat.card K := by
  unfold full at h
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨c1, e1⟩ := wprod_sound hc cA cB cBi w1
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2, e2⟩ := wprod_sound hc cA cB cBi w2
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  obtain ⟨cb, eb⟩ := wprod_sound hc cA cB cBi (w8 ++ 1 :: invW w8)
  obtain ⟨cONE, eONE⟩ := one_sound hc
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w1 = g1 at c1 e1 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1) = g1i at c1i e1i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w2 = g2 at c2 e2 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2) = g2i at c2i e2i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (w8 ++ 1 :: invW w8) = bt at cb eb h
  have hS : ∀ u : List Int, (∀ l ∈ u, Valid3 l) →
      Canon 5 133 13 (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) u ONE) ∧
        OM (wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) u ONE) =
          MS A B Bi w1 w2 u := by
    intro u hu
    obtain ⟨cs, es⟩ := wgoR_sound hc u (fun l hl => ltr3_canon cA c1 c1i c2 c2i (hu l hl)) ONE cONE
    refine ⟨cs, ?_⟩
    rw [es]
    change ordMat 5 133 13 1729 ONE * _ = _
    rw [eONE, one_mul, MS]
    congr 1
    refine List.map_congr_left fun l hl => ?_
    rw [ltr3_map OM A g1 g1i g2 g2i (hu l hl), e1, e1i, e2, e2i]
    rfl
  obtain ⟨cs0, es0⟩ := hS u0 hu0
  obtain ⟨cs1, es1⟩ := hS u1 hu1
  generalize wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) u0 ONE = s0 at cs0 es0 h
  generalize wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) u1 ONE = s1 at cs1 es1 h
  obtain ⟨hc0, h⟩ := andB_true h
  obtain ⟨hc1, h⟩ := andB_true h
  have comm : ∀ s : Nat, Canon 5 133 13 s →
      Nat.beq (mulR 5 13 1729 133 9 L H CM RM s bt) (mulR 5 13 1729 133 9 L H CM RM bt s) = true →
      OM s * OM bt = OM bt * OM s := by
    intro s cs hcs
    rw [← (mul_sound hc cs cb).2, ← (mul_sound hc cb cs).2]
    exact congrArg OM (Nat.eq_of_beq_eq_true hcs)
  have eb' : OM bt = MW A B Bi (w8 ++ 1 :: invW w8) := eb
  refine ⟨?_, ?_, ?_⟩
  · rw [← es0, ← eb']
    exact comm s0 cs0 hc0
  · rw [← es1, ← eb']
    exact comm s1 cs1 hc1
  · intro G _ ρ K _ x0 x1 hx0 hx1 ex0 ex1
    exact orbOK_sound ρ hc K cs0 cs1 hx0 hx1 (es0.trans ex0.symm) (es1.trans ex1.symm) h

end Sound

end CFSG.KS.HNF26729

end

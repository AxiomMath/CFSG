module

public import Certificates.Data.Kernel.HNFFibK
public import CFSG.Certificates.Kernel.HNF26729Sound

public section

namespace CFSG.KS.HNFFib

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib CFSG.KS.HNF26720
  CFSG.KS.HNF26729 CFSG.KS.HNLocal CFSG.KC.LQT.SecS Matrix

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

section Fibre

variable {G : Type} [Group G]

@[expose] def conjS (K : Subgroup G) (x : G) : Set G := {y | ∃ k ∈ K, k * x * k⁻¹ = y}

theorem conjS_eq (C : Subgroup G) {c y γ : G} (hc : c ∈ C) (h : c * γ * c⁻¹ = y) :
    conjS C y = conjS C γ := by
  ext x
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c, C.mul_mem hd hc, by rw [← h]; group⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨d * c⁻¹, C.mul_mem hd (C.inv_mem hc), by rw [← h]; group⟩

theorem fib_card [Finite G] (C K : Subgroup G) (a β : G) (hCa : ∀ c ∈ C, c * a = a * c)
    (hK : K ≤ C) (hKy : ∀ k ∈ K, k * (β * a * β⁻¹) = β * a * β⁻¹ * k) :
    (conjS C (β * a * β⁻¹)).ncard * (conjS K β).ncard ≤ (conjS C β).ncard := by
  classical
  have hf : ∀ c ∈ C, ∀ z : G,
      (c * z * c⁻¹) * a * (c * z * c⁻¹)⁻¹ = c * (z * a * z⁻¹) * c⁻¹ := by
    intro c hc z
    have hca : c⁻¹ * a * c = a := by
      rw [mul_assoc, ← hCa c hc, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (c * z * c⁻¹) * a * (c * z * c⁻¹)⁻¹ = c * z * (c⁻¹ * a * c) * z⁻¹ * c⁻¹ := by group
      _ = c * (z * a * z⁻¹) * c⁻¹ := by rw [hca]; group
  have hX : ∀ x ∈ conjS K β, x * a * x⁻¹ = β * a * β⁻¹ := by
    rintro x ⟨k, hk, rfl⟩
    rw [hf k (hK hk) β, hKy k hk, mul_assoc, mul_inv_cancel, mul_one]
  have hY : ∀ x ∈ conjS C (β * a * β⁻¹), ∃ c ∈ C, c * (β * a * β⁻¹) * c⁻¹ = x := fun _ hx => hx
  choose! c hcC hcy using hY
  let F : ↥(conjS C (β * a * β⁻¹)) × ↥(conjS K β) → ↥(conjS C β) := fun p =>
    ⟨c p.1 * p.2 * (c p.1)⁻¹, by
      obtain ⟨k, hk, hx⟩ := p.2.2
      refine ⟨c p.1 * k, C.mul_mem (hcC _ p.1.2) (hK hk), ?_⟩
      rw [← hx]
      group⟩
  have himg : ∀ yy ∈ conjS C (β * a * β⁻¹), ∀ xx ∈ conjS K β,
      (c yy * xx * (c yy)⁻¹) * a * (c yy * xx * (c yy)⁻¹)⁻¹ = yy := by
    intro yy hyy xx hxx
    rw [hf _ (hcC yy hyy) xx, hX xx hxx, hcy yy hyy]
  have hinj : Function.Injective F := by
    rintro ⟨⟨y1, hy1⟩, ⟨x1, hx1⟩⟩ ⟨⟨y2, hy2⟩, ⟨x2, hx2⟩⟩ he
    have he' : c y1 * x1 * (c y1)⁻¹ = c y2 * x2 * (c y2)⁻¹ := congrArg Subtype.val he
    have e1 := himg y1 hy1 x1 hx1
    rw [he', himg y2 hy2 x2 hx2] at e1
    subst e1
    have e2 : x1 = x2 := mul_left_cancel (mul_right_cancel he')
    subst e2
    rfl
  have h := Nat.card_le_card_of_injective F hinj
  rwa [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h

end Fibre

theorem okW_sound : ∀ w : List Nat, okW w = true → ∀ l ∈ decW w, Valid3 l
  | [], _, l, hl => absurd hl List.not_mem_nil
  | n :: w, h, l, hl => by
    have e : okW (n :: w) = andB (Nat.ble n 6) (andB (notB (Nat.beq n 3)) (okW w)) := rfl
    rw [e] at h
    obtain ⟨h1, h⟩ := andB_true h
    obtain ⟨h2, h3⟩ := andB_true h
    have e2 : decW (n :: w) = ((n : Int) - 3) :: decW w := rfl
    rw [e2] at hl
    rcases List.mem_cons.1 hl with rfl | hl
    · have hn6 : n ≤ 6 := Nat.le_of_ble_eq_true h1
      have hn3 : n ≠ 3 := by
        rintro rfl
        exact absurd h2 (by decide)
      exact ⟨by omega, by omega⟩
    · exact okW_sound w h3 l hl

theorem okWs_sound : ∀ us : List (List Nat), okWs us = true → ∀ u ∈ us, okW u = true
  | [], _, u, hu => absurd hu List.not_mem_nil
  | v :: us, h, u, hu => by
    have e : okWs (v :: us) = andB (okW v) (okWs us) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hu with rfl | hu
    · exact h1
    · exact okWs_sound us h2 u hu

theorem valid3_invW {w : List Int} (hw : ∀ l ∈ w, Valid3 l) : ∀ l ∈ invW w, Valid3 l := by
  intro l hl
  simp only [invW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨m, hm, rfl⟩ := hl
  have := hw m hm
  exact ⟨by omega, by omega⟩

theorem regs_eq (mul : Nat → Nat → Nat) (R : Int → Nat) (ONE : Nat) :
    ∀ (us : List (List Nat)) (k : List (Nat × Nat) → Bool),
      regs mul R ONE us k =
        k (us.map fun u => (wgoR mul R (decW u) ONE, wgoR mul R (invW (decW u)) ONE))
  | [], _ => rfl
  | u :: us, k => by
    have e : regs mul R ONE (u :: us) k = regs mul R ONE us
        (fun l => k ((wgoR mul R (decW u) ONE, wgoR mul R (invW (decW u)) ONE) :: l)) :=
      (CFSG.KS.HNF26720.strictB_eq (wgoR mul R (decW u) ONE) fun s =>
        strictB (wgoR mul R (invW (decW u)) ONE)
        fun si => regs mul R ONE us fun l => k ((s, si) :: l)).trans
      (CFSG.KS.HNF26720.strictB_eq (wgoR mul R (invW (decW u)) ONE)
        fun si => regs mul R ONE us fun l => k ((wgoR mul R (decW u) ONE, si) :: l))
    rw [e, regs_eq mul R ONE us, List.map_cons]

theorem getP_mem (Q : Nat × Nat → Prop) {d : Nat × Nat} (hd : Q d) :
    ∀ (l : List (Nat × Nat)), (∀ x ∈ l, Q x) → ∀ i, Q (getP d l i)
  | [], _, _ => hd
  | x :: l, h, 0 => h x List.mem_cons_self
  | x :: l, h, i + 1 => getP_mem Q hd l (fun y hy => h y (List.mem_cons_of_mem x hy)) i

theorem goT_sound (mul : Nat → Nat → Nat) (b ONE : Nat) (L : List (Nat × Nat)) (P : Nat → Prop)
    (Q : Nat × Nat → Prop) (hb : P b) (hd : Q (ONE, ONE)) (hL : ∀ p ∈ L, Q p)
    (hstep : ∀ x p, P x → Q p → P (mul (mul p.1 x) p.2)) :
    ∀ (t : List (Nat × Nat)) (acc : List Nat) (k : List Nat → Bool), (∀ x ∈ acc, P x) →
      goT mul b ONE L t acc k = true → ∃ l : List Nat, (∀ x ∈ l, P x) ∧ k l = true
  | [], acc, k, hacc, h => ⟨acc, hacc, h⟩
  | e :: t, acc, k, hacc, h => by
    have e1 : goT mul b ONE L (e :: t) acc k = goT mul b ONE L t
        (mul (mul (getP (ONE, ONE) L e.2).1 (getN b acc e.1)) (getP (ONE, ONE) L e.2).2 :: acc) k :=
      CFSG.KS.HNF26720.strictB_eq
        (mul (mul (getP (ONE, ONE) L e.2).1 (getN b acc e.1)) (getP (ONE, ONE) L e.2).2)
        fun x => goT mul b ONE L t (x :: acc) k
    rw [e1] at h
    refine goT_sound mul b ONE L P Q hb hd hL hstep t _ k (fun x hx => ?_) h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hstep _ _ (getN_mem P hb acc hacc e.1) (getP_mem Q hd L hL e.2)
    · exact hacc x hx

theorem incrV_sound (vec : Nat → Nat → Nat) (u b : Nat) (l : List Nat) :
    ∀ (ord : List Nat) (prev : Nat), incrV vec u b l ord prev = true →
      (∀ i ∈ ord, prev < vec u (getN b l i)) ∧
        (ord.map fun i => vec u (getN b l i)).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | i :: ord, prev, h => by
    have e1 : incrV vec u b l (i :: ord) prev =
        andB (Nat.blt prev (vec u (getN b l i))) (incrV vec u b l ord (vec u (getN b l i))) :=
      CFSG.KS.HNF26720.strictB_eq (vec u (getN b l i)) fun x => andB (Nat.blt prev x) (incrV vec u b l ord x)
    rw [e1] at h
    obtain ⟨h1, h2⟩ := andB_true h
    have hlt : prev < vec u (getN b l i) := Nat.blt_eq.mp h1
    obtain ⟨ih1, ih2⟩ := incrV_sound vec u b l ord _ h2
    refine ⟨fun j hj => ?_, ?_⟩
    · rcases List.mem_cons.1 hj with rfl | hj
      · exact hlt
      · exact hlt.trans (ih1 j hj)
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      exact ih1 j hj

theorem allC_sound (mul : Nat → Nat → Nat) (y : Nat) :
    ∀ L : List (Nat × Nat), allC mul y L = true → ∀ p ∈ L, mul p.1 y = mul y p.1
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: L, h, p, hp => by
    have e : allC mul y (q :: L) = andB (Nat.beq (mul q.1 y) (mul y q.1)) (allC mul y L) := rfl
    rw [e] at h
    obtain ⟨h1, h2⟩ := andB_true h
    rcases List.mem_cons.1 hp with rfl | hp
    · exact Nat.eq_of_beq_eq_true h1
    · exact allC_sound mul y L h2 p hp

theorem card_le_ncard {G : Type} [Group G] [Finite G]
    (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5)) (S : Set G) (u : Nat) (keys : List Nat)
    (hnd : keys.Nodup)
    (hP : ∀ x ∈ keys, VCanon 5 133 13 x ∧ ∃ g ∈ S, toVec 5 133 13 x = toVec 5 133 13 u ᵥ* ρ g) :
    keys.length ≤ S.ncard := by
  classical
  have hsel : ∀ x : keys.toFinset, ∃ g : S,
      toVec 5 133 13 x.val = toVec 5 133 13 u ᵥ* ρ (g : G) := fun x => by
    obtain ⟨-, g, hg, e⟩ := hP x.val (List.mem_toFinset.1 x.2)
    exact ⟨⟨g, hg⟩, e⟩
  choose f hf using hsel
  have hinj : Function.Injective f := by
    intro x y hxy
    have e : toVec 5 133 13 x.val = toVec 5 133 13 y.val := by
      rw [hf x, hf y, hxy]
    exact Subtype.ext (vec_inj (by norm_num) (hP x.val (List.mem_toFinset.1 x.2)).1
      (hP y.val (List.mem_toFinset.1 y.2)).1 e)
  have h1 := Nat.card_le_card_of_injective f hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd,
    Nat.card_coe_set_eq] at h1

section Sound

variable {L H CM RM ONE LV HV : Nat} (hc : constsOK 5 13 1729 133 9 L H CM RM ONE LV HV = true)
include hc

theorem fib_sound {A B Bi : Nat} (cA : Canon 5 133 13 A) (cB : Canon 5 133 13 B)
    (cBi : Canon 5 133 13 Bi) {w1 w2 wi wj : List Int} {c : List Nat} {us : List (List Nat)}
    {u N : Nat} {t : List (Nat × Nat)} {ord : List Nat}
    (h : fib (mulR 5 13 1729 133 9 L H CM RM) (vecR 5 13 1729 133 9 LV HV RM)
      (validM 5 1729 LV HV) A B Bi ONE w1 w2 wi wj c us u N t ord = true) :
    OM A * MW A B Bi w1 = MW A B Bi w1 * OM A ∧ OM A * MW A B Bi w2 = MW A B Bi w2 * OM A ∧
      (∀ l ∈ decW c, Valid3 l) ∧ (∀ s ∈ us, ∀ l ∈ decW s, Valid3 l) ∧
      MW A B Bi (wi ++ 1 :: invW wi) * OM A * MW A B Bi (wi ++ 1 :: invW wi) *
          MS A B Bi w1 w2 (decW c) =
        MS A B Bi w1 w2 (decW c) * MW A B Bi (wj ++ 1 :: invW wj) ∧
      (∀ s ∈ us, MS A B Bi w1 w2 (decW s) *
          (MW A B Bi (wi ++ 1 :: invW wi) * OM A * MW A B Bi (wi ++ 1 :: invW wi)) =
        MW A B Bi (wi ++ 1 :: invW wi) * OM A * MW A B Bi (wi ++ 1 :: invW wi) *
          MS A B Bi w1 w2 (decW s)) ∧
      ∀ {G : Type} [Group G] [Finite G] (ρ : G →* Matrix (Fin 133) (Fin 133) (ZMod 5))
        (K : Subgroup G) (β : G), ρ β = MW A B Bi (wi ++ 1 :: invW wi) →
        (∀ s ∈ us, ∃ k ∈ K, ρ k = MS A B Bi w1 w2 (decW s) ∧
          ρ k⁻¹ = MS A B Bi w1 w2 (invW (decW s))) →
        N ≤ (conjS K β).ncard := by
  unfold fib at h
  obtain ⟨hcw, h⟩ := andB_true h
  obtain ⟨hus, h⟩ := andB_true h
  have vc := okW_sound c hcw
  have vus : ∀ s ∈ us, ∀ l ∈ decW s, Valid3 l := fun s hs => okW_sound s (okWs_sound us hus s hs)
  simp only [CFSG.KS.HNF26720.strictB_eq] at h
  obtain ⟨c1, e1⟩ := wprod_sound hc cA cB cBi w1
  obtain ⟨c1i, e1i⟩ := wprod_sound hc cA cB cBi (invW w1)
  obtain ⟨c2, e2⟩ := wprod_sound hc cA cB cBi w2
  obtain ⟨c2i, e2i⟩ := wprod_sound hc cA cB cBi (invW w2)
  obtain ⟨cbi, ebi⟩ := wprod_sound hc cA cB cBi (wi ++ 1 :: invW wi)
  obtain ⟨cbj, ebj⟩ := wprod_sound hc cA cB cBi (wj ++ 1 :: invW wj)
  obtain ⟨cONE, eONE⟩ := one_sound hc
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w1 = g1 at c1 e1 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w1) = g1i at c1i e1i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE w2 = g2 at c2 e2 h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (invW w2) = g2i at c2i e2i h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (wi ++ 1 :: invW wi) = bi
    at cbi ebi h
  generalize wprod (mulR 5 13 1729 133 9 L H CM RM) A B Bi ONE (wj ++ 1 :: invW wj) = bj
    at cbj ebj h
  have ebi' : OM bi = MW A B Bi (wi ++ 1 :: invW wi) := ebi
  have ebj' : OM bj = MW A B Bi (wj ++ 1 :: invW wj) := ebj
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
  have meq : ∀ X Y Z V : Nat, Canon 5 133 13 X → Canon 5 133 13 Y → Canon 5 133 13 Z →
      Canon 5 133 13 V →
      Nat.beq (mulR 5 13 1729 133 9 L H CM RM X Y) (mulR 5 13 1729 133 9 L H CM RM Z V) = true →
      OM X * OM Y = OM Z * OM V := by
    intro X Y Z V cX cY cZ cV hb
    rw [← (mul_sound hc cX cY).2, ← (mul_sound hc cZ cV).2]
    exact congrArg OM (Nat.eq_of_beq_eq_true hb)
  obtain ⟨cy1, ey1⟩ := mul_sound hc cbi cA
  obtain ⟨cy, ey⟩ := mul_sound hc cy1 cbi
  rw [ey1] at ey
  generalize mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM bi A) bi = y
    at cy ey h
  obtain ⟨ccc, ecc⟩ := hS (decW c) vc
  generalize wgoR (mulR 5 13 1729 133 9 L H CM RM) (ltr3 A g1 g1i g2 g2i) (decW c) ONE = cc
    at ccc ecc h
  obtain ⟨hA1, h⟩ := andB_true h
  obtain ⟨hA2, h⟩ := andB_true h
  obtain ⟨hyc, h⟩ := andB_true h
  simp only [regs_eq] at h
  obtain ⟨hall, h⟩ := andB_true h
  obtain ⟨hu, h⟩ := andB_true h
  obtain ⟨hN, h⟩ := andB_true h
  have eY : OM y = MW A B Bi (wi ++ 1 :: invW wi) * OM A * MW A B Bi (wi ++ 1 :: invW wi) := by
    rw [ey, ebi']
  have hcomm := allC_sound _ y _ hall
  refine ⟨?_, ?_, vc, vus, ?_, ?_, ?_⟩
  · have := meq A g1 g1 A cA c1 c1 cA hA1
    rwa [e1] at this
  · have := meq A g2 g2 A cA c2 c2 cA hA2
    rwa [e2] at this
  · rw [← eY, ← ecc, ← ebj']
    exact meq y cc cc bj cy ccc ccc cbj hyc
  · intro s hs
    obtain ⟨cs, es⟩ := hS (decW s) (vus s hs)
    have hm := hcomm _ (List.mem_map.2 ⟨s, hs, rfl⟩)
    rw [← eY, ← es]
    rw [← (mul_sound hc cs cy).2, ← (mul_sound hc cy cs).2]
    exact congrArg OM hm
  · intro G _ _ ρ K β eβ hK
    have cu : VCanon 5 133 13 u := CFSG.KS.J4Hub.validV_canon hc hu
    have hPb : Canon 5 133 13 bi ∧ ∃ k ∈ K, OM bi = ρ (k * β * k⁻¹) :=
      ⟨cbi, 1, K.one_mem, by rw [ebi', ← eβ, one_mul, inv_one, mul_one]⟩
    have hQd : Canon 5 133 13 ONE ∧ Canon 5 133 13 ONE ∧ ∃ k ∈ K, OM ONE = ρ k ∧ OM ONE = ρ k⁻¹ := by
      refine ⟨cONE, cONE, 1, K.one_mem, ?_, ?_⟩
      · change ordMat 5 133 13 1729 ONE = _
        rw [eONE, map_one]
      · change ordMat 5 133 13 1729 ONE = _
        rw [eONE, inv_one, map_one]
    have hQL : ∀ p ∈ us.map (fun s => (wgoR (mulR 5 13 1729 133 9 L H CM RM)
        (ltr3 A g1 g1i g2 g2i) (decW s) ONE, wgoR (mulR 5 13 1729 133 9 L H CM RM)
        (ltr3 A g1 g1i g2 g2i) (invW (decW s)) ONE)),
        Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹ := by
      intro p hp
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
      obtain ⟨cs, es⟩ := hS (decW s) (vus s hs)
      obtain ⟨csi, esi⟩ := hS (invW (decW s)) (valid3_invW (vus s hs))
      obtain ⟨k, hk, ek, eki⟩ := hK s hs
      exact ⟨cs, csi, k, hk, es.trans ek.symm, esi.trans eki.symm⟩
    have hstep : ∀ (x : Nat) (p : Nat × Nat),
        (Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹)) →
        (Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹) →
        Canon 5 133 13 (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 x) p.2) ∧
          ∃ k ∈ K, OM (mulR 5 13 1729 133 9 L H CM RM (mulR 5 13 1729 133 9 L H CM RM p.1 x) p.2) =
            ρ (k * β * k⁻¹) := by
      rintro x p ⟨cx, k, hk, ex⟩ ⟨cp1, cp2, s, hs, es1, es2⟩
      obtain ⟨c3, e3⟩ := mul_sound hc cp1 cx
      obtain ⟨c4, e4⟩ := mul_sound hc c3 cp2
      refine ⟨c4, s * k, K.mul_mem hs hk, ?_⟩
      rw [e4, e3, es1, es2, ex]
      simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
    obtain ⟨l, hl, hk⟩ := goT_sound _ bi ONE _
      (fun x => Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹))
      (fun p => Canon 5 133 13 p.1 ∧ Canon 5 133 13 p.2 ∧ ∃ k ∈ K, OM p.1 = ρ k ∧ OM p.2 = ρ k⁻¹)
      hPb hQd hQL hstep t [bi] _ (fun x hx => by rw [List.mem_singleton.1 hx]; exact hPb) h
    obtain ⟨-, hpw⟩ := incrV_sound _ u bi l ord 0 hk
    have hnd := hpw.imp fun hab => Nat.ne_of_lt hab
    have hcard := card_le_ncard ρ (conjS K β) u _ hnd fun x hx => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
      obtain ⟨cz, k, hk, ez⟩ := getN_mem (fun x => Canon 5 133 13 x ∧ ∃ k ∈ K, OM x = ρ (k * β * k⁻¹))
        hPb l hl i
      obtain ⟨c5, e5⟩ := vecR_sound hc cu cz
      exact ⟨c5, k * β * k⁻¹, ⟨k, hk, rfl⟩, by rw [e5]; exact congrArg _ ez⟩
    rw [List.length_map, Nat.eq_of_beq_eq_true hN] at hcard
    exact hcard

end Sound

end CFSG.KS.HNFFib

end

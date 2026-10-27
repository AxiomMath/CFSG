
module

public import Certificates.Data.Kernel.F4PlanesTw
public import CFSG.Certificates.Kernel.F4Planes.E6RowSound
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6TwoBase
import all CFSG.Certificates.Kernel.E6SaltSound
import all CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6TwoBase

public section

namespace CFSG.KC.F4PlanesTw

open CFSG.KC.E6Salt CFSG.KC.Loop CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.SeitzGeneration.ExcHighThree.TwBits (Bits2 HasBits2 HasBits2.mul HasBits2.eq_iff
  hasBits2_one)
open CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6Two (Setup eltT tmat iota Xw0 Xw1 hasBits2_iota
  oX_mem oXY_mem_range eq_top_of_orbit)
open CFSG.KC.F4PlanesE6 (phiE iotaL allL_spec6 strictB_eq6 lenL_eq6 lt_of_blt blt_true blt_false
  hasBitsS_phiE map_phi)

set_option exponentiation.threshold 6400

theorem fa_eq (P : ℕ) : fa P = P % 2 ^ 6400 := rfl

theorem fb_eq (P : ℕ) : fb P = P / 2 ^ 6400 :=
  Nat.shiftRight_eq_div_pow P 6400

theorem pr_eq (A B : ℕ) : pr A B = A % 2 ^ 6400 + B * 2 ^ 6400 := by
  change A % 2 ^ 6400 + B <<< 6400 = _
  rw [Nat.shiftLeft_eq]

theorem fa_pr (A B : ℕ) : fa (pr A B) = A % 2 ^ 6400 := by
  rw [fa_eq, pr_eq, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem fb_pr (A B : ℕ) : fb (pr A B) = B := by
  rw [fb_eq, pr_eq, Nat.add_mul_div_right _ _ (Nat.two_pow_pos 6400),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 6400)), Nat.zero_add]

theorem lane_mod (A : ℕ) : A % 2 ^ 6400 / 2 ^ 192 % 2 ^ 6084 = A / 2 ^ 192 % 2 ^ 6084 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_mod_two_pow]
  by_cases h : i < 6084
  · have h' : i + 192 < 6400 := by omega
    simp [h, h']
  · simp [h]

theorem xor_div (A B : ℕ) : (A ^^^ B) / 2 ^ 192 = A / 2 ^ 192 ^^^ B / 2 ^ 192 := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_xor_distrib]

theorem mul2_eq (P Q : ℕ) : mul2 P Q = pr (mulS (fa P) (fa Q) ^^^ mulS (fb P) (fb Q))
    (mulS (fa P ^^^ fb P) (fa Q ^^^ fb Q) ^^^ mulS (fa P) (fa Q)) := by
  simp only [mul2, strictN_eq]
  rfl

theorem eq2_iff (P Q : ℕ) : eq2 P Q = true ↔ dataS (fa P) = dataS (fa Q) ∧
    dataS (fb P) = dataS (fb Q) := by
  rw [eq2, Bool.and_eq_true, eqS_iff, eqS_iff]

section HasP

variable (K : Type) [Field K] [CharP K 2]

def HasP (ω : K) (g : ModGL Tag.E6 K) (P : ℕ) : Prop :=
  HasBits2 K ω g ⟨fa P / 2 ^ 192, fb P / 2 ^ 192⟩

variable {K} {ω : K}

theorem hasBits2_congr {g : ModGL Tag.E6 K} {X Y : Bits2} (h : HasBits2 K ω g X)
    (ha : X.a % 2 ^ 6084 = Y.a % 2 ^ 6084) (hb : X.b % 2 ^ 6084 = Y.b % 2 ^ 6084) :
    HasBits2 K ω g Y := by
  unfold HasBits2 TwBits.toEnd2 at *
  rw [h, (E6Bits.toEnd_eq_toEnd_iff (K := K) _ _).2 ha, (E6Bits.toEnd_eq_toEnd_iff (K := K) _ _).2 hb]

theorem hasP_of_bits2 {g : ModGL Tag.E6 K} {X : Bits2} {P : ℕ} (h : HasBits2 K ω g X)
    (e : X.a % 2 ^ 6084 = fa P / 2 ^ 192 % 2 ^ 6084 ∧
      X.b % 2 ^ 6084 = fb P / 2 ^ 192 % 2 ^ 6084) : HasP K ω g P :=
  hasBits2_congr h e.1 e.2

theorem HasP.mul (hω : ω ^ 2 + ω + 1 = 0) {g h : ModGL Tag.E6 K} {P Q : ℕ} (hg : HasP K ω g P)
    (hh : HasP K ω h Q) : HasP K ω (g * h) (mul2 P Q) := by
  have hm := HasBits2.mul hω hg hh
  unfold HasP
  rw [mul2_eq]
  refine hasBits2_congr hm ?_ ?_
  · rw [fa_pr, lane_mod, xor_div, mulS_div, mulS_div]
    rfl
  · rw [fb_pr, xor_div, mulS_div, mulS_div, xor_div, xor_div]
    rfl

theorem HasP.eq_iff (hω : ω ^ 2 + ω + 1 = 0) {g h : ModGL Tag.E6 K} {P Q : ℕ}
    (hg : HasP K ω g P) (hh : HasP K ω h Q) : g = h ↔ eq2 P Q = true := by
  rw [HasBits2.eq_iff hω hg hh, eq2_iff]
  rfl

theorem HasP.of_eq2 {g : ModGL Tag.E6 K} {P Q : ℕ} (hg : HasP K ω g P) (e : eq2 P Q = true) :
    HasP K ω g Q :=
  hasBits2_congr hg ((eq2_iff P Q).1 e).1 ((eq2_iff P Q).1 e).2

theorem one_a : Bits2.one.a = E6Bits.oneBits := rfl

theorem one_b : Bits2.one.b = 0 := rfl

theorem hasP_one : HasP K ω 1 one2 := by
  refine hasBits2_congr (hasBits2_one (K := K) ω) ?_ ?_
  · rw [one2, fa_pr, lane_mod, oneS_div, one_a]
  · rw [one2, fb_pr, Nat.zero_div, one_b]

theorem hasP_pr {g : ModGL Tag.E6 K} {A : ℕ} (h : HasBits2 K ω g ⟨A / 2 ^ 192, 0⟩) :
    HasP K ω g (pr A 0) := by
  refine hasBits2_congr h ?_ ?_
  · rw [fa_pr, lane_mod]
  · rw [fb_pr, Nat.zero_div]

end HasP

section Rows

variable {k K : Type} [Field k] [Finite k] [Field K] [Finite K] [Algebra k K] [CharP k 2] [CharP K 2]
  (σ : K ≃+* K) (S : Setup k K σ)

theorem hasP_iota {x : adjointGroup Tag.F4 k} {A : ℕ} (h : HasBitsS k (embE6F4 k x) A) :
    HasP K S.ω (tmat (iota σ S.hfix x)) (pr A 0) :=
  hasP_pr (hasBits2_iota σ S.hfix S.ω h)

theorem hasP_letP {IP X8 X9 : ℕ} (hI : ∀ c < 8, HasBitsS k (iotaL k c) (letT IP c))
    (h8 : HasP K S.ω (tmat (Xw0 σ S.hK S.hσ S.ω)) X8)
    (h9 : HasP K S.ω (tmat (Xw1 σ S.hK S.hσ S.ω)) X9) (c : ℕ) :
    HasP K S.ω (tmat (eltT σ S c)) (letP IP X8 X9 c) := by
  unfold eltT letP
  by_cases h1 : c < 8
  · rw [if_pos h1, blt_true h1]
    exact hasP_iota σ S (hI c h1)
  · rw [if_neg h1, blt_false h1]
    by_cases h2 : c = 8
    · subst h2
      exact h8
    · rw [if_neg h2, Bool.eq_false_iff.2 fun hb => h2 (Nat.eq_of_beq_eq_true hb)]
      exact h9

theorem hasP_wordPAux (f : ℕ → twistedE6RootGroup K σ) {IP X8 X9 : ℕ}
    (hL : ∀ c, HasP K S.ω (tmat (f c)) (letP IP X8 X9 c)) (W : ℕ) :
    ∀ (m : ℕ) {g : twistedE6RootGroup K σ} {acc : ℕ}, HasP K S.ω (tmat g) acc →
      HasP K S.ω (tmat (((decW 4 W m).map f).prod * g)) (wordPAux IP X8 X9 W m acc)
  | 0, g, acc, h => by
    change HasP K S.ω (tmat (1 * g)) acc
    rwa [one_mul]
  | m + 1, g, acc, h => by
    have e1 : wordPAux IP X8 X9 W (m + 1) acc =
        wordPAux IP X8 X9 W m (mul2 (letP IP X8 X9 (W / 2 ^ (4 * m) % 2 ^ 4)) acc) := by
      change strictN (mul2 (letP IP X8 X9 (digit 4 W m)) acc) (wordPAux IP X8 X9 W m) = _
      rw [strictN_eq, digit_eq]
    have e : ((decW 4 W (m + 1)).map f).prod * g =
        ((decW 4 W m).map f).prod * (f (W / 2 ^ (4 * m) % 2 ^ 4) * g) := by
      rw [decW, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
        mul_assoc]
    rw [e1, e]
    exact hasP_wordPAux f hL W m (HasP.mul S.hω (hL _) h)

theorem hasP_wordP {IP X8 X9 : ℕ} (hI : ∀ c < 8, HasBitsS k (iotaL k c) (letT IP c))
    (h8 : HasP K S.ω (tmat (Xw0 σ S.hK S.hσ S.ω)) X8)
    (h9 : HasP K S.ω (tmat (Xw1 σ S.hK S.hσ S.ω)) X9) (W L : ℕ) :
    HasP K S.ω (tmat (((decW 4 W L).map (eltT σ S)).prod)) (wordP IP X8 X9 W L) := by
  have h := hasP_wordPAux σ S (eltT σ S) (hasP_letP σ S hI h8 h9) W L
    (g := 1) (hasP_one (K := K))
  rw [mul_one] at h
  exact h

theorem rowT_sound {IP X8 X9 : ℕ} (hI : ∀ c < 8, HasBitsS k (iotaL k c) (letT IP c))
    (h8 : HasP K S.ω (tmat (Xw0 σ S.hK S.hσ S.ω)) X8)
    (h9 : HasP K S.ω (tmat (Xw1 σ S.hK S.hσ S.ω)) X9)
    {pS : List ℕ} {ab ij : ℕ × ℕ} {gs : List G3} {zs : List (List ℕ)}
    {a b : adjointGroup Tag.F4 k}
    (ha : HasBitsS k (embE6F4 k a) (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0)
      (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.1))
    (hb : HasBitsS k (embE6F4 k b) (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0)
      (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.2))
    (h : rowT IP X8 X9 pS ab ij gs zs = true) :
    ∃ e ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 k)), e ≠ 1 ∧
      Subgroup.closure (((iota σ S.hfix).range : Set (twistedE6RootGroup K σ)) ∪
        (Subgroup.centralizer ({iota σ S.hfix e} : Set (twistedE6RootGroup K σ)) :
          Set (twistedE6RootGroup K σ))) = ⊤ := by
  simp only [rowT, strictB_eq6, Bool.and_eq_true, Bool.not_eq_true', lenL_eq6] at h
  obtain ⟨hE1, hgs, hz1, hz2⟩ := h
  set e : adjointGroup Tag.F4 k := a ^ ij.1 * b ^ ij.2 with hedef
  have hE : HasBitsS k (embE6F4 k e) (mulS (powS (phiE (pS.getD 0 0) (pS.getD 1 0)
      (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0) (pS.getD 5 0) ab.1) ij.1)
      (powS (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0)
        (pS.getD 5 0) ab.2) ij.2)) := by
    rw [hedef, map_mul, map_pow, map_pow]
    exact (ha.pow _).mul (hb.pow _)
  have heA : a ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 k)) :=
    Subgroup.subset_closure (by simp)
  have heB : b ∈ Subgroup.closure ({a, b} : Set (adjointGroup Tag.F4 k)) :=
    Subgroup.subset_closure (by simp)
  refine ⟨e, mul_mem (pow_mem heA _) (pow_mem heB _), fun h1 => ?_, ?_⟩
  · rw [h1, map_one] at hE
    rw [(hE.eq_iff hasBitsS_one).1 rfl] at hE1
    exact Bool.noConfusion hE1
  set Sg := Subgroup.closure (((iota σ S.hfix).range : Set (twistedE6RootGroup K σ)) ∪
    (Subgroup.centralizer ({iota σ S.hfix e} : Set (twistedE6RootGroup K σ)) :
      Set (twistedE6RootGroup K σ))) with hSgdef
  have hrange : ∀ x ∈ (iota σ S.hfix).range, x ∈ Sg := fun x hx =>
    Subgroup.subset_closure (Or.inl hx)
  have hcent : ∀ x ∈ Subgroup.centralizer ({iota σ S.hfix e} : Set (twistedE6RootGroup K σ)),
      x ∈ Sg := fun x hx => Subgroup.subset_closure (Or.inr hx)
  have hE2 := hasP_iota σ S hE
  have hgen : ∀ g ∈ gs, ∃ w ∈ Subgroup.centralizer
      ({iota σ S.hfix e} : Set (twistedE6RootGroup K σ)), HasP K S.ω (tmat w) g.2.2 := by
    intro g hg
    have h' := allL_spec6 hgs g hg
    simp only [genP, strictB_eq6, Bool.and_eq_true] at h'
    have hT := (hasP_wordP σ S hI h8 h9 g.1 g.2.1).of_eq2 h'.1
    refine ⟨_, ?_, hT⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (((HasP.mul S.hω hT hE2).eq_iff S.hω (HasP.mul S.hω hE2 hT)).2 h'.2)
  have htok : ∀ t, t < 8 + gs.length → ∃ x ∈ Sg, HasP K S.ω (tmat x) (tokP IP gs t) := by
    intro t ht
    by_cases h8' : t < 8
    · have e1 : tokP IP gs t = pr (letT IP t) 0 := by
        rw [tokP, blt_true h8']
      rw [e1]
      exact ⟨iota σ S.hfix ((CFSG.RankThree.PartOne.SEITZX.letterOfCode t).elt k),
        hrange _ ⟨_, rfl⟩, hasP_iota σ S (hI t h8')⟩
    · have e1 : tokP IP gs t = (gs.getD (t - 8) (0, 0, 0)).2.2 := by
        rw [tokP, blt_false h8']
        rfl
      have hlt : t - 8 < gs.length := by omega
      rw [e1, List.getD_eq_getElem _ _ hlt]
      obtain ⟨w, hw, hT⟩ := hgen _ (List.getElem_mem hlt)
      exact ⟨w, hcent w hw, hT⟩
  have hprod : ∀ idx : List ℕ, (∀ t ∈ idx, t < 8 + gs.length) →
      ∃ x ∈ Sg, HasP K S.ω (tmat x) (prodP IP gs idx) := by
    intro idx
    induction idx with
    | nil => exact fun _ => ⟨1, one_mem _, hasP_one (K := K)⟩
    | cons t idx ih =>
      intro ht
      obtain ⟨x, hx, hxb⟩ := htok t (ht t List.mem_cons_self)
      obtain ⟨y, hy, hyb⟩ := ih fun j hj => ht j (List.mem_cons_of_mem _ hj)
      exact ⟨x * y, mul_mem hx hy, HasP.mul S.hω hxb hyb⟩
  have hz : ∀ (idx : List ℕ) (X : ℕ) (y : twistedE6RootGroup K σ), HasP K S.ω (tmat y) X →
      tgtP IP gs gs.length idx X = true → y ∈ Sg := by
    intro idx X y hy h'
    simp only [tgtP, Bool.and_eq_true] at h'
    have hidx : ∀ t ∈ idx, t < 8 + gs.length := fun t ht => lt_of_blt (allL_spec6 h'.1 t ht)
    obtain ⟨x, hx, hxb⟩ := hprod idx hidx
    have hxy : x = y := Subtype.ext ((hxb.eq_iff S.hω hy).2 h'.2)
    rw [← hxy]
    exact hx
  exact eq_top_of_orbit σ Sg (oX_mem σ S Sg hrange (hz _ _ _ h8 hz1) (hz _ _ _ h9 hz2))
    (fun a c' hc' => hrange _ (oXY_mem_range σ S.hfix a c' hc').2)

theorem rowAtT_sound {IP X8 X9 : ℕ} (hI : ∀ c < 8, HasBitsS k (iotaL k c) (letT IP c))
    (h8 : HasP K S.ω (tmat (Xw0 σ S.hK S.hσ S.ω)) X8)
    (h9 : HasP K S.ω (tmat (Xw1 σ S.hK S.hσ S.ω)) X9)
    {s : Fin 4 → adjointGroup Tag.F4 k} {g4 g5 : adjointGroup Tag.F4 k} {pS : List ℕ}
    (hs : ∀ i : Fin 4, HasBitsS k (embE6F4 k (s i)) (pS.getD i 0))
    (h4 : HasBitsS k (embE6F4 k g4) (pS.getD 4 0)) (h5 : HasBitsS k (embE6F4 k g5) (pS.getD 5 0))
    {PR r : ℕ} {ij : List (ℕ × ℕ)} {gens : List (List G3)} {zs : List (List (List ℕ))}
    (h : rowAtT IP X8 X9 pS PR ij gens zs r = true) :
    ∃ e ∈ CFSG.KC.F4Planes.planeR s g4 g5 PR r, e ≠ 1 ∧
      Subgroup.closure (((iota σ S.hfix).range : Set (twistedE6RootGroup K σ)) ∪
        (Subgroup.centralizer ({iota σ S.hfix e} : Set (twistedE6RootGroup K σ)) :
          Set (twistedE6RootGroup K σ))) = ⊤ := by
  have hphi : ∀ m, HasBitsS k (embE6F4 k (CFSG.KC.F4Syl3.phi s g4 g5 m))
      (phiE (pS.getD 0 0) (pS.getD 1 0) (pS.getD 2 0) (pS.getD 3 0) (pS.getD 4 0)
        (pS.getD 5 0) m) := fun m => by
    rw [map_phi]
    exact hasBitsS_phiE (hs 0) (hs 1) (hs 2) (hs 3) h4 h5 m
  have h' : rowT IP X8 X9 pS (CFSG.KC.F4Planes.aR PR r, CFSG.KC.F4Planes.bR PR r)
      (ij.getD r (0, 0)) (gens.getD r []) (zs.getD r []) = true := h
  exact rowT_sound (ab := (CFSG.KC.F4Planes.aR PR r, CFSG.KC.F4Planes.bR PR r)) σ S hI h8 h9
    (hphi _) (hphi _) h'

end Rows

end CFSG.KC.F4PlanesTw

end

module

public import Certificates.Data.Kernel.Misc.A6GL4
public import Certificates.Data.Asc82NormA6
public import CFSG.Certificates.Kernel.Misc.GL4LatSound
import CFSG.Certificates.Kernel.LocalQTPermSound

public section

namespace CFSG.KC.Misc.A6GL4

open Matrix CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GL4
open CFSG.KC.Misc.Clos (ClosEnc ExactList)
open Certificates.A5GL42 (Mat4 ofCode)
open Certificates.GL4 (GL4)
open Certificates.Asc82NormA6

theorem rel_map {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (hf : Function.Injective f)
    (x y : M) : Certificates.Asc82NormA6.Rel (f x) (f y) ↔ Certificates.Asc82NormA6.Rel x y := by
  unfold Certificates.Asc82NormA6.Rel
  simp only [← map_pow, ← map_mul, ← map_one f, hf.eq_iff]

theorem rel_conj {G : Type*} [Group G] (c x y : G) :
    Certificates.Asc82NormA6.Rel (c * x * c⁻¹) (c * y * c⁻¹) ↔ Certificates.Asc82NormA6.Rel x y := by
  have h := rel_map (MulAut.conj c).toMonoidHom (MulAut.conj c).injective x y
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem eq_one_of_rel_one {M : Type*} [Monoid M] {x : M} (h : Certificates.Asc82NormA6.Rel x 1) :
    x = 1 := by
  obtain ⟨h3, -, -, h4, -, -⟩ := h
  rw [one_pow, mul_one, ← pow_mul] at h4
  have h9 : x ^ 9 = x := by rw [pow_succ, h4, one_mul]
  rw [← h9, show 9 = 3 * 3 from rfl, pow_mul, h3, one_pow]

theorem mul_enc (a b : GL4) : mul4F (enc4 a) (enc4 b) = enc4 (a * b) :=
  (gl4_enc.enc_mul a b).symm

theorem relB_iff (x y : GL4) :
    relB (enc4 x) (enc4 y) = true ↔ Certificates.Asc82NormA6.Rel x y := by
  unfold relB Certificates.Asc82NormA6.Rel
  simp only [pow4F_enc, mul_enc, andB_iff, beq_iff, enc4_eq_id4]

@[expose] def vb (k : Fin 6) : Fin 4 → ZMod 2 := fun r => ((beta k / 2 ^ (r : ℕ) % 2 : ℕ) : ZMod 2)

@[expose] def emb (i : Fin 4) : Fin 6 := Fin.castLE (by norm_num) i

theorem code4_cols (c0 c1 c2 c3 : ℕ) :
    code4 (Matrix.of fun (r i : Fin 4) => ((![c0, c1, c2, c3] i / 2 ^ (r : ℕ) % 2 : ℕ) : ZMod 2) :
      Mat4) = spread c0 + 2 * spread c1 + 4 * spread c2 + 8 * spread c3 := by
  simp only [code4, Fin.sum_univ_four, Matrix.of_apply, ZMod.val_natCast, Nat.mod_mod,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Fin.val_zero, Fin.val_one, Fin.val_two, spread]
  norm_num
  ring

theorem xor_bit : ∀ a b : Fin 6, ∀ r : Fin 4,
    (((beta a ^^^ beta b) / 2 ^ (r : ℕ) % 2 : ℕ) : ZMod 2) = vb a r + vb b r := by
  unfold vb beta
  decide

theorem rho_cols (p : Equiv.Perm (Fin 6)) :
    rho p = (Matrix.of fun (r i : Fin 4) =>
      ((![col p 0, col p 1, col p 2, col p 3] i / 2 ^ (r : ℕ) % 2 : ℕ) : ZMod 2) : Mat4) := by
  change ofCode (rhoCode p) = _
  rw [rhoCode, ← code4_cols, ofCode_code4]

theorem rho_apply (p : Equiv.Perm (Fin 6)) (r i : Fin 4) :
    rho p r i = vb (p (emb i)) r + vb (p 5) r := by
  rw [rho_cols, Matrix.of_apply]
  fin_cases i <;> exact xor_bit _ _ r

theorem vb_single : ∀ i : Fin 4, vb (emb i) = Pi.single i 1 := by
  intro i
  funext r
  revert i r
  unfold vb emb beta
  decide

theorem vb_five : vb 5 = 0 := by
  funext r
  revert r
  unfold vb beta
  decide

theorem vb_four : vb 4 = vb 0 + vb 1 + vb 2 + vb 3 := by
  funext r
  revert r
  unfold vb beta
  decide

theorem vb_sum : ∀ r : Fin 4, ∑ k : Fin 6, vb k r = 0 := by
  unfold vb beta
  decide

theorem vb_inj : ∀ a b : Fin 6, vb a = vb b → a = b := by
  unfold vb beta
  decide

theorem vb_shift : ∀ j : Fin 6, j ≠ 5 → ∃ k : Fin 6, ∀ m : Fin 6, vb m ≠ vb k + vb j := by
  unfold vb beta
  decide

theorem zmod2_add_self : ∀ a : ZMod 2, a + a = 0 := by decide

theorem zmod2_four : ∀ a0 a1 a2 a3 a4 a5 : ZMod 2, a0 + a1 + a2 + a3 + a4 + a5 = 0 →
    a0 + a5 + (a1 + a5) + (a2 + a5) + (a3 + a5) = a4 + a5 := by decide

theorem zmod2_three : ∀ a b c : ZMod 2, a + b = a + c + (b + c) := by decide

theorem zmod2_swap : ∀ a b c : ZMod 2, a = b + c → b = a + c := by decide

theorem col_mulVec (p : Equiv.Perm (Fin 6)) (i : Fin 4) :
    rho p *ᵥ vb (emb i) = vb (p (emb i)) + vb (p 5) := by
  rw [vb_single, Matrix.mulVec_single_one]
  funext r
  exact rho_apply p r i

theorem rho_mulVec (p : Equiv.Perm (Fin 6)) : ∀ k : Fin 6,
    rho p *ᵥ vb k = vb (p k) + vb (p 5) := by
  intro k
  fin_cases k
  · exact col_mulVec p 0
  · exact col_mulVec p 1
  · exact col_mulVec p 2
  · exact col_mulVec p 3
  · change rho p *ᵥ vb 4 = vb (p 4) + vb (p 5)
    have h0 : rho p *ᵥ vb 0 = vb (p 0) + vb (p 5) := col_mulVec p 0
    have h1 : rho p *ᵥ vb 1 = vb (p 1) + vb (p 5) := col_mulVec p 1
    have h2 : rho p *ᵥ vb 2 = vb (p 2) + vb (p 5) := col_mulVec p 2
    have h3 : rho p *ᵥ vb 3 = vb (p 3) + vb (p 5) := col_mulVec p 3
    rw [vb_four, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, h0, h1, h2, h3]
    funext r
    have hs : ∑ k : Fin 6, vb (p k) r = 0 := by
      rw [Equiv.sum_comp p (fun k => vb k r)]
      exact vb_sum r
    simp only [Fin.sum_univ_six] at hs
    exact zmod2_four _ _ _ _ _ _ hs
  · change rho p *ᵥ vb 5 = vb (p 5) + vb (p 5)
    rw [vb_five, Matrix.mulVec_zero]
    funext r
    exact (zmod2_add_self _).symm

theorem rho_mul' (p q : Equiv.Perm (Fin 6)) : rho (p * q) = rho p * rho q := by
  ext r i
  have hcol : (fun j => rho q j i) = vb (q (emb i)) + vb (q 5) :=
    funext fun j => rho_apply q j i
  have h1 : (rho p * rho q) r i = (rho p *ᵥ (fun j => rho q j i)) r := rfl
  rw [h1, hcol, Matrix.mulVec_add, rho_mulVec, rho_mulVec, rho_apply, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply]
  exact zmod2_three _ _ _

theorem rhoCode_one : rhoCode 1 = id4 := by decide +kernel

theorem rho_one' : rho 1 = 1 := by
  change ofCode (rhoCode 1) = 1
  rw [rhoCode_one, ofCode_id4]

theorem rho_ker' (p : Equiv.Perm (Fin 6)) (h : rho p = 1) : p = 1 := by
  have hv : ∀ k, vb (p k) = vb k + vb (p 5) := by
    intro k
    have e := rho_mulVec p k
    rw [h, Matrix.one_mulVec] at e
    funext r
    exact zmod2_swap _ _ _ (congrFun e r)
  have h5 : p 5 = 5 := by
    by_contra hne
    obtain ⟨k, hk⟩ := vb_shift (p 5) hne
    exact hk (p k) (hv k)
  refine Equiv.ext fun k => ?_
  have e := hv k
  rw [h5, vb_five, add_zero] at e
  rw [Equiv.Perm.one_apply]
  exact vb_inj _ _ e

@[expose] noncomputable def rhoU : Equiv.Perm (Fin 6) →* GL4 where
  toFun p := ⟨rho p, rho p⁻¹, by rw [← rho_mul', mul_inv_cancel, rho_one'],
    by rw [← rho_mul', inv_mul_cancel, rho_one']⟩
  map_one' := Units.ext rho_one'
  map_mul' p q := Units.ext (rho_mul' p q)

theorem rhoU_val (p : Equiv.Perm (Fin 6)) : ((rhoU p : GL4) : Mat4) = rho p := rfl

theorem rhoU_injective : Function.Injective rhoU :=
  (injective_iff_map_eq_one rhoU).2 fun p h => rho_ker' p (congrArg Units.val h)

theorem enc4_rhoU (p : Equiv.Perm (Fin 6)) : enc4 (rhoU p) = rhoCode p := by
  rw [enc4, rhoU_val, rho, code4_ofCode]
  unfold rhoCode spread
  omega

variable {EA EAI W HE HS R : ℕ → ℕ}

theorem yAt_sound {Y : ℕ} (hE : ExactList enc4 ⊤ 20160 EA)
    (hI : ∀ k < 20160, ∀ g : GL4, enc4 g = EA k → enc4 g⁻¹ = EAI k)
    (h : ∀ k < 20160, yAt EA EAI W Y k = true) (y : GL4) (hy1 : y ≠ 1) (hy5 : y ^ 5 = 1) :
    ∃ g : GL4, enc4 (g⁻¹ * y * g) = Y := by
  obtain ⟨k, hk, hyk⟩ := hE.2.1 y (Subgroup.mem_top y)
  have h' := h k hk
  unfold yAt at h'
  rw [letB_eq, ← hyk] at h'
  rcases orB_iff.1 h' with h1 | h'
  · exact absurd (enc4_eq_id4.1 (beq_iff.1 h1)) hy1
  rcases orB_iff.1 h' with h1 | h'
  · exact absurd (beq_iff.2 (pow4F_eq_id4.2 hy5)) (notB_iff.1 h1)
  unfold yWit at h'
  rw [letB_eq] at h'
  obtain ⟨hw, e⟩ := andB_iff.1 h'
  have hw' := Nat.blt_eq.mp hw
  obtain ⟨g, -, hg⟩ := hE.1 _ hw'
  refine ⟨g, ?_⟩
  rw [← mul_enc, ← mul_enc, hI _ hw' g hg, hg]
  exact beq_iff.1 e

theorem xAt_sound {Y : ℕ} {K : Subgroup GL4} (hE : ExactList enc4 ⊤ 20160 EA)
    (hI : ∀ k < 20160, ∀ g : GL4, enc4 g = EA k → enc4 g⁻¹ = EAI k)
    (hK : ExactList enc4 K 360 HE) (h : ∀ k < 20160, xAt EA EAI W HE Y k = true) {y : GL4}
    (hy : enc4 y = Y) (x : GL4) (hx1 : x ≠ 1) (hxy : Certificates.Asc82NormA6.Rel x y) :
    ∃ c : GL4, c⁻¹ * x * c ∈ K ∧ c⁻¹ * y * c ∈ K := by
  obtain ⟨k, hk, hxk⟩ := hE.2.1 x (Subgroup.mem_top x)
  have h' := h k hk
  unfold xAt at h'
  rw [letB_eq, ← hxk] at h'
  rcases orB_iff.1 h' with h1 | h'
  · exact absurd (enc4_eq_id4.1 (beq_iff.1 h1)) hx1
  rcases orB_iff.1 h' with h1 | h'
  · exact absurd (beq_iff.2 (pow4F_eq_id4.2 hxy.1)) (notB_iff.1 h1)
  rcases orB_iff.1 h' with h1 | h'
  · exact absurd (by rw [← hy]; exact (relB_iff x y).2 hxy) (notB_iff.1 h1)
  unfold xWit at h'
  rw [letB_eq, letB_eq, letB_eq] at h'
  obtain ⟨hc, h'⟩ := andB_iff.1 h'
  obtain ⟨hi, h'⟩ := andB_iff.1 h'
  obtain ⟨hj, h'⟩ := andB_iff.1 h'
  obtain ⟨e1, e2⟩ := andB_iff.1 h'
  have hc' := Nat.blt_eq.mp hc
  obtain ⟨c, -, hcc⟩ := hE.1 _ hc'
  have hci := hI _ hc' c hcc
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨a, ha, e⟩ := hK.1 _ (Nat.blt_eq.mp hi)
    have : enc4 (c⁻¹ * x * c) = enc4 a := by
      rw [← mul_enc, ← mul_enc, hci, hcc, e]
      exact beq_iff.1 e1
    rw [gl4_enc.inj this]
    exact ha
  · obtain ⟨b, hb, e⟩ := hK.1 _ (Nat.blt_eq.mp hj)
    have : enc4 (c⁻¹ * y * c) = enc4 b := by
      rw [← mul_enc, ← mul_enc, hci, hcc, e, hy]
      exact beq_iff.1 e2
    rw [gl4_enc.inj this]
    exact hb

theorem djB_sound {X Y n : ℕ} {K : Subgroup GL4} (hK : ExactList enc4 K 360 HE)
    (hs : ∀ i < 360, CFSG.KC.Misc.Clos.sortAt 360 HE HS i = true) (h : djB HE HS R X Y n = true)
    {x y : GL4} (hx : enc4 x = X) (hy : enc4 y = Y) (hxK : x ∈ K) (hyK : y ∈ K) :
    ∃ c : ℕ → GL4, ∀ l < n, ∀ k < l,
      (c l)⁻¹ * c k * x * ((c l)⁻¹ * c k)⁻¹ ∉ K ∨ (c l)⁻¹ * c k * y * ((c l)⁻¹ * c k)⁻¹ ∉ K := by
  unfold djB at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  have hinv := (allN_iff _ _).1 h1
  refine ⟨fun k => u4 (R (2 * k)), fun l hl k hk => ?_⟩
  have hck : ∀ k < n, enc4 (u4 (R (2 * k))) = R (2 * k) ∧
      enc4 (u4 (R (2 * k)))⁻¹ = R (2 * k + 1) := by
    intro k hk
    have hw := hinv k hk
    have e := enc4_u4 (exists_of_invW hw)
    refine ⟨e, ?_⟩
    rw [← e] at hw
    exact enc4_inv_of_invW hw
  have hd := (allN_iff _ _).1 ((allN_iff _ _).1 h2 l hl) k hk
  unfold djAt at hd
  rw [letB_eq, letB_eq] at hd
  obtain ⟨ek, eki⟩ := hck k (hk.trans hl)
  obtain ⟨el, eli⟩ := hck l hl
  have hm : enc4 ((u4 (R (2 * l)))⁻¹ * u4 (R (2 * k))) =
      mul4F (R (Nat.succ (Nat.mul 2 l))) (R (Nat.mul 2 k)) := by
    rw [← mul_enc, eli, ek]
    rfl
  have hmi : enc4 ((u4 (R (2 * l)))⁻¹ * u4 (R (2 * k)))⁻¹ =
      mul4F (R (Nat.succ (Nat.mul 2 k))) (R (Nat.mul 2 l)) := by
    rw [_root_.mul_inv_rev, inv_inv, ← mul_enc, eki, el]
    rfl
  have hout : ∀ z : GL4, CFSG.KC.Misc.GL4.outK HE HS 360 (enc4 z) = true → z ∉ K := by
    intro z hz hzK
    obtain ⟨j, hj, e⟩ := hK.2.1 z hzK
    exact outK_sound hs hz j hj e.symm
  rcases orB_iff.1 hd with h3 | h3
  · left
    apply hout
    rw [← mul_enc, ← mul_enc, hm, hmi, hx]
    exact h3
  · right
    apply hout
    rw [← mul_enc, ← mul_enc, hm, hmi, hy]
    exact h3

theorem normalizer_le_of {K S : Subgroup GL4} (hS : S ≤ Subgroup.normalizer (K : Set GL4))
    (hcard : Nat.card S = 720) (c : ℕ → GL4)
    (hc : ∀ l < 28, ∀ k < l, (c l)⁻¹ * c k ∉ Subgroup.normalizer (K : Set GL4)) :
    Subgroup.normalizer (K : Set GL4) ≤ S := by
  have := finite_gl4
  let N := Subgroup.normalizer (K : Set GL4)
  let f : Fin 28 → GL4 ⧸ N := fun k => (c k : GL4 ⧸ N)
  have hf : Function.Injective f := by
    intro a b hab
    have e : (c a)⁻¹ * c b ∈ N := QuotientGroup.eq.1 hab
    rcases Nat.lt_trichotomy a b with h | h | h
    · refine absurd ?_ (hc b b.isLt a h)
      have := N.inv_mem e
      rwa [_root_.mul_inv_rev, inv_inv] at this
    · exact Fin.ext h
    · exact absurd e (hc a a.isLt b h)
  have h28 : 28 ≤ N.index := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hmul := N.card_mul_index
  rw [card_gl4] at hmul
  have hN : Nat.card N ≤ Nat.card S := by
    rw [hcard]
    by_contra hlt
    rw [not_le] at hlt
    have : 721 * 28 ≤ Nat.card N * N.index := Nat.mul_le_mul hlt h28
    omega
  exact (Subgroup.eq_of_le_of_card_ge hS hN).symm.le

end CFSG.KC.Misc.A6GL4

end

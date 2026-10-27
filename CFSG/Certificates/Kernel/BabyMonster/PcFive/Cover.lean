module

public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Coll
public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Bool
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.BM.PcFive

open CFSG.Monster.B.Pinned Subgroup

theorem memN_spec {n : ℕ} : ∀ {l : List ℕ}, memN n l = true → n ∈ l
  | [], h => by simp [memN] at h
  | a :: l, h => by
    unfold memN at h
    rw [Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (memN_spec h)

theorem chunkOK_spec {rep : ℕ → ℕ} {nc : ℕ} : ∀ {i : ℕ} {ds : List ℕ},
    chunkOK rep nc i ds = true → ∀ k < ds.length, elemOK rep nc (i + k) (nth ds k) = true
  | _, [], _, k, hk => absurd hk (by simp)
  | i, d :: ds, h, k, hk => by
    unfold chunkOK at h
    rw [Bool.and_eq_true] at h
    cases k with
    | zero => simpa [nth] using h.1
    | succ k =>
      have e : i + (k + 1) = i + 1 + k := by omega
      rw [e]
      exact chunkOK_spec h.2 k (by simpa using hk)

theorem elemOK_spec {rep : ℕ → ℕ} {nc i d : ℕ} (h : elemOK rep nc i d = true) (hi : i ≠ 0)
    (ho : ord5 (dec i) = true) :
    d / 15625 < nc ∧
      mulV (dec (d % 15625)) (dec i) = mulV (dec (rep (d / 15625))) (dec (d % 15625)) := by
  unfold elemOK at h
  simp only [Bool.or_eq_true, Nat.beq_eq, hi, ho, Bool.not_true, Bool.false_eq_true, or_false,
    false_or, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, V6.beq_eq h.2⟩

theorem stepOK_fused {rep : ℕ → ℕ} {nc : ℕ} {depth : List ℕ} {c c' w : ℕ} {v : V6}
    (h : stepOK rep nc depth c c' w v = true)
    (ih : ∀ c'' < nc, nth depth c'' < nth depth c → Fused (dec (rep c''))) : Fused v := by
  unfold stepOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Fused.conj (dec_red w) (dec_red _) (V6.beq_eq h3) (ih c' h1 h2)

theorem fusOK_fused {rep : ℕ → ℕ} {nc : ℕ} {depth kind arg cls wit : List ℕ}
    (h : fusOK rep nc depth kind arg cls wit = true) : ∀ c < nc, Fused (dec (rep c)) := by
  suffices H : ∀ n, ∀ c < nc, nth depth c = n → Fused (dec (rep c)) from
    fun c hc => H _ c hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hn
    have ih' : ∀ c'' < nc, nth depth c'' < nth depth c → Fused (dec (rep c'')) :=
      fun c'' h1 h2 => ih _ (hn ▸ h2) c'' h1 rfl
    have hcl := allBelow_spec h c hc
    unfold classOK at hcl
    by_cases k0 : (nth kind c).beq 0 = true
    · simp only [k0, cond_true] at hcl
      exact Fused.target (memN_spec hcl)
    by_cases k1 : (nth kind c).beq 1 = true
    · simp only [k0, k1, cond_true, cond_false, Bool.false_eq_true, Bool.and_eq_true,
        Nat.blt_eq] at hcl
      exact Fused.aut hcl.1 (stepOK_fused hcl.2 ih')
    by_cases k2 : (nth kind c).beq 2 = true
    · simp only [k0, k1, k2, cond_true, cond_false, Bool.false_eq_true, Bool.and_eq_true,
        Nat.blt_eq, Nat.ble_eq] at hcl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcl
      exact Fused.pow h3 h1 h2 (stepOK_fused h4 ih')
    · simp only [Bool.not_eq_true] at k0 k1 k2
      simp only [k0, k1, k2, cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hcl
      obtain ⟨⟨h1, h2⟩, h3⟩ := hcl
      rw [h2]
      exact Fused.single h1 (stepOK_fused h3 ih')

theorem elem_of_chunks {rep : ℕ → ℕ} {nc : ℕ} {C : ℕ → List ℕ}
    (hC : ∀ k < 16, chunkOK rep nc (1000 * k) (C k) = true)
    (hL : ∀ k < 16, (C k).length = if k < 15 then 1000 else 625) :
    ∀ i < 15625, elemOK rep nc i (nth (C (i / 1000)) (i % 1000)) = true := by
  intro i hi
  have hk : i / 1000 < 16 := by omega
  have hl : i % 1000 < (C (i / 1000)).length := by
    rw [hL _ hk]
    split <;> omega
  have h := chunkOK_spec (hC _ hk) (i % 1000) hl
  rwa [Nat.div_add_mod] at h

theorem census_fact {rep : ℕ → ℕ} {nc : ℕ} {depth kind arg cls wit : List ℕ} {D : ℕ → ℕ}
    (hE : ∀ i < 15625, elemOK rep nc i (D i) = true)
    (hF : fusOK rep nc depth kind arg cls wit = true) : CensusFact := by
  intro i hi hi0 ho
  obtain ⟨h1, h2⟩ := elemOK_spec (hE i hi) hi0 ho
  exact Fused.conj (dec_red _) (dec_red _) h2 (fusOK_fused hF _ h1)

variable {G : Type*} [Group G] {x : G} {q : Fin 4 → G} {z : G}

@[expose] def AutRel (x : G) (q : Fin 4 → G) (z g : G) (ws : List ℕ) : Prop :=
  g * x * g⁻¹ = psi x q z (dec (nth ws 0)) ∧ g * q 0 * g⁻¹ = psi x q z (dec (nth ws 1)) ∧
    g * q 1 * g⁻¹ = psi x q z (dec (nth ws 2)) ∧ g * q 2 * g⁻¹ = psi x q z (dec (nth ws 3)) ∧
    g * q 3 * g⁻¹ = psi x q z (dec (nth ws 4)) ∧ g * z * g⁻¹ = psi x q z (dec (nth ws 5))

theorem ord5_spec {v : V6} (h : ord5 v = true) : powV v 5 = V6.one := V6.beq_eq h

theorem fused_good (H : PcHyp x q z) (hφ : phiOK () = true) (Good : G → Prop)
    (hconj : ∀ s c : G, Good s → Good (c * s * c⁻¹))
    (hpow : ∀ s : G, s ^ 5 = 1 → ∀ k : ℕ, Nat.Coprime k 5 → (Good (s ^ k) ↔ Good s))
    (hN : ∀ j < 3, ∃ g, AutRel x q z g (autAt j))
    (hS : ∀ m < 11, ∃ g : G,
      g * psi x q z (dec (nth singleSrc m)) * g⁻¹ = psi x q z (dec (nth singleTgt m)))
    (hT : ∀ i ∈ targets, Good (psi x q z (dec i))) :
    ∀ v, Fused v → v.red → Good (psi x q z v) := by
  have hback : ∀ s c : G, Good (c * s * c⁻¹) → Good s := fun s c h => by
    have h' := hconj _ c⁻¹ h
    have e : c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s := by group
    rwa [e] at h'
  intro v hv
  induction hv with
  | target hi => exact fun _ => hT _ hi
  | @conj v w g hg hw heq _ ih =>
    intro hvr
    have e1 := H.psi_mul hφ hg hvr
    have e2 := H.psi_mul hφ hw hg
    rw [heq, ← e2] at e1
    have e : psi x q z v = (psi x q z g)⁻¹ * psi x q z w * (psi x q z g)⁻¹⁻¹ := by
      rw [inv_inv, mul_assoc, ← e1]
      group
    rw [e]
    exact hconj _ _ (ih hw)
  | @aut v j hj _ ih =>
    intro hvr
    obtain ⟨g, h0, h1, h2, h3, h4, h5⟩ := hN j hj
    apply hback _ g
    rw [H.conj_alpha hφ h0 h1 h2 h3 h4 h5]
    exact ih (mulV_red _ _)
  | @pow v k ho hk2 hk5 _ ih =>
    intro hvr
    have h5 : psi x q z v ^ 5 = 1 := by
      rw [H.psi_pow hφ hvr, ord5_spec ho, psi_one]
    have hcop : Nat.Coprime k 5 := by interval_cases k <;> norm_num
    refine (hpow _ h5 k hcop).1 ?_
    rw [H.psi_pow hφ hvr]
    exact ih (powV_red _ _)
  | @single m hm _ ih =>
    intro _
    obtain ⟨g, hg⟩ := hS m hm
    apply hback _ g
    rw [hg]
    exact ih (dec_red _)

@[expose] def Mz : Matrix (Fin 4) (Fin 4) (ZMod 5) := !![0, 1, 4, 1; 4, 0, 0, 2; 1, 0, 0, 1; 4, 3, 4, 0]

@[expose] def MzInv : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  !![0, 3, 4, 0; 2, 0, 3, 3; 1, 2, 0, 3; 0, 2, 2, 0]

theorem Mz_mul_inv : Mz * MzInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem isUnit_det_Mz : IsUnit Mz.det := by
  have h := congrArg Matrix.det Mz_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem bcomm_of_swap {a b : G} {k : ℕ} (h : b * a = a * b * z ^ k) : bcomm b a = z ^ k := by
  unfold bcomm
  rw [mul_assoc (b⁻¹ * a⁻¹), h]
  group

theorem bcomm_of_swap' (hz : z ^ 5 = 1) {a b : G} {k n : ℕ} (h : b * a = a * b * z ^ k)
    (hkn : k + n = 5) : bcomm a b = z ^ n := by
  have e := bcomm_swap a b
  rw [bcomm_of_swap h] at e
  have e2 : bcomm a b = (z ^ k)⁻¹ := by rw [e, inv_inv]
  rw [e2, inv_eq_iff_mul_eq_one, ← pow_add, hkn, hz]

theorem QRel.bcomm_eq (h : QRel cmFive q z) : ∀ i j, bcomm (q i) (q j) = z ^ (Mz i j).val := by
  have b01 := bcomm_of_swap' h.z5 h.s01 (n := 1) rfl
  have b10 := bcomm_of_swap h.s01
  have b02 := bcomm_of_swap' h.z5 h.s02 (n := 4) rfl
  have b20 := bcomm_of_swap h.s02
  have b03 := bcomm_of_swap' h.z5 h.s03 (n := 1) rfl
  have b30 := bcomm_of_swap h.s03
  have b12 : bcomm (q 1) (q 2) = 1 := by
    rw [bcomm_eq_one_iff]
    have := h.s12
    simp only [cmFive, pow_zero, mul_one] at this
    exact this.symm
  have b21 := bcomm_of_swap h.s12
  have b13 := bcomm_of_swap' h.z5 h.s13 (n := 2) rfl
  have b31 := bcomm_of_swap h.s13
  have b23 := bcomm_of_swap' h.z5 h.s23 (n := 1) rfl
  have b32 := bcomm_of_swap h.s23
  have bii : ∀ i, bcomm (q i) (q i) = 1 := fun i => by rw [bcomm_eq_one_iff]
  have : Fact (1 < 5) := ⟨by norm_num⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Mz, cmFive, b01, b10, b02, b20, b03, b30, b12, b21, b13, b31, b23, b32, bii,
      ZMod.val_one] <;> rfl

theorem mem_closure_z (h : QRel cmFive q z) : z ∈ closure (Set.range q) := by
  have e := h.bcomm_eq 0 1
  have e1 : (Mz 0 1).val = 1 := rfl
  rw [e1, pow_one] at e
  rw [← e]
  unfold bcomm
  have m : ∀ i, q i ∈ closure (Set.range q) := fun i => subset_closure ⟨i, rfl⟩
  exact mul_mem (mul_mem (mul_mem (inv_mem (m 0)) (inv_mem (m 1))) (m 0)) (m 1)

theorem nfQ_mem_Q (h : QRel cmFive q z) (a : QV) : nfQ q z a ∈ closure (Set.range q) := by
  have m : ∀ i, q i ∈ closure (Set.range q) := fun i => subset_closure ⟨i, rfl⟩
  unfold nfQ
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (m 0) _) (pow_mem (m 1) _))
    (pow_mem (m 2) _)) (pow_mem (m 3) _)) (pow_mem (mem_closure_z h) _)

theorem commData (h : QRel cmFive q z) (hz : z ≠ 1) : CommData 5 q z Mz where
  pow_q := h.q5
  orderOf_z := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime h.z5 hz
  comm_z i := (h.zc i).symm
  bcomm_q := h.bcomm_eq
  isUnit_det := isUnit_det_Mz
  mem_z := mem_closure_z h

@[expose] def PSub (x : G) (q : Fin 4 → G) : Subgroup G := closure (Set.range q) ⊔ zpowers x

theorem x_conj_mem (H : PcHyp x q z) : ∀ g ∈ closure (Set.range q),
    x⁻¹ * g * x ∈ closure (Set.range q) := by
  intro g hg
  refine CommData.conj_mem (fun i => ?_) hg
  have hm : ∀ {y : G} {a : QV}, y = nfQ q z a → y ∈ closure (Set.range q) := fun e =>
    e ▸ nfQ_mem_Q H.rel _
  fin_cases i
  · exact hm H.x0
  · exact hm H.x1
  · exact hm H.x2
  · exact hm H.x3

theorem x_not_mem (H : PcHyp x q z) (hz : z ≠ 1) : x ∉ closure (Set.range q) := by
  have e : x⁻¹ * q 0 * x = q 2 := by rw [H.x0]; simp [nfQ, xAct]
  have : NeZero 5 := ⟨by norm_num⟩
  exact (commData H.rel hz).not_mem_of_conj e (by decide)

theorem card_P [Finite G] (H : PcHyp x q z) (hz : z ≠ 1) : Nat.card (PSub x q) = 5 ^ 6 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hx1 : x ≠ 1 := fun h1 => x_not_mem H hz (h1 ▸ one_mem _)
  have hox : orderOf x = 5 := orderOf_eq_prime H.x5 hx1
  unfold PSub
  rw [card_sup_zpowers hox (x_not_mem H hz) (x_conj_mem H), (commData H.rel hz).card_eq]
  norm_num

theorem psi_mem_P (H : PcHyp x q z) (v : V6) : psi x q z v ∈ PSub x q :=
  mul_mem (mem_sup_right (pow_mem (mem_zpowers x) _)) (mem_sup_left (nfQ_mem_Q H.rel _))

@[expose] def TSub [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) : Subgroup G where
  carrier := {g | ∃ i < 15625, psi x q z (dec i) = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨enc (mulV (dec i) (dec j)), enc_lt (mulV_red _ _), ?_⟩
    rw [dec_enc (mulV_red _ _), H.psi_mul hφ (dec_red _) (dec_red _)]
  one_mem' := ⟨0, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨enc (powV (dec i) (Nat.card G - 1)), enc_lt (powV_red _ _), ?_⟩
    rw [dec_enc (powV_red _ _), ← H.psi_pow hφ (dec_red _)]
    have hc : 0 < Nat.card G := Nat.card_pos
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']

theorem gens_mem_T [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) :
    PSub x q ≤ TSub H hφ := by
  unfold PSub
  refine sup_le ((closure_le _).2 ?_) (zpowers_le.2 ⟨3125, by norm_num, by simp [psi, nfQ, dec, decQ]⟩)
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp only [Fin.isValue]
  · exact ⟨625, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨125, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨25, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨5, by norm_num, by simp [psi, nfQ, dec, decQ]⟩

theorem psi_dec_inj [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) (hz : z ≠ 1) {i j : ℕ}
    (hi : i < 15625) (hj : j < 15625) (h : psi x q z (dec i) = psi x q z (dec j)) : i = j := by
  let f : Fin 15625 → PSub x q := fun k => ⟨psi x q z (dec k.val), psi_mem_P H _⟩
  have hs : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := gens_mem_T H hφ hg
    exact ⟨⟨k, hk⟩, rfl⟩
  have hb := hs.bijective_of_nat_card_le (by rw [card_P H hz, Nat.card_fin]; norm_num)
  have := hb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem mem_P_psi [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) {g : G}
    (hg : g ∈ PSub x q) : ∃ i < 15625, psi x q z (dec i) = g := gens_mem_T H hφ hg

theorem forall_of_census [Finite G] (H : PcHyp x q z) (hφ : phiOK () = true) (hz : z ≠ 1)
    (hC : CensusFact) {m : ℕ} (hcard : Nat.card G = 5 ^ 6 * m) (hm : ¬ 5 ∣ m)
    (Good : G → Prop) (hconj : ∀ s c : G, Good s → Good (c * s * c⁻¹))
    (hpow : ∀ s : G, s ^ 5 = 1 → ∀ k : ℕ, Nat.Coprime k 5 → (Good (s ^ k) ↔ Good s))
    (hN : ∀ j < 3, ∃ g, AutRel x q z g (autAt j))
    (hS : ∀ m < 11, ∃ g : G,
      g * psi x q z (dec (nth singleSrc m)) * g⁻¹ = psi x q z (dec (nth singleTgt m)))
    (hT : ∀ i ∈ targets, Good (psi x q z (dec i))) :
    ∀ s : G, orderOf s = 5 → Good s := by
  intro s hs
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow.exists_conj_into_range (by norm_num) (PSub x q).subtype
    Subtype.val_injective (card_P H hz) hcard hm hs
  rw [Subgroup.range_subtype] at hg
  obtain ⟨i, hi, hie⟩ := mem_P_psi H hφ hg
  have hs5 : s ^ 5 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have h5 : psi x q z (dec i) ^ 5 = 1 := by
    have e := conj_pow (a := g⁻¹) (b := s) (i := 5)
    rw [inv_inv] at e
    rw [hie, e, hs5]
    group
  have hord : ord5 (dec i) = true := by
    rw [H.psi_pow hφ (dec_red _), ← psi_one (x := x) (q := q) (z := z)] at h5
    have e1 : V6.one = dec 0 := rfl
    rw [e1, ← dec_enc (powV_red (dec i) 5)] at h5
    have := psi_dec_inj H hφ hz (enc_lt (powV_red _ _)) (by norm_num) h5
    unfold ord5 V6.isOne
    rw [← dec_enc (powV_red (dec i) 5), this]
    exact V6.beq_self _
  have hi0 : i ≠ 0 := by
    rintro rfl
    have e : psi x q z (dec 0) = 1 := by simp [psi, nfQ, dec, decQ]
    rw [e] at hie
    have : s = 1 := by
      have e2 : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [e2, ← hie]
      group
    rw [this, orderOf_one] at hs
    norm_num at hs
  have hgood := fused_good H hφ Good hconj hpow hN hS hT _ (hC i hi hi0 hord) (dec_red _)
  rw [hie] at hgood
  have := hconj _ g hgood
  have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rwa [e] at this

end CFSG.KC.BM.PcFive

end

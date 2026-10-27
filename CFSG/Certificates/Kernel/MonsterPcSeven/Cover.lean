module

public import CFSG.Certificates.Kernel.MonsterPcSeven.Coll
public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Cover

public section

namespace CFSG.KC.MonPcSeven

open Subgroup
open CFSG.Monster.B.Pinned (CommData bcomm bcomm_swap bcomm_eq_one_iff card_sup_zpowers)
open CFSG.KC.BM.PcFive (QV CM QAct G10 QF V6 nth allBelow memN nfQ psi allBelow_spec memN_spec
  bcomm_of_swap PSub)

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

theorem elemOK_spec {rep : ℕ → ℕ} {nc i d : ℕ} (h : elemOK rep nc i d = true) (hi : i ≠ 0) :
    d / 117649 < nc ∧
      mulV (dec (d % 117649)) (dec i) = mulV (dec (rep (d / 117649))) (dec (d % 117649)) := by
  unfold elemOK at h
  simp only [Bool.or_eq_true, Nat.beq_eq, hi, false_or, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1, CFSG.KC.BM.PcFive.V6.beq_eq h.2⟩

theorem stepOK_fused {rep : ℕ → ℕ} {nc : ℕ} {depth : List ℕ} {c c' w : ℕ} {v : V6}
    (h : stepOK rep nc depth c c' w v = true)
    (ih : ∀ c'' < nc, nth depth c'' < nth depth c → Fused (dec (rep c''))) : Fused v := by
  unfold stepOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact Fused.conj (dec_red w) (dec_red _) (CFSG.KC.BM.PcFive.V6.beq_eq h3) (ih c' h1 h2)

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
    · simp only [Bool.not_eq_true] at k0 k1
      simp only [k0, k1, cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hcl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hcl
      exact Fused.pow h3 h1 h2 (stepOK_fused h4 ih')

theorem elem_of_chunks {rep : ℕ → ℕ} {nc : ℕ} {C : ℕ → List ℕ}
    (hC : ∀ k < 49, chunkOK rep nc (2401 * k) (C k) = true)
    (hL : ∀ k < 49, (C k).length = 2401) :
    ∀ i < 117649, elemOK rep nc i (nth (C (i / 2401)) (i % 2401)) = true := by
  intro i hi
  have hk : i / 2401 < 49 := by omega
  have hl : i % 2401 < (C (i / 2401)).length := by
    rw [hL _ hk]
    omega
  have h := chunkOK_spec (hC _ hk) (i % 2401) hl
  rwa [Nat.div_add_mod] at h

theorem census_fact {rep : ℕ → ℕ} {nc : ℕ} {depth kind arg cls wit : List ℕ} {D : ℕ → ℕ}
    (hE : ∀ i < 117649, elemOK rep nc i (D i) = true)
    (hF : fusOK rep nc depth kind arg cls wit = true) : CensusFact := by
  intro i hi hi0
  obtain ⟨h1, h2⟩ := elemOK_spec (hE i hi) hi0
  exact Fused.conj (dec_red _) (dec_red _) h2 (fusOK_fused hF _ h1)

variable {G : Type*} [Group G] {u : G} {q : Fin 4 → G} {z : G}

@[expose] def AutRel (u : G) (q : Fin 4 → G) (z g : G) (ws : List ℕ) : Prop :=
  g * u * g⁻¹ = psi u q z (dec (nth ws 0)) ∧ g * q 0 * g⁻¹ = psi u q z (dec (nth ws 1)) ∧
    g * q 1 * g⁻¹ = psi u q z (dec (nth ws 2)) ∧ g * q 2 * g⁻¹ = psi u q z (dec (nth ws 3)) ∧
    g * q 3 * g⁻¹ = psi u q z (dec (nth ws 4)) ∧ g * z * g⁻¹ = psi u q z (dec (nth ws 5))

theorem ord7_spec {v : V6} (h : ord7 v = true) : powV v 7 = ⟨0, ⟨0, 0, 0, 0, 0⟩⟩ :=
  CFSG.KC.BM.PcFive.V6.beq_eq h

theorem fused_good (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) (Good : G → Prop)
    (hconj : ∀ s c : G, Good s → Good (c * s * c⁻¹))
    (hpow : ∀ s : G, s ^ 7 = 1 → ∀ k : ℕ, Nat.Coprime k 7 → (Good (s ^ k) ↔ Good s))
    (hN : ∀ j < 2, ∃ g, AutRel u q z g (autAt j))
    (hT : ∀ i ∈ targets, Good (psi u q z (dec i))) :
    ∀ v, Fused v → redV v → Good (psi u q z v) := by
  have hback : ∀ s c : G, Good (c * s * c⁻¹) → Good s := fun s c h => by
    have h' := hconj _ c⁻¹ h
    have e : c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s := by group
    rwa [e] at h'
  intro v hv
  induction hv with
  | target hi => exact fun _ => hT _ hi
  | @conj v w g hg hw heq _ ih =>
    intro hvr
    have e1 := H.psi_mul C hg hvr
    have e2 := H.psi_mul C hw hg
    rw [heq, ← e2] at e1
    have e : psi u q z v = (psi u q z g)⁻¹ * psi u q z w * (psi u q z g)⁻¹⁻¹ := by
      rw [inv_inv, mul_assoc, ← e1]
      group
    rw [e]
    exact hconj _ _ (ih hw)
  | @aut v j hj _ ih =>
    intro hvr
    obtain ⟨g, h0, h1, h2, h3, h4, h5⟩ := hN j hj
    apply hback _ g
    rw [H.conj_alpha C h0 h1 h2 h3 h4 h5]
    exact ih (mulV_red _ _)
  | @pow v k ho hk2 hk7 _ ih =>
    intro hvr
    have h7 : psi u q z v ^ 7 = 1 := by
      rw [H.psi_pow C hvr, ord7_spec ho, psi_zero]
    have hcop : Nat.Coprime k 7 := by interval_cases k <;> norm_num
    refine (hpow _ h7 k hcop).1 ?_
    rw [H.psi_pow C hvr]
    exact ih (powV_red _ _)

@[expose] def Mz : Matrix (Fin 4) (Fin 4) (ZMod 7) := !![0, 6, 1, 1; 1, 0, 6, 0; 6, 1, 0, 0; 6, 0, 0, 0]

@[expose] def MzInv : Matrix (Fin 4) (Fin 4) (ZMod 7) :=
  !![0, 0, 0, 6; 0, 0, 1, 6; 0, 6, 0, 6; 1, 1, 1, 0]

theorem Mz_mul_inv : Mz * MzInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem isUnit_det_Mz : IsUnit Mz.det := by
  have h := congrArg Matrix.det Mz_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem bcomm_of_swap' (hz : z ^ 7 = 1) {a b : G} {k n : ℕ} (h : b * a = a * b * z ^ k)
    (hkn : k + n = 7) : bcomm a b = z ^ n := by
  have e := bcomm_swap a b
  rw [bcomm_of_swap h] at e
  have e2 : bcomm a b = (z ^ k)⁻¹ := by rw [e, inv_inv]
  rw [e2, inv_eq_iff_mul_eq_one, ← pow_add, hkn, hz]

theorem bcomm_of_comm {a b : G} (h : b * a = a * b * z ^ 0) : bcomm a b = 1 := by
  rw [bcomm_eq_one_iff]
  rw [pow_zero, mul_one] at h
  exact h.symm

theorem QRel.bcomm_eq (h : QRel cmSeven q z) : ∀ i j, bcomm (q i) (q j) = z ^ (Mz i j).val := by
  have b01 := bcomm_of_swap' h.z7 h.s01 (n := 6) rfl
  have b10 := bcomm_of_swap h.s01
  have b02 := bcomm_of_swap' h.z7 h.s02 (n := 1) rfl
  have b20 := bcomm_of_swap h.s02
  have b03 := bcomm_of_swap' h.z7 h.s03 (n := 1) rfl
  have b30 := bcomm_of_swap h.s03
  have b12 := bcomm_of_swap' h.z7 h.s12 (n := 6) rfl
  have b21 := bcomm_of_swap h.s12
  have b13 := bcomm_of_comm h.s13
  have b31 := bcomm_of_swap h.s13
  have b23 := bcomm_of_comm h.s23
  have b32 := bcomm_of_swap h.s23
  have bii : ∀ i, bcomm (q i) (q i) = 1 := fun i => by rw [bcomm_eq_one_iff]
  have : Fact (1 < 7) := ⟨by norm_num⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Mz, cmSeven, b01, b10, b02, b20, b03, b30, b12, b21, b13, b31, b23, b32, bii,
      ZMod.val_one] <;> rfl

theorem mem_closure_z (h : QRel cmSeven q z) : z ∈ closure (Set.range q) := by
  have e := bcomm_of_swap h.s01
  have e1 : cmSeven.m01 = 1 := rfl
  rw [e1, pow_one] at e
  rw [← e]
  unfold bcomm
  have m : ∀ i, q i ∈ closure (Set.range q) := fun i => subset_closure ⟨i, rfl⟩
  exact mul_mem (mul_mem (mul_mem (inv_mem (m 1)) (inv_mem (m 0))) (m 1)) (m 0)

theorem nfQ_mem_Q (h : QRel cmSeven q z) (a : QV) : nfQ q z a ∈ closure (Set.range q) := by
  have m : ∀ i, q i ∈ closure (Set.range q) := fun i => subset_closure ⟨i, rfl⟩
  unfold nfQ
  exact mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (m 0) _) (pow_mem (m 1) _))
    (pow_mem (m 2) _)) (pow_mem (m 3) _)) (pow_mem (mem_closure_z h) _)

theorem commData (h : QRel cmSeven q z) (hz : z ≠ 1) : CommData 7 q z Mz where
  pow_q := h.q7
  orderOf_z := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime h.z7 hz
  comm_z i := (h.zc i).symm
  bcomm_q := h.bcomm_eq
  isUnit_det := isUnit_det_Mz
  mem_z := mem_closure_z h

theorem u_conj_mem (H : PcHyp u q z) : ∀ g ∈ closure (Set.range q),
    u⁻¹ * g * u ∈ closure (Set.range q) := by
  have fwd : ∀ g ∈ closure (Set.range q), u * g * u⁻¹ ∈ closure (Set.range q) := by
    intro g hg
    have hb : ∀ i, (u⁻¹)⁻¹ * q i * u⁻¹ ∈ closure (Set.range q) := fun i => by
      rw [inv_inv]
      fin_cases i
      · exact H.c0 ▸ nfQ_mem_Q H.rel _
      · exact H.c1 ▸ nfQ_mem_Q H.rel _
      · exact H.c2 ▸ nfQ_mem_Q H.rel _
      · exact H.c3 ▸ nfQ_mem_Q H.rel _
    have := CommData.conj_mem (b := u⁻¹) (q := q) hb hg
    rwa [inv_inv] at this
  have h6 : ∀ k : ℕ, ∀ y ∈ closure (Set.range q), u ^ k * y * (u ^ k)⁻¹ ∈ closure (Set.range q) := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      have e2 : u ^ (k + 1) * y * (u ^ (k + 1))⁻¹ = u * (u ^ k * y * (u ^ k)⁻¹) * u⁻¹ := by
        rw [pow_succ']; group
      rw [e2]
      exact fwd _ (ih y hy)
  intro g hg
  have e : u ^ 6 = u⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact H.u7
  have := h6 6 g hg
  rwa [e, inv_inv] at this

theorem u_not_mem (H : PcHyp u q z) (hz : z ≠ 1) : u ∉ closure (Set.range q) := by
  intro hu
  have hD := commData H.rel hz
  have : NeZero 7 := ⟨by norm_num⟩
  have m : ∀ i, q i ∈ closure (Set.range q) := fun i => subset_closure ⟨i, rfl⟩
  have h := hD.psi_conj (inv_mem hu) (m 2)
  rw [inv_inv, H.c2] at h
  have e : nfQ q z uAct.r2 = q 2 * q 3 * z ^ 5 := by simp [nfQ, uAct]
  rw [e, hD.psi_mul (mul_mem (m 2) (m 3)) (pow_mem (mem_closure_z H.rel) _),
    hD.psi_mul (m 2) (m 3), hD.psi_of_mem_zpowers (pow_mem (mem_zpowers z) _), hD.psi_q,
    hD.psi_q, add_zero, add_eq_left] at h
  have h0 := congrFun h 0
  revert h0
  decide

theorem card_P [Finite G] (H : PcHyp u q z) (hz : z ≠ 1) : Nat.card (PSub u q) = 7 ^ 6 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hu1 : u ≠ 1 := fun h1 => u_not_mem H hz (h1 ▸ one_mem _)
  have hou : orderOf u = 7 := orderOf_eq_prime H.u7 hu1
  unfold PSub
  rw [card_sup_zpowers hou (u_not_mem H hz) (u_conj_mem H), (commData H.rel hz).card_eq]
  norm_num

theorem psi_dec_zero : psi u q z (dec 0) = 1 := by simp [psi, nfQ, dec, decQ]

@[expose] def TSub [Finite G] (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) :
    Subgroup G where
  carrier := {g | ∃ i < 117649, psi u q z (dec i) = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨enc (mulV (dec i) (dec j)), enc_lt (mulV_red _ _), ?_⟩
    rw [dec_enc (mulV_red _ _), H.psi_mul C (dec_red _) (dec_red _)]
  one_mem' := ⟨0, by norm_num, psi_dec_zero⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨enc (powV (dec i) (Nat.card G - 1)), enc_lt (powV_red _ _), ?_⟩
    rw [dec_enc (powV_red _ _), ← H.psi_pow C (dec_red _)]
    have hc : 0 < Nat.card G := Nat.card_pos
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']

theorem gens_mem_T [Finite G] (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) :
    PSub u q ≤ TSub H C := by
  unfold PSub
  refine sup_le ((closure_le _).2 ?_) (zpowers_le.2 ⟨16807, by norm_num, by simp [psi, nfQ, dec, decQ]⟩)
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp only [Fin.isValue]
  · exact ⟨2401, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨343, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨49, by norm_num, by simp [psi, nfQ, dec, decQ]⟩
  · exact ⟨7, by norm_num, by simp [psi, nfQ, dec, decQ]⟩

theorem mem_P_psi [Finite G] (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true) {g : G}
    (hg : g ∈ PSub u q) : ∃ i < 117649, psi u q z (dec i) = g := gens_mem_T H C hg

theorem forall_of_census [Finite G] (H : PcHyp u q z) (C : ∀ k < 7, phiOK (343 * k) 343 = true)
    (hz : z ≠ 1) (hC : CensusFact) {m : ℕ} (hcard : Nat.card G = 7 ^ 6 * m) (hm : ¬ 7 ∣ m)
    (Good : G → Prop) (hconj : ∀ s c : G, Good s → Good (c * s * c⁻¹))
    (hpow : ∀ s : G, s ^ 7 = 1 → ∀ k : ℕ, Nat.Coprime k 7 → (Good (s ^ k) ↔ Good s))
    (hN : ∀ j < 2, ∃ g, AutRel u q z g (autAt j))
    (hT : ∀ i ∈ targets, Good (psi u q z (dec i))) :
    ∀ s : G, orderOf s = 7 → Good s := by
  intro s hs
  obtain ⟨g, hg⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow.exists_conj_into_range (by norm_num)
      (PSub u q).subtype Subtype.val_injective (card_P H hz) hcard hm hs
  rw [Subgroup.range_subtype] at hg
  obtain ⟨i, hi, hie⟩ := mem_P_psi H C hg
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [psi_dec_zero] at hie
    have : s = 1 := by
      have e2 : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [e2, ← hie]
      group
    rw [this, orderOf_one] at hs
    norm_num at hs
  have hgood := fused_good H C Good hconj hpow hN hT _ (hC i hi hi0) (dec_red _)
  rw [hie] at hgood
  have := hconj _ g hgood
  have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
  rwa [e] at this

end CFSG.KC.MonPcSeven

end

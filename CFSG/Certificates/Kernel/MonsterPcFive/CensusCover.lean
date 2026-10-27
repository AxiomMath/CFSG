module

public import CFSG.Certificates.Kernel.MonsterPcFive.E3Sound
public import Certificates.Data.Kernel.MonsterPcFive.Census

public section

namespace CFSG.KC.MonPcFive

open Subgroup
open CFSG.Monster.B.Pinned (CommData coord)
open CFSG.KC.BM.PcFive (pow_mod_five)

variable {G : Type*} [Group G]

@[expose] def hz (a : Fin 4 → G) (v : Fin 4 → ZMod 5) : G :=
  a 0 ^ (v 0).val * a 1 ^ (v 1).val * a 2 ^ (v 2).val * a 3 ^ (v 3).val

structure Comm4 (a : Fin 4 → G) : Prop where
  comm : ∀ i j, Commute (a i) (a j)
  pow5 : ∀ i, a i ^ 5 = 1

variable {a : Fin 4 → G}

theorem Comm4.hz_add (h : Comm4 a) (v w : Fin 4 → ZMod 5) : hz a (v + w) = hz a v * hz a w := by
  have e : ∀ i, a i ^ (v i + w i).val = a i ^ (v i).val * a i ^ (w i).val := by
    intro i
    rw [ZMod.val_add, ← pow_mod_five (h.pow5 i), pow_add]
  have c : ∀ i j (p q : ℕ), Commute (a i ^ p) (a j ^ q) := fun i j p q => (h.comm i j).pow_pow p q
  unfold hz
  simp only [Pi.add_apply, e]
  rw [(c 0 1 (w 0).val (v 1).val).mul_mul_mul_comm,
    ((c 0 2 (w 0).val (v 2).val).mul_left (c 1 2 (w 1).val (v 2).val)).mul_mul_mul_comm,
    (((c 0 3 (w 0).val (v 3).val).mul_left (c 1 3 (w 1).val (v 3).val)).mul_left
      (c 2 3 (w 2).val (v 3).val)).mul_mul_mul_comm]

theorem hz_zero : hz a 0 = 1 := by simp [hz]

theorem Comm4.hz_neg (h : Comm4 a) (v : Fin 4 → ZMod 5) : hz a (-v) = (hz a v)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← h.hz_add, neg_add_cancel, hz_zero]

theorem Comm4.hz_nsmul (h : Comm4 a) (v : Fin 4 → ZMod 5) : ∀ k : ℕ, hz a (k • v) = hz a v ^ k
  | 0 => by rw [zero_nsmul, hz_zero, pow_zero]
  | k + 1 => by rw [succ_nsmul, h.hz_add, h.hz_nsmul v k, pow_succ]

theorem Comm4.conj_hz (h : Comm4 a) {c : G} {col : Fin 4 → Fin 4 → ZMod 5}
    (hc : ∀ j, c⁻¹ * a j * c = hz a (col j)) (v : Fin 4 → ZMod 5) :
    c⁻¹ * hz a v * c = hz a (fun i => ∑ j, v j * col j i) := by
  have key : ∀ y, c⁻¹ * y * c = MulAut.conj c⁻¹ y := fun y => by
    rw [MulAut.conj_apply, inv_inv]
  have : NeZero 5 := ⟨by norm_num⟩
  have e : (fun i => ∑ j, v j * col j i) =
      (v 0).val • col 0 + (v 1).val • col 1 + (v 2).val • col 2 + (v 3).val • col 3 := by
    funext i
    simp only [Fin.sum_univ_four, Pi.add_apply, Pi.smul_apply]
    simp only [nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [key, e, h.hz_add, h.hz_add, h.hz_add, h.hz_nsmul, h.hz_nsmul, h.hz_nsmul, h.hz_nsmul]
  simp only [hz, map_mul, map_pow]
  simp only [← key, hc, hz]

@[expose] def NormBy (a : Fin 4 → G) (y : G) : Prop := ∀ w, ∃ w', y * hz a w * y⁻¹ = hz a w'

theorem Comm4.normBy_of_conj (h : Comm4 a) {y : G} {col : Fin 4 → Fin 4 → ZMod 5}
    (hc : ∀ j, y * a j * y⁻¹ = hz a (col j)) : NormBy a y := by
  intro w
  have := h.conj_hz (c := y⁻¹) (col := col) (fun j => by rw [inv_inv]; exact hc j) w
  rw [inv_inv] at this
  exact ⟨_, this⟩

theorem normBy_mul {y z : G} (hy : NormBy a y) (hz' : NormBy a z) : NormBy a (y * z) := by
  intro w
  obtain ⟨w1, e1⟩ := hz' w
  obtain ⟨w2, e2⟩ := hy w1
  refine ⟨w2, ?_⟩
  rw [← e2, ← e1]
  group

theorem normBy_one : NormBy a (1 : G) := fun w => ⟨w, by group⟩

theorem normBy_pow {y : G} (hy : NormBy a y) : ∀ k : ℕ, NormBy a (y ^ k)
  | 0 => by rw [pow_zero]; exact normBy_one
  | k + 1 => by rw [pow_succ]; exact normBy_mul (normBy_pow hy k) hy

variable {u2 u1 : G} {b : Fin 6 → G} {x : G}

@[expose] def aG (b : Fin 6 → G) (x : G) : Fin 4 → G := fun j => nfR b x (aR j.val)

@[expose] def dg (n : ℕ) : Fin 4 → ZMod 5 := fun i => ((d4 n i.val : ℕ) : ZMod 5)

theorem aR_red (k : ℕ) : (aR k).red := by
  unfold aR
  cases k.beq 0 <;> cases k.beq 1 <;> cases k.beq 2 <;> simp [RV.red, aR0, aR1, aR2, RV.xg]

theorem genV_red (i : ℕ) : (genV i).red := dec_red _

theorem psi_zr (u2 u1 : G) (b : Fin 6 → G) (x : G) (r : RV) :
    psi u2 u1 b x ⟨0, 0, r⟩ = nfR b x r := by
  simp [psi]

theorem red0 {r : RV} (hr : r.red) : (⟨0, 0, r⟩ : V9).red := ⟨by norm_num, by norm_num, hr⟩

theorem iotaV_red (n : ℕ) : (iotaV n).red := red0 (mulR_red _ _ _)

theorem RRel.comm_x (h : RRel cmM b x) (r : RV) : Commute x (nfR b x r) := by
  have hb : ∀ i, Commute x (b i) := fun i => h.xc i
  unfold nfR
  exact (((((((hb 0).pow_right _).mul_right ((hb 1).pow_right _)).mul_right
    ((hb 2).pow_right _)).mul_right ((hb 3).pow_right _)).mul_right ((hb 4).pow_right _)).mul_right
    ((hb 5).pow_right _)).mul_right ((Commute.refl x).pow_right _)

theorem aG_three : aG b x 3 = x := by
  have e : aG b x 3 = nfR b x RV.xg := rfl
  rw [e, nfR_xg]

theorem dg_apply (n : ℕ) : dg n = ![((n / 125 % 5 : ℕ) : ZMod 5), ((n / 25 % 5 : ℕ) : ZMod 5),
    ((n / 5 % 5 : ℕ) : ZMod 5), ((n % 5 : ℕ) : ZMod 5)] := by
  funext i
  fin_cases i <;> rfl

theorem hz_mk (p0 p1 p2 p3 : ZMod 5) : hz (aG b x) ![p0, p1, p2, p3] =
    nfR b x aR0 ^ p0.val * nfR b x aR1 ^ p1.val * nfR b x aR2 ^ p2.val * x ^ p3.val := by
  unfold hz
  rw [aG_three]
  rfl

theorem psi_iotaV (H : PcHyp u2 u1 b x) (n : ℕ) : psi u2 u1 b x (iotaV n) = hz (aG b x) (dg n) := by
  unfold iotaV
  rw [psi_zr]
  unfold iotaR
  rw [← nfR_mul H.rel, ← nfR_mul H.rel, ← nfR_mul H.rel, ← nfR_pow H.rel, ← nfR_pow H.rel,
    ← nfR_pow H.rel, nfR_xc, dg_apply, hz_mk]
  simp only [ZMod.val_natCast, Nat.mod_mod]

theorem cosT_mk {e0 e1 s0 s1 s2 : ℕ} (h0 : e0 < 5) (h1 : e1 < 5) (h2 : s0 < 5) (h3 : s1 < 5)
    (h4 : s2 < 5) :
    cosT (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) = ⟨e0, e1, ⟨0, 0, 0, s0, s1, s2, 0⟩⟩ := by
  have a0 : (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) / 625 % 5 = e0 := by omega
  have a1 : (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) / 125 % 5 = e1 := by omega
  have a2 : (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) / 25 % 5 = s0 := by omega
  have a3 : (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) / 5 % 5 = s1 := by omega
  have a4 : (625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2) % 5 = s2 := by omega
  unfold cosT
  rw [a0, a1, a2, a3, a4]

theorem comm4_of_aOK (H : PcHyp u2 u1 b x) {nrm : List ℕ} (h : aOK nrm = true) :
    Comm4 (aG b x) := by
  unfold aOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h01, h02⟩, h12⟩, p0⟩, p1⟩, p2⟩, -⟩ := h
  have cm : ∀ {r s : RV}, (mulR cmM r s).beq (mulR cmM s r) = true →
      Commute (nfR b x r) (nfR b x s) := by
    intro r s e
    change nfR b x r * nfR b x s = nfR b x s * nfR b x r
    rw [nfR_mul H.rel, nfR_mul H.rel, RV.beq_eq e]
  have pw : ∀ {r : RV}, (powR cmM r 5).beq RV.one = true → nfR b x r ^ 5 = 1 := by
    intro r e
    rw [nfR_pow H.rel, RV.beq_eq e, nfR_one]
  have c01 := cm h01
  have c02 := cm h02
  have c12 := cm h12
  have cx : ∀ i, Commute (aG b x i) (aG b x 3) := fun i => by
    rw [aG_three]
    exact (H.rel.comm_x _).symm
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j
    all_goals first
      | exact Commute.refl _
      | exact c01 | exact c01.symm | exact c02 | exact c02.symm | exact c12 | exact c12.symm
      | exact cx _ | exact (cx _).symm
  · fin_cases i
    · exact pw p0
    · exact pw p1
    · exact pw p2
    · change aG b x 3 ^ 5 = 1
      rw [aG_three]
      exact H.rel.x5

theorem psi_genV0 : psi u2 u1 b x (genV 0) = u2 := by simp [genV, psi, nfR, dec, decR]
theorem psi_genV1 : psi u2 u1 b x (genV 1) = u1 := by simp [genV, psi, nfR, dec, decR]
theorem psi_genV8 : psi u2 u1 b x (genV 8) = x := by simp [genV, psi, nfR, dec, decR]
theorem psi_genVb (i : Fin 6) : psi u2 u1 b x (genV (i.val + 2)) = b i := by
  fin_cases i <;> simp [genV, psi, nfR, dec, decR]

theorem gen_conj_aOK (H : PcHyp u2 u1 b x) (C : TabChecks) {nrm : List ℕ} (h : aOK nrm = true)
    {i : ℕ} (hi : i < 9) (k : Fin 4) :
    psi u2 u1 b x (genV i) * aG b x k * (psi u2 u1 b x (genV i))⁻¹ =
      hz (aG b x) (dg (nthN nrm (4 * i + k.val))) := by
  unfold aOK at h
  simp only [Bool.and_eq_true] at h
  have e := V9.beq_eq (allBelow_spec (allBelow_spec h.2 i hi) k.val k.2)
  have e2 := congrArg (psi u2 u1 b x) e
  rw [← H.psi_mul C (genV_red i) (red0 (aR_red _)), ← H.psi_mul C (iotaV_red _) (genV_red i),
    psi_zr, psi_iotaV H] at e2
  rw [mul_inv_eq_iff_eq_mul]
  exact e2

theorem normBy_gen (H : PcHyp u2 u1 b x) (C : TabChecks) {nrm : List ℕ} (h : aOK nrm = true)
    {i : ℕ} (hi : i < 9) : NormBy (aG b x) (psi u2 u1 b x (genV i)) :=
  (comm4_of_aOK H h).normBy_of_conj (fun k => gen_conj_aOK H C h hi k)

theorem normBy_psi (H : PcHyp u2 u1 b x) (C : TabChecks) {nrm : List ℕ} (h : aOK nrm = true)
    (v : V9) : NormBy (aG b x) (psi u2 u1 b x v) := by
  have g0 := normBy_gen H C h (i := 0) (by norm_num)
  have g1 := normBy_gen H C h (i := 1) (by norm_num)
  have g8 := normBy_gen H C h (i := 8) (by norm_num)
  have gb : ∀ i : Fin 6, NormBy (aG b x) (b i) := fun i => by
    rw [← psi_genVb (u2 := u2) (u1 := u1) (b := b) (x := x) i]
    exact normBy_gen H C h (by omega)
  rw [psi_genV0] at g0
  rw [psi_genV1] at g1
  rw [psi_genV8] at g8
  unfold psi nfR
  exact normBy_mul (normBy_mul (normBy_pow g0 _) (normBy_pow g1 _))
    (normBy_mul (normBy_mul (normBy_mul (normBy_mul (normBy_mul (normBy_mul (normBy_pow (gb 0) _)
      (normBy_pow (gb 1) _)) (normBy_pow (gb 2) _)) (normBy_pow (gb 3) _)) (normBy_pow (gb 4) _))
      (normBy_pow (gb 5) _)) (normBy_pow g8 _))

section Coord

variable (hD : CommData 5 b x Mz)
include hD

theorem coord_mul' {g h : G} (hg : g ∈ closure (Set.range b)) (hh : h ∈ closure (Set.range b)) :
    coord 5 b x Mz (g * h) = coord 5 b x Mz g + coord 5 b x Mz h := by
  unfold coord
  rw [hD.psi_mul hg hh, Matrix.add_vecMul]

theorem coord_pow' {g : G} (hg : g ∈ closure (Set.range b)) :
    ∀ k : ℕ, coord 5 b x Mz (g ^ k) = k • coord 5 b x Mz g
  | 0 => by
    unfold coord
    rw [pow_zero, hD.psi_one, Matrix.zero_vecMul, zero_nsmul]
  | k + 1 => by
    rw [pow_succ, coord_mul' hD (pow_mem hg k) hg, coord_pow' hg k, succ_nsmul]

theorem coord_xpow (k : ℕ) : coord 5 b x Mz (x ^ k) = 0 := by
  unfold coord
  rw [hD.psi_of_mem_zpowers (pow_mem (mem_zpowers x) k), Matrix.zero_vecMul]

theorem eq_mul_x_of_coord [Finite G] {g h : G} (hg : g ∈ closure (Set.range b))
    (hh : h ∈ closure (Set.range b)) (e : coord 5 b x Mz g = coord 5 b x Mz h) :
    ∃ c : ℕ, g = h * x ^ c := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : ∀ y, CFSG.Monster.B.Pinned.psi 5 b x y = Matrix.vecMul (coord 5 b x Mz y) Mz :=
      fun y => by
    unfold coord
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ isUnit_det_Mz, Matrix.vecMul_one]
  have hy : h⁻¹ * g ∈ closure (Set.range b) := mul_mem (inv_mem hh) hg
  have h0 : CFSG.Monster.B.Pinned.psi 5 b x (h⁻¹ * g) = 0 := by
    rw [hD.psi_mul (inv_mem hh) hg, hD.psi_inv hh, hp g, hp h, e, neg_add_cancel]
  have hker : (⟨h⁻¹ * g, hy⟩ : closure (Set.range b)) ∈ hD.psiHom.ker := by
    rw [MonoidHom.mem_ker, CommData.psiHom_apply, h0, ofAdd_zero]
  rw [hD.card_eq_and_ker.2] at hker
  have hz : h⁻¹ * g ∈ zpowers x := mem_subgroupOf.1 hker
  rw [← (isOfFinOrder_of_finite x).mem_powers_iff_mem_zpowers] at hz
  obtain ⟨c, hc⟩ := hz
  have hc' : x ^ c = h⁻¹ * g := hc
  refine ⟨c, ?_⟩
  rw [hc']
  group

end Coord

theorem nfR_mem_A (H : PcHyp u2 u1 b x) (w : Fin 4 → ZMod 5) :
    hz (aG b x) w ∈ closure (Set.range b) := by
  unfold hz
  refine mul_mem (mul_mem (mul_mem (pow_mem (nfR_mem H.rel _) _) (pow_mem (nfR_mem H.rel _) _))
    (pow_mem (nfR_mem H.rel _) _)) (pow_mem ?_ _)
  rw [aG_three]
  exact H.rel.mem_x

theorem cover_coset [Finite G] (H : PcHyp u2 u1 b x) (hx : x ≠ 1) (h4 : Comm4 (aG b x)) {v : V9}
    (hv : v.red) :
    ∃ k < 3125, ∃ w, psi u2 u1 b x v = psi u2 u1 b x (cosT k) * hz (aG b x) w := by
  obtain ⟨he0, he1, h0, h1, h2, h3, h4', h5, h6⟩ := hv
  obtain ⟨e0, e1, ⟨r0, r1, r2, r3, r4, r5, rc⟩⟩ := v
  simp only at he0 he1 h0 h1 h2 h3 h4' h5 h6
  have hD := H.rel.commData hx
  have : NeZero 5 := ⟨by norm_num⟩
  set s0 := (r3 + 2 * r1 + r2) % 5
  set s1 := (r4 + 4 * r0 + 3 * r1 + 4 * r2) % 5
  set s2 := (r5 + 4 * r0 + 2 * r1 + 2 * r2) % 5
  let sv : RV := ⟨0, 0, 0, s0, s1, s2, 0⟩
  have hsv : sv.red := ⟨by norm_num, by norm_num, by norm_num, Nat.mod_lt _ (by norm_num),
    Nat.mod_lt _ (by norm_num), Nat.mod_lt _ (by norm_num), by norm_num⟩
  let w0 : Fin 4 → ZMod 5 := ![(r0 : ZMod 5), (r1 : ZMod 5), (r2 : ZMod 5), 0]
  let r : RV := ⟨r0, r1, r2, r3, r4, r5, rc⟩
  have hr : r.red := ⟨h0, h1, h2, h3, h4', h5, h6⟩
  have hcA : ∀ j : Fin 4, coord 5 b x Mz (aG b x j) = fun l => (((aR j.val).digs l : ℕ) : ZMod 5) :=
    fun j => coord_nfR H.rel hx (aR_red _)
  have hm : ∀ j : Fin 4, aG b x j ∈ closure (Set.range b) := fun j => nfR_mem H.rel _
  have ec : coord 5 b x Mz (nfR b x r) = coord 5 b x Mz (nfR b x sv * hz (aG b x) w0) := by
    rw [coord_nfR H.rel hx hr, coord_mul' hD (nfR_mem H.rel _) (nfR_mem_A H w0)]
    unfold hz
    rw [coord_mul' hD (mul_mem (mul_mem (pow_mem (hm 0) _) (pow_mem (hm 1) _)) (pow_mem (hm 2) _))
        (pow_mem (hm 3) _),
      coord_mul' hD (mul_mem (pow_mem (hm 0) _) (pow_mem (hm 1) _)) (pow_mem (hm 2) _),
      coord_mul' hD (pow_mem (hm 0) _) (pow_mem (hm 1) _), coord_pow' hD (hm 0),
      coord_pow' hD (hm 1), coord_pow' hD (hm 2), aG_three, coord_xpow hD, coord_nfR H.rel hx hsv,
      hcA, hcA, hcA]
    funext l
    have e0' : aR 0 = aR0 := rfl
    have e1' : aR 1 = aR1 := rfl
    have e2' : aR 2 = aR2 := rfl
    fin_cases l <;>
      simp [w0, sv, r, s0, s1, s2, RV.digs, aR0, aR1, aR2, e0', e1', e2', ZMod.val_natCast,
        Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, nsmul_eq_mul] <;>
      ring_nf <;> reduce_mod_char
  obtain ⟨c, hc⟩ := eq_mul_x_of_coord hD (nfR_mem H.rel _)
    (mul_mem (nfR_mem H.rel _) (nfR_mem_A H w0)) ec
  have hs0 : s0 < 5 := Nat.mod_lt _ (by norm_num)
  have hs1 : s1 < 5 := Nat.mod_lt _ (by norm_num)
  have hs2 : s2 < 5 := Nat.mod_lt _ (by norm_num)
  set wf : Fin 4 → ZMod 5 := ![(r0 : ZMod 5), (r1 : ZMod 5), (r2 : ZMod 5), (c : ZMod 5)]
  have hw : hz (aG b x) w0 * x ^ c = hz (aG b x) wf := by
    rw [hz_mk, hz_mk]
    simp only [ZMod.val_zero, pow_zero, mul_one, ZMod.val_natCast]
    rw [← pow_mod_five H.rel.x5]
  refine ⟨625 * e0 + 125 * e1 + 25 * s0 + 5 * s1 + s2, by omega, wf, ?_⟩
  rw [cosT_mk he0 he1 hs0 hs1 hs2]
  calc psi u2 u1 b x ⟨e0, e1, r⟩ = u2 ^ e0 * u1 ^ e1 * nfR b x r := rfl
    _ = u2 ^ e0 * u1 ^ e1 * nfR b x sv * hz (aG b x) wf := by
      rw [hc, mul_assoc (nfR b x sv), hw]
      simp only [mul_assoc]
    _ = psi u2 u1 b x ⟨e0, e1, sv⟩ * hz (aG b x) wf := rfl

end CFSG.KC.MonPcFive

end

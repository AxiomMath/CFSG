module

public import CFSG.Certificates.Kernel.MonsterPcFive.CensusCover
public import CFSG.Certificates.Kernel.MonsterPcFive.CensusRun

public section

namespace CFSG.KC.MonPcFive

open Subgroup
open CFSG.KC.BM.PcFive (pow_mod_five)

variable {G : Type*} [Group G] {u2 u1 : G} {b : Fin 6 → G} {x : G}

theorem delta_eq (i j : ℕ) : delta i j = if i = j then 1 else 0 := by
  unfold delta
  cases h : i.beq j
  · have hne : i ≠ j := Nat.ne_of_beq_eq_false h
    simp [hne]
  · simp [Nat.eq_of_beq_eq_true h]

theorem sel4_0 (c0 c1 c2 c3 : ℕ) : sel4 c0 c1 c2 c3 0 = c0 := rfl
theorem sel4_1 (c0 c1 c2 c3 : ℕ) : sel4 c0 c1 c2 c3 1 = c1 := rfl
theorem sel4_2 (c0 c1 c2 c3 : ℕ) : sel4 c0 c1 c2 c3 2 = c2 := rfl
theorem sel4_3 (c0 c1 c2 c3 : ℕ) : sel4 c0 c1 c2 c3 3 = c3 := rfl

theorem fin4_val3 : (3 : Fin 4).val = 3 := rfl

theorem pi_ident (c0 c1 c2 c3 s0 s1 s2 s3 : ℕ) (u : Fin 4 → ZMod 5) (i : Fin 4) :
    (∑ j, -(∑ j', u j' * dg (sel4 s0 s1 s2 s3 j'.val) j) * dg (sel4 c0 c1 c2 c3 j.val) i) + u i +
      (∑ j, u j * dg (sel4 s0 s1 s2 s3 j.val) i) =
      ∑ j, u j * ((piE c0 c1 c2 c3 s0 s1 s2 s3 i.val j.val : ℕ) : ZMod 5) := by
  have h4 : (4 : ZMod 5) = -1 := by decide
  fin_cases i <;>
    simp only [Fin.sum_univ_four, piE, dg, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two,
      fin4_val3, sel4_0, sel4_1, sel4_2, sel4_3, delta_eq, ZMod.natCast_mod] <;>
    norm_num <;> push_cast <;> rw [h4] <;> ring

theorem cosT_red (k : ℕ) : (cosT k).red := by
  unfold cosT V9.red RV.red
  dsimp only
  omega

theorem rep_step (H : PcHyp u2 u1 b x) (C : TabChecks) (h4 : Comm4 (aG b x)) {t : V9}
    (ht : t.red) {c0 c1 c2 c3 s0 s1 s2 s3 m : ℕ} (hc : colOK t c0 c1 c2 c3 = true)
    (hp : piOK c0 c1 c2 c3 s0 s1 s2 s3 m = true) (u : Fin 4 → ZMod 5) :
    ∃ E : G, ∃ cc < 625, (∀ i < 4, inJ m i = false → d4 cc i = 0) ∧
      E⁻¹ * (psi u2 u1 b x t * hz (aG b x) u) * E = psi u2 u1 b x (mulV t (iotaV cc)) := by
  have : NeZero 5 := ⟨by norm_num⟩
  set col : Fin 4 → Fin 4 → ZMod 5 := fun j => dg (sel4 c0 c1 c2 c3 j.val) with hcol_def
  set scol : Fin 4 → Fin 4 → ZMod 5 := fun j => dg (sel4 s0 s1 s2 s3 j.val) with hscol_def
  have hcol : ∀ j : Fin 4, (psi u2 u1 b x t)⁻¹ * aG b x j * psi u2 u1 b x t = hz (aG b x) (col j) := by
    intro j
    have e := V9.beq_eq (allBelow_spec hc j.val j.2)
    have e2 := congrArg (psi u2 u1 b x) e
    rw [← H.psi_mul C (red0 (aR_red _)) ht, ← H.psi_mul C ht (iotaV_red _), psi_zr,
      psi_iotaV H] at e2
    rw [mul_assoc, inv_mul_eq_iff_eq_mul]
    exact e2
  set Su : Fin 4 → ZMod 5 := fun l => ∑ j, u j * scol j l with hSu
  set Pu : Fin 4 → ZMod 5 := fun i => (∑ j, (-Su) j * col j i) + u i + Su i with hPu
  have hconj : (hz (aG b x) Su)⁻¹ * (psi u2 u1 b x t * hz (aG b x) u) * hz (aG b x) Su =
      psi u2 u1 b x t * hz (aG b x) Pu := by
    have e1 := h4.conj_hz hcol (-Su)
    rw [h4.hz_neg] at e1
    have e : (hz (aG b x) Su)⁻¹ * (psi u2 u1 b x t * hz (aG b x) u) * hz (aG b x) Su =
        psi u2 u1 b x t * ((psi u2 u1 b x t)⁻¹ * (hz (aG b x) Su)⁻¹ * psi u2 u1 b x t) *
          hz (aG b x) u * hz (aG b x) Su := by group
    rw [e, e1, mul_assoc, mul_assoc, ← h4.hz_add, ← h4.hz_add]
    congr 2
    funext i
    simp only [hPu, Pi.add_apply, add_assoc]
  have hval : ∀ i, (Pu i).val < 5 := fun i => ZMod.val_lt _
  set cc := 125 * (Pu 0).val + 25 * (Pu 1).val + 5 * (Pu 2).val + (Pu 3).val with hcc
  have hdg : dg cc = Pu := by
    have v0 := hval 0
    have v1 := hval 1
    have v2 := hval 2
    have v3 := hval 3
    rw [dg_apply]
    funext i
    fin_cases i
    · have e : cc / 125 % 5 = (Pu 0).val := by omega
      simp [e, ZMod.natCast_zmod_val]
    · have e : cc / 25 % 5 = (Pu 1).val := by omega
      simp [e, ZMod.natCast_zmod_val]
    · have e : cc / 5 % 5 = (Pu 2).val := by omega
      simp [e, ZMod.natCast_zmod_val]
    · have e : cc % 5 = (Pu 3).val := by omega
      simp [e, ZMod.natCast_zmod_val]
  refine ⟨hz (aG b x) Su, cc, ?_, ?_, ?_⟩
  · have v0 := hval 0
    have v1 := hval 1
    have v2 := hval 2
    have v3 := hval 3
    omega
  · intro i hi hJ
    have hrow := allBelow_spec hp i hi
    rw [hJ, Bool.false_or] at hrow
    have hz0 : Pu ⟨i, hi⟩ = 0 := by
      have e := pi_ident c0 c1 c2 c3 s0 s1 s2 s3 u ⟨i, hi⟩
      have hzero : ∀ j : Fin 4, ((piE c0 c1 c2 c3 s0 s1 s2 s3 i j.val : ℕ) : ZMod 5) = 0 := by
        intro j
        rw [Nat.eq_of_beq_eq_true (allBelow_spec hrow j.val j.2), Nat.cast_zero]
      simp only [hzero, mul_zero, Finset.sum_const_zero] at e
      simp only [hPu, Pi.neg_apply]
      exact e
    have e : d4 cc i = (dg cc ⟨i, hi⟩).val := by
      rw [dg, ZMod.val_natCast]
      exact (Nat.mod_eq_of_lt (by unfold d4; cases i.beq 0 <;> cases i.beq 1 <;> cases i.beq 2 <;>
        simp only [cond_true, cond_false] <;> exact Nat.mod_lt _ (by norm_num))).symm
    rw [e, hdg, hz0, ZMod.val_zero]
  · rw [hconj, ← H.psi_mul C ht (iotaV_red _), psi_iotaV H, hdg]

@[expose] def Qt (u2 u1 : G) (b : Fin 6 → G) (x : G) (s : G) : Prop :=
  ∃ k < 31, psi u2 u1 b x (dec (nthN repK k)) ^ 5 = 1 ∧ ∃ e : ℕ, 0 < e ∧ e < 5 ∧
    ∃ c : G, c * s * c⁻¹ = psi u2 u1 b x (dec (nthN repK k)) ^ e

theorem Qt_of_conj {s W : G} (h : Qt u2 u1 b x (W * s * W⁻¹)) : Qt u2 u1 b x s := by
  obtain ⟨k, hk, hT, e, he0, he5, c, hc⟩ := h
  refine ⟨k, hk, hT, e, he0, he5, c * W, ?_⟩
  rw [← hc]
  group

theorem Qt_of_pow {s : G} (hs : s ^ 5 = 1) {a : ℕ} (ha2 : 2 ≤ a) (ha5 : a < 5)
    (h : Qt u2 u1 b x (s ^ a)) : Qt u2 u1 b x s := by
  obtain ⟨k, hk, hT, e, he0, he5, c, hc⟩ := h
  refine ⟨k, hk, hT, e * a ^ 3 % 5, ?_, Nat.mod_lt _ (by norm_num), c, ?_⟩
  · interval_cases a <;> interval_cases e <;> norm_num
  · have hs1 : s ^ (a * a ^ 3) = s := by
      rw [pow_mod_five hs]
      have : a * a ^ 3 % 5 = 1 := by interval_cases a <;> norm_num
      rw [this, pow_one]
    calc c * s * c⁻¹ = (c * s ^ a * c⁻¹) ^ (a ^ 3) := by rw [conj_pow, ← pow_mul, hs1]
      _ = _ := by rw [hc, ← pow_mul, ← pow_mod_five hT]

theorem mem_nthN {n : ℕ} : ∀ {l : List ℕ}, n ∈ l → ∃ k < l.length, nthN l k = n
  | [], h => absurd h List.not_mem_nil
  | a :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨k, hk, e⟩ := mem_nthN h
      exact ⟨k + 1, by simp [hk], e⟩

theorem psi_alphaW (H : PcHyp u2 u1 b x) (C : TabChecks) {ws : List ℕ} {c : G}
    (hc : ∀ i < 9, c * psi u2 u1 b x (genV i) * c⁻¹ = psi u2 u1 b x (dec (nthN ws i))) (v : V9) :
    c * psi u2 u1 b x v * c⁻¹ = psi u2 u1 b x (alphaW ws v) := by
  have key : ∀ y, c * y * c⁻¹ = MulAut.conj c y := fun y => by rw [MulAut.conj_apply]
  have f0 := hc 0 (by norm_num)
  have f1 := hc 1 (by norm_num)
  have f8 := hc 8 (by norm_num)
  have fb : ∀ (i : Fin 6) (n : ℕ), n = i.val + 2 →
      MulAut.conj c (b i) = psi u2 u1 b x (dec (nthN ws n)) := by
    intro i n hn
    rw [← key, ← psi_genVb (u2 := u2) (u1 := u1) (b := b) (x := x) i, hn]
    exact hc _ (by omega)
  rw [psi_genV0, key] at f0
  rw [psi_genV1, key] at f1
  rw [psi_genV8, key] at f8
  have fb0 := fb 0 2 rfl
  have fb1 := fb 1 3 rfl
  have fb2 := fb 2 4 rfl
  have fb3 := fb 3 5 rfl
  have fb4 := fb 4 6 rfl
  have fb5 := fb 5 7 rfl
  have hv : psi u2 u1 b x v = u2 ^ v.e0 * u1 ^ v.e1 * (b 0 ^ v.r.a0 * b 1 ^ v.r.a1 *
      b 2 ^ v.r.a2 * b 3 ^ v.r.a3 * b 4 ^ v.r.a4 * b 5 ^ v.r.a5 * x ^ v.r.c) := rfl
  rw [key, hv]
  simp only [map_mul, map_pow, f0, f1, f8, fb0, fb1, fb2, fb3, fb4, fb5]
  unfold alphaW
  simp only [← H.psi_mul C (mulV_red _ _) (powV_red _ _), ← H.psi_mul C (powV_red _ _) (powV_red _ _),
    ← H.psi_pow C (dec_red _)]
  simp only [mul_assoc]

theorem stepW_spec {rep depth : List ℕ} {nc c c' w : ℕ} {v' : V9}
    (h : stepW rep depth nc c c' w v' = true) :
    c' < nc ∧ nthN depth c' < nthN depth c ∧
      mulV (dec w) v' = mulV (dec (nthN rep c')) (dec w) := by
  unfold stepW at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1, h.1.2, V9.beq_eq h.2⟩

theorem route_good (H : PcHyp u2 u1 b x) (C : TabChecks) {rep depth kind arg cls wit : List ℕ}
    {nc : ℕ} (hf : ∀ c < nc, classW rep depth kind arg cls wit nc c = true)
    (hN : ∀ j < 3, ∃ c : G, ∀ i < 9,
      c * psi u2 u1 b x (genV i) * c⁻¹ = psi u2 u1 b x (dec (nthN (autW j) i))) :
    ∀ c < nc, psi u2 u1 b x (dec (nthN rep c)) ^ 5 = 1 → Qt u2 u1 b x (psi u2 u1 b x (dec (nthN rep c))) := by
  suffices Hn : ∀ n, ∀ c < nc, nthN depth c = n → psi u2 u1 b x (dec (nthN rep c)) ^ 5 = 1 →
      Qt u2 u1 b x (psi u2 u1 b x (dec (nthN rep c))) from fun c hc => Hn _ c hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hn h5
    have step : ∀ {c' w : ℕ} {v' : V9}, v'.red → stepW rep depth nc c c' w v' = true →
        psi u2 u1 b x v' ^ 5 = 1 → Qt u2 u1 b x (psi u2 u1 b x v') := by
      intro c' w v' hv' hs hv5
      obtain ⟨h1, h2, h3⟩ := stepW_spec hs
      have e := congrArg (psi u2 u1 b x) h3
      rw [← H.psi_mul C (dec_red _) hv', ← H.psi_mul C (dec_red _) (dec_red _)] at e
      have e' : psi u2 u1 b x (dec (nthN rep c')) =
          psi u2 u1 b x (dec w) * psi u2 u1 b x v' * (psi u2 u1 b x (dec w))⁻¹ := by
        rw [e]
        group
      have h5' : psi u2 u1 b x (dec (nthN rep c')) ^ 5 = 1 := by
        rw [e', conj_pow, hv5]
        group
      have q := ih _ (hn ▸ h2) c' h1 rfl h5'
      rw [e'] at q
      exact Qt_of_conj q
    have hcl := hf c hc
    unfold classW at hcl
    by_cases k0 : (nthN kind c).beq 0 = true
    · simp only [k0, cond_true] at hcl
      obtain ⟨k, hk, e⟩ := mem_nthN (memK_spec hcl)
      have hk31 : k < 31 := by simpa [repK] using hk
      refine ⟨k, hk31, by rw [e]; exact h5, 1, by norm_num, by norm_num, 1, ?_⟩
      rw [e]
      group
    by_cases k1 : (nthN kind c).beq 1 = true
    · simp only [k0, k1, cond_true, cond_false, Bool.false_eq_true, Bool.and_eq_true,
        Nat.blt_eq] at hcl
      obtain ⟨ha, hs⟩ := hcl
      obtain ⟨cN, hcN⟩ := hN _ ha
      have e := psi_alphaW H C hcN (dec (nthN rep c))
      have hv5 : psi u2 u1 b x (alphaW (autW (nthN arg c)) (dec (nthN rep c))) ^ 5 = 1 := by
        rw [← e, conj_pow, h5]
        group
      have q := step (by unfold alphaW; exact mulV_red _ _) hs hv5
      rw [← e] at q
      exact Qt_of_conj q
    · simp only [Bool.not_eq_true] at k0 k1
      simp only [k0, k1, cond_false, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq] at hcl
      obtain ⟨⟨⟨h2, h5a⟩, -⟩, hs⟩ := hcl
      have e := H.psi_pow C (dec_red (nthN rep c)) (nthN arg c)
      have hv5 : psi u2 u1 b x (powV (dec (nthN rep c)) (nthN arg c)) ^ 5 = 1 := by
        rw [← e, ← pow_mul, mul_comm, pow_mul, h5, one_pow]
      have q := step (powV_red _ _) hs hv5
      rw [← e] at q
      exact Qt_of_pow h5 h2 h5a q

theorem census_conj [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) (hs : sigOK () = true)
    (hx : x ≠ 1) {nrm rcs rep depth kind arg cls wit : List ℕ} {nc : ℕ} (hA : aOK nrm = true)
    (hcos : ∀ k < 3125, ∃ d, cosOK rcs k d = true) (hrep : ∀ ρ < 245, RepGood rcs rep nc ρ)
    (hf : ∀ c < nc, classW rep depth kind arg cls wit nc c = true)
    (hN : ∀ j < 3, ∃ c : G, ∀ i < 9,
      c * psi u2 u1 b x (genV i) * c⁻¹ = psi u2 u1 b x (dec (nthN (autW j) i)))
    {m : ℕ} (hcard : Nat.card G = 5 ^ 9 * m) (hm : ¬ 5 ∣ m) :
    ∀ s : G, orderOf s = 5 → Qt u2 u1 b x s := by
  intro s hs5
  have h4 := comm4_of_aOK H hA
  have hsp : s ^ 5 = 1 := by rw [← hs5]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs5
    norm_num at hs5
  obtain ⟨g, hg⟩ :=
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow.exists_conj_into_range (by norm_num)
      (PSub u2 u1 b).subtype Subtype.val_injective (card_P H C hs hx) hcard hm hs5
  rw [range_subtype] at hg
  obtain ⟨i, -, hie⟩ := mem_P_psi H C hg
  obtain ⟨k, hk, w, hkw⟩ := cover_coset H hx h4 (dec_red i)
  obtain ⟨d, hd⟩ := hcos k hk
  have ecos : psi u2 u1 b x (dec (d / 153125)) * psi u2 u1 b x (cosT k) =
      psi u2 u1 b x (cosT (nthN rcs (d / 625 % 245))) * hz (aG b x) (dg (d % 625)) *
        psi u2 u1 b x (dec (d / 153125)) := by
    have e := congrArg (psi u2 u1 b x) (V9.beq_eq hd)
    rw [← H.psi_mul C (dec_red _) (cosT_red _), ← H.psi_mul C (mulV_red _ _) (dec_red _),
      ← H.psi_mul C (cosT_red _) (iotaV_red _), psi_iotaV H] at e
    exact e
  obtain ⟨w', hw'⟩ := normBy_psi H C hA (dec (d / 153125)) w
  have e1 : psi u2 u1 b x (dec (d / 153125)) * (g⁻¹ * s * g) * (psi u2 u1 b x (dec (d / 153125)))⁻¹ =
      psi u2 u1 b x (cosT (nthN rcs (d / 625 % 245))) * hz (aG b x) (dg (d % 625) + w') := by
    rw [← hie, hkw, h4.hz_add, ← hw']
    calc psi u2 u1 b x (dec (d / 153125)) * (psi u2 u1 b x (cosT k) * hz (aG b x) w) *
          (psi u2 u1 b x (dec (d / 153125)))⁻¹ =
        psi u2 u1 b x (dec (d / 153125)) * psi u2 u1 b x (cosT k) *
          (hz (aG b x) w * (psi u2 u1 b x (dec (d / 153125)))⁻¹) := by group
      _ = _ := by rw [ecos]; group
  obtain ⟨c0, c1, c2, c3, s0, s1, s2, s3, mm, ds, hcol, hpi, -, hpts⟩ :=
    hrep _ (Nat.mod_lt _ (by norm_num))
  obtain ⟨E, cc, hcc, hsupp, hE⟩ := rep_step H C h4 (cosT_red _) hcol hpi (dg (d % 625) + w')
  obtain ⟨j, hj, hjv⟩ := exists_ptVec mm hcc hsupp
  have hpt := hpts j hj
  rw [hjv] at hpt
  generalize cosT (nthN rcs (d / 625 % 245)) = t at hE hpt e1
  generalize hZd : E⁻¹ * psi u2 u1 b x (dec (d / 153125)) * g⁻¹ = Z
  have hZ : Z * s * Z⁻¹ = psi u2 u1 b x (mulV t (iotaV cc)) := by
    rw [← hE, ← e1, ← hZd]
    group
  have hZ5 : psi u2 u1 b x (mulV t (iotaV cc)) ^ 5 = 1 := by
    rw [← hZ, conj_pow, hsp]
    group
  have hZ1 : psi u2 u1 b x (mulV t (iotaV cc)) ≠ 1 := by
    rw [← hZ]
    intro h
    apply hs1
    have e : s = Z⁻¹ * (Z * s * Z⁻¹) * Z := by group
    rw [e, h]
    group
  unfold ptOK at hpt
  by_cases hd0 : (nthN ds j).beq 0 = true
  · exfalso
    simp only [hd0, cond_true, Bool.or_eq_true, Bool.not_eq_true'] at hpt
    rcases hpt with h1 | h1
    · apply hZ1
      rw [V9.beq_eq h1, psi_one]
    · have e := H.psi_pow C (mulV_red t (iotaV cc)) 5
      rw [hZ5] at e
      have e2 := psi_eq_one H C hs hx (powV_red _ _) e.symm
      unfold ord5 V9.isOne at h1
      rw [e2] at h1
      exact absurd h1 (by decide)
  · simp only [Bool.not_eq_true] at hd0
    simp only [hd0, cond_false, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hpt
    obtain ⟨⟨-, hl⟩, he⟩ := hpt
    have e := congrArg (psi u2 u1 b x) (V9.beq_eq he)
    rw [← H.psi_mul C (dec_red _) (mulV_red _ _), ← H.psi_mul C (dec_red _) (dec_red _)] at e
    generalize psi u2 u1 b x (dec (nthN ds j / 1024)) = W at e
    have e' : psi u2 u1 b x (dec (nthN rep (nthN ds j % 1024 - 1))) =
        (W * Z) * s * (W * Z)⁻¹ := by
      have e3 : W * Z * s * (W * Z)⁻¹ = W * (Z * s * Z⁻¹) * W⁻¹ := by group
      rw [e3, hZ, e]
      group
    have h5 : psi u2 u1 b x (dec (nthN rep (nthN ds j % 1024 - 1))) ^ 5 = 1 := by
      rw [e', conj_pow, hsp]
      group
    have q := route_good H C hf hN _ hl h5
    rw [e'] at q
    exact Qt_of_conj q

end CFSG.KC.MonPcFive

end

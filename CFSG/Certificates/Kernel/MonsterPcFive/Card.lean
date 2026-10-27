module

public import CFSG.Certificates.Kernel.MonsterPcFive.Coll
public import CFSG.Certificates.Kernel.BabyMonster.PcFive.Cover

public section

namespace CFSG.KC.MonPcFive

open CFSG.Monster.B.Pinned Subgroup
open CFSG.KC.BM.PcFive (bcomm_of_swap bcomm_of_swap' pow_mod_five)

@[expose] def Mz : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![0, 3, 0, 0, 0, 0; 2, 0, 4, 0, 2, 2; 0, 1, 0, 0, 1, 2; 0, 0, 0, 0, 0, 3; 0, 3, 4, 0, 0, 0;
    0, 3, 3, 2, 0, 0]

@[expose] def MzInv : Matrix (Fin 6) (Fin 6) (ZMod 5) :=
  !![0, 3, 4, 2, 2, 0; 2, 0, 0, 0, 0, 0; 1, 0, 0, 0, 4, 0; 3, 0, 0, 0, 4, 3; 3, 0, 1, 1, 0, 0;
    0, 0, 0, 2, 0, 0]

theorem Mz_mul_inv : Mz * MzInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

theorem isUnit_det_Mz : IsUnit Mz.det := by
  have h := congrArg Matrix.det Mz_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem Mz_upper : ∀ i j : Fin 6, i < j → (Mz i j).val = (5 - cmAt cmM i j) % 5 := by decide

theorem Mz_lower : ∀ i j : Fin 6, j < i → (Mz i j).val = cmAt cmM j i := by decide

theorem Mz_diag : ∀ i : Fin 6, (Mz i i).val = 0 := by decide

theorem cm_le : ∀ i j : Fin 6, cmAt cmM i j ≤ 5 := by decide

variable {G : Type*} [Group G] {b : Fin 6 → G} {x : G}

theorem RRel.bcomm_eq (h : RRel cmM b x) : ∀ i j, bcomm (b i) (b j) = x ^ (Mz i j).val := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · have e := bcomm_of_swap' (n := 5 - cmAt cmM i j) h.x5 (h.sw i j hij) (by have := cm_le i j; omega)
    rw [e, Mz_upper i j hij, ← pow_mod_five h.x5]
  · rw [Mz_diag, pow_zero, bcomm_eq_one_iff]
  · rw [bcomm_of_swap (h.sw j i hji), Mz_lower i j hji]

theorem RRel.mem_x (h : RRel cmM b x) : x ∈ closure (Set.range b) := by
  have e := h.bcomm_eq 2 1
  have e1 : (Mz 2 1).val = 1 := rfl
  rw [e1, pow_one] at e
  rw [← e]
  unfold bcomm
  have m : ∀ i, b i ∈ closure (Set.range b) := fun i => subset_closure ⟨i, rfl⟩
  exact mul_mem (mul_mem (mul_mem (inv_mem (m 2)) (inv_mem (m 1))) (m 2)) (m 1)

theorem RRel.commData (h : RRel cmM b x) (hx : x ≠ 1) : CommData 5 b x Mz where
  pow_q := h.b5
  orderOf_z := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact orderOf_eq_prime h.x5 hx
  comm_z i := (h.xc i).symm
  bcomm_q := h.bcomm_eq
  isUnit_det := isUnit_det_Mz
  mem_z := h.mem_x

theorem RRel.card_R [Finite G] (h : RRel cmM b x) (hx : x ≠ 1) :
    Nat.card (closure (Set.range b)) = 5 ^ 7 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [(h.commData hx).card_eq]

theorem nfR_mem (h : RRel cmM b x) (a : RV) : nfR b x a ∈ closure (Set.range b) := by
  have m : ∀ i, b i ∈ closure (Set.range b) := fun i => subset_closure ⟨i, rfl⟩
  unfold nfR
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (pow_mem (m 0) _)
    (pow_mem (m 1) _)) (pow_mem (m 2) _)) (pow_mem (m 3) _)) (pow_mem (m 4) _))
    (pow_mem (m 5) _)) (pow_mem h.mem_x _)

@[expose] def RV.digs (a : RV) : Fin 6 → ℕ := ![a.a0, a.a1, a.a2, a.a3, a.a4, a.a5]

theorem nfR_eq_prod {a : RV} (ha : a.red) :
    nfR b x a = (List.ofFn fun l => b l ^ ((a.digs l : ℕ) : ZMod 5).val).prod * x ^ a.c := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  have e : (List.ofFn fun l => b l ^ ((a.digs l : ℕ) : ZMod 5).val) =
      [b 0 ^ a.a0, b 1 ^ a.a1, b 2 ^ a.a2, b 3 ^ a.a3, b 4 ^ a.a4, b 5 ^ a.a5] := by
    simp [List.ofFn_succ, RV.digs, ZMod.val_natCast, Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt h5]
  rw [e]
  simp only [List.prod_cons, List.prod_nil, mul_one, nfR, mul_assoc]

theorem coord_nfR (h : RRel cmM b x) (hx : x ≠ 1) {a : RV} (ha : a.red) :
    coord 5 b x Mz (nfR b x a) = fun l => ((a.digs l : ℕ) : ZMod 5) := by
  rw [nfR_eq_prod ha]
  have : NeZero 5 := ⟨by norm_num⟩
  exact (h.commData hx).coord_prod _ _

theorem unitR_red (k : ℕ) : (unitR k).red := by
  have c : ∀ t : Bool, (bif t then 1 else 0) < 5 := by decide
  exact ⟨c _, c _, c _, c _, c _, c _, by norm_num [unitR]⟩

theorem actRow_red (i j k : ℕ) : (actRow i j k).red :=
  phi1At_red _ (phi2At_red _ (unitR_red k))

variable {u2 u1 : G}

theorem PcHyp.conj_U (H : PcHyp u2 u1 b x) (C : TabChecks) {i j : ℕ} (hi : i < 5) (hj : j < 5)
    (k : Fin 6) : (u2 ^ i * u1 ^ j)⁻¹ * b k * (u2 ^ i * u1 ^ j) = nfR b x (actRow i j k.val) := by
  have e : (u2 ^ i * u1 ^ j)⁻¹ * b k * (u2 ^ i * u1 ^ j) =
      (u1 ^ j)⁻¹ * ((u2 ^ i)⁻¹ * nfR b x (unitR k.val) * u2 ^ i) * u1 ^ j := by
    rw [nfR_unitR]
    group
  rw [e, H.conj2 C hi (unitR_red _), H.conj1 C hj (phi2At_red _ (unitR_red _))]
  rfl

theorem encA_congr {a a' : RV} (h : ∀ l, a.digs l = a'.digs l) : encA a = encA a' := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp only [RV.digs, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    at h0 h1 h2 h3 h4 h5
  unfold encA
  rw [h0, h1, h2, h3, h4, h5]

theorem digs_lt {a : RV} (ha : a.red) (l : Fin 6) : a.digs l < 5 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, -⟩ := ha
  fin_cases l <;> simpa [RV.digs]

theorem PcHyp.coset_eq (H : PcHyp u2 u1 b x) (C : TabChecks) (hx : x ≠ 1) (hs : sigOK () = true)
    {i j i' j' : ℕ} (hi : i < 5) (hj : j < 5) (hi' : i' < 5) (hj' : j' < 5) {r r' : G}
    (hr : r ∈ closure (Set.range b)) (hr' : r' ∈ closure (Set.range b))
    (he : u2 ^ i * u1 ^ j * r = u2 ^ i' * u1 ^ j' * r') : i = i' ∧ j = j' := by
  have D := H.rel.commData hx
  have : NeZero 5 := ⟨by norm_num⟩
  set U := u2 ^ i * u1 ^ j
  set U' := u2 ^ i' * u1 ^ j'
  have hU : U' = U * (r * r'⁻¹) := by
    rw [← mul_assoc, he]
    group
  have hrr : r * r'⁻¹ ∈ closure (Set.range b) := mul_mem hr (inv_mem hr')
  have hrow : ∀ k < 6, ∀ l, (actRow i j k).digs l = (actRow i' j' k).digs l := by
    intro k hk l
    have c1 := H.conj_U C hi hj ⟨k, hk⟩
    have c2 := H.conj_U C hi' hj' ⟨k, hk⟩
    have e : U'⁻¹ * b ⟨k, hk⟩ * U' =
        (r * r'⁻¹)⁻¹ * (U⁻¹ * b ⟨k, hk⟩ * U) * (r * r'⁻¹) := by
      rw [hU]
      group
    have hc := D.coord_conj_of_mem hrr (c1 ▸ nfR_mem H.rel _)
    rw [← e, c2, c1, coord_nfR H.rel hx (actRow_red _ _ _),
      coord_nfR H.rel hx (actRow_red _ _ _)] at hc
    have hl := congrFun hc l
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (digs_lt (actRow_red _ _ _) l),
      Nat.mod_eq_of_lt (digs_lt (actRow_red _ _ _) l)] at hl
    exact hl.symm
  have hsig : sig i j = sig i' j' := by
    unfold sig
    rw [encA_congr (hrow 0 (by norm_num)), encA_congr (hrow 1 (by norm_num)),
      encA_congr (hrow 2 (by norm_num)), encA_congr (hrow 3 (by norm_num)),
      encA_congr (hrow 4 (by norm_num)), encA_congr (hrow 5 (by norm_num))]
  have hp : 5 * i + j = 5 * i' + j' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have := allBelow_spec (allBelow_spec hs (5 * i' + j') (by omega)) (5 * i + j) hlt
      have e1 : (5 * i' + j') / 5 = i' := by omega
      have e2 : (5 * i' + j') % 5 = j' := by omega
      have e3 : (5 * i + j) / 5 = i := by omega
      have e4 : (5 * i + j) % 5 = j := by omega
      rw [e1, e2, e3, e4, hsig, Nat.beq_refl] at this
      exact absurd this (by decide)
    · have := allBelow_spec (allBelow_spec hs (5 * i + j) (by omega)) (5 * i' + j') hlt
      have e1 : (5 * i' + j') / 5 = i' := by omega
      have e2 : (5 * i' + j') % 5 = j' := by omega
      have e3 : (5 * i + j) / 5 = i := by omega
      have e4 : (5 * i + j) % 5 = j := by omega
      rw [e1, e2, e3, e4, hsig, Nat.beq_refl] at this
      exact absurd this (by decide)
  omega

@[expose] def PSub (u2 u1 : G) (b : Fin 6 → G) : Subgroup G :=
  closure (insert u2 (insert u1 (Set.range b)))

@[expose] def encR (a : RV) : ℕ :=
  15625 * a.a0 + 3125 * a.a1 + 625 * a.a2 + 125 * a.a3 + 25 * a.a4 + 5 * a.a5 + a.c

@[expose] def enc (v : V9) : ℕ := 390625 * v.e0 + 78125 * v.e1 + encR v.r

theorem dec_enc {v : V9} (h : v.red) : dec (enc v) = v := by
  obtain ⟨he0, he1, h0, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨e0, e1, ⟨a0, a1, a2, a3, a4, a5, c⟩⟩ := v
  simp only at he0 he1 h0 h1 h2 h3 h4 h5 h6
  unfold dec enc encR decR
  simp only [V9.mk.injEq, RV.mk.injEq]
  omega

theorem enc_lt {v : V9} (h : v.red) : enc v < 1953125 := by
  obtain ⟨he0, he1, h0, h1, h2, h3, h4, h5, h6⟩ := h
  unfold enc encR
  omega

theorem psi_mem_P (H : PcHyp u2 u1 b x) (v : V9) : psi u2 u1 b x v ∈ PSub u2 u1 b := by
  have hR : closure (Set.range b) ≤ PSub u2 u1 b :=
    closure_mono (fun _ hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy))
  unfold psi
  exact mul_mem (mul_mem (pow_mem (subset_closure (Set.mem_insert _ _)) _)
    (pow_mem (subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) _))
    (hR (nfR_mem H.rel _))

@[expose] def TSub [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) : Subgroup G where
  carrier := {g | ∃ i < 1953125, psi u2 u1 b x (dec i) = g}
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    refine ⟨enc (mulV (dec i) (dec j)), enc_lt (mulV_red _ _), ?_⟩
    rw [dec_enc (mulV_red _ _), H.psi_mul C (dec_red _) (dec_red _)]
  one_mem' := ⟨0, by norm_num, by simp [psi, nfR, dec, decR]⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨enc (powV (dec i) (Nat.card G - 1)), enc_lt (powV_red _ _), ?_⟩
    rw [dec_enc (powV_red _ _), ← H.psi_pow C (dec_red _)]
    have hc : 0 < Nat.card G := Nat.card_pos
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hc, pow_card_eq_one']

theorem gens_mem_T [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) :
    PSub u2 u1 b ≤ TSub H C := by
  unfold PSub
  rw [closure_le]
  rintro g (rfl | rfl | ⟨i, rfl⟩)
  · exact ⟨390625, by norm_num, by simp [psi, nfR, dec, decR]⟩
  · exact ⟨78125, by norm_num, by simp [psi, nfR, dec, decR]⟩
  · fin_cases i <;> simp only [Fin.isValue]
    · exact ⟨15625, by norm_num, by simp [psi, nfR, dec, decR]⟩
    · exact ⟨3125, by norm_num, by simp [psi, nfR, dec, decR]⟩
    · exact ⟨625, by norm_num, by simp [psi, nfR, dec, decR]⟩
    · exact ⟨125, by norm_num, by simp [psi, nfR, dec, decR]⟩
    · exact ⟨25, by norm_num, by simp [psi, nfR, dec, decR]⟩
    · exact ⟨5, by norm_num, by simp [psi, nfR, dec, decR]⟩

theorem card_P [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) (hs : sigOK () = true)
    (hx : x ≠ 1) : Nat.card (PSub u2 u1 b) = 5 ^ 9 := by
  have hR : closure (Set.range b) ≤ PSub u2 u1 b :=
    closure_mono (fun _ hy => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hy))
  have m2 : u2 ∈ PSub u2 u1 b := subset_closure (Set.mem_insert _ _)
  have m1 : u1 ∈ PSub u2 u1 b := subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  apply le_antisymm
  · let f : Fin 1953125 → PSub u2 u1 b := fun k => ⟨psi u2 u1 b x (dec k.val), psi_mem_P H _⟩
    have hs' : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨k, hk, rfl⟩ := gens_mem_T H C hg
      exact ⟨⟨k, hk⟩, rfl⟩
    have := Nat.card_le_card_of_surjective f hs'
    rw [Nat.card_fin] at this
    norm_num
    exact this
  · let f : Fin 5 × Fin 5 × closure (Set.range b) → PSub u2 u1 b := fun t =>
      ⟨u2 ^ t.1.val * u1 ^ t.2.1.val * t.2.2, mul_mem (mul_mem (pow_mem m2 _) (pow_mem m1 _))
        (hR t.2.2.2)⟩
    have hf : Function.Injective f := by
      rintro ⟨i, j, r⟩ ⟨i', j', r'⟩ h
      have h' : u2 ^ i.val * u1 ^ j.val * r.val = u2 ^ i'.val * u1 ^ j'.val * r'.val :=
        congrArg Subtype.val h
      obtain ⟨e1, e2⟩ := H.coset_eq C hx hs i.2 j.2 i'.2 j'.2 r.2 r'.2 h'
      have ei : i = i' := Fin.ext e1
      have ej : j = j' := Fin.ext e2
      subst ei ej
      have : r = r' := Subtype.ext (mul_left_cancel h')
      rw [this]
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod, Nat.card_prod, Nat.card_fin, H.rel.card_R hx] at this
    norm_num at this ⊢
    exact this

theorem psi_dec_inj [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) (hs : sigOK () = true)
    (hx : x ≠ 1) {i j : ℕ} (hi : i < 1953125) (hj : j < 1953125)
    (h : psi u2 u1 b x (dec i) = psi u2 u1 b x (dec j)) : i = j := by
  let f : Fin 1953125 → PSub u2 u1 b := fun k => ⟨psi u2 u1 b x (dec k.val), psi_mem_P H _⟩
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := gens_mem_T H C hg
    exact ⟨⟨k, hk⟩, rfl⟩
  have hb := hsurj.bijective_of_nat_card_le (by rw [card_P H C hs hx, Nat.card_fin]; norm_num)
  have := hb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) (Subtype.ext h)
  exact congrArg Fin.val this

theorem mem_P_psi [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) {g : G}
    (hg : g ∈ PSub u2 u1 b) : ∃ i < 1953125, psi u2 u1 b x (dec i) = g := gens_mem_T H C hg

theorem psi_eq_one [Finite G] (H : PcHyp u2 u1 b x) (C : TabChecks) (hs : sigOK () = true)
    (hx : x ≠ 1) {v : V9} (hv : v.red) (h : psi u2 u1 b x v = 1) : v = V9.one := by
  have e0 : psi u2 u1 b x (dec 0) = 1 := by simp [psi, nfR, dec, decR]
  have := psi_dec_inj H C hs hx (j := 0) (enc_lt hv) (by norm_num) (by rw [dec_enc hv, h, e0])
  rw [← dec_enc hv, this]
  rfl

end CFSG.KC.MonPcFive

end

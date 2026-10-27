module

public import Certificates.Data.Kernel.FzFus.Codes
public import CFSG.Certificates.Kernel.FzJt.Sound

public section

namespace Certificates.FzFus.K

open Certificates.FzJ36 Certificates.FzFus Certificates.FzJt.K

theorem mem_filterN {n : Nat} {p : Nat → Bool} {x : Nat} :
    x ∈ filterN n p ↔ x < n ∧ p x = true := by
  induction n with
  | zero => simp [filterN]
  | succ n ih =>
    have h : filterN (n + 1) p = Bool.rec (filterN n p) (n :: filterN n p) (p n) := rfl
    rw [h]
    cases hp : p n
    · simp only [ih]
      constructor
      · exact fun h => ⟨by omega, h.2⟩
      · rintro ⟨h1, h2⟩
        have : x ≠ n := by
          rintro rfl
          rw [hp] at h2
          exact Bool.false_ne_true h2
        exact ⟨by omega, h2⟩
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | h)
        · exact ⟨by omega, hp⟩
        · exact ⟨by omega, h.2⟩
      · rintro ⟨h1, h2⟩
        by_cases hx : x = n
        · exact Or.inl hx
        · exact Or.inr ⟨by omega, h2⟩

theorem allN_iff {n : Nat} {f : Nat → Bool} : allN n f = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allN]
  | succ n ih =>
    have h : allN (n + 1) f = bA (f n) (allN n f) := rfl
    rw [h, bA_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      by_cases hin : i = n
      · exact hin ▸ h1
      · exact h2 i (by omega)
    · intro h
      exact ⟨h n (by omega), fun i hi => h i (by omega)⟩

theorem mem_hiL {x : Nat} {L : List Nat} : x ∈ hiL L ↔ ∃ y ∈ L, Nat.shiftRight y 10 = x := by
  induction L with
  | nil => simp [hiL]
  | cons y ys ih =>
    have h : hiL (y :: ys) = Nat.shiftRight y 10 :: hiL ys := rfl
    rw [h, List.mem_cons, ih, ← or_ex_cons (p := fun y => Nat.shiftRight y 10 = x)]
    exact or_congr eq_comm Iff.rfl

theorem mulR_rawc (g h : Model) : mulR (rawc g) (rawc h) = rawc (g * h) := by
  obtain ⟨-, a1, a2, a3, a4, -⟩ := rawc_lanes g
  obtain ⟨-, b1, b2, b3, b4, -⟩ := rawc_lanes h
  unfold mulR mul5R
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  obtain ⟨⟨q1, q2, q3⟩, e⟩ := g
  rcases zmod2' e with rfl | rfl
  · rw [mul_one_left]
    unfold mul8R rawc
    simp only
    rw [ec_one, sw_zero, sw_zero, qm_qc, qm_qc, qm_qc]
    exact congrArg (fun t => mk _ _ _ t) (Nat.zero_xor _)
  · rw [mul_swap_left]
    unfold mul8R rawc
    simp only
    rw [ec_mul, ec_swap, sw_one, sw_one, qm_qc, qm_qc, qm_qc]

theorem keq_iff_nz {g h : Model} : KEq g h ↔ nz (rawc g) = nz (rawc h) :=
  code_eq_iff.symm

theorem dec_rawc (g : Model) : dec (rawc g) = g :=
  rawc_inj (rawc_dec (rawc_lt g))

theorem isInvR_rawc {m : Model} : isInvR (rawc m) = true ↔ IsInvM m := by
  have h1 : nz (rawc (m * m)) = 0 ↔ KEq (m * m) 1 := code_eq_zero
  have h2 : nz (rawc m) = 0 ↔ KEq m 1 := code_eq_zero
  rw [isInvR, bA_iff, bN_iff, Bool.eq_false_iff, Ne, beq_iff, beq_iff, mulR_rawc, IsInvM, h1, h2]

theorem clsF : ∀ x y z : Fin 8, ∀ e : Fin 2,
    clsN (mk x y z e) = clsIdx (clsOf (dec (mk x y z e))) := by
  decide +kernel

theorem clsN_rawc (g : Model) : clsN (rawc g) = clsIdx (clsOf g) := by
  have h := clsF ⟨_, qc_lt g.left.1⟩ ⟨_, qc_lt g.left.2.1⟩ ⟨_, qc_lt g.left.2.2⟩ ⟨_, ec_lt g.right⟩
  change clsN (rawc g) = clsIdx (clsOf (dec (rawc g))) at h
  rwa [dec_rawc] at h

def idxCls (k : Nat) : Cls :=
  match k with
  | 0 => .III | 1 => .IIJ | 2 => .IIK | 3 => .JJI | 4 => .JJJ | 5 => .JJK | 6 => .KKI
  | 7 => .KKJ | 8 => .KKK | 9 => .IJI | 10 => .IJJ | 11 => .IJK | 12 => .IKI | 13 => .IKJ
  | 14 => .IKK | 15 => .JKI | 16 => .JKJ | 17 => .JKK | 18 => .oI | 19 => .oJ | 20 => .oK
  | 21 => .lam | 22 => .z12 | _ => .z3

theorem idxCls_clsIdx (C : Cls) : idxCls (clsIdx C) = C := by
  cases C <;> rfl

theorem clsIdx_inj {C D : Cls} (h : clsIdx C = clsIdx D) : C = D := by
  rw [← idxCls_clsIdx C, h, idxCls_clsIdx]

theorem clsIdx_lt (C : Cls) : clsIdx C < 24 := by
  cases C <;> decide

theorem repR_clsIdx (C : Cls) : repR (clsIdx C) = rawc (rep C) := by
  cases C <;> decide +kernel

theorem dec_lt {c : Nat} (hc : c < 1024) : rawc (dec c) = c := rawc_dec hc

theorem land_1023_lt (x : Nat) : Nat.land x 1023 < 1024 := by
  have : Nat.land x 1023 ≤ 1023 := Nat.and_le_right
  omega

theorem keq_conj_of {G m R : Model} (h : KEq (G * m) (R * G)) : KEq (G * m * G⁻¹) R := by
  have h' := KEq.mul h (KEq.refl G⁻¹)
  simpa [mul_assoc] using h'

theorem classB_sound {W : List Nat} (h : classB W = true) : ClassFact := by
  intro m hm
  rw [classB, bA_iff, eqL_iff, allL_iff] at h
  obtain ⟨hL, hW⟩ := h
  have hc : rawc m ∈ lowL W := by
    rw [← hL, mem_filterN]
    exact ⟨rawc_lt m, isInvR_rawc.mpr hm⟩
  obtain ⟨x, hx, hxc⟩ := mem_lowL.mp hc
  have hk := hW x hx
  rw [conjOK, bA_iff, beq_iff, hxc] at hk
  obtain ⟨hg, hk⟩ := hk
  have hg : Nat.shiftRight x 10 < 1024 := by simpa using hg
  refine ⟨dec (Nat.shiftRight x 10), keq_conj_of (keq_iff_nz.mpr ?_)⟩
  rw [← mulR_rawc, ← mulR_rawc, dec_lt hg, ← repR_clsIdx, ← clsN_rawc]
  exact hk

theorem shift_land (T : Nat) :
    Nat.land T 31 = T % 32 ∧ Nat.land (Nat.shiftRight T 5) 31 = T / 32 % 32 ∧
      Nat.shiftRight T 10 = T / 1024 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.and_two_pow_sub_one_eq_mod T 5
  · change (T >>> 5) &&& (2 ^ 5 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  · change T >>> 10 = _
    rw [Nat.shiftRight_eq_div_pow]

theorem rowsB_sound {W : List Nat} (h : rowsB rowsT W = true) : RowsFact := by
  intro r hr
  rw [rowsB, bA_iff, eqL_iff, allL_iff] at h
  obtain ⟨hT, hW⟩ := h
  have hrT : clsIdx r.1 + 32 * clsIdx r.2.1 + 1024 * clsIdx r.2.2 ∈ hiL W := by
    rw [hT, rowsT]
    exact List.mem_map_of_mem hr
  obtain ⟨x, hx, hxT⟩ := mem_hiL.mp hrT
  have hk := hW x hx
  have he := clsIdx_lt r.1
  have hu := clsIdx_lt r.2.1
  have hv := clsIdx_lt r.2.2
  obtain ⟨s1, s2, s3⟩ := shift_land (Nat.shiftRight x 10)
  have hx15 : Nat.shiftRight x 15 = Nat.shiftRight (Nat.shiftRight x 10) 5 :=
    Nat.shiftRight_add x 10 5
  have hx20 : Nat.shiftRight x 20 = Nat.shiftRight (Nat.shiftRight x 10) 10 :=
    Nat.shiftRight_add x 10 10
  have e1 : Nat.land (Nat.shiftRight x 10) 31 = clsIdx r.1 := by
    rw [s1, hxT]
    omega
  have e2 : Nat.land (Nat.shiftRight x 15) 31 = clsIdx r.2.1 := by
    rw [hx15, s2, hxT]
    omega
  have e3 : Nat.shiftRight x 20 = clsIdx r.2.2 := by
    rw [hx20, s3, hxT]
    omega
  rw [rowOK, e1, e2, e3, repR_clsIdx] at hk
  simp only [bA_iff, bN_iff, beq_iff] at hk
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk
  have hw := dec_lt (land_1023_lt x)
  refine ⟨dec (Nat.land x 1023), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [keq_iff_nz, ← mulR_rawc, ← mulR_rawc, hw]
    exact h1
  · rw [← isInvR_rawc, hw]
    exact h2
  · rw [keq_iff_nz, hw]
    intro hc
    rw [hc] at h3
    simp at h3
  · rw [← isInvR_rawc, ← mulR_rawc, hw]
    exact h4
  · apply clsIdx_inj
    rw [← clsN_rawc, hw]
    exact h5
  · apply clsIdx_inj
    rw [← clsN_rawc, ← mulR_rawc, hw]
    exact h6

theorem chi_code : ∀ (n : Fin 4) (q : Q8),
    chi n q = Multiplicative.ofAdd ((chiN n.val (qc q) : Nat) : ZMod 2) := by
  decide +kernel

theorem chiN_lt (n x : Nat) : chiN n x < 2 := by
  have : chiN n x ≤ 1 := Nat.and_le_right
  omega

theorem ofAdd3 : ∀ x y z : Fin 2,
    (Multiplicative.ofAdd ((x.val : Nat) : ZMod 2) * Multiplicative.ofAdd ((y.val : Nat) : ZMod 2) *
      Multiplicative.ofAdd ((z.val : Nat) : ZMod 2) = 1 ↔
      Nat.xor (Nat.xor x.val y.val) z.val = 0) := by
  decide

theorem phi_eq_one_iff (u v : Fin 4) (g : Model) :
    phi u v g = 1 ↔ phiR u.val v.val (rawc g) = 0 := by
  obtain ⟨-, a1, a2, a3, -, -⟩ := rawc_lanes g
  obtain ⟨⟨a, b, c⟩, e⟩ := g
  rw [phi_mk, phiR, a1, a2, a3, chi_code, chi_code, chi_code]
  exact ofAdd3 ⟨_, chiN_lt _ _⟩ ⟨_, chiN_lt _ _⟩ ⟨_, chiN_lt _ _⟩

theorem subsB_sound (h : subsB subsT = true) : SubsFact := by
  intro s hs m hm hphi
  rw [subsB, allRows_iff] at h
  have hr := h _ (List.mem_map_of_mem (f := fun s : Fin 4 × Fin 4 × List Cls =>
    s.1.val :: s.2.1.val :: s.2.2.map clsIdx) hs)
  have hr' : subRow (s.1.val :: s.2.1.val :: s.2.2.map clsIdx) =
      subOK s.1.val s.2.1.val (s.2.2.map clsIdx) := rfl
  rw [hr', subOK, allN_iff] at hr
  have hm' := hr _ (rawc_lt m)
  rw [bI_iff, bI_iff, beq_iff, memL_iff, clsN_rawc] at hm'
  obtain ⟨C, hC, hCm⟩ := List.mem_map.mp
    (hm' (isInvR_rawc.mpr hm) ((phi_eq_one_iff _ _ m).mp hphi))
  exact clsIdx_inj hCm ▸ hC

theorem z3M_central_raw : ∀ c, c < 1024 → mulR c 128 = mulR 128 c := by
  decide +kernel

theorem z3M_central (g : Model) : g * z3M = z3M * g := by
  have hz : rawc z3M = 128 := by decide +kernel
  apply rawc_inj
  rw [← mulR_rawc, ← mulR_rawc, hz]
  exact z3M_central_raw _ (rawc_lt g)

theorem keq_conj_iff (g : Model) {X Y : Model} :
    KEq (g * X * g⁻¹) (g * Y * g⁻¹) ↔ KEq X Y := by
  constructor
  · intro h
    have h' := KEq.mul (KEq.mul (KEq.refl g⁻¹) h) (KEq.refl g)
    simpa [mul_assoc] using h'
  · intro h
    exact KEq.mul (KEq.mul (KEq.refl g) h) (KEq.refl g⁻¹)

theorem keq_conj_one_iff (g : Model) {X : Model} : KEq (g * X * g⁻¹) 1 ↔ KEq X 1 := by
  have h := keq_conj_iff g (X := X) (Y := 1)
  simpa using h

theorem keq_conj_z3_iff (g : Model) {X : Model} : KEq (g * X * g⁻¹) z3M ↔ KEq X z3M := by
  have h := keq_conj_iff g (X := X) (Y := z3M)
  rwa [z3M_central, mul_assoc z3M, mul_inv_cancel, mul_one] at h

theorem conj_mul (g a b : Model) : g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by
  group

theorem D5M_conj (g : Model) {a b : Model} (h : D5M z3M a b) :
    D5M z3M (g * a * g⁻¹) (g * b * g⁻¹) := by
  unfold D5M at h ⊢
  simp only [conj_mul, keq_conj_iff, keq_conj_one_iff, keq_conj_z3_iff]
  exact h

theorem D5M_keq {a a' b : Model} (ha : KEq a a') (h : D5M z3M a b) : D5M z3M a' b := by
  have hs : ∀ X, KEq (X * a) (X * a') := fun X => KEq.mul (KEq.refl X) ha
  have hs' : ∀ X, KEq (a * X) (a' * X) := fun X => KEq.mul ha (KEq.refl X)
  have haa : KEq (a * a) (a' * a') := KEq.mul ha ha
  have hab : KEq (a * a * (b * b)) (a' * a' * (b * b)) := KEq.mul haa (KEq.refl _)
  unfold D5M at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨(hs' b).symm.trans (h1.trans (hs b)), h2, fun hc => h3 (haa.trans hc), h4,
    fun hc => h5 (hab.trans hc), fun hc => h6 (haa.trans hc), h7, fun hc => h8 (hab.trans hc),
    fun hc => h9 (haa.trans hc), fun hc => h10 (hab.trans (hc.trans haa.symm)),
    fun hc => h11 (hab.trans hc)⟩

theorem pA_code {a : Model} (h1 : ¬ KEq (a * a) 1) (h2 : ¬ KEq (a * a) z3M) :
    pA (code a) = true := by
  rw [pA, bN_iff, Bool.eq_false_iff]
  intro hc
  rw [bO_iff, beq_iff, beq_iff, ← code_mul, ← code_one, ← code_z3M, code_eq_iff,
    code_eq_iff] at hc
  rcases hc with hc | hc
  · exact h1 hc
  · exact h2 hc

theorem d5K_code {a b : Model} (h : D5M z3M a b) : d5K (code a) (code b) = true := by
  unfold D5M at h
  obtain ⟨h1, -, -, -, h5, -, -, h8, h9, h10, h11⟩ := h
  simp only [d5K, bA_iff, bN_iff, Bool.eq_false_iff, ne_eq, beq_iff, ← code_mul]
  rw [← code_one, ← code_z3M, commK_code]
  simp only [code_eq_iff]
  exact ⟨h1, h5, h8, h9, h10, h11⟩

theorem p7B_sound {A P X : List Nat} (h : p7B A P X = true) : Pair7Fact := by
  rw [p7B, bA_iff, bA_iff, bA_iff, eqL_iff, eqL_iff, allL_iff, allL_iff] at h
  obtain ⟨hA, hX, hC, hP⟩ := h
  have memA : ∀ a : Model, ¬ KEq (a * a) 1 → ¬ KEq (a * a) z3M → code a ∈ A := by
    intro a h1 h2
    rw [← hA, mem_filterR]
    obtain ⟨t, ht, hat⟩ := exists_rep a
    exact ⟨t, ht, hat.symm, hat ▸ pA_code h1 h2⟩
  intro a b hd
  have hd' := hd
  unfold D5M at hd'
  obtain ⟨-, -, ha1, hb1, -, ha3, hb3, -, -, -, -⟩ := hd'
  obtain ⟨x, hx, hxa⟩ := mem_lowL.mp (hX ▸ memA a ha1 ha3)
  have hk := hC x hx
  rw [conjP, bA_iff, bA_iff, bA_iff, memL_iff, beq_iff, hxa] at hk
  obtain ⟨hg, hr, hrP, hk⟩ := hk
  set G := dec (Nat.land (Nat.shiftRight x 10) 1023)
  set R := dec (Nat.shiftRight x 20)
  have hG : code G = Nat.land (Nat.shiftRight x 10) 1023 := code_dec_of_isC hg
  have hR : code R = Nat.shiftRight x 20 := code_dec_of_isC hr
  have hGR : KEq (G * a * G⁻¹) R := by
    apply keq_conj_of
    rw [← code_eq_iff, code_mul, code_mul, hG, hR]
    exact hk
  have hd2 := D5M_keq hGR (D5M_conj G hd)
  have hd2' := hd2
  unfold D5M at hd2'
  obtain ⟨-, -, -, hb1', -, -, hb3', -, -, -, -⟩ := hd2'
  have hb := allL_iff.mp (hP _ hrP) _ (memA _ hb1' hb3')
  rw [bN_iff, ← hR, d5K_code hd2] at hb
  exact Bool.noConfusion hb

end Certificates.FzFus.K

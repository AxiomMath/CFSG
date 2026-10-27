module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalAutDict
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28TSpec
public import Certificates.Certificate9557
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers

section Sylow


theorem txL_spec :
    txL.size = 243 ∧ txL[0]! = idCode ∧ (∀ i < 243, ∀ j < i, txL[i]! ≠ txL[j]!) ∧
    (∀ i < 243, ∀ j < 243, ∃ k < 243, mulCode txL[i]! txL[j]! = txL[k]!) ∧
    (∀ i < 243, ∃ j < 243, mulCode txL[i]! txL[j]! = idCode) :=
  t3OK_spec Certificates.certificate9557.1

theorem valid_tU : Valid tU := valid_wordCode _

theorem valid_tZ : Valid tZ := valid_wordCode _

theorem valid_tO : Valid tO := valid_wordCode _

theorem valid_txL {i : ℕ} (hi : i < 243) : Valid txL[i]! :=
  valid_t3List valid_tU valid_tZ valid_tO hi

theorem valid_tzc : Valid tzc := valid_powCode valid_tU 3

theorem frobStable_txL : ∀ n < 243, ∃ m < 243, frobCode txL[n]! = txL[m]! := by
  have := frobStable_spec Certificates.certificate9557.2.1
  rw [txL_spec.1] at this
  exact this

theorem zOKc_txL : tzc ≠ idCode ∧ powCode tzc 3 = idCode ∧ frobCode tzc = tzc ∧ txL[81]! = tzc ∧
    ∀ g ∈ tGens, semi (tzc, 0) g = semi g (tzc, 0) :=
  zOKc_spec Certificates.certificate9557.2.2.2.1

variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

@[expose] noncomputable def tuE : adjointGroup .G2 K := M.wordElt tUW

@[expose] noncomputable def tzE : adjointGroup .G2 K := M.wordElt tZW

@[expose] noncomputable def toE : adjointGroup .G2 K := M.wordElt tOW

theorem rho_tuE : M.rho (tuE M) = decode tU := M.rho_wordElt tUW

theorem rho_tzE : M.rho (tzE M) = decode tZ := M.rho_wordElt tZW

theorem rho_toE : M.rho (toE M) = decode tO := M.rho_wordElt tOW

@[expose] noncomputable def txElt (n : ℕ) : adjointGroup .G2 K :=
  tuE M ^ (n / 27) * tzE M ^ ((n / 3) % 9) * toE M ^ (n % 3)

theorem rho_txElt {n : ℕ} (hn : n < 243) : M.rho (txElt M n) = decode txL[n]! := by
  obtain ⟨h1, h1'⟩ := M.rho_pow (tuE M) valid_tU (rho_tuE M) (n / 27)
  obtain ⟨h2, h2'⟩ := M.rho_pow (tzE M) valid_tZ (rho_tzE M) ((n / 3) % 9)
  obtain ⟨h3, h3'⟩ := M.rho_pow (toE M) valid_tO (rho_toE M) (n % 3)
  rw [txElt, M.rho_mul_code (valid_mulCode h1 h2) h3 (M.rho_mul_code h1 h2 h1' h2') h3',
    txL, getElem!_t3List _ _ _ hn]

@[expose] noncomputable def TX : Subgroup (adjointGroup .G2 K) where
  carrier := {g | ∃ i < 243, M.rho g = decode txL[i]!}
  mul_mem' := by
    rintro a b ⟨i, hi, ha⟩ ⟨j, hj, hb⟩
    obtain ⟨k, hk, hk'⟩ := txL_spec.2.2.2.1 i hi j hj
    exact ⟨k, hk, by rw [M.rho_mul_code (valid_txL hi) (valid_txL hj) ha hb, hk']⟩
  one_mem' := ⟨0, by norm_num, by rw [txL_spec.2.1, map_one, decode_idCode]⟩
  inv_mem' := by
    rintro a ⟨i, hi, ha⟩
    obtain ⟨j, hj, hj'⟩ := txL_spec.2.2.2.2 i hi
    refine ⟨j, hj, ?_⟩
    have h1 : M.rho a⁻¹ * M.rho a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    have h2 : decode txL[i]! * decode txL[j]! = 1 := by
      rw [← decode_mulCode (valid_txL hi) (valid_txL hj), hj', decode_idCode]
    calc M.rho a⁻¹ = M.rho a⁻¹ * (decode txL[i]! * decode txL[j]!) := by rw [h2, mul_one]
      _ = (M.rho a⁻¹ * M.rho a) * decode txL[j]! := by rw [← ha, mul_assoc]
      _ = decode txL[j]! := by rw [h1, one_mul]

theorem mem_TX_iff (g : adjointGroup .G2 K) :
    g ∈ TX M ↔ ∃ i < 243, M.rho g = decode txL[i]! := Iff.rfl

theorem txElt_mem {n : ℕ} (hn : n < 243) : txElt M n ∈ TX M := ⟨n, hn, rho_txElt M hn⟩

theorem eq_txElt_of_rho {g : adjointGroup .G2 K} {n : ℕ} (hn : n < 243)
    (hg : M.rho g = decode txL[n]!) : g = txElt M n :=
  (M.eq_iff_codes (valid_txL hn) (valid_txL hn) hg (rho_txElt M hn)).2 rfl

theorem card_TX : Nat.card (TX M) = 243 := by
  have hbij : Function.Bijective
      (fun i : Fin 243 => (⟨txElt M i, txElt_mem M i.2⟩ : TX M)) := by
    constructor
    · intro i j hij
      have h : txElt M i = txElt M j := congrArg Subtype.val hij
      have hc := (M.eq_iff_codes (valid_txL i.2) (valid_txL j.2) (rho_txElt M i.2)
        (rho_txElt M j.2)).1 h
      by_contra hne
      have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne' with h | h
      · exact txL_spec.2.2.1 j.val j.2 i.val h hc.symm
      · exact txL_spec.2.2.1 i.val i.2 j.val h hc
    · rintro ⟨g, i, hi, hg⟩
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      exact (eq_txElt_of_rho M hi hg).symm
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem phiPow_mem_TX (k : ℕ) {g : adjointGroup .G2 K} (hg : g ∈ TX M) :
    (phi ^ k : MulAut (adjointGroup .G2 K)) g ∈ TX M := by
  obtain ⟨i, hi, hgi⟩ := hg
  have hv := valid_txL hi
  have hk : ∀ k, ∃ m < 243, frobk k txL[i]! = txL[m]! := by
    intro k
    induction k with
    | zero => exact ⟨i, hi, rfl⟩
    | succ k ih =>
      obtain ⟨m, hm, hm'⟩ := ih
      obtain ⟨m', hm2, hm2'⟩ := frobStable_txL m hm
      exact ⟨m', hm2, by rw [frobk, hm', hm2']⟩
  obtain ⟨m, hm, hm'⟩ := hk k
  exact ⟨m, hm, by rw [rho_phi_pow M k g hv hgi, hm']⟩

theorem phi_pow_apply_mem_TX_mul {g h : adjointGroup .G2 K} (i : ℕ) (hg : g ∈ TX M)
    (hh : h ∈ TX M) : g * (phi ^ i : MulAut (adjointGroup .G2 K)) h ∈ TX M :=
  (TX M).mul_mem hg (phiPow_mem_TX M i hh)

theorem mk_mul_mk_inv (hK : Nat.card K = 8) (g : adjointGroup .G2 K) {i : ℕ} (hi : i < 3) :
    (mk g i : MulAut (adjointGroup .G2 K)) *
      mk ((phi ^ ((3 - i) % 3) : MulAut (adjointGroup .G2 K)) g⁻¹) ((3 - i) % 3) = 1 := by
  have h3 := phi_pow_three hK
  have hij : i + (3 - i) % 3 = 0 ∨ i + (3 - i) % 3 = 3 := by omega
  have hphi : (phi ^ i : MulAut (adjointGroup .G2 K))
      ((phi ^ ((3 - i) % 3) : MulAut (adjointGroup .G2 K)) g⁻¹) = g⁻¹ := by
    rw [← MulAut.mul_apply, ← pow_add]
    rcases hij with h | h <;> simp [h, h3]
  rw [mk_mul, hphi, mul_inv_cancel]
  unfold mk
  rcases hij with h | h <;> simp [h, h3]

@[expose] noncomputable def T0 (hK : Nat.card K = 8) : Subgroup (MulAut (adjointGroup .G2 K)) where
  carrier := {α | ∃ g ∈ TX M, ∃ i < 3, α = mk g i}
  mul_mem' := by
    rintro _ _ ⟨g, hg, i, hi, rfl⟩ ⟨h, hh, j, hj, rfl⟩
    exact ⟨g * (phi ^ i : MulAut (adjointGroup .G2 K)) h, phi_pow_apply_mem_TX_mul M i hg hh,
      (i + j) % 3, Nat.mod_lt _ (by norm_num), by rw [mk_mul, mk_mod hK]⟩
  one_mem' := ⟨1, (TX M).one_mem, 0, by norm_num, by simp [mk]⟩
  inv_mem' := by
    rintro _ ⟨g, hg, i, hi, rfl⟩
    refine ⟨(phi ^ ((3 - i) % 3) : MulAut (adjointGroup .G2 K)) g⁻¹,
      phiPow_mem_TX M _ ((TX M).inv_mem hg), (3 - i) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
    exact inv_eq_of_mul_eq_one_right (mk_mul_mk_inv hK g hi)

theorem mem_T0_iff (hK : Nat.card K = 8) (α : MulAut (adjointGroup .G2 K)) :
    α ∈ T0 M hK ↔ ∃ g ∈ TX M, ∃ i < 3, α = mk g i := Iff.rfl

theorem mk_mem_T0 (hK : Nat.card K = 8) {g : adjointGroup .G2 K} (hg : g ∈ TX M) {i : ℕ}
    (hi : i < 3) :
    (mk g i : MulAut (adjointGroup .G2 K)) ∈ T0 M hK := ⟨g, hg, i, hi, rfl⟩

theorem card_T0 (hK : Nat.card K = 8) : Nat.card (T0 M hK) = 3 ^ 6 := by
  have hbij : Function.Bijective
      (fun p : TX M × Fin 3 => (⟨mk p.1 p.2, p.1, p.1.2, p.2, p.2.2, rfl⟩ : T0 M hK)) := by
    constructor
    · rintro ⟨⟨g, hg⟩, ⟨i, hi⟩⟩ ⟨⟨h, hh⟩, ⟨j, hj⟩⟩ e
      obtain ⟨rfl, rfl⟩ := mk_inj hK hi hj (congrArg Subtype.val e)
      rfl
    · rintro ⟨_, g, hg, i, hi, rfl⟩
      exact ⟨(⟨g, hg⟩, ⟨i, hi⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, card_TX M,
    Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  norm_num

@[expose] noncomputable def T0Sylow (hK : Nat.card K = 8) :
    Sylow 3 (MulAut (adjointGroup .G2 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine Sylow.ofCard (T0 M hK) ?_
  have hcard : Nat.card (MulAut (adjointGroup .G2 K)) = 3 ^ 6 * 17816092672 := by
    rw [card_aut hK, card_X' hK]
    ring
  rw [card_T0 M hK, factorization_eq_of_mul hcard (by norm_num)]

theorem coe_T0Sylow (hK : Nat.card K = 8) :
    ((T0Sylow M hK : Sylow 3 (MulAut (adjointGroup .G2 K))) :
      Subgroup (MulAut (adjointGroup .G2 K))) = T0 M hK := rfl

theorem tzc_eq : tzc = powCode tU 3 := rfl

@[expose] noncomputable def zE : adjointGroup .G2 K := tuE M ^ 3

theorem rho_zE : M.rho (zE M) = decode tzc := (M.rho_pow (tuE M) valid_tU (rho_tuE M) 3).2

theorem zE_mem_TX : zE M ∈ TX M :=
  ⟨81, by norm_num, by rw [rho_zE, zOKc_txL.2.2.2.1]⟩

theorem zE_pow_three : zE M ^ 3 = 1 := by
  have h1 : M.rho (zE M ^ 3) = decode (powCode tzc 3) :=
    (M.rho_pow (zE M) valid_tzc (rho_zE M) 3).2
  exact (M.eq_one_iff_code (valid_powCode valid_tzc 3) h1).2 zOKc_txL.2.1

theorem zE_ne_one : zE M ≠ 1 := fun h =>
  zOKc_txL.1 ((M.eq_one_iff_code valid_tzc (rho_zE M)).1 h)

theorem orderOf_zE : orderOf (zE M) = 3 := orderOf_eq_prime (zE_pow_three M) (zE_ne_one M)

theorem phi_zE : (phi : MulAut (adjointGroup .G2 K)) (zE M) = zE M := by
  apply M.rho_injective
  rw [rho_phi, rho_zE, ← decode_frobCode valid_tzc, zOKc_txL.2.2.1]

theorem tuE_eq : tuE M = txElt M 27 := by simp [txElt]

theorem tzE_eq : tzE M = txElt M 3 := by simp [txElt]

theorem toE_eq : toE M = txElt M 1 := by simp [txElt]

theorem tuE_mem_TX : tuE M ∈ TX M := by rw [tuE_eq]; exact txElt_mem M (by norm_num)

theorem tzE_mem_TX : tzE M ∈ TX M := by rw [tzE_eq]; exact txElt_mem M (by norm_num)

theorem toE_mem_TX : toE M ∈ TX M := by rw [toE_eq]; exact txElt_mem M (by norm_num)

theorem zE_comm_gen : zE M * tuE M = tuE M * zE M ∧ zE M * tzE M = tzE M * zE M ∧
    zE M * toE M = toE M * zE M := by
  have h := zOKc_txL.2.2.2.2
  have h1 := h (tU, 0) (by simp [tGens])
  have h2 := h (tZ, 0) (by simp [tGens])
  have h3 := h (tO, 0) (by simp [tGens])
  simp only [semi, frobk, Prod.mk.injEq] at h1 h2 h3
  refine ⟨?_, ?_, ?_⟩
  · exact (M.eq_iff_codes (valid_mulCode valid_tzc valid_tU) (valid_mulCode valid_tU valid_tzc)
      (M.rho_mul_code valid_tzc valid_tU (rho_zE M) (rho_tuE M))
      (M.rho_mul_code valid_tU valid_tzc (rho_tuE M) (rho_zE M))).2 h1.1
  · exact (M.eq_iff_codes (valid_mulCode valid_tzc valid_tZ) (valid_mulCode valid_tZ valid_tzc)
      (M.rho_mul_code valid_tzc valid_tZ (rho_zE M) (rho_tzE M))
      (M.rho_mul_code valid_tZ valid_tzc (rho_tzE M) (rho_zE M))).2 h2.1
  · exact (M.eq_iff_codes (valid_mulCode valid_tzc valid_tO) (valid_mulCode valid_tO valid_tzc)
      (M.rho_mul_code valid_tzc valid_tO (rho_zE M) (rho_toE M))
      (M.rho_mul_code valid_tO valid_tzc (rho_toE M) (rho_zE M))).2 h3.1

theorem zE_comm_txElt (n : ℕ) : zE M * txElt M n = txElt M n * zE M := by
  obtain ⟨h1, h2, h3⟩ := zE_comm_gen M
  have c1 : Commute (zE M) (tuE M) := h1
  have c2 : Commute (zE M) (tzE M) := h2
  have c3 : Commute (zE M) (toE M) := h3
  exact (((c1.pow_right _).mul_right (c2.pow_right _)).mul_right (c3.pow_right _)).eq

theorem zE_comm_TX {g : adjointGroup .G2 K} (hg : g ∈ TX M) : zE M * g = g * zE M := by
  obtain ⟨i, hi, hgi⟩ := hg
  rw [eq_txElt_of_rho M hi hgi]
  exact zE_comm_txElt M i

@[expose] noncomputable def zb : MulAut (adjointGroup .G2 K) := MulAut.conj (zE M)

theorem zb_mem_T0 (hK : Nat.card K = 8) : zb M ∈ T0 M hK :=
  ⟨zE M, zE_mem_TX M, 0, by norm_num, by simp [zb, mk]⟩

theorem zb_pow_three : zb M ^ 3 = 1 := by
  rw [zb, ← map_pow, zE_pow_three, map_one]

theorem zb_ne_one : zb M ≠ 1 := fun h =>
  zE_ne_one M (conj_injective_X (K := K) (h.trans (map_one MulAut.conj).symm))

theorem orderOf_zb : orderOf (zb M) = 3 := orderOf_eq_prime (zb_pow_three M) (zb_ne_one M)

theorem conj_mem_T0 (hK : Nat.card K = 8) {g : adjointGroup .G2 K} (hg : g ∈ TX M) :
    (MulAut.conj g : MulAut (adjointGroup .G2 K)) ∈ T0 M hK :=
  ⟨g, hg, 0, by norm_num, by simp [mk]⟩

theorem phi_mem_T0 (hK : Nat.card K = 8) : (phi : MulAut (adjointGroup .G2 K)) ∈ T0 M hK :=
  ⟨1, (TX M).one_mem, 1, by norm_num, by simp [mk]⟩

theorem isEl_conj_tuE : IsEl M (MulAut.conj (tuE M)) (tU, 0) := isEl_conj (rho_tuE M)

theorem isEl_conj_tzE : IsEl M (MulAut.conj (tzE M)) (tZ, 0) := isEl_conj (rho_tzE M)

theorem isEl_conj_toE : IsEl M (MulAut.conj (toE M)) (tO, 0) := isEl_conj (rho_toE M)

theorem center_T0_le (hK : Nat.card K = 8) :
    CFSG.Quasithin.centerOf (T0 M hK) ≤ Subgroup.zpowers (zb M) := by
  rintro α ⟨hαT, hαC⟩
  obtain ⟨g, hg, i, hi, rfl⟩ := hαT
  obtain ⟨n, hn, hgn⟩ := hg
  have hel : IsEl M (mk g i) (txL[n]!, i) := ⟨g, hgn, rfl⟩
  have hvn := valid_txL hn
  have key : ∀ (p : Array ℕ × ℕ) (γ : MulAut (adjointGroup .G2 K)), γ ∈ T0 M hK →
      IsEl M γ p → Valid p.1 → p.2 < 3 → semi (txL[n]!, i) p = semi p (txL[n]!, i) := by
    intro p γ hγ hγp hvp hp2
    have hcomm : γ * mk g i = mk g i * γ := (Subgroup.mem_centralizer_iff.mp hαC) γ hγ
    have h1 := IsEl.mul hK (p := (txL[n]!, i)) (q := p) hvn hvp hel hγp
    have h2 := IsEl.mul hK (p := p) (q := (txL[n]!, i)) hvp hvn hγp hel
    exact ((IsEl.inj hK (p := semi (txL[n]!, i) p) (q := semi p (txL[n]!, i))
      (valid_semi hvn hvp) (valid_semi hvp hvn) (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)) h1 h2).1 hcomm.symm)
  have hcen := centerOK_spec Certificates.certificate9557.2.2.1 n hn i hi (by
    intro p hp
    simp only [tGens, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact key _ _ (conj_mem_T0 M hK (tuE_mem_TX M)) (isEl_conj_tuE M) valid_tU (by norm_num)
    · exact key _ _ (conj_mem_T0 M hK (tzE_mem_TX M)) (isEl_conj_tzE M) valid_tZ (by norm_num)
    · exact key _ _ (conj_mem_T0 M hK (toE_mem_TX M)) (isEl_conj_toE M) valid_tO (by norm_num)
    · exact key _ _ (phi_mem_T0 M hK) (isEl_phi (M := M)) valid_idCode (by norm_num))
  obtain ⟨hi0, hcode⟩ := hcen
  subst hi0
  have hmk : (mk g 0 : MulAut (adjointGroup .G2 K)) = MulAut.conj g := by simp [mk]
  rw [hmk]
  rcases hcode with h | h | h
  · have : g = 1 := (M.eq_one_iff_code hvn (by rw [hgn, h])).2 h
    rw [this, map_one]
    exact Subgroup.one_mem _
  · have : g = zE M := (M.eq_iff_codes hvn valid_tzc hgn (rho_zE M)).2 h
    rw [this]
    exact Subgroup.mem_zpowers _
  · have hg2 : g = zE M * zE M := (M.eq_iff_codes hvn (valid_mulCode valid_tzc valid_tzc) hgn
      (M.rho_mul_code valid_tzc valid_tzc (rho_zE M) (rho_zE M))).2 h
    rw [hg2, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem zb_comm_T0 (hK : Nat.card K = 8) {α : MulAut (adjointGroup .G2 K)} (hα : α ∈ T0 M hK) :
    α * zb M = zb M * α := by
  obtain ⟨g, hg, i, hi, rfl⟩ := hα
  unfold mk zb
  have hc : MulAut.conj g * MulAut.conj (zE M) = MulAut.conj (zE M) * MulAut.conj g := by
    rw [← map_mul, ← map_mul, (zE_comm_TX M hg).symm]
  calc MulAut.conj g * phi ^ i * MulAut.conj (zE M)
      = MulAut.conj g * (phi ^ i * MulAut.conj (zE M)) := by rw [mul_assoc]
    _ = MulAut.conj g *
          (MulAut.conj ((phi ^ i : MulAut (adjointGroup .G2 K)) (zE M)) * phi ^ i) := by
      rw [phi_pow_mul_conj]
    _ = MulAut.conj g * (MulAut.conj (zE M) * phi ^ i) := by
      rw [show (phi ^ i : MulAut (adjointGroup .G2 K)) (zE M) = zE M from ?_]
      induction i with
      | zero => rfl
      | succ k ih => rw [pow_succ', MulAut.mul_apply, ih (by omega), phi_zE]
    _ = MulAut.conj (zE M) * MulAut.conj g * phi ^ i := by rw [← mul_assoc, hc]

end Sylow

end CFSG.AGLEmbedding.KFactProofs.G28

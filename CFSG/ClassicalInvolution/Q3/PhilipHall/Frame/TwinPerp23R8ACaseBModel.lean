module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8ClsMModel
public import CFSG.ClassicalInvolution.Q3.TL3T54
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamModel
public import CFSG.ClassicalInvolution.Q3.Sec13AE5Model
public import CFSG.ClassicalInvolution.Q3.TL3T37

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CaseB

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.Ae5Model
open CFSG.ClassicalInvolution.Q3.Sec13
open CFSG.ClassicalInvolution.Q3.TL4 Wr
open scoped symmDiff

private theorem mem_miss_of_embed {m : ℕ} (p : Fin 5) (ι : Fin m ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) (i : Fin m) : ι i ∈ miss p := by
  rw [miss, Finset.mem_erase]
  exact ⟨(hι (ι i)).mp (Set.mem_range_self i), Finset.mem_univ _⟩

private theorem pairVec_eq_indv {i j : Fin 5} (hij : i ≠ j) :
    TL4.pairVec i j = TC.Thin.indv ({i, j} : Finset (Fin 5)) := by
  funext x
  rw [TL4.pairVec_apply]
  simp only [TC.Thin.indv]
  by_cases hi : x = i
  · subst hi
    simp [hij, Ne.symm hij]
  · by_cases hj : x = j
    · subst hj
      simp [hi, Ne.symm hij]
    · simp [hi, hj]

private theorem indv_add_eq_indv_symmDiff (s t : Finset (Fin 5)) :
    TC.Thin.indv s + TC.Thin.indv t = TC.Thin.indv (s ∆ t) := by
  funext x
  rw [Pi.add_apply]
  simp only [TC.Thin.indv, Finset.mem_symmDiff]
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [hs, ht] <;> decide

private theorem indv_union {s t : Finset (Fin 5)} (h : Disjoint s t) :
    TC.Thin.indv (s ∪ t) = TC.Thin.indv s + TC.Thin.indv t := by
  rw [indv_add_eq_indv_symmDiff, h.symmDiff_eq_sup, Finset.sup_eq_union]

private theorem mkQ_embed_w0_eq_vbar (ι : Fin 4 ↪ Fin 5) :
    mkQ 5 (embed ι w0) = TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) := by
  rw [ClsM.mkQ_embed_w0]
  rw [ClsM.zBar_mul_zBar (ι.injective.ne (by decide))]
  rw [TL4.vbar]
  congr 1
  refine Wr.ext (funext fun x => ?_) rfl
  show (if x = ι 0 ∨ x = ι 1 then (1 : ZMod 2) else 0) = TL4.pairVec (ι 0) (ι 1) x
  rw [TL4.pairVec_apply]
  by_cases h0 : x = ι 0
  · subst h0
    simp [ι.injective.ne (by decide : (0 : Fin 4) ≠ 1)]
  · by_cases h1 : x = ι 1
    · subst h1
      simp [h0]
    · have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
      simp [h0, h1, h01, Ne.symm h0, Ne.symm h1]

private theorem vbar_pairVec_mul_self {n : ℕ} (i j : Fin n) :
    TL4.vbar n (TL4.pairVec i j) * TL4.vbar n (TL4.pairVec i j) = 1 := by
  rw [← TL4.vbar_add, TL4.add_self_vec, TL4.vbar_zero]

private theorem a_eq_vbar_pairVec (p : Fin 5) (ι : Fin 4 ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) (q r : Fin 5) (hqr : q ≠ r)
    (hT : ((miss p).erase (ι 0)).erase (ι 1) = {q, r}) :
    zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0) =
      TL4.vbar 5 (TL4.pairVec q r) := by
  have hι0 := mem_miss_of_embed p ι hι 0
  have hι1 := mem_miss_of_embed p ι hι 1
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have hι1' : ι 1 ∈ (miss p).erase (ι 0) :=
    Finset.mem_erase.mpr ⟨Ne.symm h01, hι1⟩
  have hqT : q ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hrT : r ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hq0 : q ≠ ι 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hqT).2).1
  have hq1 : q ≠ ι 1 := (Finset.mem_erase.mp hqT).1
  have hr0 : r ≠ ι 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hrT).2).1
  have hr1 : r ≠ ι 1 := (Finset.mem_erase.mp hrT).1
  have hdisj : Disjoint ({ι 0, ι 1} : Finset (Fin 5)) {q, r} := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hx'
    rcases hx with rfl | rfl <;> rcases hx' with rfl | rfl <;>
      simp_all [Ne.symm hq0, Ne.symm hq1, Ne.symm hr0, Ne.symm hr1]
  have hmiss : miss p = ({ι 0, ι 1} : Finset (Fin 5)) ∪ {q, r} := by
    rw [← Finset.insert_erase hι0, ← Finset.insert_erase hι1', hT]
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    tauto
  rw [TC.Thin.zBar_eq_vbar_indv, mkQ_embed_w0_eq_vbar, ← TL4.vbar_add]
  congr 1
  rw [pairVec_eq_indv h01, pairVec_eq_indv hqr, hmiss, indv_union hdisj]
  calc TC.Thin.indv ({ι 0, ι 1} : Finset (Fin 5)) + TC.Thin.indv {q, r} +
        TC.Thin.indv ({ι 0, ι 1} : Finset (Fin 5))
      = TC.Thin.indv {q, r} + (TC.Thin.indv ({ι 0, ι 1} : Finset (Fin 5)) +
        TC.Thin.indv ({ι 0, ι 1} : Finset (Fin 5))) := by abel
    _ = TC.Thin.indv {q, r} := by rw [TL4.add_self_vec, add_zero]


private theorem pow_three_eq_one (s : AEQ 5) (hs : s ∈ (aeSub 5).map (mkQ 5))
    (hs3 : IsPGroup 3 (Subgroup.zpowers s)) (hs1 : s ≠ 1) : s ^ 3 = 1 := by
  have hsA : s ∈ TL4.aeModel 5 := hs
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hs3) ⟨s, Subgroup.mem_zpowers s⟩
  have hdvd : orderOf s ∣ 960 := by
    have h := orderOf_dvd_natCard (⟨s, hsA⟩ : TL4.aeModel 5)
    rw [Subgroup.orderOf_mk] at h
    change orderOf s ∣ Nat.card (TL4.aeModel 5) at h
    rw [CFSG.ClassicalInvolution.Q3.Sec13.AE5Q8.card_aeModel_five] at h
    exact h
  have hns : orderOf s = 3 ^ n := by
    rw [← Subgroup.orderOf_mk]
    exact hn
  have hn' : 3 ^ n ∣ 960 := hns ▸ hdvd
  have hle : 3 ^ n ≤ 960 := Nat.le_of_dvd (by norm_num) hn'
  have hnle : n ≤ 6 := by
    by_contra h
    have h7 : 7 ≤ n := by omega
    have hpow : 3 ^ 7 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) h7
    norm_num at hpow
    omega
  have hord : orderOf s = 1 ∨ orderOf s = 3 := by
    interval_cases n <;> simp_all
  rcases hord with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hs1
  · rw [← h, pow_orderOf_eq_one]

private def pairShiftOK (p q r a b : Fin 5) (σ : Equiv.Perm (Fin 5)) : Bool :=
  let h := (q != r) && ({p, a, b, q, r} == (Finset.univ : Finset (Fin 5))) &&
    (σ ^ 3 == 1) && (σ != 1) && (σ a == a) && (σ b == b)
  let c := ((({q, r} : Finset (Fin 5)) ∩ ({σ q, σ r} : Finset (Fin 5))).card == 1) &&
    (({q, r} : Finset (Fin 5)) != ({σ q, σ r} : Finset (Fin 5)))
  !h || c

private theorem pairShiftOK_of_three :
    ∀ σ : Equiv.Perm (Fin 5), (σ ^ 3 == 1 && σ != 1) = true → ∀ a : Fin 5, σ a = a →
      ∀ b : Fin 5, σ b = b → ∀ p q r : Fin 5, pairShiftOK p q r a b σ = true := by
  decide +kernel

private theorem pairShiftOK_all :
    ∀ (p q r a b : Fin 5) (σ : Equiv.Perm (Fin 5)), pairShiftOK p q r a b σ = true := by
  intro p q r a b σ
  by_cases hb : σ b = b
  · by_cases ha : σ a = a
    · cases h1 : (σ ^ 3 == 1) <;> cases h2 : (σ != 1)
      · simp only [pairShiftOK, h1, h2, Bool.and_false, Bool.false_and, Bool.not_false,
          Bool.true_or]
      · simp only [pairShiftOK, h1, Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
      · simp only [pairShiftOK, h2, Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
      · exact pairShiftOK_of_three σ (by rw [h1, h2]; rfl) a ha b hb p q r
    · have ha' : (σ a == a) = false := beq_eq_false_iff_ne.2 ha
      simp only [pairShiftOK, ha', Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]
  · have hb' : (σ b == b) = false := beq_eq_false_iff_ne.2 hb
    simp only [pairShiftOK, hb', Bool.and_false, Bool.false_and, Bool.not_false, Bool.true_or]


private theorem pair_shift_card (p q r a b : Fin 5) (σ : Equiv.Perm (Fin 5))
    (hqr : q ≠ r) (hcover : ({p, a, b, q, r} : Finset (Fin 5)) = Finset.univ)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (ha : σ a = a) (hb : σ b = b) :
    (({q, r} : Finset (Fin 5)) ∩ ({σ q, σ r} : Finset (Fin 5))).card = 1 ∧
    (({q, r} : Finset (Fin 5)) ≠ ({σ q, σ r} : Finset (Fin 5))) := by
  have h := pairShiftOK_all p q r a b σ
  simp only [pairShiftOK] at h
  simp [hqr, hcover, hσ3, hσ1, ha, hb] at h
  exact h


private theorem not_swap_of_pow_three {σ : Equiv.Perm (Fin 5)} {a b : Fin 5} (hab : a ≠ b)
    (hσ3 : σ ^ 3 = 1) (h : σ a = b ∧ σ b = a) : False := by
  have h2 : σ (σ a) = a := by rw [h.1, h.2]
  have h3 : σ (σ (σ a)) = σ a := congrArg σ h2
  have h4 : σ (σ (σ a)) = a := by
    change (σ ^ 3) a = a
    rw [hσ3]
    rfl
  rw [h4, h.1] at h3
  exact hab h3

private theorem cover_univ (p : Fin 5) (ι : Fin 4 ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) (q r : Fin 5) (hqr : q ≠ r)
    (hT : ((miss p).erase (ι 0)).erase (ι 1) = {q, r}) :
    ({p, ι 0, ι 1, q, r} : Finset (Fin 5)) = Finset.univ := by
  have hι0 := mem_miss_of_embed p ι hι 0
  have hι1 := mem_miss_of_embed p ι hι 1
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have hpι0 : p ≠ ι 0 := ((hι (ι 0)).mp (Set.mem_range_self 0)).symm
  have hpι1 : p ≠ ι 1 := ((hι (ι 1)).mp (Set.mem_range_self 1)).symm
  have hqT : q ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hrT : r ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hqerase : q ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hqT).2
  have hqmiss : q ∈ miss p := (Finset.mem_erase.mp hqerase).2
  have hrerase : r ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hrT).2
  have hrmiss : r ∈ miss p := (Finset.mem_erase.mp hrerase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqmiss).1.symm
  have hpr : p ≠ r := (Finset.mem_erase.mp hrmiss).1.symm
  have hq0 : q ≠ ι 0 := (Finset.mem_erase.mp hqerase).1
  have hq1 : q ≠ ι 1 := (Finset.mem_erase.mp hqT).1
  have hr0 : r ≠ ι 0 := (Finset.mem_erase.mp hrerase).1
  have hr1 : r ≠ ι 1 := (Finset.mem_erase.mp hrT).1
  refine Finset.eq_univ_of_forall (fun y => ?_)
  by_cases hyp : y = p
  · subst hyp
    simp
  · rcases YGam.eq_of_ne_of_distinct p q r (ι 0) (ι 1) hpq hpr hpι0 hpι1 hqr hq0 hq1 hr0 hr1 h01 y hyp with h | h | h | h
    · subst h; simp
    · subst h; simp
    · subst h; simp
    · subst h; simp


private theorem sigma_facts (p : Fin 5) (ι : Fin 4 ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p)
    (s : AEQ 5) (hs : s ∈ (aeSub 5).map (mkQ 5))
    (hs3 : IsPGroup 3 (Subgroup.zpowers s)) (hs1 : s ≠ 1)
    (hsb : s * mkQ 5 (embed ι w0) = mkQ 5 (embed ι w0) * s)
    (q r : Fin 5) (hqr : q ≠ r)
    (hT : ((miss p).erase (ι 0)).erase (ι 1) = {q, r}) :
    ∃ σ : Equiv.Perm (Fin 5),
      σ = TL4.permBar 5 s ∧ σ ∈ alternatingGroup (Fin 5) ∧ σ ^ 3 = 1 ∧ σ ≠ 1 ∧
      σ (ι 0) = ι 0 ∧ σ (ι 1) = ι 1 ∧
      (({q, r} : Finset (Fin 5)) ∩ ({σ q, σ r} : Finset (Fin 5))).card = 1 ∧
      (({q, r} : Finset (Fin 5)) ≠ ({σ q, σ r} : Finset (Fin 5))) := by
  classical
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  let σ : Equiv.Perm (Fin 5) := TL4.permBar 5 s
  have hspow : s ^ 3 = 1 := pow_three_eq_one s hs hs3 hs1
  have hsA : s ∈ aeBarOver (alternatingGroup (Fin 5)) := by
    rw [← TL4.aeModel_eq 5]
    exact hs
  have hσmem : σ ∈ alternatingGroup (Fin 5) := TL4.permBar_mem_of_mem hsA
  have hσ3 : σ ^ 3 = 1 := by
    show (TL4.permBar 5 s) ^ 3 = 1
    rw [← map_pow, hspow, map_one]
  have hσ1 : σ ≠ 1 := by
    intro h
    have hss : s * s = 1 := TL4.mul_self_of_permBar_eq_one (by
      show TL4.permBar 5 s = 1
      exact h)
    have : s = 1 := by
      calc s = s ^ 3 * (s * s)⁻¹ := by group
        _ = 1 := by rw [hspow, hss, inv_one, mul_one]
    exact hs1 this
  have hb_eq : mkQ 5 (embed ι w0) = TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) :=
    mkQ_embed_w0_eq_vbar ι
  have hconj_b : s * mkQ 5 (embed ι w0) * s⁻¹ = mkQ 5 (embed ι w0) := by
    rw [hsb, mul_assoc, mul_inv_cancel, mul_one]
  have hconj_b' : s * TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) * s⁻¹ =
      TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) := by
    simpa [hb_eq] using hconj_b
  have hconj : s * TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) * s⁻¹ =
      TL4.vbar 5 (TL4.actV σ (TL4.pairVec (ι 0) (ι 1))) :=
    TL4.conj_vbar (g := s) (σ := σ) (by rfl) _
  have hveq : TL4.vbar 5 (TL4.actV σ (TL4.pairVec (ι 0) (ι 1))) =
      TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) := by
    rw [← hconj, hconj_b']
  have hmod : TL4.ModPi (TL4.actV σ (TL4.pairVec (ι 0) (ι 1)))
      (TL4.pairVec (ι 0) (ι 1)) :=
    TL4.vbar_eq_iff.mp hveq
  rw [TL4.actV_pairVec] at hmod
  obtain ⟨hpair0, hpair1⟩ := TL4.pair_eq_of_modPi (by norm_num) h01 hmod
  have hfix0 : σ (ι 0) = ι 0 := by
    rcases hpair0 with h | h
    · exact h
    · exfalso
      have h1' : σ (ι 1) = ι 0 := by
        rcases hpair1 with h' | h'
        · exact h'
        · exact absurd (h.trans h'.symm) (σ.injective.ne h01)
      exact not_swap_of_pow_three h01 hσ3 ⟨h, h1'⟩
  have hfix1 : σ (ι 1) = ι 1 := by
    rcases hpair1 with h' | h'
    · exfalso
      exact (σ.injective.ne h01) (hfix0.trans h'.symm)
    · exact h'
  have hcover : ({p, ι 0, ι 1, q, r} : Finset (Fin 5)) = Finset.univ :=
    cover_univ p ι hι q r hqr hT
  have hshift := pair_shift_card p q r (ι 0) (ι 1) σ hqr hcover hσ3 hσ1 hfix0 hfix1
  exact ⟨σ, rfl, hσmem, hσ3, hσ1, hfix0, hfix1, hshift⟩


private def pairSumOK (a b c d : Fin 5) : Bool :=
  let h := (a != b) && (c != d) &&
    ((({a, b} : Finset (Fin 5)) ∩ ({c, d} : Finset (Fin 5))).card == 1) &&
    (({a, b} : Finset (Fin 5)) != ({c, d} : Finset (Fin 5)))
  let ccl := ((({a, b} : Finset (Fin 5)) ∆ ({c, d} : Finset (Fin 5))).card == 2)
  !h || ccl

private theorem pairSumOK_all : ∀ a b c d : Fin 5, pairSumOK a b c d = true := by
  decide +kernel

private theorem pair_symmDiff_card {a b c d : Fin 5}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hinter : (({a, b} : Finset (Fin 5)) ∩ ({c, d} : Finset (Fin 5))).card = 1)
    (hne : ({a, b} : Finset (Fin 5)) ≠ ({c, d} : Finset (Fin 5))) :
    (({a, b} : Finset (Fin 5)) ∆ ({c, d} : Finset (Fin 5))).card = 2 := by
  have h := pairSumOK_all a b c d
  simp only [pairSumOK] at h
  simp [hab, hcd, hinter, hne] at h
  exact h


private theorem exists_qr (p : Fin 5) (ι : Fin 4 ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) :
    ∃ q r : Fin 5, q ≠ r ∧ ((miss p).erase (ι 0)).erase (ι 1) = {q, r} := by
  have hι0 := mem_miss_of_embed p ι hι 0
  have hι1 := mem_miss_of_embed p ι hι 1
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have hι1' : ι 1 ∈ (miss p).erase (ι 0) :=
    Finset.mem_erase.mpr ⟨Ne.symm h01, hι1⟩
  have hcard : (((miss p).erase (ι 0)).erase (ι 1)).card = 2 := by
    rw [Finset.card_erase_of_mem hι1', Finset.card_erase_of_mem hι0]
    simp [miss]
  exact Finset.card_eq_two.mp hcard

private theorem all_pairVec_mem (N : Subgroup (AEQ 5))
    (hNn : ∀ x ∈ (aeSub 5).map (mkQ 5), ∀ m ∈ N, x * m * x⁻¹ ∈ N)
    {x y : Fin 5} (hxy : x ≠ y)
    (hxyn : TL4.vbar 5 (TL4.pairVec x y) ∈ N) :
    ∀ u v : Fin 5, u ≠ v → TL4.vbar 5 (TL4.pairVec u v) ∈ N := by
  intro u v huv
  obtain ⟨g, hg1, hg2⟩ := CFSG.ClassicalInvolution.Q3.Sec13.A5.exists_two_trans x y u v hxy huv
  have hgA : mkQ 5 (Wr.ofPerm (g : Equiv.Perm (Fin 5))) ∈ (aeSub 5).map (mkQ 5) :=
    TC.Thin.mem_aeModel_ofPerm g.2
  have hconj := hNn _ hgA _ hxyn
  have hconj_eq : mkQ 5 (Wr.ofPerm (g : Equiv.Perm (Fin 5))) *
      TL4.vbar 5 (TL4.pairVec x y) *
      (mkQ 5 (Wr.ofPerm (g : Equiv.Perm (Fin 5))))⁻¹ =
      TL4.vbar 5 (TL4.pairVec u v) := by
    rw [TL4.conj_vbar (permBar_mkQ (Wr.ofPerm (g : Equiv.Perm (Fin 5)))), TL4.actV_pairVec]
    change TL4.vbar 5 (TL4.pairVec ((g : Equiv.Perm (Fin 5)) x) ((g : Equiv.Perm (Fin 5)) y)) =
      TL4.vbar 5 (TL4.pairVec u v)
    rw [hg1, hg2]
  rwa [hconj_eq] at hconj


theorem caseB_model_normal (p : Fin 5) (ι : Fin 4 ↪ Fin 5) (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p)
    (s : AEQ 5) (hs : s ∈ (aeSub 5).map (mkQ 5)) (hs3 : IsPGroup 3 (Subgroup.zpowers s)) (hs1 : s ≠ 1)
    (hsb : s * mkQ 5 (embed ι w0) = mkQ 5 (embed ι w0) * s)
    (N : Subgroup (AEQ 5)) (hNA : N ≤ (aeSub 5).map (mkQ 5))
    (hNn : ∀ x ∈ (aeSub 5).map (mkQ 5), ∀ m ∈ N, x * m * x⁻¹ ∈ N)
    (hc : s * (zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0)) * s⁻¹ *
        (zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0))⁻¹ ∈ N) :
    zBar (miss p) (card_miss p) ∈ N := by
  classical
  set z : AEQ 5 := zBar (miss p) (card_miss p) with hz
  set b : AEQ 5 := mkQ 5 (embed ι w0) with hb
  obtain ⟨q, r, hqr, hT⟩ := exists_qr p ι hι
  have ha : z * b = TL4.vbar 5 (TL4.pairVec q r) := by
    rw [hz, hb]
    exact a_eq_vbar_pairVec p ι hι q r hqr hT
  obtain ⟨σ, hσeq, hσmem, hσ3, hσ1, hfix0, hfix1, hshift⟩ :=
    sigma_facts p ι hι s hs hs3 hs1 hsb q r hqr hT
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have ha' : s * (z * b) * s⁻¹ = TL4.vbar 5 (TL4.pairVec (σ q) (σ r)) := by
    rw [ha]
    rw [TL4.conj_vbar (g := s) (σ := σ) (by rw [hσeq])]
    rw [TL4.actV_pairVec]
  have hcard : (({q, r} : Finset (Fin 5)) ∆ ({σ q, σ r} : Finset (Fin 5))).card = 2 :=
    pair_symmDiff_card hqr (σ.injective.ne hqr) hshift.1 hshift.2
  obtain ⟨x, y, hxy, hU⟩ := Finset.card_eq_two.mp hcard
  have hsum : TL4.pairVec (σ q) (σ r) + TL4.pairVec q r = TL4.pairVec x y := by
    rw [pairVec_eq_indv (σ.injective.ne hqr), pairVec_eq_indv hqr, indv_add_eq_indv_symmDiff]
    rw [symmDiff_comm, hU, ← pairVec_eq_indv hxy]
  have hb_sq : b * b = 1 := by
    rw [hb, mkQ_embed_w0_eq_vbar]
    exact vbar_pairVec_mul_self (ι 0) (ι 1)
  have hcN : s * (z * b) * s⁻¹ * (z * b)⁻¹ ∈ N := by
    simpa [hz, hb] using hc
  have hc_vbar : s * (z * b) * s⁻¹ * (z * b)⁻¹ = TL4.vbar 5 (TL4.pairVec x y) := by
    rw [ha']
    rw [show (z * b)⁻¹ = TL4.vbar 5 (TL4.pairVec q r) from by
      rw [ha]
      exact inv_eq_of_mul_eq_one_right (vbar_pairVec_mul_self q r)]
    rw [← TL4.vbar_add, hsum]
  have hxyn : TL4.vbar 5 (TL4.pairVec x y) ∈ N := by
    rw [← hc_vbar]
    exact hcN
  have hall := all_pairVec_mem N hNn hxy hxyn
  have haN : TL4.vbar 5 (TL4.pairVec q r) ∈ N := hall q r hqr
  have hbN : TL4.vbar 5 (TL4.pairVec (ι 0) (ι 1)) ∈ N := hall (ι 0) (ι 1) h01
  have hzbN : z * b ∈ N := by
    rw [ha]
    exact haN
  have hbN' : b ∈ N := by
    rw [hb, mkQ_embed_w0_eq_vbar]
    exact hbN
  have hz_eq : z = (z * b) * b := by
    rw [mul_assoc, hb_sq, mul_one]
  rw [hz_eq]
  exact N.mul_mem hzbN hbN'


private theorem pairVec_eq_of_pair_eq {a b c d : Fin 5} (hab : a ≠ b) (hcd : c ≠ d)
    (h : ({a, b} : Finset (Fin 5)) = {c, d}) : TL4.pairVec a b = TL4.pairVec c d := by
  rw [pairVec_eq_indv hab, pairVec_eq_indv hcd, h]

private theorem ofPerm_mem_centralizer_pairVec {τ : Equiv.Perm (Fin 5)}
    (hτ : τ ∈ alternatingGroup (Fin 5)) {u v : Fin 5} (huv : u ≠ v)
    (hfix : ({τ u, τ v} : Finset (Fin 5)) = {u, v}) :
    mkQ 5 (Wr.ofPerm τ) * TL4.vbar 5 (TL4.pairVec u v) * (mkQ 5 (Wr.ofPerm τ))⁻¹ =
      TL4.vbar 5 (TL4.pairVec u v) := by
  rw [TL4.conj_vbar (permBar_mkQ (Wr.ofPerm τ)), TL4.actV_pairVec]
  congr 1
  exact pairVec_eq_of_pair_eq (τ.injective.ne huv) huv hfix


private theorem pair_other :
    ∀ (p q r : Fin 5) (pair : Finset (Fin 5)),
      p ≠ q → p ≠ r → q ≠ r →
      pair ⊆ {p, q, r} → pair.card = 2 → pair ≠ {q, r} →
      ∃ t s : Fin 5, ({t, s} : Finset (Fin 5)) = {q, r} ∧ t ∉ pair ∧ s ∈ pair ∧
        pair = {p, s} := by
  decide +kernel


private theorem sigma_mem_pqr (p : Fin 5) (ι : Fin 4 ↪ Fin 5)
    (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p) (q r : Fin 5) (hqr : q ≠ r)
    (hT : ((miss p).erase (ι 0)).erase (ι 1) = {q, r}) (σ : Equiv.Perm (Fin 5))
    (hfix0 : σ (ι 0) = ι 0) (hfix1 : σ (ι 1) = ι 1) :
    ({σ q, σ r} : Finset (Fin 5)) ⊆ ({p, q, r} : Finset (Fin 5)) := by
  have hcover := cover_univ p ι hι q r hqr hT
  have hqT : q ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hrT : r ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
  have hqerase : q ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hqT).2
  have hrerase : r ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hrT).2
  have hq0 : q ≠ ι 0 := (Finset.mem_erase.mp hqerase).1
  have hq1 : q ≠ ι 1 := (Finset.mem_erase.mp hqT).1
  have hr0 : r ≠ ι 0 := (Finset.mem_erase.mp hrerase).1
  have hr1 : r ≠ ι 1 := (Finset.mem_erase.mp hrT).1
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · have hmem : σ q ∈ ({p, ι 0, ι 1, q, r} : Finset (Fin 5)) := by
      rw [hcover]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · simp [h]
    · exfalso; exact hq0 (σ.injective (h.trans hfix0.symm))
    · exfalso; exact hq1 (σ.injective (h.trans hfix1.symm))
    · simp [h]
    · simp [h]
  · have hmem : σ r ∈ ({p, ι 0, ι 1, q, r} : Finset (Fin 5)) := by
      rw [hcover]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h
    · simp [h]
    · exfalso; exact hr0 (σ.injective (h.trans hfix0.symm))
    · exfalso; exact hr1 (σ.injective (h.trans hfix1.symm))
    · simp [h]
    · simp [h]


private theorem swap_pair_other {q r t s : Fin 5} (hqr : q ≠ r)
    (hts : ({t, s} : Finset (Fin 5)) = {q, r}) : Equiv.swap q r t = s := by
  have ht : t = q ∨ t = r := by
    have : t ∈ ({q, r} : Finset (Fin 5)) := by rw [← hts]; simp
    simpa using this
  have hs : s = q ∨ s = r := by
    have : s ∈ ({q, r} : Finset (Fin 5)) := by rw [← hts]; simp
    simpa using this
  rcases ht with rfl | rfl <;> rcases hs with rfl | rfl
  · exfalso
    have hcard := congrArg Finset.card hts
    simp [hqr] at hcard
  · simp
  · simp
  · exfalso
    have hcard := congrArg Finset.card hts
    simp [hqr] at hcard

private theorem mem_centralizer_pairVec {τ : Equiv.Perm (Fin 5)}
    (hτ : τ ∈ alternatingGroup (Fin 5)) {u v : Fin 5} (huv : u ≠ v)
    (hfix : ({τ u, τ v} : Finset (Fin 5)) = {u, v}) :
    mkQ 5 (Wr.ofPerm τ) ∈ Subgroup.centralizer
      ({TL4.vbar 5 (TL4.pairVec u v)} : Set (AEQ 5)) := by
  refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
  have hconj := ofPerm_mem_centralizer_pairVec hτ huv hfix
  calc mkQ 5 (Wr.ofPerm τ) * TL4.vbar 5 (TL4.pairVec u v)
      = (mkQ 5 (Wr.ofPerm τ) * TL4.vbar 5 (TL4.pairVec u v) *
          (mkQ 5 (Wr.ofPerm τ))⁻¹) * mkQ 5 (Wr.ofPerm τ) := by group
    _ = TL4.vbar 5 (TL4.pairVec u v) * mkQ 5 (Wr.ofPerm τ) := by rw [hconj]


theorem caseB_model_gen (p : Fin 5) (ι : Fin 4 ↪ Fin 5) (hι : ∀ y, y ∈ Set.range ι ↔ y ≠ p)
    (s : AEQ 5) (hs : s ∈ (aeSub 5).map (mkQ 5)) (hs3 : IsPGroup 3 (Subgroup.zpowers s)) (hs1 : s ≠ 1)
    (hsb : s * mkQ 5 (embed ι w0) = mkQ 5 (embed ι w0) * s) :
    zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0) ∈ (aeSub 5).map (mkQ 5) ∧
    (aeSub 5).map (mkQ 5) ≤
      (Subgroup.centralizer ({zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0)} : Set (AEQ 5)) ⊓
          (aeSub 5).map (mkQ 5)) ⊔
      (Subgroup.centralizer
          ({s * (zBar (miss p) (card_miss p) * mkQ 5 (embed ι w0)) * s⁻¹} : Set (AEQ 5)) ⊓
          (aeSub 5).map (mkQ 5)) := by
  classical
  set z : AEQ 5 := zBar (miss p) (card_miss p) with hz
  set b : AEQ 5 := mkQ 5 (embed ι w0) with hb
  set a : AEQ 5 := z * b with ha_def
  set a' : AEQ 5 := s * a * s⁻¹ with ha'_def
  set A : Subgroup (AEQ 5) := (aeSub 5).map (mkQ 5) with hA
  set H : Subgroup (AEQ 5) := (Subgroup.centralizer ({a} : Set (AEQ 5)) ⊓ A) ⊔
      (Subgroup.centralizer ({a'} : Set (AEQ 5)) ⊓ A) with hH
  obtain ⟨q, r, hqr, hT⟩ := exists_qr p ι hι
  have ha : a = TL4.vbar 5 (TL4.pairVec q r) := by
    rw [ha_def, hz, hb]
    exact a_eq_vbar_pairVec p ι hι q r hqr hT
  obtain ⟨σ, hσeq, hσmem, hσ3, hσ1, hfix0, hfix1, hshift⟩ :=
    sigma_facts p ι hι s hs hs3 hs1 hsb q r hqr hT
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  have ha' : a' = TL4.vbar 5 (TL4.pairVec (σ q) (σ r)) := by
    rw [ha'_def, ha]
    rw [TL4.conj_vbar (g := s) (σ := σ) (by rw [hσeq])]
    rw [TL4.actV_pairVec]
  have hzA : z ∈ A := by
    rw [hz, hA]
    exact TC.Thin.zBar_mem_aeModel (miss p) (card_miss p)
  have hbA : b ∈ A := by
    rw [hb, hA, mkQ_embed_w0_eq_vbar]
    exact TC.Thin.vbar_pairVec_mem_aeModel (ι 0) (ι 1)
  have haA : a ∈ A := by rw [ha_def]; exact A.mul_mem hzA hbA
  have ha'A : a' ∈ A := by rw [ha'_def]; exact A.mul_mem (A.mul_mem hs haA) (A.inv_mem hs)
  refine ⟨?_, ?_⟩
  · exact haA
  ·
    have hvbar_H : ∀ u : Fin 5 → ZMod 2, (∑ i, u i = 0) → TL4.vbar 5 u ∈ H := by
      intro u hu
      have huA : TL4.vbar 5 u ∈ A := by
        rw [hA]
        have h := TL4.vbar_mem_aeBarOver (P := alternatingGroup (Fin 5)) hu
        simpa [TL4.aeModel_eq] using h
      have hcomm : TL4.vbar 5 u * a = a * TL4.vbar 5 u := by
        rw [ha, ← TL4.vbar_add, ← TL4.vbar_add, add_comm]
      exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm, huA⟩)
    have hqT : q ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
    have hrT : r ∈ ((miss p).erase (ι 0)).erase (ι 1) := by rw [hT]; simp
    have hqerase : q ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hqT).2
    have hrerase : r ∈ (miss p).erase (ι 0) := (Finset.mem_erase.mp hrT).2
    have hqmiss : q ∈ miss p := (Finset.mem_erase.mp hqerase).2
    have hrmiss : r ∈ miss p := (Finset.mem_erase.mp hrerase).2
    have hpq : p ≠ q := (Finset.mem_erase.mp hqmiss).1.symm
    have hpr : p ≠ r := (Finset.mem_erase.mp hrmiss).1.symm
    have hpι0 : p ≠ ι 0 := ((hι (ι 0)).mp (Set.mem_range_self 0)).symm
    have hpι1 : p ≠ ι 1 := ((hι (ι 1)).mp (Set.mem_range_self 1)).symm
    have hq0 : q ≠ ι 0 := (Finset.mem_erase.mp hqerase).1
    have hq1 : q ≠ ι 1 := (Finset.mem_erase.mp hqT).1
    have hr0 : r ≠ ι 0 := (Finset.mem_erase.mp hrerase).1
    have hr1 : r ≠ ι 1 := (Finset.mem_erase.mp hrT).1
    have hcover := cover_univ p ι hι q r hqr hT
    have hpair_subset : ({σ q, σ r} : Finset (Fin 5)) ⊆ ({p, q, r} : Finset (Fin 5)) :=
      sigma_mem_pqr p ι hι q r hqr hT σ hfix0 hfix1
    have hpair_card : ({σ q, σ r} : Finset (Fin 5)).card = 2 :=
      Finset.card_pair (σ.injective.ne hqr)
    obtain ⟨t, u, htu, ht_notin, hu_in, hpair_eq⟩ :=
      pair_other p q r ({σ q, σ r} : Finset (Fin 5)) hpq hpr hqr hpair_subset hpair_card (Ne.symm hshift.2)
    let τ1 : Equiv.Perm (Fin 5) := Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)
    let h : Equiv.Perm (Fin 5) := Equiv.swap q r * Equiv.swap (ι 0) (ι 1)
    let τ2 : Equiv.Perm (Fin 5) := Equiv.swap t (ι 0) * Equiv.swap (ι 0) (ι 1)
    let G : Subgroup (Equiv.Perm (Fin 5)) := Subgroup.closure ({τ1, τ2, h} : Set (Equiv.Perm (Fin 5)))
    have htu_mem : t = q ∨ t = r := by
      have : t ∈ ({q, r} : Finset (Fin 5)) := by rw [← htu]; simp
      simpa using this
    have huu_mem : u = q ∨ u = r := by
      have : u ∈ ({q, r} : Finset (Fin 5)) := by rw [← htu]; simp
      simpa using this
    have htu_ne : t ≠ u := by
      intro h
      subst h
      have : ({t, t} : Finset (Fin 5)).card = 1 := by simp
      rw [htu] at this
      rw [Finset.card_pair hqr] at this
      omega
    have ht0 : t ≠ ι 0 := by rcases htu_mem with rfl | rfl; exacts [hq0, hr0]
    have ht1 : t ≠ ι 1 := by rcases htu_mem with rfl | rfl; exacts [hq1, hr1]
    have hu0 : u ≠ ι 0 := by rcases huu_mem with rfl | rfl; exacts [hq0, hr0]
    have hu1 : u ≠ ι 1 := by rcases huu_mem with rfl | rfl; exacts [hq1, hr1]
    have htp : t ≠ p := by rcases htu_mem with rfl | rfl; exacts [Ne.symm hpq, Ne.symm hpr]
    have hup : u ≠ p := by rcases huu_mem with rfl | rfl; exacts [Ne.symm hpq, Ne.symm hpr]
    have hτ1_q : τ1 q = q := by
      change (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)) q = q
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hq0 hq1,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hpq) hq0]
    have hτ1_r : τ1 r = r := by
      change (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)) r = r
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hr0 hr1,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hpr) hr0]
    have hτ1_fix : ({τ1 q, τ1 r} : Finset (Fin 5)) = {q, r} := by rw [hτ1_q, hτ1_r]
    have hh_q : h q = r := by
      show Equiv.swap q r (Equiv.swap (ι 0) (ι 1) q) = r
      rw [Equiv.swap_apply_of_ne_of_ne hq0 hq1]
      exact Equiv.swap_apply_left q r
    have hh_r : h r = q := by
      show Equiv.swap q r (Equiv.swap (ι 0) (ι 1) r) = q
      rw [Equiv.swap_apply_of_ne_of_ne hr0 hr1]
      exact Equiv.swap_apply_right q r
    have hh_fix : ({h q, h r} : Finset (Fin 5)) = {q, r} := by rw [hh_q, hh_r, Finset.pair_comm]
    have hτ2_p : τ2 p = p := by
      change (Equiv.swap t (ι 0) * Equiv.swap (ι 0) (ι 1)) p = p
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpι0 hpι1,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm htp) hpι0]
    have hτ2_u : τ2 u = u := by
      change (Equiv.swap t (ι 0) * Equiv.swap (ι 0) (ι 1)) u = u
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hu0 hu1,
        Equiv.swap_apply_of_ne_of_ne (Ne.symm htu_ne) hu0]
    have hτ2_fix : ({τ2 (σ q), τ2 (σ r)} : Finset (Fin 5)) = {σ q, σ r} := by
      have hfixq : τ2 (σ q) = σ q := by
        have : σ q ∈ ({p, u} : Finset (Fin 5)) := by rw [← hpair_eq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · rw [h, hτ2_p]
        · rw [h, hτ2_u]
      have hfixr : τ2 (σ r) = σ r := by
        have : σ r ∈ ({p, u} : Finset (Fin 5)) := by rw [← hpair_eq]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at this
        rcases this with h | h
        · rw [h, hτ2_p]
        · rw [h, hτ2_u]
      rw [hfixq, hfixr]
    have hτ1_mem : τ1 ∈ G := Subgroup.subset_closure (by simp [G])
    have hτ2_mem : τ2 ∈ G := Subgroup.subset_closure (by simp [G])
    have hh_mem : h ∈ G := Subgroup.subset_closure (by simp [G])
    have hτ1A : τ1 ∈ alternatingGroup (Fin 5) :=
      CFSG.ClassicalInvolution.Q3.AE.Block4.swap_mul_swap_mem hpι0 h01
    have hτ2A : τ2 ∈ alternatingGroup (Fin 5) :=
      CFSG.ClassicalInvolution.Q3.AE.Block4.swap_mul_swap_mem ht0 h01
    have hhA : h ∈ alternatingGroup (Fin 5) :=
      CFSG.ClassicalInvolution.Q3.AE.Block4.swap_mul_swap_mem hqr h01
    have hg1 : mkQ 5 (Wr.ofPerm τ1) ∈ H := by
      rw [hH, ha]
      refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mem_centralizer_pairVec hτ1A hqr hτ1_fix
      · exact TC.Thin.mem_aeModel_ofPerm hτ1A
    have hg2 : mkQ 5 (Wr.ofPerm τ2) ∈ H := by
      rw [hH, ha']
      refine Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mem_centralizer_pairVec hτ2A (σ.injective.ne hqr) hτ2_fix
      · exact TC.Thin.mem_aeModel_ofPerm hτ2A
    have hhh : mkQ 5 (Wr.ofPerm h) ∈ H := by
      rw [hH, ha]
      refine Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      · exact mem_centralizer_pairVec hhA hqr hh_fix
      · exact TC.Thin.mem_aeModel_ofPerm hhA
    have hG_le : G ≤ H.comap (show Equiv.Perm (Fin 5) →* AEQ 5 from
        { toFun := fun g => mkQ 5 (Wr.ofPerm g)
          map_one' := by rw [ofPerm_one, map_one]
          map_mul' := fun g h => by rw [← ofPerm_mul, map_mul] }) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact hg1
      · exact hg2
      · exact hhh
    have hht : h t = u := by
      show Equiv.swap q r (Equiv.swap (ι 0) (ι 1) t) = u
      rw [Equiv.swap_apply_of_ne_of_ne ht0 ht1]
      exact swap_pair_other hqr htu
    have hcover' : ({p, ι 0, ι 1, t, u} : Finset (Fin 5)) = Finset.univ := by
      rw [show ({t, u} : Finset (Fin 5)) = {q, r} from htu, hcover]
    have hτ1_sq : (τ1 ^ 2) (ι 0) = p := by
      rw [pow_two, Equiv.Perm.mul_apply]
      have e1 : τ1 (ι 0) = ι 1 := by
        change (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)) (ι 0) = ι 1
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hpι1) (Ne.symm h01)]
      rw [e1]
      change (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)) (ι 1) = p
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    have hτ2_sq : (τ2 ^ 2) (ι 0) = t := by
      rw [pow_two, Equiv.Perm.mul_apply]
      have e1 : τ2 (ι 0) = ι 1 := by
        change (Equiv.swap t (ι 0) * Equiv.swap (ι 0) (ι 1)) (ι 0) = ι 1
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm ht1) (Ne.symm h01)]
      rw [e1]
      change (Equiv.swap t (ι 0) * Equiv.swap (ι 0) (ι 1)) (ι 1) = t
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_right]
    have horb : ∀ y : Fin 5, ∃ g ∈ G, g • ι 0 = y := by
      intro y
      have hy : y ∈ ({p, ι 0, ι 1, t, u} : Finset (Fin 5)) := by rw [hcover']; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl
      · exact ⟨τ1 ^ 2, G.pow_mem hτ1_mem 2, hτ1_sq⟩
      · exact ⟨1, G.one_mem, by simp⟩
      · refine ⟨τ1, hτ1_mem, ?_⟩
        change (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)) (ι 0) = ι 1
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
          Equiv.swap_apply_of_ne_of_ne (Ne.symm hpι1) (Ne.symm h01)]
      · exact ⟨τ2 ^ 2, G.pow_mem hτ2_mem 2, hτ2_sq⟩
      · exact ⟨h * τ2 ^ 2, G.mul_mem hh_mem (G.pow_mem hτ2_mem 2), by
          change (h * τ2 ^ 2) (ι 0) = y
          rw [Equiv.Perm.mul_apply, hτ2_sq]
          exact hht⟩
    have hG_trans : MulAction.IsPretransitive G (Fin 5) := by
      rw [MulAction.isPretransitive_iff]
      intro x y
      obtain ⟨gx, hgx, hx⟩ := horb x
      obtain ⟨gy, hgy, hy⟩ := horb y
      refine ⟨⟨gy * gx⁻¹, G.mul_mem hgy (G.inv_mem hgx)⟩, ?_⟩
      show (gy * gx⁻¹) • x = y
      calc (gy * gx⁻¹) • x = gy • (gx⁻¹ • x) := by rw [mul_smul]
        _ = gy • ι 0 := by rw [← hx]; simp
        _ = y := hy
    have hG_prim : MulAction.IsPreprimitive G (Fin 5) :=
      MulAction.IsPreprimitive.of_prime_card (by norm_num : Nat.Prime (Nat.card (Fin 5)))
    have hτ1_three : τ1.IsThreeCycle := by
      show (Equiv.swap p (ι 0) * Equiv.swap (ι 0) (ι 1)).IsThreeCycle
      rw [Equiv.swap_comm p (ι 0)]
      exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hpι0) h01 hpι1
    have hA5_le : alternatingGroup (Fin 5) ≤ G :=
      Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG_prim hτ1_three
        (Subgroup.subset_closure (by simp [G]))
    intro x hx
    obtain ⟨w, hwA, rfl⟩ := hx
    have hwvec : (∑ i, w.vec i) = 0 := hwA.1
    have hwperm : w.perm ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      exact hwA.2
    have hwpermH : mkQ 5 (Wr.ofPerm w.perm) ∈ H := by
      have := hG_le (hA5_le hwperm)
      simpa using this
    have hx_eq : mkQ 5 w = TL4.vbar 5 w.vec * mkQ 5 (Wr.ofPerm w.perm) := by
      rw [TL4.vbar, ← map_mul]
      congr 1
      exact TL4.eq_ofVec_mul_ofPerm w
    rw [hx_eq]
    exact H.mul_mem (hvbar_H w.vec hwvec) hwpermH


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.CaseB

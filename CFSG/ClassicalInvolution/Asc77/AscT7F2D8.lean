module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Cnt
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Bsub

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7F2

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


namespace Hyp25T

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem S_inf_K : (S : Subgroup G) ⊓ K = R :=
  h.hRsyl.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) (le_inf h.hRS h.hRsyl.1)

theorem S_inf_K' : (S : Subgroup G) ⊓ K' = R' :=
  h.hR'syl.2.2 _ inf_le_right (S.isPGroup'.to_le inf_le_left) (le_inf h.hR'S h.hR'syl.1)

theorem conj_twin {x : G} (hx : x⁻¹ * z * x = z) {J : Subgroup G} (hJ : J = K ∨ J = K') :
    conjSub x⁻¹ J = K ∨ conjSub x⁻¹ J = K' := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  have hzJ : IsUniqueInvolution J z := by rcases hJ with rfl | rfl; exacts [h.hz, h.hz']
  have hc : IsUniqueInvolution (conjSub x⁻¹ J) z := by
    have := hzJ.conj x⁻¹
    simpa [hx] using this
  have hmem : conjSub x⁻¹ J ∈ twinSet Ω K :=
    ⟨h.hΩ.conjInvariant x⁻¹ J hJΩ, z, h.hz, hc⟩
  rw [h.hs.twinSet_eq] at hmem
  exact hmem

theorem conj_twin_of_orderOf_four {J : Subgroup G} (hJ : J ∈ Ω) {v : G} (hvJ : v ∈ J)
    (hv4 : orderOf v = 4) {x : G} (hvS : x⁻¹ * v * x ∈ (S : Subgroup G)) :
    conjSub x⁻¹ J = K ∨ conjSub x⁻¹ J = K' := by
  have hJ' : conjSub x⁻¹ J ∈ Ω := h.hΩ.conjInvariant x⁻¹ J hJ
  by_contra hcon
  push Not at hcon
  have hnot : conjSub x⁻¹ J ∉ twinSet Ω K := by
    intro hmem
    rw [h.hs.twinSet_eq] at hmem
    rcases hmem with h1 | h1
    · exact hcon.1 h1
    · exact hcon.2 h1
  have hy : x⁻¹ * v * x ∈ conjSub x⁻¹ J := by
    have := conj_mem_conjSub (n := x⁻¹) hvJ
    simpa using this
  have hy4 : orderOf (x⁻¹ * v * x) = 4 := by
    have := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) v
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, hv4]
  exact T7ER.not_commute_of_orderOf_four h.hs h.hyp.hW h.hyp.hE4 hJ' hnot hy hy4
    (h.hyp.hzS _ hvS).symm

theorem conj_mem_R_or_R' {J : Subgroup G} (hJ : J = K ∨ J = K') {v : G} (hvJ : v ∈ J) {m : ℕ}
    (hm : 2 ≤ m) (hv : orderOf v = 2 ^ m) {x : G} (hvS : x⁻¹ * v * x ∈ (S : Subgroup G)) :
    x⁻¹ * v * x ∈ R ∨ x⁻¹ * v * x ∈ R' := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hdvd : 2 ^ m' ∣ orderOf v := by rw [hv]; exact pow_dvd_pow 2 (by omega)
  have hv4 : orderOf (v ^ 2 ^ m') = 4 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hv]
    have : 2 ^ (m' + 2) = 2 ^ m' * 4 := by ring
    rw [this, Nat.mul_div_cancel_left _ (by positivity)]
  have hvS' : x⁻¹ * v ^ 2 ^ m' * x ∈ (S : Subgroup G) := by
    have : x⁻¹ * v ^ 2 ^ m' * x = (x⁻¹ * v * x) ^ 2 ^ m' := by
      have := (conj_pow (a := x⁻¹) (b := v) (i := 2 ^ m')).symm
      simpa using this
    rw [this]
    exact (S : Subgroup G).pow_mem hvS _
  have hmem : v ^ 2 ^ m' ∈ J := J.pow_mem hvJ _
  have hc := h.conj_twin_of_orderOf_four hJΩ hmem hv4 hvS'
  have hy : x⁻¹ * v * x ∈ conjSub x⁻¹ J := by
    have := conj_mem_conjSub (n := x⁻¹) hvJ
    simpa using this
  rcases hc with hc | hc
  · left
    rw [hc] at hy
    exact h.S_inf_K ▸ ⟨hvS, hy⟩
  · right
    rw [hc] at hy
    exact h.S_inf_K' ▸ ⟨hvS, hy⟩


theorem eq_z_of_conj_mem_RR {x : G} (hu : x⁻¹ * z * x ∈ R ⊔ R') : x⁻¹ * z * x = z := by
  by_contra hne
  obtain ⟨r, hr, r', hr', hur⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hu
  have hu2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [h.hz.sq]; group
  have hu1 : x⁻¹ * z * x ≠ 1 := by
    intro h1
    apply h.hz.ne_one
    have : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
    rw [this, h1]; group
  have hrr' : r * r' = r' * r := h.hcomm r hr r' hr'
  have hsq : (r * r) * (r' * r') = 1 := by
    calc (r * r) * (r' * r') = (r * r') * (r * r') := by
          calc (r * r) * (r' * r') = r * (r * r') * r' := by group
            _ = r * (r' * r) * r' := by rw [hrr']
            _ = (r * r') * (r * r') := by group
      _ = 1 := by rw [← hur]; exact hu2
  have hw' : r * r = (r' * r')⁻¹ := eq_inv_of_mul_eq_one_left hsq
  have hwR : r * r ∈ R := R.mul_mem hr hr
  have hwR' : r * r ∈ R' := by rw [hw']; exact R'.inv_mem (R'.mul_mem hr' hr')
  have hw2 : (r * r) * (r * r) = 1 := by
    have hcard := h.inf_R_R'
    have hmem : r * r ∈ R ⊓ R' := ⟨hwR, hwR'⟩
    have := pow_card_eq_one' (G := ↥(R ⊓ R')) (x := ⟨r * r, hmem⟩)
    rw [hcard] at this
    have := congrArg Subtype.val this
    simpa [pow_two] using this
  by_cases hr2 : r * r = 1
  ·
    have hr1 : r = 1 ∨ r = z := h.hzR.unique r hr hr2
    have hr'2 : r' * r' = 1 := by rw [hr2, one_mul] at hsq; exact hsq
    have hr'1 : r' = 1 ∨ r' = z := h.hzR'.unique r' hr' hr'2
    have hzz : z * z = 1 := h.hz.sq
    rcases hr1 with rfl | rfl <;> rcases hr'1 with rfl | rfl
    · exact hu1 (by rw [hur]; simp)
    · exact hne (by rw [hur]; simp)
    · exact hne (by rw [hur]; simp)
    · exact hu1 (by rw [hur]; exact hzz)
  ·
    have hrz : r * r = z := by
      rcases h.hzR.unique (r * r) hwR hw2 with h1 | h1
      · exact absurd h1 hr2
      · exact h1
    have hr4 : orderOf r = 4 := by
      have h1 : ¬ r ^ 2 ^ 1 = 1 := by
        rw [pow_one, pow_two]; intro h1; exact hr2 h1
      have h2 : r ^ 2 ^ (1 + 1) = 1 := by
        have : r ^ 2 ^ (1 + 1) = (r * r) * (r * r) := by
          simp [pow_succ, mul_assoc]
        rw [this, hrz]; exact h.hz.sq
      have := orderOf_eq_prime_pow (p := 2) h1 h2
      simpa using this
    have hcomm : (x⁻¹ * z * x⁻¹⁻¹) * r = r * (x⁻¹ * z * x⁻¹⁻¹) := by
      simp only [inv_inv]
      rw [hur]
      calc r * r' * r = r * (r' * r) := by group
        _ = r * (r * r') := by rw [hrr']
        _ = r * (r * r') := rfl
    exact T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 h.hK h.hz (y := x⁻¹)
      (by simpa using hne) (h.hRsyl.1 hr) hr4 hcomm


theorem swap_P' {n : G} : t' * n * t'⁻¹ ∈ Psub S R' ↔ n ∈ Psub S R := by
  have := h.swap_P (n := t' * n * t'⁻¹)
  have e : t' * (t' * n * t'⁻¹) * t'⁻¹ = n := by
    calc t' * (t' * n * t'⁻¹) * t'⁻¹ = (t' * t') * n * (t' * t')⁻¹ := by group
      _ = n := by rw [h.ht'2]; group
  rw [e] at this
  exact this.symm

theorem bdata (h11 : C25_11 p f) (h16 : C25_16 p f)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) {a : G} (haC : a ∈ Csub S R)
    (haR' : a ∉ R') :
    BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a where
  hNS := fun x hx => (mem_Nsub.mp hx).1
  ht := h.ht'S
  htN := h.t'_not_mem_N
  htt := h.ht'2
  hS := fun s hs => h.S_cover hs
  hnorm := fun n hn => h.N_conj hn
  hP := h.P_le_N
  hP' := h.P'_le_N
  hPi := h.relIndex_P_eq h11 h16 hlt
  hPi' := (h.d8_of_lt h11 h16 hlt).1
  hswap := fun n _ => ⟨h.swap_P, h.swap_P'⟩
  haP := (le_sup_right : Csub S R ≤ Psub S R) haC
  haP' := by
    intro haP'
    have haP : a ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) haC
    exact haR' (h.mem_R'_of_mem_RR_of_mem_C h11 (h.P_inf_P' h11 ⟨haP, haP'⟩) haC)

theorem exists_a (h11 : C25_11 p f) (h16 : C25_16 p f)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) :
    ∃ a ∈ Csub S R, a ∉ R' ∧ a * a ≠ 1 := by
  have hc := (h.d8_of_lt h11 h16 hlt).2
  have hcard : Nat.card ↥(R') < Nat.card ↥(Csub S R) := by
    rw [h.card_C_eq, hc]
    have := Nat.card_pos (α := ↥R')
    omega
  have hex : ∃ a ∈ Csub S R, a ∉ R' := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show Csub S R ≤ R' from fun x hx => hcon x hx)
    omega
  obtain ⟨a₀, ha₀C, ha₀R'⟩ := hex
  by_contra hall
  push Not at hall
  have ha₀ : a₀ * a₀ = 1 := hall a₀ ha₀C ha₀R'
  have hinv : ∀ r ∈ R', a₀ * r * a₀ = r⁻¹ := by
    intro r hr
    have hmem : a₀ * r ∈ Csub S R := (Csub S R).mul_mem ha₀C (h.R'_le_C hr)
    have hnot : a₀ * r ∉ R' := fun hh => ha₀R' (by simpa using R'.mul_mem hh (R'.inv_mem hr))
    have h1 := hall _ hmem hnot
    calc a₀ * r * a₀ = (a₀ * r * a₀ * r) * r⁻¹ := by group
      _ = r⁻¹ := by rw [show a₀ * r * a₀ * r = (a₀ * r) * (a₀ * r) by group, h1]; group
  obtain ⟨x, hx, y, hy, hxy⟩ := h.hqR'.exists_not_commute
  apply hxy
  have h1 := hinv (x * y) (R'.mul_mem hx hy)
  have hx1 := hinv x hx
  have hy1 := hinv y hy
  have e : a₀ * (x * y) * a₀ = (a₀ * x * a₀) * (a₀ * y * a₀) := by
    calc a₀ * (x * y) * a₀ = a₀ * x * (a₀ * a₀) * y * a₀ := by rw [ha₀]; group
      _ = (a₀ * x * a₀) * (a₀ * y * a₀) := by
        calc a₀ * x * (a₀ * a₀) * y * a₀ = a₀ * x * a₀ * (a₀ * y * a₀) := by group
          _ = _ := rfl
  rw [e, hx1, hy1, mul_inv_rev] at h1
  have h2 : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := h1
  calc x * y = (y⁻¹ * x⁻¹)⁻¹ := by group
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [h2]
    _ = y * x := by group


theorem not_commute_conj_z {x : G} (hne : x⁻¹ * z * x ≠ z) {J : Subgroup G}
    (hJ : J = K ∨ J = K') {ρ : G} (hρ : ρ ∈ J) (hρ4 : orderOf ρ = 4) :
    (x⁻¹ * z * x) * ρ ≠ ρ * (x⁻¹ * z * x) := by
  have hJΩ : J ∈ Ω := by rcases hJ with rfl | rfl; exacts [h.hK, h.hK']
  have hzJ : IsUniqueInvolution J z := by rcases hJ with rfl | rfl; exacts [h.hz, h.hz']
  have := T7ER.not_commute_of_conj h.hs h.hyp.hW h.hyp.hE4 hJΩ hzJ (y := x⁻¹)
    (by simpa using hne) hρ hρ4
  simpa using this

theorem RR_le_N : R ⊔ R' ≤ Nsub S R := sup_le h.R_le_N h.R'_le_N

theorem RR_le_D {a : G} (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a) :
    R ⊔ R' ≤ d.D := fun _ hx =>
  ⟨h.RR_le_N hx, iff_of_true (h.RR_le_P hx) (h.RR_le_P' hx)⟩

theorem z_conj_mem_B {a : G} (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    {x : G} (hxS : x⁻¹ * z * x ∈ (S : Subgroup G)) : x⁻¹ * z * x ∈ d.B := by
  by_cases hy : x⁻¹ * z * x = z
  · rw [hy]
    exact d.D_le_B (h.RR_le_D d (le_sup_left (a := R) (b := R') h.hzR.mem))
  have hy2 : (x⁻¹ * z * x) * (x⁻¹ * z * x) = 1 := by
    calc (x⁻¹ * z * x) * (x⁻¹ * z * x) = x⁻¹ * (z * z) * x := by group
      _ = 1 := by rw [h.hz.sq]; group
  rcases h.S_cover hxS with hN | htN
  · by_cases hD : x⁻¹ * z * x ∈ d.D
    · exact d.D_le_B hD
    exfalso
    have hnot : ¬ (x⁻¹ * z * x ∈ Psub S R ↔ x⁻¹ * z * x ∈ Psub S R') := fun hi => hD ⟨hN, hi⟩
    by_cases hP : x⁻¹ * z * x ∈ Psub S R
    · obtain ⟨r, hr, m, hm, hrm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R) (B := Csub S R) (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hP
      obtain ⟨ρ, hρ, hρ4, hρr⟩ := AscE186.exists_orderOf_four_commute_of_isQuatSub h.hqR hr
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      refine h.not_commute_conj_z hy (Or.inl rfl) (h.hRsyl.1 hρ) hρ4 ?_
      rw [hrm]
      calc r * m * ρ = r * (m * ρ) := by group
        _ = r * (ρ * m) := by rw [hρm]
        _ = (r * ρ) * m := by group
        _ = (ρ * r) * m := by rw [hρr]
        _ = ρ * (r * m) := by group
    · have hP' : x⁻¹ * z * x ∈ Psub S R' := by
        by_contra hP'
        exact hnot ⟨fun hh => absurd hh hP, fun hh => absurd hh hP'⟩
      obtain ⟨r, hr, m, hm, hrm⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute
        (A := R') (B := Csub S R') (fun x hx y hy => (mem_Csub.mp hy).2 x hx) hP'
      obtain ⟨ρ, hρ, hρ4, hρr⟩ := AscE186.exists_orderOf_four_commute_of_isQuatSub h.hqR' hr
      have hρm : ρ * m = m * ρ := (mem_Csub.mp hm).2 ρ hρ
      refine h.not_commute_conj_z hy (Or.inr rfl) (h.hR'syl.1 hρ) hρ4 ?_
      rw [hrm]
      calc r * m * ρ = r * (m * ρ) := by group
        _ = r * (ρ * m) := by rw [hρm]
        _ = (r * ρ) * m := by group
        _ = (ρ * r) * m := by rw [hρr]
        _ = ρ * (r * m) := by group
  ·
    set n := t' * (x⁻¹ * z * x) with hn
    have hu : x⁻¹ * z * x = t' * n := by
      rw [hn, ← mul_assoc, h.ht'2, one_mul]
    have hn2 : t' * n * t'⁻¹ = n⁻¹ := by
      have h1 : (t' * n) * (t' * n) = 1 := by rw [← hu]; exact hy2
      rw [h.ht'inv]
      apply eq_inv_of_mul_eq_one_left
      calc t' * n * t' * n = (t' * n) * (t' * n) := by group
        _ = 1 := h1
    have hnD : n ∈ d.D := by
      refine ⟨htN, ?_⟩
      have hs := (d.hswap n htN).1
      rw [hn2] at hs
      rw [← hs]
      exact (inv_mem_iff (x := n) (H := Psub S R)).symm
    rw [hu]
    exact (d.B).mul_mem d.t_mem_B (d.D_le_B hnD)

end Hyp25T

end T7F2

end CFSG.ClassicalInvolution.Asc77

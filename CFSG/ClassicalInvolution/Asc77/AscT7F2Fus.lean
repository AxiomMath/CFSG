module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2D8
public import CFSG.ClassicalInvolution.Asc77.AscT7F2Trans

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7F2

section Aux

variable {G : Type} [Group G] [Finite G]

theorem fuse_aux {S : Sylow 2 G} {K₁ R₁ R₂ : Subgroup G} {y : G}
    (hyS : y ∈ (S : Subgroup G)) (hyN : y ∈ Subgroup.normalizer (K₁ : Set G))
    (hR₁ : IsSylow2In R₁ K₁) (hR₂ : IsSylow2In R₂ K₁) (hR₂S : (S : Subgroup G) ⊓ K₁ = R₂)
    (hc : ∀ r ∈ R₁, y * r = r * y) :
    ∃ k ∈ K₁, ∃ κ ∈ R₂, k * y * k⁻¹ = κ * y ∧ k * y * k⁻¹ ∈ (S : Subgroup G) ∧
      ∀ r ∈ R₂, r * (k * y * k⁻¹) = (k * y * k⁻¹) * r := by
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hyS)
  have hn : ∀ r ∈ R₂, y * r * y⁻¹ ∈ R₂ := by
    intro r hr
    rw [← hR₂S] at hr ⊢
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hyS hr.1)
      ((S : Subgroup G).inv_mem hyS), (Subgroup.mem_normalizer_iff.mp hyN r).mp hr.2⟩
  obtain ⟨k, hk, κ, hκ, hkey, hcomm⟩ :=
    exists_conj_mem_mul_of_centralizes hyN hy2 hR₁ hR₂ hc hn
  refine ⟨k, hk, κ, hκ, hkey, ?_, fun r hr => (hcomm r hr).symm⟩
  rw [hkey]
  have hκS : κ ∈ (S : Subgroup G) := by
    rw [← hR₂S] at hκ
    exact hκ.1
  exact (S : Subgroup G).mul_mem hκS hyS

end Aux

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


namespace Hyp25T

variable (h : Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t')

include h

theorem conj_K_of_mem_C {a : G} (ha : a ∈ Csub S R) : conjSub a K = K := by
  have hcz : a⁻¹⁻¹ * z * a⁻¹ = z := by
    have h1 := (mem_Csub.mp ha).2 z h.hzR.mem
    calc a⁻¹⁻¹ * z * a⁻¹ = a * z * a⁻¹ := by rw [inv_inv]
      _ = (z * a) * a⁻¹ := by rw [h1]
      _ = z := by group
  have hc := h.conj_twin hcz (J := K) (Or.inl rfl)
  rw [inv_inv] at hc
  rcases hc with hc | hc
  · exact hc
  · exfalso
    have hRa : conjSub a R = R := conjSub_eq_of_centralizes (mem_Csub.mp ha).2
    have hle : R ≤ (S : Subgroup G) ⊓ K' := by
      refine le_inf h.hRS ?_
      have := conjSub_mono (n := a) h.hRsyl.1
      rw [hRa, hc] at this
      exact this
    rw [h.S_inf_K'] at hle
    have heq : R = R' :=
      Subgroup.eq_of_le_of_card_ge hle (le_of_eq h.card_R_eq.symm)
    exact h.hne heq

variable (h11 : C25_11 p f)

include h11

theorem sq_mem_R' {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) : a * a ∈ R' := by
  have haN : a ∈ Nsub S R := h.C_le_N ha
  have haP : a ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) ha
  have h1 : a * a ∈ Psub S R' := by
    rw [mul_mem_iff_of_relIndex_two d.hPi' haN haN]
  have h2 : a * a ∈ Psub S R := (Psub S R).mul_mem haP haP
  have h3 : a * a ∈ R ⊔ R' := h.P_inf_P' h11 ⟨h2, h1⟩
  exact h.mem_R'_of_mem_RR_of_mem_C h11 h3 ((Csub S R).mul_mem ha ha)

omit h h11 in
theorem exists_pow_eq_z {R' : Subgroup G} {z : G} (hR' : IsUniqueInvolution R' z)
    (hR'2 : IsPGroup 2 R') {c : G} (hc : c ∈ R') (hc1 : c ≠ 1) :
    ∃ j : ℕ, c ^ (2 ^ j) = z := by
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥R')).mp hR'2 ⟨c, hc⟩
  have he' : orderOf c = 2 ^ e := by simpa using he
  obtain ⟨j, rfl⟩ : ∃ j, e = j + 1 := by
    refine ⟨e - 1, ?_⟩
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · exfalso
      subst h0
      exact hc1 (orderOf_eq_one_iff.mp (by simpa using he'))
    · omega
  refine ⟨j, ?_⟩
  have hsq : c ^ (2 ^ j) * c ^ (2 ^ j) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← he']
    exact pow_orderOf_eq_one c
  rcases hR'.unique (c ^ (2 ^ j)) (R'.pow_mem hc _) hsq with h1 | h1
  · exfalso
    have := orderOf_dvd_of_pow_eq_one h1
    rw [he'] at this
    have h2 : 2 ^ (j + 1) ≤ 2 ^ j := Nat.le_of_dvd (by positivity) this
    have h3 : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · exact h1

omit h h11 in
theorem exists_orderOf_eq {S : Sylow 2 G} {a : G} (ha : a ∈ (S : Subgroup G)) :
    ∃ e : ℕ, orderOf a = 2 ^ e := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf (p := 2) (G := ↥(S : Subgroup G))).mp
    S.isPGroup' ⟨a, ha⟩
  exact ⟨m, by simpa using hm⟩

omit h11 in
theorem exists_fuse {a : G} (ha : a ∈ Csub S R) {x : G} (hx : x⁻¹ * z * x = z)
    (hy : x⁻¹ * a * x ∈ (S : Subgroup G)) :
    ∃ w : G, ∃ κ ∈ R ⊔ R', w⁻¹ * a * w = κ * (x⁻¹ * a * x) ∧
      (w⁻¹ * a * w ∈ Csub S R ∨ w⁻¹ * a * w ∈ Csub S R') := by
  have hK := h.conj_K_of_mem_C ha
  have hyN : x⁻¹ * a * x ∈ Subgroup.normalizer ((conjSub x⁻¹ K : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul,
      show x⁻¹ * a * x * x⁻¹ = x⁻¹ * a by group, conjSub_mul, hK]
  have hR₁ : IsSylow2In (conjSub x⁻¹ R) (conjSub x⁻¹ K) := h.hRsyl.conj x⁻¹
  have hR₁c : ∀ r ∈ conjSub x⁻¹ R, (x⁻¹ * a * x) * r = r * (x⁻¹ * a * x) := by
    intro r hr
    have hr' : x * r * x⁻¹ ∈ R := by
      have := mem_conjSub_iff.mp hr
      simpa using this
    have h1 := (mem_Csub.mp ha).2 _ hr'
    calc (x⁻¹ * a * x) * r = x⁻¹ * (a * (x * r * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * r * x⁻¹) * a) * x := by rw [h1]
      _ = r * (x⁻¹ * a * x) := by group
  rcases h.conj_twin hx (J := K) (Or.inl rfl) with hJ | hJ
  · rw [hJ] at hyN hR₁
    obtain ⟨k, hk, κ, hκ, hkey, hkS, hkc⟩ :=
      fuse_aux hy hyN hR₁ h.hRsyl h.S_inf_K hR₁c
    refine ⟨x * k⁻¹, κ, (le_sup_left : R ≤ R ⊔ R') hκ, ?_, Or.inl ?_⟩
    · rw [← hkey]; group
    · refine mem_Csub.mpr ⟨?_, ?_⟩
      · convert hkS using 1; group
      · intro r hr
        have := hkc r hr
        convert this using 2 <;> group
  · rw [hJ] at hyN hR₁
    obtain ⟨k, hk, κ, hκ, hkey, hkS, hkc⟩ :=
      fuse_aux hy hyN hR₁ h.hR'syl h.S_inf_K' hR₁c
    refine ⟨x * k⁻¹, κ, (le_sup_right : R' ≤ R ⊔ R') hκ, ?_, Or.inr ?_⟩
    · rw [← hkey]; group
    · refine mem_Csub.mpr ⟨?_, ?_⟩
      · convert hkS using 1; group
      · intro r hr
        have := hkc r hr
        convert this using 2 <;> group

include h11

theorem conj_not_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (ha2 : a * a ≠ 1) {x : G} (hy : x⁻¹ * a * x ∈ (S : Subgroup G)) :
    x⁻¹ * a * x ∉ d.B := by
  intro hyB
  have haS : a ∈ (S : Subgroup G) := (mem_Csub.mp ha).1
  have hc : a * a ∈ R' := h.sq_mem_R' h11 d ha
  obtain ⟨j, hzj⟩ := exists_pow_eq_z h.hzR' (h.hR'syl.2.1) hc ha2
  have hyy : (x⁻¹ * a * x) * (x⁻¹ * a * x) ∈ R ⊔ R' := by
    obtain ⟨h1, h2⟩ := d.mul_self_mem hyB
    exact h.P_inf_P' h11 ⟨h1, h2⟩
  have hxz : x⁻¹ * z * x = z := by
    apply h.eq_z_of_conj_mem_RR
    rw [← hzj]
    have e : x⁻¹ * (a * a) ^ (2 ^ j) * x = ((x⁻¹ * a * x) * (x⁻¹ * a * x)) ^ (2 ^ j) := by
      have := (conj_pow (a := x⁻¹) (b := a * a) (i := 2 ^ j)).symm
      rw [inv_inv] at this
      rw [this]
      congr 1
      group
    rw [e]
    exact (R ⊔ R').pow_mem hyy _
  obtain ⟨w, κ, hκ, hwk, hw⟩ := h.exists_fuse ha hxz hy
  have hy'B : w⁻¹ * a * w ∈ d.B := by
    rw [hwk]
    exact d.B.mul_mem (d.D_le_B (h.RR_le_D d hκ)) hyB
  have hy'N : w⁻¹ * a * w ∈ Nsub S R := by
    rcases hw with hw | hw
    exacts [h.C_le_N hw, h.C'_le_N hw]
  have hy'D := d.mem_D_of_mem_B_of_mem_N hy'B hy'N
  have hy'RR : w⁻¹ * a * w ∈ R ⊔ R' := by
    rcases hw with hw | hw
    · have hP : w⁻¹ * a * w ∈ Psub S R := (le_sup_right : Csub S R ≤ Psub S R) hw
      exact h.P_inf_P' h11 ⟨hP, hy'D.2.mp hP⟩
    · have hP' : w⁻¹ * a * w ∈ Psub S R' := (le_sup_right : Csub S R' ≤ Psub S R') hw
      exact h.P_inf_P' h11 ⟨hy'D.2.mpr hP', hP'⟩
  obtain ⟨e, he⟩ := exists_orderOf_eq haS
  have he2 : 2 ≤ e := by
    by_contra hlt
    push Not at hlt
    apply ha2
    have hdvd : orderOf a ∣ 2 := by
      rw [he]
      calc 2 ^ e ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
        _ = 2 := by norm_num
    have := orderOf_dvd_iff_pow_eq_one.mp hdvd
    simpa [pow_two] using this
  have hord : orderOf (w⁻¹ * a * w) = 2 ^ e := by
    have := MulEquiv.orderOf_eq (MulAut.conj w⁻¹) a
    simp only [MulAut.conj_apply, inv_inv] at this
    rw [this, he]
  have hback : (w⁻¹)⁻¹ * (w⁻¹ * a * w) * w⁻¹ = a := by group
  have hmem : a ∈ R ∨ a ∈ R' := by
    rcases hw with hw | hw
    · have hv : w⁻¹ * a * w ∈ R' := h.mem_R'_of_mem_RR_of_mem_C h11 hy'RR hw
      have := h.conj_mem_R_or_R' (J := K') (Or.inr rfl) (h.hR'syl.1 hv) he2 hord (x := w⁻¹)
        (by rw [hback]; exact haS)
      rwa [hback] at this
    · have hv : w⁻¹ * a * w ∈ R := h.mem_R_of_mem_RR_of_mem_C' h11 hy'RR hw
      have := h.conj_mem_R_or_R' (J := K) (Or.inl rfl) (h.hRsyl.1 hv) he2 hord (x := w⁻¹)
        (by rw [hback]; exact haS)
      rwa [hback] at this
  have haP' : a ∈ Psub S R' := by
    rcases hmem with hm | hm
    · exact h.RR_le_P' ((le_sup_left : R ≤ R ⊔ R') hm)
    · exact h.RR_le_P' ((le_sup_right : R' ≤ R ⊔ R') hm)
  exact d.haP' haP'

theorem pow_conj_mem_B {a : G}
    (d : BData (S : Subgroup G) (Nsub S R) (Psub S R) (Psub S R') t' a)
    (ha : a ∈ Csub S R) (i : ℕ) {x : G}
    (hx : x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ (S : Subgroup G)) :
    x⁻¹ * a ^ (2 ^ (i + 1)) * x ∈ d.B := by
  have hc : a * a ∈ R' := h.sq_mem_R' h11 d ha
  have hcpow : a ^ (2 ^ (i + 1)) ∈ R' := by
    have e : a ^ (2 ^ (i + 1)) = (a * a) ^ (2 ^ i) := by
      rw [pow_succ', pow_mul, pow_two]
    rw [e]
    exact R'.pow_mem hc _
  set c := a ^ (2 ^ (i + 1)) with hcdef
  obtain ⟨m, hm⟩ := exists_orderOf_eq (S := S) (h.hR'S hcpow)
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have : c = 1 := orderOf_eq_one_iff.mp (by simpa using hm)
      rw [this]
      simp
    · have hc2 : c * c = 1 := by
        have := pow_orderOf_eq_one c
        rw [hm] at this
        simpa [pow_two] using this
      have hcz : c = z := by
        rcases h.hzR'.unique c hcpow hc2 with h1 | h1
        · exfalso
          rw [h1, orderOf_one] at hm
          norm_num at hm
        · exact h1
      rw [hcz] at hx ⊢
      exact h.z_conj_mem_B d hx
  · have := h.conj_mem_R_or_R' (J := K') (Or.inr rfl) (h.hR'syl.1 hcpow) hm2 hm hx
    rcases this with h1 | h1
    · exact d.D_le_B (h.RR_le_D d ((le_sup_left : R ≤ R ⊔ R') h1))
    · exact d.D_le_B (h.RR_le_D d ((le_sup_right : R' ≤ R ⊔ R') h1))

theorem false_of_d8 (h16 : C25_16 p f)
    (hlt : 2 * Nat.card ↥(R ⊔ R') < Nat.card ↥(Nsub S R)) : False := by
  obtain ⟨a, haC, haR', ha2⟩ := h.exists_a h11 h16 hlt
  have d := h.bdata h11 h16 hlt haC haR'
  obtain ⟨x, hx, y, hy, hxy⟩ := h.hqR.exists_not_commute
  refine T7F2.false_of_fusion (hom_eq_one_of_isSimpleGroup ⟨x, y, hxy⟩) S d.B d.relIndex_B a
    (mem_Csub.mp haC).1 (fun x hx => h.conj_not_mem_B h11 d haC ha2 hx)
    (fun i x hx => h.pow_conj_mem_B h11 d haC i hx)

end Hyp25T

end T7F2

end CFSG.ClassicalInvolution.Asc77

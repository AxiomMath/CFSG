module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltY
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8AltPerm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section SubAct

variable {A : Type} [Group A]

@[expose] noncomputable def subAct (M J : Subgroup A) (hn : M ≤ normalizer (J : Set A)) :
    ↥M →* MulAut (↥J ⧸ center ↥J) :=
  (yAct J).comp (Subgroup.inclusion hn)

theorem subAct_ker_mem {M J : Subgroup A} [Group.IsPerfect ↥J] (hn : M ≤ normalizer (J : Set A))
    (x : ↥M) : x ∈ (subAct M J hn).ker ↔ (x : A) ∈ centralizer (J : Set A) := by
  rw [MonoidHom.mem_ker]
  exact yAct_eq_one_iff J ⟨(x : A), hn x.2⟩

theorem card_ker_subAct {M J : Subgroup A} [Group.IsPerfect ↥J]
    (hn : M ≤ normalizer (J : Set A)) :
    Nat.card (subAct M J hn).ker = Nat.card ↥(M ⊓ centralizer (J : Set A)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : A), x.1.2, (subAct_ker_mem hn x.1).1 x.2⟩
      invFun := fun y => ⟨⟨(y : A), y.2.1⟩, (subAct_ker_mem hn _).2 y.2.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }

theorem card_eq_ker_mul_range {M J : Subgroup A} [Group.IsPerfect ↥J] [Finite A]
    (hn : M ≤ normalizer (J : Set A)) :
    Nat.card ↥M = Nat.card ↥(M ⊓ centralizer (J : Set A)) * Nat.card (subAct M J hn).range := by
  set f := subAct M J hn with hf
  rw [← card_ker_subAct hn, Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

theorem card_range_dvd {M J : Subgroup A} [Finite A] (hn : M ≤ normalizer (J : Set A)) :
    Nat.card (subAct M J hn).range ∣ Nat.card (MulAut (↥J ⧸ center ↥J)) :=
  Subgroup.card_subgroup_dvd_card _

theorem card_le_ker_mul [Finite A] {Sb J : Subgroup A} [Group.IsPerfect ↥J]
    (hn : Sb ≤ normalizer (J : Set A)) (h2 : IsPGroup 2 ↥Sb) :
    Nat.card ↥Sb ≤ Nat.card ↥(Sb ⊓ centralizer (J : Set A)) *
      2 ^ (Nat.card (MulAut (↥J ⧸ center ↥J))).factorization 2 := by
  set f := subAct Sb J hn with hf
  have hrange2 : IsPGroup 2 ↥f.range :=
    h2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨k, hk⟩ := hrange2.exists_card_eq
  have hdvd : Nat.card f.range ∣ Nat.card (MulAut (↥J ⧸ center ↥J)) := card_range_dvd hn
  have hpos : 0 < Nat.card (MulAut (↥J ⧸ center ↥J)) := Nat.card_pos
  have hle : k ≤ (Nat.card (MulAut (↥J ⧸ center ↥J))).factorization 2 := by
    rw [hk] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hpos.ne').1 hdvd
  rw [card_eq_ker_mul_range hn, hk]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hle)

end SubAct

theorem card_mulAut_of_alt (n : ℕ) (hn : 5 ≤ n) (hn6 : n ≠ 6) {Y : Type} [Group Y]
    (e : Y ≃* alternatingGroup (Fin n)) : Nat.card (MulAut Y) = n.factorial := by
  have h1 : Nat.card (MulAut Y) = Nat.card (Equiv.Perm (Fin n)) :=
    Nat.card_congr (autTransport hn hn6 e).toEquiv
  rw [h1, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

section Alt7

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb J : Subgroup A}

theorem alt7_false (hfr : AFrame A zb Sb Vb) (hJ : IsComponent J)
    (hsw : Sb ≤ normalizer (J : Set A)) (hzc : Nat.card ↥(Sb ⊓ centralizer (J : Set A)) ≤ 2)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 7)) : False := by
  have : Group.IsPerfect ↥J := hJ.1.1
  have h2 : IsPGroup 2 ↥Sb := hfr.sylow.isPGroup
  have hle := card_le_ker_mul hsw h2
  rw [card_mulAut_of_alt 7 (by norm_num) (by norm_num) e,
    show (Nat.factorial 7).factorization 2 = 4 by
      rw [show Nat.factorial 7 = 2 ^ 4 * 315 by decide]
      exact factorization_two_pow_mul_odd 4 315 (by norm_num),
    hfr.card] at hle
  have := Nat.mul_le_mul_right (2 ^ 4) hzc
  omega

end Alt7

section Alt11

variable {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}

theorem pRank_two_subgroup_le {X : Type} [Group X] [Finite X] (F : Subgroup X) :
    pRank 2 ↥F ≤ pRank 2 X := by
  rw [SectionRank.pRank_eq_open_pRank_top, SectionRank.pRank_eq_open_pRank_top]
  exact (SectionRank.pRank_le_map one_lt_two F.subtype F.subtype_injective ⊤).trans
    (SectionRank.pRank_mono one_lt_two le_top)

theorem alt11_false_of_ker_bot (hfr : AFrame A zb Sb Vb) {J : Subgroup A} [Group.IsPerfect ↥J]
    (hsw : Sb ≤ normalizer (J : Set A)) (hC : Sb ⊓ centralizer (J : Set A) = ⊥)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 11)) : False := by
  set Φ := autTransport (show 5 ≤ 11 by norm_num) (show (11 : ℕ) ≠ 6 by norm_num) e with hΦ
  set Θ : ↥Sb →* Equiv.Perm (Fin 11) := Φ.toMonoidHom.comp (subAct Sb J hsw) with hΘ
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : subAct Sb J hsw x = 1 := Φ.injective (by simpa [hΘ] using hx)
    have h2 : (x : A) ∈ centralizer (J : Set A) := (subAct_ker_mem hsw x).1 h1
    have h3 : (x : A) ∈ Sb ⊓ centralizer (J : Set A) := ⟨x.2, h2⟩
    rw [hC, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have e1 : ↥Sb ≃* ↥Θ.range := MonoidHom.ofInjective hinj
  have hcard : Nat.card ↥Θ.range = 2 ^ 8 := by
    rw [← hfr.card]
    exact Nat.card_congr e1.toEquiv.symm
  have h5 : 5 ≤ pRank 2 ↥Θ.range := five_le_pRank_of_sylow_perm_eleven (by rw [hcard])
  have h6 : pRank 2 ↥Sb = pRank 2 ↥Θ.range := CFSG.GH74.GLS.IVK.Lifted.pRank_two_congr e1
  have h7 : pRank 2 ↥Sb ≤ pRank 2 A := pRank_two_subgroup_le Sb
  have := hfr.rank_hi
  omega

theorem alt11_eq_top (hfr : AFrame A zb Sb Vb) {J : Subgroup A} (hJ : IsComponent J)
    (hJn : J.Normal) (hC : centralizer (J : Set A) = Subgroup.zpowers zb)
    (hZ : Nat.card ↥(center ↥J) = 2)
    (e : (↥J ⧸ center ↥J) ≃* alternatingGroup (Fin 11)) : J = ⊤ := by
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsw : (⊤ : Subgroup A) ≤ normalizer (J : Set A) := by
    rw [Subgroup.normalizer_eq_top]
  have hmul := card_eq_ker_mul_range hsw
  have hker : Nat.card ↥((⊤ : Subgroup A) ⊓ centralizer (J : Set A)) = 2 := by
    rw [top_inf_eq, hC, Nat.card_zpowers, hfr.zb_ord]
  have hdvd := card_range_dvd hsw
  rw [card_mulAut_of_alt 11 (by norm_num) (by norm_num) e] at hdvd
  set r := Nat.card (subAct (⊤ : Subgroup A) J hsw).range with hr
  have hr0 : r ≠ 0 := Nat.card_pos.ne'
  rw [hker, Subgroup.card_top] at hmul
  have hv : (Nat.card A).factorization 2 = 8 := by
    have h1 := hfr.sylow.card_eq
    rw [hfr.card, Subgroup.card_top] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hvr : r.factorization 2 = 7 := by
    rw [hmul, Nat.factorization_mul (by norm_num) hr0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two] at hv
    omega
  have hne : r ≠ Nat.factorial 11 := by
    intro h
    rw [h, show Nat.factorial 11 = 2 ^ 8 * 155925 by decide,
      factorization_two_pow_mul_odd 8 155925 (by norm_num)] at hvr
    omega
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · exact absurd (hk.trans (mul_zero r)) (Nat.factorial_ne_zero 11)
      · exact absurd (by simpa using hk.symm) hne
    · exact h
  have hA : Nat.card A ≤ Nat.factorial 11 := by
    rw [hmul, hk]
    nlinarith
  have hJcard : Nat.card ↥J = Nat.factorial 11 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥J), hZ,
      Nat.card_congr e.toEquiv, card_alt_fin (by norm_num)]
    exact Nat.div_mul_cancel (by decide)
  exact Subgroup.eq_top_of_card_eq J (le_antisymm (Subgroup.card_le_card_group J)
    (hJcard ▸ hA))

end Alt11

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

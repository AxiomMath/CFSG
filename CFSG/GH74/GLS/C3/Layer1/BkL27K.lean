module

public import CFSG.GH74.GLS.C3.Layer1.Back112Kfacts
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma15a

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter

theorem subsingleton_ringEquiv_of_card_prime {F : Type} [Field F] [Finite F] {p : ℕ}
    [Fact p.Prime] (h : Nat.card F = p) : Subsingleton (F ≃+* F) := by
  have : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = p := by rw [← Nat.card_eq_fintype_card]; exact h
  let eK : ZMod p ≃+* F := ZMod.ringEquivOfPrime F (Fact.out) hc
  refine ⟨fun σ τ => ?_⟩
  have h1 : σ.toRingHom.comp eK.toRingHom = τ.toRingHom.comp eK.toRingHom :=
    RingHom.ext_zmod _ _
  ext a
  obtain ⟨n, rfl⟩ := eK.surjective a
  have := congrArg (fun f : ZMod p →+* F => f n) h1
  simpa using this

theorem mem_innDiagSub_of_card_prime {F : Type} [Field F] [Finite F] {K : Type} [Group K]
    (e : K ≃* L2 F) {p : ℕ} [Fact p.Prime] (h : Nat.card F = p) (ρ : MulAut K) :
    ρ ∈ innDiagSub e := by
  have : Subsingleton (F ≃+* F) := subsingleton_ringEquiv_of_card_prime h
  have hbot : fieldAutSub e = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 ?_
    rintro _ ⟨σ, rfl⟩
    rw [Subsingleton.elim σ 1, map_one]
  have htop := innDiagSub_sup_fieldAutSub e
  rw [hbot, sup_bot_eq] at htop
  rw [htop]
  exact Subgroup.mem_top ρ

theorem two_mul_card_of_hasL2Model_eq {H : Type} [Group H] {q : ℕ} (hq : Odd q)
    (h : HasL2Model H (fun r => r = q)) : 2 * Nat.card H = q * (q ^ 2 - 1) := by
  obtain ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e⟩⟩ :=
    C3.Layer1.Back.exists_psl_model_of_hasL2Model h
  have hFq : Nat.card F = q := by rw [hcard, hP]
  have hpodd : Odd p := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    exact (Nat.not_even_iff_odd.2 hq) (hP ▸ (Nat.even_pow).2 ⟨hne, by omega⟩)
  have hodd : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, hcard⟩
  have h1 : Nat.card H = q * (q ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, psl2_card_formula F hodd, hFq]
  have hev : Even (q * (q ^ 2 - 1)) := by
    have : Even (q ^ 2 - 1) := Nat.Odd.sub_odd hq.pow (odd_one)
    exact this.mul_left q
  rw [h1]
  exact Nat.mul_div_cancel' hev.two_dvd

theorem card_eq_of_hasL2Model_seven {H : Type} [Group H] (h : HasL2Model H (fun r => r = 7)) :
    Nat.card H = 168 := by
  have := two_mul_card_of_hasL2Model_eq (by decide : Odd 7) h
  norm_num at this
  omega

theorem card_eq_of_hasL2Model_five {H : Type} [Group H] (h : HasL2Model H (fun r => r = 5)) :
    Nat.card H = 60 := by
  have := two_mul_card_of_hasL2Model_eq (by decide : Odd 5) h
  norm_num at this
  omega

theorem xu_seven_outer {H : Type} [Group H] [Finite H] (h : HasL2Model H (fun r => r = 7))
    {ρ : MulAut H} (hρ : ρ ∉ (MulAut.conj : H →* MulAut H).range) (hρ2 : ρ ^ 2 = 1) :
    3 ≤ Nat.card ↥(xu ρ) ∧ Odd (Nat.card ↥(xu ρ)) := by
  obtain ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e⟩⟩ :=
    C3.Layer1.Back.exists_psl_model_of_hasL2Model h
  have hF7 : Nat.card F = 7 := by rw [hcard, hP]
  let e' : H ≃* L2 F := e.trans (L2.equivPSL F).symm
  have hL : L2Field F := ⟨by rw [hF7]; decide, by rw [hF7]; decide⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdiag : ρ ∈ innDiagSub e' := mem_innDiagSub_of_card_prime e' hF7 ρ
  have hρ1 : ρ ≠ 1 := fun h1 => hρ (h1 ▸ Subgroup.one_mem _)
  have hord : orderOf ρ = 2 := orderOf_eq_prime hρ2 hρ1
  obtain ⟨-, hodd, h3, -⟩ := Proofs2.xu_outer_data hL e' hdiag hρ hord
  exact ⟨h3, hodd⟩

end CFSG.GH74.GLS.C3.Layer1.Bk

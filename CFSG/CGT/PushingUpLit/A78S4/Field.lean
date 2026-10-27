module

public import CFSG.CGT.PushingUpLit.A78S4.H1

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e) (hZ : Z ≠ ⊥)

include P hZ

theorem exists_involution (hTJ : T ≠ V ⊔ W) : ∃ f ∈ T, f ∉ V ⊔ W ∧ f * f = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  have h := P.side₁
  obtain ⟨t₁, ht₁, ht₁J⟩ : ∃ t ∈ T, t ∉ V ⊔ W := by
    by_contra hcon
    push Not at hcon
    exact hTJ (le_antisymm hcon P.side₁.J_le_T)
  have : Finite (GaloisField 2 e ≃+* GaloisField 2 e) :=
    Finite.of_injective (fun σ : GaloisField 2 e ≃+* GaloisField 2 e => (σ : GaloisField 2 e →
      GaloisField 2 e)) fun _ _ hσ => RingEquiv.ext (congrFun hσ)
  set R := (P.side₁.sigHom D).range with hR
  have hR2 : IsPGroup 2 R := P.side₁.pT.of_surjective (P.side₁.sigHom D).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have hRne : Nat.card R ≠ 1 := by
    intro h1
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem : P.side₁.sigHom D ⟨t₁, ht₁⟩ ∈ R := ⟨⟨t₁, ht₁⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, S4Side.sigHom_apply] at hmem
    exact ht₁J ((P.side₁.sig_eq_one_iff D ⟨t₁, ht₁⟩).1 hmem)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hR2)
  have hk0 : k ≠ 0 := by rintro rfl; exact hRne (by simpa using hk)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := R) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  obtain ⟨⟨x, hx⟩, hgx⟩ := g.2
  set σ := P.side₁.sig D ⟨x, hx⟩ with hσ
  have hgσ : (g : GaloisField 2 e ≃+* GaloisField 2 e) = σ := by rw [← hgx]; rfl
  have hσord : orderOf σ = 2 := by rw [← hgσ, Subgroup.orderOf_coe, hg]
  have hσ2 : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hσord, pow_two] at this
    exact this
  have hσ1 : σ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hσord; norm_num at hσord
  have hxJ : x ∉ V ⊔ W := fun hxJ => hσ1 ((P.side₁.sig_eq_one_iff D ⟨x, hx⟩).2 hxJ)
  have hxx : x * x ∈ V ⊔ W := by
    have h1 : P.side₁.sig D ⟨x * x, mul_mem hx hx⟩ = 1 := by
      have : (⟨x * x, mul_mem hx hx⟩ : ↥T) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
      rw [this, ← S4Side.sigHom_apply, map_mul, S4Side.sigHom_apply, ← hσ, hσ2]
    exact (P.side₁.sig_eq_one_iff D _).1 h1
  obtain ⟨ν, hν⟩ := fr.b_conj hx
  have hxj_mem : ∀ j ∈ V ⊔ W, x * j * x⁻¹ ∈ V ⊔ W := by
    intro j hj
    obtain ⟨v, hv, w, hw, rfl⟩ := (P.side₁.jst.mem_sup_iff).1 hj
    have e1 : x * (v * w) * x⁻¹ = (x * v * x⁻¹) * (x * w * x⁻¹) := by group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_left (conj_mem_of_mem_normalizer (P.side₁.T_le_V hx) hv))
      (Subgroup.mem_sup_right (conj_mem_of_mem_normalizer (P.side₁.T_le_W hx) hw))
  have hs : ν * σ (fr.b (x * x)) = fr.b (x * x) := by
    have h1 := hν _ hxx
    rw [show x * (x * x) * x⁻¹ = x * x by group] at h1
    exact h1.symm
  obtain ⟨r, hr⟩ := exists_add_mul_eq σ hσ1 hσ2 hs
  obtain ⟨j, hj, -, hjr⟩ := fr.surj_ab 0 r
  set x' := x * j with hx'
  have hx'T : x' ∈ T := mul_mem hx (P.side₁.J_le_T hj)
  have hx'J : x' ∉ V ⊔ W := fun h1 => hxJ (by
    have e : x = x' * j⁻¹ := by rw [hx']; group
    rw [e]
    exact mul_mem h1 (inv_mem hj))
  have hx'V : x' * x' ∈ V := by
    have hxj := hxj_mem j hj
    have e1 : x' * x' = (x * j * x⁻¹) * (x * x) * j := by rw [hx']; group
    have hJ2 : x' * x' ∈ V ⊔ W := by rw [e1]; exact mul_mem (mul_mem hxj hxx) hj
    rw [fr.mem_V_iff_b hJ2, e1, fr.b_mul (mul_mem hxj hxx) hj, fr.b_mul hxj hxx, hν _ hj, hjr]
    linear_combination -hr + CharTwo.add_self_eq_zero (r + ν * σ r)
  have hfix : x' * (x' * x') * x'⁻¹ = x' * x' := by group
  obtain ⟨u, huV, hu⟩ := P.exists_mul_conj_eq hZ hx'T hx'J hx'V hx'V hfix
  have hau : x' * u * x'⁻¹ ∈ V := conj_mem_of_mem_normalizer (P.side₁.T_le_V hx'T) huV
  refine ⟨x' * u, mul_mem hx'T (P.side₁.V_le_T huV), fun h1 => hx'J (by
    simpa using mul_mem h1 (inv_mem (Subgroup.mem_sup_left huV))), ?_⟩
  have hcomm : u * (x' * u * x'⁻¹) = (x' * u * x'⁻¹) * u :=
    (P.side₁.jst.abelian_V u huV _ hau).eq
  calc x' * u * (x' * u) = (x' * u * x'⁻¹) * (x' * x') * u := by group
    _ = (x' * u * x'⁻¹) * (u * (x' * u * x'⁻¹)) * u := by rw [hu]
    _ = (x' * u * x'⁻¹) * ((x' * u * x'⁻¹) * u) * u := by rw [hcomm]
    _ = ((x' * u * x'⁻¹) * (x' * u * x'⁻¹)) * (u * u) := by group
    _ = 1 := by rw [P.side₁.jst.sq_V _ hau, P.side₁.jst.sq_V _ huV, mul_one]

theorem inv_conj {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1) {x : G} (hx : x ∈ T)
    (hxJ : x ∉ V ⊔ W) (hxx : x * x = 1) : ∃ k ∈ V ⊔ W, k⁻¹ * f * k = x := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hmJ : f * x ∈ V ⊔ W := P.side₁.mul_mem_J_of_involutions D hf hfJ hff hx hxJ hxx
  set m := f * x with hm
  have hxm : x = f * m := by rw [hm, ← mul_assoc, hff, one_mul]
  obtain ⟨ν, hν⟩ := fr.b_conj hf
  set σ := P.side₁.sig D ⟨f, hf⟩ with hσ
  have hfJn : ∀ j ∈ V ⊔ W, f * j * f⁻¹ ∈ V ⊔ W := by
    intro j hj
    obtain ⟨v, hv, w, hw, rfl⟩ := (P.side₁.jst.mem_sup_iff).1 hj
    have e1 : f * (v * w) * f⁻¹ = (f * v * f⁻¹) * (f * w * f⁻¹) := by group
    rw [e1]
    exact mul_mem (Subgroup.mem_sup_left (conj_mem_of_mem_normalizer (P.side₁.T_le_V hf) hv))
      (Subgroup.mem_sup_right (conj_mem_of_mem_normalizer (P.side₁.T_le_W hf) hw))
  have hfm : f * m * f⁻¹ = m⁻¹ := by
    have h1 : f * m * (f * m) = 1 := by rw [← hxm]; exact hxx
    rw [hfi]
    calc f * m * f = f * m * (f * m) * m⁻¹ := by group
      _ = m⁻¹ := by rw [h1, one_mul]
  have hbinv : ∀ j ∈ V ⊔ W, fr.b j⁻¹ = fr.b j := by
    intro j hj
    have h1 := fr.b_mul hj (inv_mem hj)
    rw [mul_inv_cancel, fr.b_of_mem_V (Subgroup.one_mem _)] at h1
    have := eq_neg_of_add_eq_zero_right h1.symm
    rw [this, CharTwo.neg_eq]
  have hs : ν * σ (fr.b m) = fr.b m := by
    have h1 := hν m hmJ
    rw [hfm, hbinv m hmJ] at h1
    exact h1.symm
  obtain ⟨r, hr⟩ := exists_add_mul_eq σ (P.side₁.sig_ne_one D hf hfJ) (P.side₁.sig_sq D hf hff) hs
  obtain ⟨k₁, hk₁J, -, hk₁r⟩ := fr.surj_ab 0 r
  have hfk : f * k₁⁻¹ * f⁻¹ ∈ V ⊔ W := hfJn _ (inv_mem hk₁J)
  set m' := (f * k₁⁻¹ * f⁻¹) * k₁ with hm'
  have hm'J : m' ∈ V ⊔ W := mul_mem hfk hk₁J
  have hbm' : fr.b m' = fr.b m := by
    rw [hm', fr.b_mul hfk hk₁J, hν _ (inv_mem hk₁J), hbinv k₁ hk₁J, hk₁r, ← hr]
    ring
  set f' := k₁⁻¹ * f * k₁ with hf'
  have hf'm : f' = f * m' := by
    rw [hf', hm']
    calc k₁⁻¹ * f * k₁ = k₁⁻¹ * f⁻¹ * k₁ := by rw [hfi]
      _ = f * (f * k₁⁻¹ * f⁻¹ * k₁) := by
          rw [show f * (f * k₁⁻¹ * f⁻¹ * k₁) = (f * f) * k₁⁻¹ * f⁻¹ * k₁ by group, hff]
          group
  have hdJ : m'⁻¹ * m ∈ V ⊔ W := mul_mem (inv_mem hm'J) hmJ
  have hdV : m'⁻¹ * m ∈ V := by
    rw [fr.mem_V_iff_b hdJ, fr.b_mul (inv_mem hm'J) hmJ, hbinv m' hm'J, hbm',
      CharTwo.add_self_eq_zero]
  set d := m'⁻¹ * m with hd
  have hxd : x = f' * d := by rw [hf'm, hd, hxm]; group
  have hk₁T : k₁ ∈ T := P.side₁.J_le_T hk₁J
  have hf'T : f' ∈ T := mul_mem (mul_mem (inv_mem hk₁T) hf) hk₁T
  have hf'J : f' ∉ V ⊔ W := fun h1 => hfJ (by
    have e : f = k₁ * f' * k₁⁻¹ := by rw [hf']; group
    rw [e]
    exact mul_mem (mul_mem hk₁J h1) (inv_mem hk₁J))
  have hf'f' : f' * f' = 1 := by
    rw [hf']
    calc k₁⁻¹ * f * k₁ * (k₁⁻¹ * f * k₁) = k₁⁻¹ * (f * f) * k₁ := by group
      _ = 1 := by rw [hff]; group
  have hf'i : f'⁻¹ = f' := inv_eq_of_mul_eq_one_right hf'f'
  have hfd : f' * d * f'⁻¹ = d := by
    have h1 : f' * d * (f' * d) = 1 := by rw [← hxd]; exact hxx
    have hd1 : d⁻¹ = d := P.side₁.jst.inv_eq_of_V hdV
    rw [hf'i]
    calc f' * d * f' = f' * d * (f' * d) * d⁻¹ := by group
      _ = d := by rw [h1, one_mul, hd1]
  obtain ⟨u, huV, hu⟩ := P.exists_mul_conj_eq hZ hf'T hf'J (by rw [hf'f']; exact V.one_mem)
    hdV hfd
  have hcv : f' * u * f'⁻¹ ∈ V := conj_mem_of_mem_normalizer (P.side₁.T_le_V hf'T) huV
  have hcomm : (f' * u * f'⁻¹) * u = u * (f' * u * f'⁻¹) :=
    (P.side₁.jst.abelian_V _ hcv u huV).eq
  refine ⟨k₁ * u, mul_mem hk₁J (Subgroup.mem_sup_left huV), ?_⟩
  calc (k₁ * u)⁻¹ * f * (k₁ * u) = u⁻¹ * f' * u := by rw [hf']; group
    _ = f' * ((f' * u⁻¹ * f'⁻¹) * u) := by
        rw [hf'i]
        calc u⁻¹ * f' * u = (f' * f') * u⁻¹ * f' * u := by rw [hf'f', one_mul]
          _ = f' * (f' * u⁻¹ * f' * u) := by group
    _ = f' * d := by rw [P.side₁.jst.inv_eq_of_V huV, hcomm, hu]
    _ = x := hxd.symm

section CentL

variable {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1)

include hf hfJ hff

theorem act_comm_of_mem_cent {D : NatCoordK G L₁ V Z (GaloisField 2 e)} {k : G}
    (hk : k ∈ L₁ ⊓ Subgroup.centralizer ({f} : Set G)) (u : Fin 2 → GaloisField 2 e) :
    D.act f ((D.ρ k : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u) =
      (D.ρ k : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.act f u := by
  rw [NatCoordK.act_twist (P.side₁.T_le_L hf) (P.side₁.T_le_NVK hf) hk.1]
  congr 3
  have hkf : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  calc f * k * f⁻¹ = k * f * f⁻¹ := by rw [hkf]
    _ = k := by group

theorem exists_lift (D : NatCoordK G L₁ V Z (GaloisField 2 e))
    {M : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)} (hM : M ∈ centSL (D.act f)) :
    ∃ k ∈ L₁ ⊓ Subgroup.centralizer ({f} : Set G), D.ρ k = M := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfL := P.side₁.T_le_L hf
  have hfK := P.side₁.T_le_NVK hf
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  have hfl : f * l * f⁻¹ ∈ L₁ := conj_mem_of_mem_normalizer hfL hl
  have hρ : D.ρ (f * l * f⁻¹) = D.ρ l := by
    apply CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec
    intro w
    have h1 := NatCoordK.act_twist (D := D) hfL hfK hl (D.act f⁻¹ w)
    rw [NatCoordK.act_act_inv hfK] at h1
    rw [← h1, hlM]
    have h2 := hM (D.act f⁻¹ w)
    rw [NatCoordK.act_act_inv hfK] at h2
    rw [h2]
  have hv₁L : f * l * f⁻¹ * l⁻¹ ∈ L₁ := mul_mem hfl (inv_mem hl)
  have hv₁ : f * l * f⁻¹ * l⁻¹ ∈ V := by
    rw [← D.ρ_eq_one _ hv₁L, D.ρ_mul _ hfl _ (inv_mem hl), hρ, D.ρ_inv hl, mul_inv_cancel]
  set v₁ := f * l * f⁻¹ * l⁻¹ with hv₁def
  have hfv : f * v₁ * f⁻¹ = v₁ := by
    have hv₁1 : v₁⁻¹ = v₁ := P.side₁.jst.inv_eq_of_V hv₁
    have e1 : f * v₁ * f⁻¹ = v₁⁻¹ := by
      rw [hv₁def, hfi]
      have e2 : (f * l * f * l⁻¹)⁻¹ = l * f * l⁻¹ * f := by
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hfi]; group
      rw [e2]
      calc f * (f * l * f * l⁻¹) * f = (f * f) * (l * f * l⁻¹ * f) := by group
        _ = l * f * l⁻¹ * f := by rw [hff, one_mul]
    rw [e1, hv₁1]
  obtain ⟨u, huV, hu⟩ := P.exists_mul_conj_eq hZ hf hfJ (by rw [hff]; exact V.one_mem) hv₁ hfv
  have hfu : f * u * f⁻¹ ∈ V := conj_mem_of_mem_normalizer hfK.1 huV
  have hfu1 : (f * u * f⁻¹) * (f * u * f⁻¹) = 1 := P.side₁.jst.sq_V _ hfu
  have hcomm : (f * u * f⁻¹) * u = u * (f * u * f⁻¹) := (P.side₁.jst.abelian_V _ hfu u huV).eq
  refine ⟨u * l, Subgroup.mem_inf.2 ⟨mul_mem (P.side₁.V_le_L huV) hl,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
  · have h5 : f * (u * l) * f⁻¹ = u * l := by
      calc f * (u * l) * f⁻¹ = (f * u * f⁻¹) * (f * l * f⁻¹) := by group
        _ = (f * u * f⁻¹) * v₁ * l := by rw [hv₁def]; group
        _ = (f * u * f⁻¹) * (u * (f * u * f⁻¹)) * l := by rw [hu]
        _ = ((f * u * f⁻¹) * (f * u * f⁻¹)) * u * l := by rw [← hcomm]; group
        _ = u * l := by rw [hfu1, one_mul]
    calc u * l * f = f * (u * l) * f⁻¹ * f := by rw [h5]
      _ = f * (u * l) := by group
  · rw [D.ρ_mul _ (P.side₁.V_le_L huV) _ hl, (D.ρ_eq_one _ (P.side₁.V_le_L huV)).2 huV, one_mul,
      hlM]

theorem centL : Sp4CentL G L₁ V Z f e := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := P.side₁.nat
  have hfK := P.side₁.T_le_NVK hf
  have hσ := P.side₁.exists_sig_ne D hf hfJ
  have hb := P.side₁.semInv D hf hff
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    (P.side₁.jst.abelian_V x hx y hy).eq
  have hCfix : ∀ v ∈ V ⊓ Subgroup.centralizer ({f} : Set G), D.act f (D.κ v) = D.κ v := by
    intro v hv
    rw [NatCoordK.act_κ hfK hv.1]
    congr 1
    have := Subgroup.mem_centralizer_singleton_iff.1 hv.2
    calc f * v * f⁻¹ = v * f * f⁻¹ := by rw [this]
      _ = v := by group
  refine ⟨?_, P.card_CV hZ hf hfJ hff, ?_, ?_⟩
  ·
    intro Q hQ hQ2 hQn
    let φ : ↥Q →* SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
      { toFun := fun q => D.ρ q
        map_one' := D.ρ_one
        map_mul' := fun q q' => D.ρ_mul _ (hQ q.2).1 _ (hQ q'.2).1 }
    letI : MulAction ↥Q (Fin 2 → GaloisField 2 e) := MulAction.compHom _ φ
    have hsmul : ∀ (q : ↥Q) (u : Fin 2 → GaloisField 2 e),
        q • u = (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u := fun _ _ => rfl
    obtain ⟨w, hwfix, hw0⟩ : ∃ w : Fin 2 → GaloisField 2 e,
        (∀ q ∈ Q, (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ w = w) ∧ w ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hmod := hQ2.card_modEq_card_fixedPoints (Fin 2 → GaloisField 2 e)
      have h1 : Nat.card (MulAction.fixedPoints ↥Q (Fin 2 → GaloisField 2 e)) = 1 := by
        rw [Nat.card_eq_one_iff_exists]
        refine ⟨⟨0, fun q => by rw [hsmul, mulVec_zero]⟩, fun x => Subtype.ext ?_⟩
        exact hcon x.1 fun q hq => by rw [← hsmul ⟨q, hq⟩]; exact x.2 ⟨q, hq⟩
      rw [h1, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
        P.side₁.card_F] at hmod
      have h2 : (2 ^ e) ^ 2 % 2 = 0 := by
        rw [← pow_mul]
        exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by have := P.side₁.two_le; omega))
      have h3 := hmod
      unfold Nat.ModEq at h3
      rw [h2] at h3
      norm_num at h3
    have hqb : ∀ q ∈ Q, ∀ u, D.act f ((D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u) =
        (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.act f u :=
      fun q hq u => P.act_comm_of_mem_cent hZ hf hfJ hff (hQ hq) u
    obtain ⟨c, hc⟩ := id hσ
    obtain ⟨u₀, hu₀fix, hu₀0, hu₀Q⟩ : ∃ u₀ ∈ fixSet (D.act f), u₀ ≠ 0 ∧
        ∀ q ∈ Q, (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u₀ = u₀ := by
      have hfixA : ∀ y, y + D.act f y ∈ fixSet (D.act f) := fun y => by
        show D.act f (y + D.act f y) = y + D.act f y
        rw [hb.add, hb.invol, add_comm]
      have hQA : ∀ y, (∀ q ∈ Q, (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ y = y) →
          ∀ q ∈ Q, (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ (y + D.act f y) =
            y + D.act f y := fun y hy q hq => by
        rw [mulVec_add, ← hqb q hq, hy q hq]
      have hQc : ∀ q ∈ Q, (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ (c • w) =
          c • w := fun q hq => by rw [mulVec_smul, hwfix q hq]
      by_cases h1 : w + D.act f w = 0
      · refine ⟨c • w + D.act f (c • w), hfixA _, fun h2 => ?_, hQA _ hQc⟩
        have hbw : D.act f w = w := by
          rw [eq_neg_of_add_eq_zero_right h1, L3Side.vec_neg]
        have hbcw : D.act f (c • w) = c • w := by
          rw [eq_neg_of_add_eq_zero_right h2, L3Side.vec_neg]
        rw [hb.smul, hbw] at hbcw
        exact hc (smul_left_injective _ hw0 hbcw)
      · exact ⟨w + D.act f w, hfixA w, h1, hQA w hwfix⟩
    have hall : ∀ q ∈ Q, ∀ u ∈ fixSet (D.act f),
        (D.ρ q : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u = u := by
      intro q hq u hu
      by_cases hu0 : u = 0
      · rw [hu0, mulVec_zero]
      obtain ⟨M, hM, hMu⟩ := exists_centSL_smul hσ hb hu₀fix hu hu₀0 hu0
      obtain ⟨k, hk, hkM⟩ := P.exists_lift hZ hf hfJ hff D hM
      have hkq : k⁻¹ * q * k ∈ Q := by
        have := hQn.conj_mem ⟨q, hQ hq⟩ hq ⟨k⁻¹, inv_mem hk⟩
        simpa [Subgroup.mem_subgroupOf] using this
      have h1 := hu₀Q _ hkq
      have hkL := hk.1
      have hqL := (hQ hq).1
      have hkM' : (D.ρ k : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hkM]
      rw [← hMu, ← hkM']
      have e1 : q * k = k * (k⁻¹ * q * k) := by group
      rw [← D.ρ_mulVec_mul hqL hkL, e1,
        D.ρ_mulVec_mul hkL (mul_mem (mul_mem (inv_mem hkL) hqL) hkL), h1]
    intro q hq
    obtain ⟨v₁, v₂, h1, h2, hdet⟩ := hb.exists_fixed_pair hσ
    have hd : det2 v₁ v₂ ≠ 0 := by
      simp only [det2]
      intro h0
      apply hdet
      linear_combination h0
    exact (D.ρ_eq_one q (hQ hq).1).1 (eq_one_of_fix_two hd (hall q hq v₁ h1) (hall q hq v₂ h2))
  ·
    intro X hXC hZX hX
    let A : AddSubgroup (Fin 2 → GaloisField 2 e) :=
      { carrier := {w | ∃ x ∈ X, D.κ x = w}
        zero_mem' := ⟨1, X.one_mem, D.κ_one⟩
        add_mem' := fun {w w'} ⟨x, hx, hxw⟩ ⟨x', hx', hxw'⟩ =>
          ⟨x * x', X.mul_mem hx hx', by rw [D.κ_mul x (hXC hx).1 x' (hXC hx').1, hxw, hxw']⟩
        neg_mem' := fun {w} ⟨x, hx, hxw⟩ =>
          ⟨x⁻¹, X.inv_mem hx, by rw [D.κ_inv (hXC hx).1, hxw]⟩ }
    have hAfix : ∀ w ∈ A, w ∈ fixSet (D.act f) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hCfix x (hXC hx)
    have hAinv : ∀ M ∈ centSL (D.act f), ∀ w ∈ A, M.1 *ᵥ w ∈ A := by
      rintro M hM _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hkM⟩ := P.exists_lift hZ hf hfJ hff D hM
      refine ⟨k * x * k⁻¹, ?_, ?_⟩
      · have := mul_mem_cj k hx
        rwa [hX k hk] at this
      · rw [D.conj k hk.1 x (hXC hx).1, hkM]
    rcases irred_fixSet hσ hb A hAfix hAinv with hA | hA
    · left
      refine le_antisymm (fun x hx => ?_) hZX
      have : D.κ x ∈ A := ⟨x, hx, rfl⟩
      rw [hA, AddSubgroup.mem_bot] at this
      exact Subgroup.mem_inf.2 ⟨(D.κ_eq_zero _ (hXC hx).1).1 this, (hXC hx).2⟩
    · right
      refine le_antisymm hXC fun v hv => ?_
      obtain ⟨x, hx, hxv⟩ := hA (D.κ v) (hCfix v hv)
      have h1 := (D.κ_eq_iff hv.1 (hXC hx).1).1 hxv.symm
      have h2 : v * x⁻¹ ∈ Z ⊓ Subgroup.centralizer ({f} : Set G) :=
        Subgroup.mem_inf.2 ⟨h1, mul_mem hv.2 (inv_mem (hXC hx).2)⟩
      have e1 : v = (v * x⁻¹) * x := by group
      rw [e1]
      exact mul_mem (hZX h2) hx
  ·
    intro z hz hzZ
    obtain ⟨M, hM, hMz⟩ := exists_centSL_ne hσ hb (hCfix z hz) (D.κ_ne_zero hz.1 hzZ)
    obtain ⟨k, hk, hkM⟩ := P.exists_lift hZ hf hfJ hff D hM
    refine ⟨k, hk, fun hc => ?_⟩
    have e1 : ⁅z, k⁆ = z * (k * z⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e1] at hc
    have h1 := D.κ_of_mem_K hc
    rw [D.κ_comm hz.1 hk.1, hkM, sub_eq_zero] at h1
    exact hMz h1.symm

end CentL

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4

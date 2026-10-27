module

public import CFSG.CGT.PushingUpLit.A78L3.Fields
public import CFSG.CGT.PushingUpLit.A78L3.Heis
public import CFSG.CGT.PushingUpLit.A78L3.TJ

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open Matrix
open scoped commutatorElement

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}
  (h : L3Side G L V W T e) (D : NatCoord G L V (GaloisField 2 e))

include h in
theorem T_le_J_normalizer {t : G} (ht : t ∈ T) {j : G} (hj : j ∈ V ⊔ W) :
    t * j * t⁻¹ ∈ V ⊔ W := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.jst.mem_sup_iff).1 hj
  have e1 : t * (v * w) * t⁻¹ = (t * v * t⁻¹) * (t * w * t⁻¹) := by group
  rw [e1]
  exact mul_mem (Subgroup.mem_sup_left (conj_mem_of_mem_normalizer (h.T_le_V ht) hv))
    (Subgroup.mem_sup_right (conj_mem_of_mem_normalizer (h.T_le_W ht) hw))

include h in
theorem act_act_of_sq_mem {a : G} (ha : a ∈ T) (hsq : a * a ∈ V) (w : Fin 2 → GaloisField 2 e) :
    D.act a (D.act a w) = w := by
  rw [← NatCoord.act_mul (h.T_le_V ha)]
  refine NatCoord.act_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun v hv => ?_) w
  exact (h.jst.abelian_V v hv _ hsq).eq

theorem semInv_of_sq_mem {a : G} (ha : a ∈ T) (hsq : a * a ∈ V) :
    SemInv (h.sig D ⟨a, ha⟩) (D.act a) :=
  ⟨fun w w' => NatCoord.act_add (h.T_le_V ha) w w', fun c w => h.act_smul D ha c w,
    fun w => h.act_act_of_sq_mem D ha hsq w⟩

namespace Frame

variable {h D} (fr : Frame h D)

theorem act_z₀ {t : G} (ht : t ∈ T) :
    ∃ μ : GaloisField 2 e, D.act t (D.κ fr.z₀) = μ • D.κ fr.z₀ := by
  have htz : t * fr.z₀ * t⁻¹ ∈ V ⊓ W :=
    ⟨conj_mem_of_mem_normalizer (h.T_le_V ht) fr.hz₀.1,
      conj_mem_of_mem_normalizer (h.T_le_W ht) fr.hz₀.2⟩
  obtain ⟨μ, hμ⟩ := (h.mem_Z_iff D fr.hz₀ fr.hz₀1 htz.1).1 htz
  exact ⟨μ, by rw [NatCoord.act_κ fr.hz₀.1]; exact hμ⟩

theorem b_conj {t : G} (ht : t ∈ T) :
    ∃ ν, ∀ j ∈ V ⊔ W, fr.b (t * j * t⁻¹) = ν * h.sig D ⟨t, ht⟩ (fr.b j) := by
  obtain ⟨μ, hμ⟩ := fr.act_z₀ ht
  set u := D.act t⁻¹ fr.y₀ with hu
  have htV := h.T_le_V ht
  have htL := h.T_le_L ht
  refine ⟨h.sig D ⟨t, ht⟩ (det2 (D.κ fr.z₀) u) * μ, fun j hj => ?_⟩
  have hjL := h.J_le_L hj
  have h1 : (D.ρ (t * j * t⁻¹) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
      D.act t ((D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u) := by
    rw [NatCoord.act_twist htL htV hjL, hu, NatCoord.act_act_inv htV]
  rw [fr.ρ_mulVec hj, NatCoord.act_add htV, h.act_smul D ht, hμ, hu,
    NatCoord.act_act_inv htV, smul_smul, ← hu, map_mul] at h1
  rw [b, h1, det2_add_left, det2_self, zero_add, det2_smul_left, fr.hdet, mul_one]
  ring

theorem b_inv {j : G} (hj : j ∈ V ⊔ W) : fr.b j⁻¹ = fr.b j := by
  have h1 := fr.b_mul hj (inv_mem hj)
  rw [mul_inv_cancel, fr.b_of_mem_V (Subgroup.one_mem _)] at h1
  have := eq_neg_of_add_eq_zero_right h1.symm
  rw [this, CharTwo.neg_eq]

theorem nu_sigma {f : G} (hf : f ∈ T) (hff : f * f = 1) {ν : GaloisField 2 e}
    (hν : ∀ j ∈ V ⊔ W, fr.b (f * j * f⁻¹) = ν * h.sig D ⟨f, hf⟩ (fr.b j)) :
    ν * h.sig D ⟨f, hf⟩ ν = 1 := by
  have hw₁ : fr.w₁ ∈ V ⊔ W := Subgroup.mem_sup_right fr.hw₁
  have hb1 : fr.b fr.w₁ = 1 := fr.hb
  have hfj := h.T_le_J_normalizer hf hw₁
  have h1 := hν _ hfj
  have e1 : f * (f * fr.w₁ * f⁻¹) * f⁻¹ = fr.w₁ := by
    have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
    rw [hfi, show f * (f * fr.w₁ * f) * f = (f * f) * fr.w₁ * (f * f) by group, hff]
    group
  rw [e1, hν _ hw₁, hb1, map_one, mul_one] at h1
  exact h1.symm

end Frame

include h D in
theorem exists_involution (hTJ : T ≠ V ⊔ W) : ∃ f ∈ T, f ∉ V ⊔ W ∧ f * f = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨fr⟩ := h.exists_frame D
  obtain ⟨t₁, ht₁, ht₁J⟩ : ∃ t ∈ T, t ∉ V ⊔ W := by
    by_contra hcon
    push Not at hcon
    exact hTJ (le_antisymm hcon h.J_le_T)
  have : Finite (GaloisField 2 e ≃+* GaloisField 2 e) :=
    Finite.of_injective (fun σ : GaloisField 2 e ≃+* GaloisField 2 e => (σ : GaloisField 2 e →
      GaloisField 2 e)) fun _ _ hσ => RingEquiv.ext (congrFun hσ)
  set R := (h.sigHom D).range with hR
  have hR2 : IsPGroup 2 R := h.pT.of_surjective (h.sigHom D).rangeRestrict
    (MonoidHom.rangeRestrict_surjective _)
  have hRne : Nat.card R ≠ 1 := by
    intro h1
    have hbot := Subgroup.card_eq_one.1 h1
    have hmem : h.sigHom D ⟨t₁, ht₁⟩ ∈ R := ⟨⟨t₁, ht₁⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot, sigHom_apply] at hmem
    exact ht₁J ((h.sig_eq_one_iff D ⟨t₁, ht₁⟩).1 hmem)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.1 hR2)
  have hk0 : k ≠ 0 := by rintro rfl; exact hRne (by simpa using hk)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := R) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  obtain ⟨⟨x, hx⟩, hgx⟩ := g.2
  set σ := h.sig D ⟨x, hx⟩ with hσ
  have hgσ : (g : GaloisField 2 e ≃+* GaloisField 2 e) = σ := by rw [← hgx]; rfl
  have hσord : orderOf σ = 2 := by rw [← hgσ, Subgroup.orderOf_coe, hg]
  have hσ2 : σ * σ = 1 := by
    have := pow_orderOf_eq_one σ
    rw [hσord, pow_two] at this
    exact this
  have hσ1 : σ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hσord; norm_num at hσord
  have hxJ : x ∉ V ⊔ W := fun hxJ => hσ1 ((h.sig_eq_one_iff D ⟨x, hx⟩).2 hxJ)
  have hxx : x * x ∈ V ⊔ W := by
    have h1 : h.sig D ⟨x * x, mul_mem hx hx⟩ = 1 := by
      have : (⟨x * x, mul_mem hx hx⟩ : ↥T) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
      rw [this, ← sigHom_apply, map_mul, sigHom_apply, ← hσ, hσ2]
    exact (h.sig_eq_one_iff D _).1 h1
  obtain ⟨ν, hν⟩ := fr.b_conj hx
  have hs : ν * σ (fr.b (x * x)) = fr.b (x * x) := by
    have h1 := hν _ hxx
    rw [show x * (x * x) * x⁻¹ = x * x by group] at h1
    exact h1.symm
  obtain ⟨r, hr⟩ := exists_add_mul_eq σ hσ1 hσ2 hs
  obtain ⟨j, hj, -, hjr⟩ := fr.surj_ab 0 r
  set x' := x * j with hx'
  have hx'T : x' ∈ T := mul_mem hx (h.J_le_T hj)
  have hx'J : x' ∉ V ⊔ W := fun h1 => hxJ (by
    have e : x = x' * j⁻¹ := by rw [hx']; group
    rw [e]
    exact mul_mem h1 (inv_mem hj))
  have hx'V : x' * x' ∈ V := by
    have hxj := h.T_le_J_normalizer hx hj
    have e1 : x' * x' = (x * j * x⁻¹) * (x * x) * j := by rw [hx']; group
    have hJ2 : x' * x' ∈ V ⊔ W := by rw [e1]; exact mul_mem (mul_mem hxj hxx) hj
    rw [fr.mem_V_iff_b hJ2, e1, fr.b_mul (mul_mem hxj hxx) hj, fr.b_mul hxj hxx, hν _ hj, hjr]
    linear_combination -hr + CharTwo.add_self_eq_zero (r + ν * σ r)
  have hb := h.semInv_of_sq_mem D hx'T hx'V
  have hσ' : ∃ c, h.sig D ⟨x', hx'T⟩ c ≠ c := h.exists_sig_ne D hx'T hx'J
  have hwfix : D.act x' (D.κ (x' * x')) = D.κ (x' * x') := by
    rw [NatCoord.act_κ hx'V]
    congr 1
    group
  obtain ⟨u, hu⟩ := exists_add_semInv_eq hσ' hb hwfix
  refine ⟨x' * D.sec u, mul_mem hx'T (h.V_le_T (D.sec_mem u)), fun h1 => hx'J (by
    simpa using mul_mem h1 (inv_mem (Subgroup.mem_sup_left (D.sec_mem u)))), ?_⟩
  have hv := D.sec_mem u
  have hxv : x' * D.sec u * x'⁻¹ ∈ V := conj_mem_of_mem_normalizer (h.T_le_V hx'T) hv
  have e1 : x' * D.sec u * (x' * D.sec u) = (x' * D.sec u * x'⁻¹) * (x' * x') * D.sec u := by
    group
  refine (D.κ_eq_zero_iff (by rw [e1]; exact mul_mem (mul_mem hxv hx'V) hv)).1 ?_
  have h2 : ∀ y : Fin 2 → GaloisField 2 e, y + y = 0 := fun y => by
    ext i; simp [CharTwo.add_self_eq_zero]
  rw [e1, D.κ_mul _ (mul_mem hxv hx'V) _ hv, D.κ_mul _ hxv _ hx'V, ← NatCoord.act_κ hv,
    D.κ_sec, ← hu]
  linear_combination (norm := module) h2 (u + D.act x' u)

omit [Finite G] in
theorem vec_add_self (y : Fin 2 → GaloisField 2 e) : y + y = 0 := by
  ext i; simp [CharTwo.add_self_eq_zero]

omit [Finite G] in
theorem vec_neg (y : Fin 2 → GaloisField 2 e) : -y = y := by
  ext i; simp [CharTwo.neg_eq]

include h D in
theorem inv_conj {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1) {x : G} (hx : x ∈ T)
    (hxJ : x ∉ V ⊔ W) (hxx : x * x = 1) : ∃ k ∈ V ⊔ W, k⁻¹ * f * k = x := by
  obtain ⟨fr⟩ := h.exists_frame D
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hmJ : f * x ∈ V ⊔ W := h.mul_mem_J_of_involutions D hf hfJ hff hx hxJ hxx
  set m := f * x with hm
  have hxm : x = f * m := by rw [hm, ← mul_assoc, hff, one_mul]
  obtain ⟨ν, hν⟩ := fr.b_conj hf
  set σ := h.sig D ⟨f, hf⟩ with hσ
  have hfm : f * m * f⁻¹ = m⁻¹ := by
    have h1 : f * m * (f * m) = 1 := by rw [← hxm]; exact hxx
    rw [hfi]
    calc f * m * f = f * m * (f * m) * m⁻¹ := by group
      _ = m⁻¹ := by rw [h1, one_mul]
  have hs : ν * σ (fr.b m) = fr.b m := by
    have h1 := hν m hmJ
    rw [hfm, fr.b_inv hmJ] at h1
    exact h1.symm
  obtain ⟨r, hr⟩ := exists_add_mul_eq σ (h.sig_ne_one D hf hfJ) (h.sig_sq D hf hff) hs
  obtain ⟨k₁, hk₁J, -, hk₁r⟩ := fr.surj_ab 0 r
  have hfk : f * k₁⁻¹ * f⁻¹ ∈ V ⊔ W := h.T_le_J_normalizer hf (inv_mem hk₁J)
  set m' := (f * k₁⁻¹ * f⁻¹) * k₁ with hm'
  have hm'J : m' ∈ V ⊔ W := mul_mem hfk hk₁J
  have hbm' : fr.b m' = fr.b m := by
    rw [hm', fr.b_mul hfk hk₁J, hν _ (inv_mem hk₁J), fr.b_inv hk₁J, hk₁r, ← hr]
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
    rw [fr.mem_V_iff_b hdJ, fr.b_mul (inv_mem hm'J) hmJ, fr.b_inv hm'J, hbm',
      CharTwo.add_self_eq_zero]
  set d := m'⁻¹ * m with hd
  have hxd : x = f' * d := by rw [hf'm, hd, hxm]; group
  have hk₁T : k₁ ∈ T := h.J_le_T hk₁J
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
    have hd1 : d⁻¹ = d := h.jst.inv_eq_of_V hdV
    rw [hf'i]
    calc f' * d * f' = f' * d * (f' * d) * d⁻¹ := by group
      _ = d := by rw [h1, one_mul, hd1]
  have hwfix : D.act f' (D.κ d) = D.κ d := by rw [NatCoord.act_κ hdV, hfd]
  obtain ⟨u, hu⟩ := exists_add_semInv_eq (h.exists_sig_ne D hf'T hf'J)
    (h.semInv D hf'T hf'f') hwfix
  have hv := D.sec_mem u
  refine ⟨k₁ * D.sec u, mul_mem hk₁J (Subgroup.mem_sup_left hv), ?_⟩
  have hcv : f' * (D.sec u)⁻¹ * f'⁻¹ ∈ V :=
    conj_mem_of_mem_normalizer (h.T_le_V hf'T) (inv_mem hv)
  have h3 : (f' * (D.sec u)⁻¹ * f'⁻¹) * D.sec u = d := by
    refine D.κ_inj _ (mul_mem hcv hv) _ hdV ?_
    rw [D.κ_mul _ hcv _ hv, ← NatCoord.act_κ (inv_mem hv), D.κ_inv hv, vec_neg, D.κ_sec, ← hu,
      add_comm]
  calc (k₁ * D.sec u)⁻¹ * f * (k₁ * D.sec u) = (D.sec u)⁻¹ * f' * D.sec u := by rw [hf']; group
    _ = f' * ((f' * (D.sec u)⁻¹ * f'⁻¹) * D.sec u) := by
        rw [hf'i]
        calc (D.sec u)⁻¹ * f' * D.sec u = (f' * f') * (D.sec u)⁻¹ * f' * D.sec u := by
              rw [hf'f', one_mul]
          _ = f' * (f' * (D.sec u)⁻¹ * f' * D.sec u) := by group
    _ = x := by rw [h3, hxd]

include h D in
theorem card_CJf {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1) :
    2 ^ (e + e / 2) ≤ Nat.card ↥((V ⊔ W) ⊓ Subgroup.centralizer ({f} : Set G)) := by
  classical
  obtain ⟨fr⟩ := h.exists_frame D
  obtain ⟨ν, hν⟩ := fr.b_conj hf
  set σ := h.sig D ⟨f, hf⟩ with hσ
  have hνσ := fr.nu_sigma hf hff hν
  have hσ2 : σ * σ = 1 := h.sig_sq D hf hff
  have hσσ : ∀ r, σ (σ r) = r := fun r => by
    have := congrArg (fun τ : GaloisField 2 e ≃+* GaloisField 2 e => τ r) hσ2
    simpa using this
  have hev := h.even_of_involution D hf hfJ hff
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  let ψ : GaloisField 2 e →+ GaloisField 2 e :=
    { toFun := fun r => r + ν * σ r
      map_zero' := by simp
      map_add' := fun r r' => by rw [map_add]; ring }
  set Fx := {s : GaloisField 2 e // ν * σ s = s}
  have hker : Nat.card ψ.ker = Nat.card Fx := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    rw [AddMonoidHom.mem_ker]
    show r + ν * σ r = 0 ↔ ν * σ r = r
    constructor
    · intro h0
      linear_combination h0 - CharTwo.add_self_eq_zero r
    · intro h0
      rw [h0, CharTwo.add_self_eq_zero]
  have hrange : Nat.card ψ.range ≤ Nat.card Fx := by
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) fun y y' hyy => ?_
    · obtain ⟨r, hr⟩ := y.2
      rw [← hr]
      show ν * σ (r + ν * σ r) = r + ν * σ r
      rw [map_add, map_mul, hσσ]
      linear_combination r * hνσ
    · exact Subtype.ext (congrArg (fun z : Fx => z.1) hyy)
  have hkr := AddSubgroup.card_ker_mul_card_range ψ
  rw [hker, GaloisField.card 2 e h.e_ne_zero] at hkr
  have hFx : 2 ^ (e / 2) ≤ Nat.card Fx := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card Fx * Nat.card ψ.range < 2 ^ (e / 2) * 2 ^ (e / 2) :=
      Nat.mul_lt_mul_of_lt_of_le hlt (hrange.trans hlt.le) (by positivity)
    rw [hkr, ← pow_add, show e / 2 + e / 2 = e by obtain ⟨k, hk⟩ := hev; omega] at h1
    exact lt_irrefl _ h1
  set C := (V ⊔ W) ⊓ Subgroup.centralizer ({f} : Set G) with hC
  let β : ↥C →* Multiplicative (GaloisField 2 e) :=
    { toFun := fun j => Multiplicative.ofAdd (fr.b j)
      map_one' := by simp [fr.b_of_mem_V (Subgroup.one_mem V)]
      map_mul' := fun j k => by
        show Multiplicative.ofAdd (fr.b ((j : G) * k)) = _
        rw [fr.b_mul j.2.1 k.2.1, ofAdd_add] }
  have hβker : Nat.card β.ker = 2 ^ e := by
    rw [← h.card_CV D hf hfJ hff]
    refine Nat.card_congr (Equiv.ofBijective (fun j => ⟨(j : ↥C), ?_⟩) ⟨?_, ?_⟩)
    · have hj := (j : ↥C).2
      have h0 : fr.b (j : ↥C) = 0 := Multiplicative.ofAdd.injective j.2
      exact ⟨(fr.mem_V_iff_b hj.1).2 h0, hj.2⟩
    · intro j j' hjj
      exact Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(V ⊓ Subgroup.centralizer ({f} : Set G)) => (z : G)) hjj))
    · rintro ⟨v, hvV, hvC⟩
      refine ⟨⟨⟨v, Subgroup.mem_sup_left hvV, hvC⟩, ?_⟩, rfl⟩
      show Multiplicative.ofAdd (fr.b v) = 1
      rw [fr.b_of_mem_V hvV]
      rfl
  have hβrange : Nat.card Fx ≤ Nat.card β.range := by
    refine Nat.card_le_card_of_injective (fun s => ⟨Multiplicative.ofAdd s.1, ?_⟩)
      fun s s' hss => Subtype.ext (Multiplicative.ofAdd.injective
        (congrArg (fun z : ↥β.range => (z : Multiplicative (GaloisField 2 e))) hss))
    obtain ⟨j₀, hj₀J, -, hj₀s⟩ := fr.surj_ab 0 s.1
    have hfj := h.T_le_J_normalizer hf hj₀J
    have hv₁J : f * j₀ * f⁻¹ * j₀⁻¹ ∈ V ⊔ W := mul_mem hfj (inv_mem hj₀J)
    have hv₁ : f * j₀ * f⁻¹ * j₀⁻¹ ∈ V := by
      rw [fr.mem_V_iff_b hv₁J, fr.b_mul hfj (inv_mem hj₀J), hν _ hj₀J, fr.b_inv hj₀J, hj₀s,
        s.2, CharTwo.add_self_eq_zero]
    set v₁ := f * j₀ * f⁻¹ * j₀⁻¹ with hv₁def
    have hfv : f * v₁ * f⁻¹ = v₁ := by
      have hv₁1 : v₁⁻¹ = v₁ := h.jst.inv_eq_of_V hv₁
      have e1 : f * v₁ * f⁻¹ = v₁⁻¹ := by
        rw [hv₁def, hfi]
        have e2 : (f * j₀ * f * j₀⁻¹)⁻¹ = j₀ * f * j₀⁻¹ * f := by
          rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hfi]; group
        rw [e2]
        calc f * (f * j₀ * f * j₀⁻¹) * f = (f * f) * (j₀ * f * j₀⁻¹ * f) := by group
          _ = j₀ * f * j₀⁻¹ * f := by rw [hff, one_mul]
      rw [e1, hv₁1]
    have hwfix : D.act f (D.κ v₁) = D.κ v₁ := by rw [NatCoord.act_κ hv₁, hfv]
    obtain ⟨u, hu⟩ := exists_add_semInv_eq (h.exists_sig_ne D hf hfJ)
      (h.semInv D hf hff) hwfix
    have hu' := D.sec_mem u
    set j := D.sec u * j₀ with hj
    have hjJ : j ∈ V ⊔ W := mul_mem (Subgroup.mem_sup_left hu') hj₀J
    have hfu : f * D.sec u * f⁻¹ ∈ V := conj_mem_of_mem_normalizer (h.T_le_V hf) hu'
    have h4 : (f * D.sec u * f⁻¹) * v₁ = D.sec u := by
      refine D.κ_inj _ (mul_mem hfu hv₁) _ hu' ?_
      rw [D.κ_mul _ hfu _ hv₁, ← NatCoord.act_κ hu', D.κ_sec, ← hu]
      linear_combination (norm := module) vec_add_self (D.act f u)
    have hjC : j ∈ C := by
      refine ⟨hjJ, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have h5 : f * j * f⁻¹ = j := by
        calc f * j * f⁻¹ = (f * D.sec u * f⁻¹) * (f * j₀ * f⁻¹) := by rw [hj]; group
          _ = (f * D.sec u * f⁻¹) * v₁ * j₀ := by rw [hv₁def]; group
          _ = j := by rw [h4, hj]
      calc j * f = f * j * f⁻¹ * f := by rw [h5]
        _ = f * j := by group
    refine ⟨⟨j, hjC⟩, ?_⟩
    show Multiplicative.ofAdd (fr.b j) = Multiplicative.ofAdd s.1
    rw [hj, fr.b_mul (Subgroup.mem_sup_left hu') hj₀J, fr.b_of_mem_V hu', zero_add, hj₀s]
  have hcard := Subgroup.card_ker_mul_card_range β
  rw [hβker] at hcard
  rw [← hcard, pow_add]
  exact Nat.mul_le_mul_left _ (hFx.trans hβrange)

end L3Side

end CFSG.CGT.PushingUpLit.A78L3

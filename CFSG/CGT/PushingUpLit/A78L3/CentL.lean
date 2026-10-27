module

public import CFSG.CGT.PushingUpLit.A78L3.FieldT
public import CFSG.CGT.PushingUpLit.A78L3.Base
public import CFSG.CGT.PushingUpLit.T2K.Nat

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78T2 (T2CentL)
open Matrix
open scoped commutatorElement

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}
  (h : L3Side G L V W T e) (D : NatCoord G L V (GaloisField 2 e))

variable {f : G} (hf : f ∈ T) (hfJ : f ∉ V ⊔ W) (hff : f * f = 1)

include h hf hff in
theorem exists_lift (hfJ' : f ∉ V ⊔ W) {M : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)}
    (hM : M ∈ centSL (D.act f)) :
    ∃ k ∈ L ⊓ Subgroup.centralizer ({f} : Set G), D.ρ k = M := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hfL := h.T_le_L hf
  have hfV := h.T_le_V hf
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  have hfl : f * l * f⁻¹ ∈ L := conj_mem_of_mem_normalizer hfL hl
  have hρ : D.ρ (f * l * f⁻¹) = D.ρ l := by
    apply CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec
    intro w
    have h1 := NatCoord.act_twist (D := D) hfL hfV hl (D.act f⁻¹ w)
    rw [NatCoord.act_act_inv hfV] at h1
    rw [← h1, hlM]
    have h2 := hM (D.act f⁻¹ w)
    rw [NatCoord.act_act_inv hfV] at h2
    rw [h2]
  have hv₁L : f * l * f⁻¹ * l⁻¹ ∈ L := mul_mem hfl (inv_mem hl)
  have hv₁ : f * l * f⁻¹ * l⁻¹ ∈ V := by
    rw [← D.ρ_eq_one _ hv₁L, D.ρ_mul _ hfl _ (inv_mem hl), hρ, D.ρ_inv hl, mul_inv_cancel]
  set v₁ := f * l * f⁻¹ * l⁻¹ with hv₁def
  have hfv : f * v₁ * f⁻¹ = v₁ := by
    have hv₁1 : v₁⁻¹ = v₁ := h.jst.inv_eq_of_V hv₁
    have e1 : f * v₁ * f⁻¹ = v₁⁻¹ := by
      rw [hv₁def, hfi]
      have e2 : (f * l * f * l⁻¹)⁻¹ = l * f * l⁻¹ * f := by
        rw [_root_.mul_inv_rev, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, hfi]; group
      rw [e2]
      calc f * (f * l * f * l⁻¹) * f = (f * f) * (l * f * l⁻¹ * f) := by group
        _ = l * f * l⁻¹ * f := by rw [hff, one_mul]
    rw [e1, hv₁1]
  have hwfix : D.act f (D.κ v₁) = D.κ v₁ := by rw [NatCoord.act_κ hv₁, hfv]
  obtain ⟨u, hu⟩ := exists_add_semInv_eq (h.exists_sig_ne D hf hfJ') (h.semInv D hf hff) hwfix
  have hu' := D.sec_mem u
  have hfu : f * D.sec u * f⁻¹ ∈ V := conj_mem_of_mem_normalizer hfV hu'
  have h4 : (f * D.sec u * f⁻¹) * v₁ = D.sec u := by
    refine D.κ_inj _ (mul_mem hfu hv₁) _ hu' ?_
    rw [D.κ_mul _ hfu _ hv₁, ← NatCoord.act_κ hu', D.κ_sec, ← hu]
    linear_combination (norm := module) vec_add_self (D.act f u)
  refine ⟨D.sec u * l, Subgroup.mem_inf.2 ⟨mul_mem (h.V_le_L hu') hl,
    Subgroup.mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
  · have h5 : f * (D.sec u * l) * f⁻¹ = D.sec u * l := by
      calc f * (D.sec u * l) * f⁻¹ = (f * D.sec u * f⁻¹) * (f * l * f⁻¹) := by group
        _ = (f * D.sec u * f⁻¹) * v₁ * l := by rw [hv₁def]; group
        _ = D.sec u * l := by rw [h4]
    calc D.sec u * l * f = f * (D.sec u * l) * f⁻¹ * f := by rw [h5]
      _ = f * (D.sec u * l) := by group
  · rw [D.ρ_mul _ (h.V_le_L hu') _ hl, (D.ρ_eq_one _ (h.V_le_L hu')).2 hu', one_mul, hlM]

include D in
theorem cj_CV {k : G} (hk : k ∈ L ⊓ Subgroup.centralizer ({f} : Set G)) :
    cj k (V ⊓ Subgroup.centralizer ({f} : Set G)) = V ⊓ Subgroup.centralizer ({f} : Set G) := by
  have hkf : k * f = f * k := Subgroup.mem_centralizer_singleton_iff.1 hk.2
  refine cj_eq_of_mem_normalizer_set (mem_normalizer_of_conj_le fun v hv => ?_)
  refine ⟨D.norm k hk.1 v hv.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hvf : v * f = f * v := Subgroup.mem_centralizer_singleton_iff.1 hv.2
  calc k * v * k⁻¹ * f = k * v * (k⁻¹ * f) := by group
    _ = k * v * (f * k⁻¹) := by
        congr 1
        calc k⁻¹ * f = k⁻¹ * (f * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * f) * k⁻¹ := by rw [hkf]
          _ = f * k⁻¹ := by group
    _ = k * (v * f) * k⁻¹ := by group
    _ = k * (f * v) * k⁻¹ := by rw [hvf]
    _ = (k * f) * v * k⁻¹ := by group
    _ = f * (k * v * k⁻¹) := by rw [hkf]; group

include h D hf hfJ hff in
theorem centL : T2CentL G L V (V ⊓ W) f e := by
  classical
  have hfV := h.T_le_V hf
  have hσ := h.exists_sig_ne D hf hfJ
  have hb := h.semInv D hf hff
  set C := V ⊓ Subgroup.centralizer ({f} : Set G) with hCdef
  have hCfix : ∀ v ∈ C, D.act f (D.κ v) = D.κ v := fun v hv => by
    rw [NatCoord.act_κ hv.1]
    congr 1
    have := Subgroup.mem_centralizer_singleton_iff.1 hv.2
    calc f * v * f⁻¹ = v * f * f⁻¹ := by rw [this]
      _ = v := by group
  have hfixC : ∀ w ∈ fixSet (D.act f), D.sec w ∈ C := by
    intro w hw
    refine ⟨D.sec_mem w, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : D.κ (f * D.sec w * f⁻¹) = D.κ (D.sec w) := by
      rw [← NatCoord.act_κ (D.sec_mem w), D.κ_sec]; exact hw
    have h2 := D.κ_inj _ (conj_mem_of_mem_normalizer hfV (D.sec_mem w)) _ (D.sec_mem w) h1
    calc D.sec w * f = f * D.sec w * f⁻¹ * f := by rw [h2]
      _ = f * D.sec w := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro P hP hP2 hPn
    have hPC : ∀ t ∈ P, cj t C = C := fun t ht => cj_CV D (hP ht)
    have hCel : ElemAb2 C := fun x hx y hy =>
      ⟨(h.jst.abelian_V x hx.1 y hy.1).eq, h.jst.sq_V x hx.1⟩
    have hC1 : C ≠ ⊥ := by
      intro hbot
      have := h.card_CV D hf hfJ hff
      rw [← hCdef, hbot, Subgroup.card_bot] at this
      have h2 : 2 ≤ 2 ^ e := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by have := h.two_le; omega)
      omega
    obtain ⟨v₀, hv₀, hv₀1, hfixP⟩ := exists_fixed_ne_one hP2 hCel hC1 hPC
    have hall : ∀ p ∈ P, ∀ v ∈ C, p * v * p⁻¹ = v := by
      intro p hp v hv
      by_cases hv1 : v = 1
      · rw [hv1]; group
      obtain ⟨M, hM, hMv⟩ := exists_centSL_smul hσ hb (hCfix v₀ hv₀) (hCfix v hv)
        (D.κ_ne_zero hv₀.1 hv₀1) (D.κ_ne_zero hv.1 hv1)
      obtain ⟨k, hk, hkM⟩ := h.exists_lift D hf hff hfJ hM
      have hkv : k * v₀ * k⁻¹ = v := by
        refine D.κ_inj _ (D.norm k hk.1 v₀ hv₀.1) _ hv.1 ?_
        rw [D.conj k hk.1 v₀ hv₀.1, hkM]
        exact hMv
      have hkp : k⁻¹ * p * k ∈ P := by
        have := hPn.conj_mem ⟨p, hP hp⟩ hp ⟨k⁻¹, inv_mem hk⟩
        simpa [Subgroup.mem_subgroupOf] using this
      have h1 := hfixP _ hkp
      rw [← hkv]
      calc p * (k * v₀ * k⁻¹) * p⁻¹ = k * ((k⁻¹ * p * k) * v₀ * (k⁻¹ * p * k)⁻¹) * k⁻¹ := by
            group
        _ = k * v₀ * k⁻¹ := by rw [h1]
    intro p hp
    have hpL : p ∈ L := (hP hp).1
    refine (D.ρ_eq_one p hpL).1 (CFSG.CGT.PushingUpLit.T2K.eq_of_forall_mulVec fun w => ?_)
    obtain ⟨v₁, v₂, h1, h2, hdet⟩ := hb.exists_fixed_pair hσ
    have hd : det2 v₁ v₂ ≠ 0 := by
      simp only [det2]
      intro h0
      apply hdet
      linear_combination h0
    have hv₂' : det2 v₁ ((det2 v₁ v₂)⁻¹ • v₂) = 1 := by
      rw [det2_smul_right, inv_mul_cancel₀ hd]
    have hfixM : ∀ y ∈ fixSet (D.act f), (D.ρ p : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ y = y := by
      intro y hy
      have hc := hfixC y hy
      have := hall p hp _ hc
      rw [← D.κ_sec y, ← D.conj p hpL _ (D.sec_mem y), this]
    rw [eq_det2_smul hv₂' w, mulVec_add, mulVec_smul, mulVec_smul, hfixM v₁ h1,
      mulVec_smul, hfixM v₂ h2]
    simp
  ·
    exact (h.card_CV D hf hfJ hff).ge
  ·
    intro X hXC hX
    let A : AddSubgroup (Fin 2 → GaloisField 2 e) :=
      { carrier := {w | ∃ x ∈ X, D.κ x = w}
        zero_mem' := ⟨1, X.one_mem, D.κ_one⟩
        add_mem' := fun {w w'} ⟨x, hx, hxw⟩ ⟨x', hx', hxw'⟩ =>
          ⟨x * x', X.mul_mem hx hx', by rw [D.κ_mul x (hXC hx).1 x' (hXC hx').1, hxw, hxw']⟩
        neg_mem' := fun {w} ⟨x, hx, hxw⟩ => ⟨x⁻¹, X.inv_mem hx, by rw [D.κ_inv (hXC hx).1, hxw]⟩ }
    have hAfix : ∀ w ∈ A, w ∈ fixSet (D.act f) := by
      rintro _ ⟨x, hx, rfl⟩
      exact hCfix x (hXC hx)
    have hAinv : ∀ M ∈ centSL (D.act f), ∀ w ∈ A, M.1 *ᵥ w ∈ A := by
      rintro M hM _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk, hkM⟩ := h.exists_lift D hf hff hfJ hM
      refine ⟨k * x * k⁻¹, ?_, ?_⟩
      · have := mul_mem_cj k hx
        rwa [hX k hk] at this
      · rw [D.conj k hk.1 x (hXC hx).1, hkM]
    rcases irred_fixSet hσ hb A hAfix hAinv with hA | hA
    · left
      refine (Subgroup.eq_bot_iff_forall X).2 fun x hx => ?_
      have : D.κ x ∈ A := ⟨x, hx, rfl⟩
      rw [hA, AddSubgroup.mem_bot] at this
      exact (D.κ_eq_zero_iff (hXC hx).1).1 this
    · right
      refine le_antisymm hXC fun v hv => ?_
      obtain ⟨x, hx, hxv⟩ := hA (D.κ v) (hCfix v hv)
      rw [D.κ_inj x (hXC hx).1 v hv.1 hxv] at hx
      exact hx
  ·
    obtain ⟨z, hz, hzf⟩ := h.not_centralizes_Z D hf hfJ
    have hle : (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) ≤ V ⊓ W := inf_le_left
    have hne : (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) ≠ V ⊓ W := by
      intro heq
      have : z ∈ (V ⊓ W) ⊓ Subgroup.centralizer ({f} : Set G) := by rw [heq]; exact hz
      exact hzf (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm
    rw [← h.card_Z]
    exact lt_of_le_of_ne (Subgroup.card_le_of_le hle) fun hc =>
      hne (Subgroup.eq_of_le_of_card_ge hle hc.ge)

end L3Side

end CFSG.CGT.PushingUpLit.A78L3

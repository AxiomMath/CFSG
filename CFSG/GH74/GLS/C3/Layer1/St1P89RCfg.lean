module

public import CFSG.GH74.GLS.C3.Layer1.St1P89RCtx
public import CFSG.GH74.GLS.C3.Layer1.St1P89AutStmt
public import CFSG.GH74.GLS.C3.Layer1.St1P89Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.P34Real

variable {G : Type} [Group G] {K : Subgroup G}

theorem act_pow_nat {C : Subgroup G} (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) {g : G} (hg : g ∈ C)
    (n : ℕ) : act hKN (g ^ n) = (act hKN g) ^ n := by
  have := act_zpow hKN hg (n : ℤ)
  simpa [zpow_natCast] using this

namespace Base89

variable {u x : G} {T : Subgroup G} (H : Base89 u K T)

include H in
theorem act_comm_of_mem_Qs {t t' : G} (ht : t ∈ T) (ht' : t' ∈ T)
    (hq : t * t' * t⁻¹ * t'⁻¹ ∈ Qs u K T) : act H.KN t * act H.KN t' = act H.KN t' * act H.KN t := by
  have hC := H.T_le_C
  have h1 := H.act_Qs hq
  rw [act_mul H.KN (hC (T.mul_mem (T.mul_mem ht ht') (T.inv_mem ht))) (hC (T.inv_mem ht')),
    act_mul H.KN (hC (T.mul_mem ht ht')) (hC (T.inv_mem ht)), act_mul H.KN (hC ht) (hC ht'),
    act_inv H.KN (hC ht), act_inv H.KN (hC ht')] at h1
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h1)

include H in
theorem cfg89_of_data [Finite G] (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hrank : pRank 2 G = 4) (hu2 : orderOf u = 2) (hx2 : orderOf x = 2) (hxT : x ∈ T)
    (hxstar : ¬ IsStar2 x) (hQinv : ∀ q ∈ Qs u K T, q ^ 2 = 1 → q = 1 ∨ q = u)
    {Eb : Subgroup (MulAut (kBar K))} {rb sb fb : MulAut (kBar K)} {k₁ k₂ : kBar K}
    (hAD : AutData89 H.B Eb (act H.KN x) rb sb fb k₁ k₂) {r s f : G} (hr : r ∈ T ⊓ K)
    (hs : s ∈ T ⊓ K) (hf : f ∈ T) (hf2 : f ^ 2 = 1) (hra : act H.KN r = rb)
    (hsa : act H.KN s = sb) (hfa : act H.KN f = fb) :
    Cfg89T G T (T ⊓ K) (Qs u K T) u (r ^ 2) x f r s := by
  have hC := H.T_le_C
  have hPact : ∀ p ∈ T ⊓ K, act H.KN p ∈ H.B ⊓ innAut (kBar K) := fun p hp =>
    (H.mem_B_inf_inn).2 ⟨p, hp, rfl⟩
  have hrC : r ∈ centralizer ({u} : Set G) := hC hr.1
  have hsC : s ∈ centralizer ({u} : Set G) := hC hs.1
  have hfC : f ∈ centralizer ({u} : Set G) := hC hf
  have hxC : x ∈ centralizer ({u} : Set G) := hC hxT
  have hz : r ^ 2 ∈ T ⊓ K := (T ⊓ K).pow_mem hr 2
  have hza : act H.KN (r ^ 2) = rb ^ 2 := by rw [act_pow_nat H.KN hrC, hra]
  have hr4 : r ^ 4 = 1 := by
    apply H.act_inj_P ((T ⊓ K).pow_mem hr 4) (Subgroup.one_mem _)
    rw [act_pow_nat H.KN hrC, hra, act_one]
    exact hAD.r4
  have hs2 : s ^ 2 = 1 := by
    apply H.act_inj_P ((T ⊓ K).pow_mem hs 2) (Subgroup.one_mem _)
    rw [act_pow_nat H.KN hsC, hsa, act_one]
    exact hAD.s2
  have hsrs : s * r * s⁻¹ = r⁻¹ := by
    apply H.act_inj_P ((T ⊓ K).mul_mem ((T ⊓ K).mul_mem hs hr) ((T ⊓ K).inv_mem hs))
      ((T ⊓ K).inv_mem hr)
    rw [act_conj H.KN hsC hrC, act_inv H.KN hrC, hra, hsa]
    exact hAD.srs
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    apply hAD.r2_ne
    rw [← hza, h, act_one]
  have hPgen : ∀ p ∈ T ⊓ K, ∃ i j : ℕ, p = r ^ i * s ^ j := by
    intro p hp
    obtain ⟨i, j, hij⟩ := hAD.P_gen _ (hPact p hp)
    refine ⟨i, j, H.act_inj_P hp ((T ⊓ K).mul_mem ((T ⊓ K).pow_mem hr i) ((T ⊓ K).pow_mem hs j)) ?_⟩
    rw [act_mul H.KN (hC ((T ⊓ K).pow_mem hr i).1) (hC ((T ⊓ K).pow_mem hs j).1),
      act_pow_nat H.KN hrC, act_pow_nat H.KN hsC, hra, hsa]
    exact hij
  have hxr : x * r * x⁻¹ = r⁻¹ := by
    apply H.act_inj_P ⟨T.mul_mem (T.mul_mem hxT hr.1) (T.inv_mem hxT), H.KN x hxC r hr.2⟩
      ((T ⊓ K).inv_mem hr)
    rw [act_conj H.KN hxC hrC, act_inv H.KN hrC, hra]
    exact hAD.x_r
  have hxs : x * s * x⁻¹ = r * s ∨ x * s * x⁻¹ = r ^ 3 * s := by
    have hxsP : x * s * x⁻¹ ∈ T ⊓ K :=
      ⟨T.mul_mem (T.mul_mem hxT hs.1) (T.inv_mem hxT), H.KN x hxC s hs.2⟩
    have hxsa : act H.KN (x * s * x⁻¹) = act H.KN x * sb * (act H.KN x)⁻¹ := by
      rw [act_conj H.KN hxC hsC, hsa]
    rcases hAD.x_s with h | h
    · left
      apply H.act_inj_P hxsP ((T ⊓ K).mul_mem hr hs)
      rw [hxsa, h, act_mul H.KN hrC hsC, hra, hsa]
    · right
      apply H.act_inj_P hxsP ((T ⊓ K).mul_mem ((T ⊓ K).pow_mem hr 3) hs)
      rw [hxsa, h, act_mul H.KN (hC ((T ⊓ K).pow_mem hr 3).1) hsC, act_pow_nat H.KN hrC, hra, hsa]
  have hfcent : ∀ p ∈ T ⊓ K, f * p = p * f := by
    intro p hp
    have hpC : p ∈ centralizer ({u} : Set G) := hC hp.1
    have h1 : f * p * f⁻¹ = p := by
      apply H.act_inj_P ⟨T.mul_mem (T.mul_mem hf hp.1) (T.inv_mem hf), H.KN f hfC p hp.2⟩ hp
      rw [act_conj H.KN hfC hpC, hfa]
      exact mul_inv_eq_iff_eq_mul.2 (hAD.f_cent _ (hPact p hp))
    exact mul_inv_eq_iff_eq_mul.1 h1
  have hfnot : ∀ q ∈ Qs u K T, ∀ i : ℕ, f ≠ q * (r ^ 2) ^ i := by
    intro q hq i hfq
    have hzi : (r ^ 2) ^ i ∈ T ⊓ K := (T ⊓ K).pow_mem hz i
    have h1 : act H.KN f = act H.KN (q * (r ^ 2) ^ i) := by rw [← hfq]
    rw [act_mul H.KN (hC (Qs_le_T hq)) (hC hzi.1), H.act_Qs hq, one_mul,
      act_pow_nat H.KN (hC hz.1), hza, hfa] at h1
    have hz2 : (rb ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hAD.r4
    rw [pow_eq_pow_mod i hz2] at h1
    rcases Nat.mod_two_eq_zero_or_one i with h | h
    · rw [h, pow_zero] at h1
      exact hAD.f_ne_one h1
    · rw [h, pow_one] at h1
      exact hAD.f_ne_z h1
  have hTgen : ∀ t ∈ T, ∃ p ∈ T ⊓ K, ∃ q ∈ Qs u K T, ∃ i j : ℕ, t = p * q * f ^ i * x ^ j := by
    intro t ht
    have hbt : act H.KN t ∈ H.B := (H.mem_B).2 ⟨t, ht, rfl⟩
    obtain ⟨pb, hpb, i, j, hij⟩ := hAD.B_gen _ hbt
    obtain ⟨p, hp, hpa⟩ := (H.mem_B_inf_inn).1 hpb
    have hw : f ^ i * x ^ j ∈ T := T.mul_mem (T.pow_mem hf i) (T.pow_mem hxT j)
    have ht' : p * (f ^ i * x ^ j) ∈ T := T.mul_mem hp.1 hw
    have hact : act H.KN t = act H.KN (p * (f ^ i * x ^ j)) := by
      rw [act_mul H.KN (hC hp.1) (hC hw), act_mul H.KN (hC (T.pow_mem hf i))
        (hC (T.pow_mem hxT j)), act_pow_nat H.KN hfC, act_pow_nat H.KN hxC, hpa, hfa, hij,
        mul_assoc]
    have hq0 := H.fiber_mem_Qs ht ht' hact
    refine ⟨p, hp, (f ^ i * x ^ j) * ((p * (f ^ i * x ^ j))⁻¹ * t) * (f ^ i * x ^ j)⁻¹,
      H.Qs_norm hw hq0, i, j, ?_⟩
    group
  have hCTP : ∀ t ∈ T, (∀ p ∈ T ⊓ K, t * p = p * t) →
      ∃ i : ℕ, ∃ q ∈ Qs u K T, ∃ j : ℕ, t = (r ^ 2) ^ i * q * f ^ j := by
    intro t ht hcomm
    have hbt : act H.KN t ∈ H.B := (H.mem_B).2 ⟨t, ht, rfl⟩
    have hcb : ∀ p ∈ H.B ⊓ innAut (kBar K), act H.KN t * p = p * act H.KN t := by
      intro pb hpb
      obtain ⟨p, hp, rfl⟩ := (H.mem_B_inf_inn).1 hpb
      rw [← act_mul H.KN (hC ht) (hC hp.1), ← act_mul H.KN (hC hp.1) (hC ht), hcomm p hp]
    obtain ⟨i, j, hij⟩ := hAD.C_P _ hbt hcb
    have hzi : (r ^ 2) ^ i ∈ T ⊓ K := (T ⊓ K).pow_mem hz i
    have hfj : f ^ j ∈ T := T.pow_mem hf j
    have ht' : (r ^ 2) ^ i * f ^ j ∈ T := T.mul_mem hzi.1 hfj
    have hact : act H.KN t = act H.KN ((r ^ 2) ^ i * f ^ j) := by
      rw [act_mul H.KN (hC hzi.1) (hC hfj), act_pow_nat H.KN (hC hz.1), act_pow_nat H.KN hfC,
        hza, hfa, ← pow_mul, hij]
    have hq0 := H.fiber_mem_Qs ht ht' hact
    refine ⟨i, f ^ j * (((r ^ 2) ^ i * f ^ j)⁻¹ * t) * (f ^ j)⁻¹, H.Qs_norm hfj hq0, j, ?_⟩
    group
  have hZTQ : ∀ t ∈ T, (∀ t' ∈ T, t * t' * t⁻¹ * t'⁻¹ ∈ Qs u K T) →
      ∃ i : ℕ, ∃ q ∈ Qs u K T, t = (r ^ 2) ^ i * q := by
    intro t ht hZ
    have hbt : act H.KN t ∈ H.B := (H.mem_B).2 ⟨t, ht, rfl⟩
    have hZb : ∀ b ∈ H.B, act H.KN t * b = b * act H.KN t := by
      intro b hb
      obtain ⟨t', ht', rfl⟩ := (H.mem_B).1 hb
      exact H.act_comm_of_mem_Qs ht ht' (hZ t' ht')
    rcases hAD.Z_B _ hbt hZb with h | h
    · refine ⟨0, t, (H.mem_Qs).2 ⟨ht, h⟩, ?_⟩
      group
    · have hq0 := H.fiber_mem_Qs ht hz.1 (by rw [h, hza])
      refine ⟨1, (r ^ 2)⁻¹ * t, hq0, ?_⟩
      group
  have hxf : ∃ q ∈ Qs u K T, x * f * x⁻¹ = r ^ 2 * q * f := by
    have hxfT : x * f * x⁻¹ ∈ T := T.mul_mem (T.mul_mem hxT hf) (T.inv_mem hxT)
    have hzfT : r ^ 2 * f ∈ T := T.mul_mem hz.1 hf
    have hact : act H.KN (x * f * x⁻¹) = act H.KN (r ^ 2 * f) := by
      rw [act_conj H.KN hxC hfC, act_mul H.KN (hC hz.1) hfC, hza, hfa]
      exact hAD.xf
    have hq0 := H.fiber_mem_Qs hxfT hzfT hact
    refine ⟨f * ((r ^ 2 * f)⁻¹ * (x * f * x⁻¹)) * f⁻¹, H.Qs_norm hf hq0, ?_⟩
    group
  exact
    { simple := hsimple
      nonab := hnonab
      rank4 := hrank
      sylowT := H.sylowT
      x_ord := hx2
      x_not_star := hxstar
      P_le := inf_le_left
      Q_le := Qs_le_T
      P_norm := fun t ht p hp =>
        ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), H.KN t (hC ht) p hp.2⟩
      Q_norm := fun t ht q hq => H.Qs_norm ht hq
      PQ_comm := fun p hp q hq => H.P_comm_Qs hp hq
      PQ_inf := fun g hgP hgQ =>
        H.act_inj_P hgP (Subgroup.one_mem _) (by rw [H.act_Qs hgQ, act_one H.KN])
      r_mem := hr
      s_mem := hs
      r4 := hr4
      s2 := hs2
      srs := hsrs
      r2_ne := hr2
      z_eq := rfl
      P_gen := hPgen
      u_mem := H.u_mem_Qs
      u2 := by
        have := pow_orderOf_eq_one u
        rwa [hu2] at this
      u_ne := by
        intro h
        rw [h, orderOf_one] at hu2
        omega
      Q_inv := hQinv
      u_central := fun t ht => mem_centralizer_singleton_iff.1 (hC ht)
      f_mem := hf
      f2 := hf2
      f_cent := hfcent
      f_not := hfnot
      x_mem := hxT
      x2 := by
        have := pow_orderOf_eq_one x
        rwa [hx2] at this
      x_r := hxr
      x_s := hxs
      T_gen := hTgen
      CTP := hCTP
      ZTQ := hZTQ
      xf := hxf }

end Base89

end CFSG.GH74.GLS.C3.Layer1.P89

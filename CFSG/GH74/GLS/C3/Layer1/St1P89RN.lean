module

public import CFSG.GH74.GLS.C3.Layer1.St1P89RCfg
public import CFSG.GH74.GLS.C3.Layer1.St1P89RLift
public import CFSG.GH74.GLS.C3.Layer1.St1P89Z
public import CFSG.GH74.GLS.C3.Layer1.BkIv10

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.P34Real

variable {G : Type} [Group G] {K : Subgroup G}

theorem mulConjMulInv89 {H : Type} [Group H] (γ : MulAut H) (g : H) :
    γ * MulAut.conj g * γ⁻¹ = MulAut.conj (γ g) := by
  ext y
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem mem_O_of_mk_eq {a b : G} (ha : a ∈ K) (hb : b ∈ K)
    (h : (QuotientGroup.mk ⟨a, ha⟩ : kBar K) = QuotientGroup.mk ⟨b, hb⟩) :
    a * b⁻¹ ∈ pPrimeCoreOf 2 K := by
  have h1 := (QuotientGroup.eq_iff_div_mem).1 h
  have hdiv : ((⟨a, ha⟩ : ↥K) / ⟨b, hb⟩ : ↥K) = ⟨a * b⁻¹, K.mul_mem ha (K.inv_mem hb)⟩ :=
    Subtype.ext (by simp [div_eq_mul_inv])
  rw [hdiv] at h1
  exact Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨_, h1⟩

namespace Base89

variable {u x : G} {T : Subgroup G} (H : Base89 u K T)

include H in
theorem exists_n [Finite G] {Eb : Subgroup (MulAut (kBar K))} {rb sb fb : MulAut (kBar K)}
    {k₁ k₂ : kBar K} (hAD : AutData89 H.B Eb (act H.KN x) rb sb fb k₁ k₂) {r s f : G}
    (c : Cfg89T G T (T ⊓ K) (Qs u K T) u (r ^ 2) x f r s) (hra : act H.KN r = rb)
    (hsa : act H.KN s = sb) (hfa : act H.KN f = fb) :
    ∃ n1 n2 : G, n1 ∈ K ∧ n2 ∈ K ∧ n1 * u * n1⁻¹ = u ∧ n1 * f * n1⁻¹ = f ∧
      n1 * r ^ 2 * n1⁻¹ = s ∧ n1 * s * n1⁻¹ = r ^ 2 ∧ n2 * u * n2⁻¹ = u ∧ n2 * f * n2⁻¹ = f ∧
      n2 * r ^ 2 * n2⁻¹ = r ^ 2 ∧ n2 * s * n2⁻¹ = r ^ 2 * s := by
  have hC := H.T_le_C
  have hzK : r ^ 2 ∈ K := c.z_mem.2
  have hsK : s ∈ K := c.s_mem.2
  have hzsK : r ^ 2 * s ∈ K := K.mul_mem hzK hsK
  have hrC : r ∈ centralizer ({u} : Set G) := hC c.r_mem.1
  have hsC : s ∈ centralizer ({u} : Set G) := hC c.s_mem.1
  have hfC : f ∈ centralizer ({u} : Set G) := hC c.f_mem
  have hf2 : orderOf f = 2 := orderOf_eq_prime c.f2 c.f_ne_one
  have hza : act H.KN (r ^ 2) = rb ^ 2 := by rw [act_pow_nat H.KN hrC, hra]
  have hzsa : act H.KN (r ^ 2 * s) = rb ^ 2 * sb := by
    rw [act_mul H.KN (hC c.z_mem.1) hsC, hza, hsa]
  have hmk : ∀ (g : G) (hg : g ∈ K),
      act H.KN g = MulAut.conj (QuotientGroup.mk (⟨g, hg⟩ : ↥K) : kBar K) := fun g hg =>
    act_of_mem_K H.KN H.KC hg
  have hfix : ∀ k : kBar K, fb * MulAut.conj k = MulAut.conj k * fb →
      Back.actHom H.KN ⟨f, hfC⟩ k = k := by
    intro k hk
    have hfb : Back.actHom H.KN ⟨f, hfC⟩ = fb := by rw [← hfa, act_of_mem H.KN hfC]
    rw [hfb]
    apply H.cen
    rw [← mulConjMulInv89, hk]
    group
  have hclass : ∀ (k : kBar K) (c' : ↥K), (QuotientGroup.mk c' : kBar K) = k → ∀ (a b : G)
      (ha : a ∈ K) (hb : b ∈ K), MulAut.conj k * act H.KN a * (MulAut.conj k)⁻¹ = act H.KN b →
      (c' : G) * a * (c' : G)⁻¹ * b⁻¹ ∈ pPrimeCoreOf 2 K := by
    intro k c' hk a b ha hb h
    have hca : (c' : G) * a * (c' : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem c'.2 ha) (K.inv_mem c'.2)
    have h2 : MulAut.conj (k * QuotientGroup.mk ⟨a, ha⟩ * k⁻¹) =
        MulAut.conj (QuotientGroup.mk ⟨b, hb⟩ : kBar K) := by
      rw [map_mul, map_mul, map_inv, ← hmk a ha, ← hmk b hb]
      exact h
    have h3 := H.cen h2
    have h4 : (QuotientGroup.mk (⟨(c' : G) * a * (c' : G)⁻¹, hca⟩ : ↥K) : kBar K) =
        QuotientGroup.mk ⟨b, hb⟩ := by
      have : (⟨(c' : G) * a * (c' : G)⁻¹, hca⟩ : ↥K) = c' * ⟨a, ha⟩ * c'⁻¹ := Subtype.ext rfl
      rw [this, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hk]
      exact h3
    exact mem_O_of_mk_eq hca hb h4
  have hu : ∀ n ∈ K, n * u * n⁻¹ = u := fun n hn =>
    mul_inv_eq_iff_eq_mul.2 (mem_centralizer_singleton_iff.1 (H.KC hn))
  have hfz : f * r ^ 2 = r ^ 2 * f := c.f_cent _ c.z_mem
  have hfs : f * s = s * f := c.f_cent _ c.s_mem
  have hVz : r ^ 2 ∈ zpowers (r ^ 2) ⊔ zpowers s := Subgroup.mem_sup_left (mem_zpowers _)
  have hVs : s ∈ zpowers (r ^ 2) ⊔ zpowers s := Subgroup.mem_sup_right (mem_zpowers _)
  have hVzs : r ^ 2 * s ∈ zpowers (r ^ 2) ⊔ zpowers s := Subgroup.mul_mem _ hVz hVs
  obtain ⟨c1, hc1f, hc1k⟩ := Bk.exists_lift_fixed hf2 hfC H.KN k₁ (hfix k₁ hAD.k1_f)
  obtain ⟨n1, hn1K, hn1f, hn1z, hn1s⟩ := exists_normalizer_lift_klein hzK hsK c.z_sq c.s2
    c.z_comm_s hVs hVz hfz hfs c1.2 hc1f.symm
    (hclass k₁ c1 hc1k _ _ hzK hsK (by rw [hza, hsa]; exact hAD.k1_z))
    (hclass k₁ c1 hc1k _ _ hsK hzK (by rw [hsa, hza]; exact hAD.k1_s))
  obtain ⟨c2, hc2f, hc2k⟩ := Bk.exists_lift_fixed hf2 hfC H.KN k₂ (hfix k₂ hAD.k2_f)
  obtain ⟨n2, hn2K, hn2f, hn2z, hn2s⟩ := exists_normalizer_lift_klein hzK hsK c.z_sq c.s2
    c.z_comm_s hVz hVzs hfz hfs c2.2 hc2f.symm
    (hclass k₂ c2 hc2k _ _ hzK hzK (by rw [hza]; exact hAD.k2_z))
    (hclass k₂ c2 hc2k _ _ hsK hzsK (by rw [hsa, hzsa]; exact hAD.k2_s))
  exact ⟨n1, n2, hn1K, hn2K, hu n1 hn1K, mul_inv_eq_iff_eq_mul.2 hn1f.symm, hn1z, hn1s,
    hu n2 hn2K, mul_inv_eq_iff_eq_mul.2 hn2f.symm, hn2z, hn2s⟩

end Base89

end CFSG.GH74.GLS.C3.Layer1.P89

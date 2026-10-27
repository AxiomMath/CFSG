module

public import CFSG.LocalAnalysis.GH72.G3cFifteen
import CFSG.LocalAnalysis.GH72.InvolutionCentralizer
import CFSG.LocalAnalysis.GH72.Sec4A
import CFSG.LocalAnalysis.GH72.Sec4Bar
import CFSG.LocalAnalysis.GH72.Sec4M0

public section

namespace CFSG.GH72

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

namespace G3c17

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G)

theorem isIsolatedIn_C_mul (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂) {z₁ z₂ : G}
    (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁)
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) :
    IsIsolatedIn (C (z₁ * z₂)) z₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS₁z : (𝔖.S : Subgroup G) ≤ C z₁ := G3cF.le_C_of_central 𝔖 hz₁.2.2
    fun y hy => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hz₁.1 hy).symm
  have hS₂z : (𝔖.S : Subgroup G) ≤ C z₂ := G3cF.le_C_of_central 𝔖
    (fun x hx => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hx hz₂.1)) hz₂.2.2
  have hCC : C z₁ ⊓ C z₂ ≤ C (z₁ * z₂) := fun g hg => by
    obtain ⟨h1, h2⟩ := mem_inf.1 hg
    rw [mem_centralizer_singleton_iff] at h1 h2 ⊢
    rw [← mul_assoc, h1, mul_assoc, h2, ← mul_assoc]
  have hSH : (𝔖.S : Subgroup G) ≤ C (z₁ * z₂) := (le_inf hS₁z hS₂z).trans hCC
  have hz₁H : z₁ ∈ C (z₁ * z₂) := hSH (𝔖.decomp.le_left hz₁.1)
  refine ⟨hz₁H, hz₁.2.1, fun h hh hcomm => ?_⟩
  have hSD : (𝔖.S : Subgroup G) ≤ C (z₁ * z₂) ⊓ C z₁ := le_inf hSH hS₁z
  have hDsyl : IsSylowOf 2 (𝔖.S : Subgroup G) (C (z₁ * z₂) ⊓ C z₁) := G3cF.isSylowOf_S 𝔖 hSD
  have hwD : h * z₁ * h⁻¹ ∈ C (z₁ * z₂) ⊓ C z₁ :=
    mem_inf.2 ⟨mul_mem (mul_mem hh hz₁H) (inv_mem hh), mem_centralizer_singleton_iff.2 hcomm.eq⟩
  have hw2 : IsPGroup 2 (zpowers (h * z₁ * h⁻¹)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_conj_eq, hz₁.2.1, pow_one])
  obtain ⟨d, hdD, hdS⟩ := exists_mem_conj_mem_of_isSylowOf hDsyl hwD hw2
  obtain ⟨hdH, hdz⟩ := mem_inf.1 hdD
  have hkH : d * h ∈ C (z₁ * z₂) := mul_mem hdH hh
  have hvS₁ : d * h * z₁ * (d * h)⁻¹ ∈ 𝔖.S₁ := by
    refine G3cF.conj_mem_left 𝔖 hpf hz₁.1 hz₁.2.1 ?_
    have e : d * h * z₁ * (d * h)⁻¹ = d * (h * z₁ * h⁻¹) * d⁻¹ := by group
    rw [e]
    exact hdS
  have hT : 𝔖.S₂.map (MulAut.conj (d * h)⁻¹).toMonoidHom ≤ C (z₁ * z₂) ⊓ C z₁ := by
    rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hkH) (hSH (𝔖.decomp.le_right hy)))
      (inv_mem (inv_mem hkH)), ?_⟩
    rw [mem_centralizer_singleton_iff]
    have hyv : y * (d * h * z₁ * (d * h)⁻¹) = d * h * z₁ * (d * h)⁻¹ * y :=
      (𝔖.decomp.comm hvS₁ hy).symm
    calc (d * h)⁻¹ * y * (d * h)⁻¹⁻¹ * z₁
        = (d * h)⁻¹ * (y * (d * h * z₁ * (d * h)⁻¹)) * (d * h) := by group
      _ = (d * h)⁻¹ * (d * h * z₁ * (d * h)⁻¹ * y) * (d * h) := by rw [hyv]
      _ = z₁ * ((d * h)⁻¹ * y * (d * h)⁻¹⁻¹) := by group
  obtain ⟨d', hd'D, hd'S⟩ := exists_mem_map_conj_le_of_isSylowOf hDsyl hT
    (𝔖.decomp.isDih₂.isPGroup.map _)
  obtain ⟨hd'H, hd'z⟩ := mem_inf.1 hd'D
  have hgS : 𝔖.S₂.map (MulAut.conj (d' * (d * h)⁻¹)).toMonoidHom ≤ 𝔖.S := by
    rw [← G4b.map_conj_map_conj]
    exact hd'S
  set g := d' * (d * h)⁻¹ with hg
  have hgH : g ∈ C (z₁ * z₂) := mul_mem hd'H (inv_mem hkH)
  have hgS₂ : ∀ y ∈ 𝔖.S₂, g * y * g⁻¹ ∈ 𝔖.S₂ := by
    have hle : 𝔖.S₂ ≤ 𝔖.S₂.comap (MulAut.conj g).toMonoidHom :=
      G3cF.le_of_forall_mul_self_eq_one 𝔖.decomp.isDih₂ fun y hy hyy => by
        by_cases hy1 : y = 1
        · rw [hy1]
          exact one_mem _
        have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
        have hgy : g * y * g⁻¹ ∈ (𝔖.S : Subgroup G) := hgS ⟨y, hy, rfl⟩
        exact G3cF.conj_mem_right 𝔖 hpf hy hy2 hgy
    exact fun y hy => hle hy
  have hgN : g ∈ normalizer (𝔖.S₂ : Set G) := by
    rw [G4b.mem_normalizer_iff_map_conj_eq']
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hgS₂ y hy
    · rw [card_map_of_injective (MulAut.conj g).injective]
  obtain ⟨z₀, -, hz₀2, hZ⟩ := IsDihNonab.exists_inf_centralizer_self_eq 𝔖.decomp.dih₂
  have hcen : ∀ u ∈ 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G), u ≠ 1 → u = z₀ := by
    intro u hu hu1
    rw [hZ] at hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu
    have h2 : ((orderOf z₀ : ℕ) : ℤ) = 2 := by rw [hz₀2]; rfl
    rw [← zpow_mod_orderOf, h2] at hu1 ⊢
    rcases Int.emod_two_eq_zero_or_one j with hj | hj
    · rw [hj, zpow_zero] at hu1
      exact absurd rfl hu1
    · rw [hj, zpow_one]
  have hz₂1 : z₂ ≠ 1 := fun h1 => by
    have h := hz₂.2.1
    rw [h1, orderOf_one] at h
    exact absurd h (by norm_num)
  have hz₂Z : z₂ ∈ 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) :=
    mem_inf.2 ⟨hz₂.1, mem_centralizer_iff.2 fun y hy =>
      mem_centralizer_singleton_iff.1 (hz₂.2.2 hy)⟩
  have hgz₂Z : g * z₂ * g⁻¹ ∈ 𝔖.S₂ ⊓ centralizer (𝔖.S₂ : Set G) :=
    mem_inf.2 ⟨hgS₂ z₂ hz₂.1,
      (mem_normalizer_iff.1 (G4b.mem_normalizer_centralizer hgN) z₂).1 (mem_inf.1 hz₂Z).2⟩
  have hgz₂1 : g * z₂ * g⁻¹ ≠ 1 := fun h1 => hz₂1 (by
    calc z₂ = g⁻¹ * (g * z₂ * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group)
  have hgz₂ : g * z₂ * g⁻¹ = z₂ := (hcen _ hgz₂Z hgz₂1).trans (hcen _ hz₂Z hz₂1).symm
  have hgz₁ : g * z₁ * g⁻¹ = z₁ := by
    have h12 : g * (z₁ * z₂) * g⁻¹ = z₁ * z₂ := by
      rw [mem_centralizer_singleton_iff.1 hgH, mul_inv_cancel_right]
    calc g * z₁ * g⁻¹ = g * (z₁ * z₂) * g⁻¹ * (g * z₂ * g⁻¹)⁻¹ := by group
      _ = z₁ := by rw [h12, hgz₂, mul_inv_cancel_right]
  have hgv : g * (d * h * z₁ * (d * h)⁻¹) * g⁻¹ = z₁ := by
    rw [hg]
    calc d' * (d * h)⁻¹ * (d * h * z₁ * (d * h)⁻¹) * (d' * (d * h)⁻¹)⁻¹ = d' * z₁ * d'⁻¹ := by
          group
      _ = z₁ := by rw [mem_centralizer_singleton_iff.1 hd'z, mul_inv_cancel_right]
  have hv : d * h * z₁ * (d * h)⁻¹ = z₁ :=
    mul_left_cancel (mul_right_cancel (hgv.trans hgz₁.symm))
  calc h * z₁ * h⁻¹ = d⁻¹ * (d * h * z₁ * (d * h)⁻¹) * d := by group
    _ = d⁻¹ * (z₁ * d) := by rw [hv, mul_assoc]
    _ = z₁ := by rw [← mem_centralizer_singleton_iff.1 hdz, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_normal_odd {z₁ z₂ : G} (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁)
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) {H₁ : Subgroup (Bar (C z₁))}
    (hRF : bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥) (hRF' : bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤)
    (hFR : H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))))
    (hTL : bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆) {X : Subgroup G} (hX₁ : X ≤ C z₁) (hX₂ : X ≤ C z₂) :
    ∃ N : Subgroup X, N.Normal ∧ Odd (Nat.card N) ∧ ∀ x : X, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSM : (𝔖.S : Subgroup G) ≤ C z₁ := G3cF.le_C_of_central 𝔖 hz₁.2.2
    fun y hy => mem_centralizer_singleton_iff.2 (𝔖.decomp.comm hz₁.1 hy).symm
  have hS₂M : 𝔖.S₂ ≤ C z₁ := 𝔖.decomp.le_right.trans hSM
  have hS₁2 : IsPGroup 2 𝔖.S₁ := 𝔖.decomp.dih₁.isPGroup
  have hS₂2 : IsPGroup 2 𝔖.S₂ := 𝔖.decomp.isDih₂.isPGroup
  have hS₂H : bar (C z₁) 𝔖.S₂ ≤ H₁ := hTL.trans (commutator_le_self H₁)
  have hD : HasDihedralSylowTwo H₁ := by
    have hS : IsSylowOf 2 (𝔖.S₁ ⊔ 𝔖.S₂) (C z₁) := by
      rw [𝔖.decomp.sup_eq]
      exact G3cF.isSylowOf_S 𝔖 hSM
    obtain ⟨Q, hQ⟩ := G4b.isSylowOf_bar hS 𝔖.decomp.commute 𝔖.decomp.inf_eq hRF hFR hTL
    obtain ⟨a, ha, ⟨e⟩⟩ := IsDihNonab.bar 𝔖.decomp.dih₂ hS₂M
    intro P
    exact ⟨a, by omega, ⟨(Sylow.equiv P Q).trans
      ((((Q : Subgroup H₁).equivMapOfInjective H₁.subtype H₁.subtype_injective).trans
        (MulEquiv.subgroupCongr hQ)).trans e)⟩⟩
  have hz₂M : z₂ ∈ C z₁ := hS₂M hz₂.1
  set zb : Bar (C z₁) := QuotientGroup.mk' (CFSG.oddCore (C z₁)) ⟨z₂, hz₂M⟩ with hzb
  have hzbH : zb ∈ H₁ := hS₂H (mk_mem_bar hz₂M hz₂.1)
  set t : H₁ := ⟨zb, hzbH⟩ with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, Subgroup.orderOf_mk]
    let ψ : 𝔖.S₂ →* Bar (C z₁) := (QuotientGroup.mk' (CFSG.oddCore (C z₁))).comp (inclusion hS₂M)
    have hψ : Function.Injective ψ := fun a b hab =>
      inclusion_injective hS₂M (mk_inj_of_isPGroup hS₂2 a.2 b.2 hab)
    have h := orderOf_injective ψ hψ ⟨z₂, hz₂.1⟩
    rw [Subgroup.orderOf_mk] at h
    exact h.trans hz₂.2.1
  obtain ⟨K, hKC, hKn, hKodd, n, hn⟩ := hasNormalTwoComplement_C_of_hasDihedralSylowTwo hD ht
  have hKN : C t ≤ normalizer (K : Set H₁) := (normal_subgroupOf_iff_le_normalizer hKC).1 hKn
  set φ : X →* Bar (C z₁) := (QuotientGroup.mk' (CFSG.oddCore (C z₁))).comp (inclusion hX₁)
    with hφ
  set K' : Subgroup (Bar (C z₁)) := K.map H₁.subtype with hK'
  have hK'odd : Odd (Nat.card K') := by
    rw [hK', card_map_of_injective H₁.subtype_injective]
    exact hKodd
  have hPH : bar (C z₁) 𝔖.S₁ ≤ normalizer (H₁ : Set (Bar (C z₁))) :=
    (le_centralizer_iff.1 hFR).trans (centralizer_le_normalizer _)
  have hdec : ∀ x : X, ∃ s ∈ bar (C z₁) 𝔖.S₁, ∃ h : H₁, h ∈ C t ∧ s * (h : Bar (C z₁)) = φ x := by
    intro x
    obtain ⟨s, hs, h, hh, hsh⟩ := G4b.mem_sup_of_le_normalizer hPH (hRF' ▸ mem_top (φ x))
    refine ⟨s, hs, ⟨h, hh⟩, ?_, hsh⟩
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    show h * zb = zb * h
    have hxz : φ x * zb = zb * φ x := by
      have hc : inclusion hX₁ x * ⟨z₂, hz₂M⟩ = ⟨z₂, hz₂M⟩ * inclusion hX₁ x :=
        Subtype.ext (mem_centralizer_singleton_iff.1 (hX₂ x.2))
      rw [hφ, hzb, MonoidHom.comp_apply, ← map_mul, hc, map_mul]
    have hsz : s * zb = zb * s := mem_centralizer_iff.1 (hFR hzbH) s hs
    rw [← hsh] at hxz
    refine mul_left_cancel (a := s) ?_
    calc s * (h * zb) = s * h * zb := by group
      _ = zb * (s * h) := hxz
      _ = zb * s * h := by group
      _ = s * zb * h := by rw [hsz]
      _ = s * (zb * h) := by group
  refine ⟨K'.comap φ, ⟨fun a ha g => ?_⟩, ?_, fun x => ?_⟩
  ·
    obtain ⟨s, hs, h, hht, hsh⟩ := hdec g
    obtain ⟨k, hk, hka⟩ := ha
    show φ (g * a * g⁻¹) ∈ K'
    rw [map_mul, map_mul, map_inv, ← hsh, ← hka]
    refine ⟨h * k * h⁻¹, (mem_normalizer_iff.1 (hKN hht) k).1 hk, ?_⟩
    have hc : s * ((h * k * h⁻¹ : H₁) : Bar (C z₁)) = ((h * k * h⁻¹ : H₁) : Bar (C z₁)) * s :=
      mem_centralizer_iff.1 (hFR (h * k * h⁻¹).2) s hs
    simp only [Subgroup.coe_subtype, coe_mul, coe_inv] at hc ⊢
    calc (h : Bar (C z₁)) * k * (h : Bar (C z₁))⁻¹
        = s * ((h : Bar (C z₁)) * k * (h : Bar (C z₁))⁻¹) * s⁻¹ := by rw [hc]; group
      _ = s * h * k * (s * h)⁻¹ := by group
  ·
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(K'.comap φ)) 2 h2
    have hxx : (((x : X) : G)) * ((x : X) : G) = 1 := by
      have h := pow_orderOf_eq_one x
      rw [hx, pow_two] at h
      exact congrArg (fun y : ↥(K'.comap φ) => ((y : X) : G)) h
    have hφx : φ x * φ x = 1 := by
      rw [← map_mul]
      have e : (x : X) * x = 1 := Subtype.ext hxx
      rw [e, map_one]
    have hφx1 : φ x = 1 := eq_one_of_mul_self_of_odd hK'odd x.2 hφx
    have hxO : ((x : X) : G) ∈ O (C z₁) :=
      ⟨inclusion hX₁ x, (QuotientGroup.eq_one_iff _).1 hφx1, rfl⟩
    have hx1 : ((x : X) : G) = 1 := eq_one_of_mul_self_of_odd (card_O_odd (C z₁)) hxO hxx
    have : x = 1 := Subtype.ext (Subtype.ext hx1)
    rw [this, orderOf_one] at hx
    exact absurd hx (by norm_num)
  ·
    obtain ⟨s, hs, h, hht, hsh⟩ := hdec x
    obtain ⟨a, ha⟩ := (isPGroup_bar (H := C z₁) hS₁2) ⟨s, hs⟩
    have hs1 : s ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hhK : h ^ 2 ^ n ∈ K := pow_mem_of_relIndex_eq hKn hn hht
    have hc : Commute s (h : Bar (C z₁)) := mem_centralizer_iff.1 (hFR h.2) s hs
    refine ⟨a + n, ?_⟩
    show φ (x ^ 2 ^ (a + n)) ∈ K'
    rw [map_pow, ← hsh, hc.mul_pow, pow_add, pow_mul, hs1, one_pow, one_mul, mul_comm, pow_mul]
    exact ⟨(h ^ 2 ^ n) ^ 2 ^ a, pow_mem hhK _, by simp⟩

end G3c17

namespace Sec3Setting

section Of

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec3Setting G)
variable (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂)
include hpf

theorem prop_3_17_of
    (h315 : ∀ z₁ z₂ : G, (z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁) →
      (z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) →
      (∃ H₁ : Subgroup (Bar (C z₁)), bar (C z₁) 𝔖.S₁ ⊓ H₁ = ⊥ ∧ bar (C z₁) 𝔖.S₁ ⊔ H₁ = ⊤ ∧
        H₁ ≤ centralizer (bar (C z₁) 𝔖.S₁ : Set (Bar (C z₁))) ∧
        bar (C z₁) 𝔖.S₂ ≤ ⁅H₁, H₁⁆ ∧ IsL2OrA7 (⁅H₁, H₁⁆ : Subgroup (Bar (C z₁))) 7) ∧
      (∃ K₁ : Subgroup (Bar (C z₂)), bar (C z₂) 𝔖.S₂ ⊓ K₁ = ⊥ ∧ bar (C z₂) 𝔖.S₂ ⊔ K₁ = ⊤ ∧
        K₁ ≤ centralizer (bar (C z₂) 𝔖.S₂ : Set (Bar (C z₂))) ∧
        bar (C z₂) 𝔖.S₁ ≤ ⁅K₁, K₁⁆ ∧
        (IsL2OrA7 (⁅K₁, K₁⁆ : Subgroup (Bar (C z₂))) 5 ∨ ⁅K₁, K₁⁆ = bar (C z₂) 𝔖.S₁)))
    (z₁ z₂ : G) (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁)
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) :
    HasNormalTwoComplement (C (z₁ * z₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hiso := G3c17.isIsolatedIn_C_mul 𝔖 hpf hz₁ hz₂
  have hcov : ∀ h ∈ C (z₁ * z₂), ∃ p ∈ C (z₁ * z₂) ⊓ C z₁, p⁻¹ * h ∈ O (C (z₁ * z₂)) :=
    fun h hh => hiso.exists_mem_C hh
  have hX₂ : C (z₁ * z₂) ⊓ C z₁ ≤ C z₂ := fun g hg => by
    obtain ⟨h1, h2⟩ := mem_inf.1 hg
    rw [mem_centralizer_singleton_iff] at h1 h2 ⊢
    refine mul_left_cancel (a := z₁) ?_
    calc z₁ * (g * z₂) = z₁ * g * z₂ := by group
      _ = g * z₁ * z₂ := by rw [h2]
      _ = g * (z₁ * z₂) := by group
      _ = z₁ * z₂ * g := h1
      _ = z₁ * (z₂ * g) := by group
  obtain ⟨⟨H₁, hRF, hRF', hFR, hTL, -⟩, -⟩ := h315 z₁ z₂ hz₁ hz₂
  obtain ⟨N, hNn, hNodd, hpow⟩ :=
    G3c17.exists_normal_odd 𝔖 hz₁ hz₂ hRF hRF' hFR hTL inf_le_right hX₂
  have h2 : IsPGroup 2 (Bar (C (z₁ * z₂))) :=
    isPGroup_of_surjective_of_odd_normal (oddCore_quotient_oddCore_eq_bot _) _
      (surjective_of_covers inf_le_left hcov) N hNn hNodd hpow
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 h2
  have hsub : (O (C (z₁ * z₂))).subgroupOf (C (z₁ * z₂)) = CFSG.oddCore (C (z₁ * z₂)) := by
    rw [← comap_subtype, comap_map_eq_self_of_injective (C (z₁ * z₂)).subtype_injective]
  refine ⟨O (C (z₁ * z₂)), map_subtype_le _, ?_, card_O_odd _, n, ?_⟩
  · rw [hsub]
    exact CFSG.oddCore_normal _
  · unfold relIndex
    rw [hsub]
    exact hn

end Of

section Frozen

variable {G : Type} [Group G] [Finite G]
variable (𝔖 : Sec3Setting G) (hpf : HasProductFusion 𝔖.S₁ 𝔖.S₂)
include hpf

theorem prop_3_17 (z₁ z₂ : G) (hz₁ : z₁ ∈ 𝔖.S₁ ∧ orderOf z₁ = 2 ∧ 𝔖.S₁ ≤ C z₁)
    (hz₂ : z₂ ∈ 𝔖.S₂ ∧ orderOf z₂ = 2 ∧ 𝔖.S₂ ≤ C z₂) :
    HasNormalTwoComplement (C (z₁ * z₂)) :=
  prop_3_17_of 𝔖 hpf (prop_3_15 𝔖 hpf) z₁ z₂ hz₁ hz₂

end Frozen

end Sec3Setting

end CFSG.GH72

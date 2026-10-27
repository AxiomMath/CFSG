module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Aut
public import CFSG.GH74.GLS.C3.Layer1.Thm1Transport

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1

theorem exists_mul_mem_cmk_of_centralizes' {G : Type} [Group G] [Finite G] {C K P : Subgroup G}
    (hKC : K ≤ C) (hKN : ∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) (hPK : IsSylowOf 2 P K)
    (hcen : Function.Injective (MulAut.conj : kBar K →* MulAut (kBar K)))
    (hAutC : AutLevelC' (kBar K)) (hPdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥P n)
    {f d : G} (hfC : f ∈ C) (hf2 : orderOf f = 2) (hfP : ∀ p ∈ P, f * p = p * f)
    (hfout : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hdC : d ∈ C) (hd2 : ∃ k : ℕ, d ^ (2 ^ k) = 1) (hdP : ∀ p ∈ P, d * p = p * d) :
    ∃ z₀ ∈ P, orderOf z₀ = 2 ∧ (∀ p ∈ P, z₀ * p = p * z₀) ∧ ∃ a b : ℤ, d * z₀ ^ a * f ^ b ∈ CMK C K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ := Back.actHom hKN with hφ
  have hPK' : P ≤ K := hPK.le
  have hPC : P ≤ C := hPK'.trans hKC
  have hP2 : IsPGroup 2 ↥P := hPK.isPGroup
  have hPker : ∀ p ∈ P.subgroupOf C, φ p = 1 → p = 1 := by
    intro p hp hφp
    have hp' : (p : G) ∈ P := hp
    have h1 := Back.actHom_of_mem hKN (hPK' hp') p.2
    have h2 : (MulAut.conj (QuotientGroup.mk (⟨(p : G), hPK' hp'⟩ : ↥K) : kBar K)) =
        MulAut.conj 1 := by
      rw [map_one, ← h1]
      exact hφp
    have h3 := hcen h2
    have h4 : (⟨(p : G), hPK' hp'⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : (p : G) ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hPK' hp', h4⟩
    have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K hP2
    have h7 : (p : G) ∈ P ⊓ pPrimeCoreOf 2 K := ⟨hp', h5⟩
    rw [h6, Subgroup.mem_bot] at h7
    exact Subtype.ext h7
  have hSylK : IsSylowOf 2 (P.subgroupOf C) (K.subgroupOf C) := by
    rw [← isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, inf_eq_left.2 hKC]
    exact hPK
  set Pb := (P.subgroupOf C).map φ with hPb
  have hSyl : IsSylowOf 2 Pb (innAut (kBar K)) := by
    have := isSylowOf_map_hom φ hSylK
    rwa [hφ, map_actHom_K hKC hKN] at this
  have hPinn : Pb ≤ innAut (kBar K) := hSyl.le
  have hinj : Function.Injective (φ.comp (P.subgroupOf C).subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hPker a a.2 ha)
  have hrange : (φ.comp (P.subgroupOf C).subtype).range = Pb := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eP : ↥P ≃* ↥Pb :=
    ((Subgroup.subgroupOfEquivOfLe hPC).symm).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
  have hdih : ∃ n : ℕ, 3 ≤ n ∧ IsDihedralTwoGroup ↥Pb n := by
    obtain ⟨n, hn3, hn⟩ := hPdih
    exact ⟨n, hn3, isDihedralTwoGroup_of_equiv eP.symm hn⟩
  set σ := φ ⟨f, hfC⟩ with hσdef
  set γ := φ ⟨d, hdC⟩ with hγdef
  have hfsq : (⟨f, hfC⟩ : ↥C) * ⟨f, hfC⟩ = 1 := Subtype.ext (by
    have := pow_orderOf_eq_one f
    rwa [hf2, sq] at this)
  have hσσ : σ * σ = 1 := by rw [hσdef, ← map_mul, hfsq, map_one]
  have hσ1 : σ ≠ 1 := fun h => hfout (h ▸ (innAut (kBar K)).one_mem)
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hσc : ∀ q ∈ Pb, σ * q = q * σ := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hσdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hfP _ hm)
  have hγc : ∀ q ∈ Pb, γ * q = q * γ := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hγdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hdP _ hm)
  have hγ2 : ∃ k : ℕ, γ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := hd2
    refine ⟨k, ?_⟩
    rw [hγdef, ← map_pow]
    have : (⟨d, hdC⟩ : ↥C) ^ (2 ^ k) = 1 := Subtype.ext hk
    rw [this, map_one]
  obtain ⟨zb, hzbP, hzb2, hzbc, hγz⟩ := hAutC Pb hPinn hSyl hdih σ γ hσ2 hfout hσc hγc hγ2
  obtain ⟨m, hm, hmz⟩ := hzbP
  have hinjφ : ∀ a b : ↥C, a ∈ P.subgroupOf C → b ∈ P.subgroupOf C → φ a = φ b → a = b := by
    intro a b ha hb hab
    have h1 : φ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h2 : a⁻¹ * b ∈ P.subgroupOf C := (P.subgroupOf C).mul_mem ((P.subgroupOf C).inv_mem ha) hb
    have h3 := hPker _ h2 h1
    calc a = a * (a⁻¹ * b) := by rw [h3, mul_one]
      _ = b := by group
  have hmcomm : ∀ p ∈ P, (m : G) * p = p * (m : G) := by
    intro p hp
    have hp' : (⟨p, hPC hp⟩ : ↥C) ∈ P.subgroupOf C := hp
    have h1 : φ (m * ⟨p, hPC hp⟩) = φ (⟨p, hPC hp⟩ * m) := by
      rw [map_mul, map_mul, hmz]
      exact hzbc _ ⟨_, hp', rfl⟩
    have h2 := hinjφ _ _ ((P.subgroupOf C).mul_mem hm hp') ((P.subgroupOf C).mul_mem hp' hm) h1
    exact congrArg Subtype.val h2
  have hmm : (m : G) * m = 1 := by
    have hzbzb : zb * zb = 1 := by
      have := pow_orderOf_eq_one zb
      rwa [hzb2, sq] at this
    have h1 : φ (m * m) = φ 1 := by rw [map_mul, hmz, hzbzb, map_one]
    have h2 := hinjφ _ _ ((P.subgroupOf C).mul_mem hm hm) (P.subgroupOf C).one_mem h1
    exact congrArg Subtype.val h2
  have hm1 : (m : G) ≠ 1 := by
    intro h
    have hm1' : m = 1 := Subtype.ext h
    rw [hm1', map_one] at hmz
    rw [← hmz, orderOf_one] at hzb2
    omega
  have hm2 : orderOf (m : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hmm) hm1
  have hcomm : ∀ u ∈ zpowers zb, ∀ w ∈ zpowers σ, u * w = w * u := by
    intro u hu w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    have hc : Commute σ zb := by
      rw [← hmz]; exact hσc _ ⟨m, hm, rfl⟩
    exact (Commute.zpow_zpow (show Commute zb σ from hc.symm) i j).eq
  obtain ⟨u, hu, w, hw, hγeq⟩ := Thm1P310.exists_mul_of_mem_sup hcomm hγz
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.1 hu
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.1 hw
  refine ⟨(m : G), hm, hm2, hmcomm, -a, -b, ?_⟩
  set δ : ↥C := ⟨d, hdC⟩ * m ^ (-a) * ⟨f, hfC⟩ ^ (-b) with hδ
  have hφδ : φ δ = 1 := by
    rw [hδ, map_mul, map_mul, map_zpow, map_zpow, hmz, ← hγdef, ← hσdef, hγeq]
    have hc : Commute σ zb := by
      rw [← hmz]; exact hσc _ ⟨m, hm, rfl⟩
    have h1 : zb ^ a * σ ^ b * zb ^ (-a) * σ ^ (-b) = 1 := by
      have hcz : σ ^ b * zb ^ (-a) = zb ^ (-a) * σ ^ b :=
        (Commute.zpow_zpow hc.symm (-a) b).eq.symm
      calc zb ^ a * σ ^ b * zb ^ (-a) * σ ^ (-b) = zb ^ a * (σ ^ b * zb ^ (-a)) * σ ^ (-b) := by
            rw [mul_assoc (zb ^ a)]
        _ = zb ^ a * (zb ^ (-a) * σ ^ b) * σ ^ (-b) := by rw [hcz]
        _ = 1 := by group
    exact h1
  have hker : δ ∈ φ.ker := hφδ
  rw [hφ, Back.actHom_ker hKN] at hker
  have hδmem : (δ : G) ∈ CMK C K := hker
  have hδval : (δ : G) = d * (m : G) ^ (-a) * f ^ (-b) := by
    rw [hδ]; simp
  rw [← hδval]
  exact hδmem

end CFSG.GH74.GLS.C3.Layer1.Thm1

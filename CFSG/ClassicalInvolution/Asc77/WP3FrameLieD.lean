module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieC
import CFSG.ClassicalInvolution.Asc77.AscE187Img

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem isUniqueInvolution_modOdd {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) :
    IsUniqueInvolution (modOdd z (exactCore z N))
      (oddQuotMk z ⟨w, C.involution_mem_centralizer hN hw⟩) := by
  have hwE := C.involution_mem_exactCore hN hw
  have hwC := C.involution_mem_centralizer hN hw
  have hcw := isCentralInvolution_of_isClassicalMember hw
  set Cz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCz
  set E' : Subgroup ↥Cz := (exactCore z N).subgroupOf Cz with hE'
  have hU : IsUniqueInvolution E' ⟨w, hwC⟩ := by
    refine ⟨hwE, fun h => hcw.ne_one (congrArg Subtype.val h), Subtype.ext hcw.sq, ?_⟩
    intro y hy hy2
    rcases eq_one_or_eq_of_mem_exactCore hw C.hp C.hq hy (congrArg Subtype.val hy2) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hodd : Odd (Nat.card ↥(componentClassificationOddCore ↥Cz ⊓ E')) :=
    (OddCore.odd_card ↥Cz).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact isUniqueInvolution_map_mk_of_odd hodd hU

theorem exists_conj_of_oddQuotMk_eq {w₁ w₂ : G} (h₁ : w₁ ∈ exactLayer Ω z)
    (h₂ : w₂ ∈ exactLayer Ω z) (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1)
    (heq : oddQuotMk z ⟨w₁, exactLayer_le_centralizer Ω z h₁⟩ =
      oddQuotMk z ⟨w₂, exactLayer_le_centralizer Ω z h₂⟩) :
    ∃ o ∈ oddCoreIn (exactLayer Ω z), w₁ = o * w₂ * o⁻¹ := by
  have hker : (⟨w₁, h₁⟩ : ↥(exactLayer Ω z)) * ⟨w₂, h₂⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω z) z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes C.hs.normalizes] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hinv : w₂⁻¹ = w₂ := inv_eq_of_mul_eq_one_right hs₂
  have hmem' : w₁ * w₂ ∈ oddCoreIn (exactLayer Ω z) := by
    have : ((⟨w₁, h₁⟩ * ⟨w₂, h₂⟩⁻¹ : ↥(exactLayer Ω z)) : G) = w₁ * w₂ := by
      simp [hinv]
    rwa [this] at hmem
  exact exists_conj_of_mul_mem hs₂ hs₁ (odd_card_oddCoreIn _) hmem'

theorem exists_lift_psi (j : Fin C.D.card) (k : (compModel C.D j).K) :
    ∃ (y : G) (hy : y ∈ exactLayer Ω z),
      oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ = C.psi j k := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective _ (C.D.hom j k)
  refine ⟨y, y.2, ?_⟩
  have h : C.psi j k = sectionQuotientHom C.hs.normalizes (C.D.hom j k) := rfl
  rw [h, ← hy]
  rfl

end ChainCtx

end Link

section Conj

theorem ChainPairData.center₁_conj {K : Type*} [Group K] {𝓕 : Set (Subgroup K)}
    {R₁ R₂ : Subgroup K} {τ₁ τ₂ ν₁ ν₂ : K} (h : ChainPairData 𝓕 R₁ R₂ τ₁ τ₂ ν₁ ν₂) (g : K) :
    ∀ c ∈ conjSub g R₁, (∀ r ∈ conjSub g R₁, c * r = r * c) → c = 1 ∨ c = g * τ₁ * g⁻¹ := by
  rintro _ ⟨c₀, hc₀, rfl⟩ hcc
  have hcc' : ∀ r ∈ R₁, c₀ * r = r * c₀ := by
    intro r hr
    have := hcc _ ⟨r, hr, rfl⟩
    have h2 : g * (c₀ * r) * g⁻¹ = g * (r * c₀) * g⁻¹ := by
      calc g * (c₀ * r) * g⁻¹ = (MulAut.conj g).toMonoidHom c₀ * (MulAut.conj g).toMonoidHom r := by
            simp [mul_assoc]
        _ = (MulAut.conj g).toMonoidHom r * (MulAut.conj g).toMonoidHom c₀ := this
        _ = g * (r * c₀) * g⁻¹ := by simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel h2)
  rcases h.center₁ c₀ hc₀ hcc' with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr rfl

end Conj

section Link2

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  (C : ChainCtx p f Ω z)

namespace ChainCtx

include C

theorem K_comp : ∃ R_K ∈ fundamentalSubgroups (C.D.tag C.i₀) (compModel C.D C.i₀).D,
    modOdd z (exactCore z C.K) = R_K.map (C.psi C.i₀) := by
  obtain ⟨κ, R_K, hR_K, hmodK⟩ := C.exists_fund_of_mem (N := C.K) ⟨C.hK, C.hKtq⟩
  rcases C.eq_i₀_or_i₁ κ with rfl | rfl
  · exact ⟨R_K, hR_K, hmodK.symm⟩
  · exfalso
    obtain ⟨R₁, hR₁, R₂, hR₂, τ₁, τ₂, ν₁, ν₂, hd⟩ := C.pair
    obtain ⟨g, hg⟩ := C.single C.i₁ C.tag₁ R₁ hR₁ R_K hR_K
    have hzcl := isClassicalMember_of_twin C.hΩ C.hK C.hKz
    have hWz := C.oddQuotMk_involution ⟨C.hK, C.hKtq⟩ hzcl C.i₁ C.tag₁ hR_K
      (τ := g * τ₁ * g⁻¹) (by rw [hg]; exact hd.center₁_conj g) hmodK.symm
    obtain ⟨r, hr, hrc⟩ := hd.not_central
    have hcen := oddQuotMk_central (ChainLift.hzC (z := z)) (C.psi C.i₁ (g * r * g⁻¹))
    have hz1 : oddQuotMk z ⟨z, ChainLift.hzC⟩ = C.psi C.i₁ (g * τ₁ * g⁻¹) := hWz
    rw [hz1] at hcen
    apply hrc
    apply ChainFrame.mem_center_of_conj_mem g
    refine C.psi_ker C.i₁ (MonoidHom.mem_ker.mpr ?_)
    have e : g * (τ₁ * r * τ₁⁻¹ * r⁻¹) * g⁻¹ =
        (g * τ₁ * g⁻¹) * (g * r * g⁻¹) * (g * τ₁ * g⁻¹)⁻¹ * (g * r * g⁻¹)⁻¹ := by group
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact ChainFrame.commutator_eq_one_of_comm hcen

theorem z_mem_exactLayer : z ∈ exactLayer Ω z := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hKN : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩
  exact exactCore_le_exactLayer hKN (C.involution_mem_exactCore hKN hKcl)

end ChainCtx

end Link2

section Link3

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}
  {C : ChainCtx p f Ω z} (L : ChainLift C)

namespace ChainLift

theorem t_mem_exactLayer : L.t ∈ exactLayer Ω z :=
  exactCore_le_exactLayer L.hJ (C.involution_mem_exactCore L.hJ L.hJt)

theorem t_sq : L.t * L.t = 1 := (isCentralInvolution_of_isClassicalMember L.hJt).sq

theorem link_z {N : Subgroup G} {w : G} (hN : N ∈ tqMembers Ω z)
    (hw : IsClassicalMember p f N w) :
    ∃ h ∈ exactLayer Ω z, w = h * z * h⁻¹ ∨ w = h * L.t * h⁻¹ := by
  have hwC := C.involution_mem_centralizer hN hw
  have hwY : w ∈ exactLayer Ω z := exactCore_le_exactLayer hN (C.involution_mem_exactCore hN hw)
  have hwsq := (isCentralInvolution_of_isClassicalMember hw).sq
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  have hKN : C.K ∈ tqMembers Ω z := ⟨C.hK, C.hKtq⟩
  have hzE : z ∈ exactCore z C.K := C.involution_mem_exactCore hKN hKcl
  have hzY : z ∈ exactLayer Ω z := C.z_mem_exactLayer
  have hzC : z ∈ Subgroup.centralizer ({z} : Set G) := ChainLift.hzC
  obtain ⟨j, R, hR, hmod⟩ := C.exists_fund_of_mem hN
  rcases C.eq_i₀_or_i₁ j with rfl | rfl
  ·
    obtain ⟨R_K, hR_K, hmodK⟩ := C.K_comp
    obtain ⟨g, hg⟩ := C.single C.i₀ (Or.inl C.tag₀) R hR R_K hR_K
    have hzbmem : oddQuotMk z ⟨z, hzC⟩ ∈ R_K.map (C.psi C.i₀) :=
      hmodK ▸ oddQuotMk_mem_modOdd hzE hzC
    obtain ⟨r, hrR, hr⟩ := hzbmem
    rw [hg] at hrR
    obtain ⟨r₀, hr₀, rfl⟩ := hrR
    have hcen := oddQuotMk_central hzC (C.psi C.i₀ g)
    have hr₀z : C.psi C.i₀ r₀ = oddQuotMk z ⟨z, hzC⟩ := by
      have h1 : C.psi C.i₀ ((MulAut.conj g).toMonoidHom r₀) = oddQuotMk z ⟨z, hzC⟩ := hr
      have h2 : (MulAut.conj g).toMonoidHom r₀ = g * r₀ * g⁻¹ := rfl
      rw [h2, map_mul, map_mul, map_inv] at h1
      calc C.psi C.i₀ r₀ = (C.psi C.i₀ g)⁻¹ * (C.psi C.i₀ g * C.psi C.i₀ r₀ *
            (C.psi C.i₀ g)⁻¹) * C.psi C.i₀ g := by group
        _ = (C.psi C.i₀ g)⁻¹ * oddQuotMk z ⟨z, hzC⟩ * C.psi C.i₀ g := by rw [h1]
        _ = oddQuotMk z ⟨z, hzC⟩ := by rw [mul_assoc, hcen, ← mul_assoc, inv_mul_cancel, one_mul]
    have hzbN : oddQuotMk z ⟨z, hzC⟩ ∈ modOdd z (exactCore z N) := by
      rw [← hmod, ← hr₀z]
      exact ⟨r₀, hr₀, rfl⟩
    have hzbsq : oddQuotMk z ⟨z, hzC⟩ * oddQuotMk z ⟨z, hzC⟩ = 1 := by
      rw [← map_mul]
      have : (⟨z, hzC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) * ⟨z, hzC⟩ = 1 :=
        Subtype.ext C.hKz.sq
      rw [this, map_one]
    have hzb1 : oddQuotMk z ⟨z, hzC⟩ ≠ 1 := fun h =>
      C.hKz.ne_one (congrArg Subtype.val
        (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))
    have hU := C.isUniqueInvolution_modOdd hN hw
    have heq : oddQuotMk z ⟨w, hwC⟩ = oddQuotMk z ⟨z, hzC⟩ :=
      ((hU.unique _ hzbN hzbsq).resolve_left hzb1).symm
    obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hzY hwsq C.hKz.sq heq
    exact ⟨o, oddCoreIn_le _ ho, Or.inl hwo⟩
  ·
    obtain ⟨g, hg⟩ := C.single C.i₁ C.tag₁ L.R₁ L.hR₁ R hR
    have hτ : ∀ c ∈ R, (∀ r ∈ R, c * r = r * c) → c = 1 ∨ c = g * L.τ₁ * g⁻¹ := by
      rw [hg]
      exact L.hd.center₁_conj g
    have hWz := C.oddQuotMk_involution hN hw C.i₁ C.tag₁ hR hτ hmod.symm
    obtain ⟨y, hy, hyψ⟩ := C.exists_lift_psi C.i₁ g
    have hyC := exactLayer_le_centralizer Ω z hy
    have htC := L.ht
    have hconj : y * L.t * y⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      mul_mem (mul_mem hyC htC) (inv_mem hyC)
    have hconjY : y * L.t * y⁻¹ ∈ exactLayer Ω z :=
      mul_mem (mul_mem hy L.t_mem_exactLayer) (inv_mem hy)
    have hbar : oddQuotMk z ⟨y * L.t * y⁻¹, hconj⟩ = C.psi C.i₁ (g * L.τ₁ * g⁻¹) := by
      have : (⟨y * L.t * y⁻¹, hconj⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
          ⟨y, hyC⟩ * ⟨L.t, htC⟩ * ⟨y, hyC⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hyψ, L.htbar, map_mul, map_mul, map_inv]
    have hsq : (y * L.t * y⁻¹) * (y * L.t * y⁻¹) = 1 := by
      have e : (y * L.t * y⁻¹) * (y * L.t * y⁻¹) = y * (L.t * L.t) * y⁻¹ := by group
      rw [e, L.t_sq]
      group
    obtain ⟨o, ho, hwo⟩ := C.exists_conj_of_oddQuotMk_eq hwY hconjY hwsq hsq
      (hWz.trans hbar.symm)
    refine ⟨o * y, mul_mem (oddCoreIn_le _ ho) hy, Or.inr ?_⟩
    rw [hwo]
    group

theorem exists_swap_zt (htrans : ∀ M ∈ Ω, ∃ g : G, conjSub g C.K = M) :
    ∃ s : G, s * z * s⁻¹ = L.t ∧ s * L.t * s⁻¹ = z := by
  have hKcl : IsClassicalMember p f C.K z := isClassicalMember_of_twin C.hΩ C.hK C.hKz
  obtain ⟨g₀, hg₀⟩ := htrans L.J L.hJ.1
  have hgz : g₀ * z * g₀⁻¹ = L.t := by
    have h1 : IsUniqueInvolution (conjSub g₀ C.K) (g₀ * z * g₀⁻¹) :=
      ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq (hKcl.conj g₀)
    rw [hg₀] at h1
    exact h1.eq (ConnectedA2.isUniqueInvolution_of_isClassicalMember C.hp C.hq L.hJt)
  have htK : L.t ∈ trivialOnQuot C.K := L.frameData.tq_t C.hp C.hq C.hΩ
  have hK''tq : conjSub g₀⁻¹ C.K ∈ tqMembers Ω z := by
    refine ⟨C.hΩ.conjInvariant g₀⁻¹ C.K C.hK, ?_⟩
    have h := trivialOnQuot_conjSub htK g₀⁻¹
    have e : g₀⁻¹ * L.t * g₀⁻¹⁻¹ = z := by rw [← hgz]; group
    rwa [e] at h
  obtain ⟨h, hh, hcase⟩ := L.link_z hK''tq (hKcl.conj g₀⁻¹)
  have hhz : h * z * h⁻¹ = z :=
    conj_eq_of_mem_centralizer_singleton (exactLayer_le_centralizer Ω z hh)
  rcases hcase with hc | hc
  · exfalso
    have h2 : g₀⁻¹ * z * g₀⁻¹⁻¹ = z := hc.trans hhz
    apply L.t_ne_z
    rw [← hgz]
    calc g₀ * z * g₀⁻¹ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [h2]
      _ = z := by group
  · refine ⟨g₀ * h, ?_, ?_⟩
    · calc g₀ * h * z * (g₀ * h)⁻¹ = g₀ * (h * z * h⁻¹) * g₀⁻¹ := by group
        _ = g₀ * z * g₀⁻¹ := by rw [hhz]
        _ = L.t := hgz
    · calc g₀ * h * L.t * (g₀ * h)⁻¹ = g₀ * (h * L.t * h⁻¹) * g₀⁻¹ := by group
        _ = g₀ * (g₀⁻¹ * z * g₀⁻¹⁻¹) * g₀⁻¹ := by rw [hc]
        _ = z := by group

end ChainLift

end Link3

end CFSG.ClassicalInvolution.Asc77

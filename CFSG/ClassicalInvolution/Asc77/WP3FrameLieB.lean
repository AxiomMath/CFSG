module

public import CFSG.ClassicalInvolution.Asc77.WP3FrameLieA
import CFSG.ClassicalInvolution.Balance.GoodDataBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_commuting (z : G) {w₁ w₂ : G} (h₁ : w₁ ∈ Subgroup.centralizer ({z} : Set G))
    (h₂ : w₂ ∈ Subgroup.centralizer ({z} : Set G)) (hs₁ : w₁ * w₁ = 1) (hs₂ : w₂ * w₂ = 1)
    (hcomm : oddQuotMk z ⟨w₁, h₁⟩ * oddQuotMk z ⟨w₂, h₂⟩ =
      oddQuotMk z ⟨w₂, h₂⟩ * oddQuotMk z ⟨w₁, h₁⟩) :
    ∃ o₁ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
      ∃ o₂ ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)),
        (o₁ * w₁ * o₁⁻¹) * (o₂ * w₂ * o₂⁻¹) = (o₂ * w₂ * o₂⁻¹) * (o₁ * w₁ * o₁⁻¹) := by
  classical
  set Cz : Subgroup G := Subgroup.centralizer ({z} : Set G) with hCz
  set N₀ := componentClassificationOddCore ↥Cz with hN₀
  set x₁ := oddQuotMk z ⟨w₁, h₁⟩ with hx₁
  set x₂ := oddQuotMk z ⟨w₂, h₂⟩ with hx₂
  have hsq₁ : x₁ * x₁ = 1 := by
    rw [hx₁, ← map_mul]
    have : (⟨w₁, h₁⟩ : ↥Cz) * ⟨w₁, h₁⟩ = 1 := Subtype.ext hs₁
    rw [this, map_one]
  have hsq₂ : x₂ * x₂ = 1 := by
    rw [hx₂, ← map_mul]
    have : (⟨w₂, h₂⟩ : ↥Cz) * ⟨w₂, h₂⟩ = 1 := Subtype.ext hs₂
    rw [this, map_one]
  have hpair : ∀ a ∈ ({x₁, x₂} : Set (OddQuot z)), ∀ b ∈ ({x₁, x₂} : Set (OddQuot z)),
      a * b = b * a := by
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hcomm
    · exact hcomm.symm
    · rfl
  have hsqs : ∀ a ∈ ({x₁, x₂} : Set (OddQuot z)), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl
    exacts [hsq₁, hsq₂]
  have hE : IsElemAbelian 2 (Subgroup.closure ({x₁, x₂} : Set (OddQuot z))) := by
    have hcm := ChainFrame.commutes_closure hpair
    refine ⟨⟨⟨fun a b => Subtype.ext (hcm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
    rw [pow_two]
    exact ChainFrame.sq_closure hsqs hpair x hx
  obtain ⟨H, hHe, hHmap, -⟩ := GoodData.exists_isElemAbelian_lift_map N₀ (OddCore.odd_card _) _ hE
  have hmem : ∀ x ∈ ({x₁, x₂} : Set (OddQuot z)), ∃ a ∈ H, QuotientGroup.mk' N₀ a = x := by
    intro x hx
    have : x ∈ H.map (QuotientGroup.mk' N₀) := by
      rw [hHmap]
      exact Subgroup.subset_closure hx
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨a, ha, rfl⟩
  have hconj : ∀ (w : G) (hw : w ∈ Cz) (a : ↥Cz), a ∈ H → w * w = 1 →
      QuotientGroup.mk' N₀ a = oddQuotMk z ⟨w, hw⟩ →
      ∃ o ∈ oddCoreIn Cz, (a : G) = o * w * o⁻¹ := by
    intro w hw a ha hw2 hmk
    have ha2 : a * a = 1 := by
      have := hHe.2 a ha
      rwa [pow_two] at this
    have haG : (a : G) * a = 1 := congrArg Subtype.val ha2
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have h1 : a⁻¹ * (⟨w, hw⟩ : ↥Cz) ∈ N₀ := QuotientGroup.eq.mp hmk
    rw [hinv] at h1
    have hmul : (a : G) * w ∈ oddCoreIn Cz := ⟨a * ⟨w, hw⟩, h1, rfl⟩
    exact exists_conj_of_mul_mem hw2 haG (odd_card_oddCoreIn Cz) hmul
  obtain ⟨a, ha, hax⟩ := hmem x₁ (Set.mem_insert _ _)
  obtain ⟨b, hb, hbx⟩ := hmem x₂ (Set.mem_insert_of_mem _ rfl)
  obtain ⟨o₁, ho₁, hao⟩ := hconj w₁ h₁ a ha hs₁ hax
  obtain ⟨o₂, ho₂, hbo⟩ := hconj w₂ h₂ b hb hs₂ hbx
  refine ⟨o₁, ho₁, o₂, ho₂, ?_⟩
  rw [← hao, ← hbo]
  have h := hHe.1.is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩
  have h2 := congrArg (fun x : H => ((x : ↥Cz) : G)) h
  simpa using h2

end Lift

section Chain

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)} {z : G}

structure ChainLift (C : ChainCtx p f Ω z) where
  R₁ : Subgroup (compModel C.D C.i₁).K
  R₂ : Subgroup (compModel C.D C.i₁).K
  τ₁ : (compModel C.D C.i₁).K
  τ₂ : (compModel C.D C.i₁).K
  ν₁ : (compModel C.D C.i₁).K
  ν₂ : (compModel C.D C.i₁).K
  hR₁ : R₁ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  hR₂ : R₂ ∈ fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D
  hd : ChainPairData (fundamentalSubgroups (C.D.tag C.i₁) (compModel C.D C.i₁).D) R₁ R₂ τ₁ τ₂ ν₁ ν₂
  J : Subgroup G
  K' : Subgroup G
  t : G
  z' : G
  ht : t ∈ Subgroup.centralizer ({z} : Set G)
  hz' : z' ∈ Subgroup.centralizer ({z} : Set G)
  hJ : J ∈ tqMembers Ω z
  hK' : K' ∈ tqMembers Ω z
  hJt : IsClassicalMember p f J t
  hK'z' : IsClassicalMember p f K' z'
  hJimg : modOdd z (exactCore z J) = R₁.map (C.psi C.i₁)
  hK'img : modOdd z (exactCore z K') = R₂.map (C.psi C.i₁)
  htbar : oddQuotMk z ⟨t, ht⟩ = C.psi C.i₁ τ₁
  hz'bar : oddQuotMk z ⟨z', hz'⟩ = C.psi C.i₁ τ₂
  htz' : t * z' = z' * t

theorem ChainCtx.exists_lift (C : ChainCtx p f Ω z) : Nonempty (ChainLift C) := by
  obtain ⟨R₁, hR₁, R₂, hR₂, τ₁, τ₂, ν₁, ν₂, hd⟩ := C.pair
  obtain ⟨N₁, hN₁, hN₁img⟩ := C.exists_member_of_fund C.i₁ C.tag₁ hR₁
  obtain ⟨N₂, hN₂, hN₂img⟩ := C.exists_member_of_fund C.i₁ C.tag₁ hR₂
  obtain ⟨w₁, hw₁⟩ := C.hΩ.classical N₁ hN₁.1
  obtain ⟨w₂, hw₂⟩ := C.hΩ.classical N₂ hN₂.1
  have hw₁C := C.involution_mem_centralizer hN₁ hw₁
  have hw₂C := C.involution_mem_centralizer hN₂ hw₂
  have hw₁bar : oddQuotMk z ⟨w₁, hw₁C⟩ = C.psi C.i₁ τ₁ :=
    C.oddQuotMk_involution hN₁ hw₁ C.i₁ C.tag₁ hR₁ hd.center₁ hN₁img
  have hw₂bar : oddQuotMk z ⟨w₂, hw₂C⟩ = C.psi C.i₁ τ₂ :=
    C.oddQuotMk_involution hN₂ hw₂ C.i₁ C.tag₁ hR₂ hd.center₂ hN₂img
  have hcomm : oddQuotMk z ⟨w₁, hw₁C⟩ * oddQuotMk z ⟨w₂, hw₂C⟩ =
      oddQuotMk z ⟨w₂, hw₂C⟩ * oddQuotMk z ⟨w₁, hw₁C⟩ := by
    rw [hw₁bar, hw₂bar, ← map_mul, ← map_mul, hd.comm]
  obtain ⟨o₁, ho₁, o₂, ho₂, hc⟩ := exists_conj_commuting z hw₁C hw₂C
    (isCentralInvolution_of_isClassicalMember hw₁).sq
    (isCentralInvolution_of_isClassicalMember hw₂).sq hcomm
  have ho₁C : o₁ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₁
  have ho₂C : o₂ ∈ Subgroup.centralizer ({z} : Set G) := oddCoreIn_le _ ho₂
  have htC : o₁ * w₁ * o₁⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₁C hw₁C) (inv_mem ho₁C)
  have hz'C : o₂ * w₂ * o₂⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    mul_mem (mul_mem ho₂C hw₂C) (inv_mem ho₂C)
  have hbar : ∀ (o w : G) (ho : o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)))
      (hoC : o ∈ Subgroup.centralizer ({z} : Set G)) (hwC : w ∈ Subgroup.centralizer ({z} : Set G))
      (hC : o * w * o⁻¹ ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨o * w * o⁻¹, hC⟩ = oddQuotMk z ⟨w, hwC⟩ := by
    intro o w ho hoC hwC hC
    have h1 : oddQuotMk z ⟨o, hoC⟩ = 1 := oddQuotMk_eq_one_of_mem_oddCoreIn ho hoC
    have : (⟨o * w * o⁻¹, hC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨o, hoC⟩ * ⟨w, hwC⟩ * ⟨o, hoC⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, h1]
    simp
  have himg : ∀ (o : G) (N : Subgroup G), o ∈ oddCoreIn (Subgroup.centralizer ({z} : Set G)) →
      o ∈ Subgroup.centralizer ({z} : Set G) →
      modOdd z (exactCore z (conjSub o N)) = modOdd z (exactCore z N) := by
    intro o N ho hoC
    have : exactCore z (conjSub o N) = conjSub o (exactCore z N) :=
      triangleResidual_conjSub N hoC
    rw [this]
    exact modOdd_conjSub_of_mem_oddCoreIn ho
  exact ⟨{
    R₁ := R₁
    R₂ := R₂
    τ₁ := τ₁
    τ₂ := τ₂
    ν₁ := ν₁
    ν₂ := ν₂
    hR₁ := hR₁
    hR₂ := hR₂
    hd := hd
    J := conjSub o₁ N₁
    K' := conjSub o₂ N₂
    t := o₁ * w₁ * o₁⁻¹
    z' := o₂ * w₂ * o₂⁻¹
    ht := htC
    hz' := hz'C
    hJ := conjSub_mem_tqMembers C.hΩ.conjInvariant ho₁C hN₁
    hK' := conjSub_mem_tqMembers C.hΩ.conjInvariant ho₂C hN₂
    hJt := hw₁.conj o₁
    hK'z' := hw₂.conj o₂
    hJimg := (himg o₁ N₁ ho₁ ho₁C).trans hN₁img
    hK'img := (himg o₂ N₂ ho₂ ho₂C).trans hN₂img
    htbar := (hbar o₁ w₁ ho₁ ho₁C hw₁C htC).trans hw₁bar
    hz'bar := (hbar o₂ w₂ ho₂ ho₂C hw₂C hz'C).trans hw₂bar
    htz' := hc }⟩

end Chain

end CFSG.ClassicalInvolution.Asc77

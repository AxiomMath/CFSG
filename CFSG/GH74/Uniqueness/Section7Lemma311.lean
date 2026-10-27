module

public import CFSG.GH74.Uniqueness.Lemma311
public import CFSG.GH74.Uniqueness.Section5Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

theorem exists_conj_of_involution_mem_sup {G : Type*} [Group G] {R : Subgroup G} {z t : G}
    (hz : z * z = 1) (hzN : z ∈ normalizer (R : Set G)) (hRodd : Odd (Nat.card R))
    (hinv : ∀ ρ ∈ R, z * ρ * z⁻¹ = ρ⁻¹) (ht : t ∈ R ⊔ zpowers z) (ht2 : orderOf t = 2) :
    ∃ σ ∈ R, σ⁻¹ * z * σ = t := by
  have hle : zpowers z ≤ normalizer (R : Set G) := (Subgroup.zpowers_le).mpr hzN
  have hmem : t ∈ ((R ⊔ zpowers z : Subgroup G) : Set G) := ht
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R (zpowers z) hle] at hmem
  obtain ⟨ρ, hρ, w, hw, rfl⟩ := Set.mem_mul.mp hmem
  have hw' : w = 1 ∨ w = z := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hz2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
    · left
      rw [zpow_mul, hz2, one_zpow]
    · right
      rw [zpow_add_one, zpow_mul, hz2, one_zpow, one_mul]
  rcases hw' with hw1 | hwz
  ·
    exfalso
    rw [hw1, mul_one] at ht2
    have hdvd : orderOf ρ ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hρ
    rw [ht2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hRodd) (even_iff_two_dvd.mpr hdvd)
  · rw [hwz]
    obtain ⟨m, hm⟩ := hRodd
    have hρ1 : ρ ^ (2 * m + 1) = 1 := by
      have := pow_card_eq_one' (G := R) (x := ⟨ρ, hρ⟩)
      rw [hm] at this
      exact congrArg Subtype.val this
    have hρsq : (ρ ^ (m + 1)) * (ρ ^ (m + 1)) = ρ := by
      calc (ρ ^ (m + 1)) * (ρ ^ (m + 1)) = ρ ^ (2 * m + 1) * ρ := by
            rw [← pow_add, ← pow_succ]; congr 1; ring
        _ = ρ := by rw [hρ1, one_mul]
    set σ : G := (ρ ^ (m + 1))⁻¹ with hσ
    have hσR : σ ∈ R := R.inv_mem (R.pow_mem hρ _)
    refine ⟨σ, hσR, ?_⟩
    have hzσ : z * σ = σ⁻¹ * z := by
      have := hinv σ hσR
      calc z * σ = (z * σ * z⁻¹) * z := by group
        _ = σ⁻¹ * z := by rw [this]
    calc σ⁻¹ * z * σ = σ⁻¹ * (z * σ) := by rw [mul_assoc]
      _ = σ⁻¹ * (σ⁻¹ * z) := by rw [hzσ]
      _ = (σ⁻¹ * σ⁻¹) * z := by rw [mul_assoc]
      _ = ρ * z := by rw [hσ, inv_inv, hρsq]

theorem IsZStarIn.isZStar_subtype {X : Type} [Group X] [Finite X] {A : Subgroup X} {z : X}
    (h : IsZStarIn A z) : IsZStar ↥A ⟨z, h.1⟩ := by
  obtain ⟨hzA, N, hNA, hNn, hNodd, hN⟩ := h
  have hnorm : A ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNn
  have hle : N ≤ pPrimeCoreIn A := le_pPrimeCoreIn hNA hnorm hNodd
  intro g
  obtain ⟨k, hk, hkg⟩ := hle (hN g g.2)
  have hkeq : k = g * ⟨z, hzA⟩ * g⁻¹ * ⟨z, hzA⟩⁻¹ := Subtype.ext hkg
  rwa [← hkeq]

@[expose] def omegaOrbit {X : Type} [Group X] (M R : Subgroup X) : Set (Subgroup X) :=
  {β | ∃ ρ ∈ R, conjugate M ρ = β}

theorem self_mem_omegaOrbit {X : Type} [Group X] (M R : Subgroup X) : M ∈ omegaOrbit M R :=
  ⟨1, R.one_mem, conjugate_one M⟩

theorem omegaOrbit_subset_omega {X : Type} [Group X] (M R : Subgroup X) :
    omegaOrbit M R ⊆ omega M :=
  fun _ ⟨ρ, _, hρ⟩ => ⟨ρ, hρ⟩

theorem conjugate_mem_omegaOrbit {X : Type} [Group X] {M R : Subgroup X} {β : Subgroup X}
    (hβ : β ∈ omegaOrbit M R) {σ : X} (hσ : σ ∈ R) : conjugate β σ ∈ omegaOrbit M R := by
  obtain ⟨ρ, hρ, rfl⟩ := hβ
  exact ⟨ρ * σ, R.mul_mem hρ hσ, (conjugate_conjugate M ρ σ).symm⟩

theorem exists_conjugate_eq_of_mem_omegaOrbit {X : Type} [Group X] {M R : Subgroup X}
    {β : Subgroup X} (hβ : β ∈ omegaOrbit M R) : ∃ σ ∈ R, conjugate β σ = M := by
  obtain ⟨ρ, hρ, rfl⟩ := hβ
  exact ⟨ρ⁻¹, R.inv_mem hρ, by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]⟩

theorem lemma311_omega_of_map {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) {Hs : Subgroup X} {z : X}
    (hz2 : orderOf z = 2) (hzH : z ∈ Hs) (hZS : IsZStarIn Hs z) (hHM : ¬ Hs ≤ M)
    (hcent : ∀ c ∈ Hs, c * z = z * c → c ∈ M)
    {Ψ : Type} [MulAction ↥Hs Ψ] [MulAction.IsPretransitive ↥Hs Ψ]
    (Φ : Ψ → Subgroup X) (hΦinj : Function.Injective Φ) (hΦmem : ∀ ψ, Φ ψ ∈ omega M)
    (hΦsmul : ∀ (g : ↥Hs) (ψ : Ψ), Φ (g • ψ) = conjugate (Φ ψ) (g : X)⁻¹)
    (a : Ψ) (ha : Φ a = M) :
    ∃ R : Subgroup X, R ≤ Hs ∧
      1 < (omegaOrbit M R).ncard ∧
      (∀ β ∈ omegaOrbit M R, conjugate β z ∈ omegaOrbit M R) ∧
      (∀ β ∈ omegaOrbit M R, ∀ γ ∈ omegaOrbit M R, β ≠ γ → ∀ x ∈ Hs, x ∈ β → x ∈ γ →
        ∀ δ ∈ omegaOrbit M R, x ∈ δ) ∧
      (∀ β ∈ omegaOrbit M R, β ≠ M → ∃ σ ∈ R, conjugate M (σ⁻¹ * z * σ) = β) := by
  have hzz : z * z = 1 := mul_self_of_orderOf_eq_two hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzH2 : orderOf (⟨z, hzH⟩ : ↥Hs) = 2 := by
    rw [← hz2]
    exact Subgroup.orderOf_mk z hzH
  have hZ' : IsZStar ↥Hs (⟨z, hzH⟩ : ↥Hs) := hZS.isZStar_subtype
  have hfix_iff : ∀ (g : ↥Hs) (ψ : Ψ), g • ψ = ψ ↔ (g : X) ∈ Φ ψ := by
    intro g ψ
    rw [← hΦinj.eq_iff, hΦsmul, h.conjugate_eq_iff_mem (hΦmem ψ)]
    exact inv_mem_iff
  have hstab : MulAction.stabilizer ↥Hs a = M.comap Hs.subtype := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hfix_iff, ha]
    exact Iff.rfl
  have hYtop : M.comap Hs.subtype ≠ ⊤ := by
    intro htop
    apply hHM
    intro x hx
    have : (⟨x, hx⟩ : ↥Hs) ∈ M.comap Hs.subtype := htop ▸ Subgroup.mem_top _
    exact this
  have hcentY : centralizer ({(⟨z, hzH⟩ : ↥Hs)} : Set ↥Hs) ≤ M.comap Hs.subtype := by
    intro c hc
    have hc' : c * (⟨z, hzH⟩ : ↥Hs) = (⟨z, hzH⟩ : ↥Hs) * c :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    exact hcent c c.2 (congrArg Subtype.val hc')
  obtain ⟨R, r, hr, hrodd, hRp, hcard, hzR, hzΓ, ⟨-, hinvR⟩, hswap, hpt⟩ :=
    lemma311 (H := ↥Hs) (Ψ := Ψ) hzH2 hZ' (M.comap Hs.subtype) a hstab hYtop hcentY
  have hRodd : Odd (Nat.card R) := by
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hRp
    rw [hn]
    exact hrodd.pow
  have horb : omegaOrbit M (R.map Hs.subtype) = Φ '' (MulAction.orbit R a) := by
    ext β
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      obtain ⟨ρ₀, hρ₀, rfl⟩ := Subgroup.mem_map.mp hρ
      refine ⟨(⟨ρ₀⁻¹, R.inv_mem hρ₀⟩ : ↥R) • a, MulAction.mem_orbit _ _, ?_⟩
      have := hΦsmul (ρ₀⁻¹) a
      rw [ha] at this
      rw [show (⟨ρ₀⁻¹, R.inv_mem hρ₀⟩ : ↥R) • a = ρ₀⁻¹ • a from rfl, this]
      simp
    · rintro ⟨ψ, hψ, rfl⟩
      obtain ⟨ρ, rfl⟩ := MulAction.mem_orbit_iff.mp hψ
      refine ⟨((ρ : ↥Hs) : X)⁻¹, ⟨(ρ : ↥Hs)⁻¹, R.inv_mem ρ.2, rfl⟩, ?_⟩
      have := hΦsmul (ρ : ↥Hs) a
      rw [ha] at this
      rw [show (ρ : ↥R) • a = (ρ : ↥Hs) • a from rfl, this]
  refine ⟨R.map Hs.subtype, Subgroup.map_subtype_le R, ?_, ?_, ?_, ?_⟩
  ·
    rw [horb, Set.ncard_image_of_injective _ hΦinj, ← Nat.card_coe_set_eq, hcard]
    exact hr.one_lt
  ·
    intro β hβ
    rw [horb] at hβ ⊢
    obtain ⟨ψ, hψ, rfl⟩ := hβ
    refine ⟨(⟨z, hzH⟩ : ↥Hs) • ψ, hzΓ ψ hψ, ?_⟩
    rw [hΦsmul]
    show conjugate (Φ ψ) z⁻¹ = conjugate (Φ ψ) z
    rw [hzi]
  ·
    intro β hβ γ hγ hβγ x hxH hxβ hxγ δ hδ
    rw [horb] at hβ hγ hδ
    obtain ⟨ψβ, hψβ, rfl⟩ := hβ
    obtain ⟨ψγ, hψγ, rfl⟩ := hγ
    obtain ⟨ψδ, hψδ, rfl⟩ := hδ
    have hne : ψβ ≠ ψγ := fun e => hβγ (congrArg Φ e)
    have := hpt ψβ hψβ ψγ hψγ hne ⟨x, hxH⟩ ((hfix_iff _ _).mpr hxβ) ((hfix_iff _ _).mpr hxγ)
      ψδ hψδ
    exact (hfix_iff ⟨x, hxH⟩ ψδ).mp this
  ·
    intro β hβ hβM
    rw [horb] at hβ
    obtain ⟨ψ, hψ, rfl⟩ := hβ
    have hψa : ψ ≠ a := by
      rintro rfl
      exact hβM ha
    obtain ⟨τ, hτ, hτ2, hτa, -⟩ := hswap a (MulAction.mem_orbit_self a) ψ hψ (Ne.symm hψa)
    obtain ⟨σ, hσ, hστ⟩ := exists_conj_of_involution_mem_sup (G := ↥Hs) (R := R)
      (z := (⟨z, hzH⟩ : ↥Hs)) (t := τ) (mul_self_of_orderOf_eq_two hzH2) hzR hRodd hinvR hτ hτ2
    refine ⟨(σ : X), ⟨σ, hσ, rfl⟩, ?_⟩
    have e1 : (σ : X)⁻¹ * z * σ = (τ : X) := congrArg Subtype.val hστ
    have hτinv : (τ : X)⁻¹ = (τ : X) :=
      congrArg Subtype.val (inv_eq_of_mul_eq_one_right (mul_self_of_orderOf_eq_two hτ2))
    have := hΦsmul τ a
    rw [ha, hτa, hτinv] at this
    rw [e1, this]

theorem lemma311_omega {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) {Hs : Subgroup X} {z : X}
    (hz2 : orderOf z = 2) (hzH : z ∈ Hs) (hZS : IsZStarIn Hs z) (hHM : ¬ Hs ≤ M)
    (hcent : ∀ c ∈ Hs, c * z = z * c → c ∈ M) :
    ∃ R : Subgroup X, R ≤ Hs ∧
      1 < (omegaOrbit M R).ncard ∧
      (∀ β ∈ omegaOrbit M R, conjugate β z ∈ omegaOrbit M R) ∧
      (∀ β ∈ omegaOrbit M R, ∀ γ ∈ omegaOrbit M R, β ≠ γ → ∀ x ∈ Hs, x ∈ β → x ∈ γ →
        ∀ δ ∈ omegaOrbit M R, x ∈ δ) ∧
      (∀ β ∈ omegaOrbit M R, β ≠ M → ∃ σ ∈ R, conjugate M (σ⁻¹ * z * σ) = β) := by
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : omega M, (α₀ : Subgroup X) = M := ⟨⟨M, self_mem_omega M⟩, rfl⟩
  exact lemma311_omega_of_map h hz2 hzH hZS hHM hcent
    (Ψ := ↥(MulAction.orbit ↥Hs α₀)) (fun ψ => ((ψ : omega M) : Subgroup X))
    (fun ψ₁ ψ₂ e => Subtype.ext (Subtype.ext e)) (fun ψ => (ψ : omega M).2) (fun g ψ => rfl)
    ⟨α₀, MulAction.mem_orbit_self α₀⟩ hα₀

end CFSG.GH74.Uniqueness

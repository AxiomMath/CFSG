module

public import CFSG.LargeExtraspecial.S12InspPSLCaseH3
public import CFSG.LargeExtraspecial.S12InspPSLCaseG

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

theorem finrank_H_lt : finrank (ZMod 2) P.H < S.width := by
  obtain ⟨e, he, he1⟩ := P.exists_polar_c'
  have hlt : P.H < P.W := by
    refine lt_of_le_of_ne P.H_le fun h => ?_
    have : e ∈ P.H := h ▸ he
    have h2 : polar S.q P.c' e = 0 := this.2
    rw [polar_comm, he1] at h2
    exact one_ne_zero h2
  have := Submodule.finrank_lt_finrank_of_lt hlt
  rwa [P.dim] at this

theorem width_le_finrank_H : S.width ≤ finrank (ZMod 2) P.H + 1 := by
  have := psl_finrank_le_finrank_inf_ker_add_one P.W (S.q.polarBilin P.c')
  rwa [P.dim] at this

theorem card_inf_le (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 3 ≤ S.width) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (htX : t ∈ S.Xbar12 g)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') :
    Nat.card ↥(S.Xbar12 g ⊓ S.Lbar g) ≤ 2 ^ (S.width - 1) := by
  obtain ⟨e, he, he1⟩ := P.exists_polar_c'
  have hmem : ∀ ℓ : ↥(S.Xbar12 g ⊓ S.Lbar g),
      ((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e ∈ P.H := by
    intro ℓ
    have hℓc' := (fix_of_mem_Lbar haQ ha ℓ.2.2 ℓ.2.1).2
    refine ⟨P.W.sub_mem (P.apply_mem ℓ.2.1 he) he, ?_⟩
    change polar S.q P.c' (((ℓ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e) = 0
    rw [polar_sub_right, ← hℓc', psl_polar_apply_apply, hℓc', sub_self]
  let F : ↥(S.Xbar12 g ⊓ S.Lbar g) → P.H := fun ℓ => ⟨_, hmem ℓ⟩
  have hF : Function.Injective F := by
    intro ℓ₁ ℓ₂ h12
    have h12' : ((ℓ₁ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e = ((ℓ₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) e :=
      sub_left_injective (congrArg Subtype.val h12)
    set ℓ : S.O := (ℓ₁ : S.O)⁻¹ * ℓ₂
    have hℓ : ℓ ∈ S.Xbar12 g ⊓ S.Lbar g :=
      (S.Xbar12 g ⊓ S.Lbar g).mul_mem ((S.Xbar12 g ⊓ S.Lbar g).inv_mem ℓ₁.2) ℓ₂.2
    have hℓe : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e = e := by
      rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h12', psl_inv_apply_apply]
    have hH := P.comm_H_le haQ hne hn ha hℓ.2 hℓ.1
    rcases P.eq_one_or_eq_of_comm_le haQ hne htA htX ha hℓ.2 hℓ.1 (fun w hw => by
        have h1 := hH _ (P.sub_mem_H he he1 hw)
        have e1 : (ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w =
            ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) (w - polar S.q w P.c' • e) - (w - polar S.q w P.c' • e)) +
              polar S.q w P.c' • ((ℓ : S.Qt ≃ₗ[ZMod 2] S.Qt) e - e) := by
          rw [map_sub, map_smul, smul_sub]
          abel
        rw [e1, hℓe, sub_self, smul_zero, add_zero]
        exact h1) with h | h
    · apply Subtype.ext
      calc (ℓ₁ : S.O) = ℓ₁ * ℓ := by rw [h, mul_one]
        _ = ℓ₂ := by rw [mul_inv_cancel_left]
    · exfalso
      rw [h, P.tW e he, he1, one_smul, add_eq_left] at hℓe
      exact P.c_ne hℓe
  calc Nat.card ↥(S.Xbar12 g ⊓ S.Lbar g) ≤ Nat.card P.H := Nat.card_le_card_of_injective F hF
    _ = 2 ^ finrank (ZMod 2) P.H := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    _ ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by have := P.finrank_H_lt; omega)

theorem card_Lbar_le_of_eq_add (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 4 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') : Nat.card (S.Lbar g) ≤ 2 ^ (S.width - 1) := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hinf := P.card_inf_le haQ hne (by omega) htA htX ha
  by_cases hLX : S.Lbar g ≤ S.Xbar12 g
  · rwa [inf_eq_right.mpr hLX] at hinf
  obtain ⟨ℓ₀, hℓ₀, hℓ₀X⟩ : ∃ ℓ₀ ∈ S.Lbar g, ℓ₀ ∉ S.Xbar12 g := by
    by_contra h
    push Not at h
    exact hLX h
  have hcard := psl_card_Lbar_le_two_mul (P.relIndex_le_two hS (by omega))
  have hge := S.card_Lbar_ge haQ hne
  have h8 : 2 ^ 3 ≤ 2 ^ (S.width - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ℓ₁, ⟨hℓ₁X, hℓ₁⟩, hℓ₁1, hℓ₁t⟩ : ∃ ℓ ∈ S.Xbar12 g ⊓ S.Lbar g, ℓ ≠ 1 ∧ ℓ ≠ t := by
    by_contra hcon
    push Not at hcon
    have := psl_card_le_two_of_subset (K := S.Xbar12 g ⊓ S.Lbar g) (t := t) fun x hx => by
      by_cases h1 : x = 1
      · exact Or.inl h1
      · exact Or.inr (hcon x hx h1)
    omega
  obtain ⟨e, he, he1⟩ := P.exists_polar_c'
  obtain ⟨⟨h₁, hh₁, hℓh₁⟩, -⟩ :=
    P.exists_mixed haQ hne (by omega) htA htX ha hℓ₁ hℓ₁X hℓ₁1 hℓ₁t he he1
  have hperp : ∀ h ∈ P.H, polar S.q (S.cl (g * S.z * g⁻¹)) h = 0 := fun h hh => by
    rw [P.polar_a_eq ha hh.1]
    exact hh.2
  set D := S.clSub (S.QG ⊓ S.Qa g)
  have hcD : P.c ∈ D := by
    have := S.s12_Lbar_apply_sub_mem haQ hℓ₁ (hperp h₁ hh₁)
    rwa [hℓh₁, add_sub_cancel_left] at this
  have hℓ₀M := S.Lbar_le_Mbar g hℓ₀
  have hfix0 : ∀ h ∈ P.W, (ℓ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) h ∈ P.W → h = 0 := fun h hh hℓh => by
    by_contra h0
    exact hℓ₀X (P.mem_Xbar12_of_apply_mem hS (by omega) hred hℓ₀M hh h0 hℓh)
  set φ : P.H →ₗ[ZMod 2] S.Qt :=
    (((ℓ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id) ∘ₗ P.H.subtype
  have hφ : ∀ h : P.H, φ h = (ℓ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) h - h := fun h => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro h hh
    rw [LinearMap.mem_ker, hφ, sub_eq_zero] at hh
    rw [Submodule.mem_bot]
    exact Subtype.ext (hfix0 _ h.2.1 (by rw [hh]; exact h.2.1))
  have hφD : LinearMap.range φ ≤ D := by
    rintro _ ⟨h, rfl⟩
    rw [hφ]
    exact S.s12_Lbar_apply_sub_mem haQ hℓ₀ (hperp h h.2)
  have hdisj : span (ZMod 2) {P.c} ⊓ LinearMap.range φ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hv, ⟨h, rfl⟩⟩
    rw [Submodule.mem_bot]
    have hvW : φ h ∈ P.W := by
      replace hv : φ h ∈ span (ZMod 2) {P.c} := hv
      rw [mem_span_singleton_iff] at hv
      rcases hv with hv | hv <;> rw [hv]
      · exact zero_mem _
      · exact P.hc
    have h0 : (h : S.Qt) = 0 := by
      refine hfix0 _ h.2.1 ?_
      have : (ℓ₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) h = φ h + h := by rw [hφ, sub_add_cancel]
      rw [this]
      exact P.W.add_mem hvW h.2.1
    rw [hφ, h0, map_zero, sub_zero]
  have hfin := finrank_sup_add_finrank_inf_eq (span (ZMod 2) {P.c}) (LinearMap.range φ)
  rw [hdisj, finrank_bot, add_zero, finrank_span_singleton P.c_ne,
    LinearMap.finrank_range_of_inj hφinj] at hfin
  have hle : span (ZMod 2) {P.c} ⊔ LinearMap.range φ ≤ D :=
    sup_le (span_le.mpr (Set.singleton_subset_iff.mpr hcD)) hφD
  have hD := finrank_mono hle
  have hH := P.width_le_finrank_H
  have hDcard : 2 ^ S.width ≤ Nat.card D := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hF1 : Nat.card (S.Lbar g) * (2 * Nat.card D) = 2 ^ (2 * S.width) :=
    psl_card_Lbar_mul_card_clSub haQ hne
  have h2n : 2 ^ (2 * S.width) = 2 ^ (S.width - 1) * (2 * 2 ^ S.width) := by
    rw [← pow_succ', ← pow_add]
    congr 1
    omega
  rw [h2n] at hF1
  by_contra hlt
  push Not at hlt
  have : 2 ^ (S.width - 1) * (2 * 2 ^ S.width) <
      Nat.card (S.Lbar g) * (2 * Nat.card D) :=
    Nat.mul_lt_mul_of_lt_of_le hlt (Nat.mul_le_mul_left 2 hDcard)
      (by have : 0 < 2 ^ S.width := by positivity
          omega)
  rw [hF1] at this
  exact lt_irrefl _ this

theorem case1_of_eq_add (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hn : 4 ≤ S.width) (ht : t ∈ S.Lbar g) (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2)
    (hS : S.S12Standing g t) (hred : ¬ S.IsReducible12)
    (ha : S.cl (g * S.z * g⁻¹) = P.c + P.c') : S.S12Case1 g t := by
  by_cases hn5 : 5 ≤ S.width
  · exact (P.false_of_eq_add haQ hne hn5 ht htA hS ha).elim
  have hn4 : S.width = 4 := by omega
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hle := P.card_Lbar_le_of_eq_add haQ hne hn ht htA hS hred ha
  have hge := S.card_Lbar_ge haQ hne
  rw [hn4] at hle hge
  refine ⟨P.normal haQ hne (by omega) ht htA, P.relIndex_le_two hS (by omega),
    ⟨S.width, by omega, P.model, Or.inr ⟨hn4, le_antisymm hle hge, fun d hd hdL => ?_⟩⟩⟩
  obtain ⟨x, hx, rfl⟩ := hS.cls d hd
  obtain ⟨hxc, hxc'⟩ := P.conj_fix_of_mem_Lbar haQ hne htA ha hx hdL
  exact P.conj_eq_of_fix htX hx hxc hxc'

end PSLPair

end Setting

end CFSG.LargeExtraspecial

module

public import CFSG.LargeExtraspecial.S111SJBenB
public import CFSG.Timmesfeld.Bridge.RootSetsConn7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup CFSG.Open CFSG.ComponentClassification CFSG.GH74.Uniqueness.Bender

namespace LayerCfg

variable {X : Type} [Group X] {E O L : Subgroup X} {w : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : X →* (V ≃ₗ[ZMod 2] V)} {a : V}

theorem isPGroup_of_sq {Q : Type*} [Group Q] {A : Subgroup Q} (hA : ∀ q ∈ A, q * q = 1) :
    IsPGroup 2 A := fun q => ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact hA q q.2)⟩

theorem false_of_inner_of_O_eq_bot [Finite X] [E.Normal] (C : LayerCfg E O L w ρ a) {f : ℕ}
    (hB : BenderType (E ⧸ center E) f 1 1)
    (hinner : ∀ l ∈ L.map (barAct E), ∃ q, l = MulAut.conj q) (hO : O = ⊥) : False := by
  have hperf := C.perfect
  have hconj := conj_injective_of_center C.center_eq_bot
  obtain ⟨t, htL, ht1, x₀, htx, hne⟩ := C.not_TI
  obtain ⟨eB⟩ : Nonempty (E ⧸ center E ≃* CFSG.Theory.Comparator.PSL2Model f) := by
    cases hB with
    | linear n hn e => exact ⟨e⟩
  have hf2 : 2 ≤ f := hB.two_le.2
  have hBG : CFSG.BenderSuzuki.IsBenderGroup (E ⧸ center E) := .isPSL2 f hf2 eB
  have : Finite (E ⧸ center E) := inferInstance
  obtain ⟨a₀, ha₀⟩ := hinner (barAct E t) ⟨t, htL, rfl⟩
  have ha₀1 : a₀ ≠ 1 := by
    intro h
    apply ht1
    apply C.eq_one_of_barAct htL
    rw [ha₀, h, map_one]
  set Lx := L.map (MulAut.conj x₀).toMonoidHom with hLx
  have hLx2 : ∀ y ∈ Lx, y * y = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, C.L_sq y hy, map_one]
  set A : Subgroup (E ⧸ center E) := (L.map (barAct E)).comap MulAut.conj with hA
  set A' : Subgroup (E ⧸ center E) := (Lx.map (barAct E)).comap MulAut.conj with hA'
  have hA2 : ∀ q ∈ A, q * q = 1 := fun q hq => hconj (by
    rw [map_mul, map_one]; exact C.lam_sq hq)
  have hA'2 : ∀ q ∈ A', q * q = 1 := by
    intro q hq
    apply hconj
    rw [map_mul, map_one]
    obtain ⟨y, hy, hyq⟩ := hq
    rw [← hyq, ← map_mul, hLx2 y hy, map_one]
  have ha₀A : a₀ ∈ A := by
    show MulAut.conj a₀ ∈ L.map (barAct E)
    rw [← ha₀]
    exact ⟨t, htL, rfl⟩
  have ha₀A' : a₀ ∈ A' := by
    show MulAut.conj a₀ ∈ Lx.map (barAct E)
    rw [← ha₀]
    exact ⟨t, htx, rfl⟩
  obtain ⟨T, hAT⟩ := (isPGroup_of_sq hA2).exists_le_sylow
  have ha₀T : a₀ ∈ (T : Subgroup (E ⧸ center E)) := hAT ha₀A
  have hA'T : A' ≤ T := CFSG.Timmesfeld.Bridge.bender_le_sylow hBG T ha₀T ha₀1
    (isPGroup_of_sq hA'2) ha₀A'
  have hTc := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_psl2 hf2 eB T
  have hFE : (O ⊔ E : Subgroup X) = E := by rw [hO, bot_sup_eq]
  have hCE : centralizer (E : Set X) ≤ E := by
    have := C.fstar_cent
    rwa [hFE] at this
  have hLE : ∀ ℓ ∈ L, ℓ ∈ E := by
    intro ℓ hℓ
    obtain ⟨b, hb⟩ := hinner (barAct E ℓ) ⟨ℓ, hℓ, rfl⟩
    obtain ⟨e, -, he⟩ := C.exists_mul_of_barAct_eq_conj hb
    have h1 : (e : X)⁻¹ * ℓ ∈ E := hCE (mem_centralizer_iff.mpr fun e' he' => (he e' he').symm)
    have : ℓ = e * ((e : X)⁻¹ * ℓ) := by group
    rw [this]
    exact E.mul_mem e.2 h1
  have hcomm : ∀ ℓ ∈ L, ∀ ℓ' ∈ Lx, ℓ * ℓ' = ℓ' * ℓ := by
    intro ℓ hℓ ℓ' hℓ'
    obtain ⟨b, hb⟩ := hinner (barAct E ℓ) ⟨ℓ, hℓ, rfl⟩
    obtain ⟨ℓ'', hℓ'', rfl⟩ := hℓ'
    obtain ⟨b'', hb''⟩ := hinner (barAct E ℓ'') ⟨ℓ'', hℓ'', rfl⟩
    set b' := barAct E x₀ b'' with hb'
    have hφℓ' : barAct E ((MulAut.conj x₀).toMonoidHom ℓ'') = MulAut.conj b' := by
      change barAct E (x₀ * ℓ'' * x₀⁻¹) = _
      rw [map_mul, map_mul, map_inv, hb'', mul_conj_mul_inv]
    have hbA : b ∈ A := by
      show MulAut.conj b ∈ L.map (barAct E)
      rw [← hb]
      exact ⟨ℓ, hℓ, rfl⟩
    have hb'A' : b' ∈ A' := by
      show MulAut.conj b' ∈ Lx.map (barAct E)
      rw [← hφℓ']
      exact ⟨_, ⟨ℓ'', hℓ'', rfl⟩, rfl⟩
    have hbb' : b * b' = b' * b := (hTc b (hAT hbA) b' (hA'T hb'A')).eq
    set ℓ' := (MulAut.conj x₀).toMonoidHom ℓ'' with hℓ'def
    have hℓ'2 : ℓ' * ℓ' = 1 := hLx2 ℓ' ⟨ℓ'', hℓ'', rfl⟩
    have hℓ2 := C.L_sq ℓ hℓ
    set c := ℓ * ℓ' * ℓ⁻¹ * ℓ'⁻¹ with hc
    have hc1 : barAct E c = 1 := by
      calc barAct E c = MulAut.conj b * MulAut.conj b' * (MulAut.conj b)⁻¹ *
            (MulAut.conj b')⁻¹ := by
            rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv, hb, hφℓ']
        _ = MulAut.conj (b * b' * b⁻¹ * b'⁻¹) := by simp only [map_mul, map_inv]
        _ = MulAut.conj 1 := by
            congr 1
            rw [hbb']
            group
        _ = 1 := map_one _
    have hcE : ∀ e ∈ E, e * c = c * e := fun e he => (commute_of_barAct_eq_one hc1 e he).symm
    have hcℓ : ℓ * c = c * ℓ := hcE ℓ (hLE ℓ hℓ)
    have hli : ℓ⁻¹ = ℓ := inv_eq_of_mul_eq_one_right hℓ2
    have hl'i : ℓ'⁻¹ = ℓ' := inv_eq_of_mul_eq_one_right hℓ'2
    have hcc : c * c = 1 := by
      have h1 : ℓ * c * ℓ⁻¹ = c⁻¹ := by
        rw [hc, hli, hl'i]
        calc ℓ * (ℓ * ℓ' * ℓ * ℓ') * ℓ = (ℓ * ℓ) * ℓ' * ℓ * ℓ' * ℓ := by group
          _ = ℓ' * ℓ * ℓ' * ℓ := by rw [hℓ2, one_mul]
          _ = (ℓ * ℓ' * ℓ * ℓ')⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, hli, hl'i]
              group
      rw [hcℓ, mul_inv_cancel_right] at h1
      calc c * c = c * c⁻¹ := by rw [← h1]
        _ = 1 := mul_inv_cancel c
    have hc1' : c = 1 := C.fstar_inv c hcc (by
      rw [hFE]; exact mem_centralizer_iff.mpr fun e he => hcE e he)
    rw [hc] at hc1'
    calc ℓ * ℓ' = ℓ * ℓ' * ℓ⁻¹ * ℓ'⁻¹ * (ℓ' * ℓ) := by group
      _ = ℓ' * ℓ := by rw [hc1', one_mul]
  apply hne
  apply C.weakly
  intro ℓ' hℓ'
  rw [mem_normalizer_iff]
  intro h
  have hh : ℓ' * h * ℓ'⁻¹ = h → (h ∈ L ↔ ℓ' * h * ℓ'⁻¹ ∈ L) := fun e => by rw [e]
  by_cases hhL : h ∈ L
  · exact hh (by rw [← hcomm h hhL ℓ' hℓ', mul_inv_cancel_right])
  · refine ⟨fun h' => absurd h' hhL, fun h' => ?_⟩
    have hk := hcomm _ h' ℓ' hℓ'
    have h2 : h = ℓ' * h * ℓ'⁻¹ := by
      calc h = ℓ'⁻¹ * ((ℓ' * h * ℓ'⁻¹) * ℓ') := by group
        _ = ℓ'⁻¹ * (ℓ' * (ℓ' * h * ℓ'⁻¹)) := by rw [hk]
        _ = ℓ' * h * ℓ'⁻¹ := by group
    rw [h2]
    exact h'

end LayerCfg

end CFSG.LargeExtraspecial.S11

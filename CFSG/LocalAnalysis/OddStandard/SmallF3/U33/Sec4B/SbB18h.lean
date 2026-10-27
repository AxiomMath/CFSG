module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbD18a
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutCoprime
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18c

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma card_mul_card_le_of_le_card_mul_card_inf {G : Type*} [Group G] [Finite G]
    {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    Nat.card A * Nat.card B ≤ Nat.card C * Nat.card ↥(A ⊓ B) := by
  let H : Subgroup C := A.subgroupOf C
  let K : Subgroup C := B.subgroupOf C
  have hH : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  have hK : Nat.card K = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have hinf : H ⊓ K = (A ⊓ B).subgroupOf C := by
    show (A.subgroupOf C) ⊓ (B.subgroupOf C) = (A ⊓ B).subgroupOf C
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hHK : Nat.card ↥(H ⊓ K) = Nat.card ↥(A ⊓ B) := by
    rw [hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA)).toEquiv
  have h1 : H.index * Nat.card H = Nat.card C := Subgroup.index_mul_card H
  have h2 : K.index * Nat.card K = Nat.card C := Subgroup.index_mul_card K
  have h3 : (H ⊓ K).index * Nat.card ↥(H ⊓ K) = Nat.card C :=
    Subgroup.index_mul_card (H ⊓ K)
  have hle : (H ⊓ K).index ≤ H.index * K.index := Subgroup.index_inf_le
  have hmul : (H ⊓ K).index * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K))
      ≤ (H.index * K.index) * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K)) :=
    Nat.mul_le_mul_right _ hle
  have e1 : (H ⊓ K).index * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K))
      = Nat.card C * (Nat.card H * Nat.card K) := by
    calc (H ⊓ K).index * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K))
        = ((H ⊓ K).index * Nat.card ↥(H ⊓ K)) * (Nat.card H * Nat.card K) := by ring
      _ = Nat.card C * (Nat.card H * Nat.card K) := by rw [h3]
  have e2 : (H.index * K.index) * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K))
      = Nat.card C * (Nat.card C * Nat.card ↥(H ⊓ K)) := by
    calc (H.index * K.index) * (Nat.card H * Nat.card K * Nat.card ↥(H ⊓ K))
        = (H.index * Nat.card H) * (K.index * Nat.card K) * Nat.card ↥(H ⊓ K) := by ring
      _ = Nat.card C * (Nat.card C * Nat.card ↥(H ⊓ K)) := by rw [h1, h2]; ring
  rw [e1, e2] at hmul
  haveI : Nonempty C := ⟨1, C.one_mem⟩
  have hpos : 0 < Nat.card C := Nat.card_pos
  have hmain : Nat.card H * Nat.card K ≤ Nat.card C * Nat.card ↥(H ⊓ K) :=
    Nat.le_of_mul_le_mul_left hmul hpos
  rwa [hH, hK, hHK] at hmain

theorem l18_D_rho (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {x : G}
    (hx : x ∈ ctxXi t tau x₁ x₂ rho) (h : rho * x * rho⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho) :
    x ∈ ctxYq t tau x₁ x₂ rho := by
  have hρK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.2
  have hYnorm := l17_K_normalizes_Y hc.toCtx13
  have hYc : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ z ∈ ctxXi t tau x₁ x₂ rho, z * y = y * z := by
    intro y hy z hz
    have hzC : z ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hz
    exact ((Subgroup.mem_centralizer_iff.mp hzC.2) y hy).symm
  have hρ3 : (MulAut.conj rho) ^ 3 = 1 := by
    rw [← map_pow, show rho ^ 3 = 1 from by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho]
    simp
  have hA : ∀ a ∈ ctxYq t tau x₁ x₂ rho, MulAut.conj rho a ∈ ctxYq t tau x₁ x₂ rho := by
    intro a ha
    rw [MulAut.conj_apply]
    exact hYnorm rho hρK a ha
  have hcard : ¬ 3 ∣ Nat.card (ctxYq t tau x₁ x₂ rho) := by
    rw [l17_card_Y hc.toCtx13]
    norm_num
  have ht : x⁻¹ * MulAut.conj rho x ∈ ctxYq t tau x₁ x₂ rho := by
    rw [MulAut.conj_apply]
    have hxch : x * (rho * x * rho⁻¹ * x⁻¹) = (rho * x * rho⁻¹ * x⁻¹) * x := hYc _ h x hx
    have e : x⁻¹ * (rho * x * rho⁻¹) = rho * x * rho⁻¹ * x⁻¹ := by
      calc x⁻¹ * (rho * x * rho⁻¹)
          = x⁻¹ * ((rho * x * rho⁻¹ * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (rho * x * rho⁻¹ * x⁻¹)) := by rw [← hxch]
        _ = rho * x * rho⁻¹ * x⁻¹ := by group
    rw [e]
    exact h
  obtain ⟨s, hs, hfix⟩ :=
    Outside.exists_fixed_in_coset_of_not_dvd (MulAut.conj rho) hρ3
      (ctxYq t tau x₁ x₂ rho) hA hcard x ht
  have hfix' : rho * s * rho⁻¹ = s := by
    have := hfix
    rwa [MulAut.conj_apply] at this
  have hscent : s ∈ centralizer ({rho} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : rho * s = s * rho := by
      calc rho * s = (rho * s * rho⁻¹) * rho := by group
        _ = s * rho := by rw [hfix']
    exact h2.symm
  have hYleΞ : ctxYq t tau x₁ x₂ rho ≤ ctxXi t tau x₁ x₂ rho :=
    ctxYq_le_ctxQ.trans (l18_Q_le_Xi hc.toCtx13)
  have hsXi : s ∈ ctxXi t tau x₁ x₂ rho := by
    have hm : x * (x⁻¹ * s) ∈ ctxXi t tau x₁ x₂ rho :=
      (ctxXi t tau x₁ x₂ rho).mul_mem hx (hYleΞ hs)
    rwa [mul_inv_cancel_left] at hm
  have hsbot : s ∈ (⊥ : Subgroup G) := by
    have hinf : s ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({rho} : Set G) := ⟨hsXi, hscent⟩
    rwa [l18_Xi_cap_cent_rho hc] at hinf
  have hs1 : s = 1 := Subgroup.mem_bot.mp hsbot
  have hxinv : x⁻¹ ∈ ctxYq t tau x₁ x₂ rho := by
    have := hs
    rwa [hs1, mul_one] at this
  simpa using (ctxYq t tau x₁ x₂ rho).inv_mem hxinv

theorem l18_exists_D_lam (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ∃ D : Subgroup G, D ≤ ctxXi t tau x₁ x₂ rho ∧
      (∀ x ∈ ctxXi t tau x₁ x₂ rho, lam * x * lam⁻¹ * x⁻¹ ∈ ctxYq t tau x₁ x₂ rho → x ∈ D) ∧
      Nat.card D ≤ 64 := by
  obtain ⟨_htK, _htauK, _homK, hlamK, hρK⟩ := l17_mem_K hc.toCtx13
  have hYnorm := l17_K_normalizes_Y hc.toCtx13
  have hYc : ∀ y ∈ ctxYq t tau x₁ x₂ rho, ∀ z ∈ ctxXi t tau x₁ x₂ rho, z * y = y * z := by
    intro y hy z hz
    have hzC : z ∈ ctxCY t tau x₁ x₂ rho := l18_Xi_le_C hc hz
    exact ((Subgroup.mem_centralizer_iff.mp hzC.2) y hy).symm
  let Ξ : Subgroup G := ctxXi t tau x₁ x₂ rho
  let Y : Subgroup G := ctxYq t tau x₁ x₂ rho
  let D : Subgroup G := Dsub Ξ Y hYc lam
  let D' : Subgroup G := Dsub Ξ Y hYc (rho * lam * rho⁻¹)
  have hDle : D ≤ Ξ := Dsub_le
  have hD'le : D' ≤ Ξ := Dsub_le
  have hD1 : ∀ x : G, x ∈ D → x ∈ Ξ ∧ lam * x * lam⁻¹ * x⁻¹ ∈ Y :=
    fun x hx => mem_Dsub.mp hx
  have hD'1 : ∀ x : G, x ∈ D' →
      x ∈ Ξ ∧ (rho * lam * rho⁻¹) * x * (rho * lam * rho⁻¹)⁻¹ * x⁻¹ ∈ Y :=
    fun x hx => mem_Dsub.mp hx
  refine ⟨D, hDle, ?_, ?_⟩
  · intro x hx h
    exact mem_Dsub.mpr ⟨hx, h⟩
  · have hcard_le : Nat.card D ≤ Nat.card D' := by
      let f : D → D' := fun x =>
        ⟨rho * x.1 * rho⁻¹, by
          show rho * x.1 * rho⁻¹ ∈ Dsub Ξ Y hYc (rho * lam * rho⁻¹)
          refine mem_Dsub.mpr ⟨?_, ?_⟩
          · exact (l18_Xi_normal hc.toCtx13).2 rho hρK x.1 (hD1 x.1 x.2).1
          · have hxY := (hD1 x.1 x.2).2
            have hcomm : (rho * lam * rho⁻¹) * (rho * x.1 * rho⁻¹) * (rho * lam * rho⁻¹)⁻¹
                * (rho * x.1 * rho⁻¹)⁻¹
                = rho * (lam * x.1 * lam⁻¹ * x.1⁻¹) * rho⁻¹ := by group
            rw [hcomm]
            exact hYnorm rho hρK _ hxY⟩
      have hf : Function.Injective f := by
        intro a b hab
        apply Subtype.ext
        have h : rho * a.1 * rho⁻¹ = rho * b.1 * rho⁻¹ := congrArg Subtype.val hab
        exact mul_left_cancel (mul_right_cancel h)
      exact Nat.card_le_card_of_injective f hf
    have hINle : D ⊓ D' ≤ Y := by
      intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxD, hxD'⟩ := hx
      have hxΞ : x ∈ Ξ := hDle hxD
      have h1 : lam * x * lam⁻¹ * x⁻¹ ∈ Y := (hD1 x hxD).2
      have h2 : (rho * lam * rho⁻¹) * x * (rho * lam * rho⁻¹)⁻¹ * x⁻¹ ∈ Y := (hD'1 x hxD').2
      have hlam2 : lam * lam = 1 := by
        have := (ctx13_lam_facts hc.toCtx13).1
        simpa [pow_two] using this
      have hlamρinvlam : lam * rho⁻¹ * lam = rho := by
        have e : lam * rho⁻¹ * lam = (lam * lam) * rho * (lam⁻¹ * lam) := by
          rw [← hc.lam_rho]
          group
        rw [e, hlam2]
        group
      have hρ3 : rho ^ 3 = 1 := by rw [← hc.ord_rho]; exact pow_orderOf_eq_one rho
      have hρ2 : rho * rho = rho⁻¹ := by
        have h : rho * rho * rho = 1 := by
          have := hρ3
          rwa [pow_succ, pow_two] at this
        exact eq_inv_of_mul_eq_one_left h
      have ha_lam : (rho * lam * rho⁻¹) * lam = rho⁻¹ := by
        have e : (rho * lam * rho⁻¹) * lam = rho * (lam * rho⁻¹ * lam) := by group
        rw [e, hlamρinvlam, hρ2]
      have haK : rho * lam * rho⁻¹ ∈ ctxK t tau x₁ x₂ rho :=
        (ctxK t tau x₁ x₂ rho).mul_mem ((ctxK t tau x₁ x₂ rho).mul_mem hρK hlamK)
          ((ctxK t tau x₁ x₂ rho).inv_mem hρK)
      have hcomm : ((rho * lam * rho⁻¹) * lam) * x * ((rho * lam * rho⁻¹) * lam)⁻¹ * x⁻¹
          = ((rho * lam * rho⁻¹) * (lam * x * lam⁻¹ * x⁻¹) * (rho * lam * rho⁻¹)⁻¹)
            * ((rho * lam * rho⁻¹) * x * (rho * lam * rho⁻¹)⁻¹ * x⁻¹) := by group
      have hp1 : (rho * lam * rho⁻¹) * (lam * x * lam⁻¹ * x⁻¹) * (rho * lam * rho⁻¹)⁻¹ ∈ Y :=
        hYnorm _ haK _ h1
      have hp2 : (rho * lam * rho⁻¹) * x * (rho * lam * rho⁻¹)⁻¹ * x⁻¹ ∈ Y := h2
      have hsum : ((rho * lam * rho⁻¹) * lam) * x * ((rho * lam * rho⁻¹) * lam)⁻¹ * x⁻¹ ∈ Y := by
        rw [hcomm]
        exact Y.mul_mem hp1 hp2
      have hrhoinv : rho⁻¹ * x * (rho⁻¹)⁻¹ * x⁻¹ ∈ Y := by
        have := hsum
        rwa [ha_lam] at this
      have h3 : rho * x * rho⁻¹ * x⁻¹ ∈ Y := by
        have e : rho * x * rho⁻¹ * x⁻¹
            = rho * (rho⁻¹ * x * (rho⁻¹)⁻¹ * x⁻¹)⁻¹ * rho⁻¹ := by group
        rw [e]
        exact hYnorm rho hρK _ (Y.inv_mem hrhoinv)
      exact l18_D_rho hc hxΞ h3
    have hYcard : Nat.card Y = 16 := l17_card_Y hc.toCtx13
    have hINcard : Nat.card ↥(D ⊓ D') ≤ 16 := by
      have := Subgroup.card_le_of_le hINle
      rwa [hYcard] at this
    have hprod := card_mul_card_le_of_le_card_mul_card_inf hDle hD'le
    have hΞcard : Nat.card Ξ = 2 ^ 8 := l18_card_Xi hc
    have hbound : Nat.card D * Nat.card D' ≤ 2 ^ 8 * 16 := by
      calc Nat.card D * Nat.card D' ≤ Nat.card Ξ * Nat.card ↥(D ⊓ D') := hprod
        _ ≤ 2 ^ 8 * 16 := by
            rw [hΞcard]
            exact Nat.mul_le_mul_left _ hINcard
    have hsq : Nat.card D * Nat.card D ≤ 2 ^ 12 := by
      have h1 : Nat.card D * Nat.card D ≤ Nat.card D * Nat.card D' :=
        Nat.mul_le_mul_left _ hcard_le
      have h2 : Nat.card D * Nat.card D' ≤ 2 ^ 12 := by
        have hb := hbound
        rwa [show (2 : ℕ) ^ 8 * 16 = 2 ^ 12 by norm_num] at hb
      exact le_trans h1 h2
    have hsq' : Nat.card D ^ 2 ≤ 64 ^ 2 := by
      have h1 : Nat.card D ^ 2 = Nat.card D * Nat.card D := pow_two _
      rw [h1, show (64 : ℕ) ^ 2 = 2 ^ 12 by norm_num]
      exact hsq
    exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hsq'

end CFSG.OddStandard.SmallF3.HarrisU33.S4B

module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelNu
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OddNu
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterLevelMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1OuterStage

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ}

theorem outerNu_inv (h : U3C1OuterStage G L f t T d V U U₁ k)
    (hv : ∃ v ∈ T, v ^ 2 = 1 ∧ v ∉ szT₁ L T ⊔ zpowers t)
    (hTV₁ : T ≤ normalizer ((U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) : Set G))
    (hμV : U₁ ≤ centralizer (V : Set G))
    (hlam : U₁ = szT₁ L T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G))) {g : G}
    (hgN : g ∈ normalizer ((T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) : Set G))
    {c w : G} (hc : c ∈ szT₁ L T) (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G))
    (hx : g * t * g⁻¹ = c * w * t) (hcw : c * w ∉ szT₁ L T ⊔ V) :
    ∀ x ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), t * x * t⁻¹ = x⁻¹ := by
  by_contra hne
  push Not at hne
  obtain ⟨w₀, hw₀, hw₀ne⟩ := hne
  have hν : ∃ w₀ ∈ U₁ ⊓ centralizer (szT₁ L T : Set G), (w₀ * t) ^ 2 ≠ 1 :=
    ⟨w₀, hw₀, fun h1 => hw₀ne (by
      rw [h.sq_mul_t] at h1
      exact eq_inv_of_mul_eq_one_right h1)⟩
  obtain ⟨K, _, _, _, v, μ, hK, hcoord, hμ⟩ := h.coords
  obtain ⟨-, -, -, -, -, hA₁sq, hinvA⟩ := h.start.facts_of_card_sylow h.card_sylow
  obtain ⟨-, -, hAC, -⟩ := h.start.szA_facts_of_card_sylow h.card_sylow
  have hcwU : c * w ∈ U₁ := mul_mem (h.T₁_le_U₁ hc) (mem_inf.mp hw).1
  have hxU : c * w * t ∉ U₁ := fun hxU => h.t_not_mem (by
    have := mul_mem (inv_mem hcwU) hxU
    rwa [inv_mul_cancel_left] at this)
  have hcA : c ∉ szA₁ (szT₁ L T) := by
    intro hcA
    have hcw' : c * w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G) :=
      mul_mem (h.V_le_V₁ (h.le hcA)) hw
    have hsq : (c * w * t) ^ 2 = 1 := by
      rw [← hx, sq, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group,
        h.t_mul_self, mul_one, mul_inv_cancel]
    exact hcw (mem_sup_right (h.mem_V_of_sq_eq_one hK hcoord hμ hμV hlam hν hcw' hsq))
  set C : Subgroup G := U₁ ⊓ centralizer ({c * w * t} : Set G) with hC
  have hmemC : ∀ z, z ∈ C ↔ z ∈ U₁ ∧ c * w * t * z = z * (c * w * t) := fun z => by
    rw [hC, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  have hCcard : (2 ^ f) ^ 3 ≤ Nat.card C := h.outerNu_card_le_centralizer hμV hlam hc hw
  have hV₁2 : IsPGroup 2 (U₁ ⊓ centralizer (szT₁ L T : Set G) : Subgroup G) :=
    IsPGroup.of_card (n := f * (k + 2)) (by rw [h.card_V₁ hlam, ← pow_mul])
  have hS2 : IsPGroup 2 (T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' h.start.isPGroup hV₁2 hTV₁
  have hU₁S : U₁ ≤ T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) :=
    hlam.le.trans (sup_le_sup_right (szT₁_le_left L T) _)
  have hPT' : ∀ z ∈ C, g⁻¹ * z * g ∈ T := by
    intro z hz
    obtain ⟨hzU, hzx⟩ := (hmemC z).mp hz
    have hzS : g⁻¹ * z * g ∈ T ⊔ (U₁ ⊓ centralizer (szT₁ L T : Set G)) := by
      have := (mem_normalizer_iff.mp (inv_mem hgN) z).mp (hU₁S hzU)
      rwa [inv_inv] at this
    refine h.start.outerNu_mem_T le_sup_left hS2 hzS ?_
    have e : z * (g * t * g⁻¹) = (g * t * g⁻¹) * z := by rw [hx]; exact hzx.symm
    calc g⁻¹ * z * g * t = g⁻¹ * (z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * z) * g := by rw [e]
      _ = t * (g⁻¹ * z * g) := by group
  set P : Subgroup G := C.map (MulAut.conj g⁻¹).toMonoidHom with hP
  have hmemP : ∀ s, s ∈ P ↔ ∃ z ∈ C, g⁻¹ * z * g = s := fun s => by
    rw [hP, mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hPT : P ≤ T := fun s hs => by
    obtain ⟨z, hz, rfl⟩ := (hmemP s).mp hs
    exact hPT' z hz
  have hPcard : Nat.card P = Nat.card C := card_map_of_injective (MulAut.conj g⁻¹).injective
  have htP : t ∉ P := fun htP => by
    obtain ⟨z, hz, hzt⟩ := (hmemP t).mp htP
    have hz' : z = c * w * t := by rw [← hx, ← hzt]; group
    exact hxU (hz' ▸ ((hmemC z).mp hz).1)
  have hA₁C : ∀ a ∈ szA₁ (szT₁ L T), a ∈ C := fun a ha =>
    (hmemC a).mpr ⟨h.T₁_le_U₁ (szA₁_le _ ha), h.outerNu_commute_szA₁ hc hw ha⟩
  have hsqC : ∀ z ∈ C, z ^ 2 ∈ szA₁ (szT₁ L T) := fun z hz =>
    h.outerNu_sq_mem hμV hlam hc hw ((hmemC z).mp hz).1 ((hmemC z).mp hz).2
  have hconj_pow : ∀ (z : G) (n : ℕ), (g⁻¹ * z * g) ^ n = g⁻¹ * z ^ n * g := fun z n => by
    simpa only [inv_inv] using conj_pow (a := g⁻¹) (b := z) (i := n)
  have hpow4 : ∀ s ∈ P, s ^ 4 = 1 := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := (hmemP s).mp hs
    rw [hconj_pow, show z ^ 4 = (z ^ 2) ^ 2 by rw [← pow_mul], hA₁sq _ (hsqC z hz), mul_one,
      inv_mul_cancel]
  have hA'S : ∀ a ∈ szA₁ (szT₁ L T), g⁻¹ * a * g ∈ szT₁ L T ⊔ zpowers t := by
    intro a ha
    by_contra haS
    have ha2 : (g⁻¹ * a * g) ^ 2 = 1 := by
      rw [hconj_pow, hA₁sq a ha, mul_one, inv_mul_cancel]
    have hac : ∀ s ∈ P, s * (g⁻¹ * a * g) = (g⁻¹ * a * g) * s := by
      intro s hs
      obtain ⟨z, hz, rfl⟩ := (hmemP s).mp hs
      have hza : z * a = a * z := by
        have e := h.conj_szA₁ z (h.U₁_le ((hmemC z).mp hz).1) a ha
        calc z * a = z * a * z⁻¹ * z := by group
          _ = a * z := by rw [e]
      calc g⁻¹ * z * g * (g⁻¹ * a * g) = g⁻¹ * (z * a) * g := by group
        _ = g⁻¹ * (a * z) * g := by rw [hza]
        _ = g⁻¹ * a * g * (g⁻¹ * z * g) := by group
    have hle := h.start.outerNu_card_le_of_central h.card_sylow hPT hpow4
      (hPT' a (hA₁C a ha)) ha2 haS hac
    rw [hPcard] at hle
    have hq4 := h.four_le_q
    have h16 : 16 * 2 ^ f ≤ (2 ^ f) ^ 3 := by
      calc 16 * 2 ^ f = 4 * 4 * 2 ^ f := by norm_num
        _ ≤ 2 ^ f * 2 ^ f * 2 ^ f := Nat.mul_le_mul_right _ (Nat.mul_le_mul hq4 hq4)
        _ = (2 ^ f) ^ 3 := by ring
    have hpos : 0 < 2 ^ f := by positivity
    omega
  have hsqA : ∀ s ∈ P, s ^ 2 ∈ szA L T t := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := (hmemP s).mp hs
    rw [hconj_pow]
    refine hinvA _ (hA'S _ (hsqC z hz)) ?_
    rw [hconj_pow, hA₁sq _ (hsqC z hz), mul_one, inv_mul_cancel]
  have hPle := h.start.outerNu_le_of_sq_mem h.card_sylow hv hPT htP hsqA
    (by rw [hPcard]; exact hCcard)
  obtain ⟨E, _, _, _, σ, hE, hσ, hfix, u, v', hco, hA⟩ :=
    h.start.exists_rootCoords_of_card_sylow h.card_sylow
  have hc0 : u c ≠ 0 := fun h0 => hcA ((hA c hc).mpr h0)
  obtain ⟨b, hb0, hbN⟩ :=
    U3C1Odd.exists_ne_zero_norm hσ (by have := h.four_le_q; omega) hE hfix hc0
  obtain ⟨y₀, hy₀, hy₀b⟩ := hco.u_surj b
  obtain ⟨r₀, hr₀, hr₀2⟩ := h.outerNu_exists_sq hc hy₀
  have hmemC' : ∀ y ∈ szT₁ L T, ∀ r ∈ V, r ^ 2 = y⁻¹ * c * y * c⁻¹ → y * r ∈ C :=
    fun y hy r hr hr2 => (hmemC _).mpr ⟨h.sup_le_U₁ (mul_mem (mem_sup_left hy)
      (mem_sup_right hr)), h.outerNu_commute_of_sq hμV hlam hc hw hy hr hr2⟩
  have hz₀C : y₀ * r₀ ∈ C := hmemC' y₀ hy₀ r₀ hr₀ hr₀2
  have hcomA : y₀⁻¹ * c * y₀ * c⁻¹ ∈ szA₁ (szT₁ L T) := by
    have := h.comm_T₁_mem (inv_mem hy₀) hc
    rwa [inv_inv] at this
  have hz2 : (y₀ * r₀) ^ 2 = y₀ ^ 2 * (y₀⁻¹ * c * y₀ * c⁻¹) := by
    rw [← hr₀2]
    have e : r₀ * y₀ = y₀ * r₀ := (h.V_comm hr₀ hy₀).symm
    calc (y₀ * r₀) ^ 2 = y₀ * (r₀ * y₀) * r₀ := by rw [sq]; group
      _ = y₀ * (y₀ * r₀) * r₀ := by rw [e]
      _ = y₀ ^ 2 * r₀ ^ 2 := by rw [sq, sq]; group
  have hy₀2 := hco.sq hy₀
  have hcm := U3C1Odd.rootCoords_comm hco (inv_mem hy₀) hc
  rw [inv_inv] at hcm
  have hcmT : y₀⁻¹ * c * y₀ * c⁻¹ ∈ szT₁ L T := szA₁_le _ hcomA
  have hy₀2T : y₀ ^ 2 ∈ szT₁ L T := pow_mem hy₀ 2
  have hz2T : (y₀ * r₀) ^ 2 ∈ szT₁ L T := by
    rw [hz2]
    exact mul_mem hy₀2T hcmT
  have hu2 : u ((y₀ * r₀) ^ 2) = 0 := by
    rw [hz2, hco.mul_u _ hy₀2T _ hcmT, hy₀2.1, hcm.1, add_zero]
  have hv2 : v' ((y₀ * r₀) ^ 2) = 0 := by
    rw [hz2, hco.v_mul_of_u_eq_zero hy₀2T hcmT hy₀2.1, hy₀2.2, hcm.2, hco.u_inv hy₀, map_neg,
      hy₀b]
    simp only [CharTwo.neg_eq]
    exact hbN
  have hz21 : (y₀ * r₀) ^ 2 = 1 := hco.inj _ hz2T _ (one_mem _) (by rw [hu2, hco.u_one])
    (by rw [hv2, U3C1Odd.rootCoords_v_one hco])
  have hs₀A : g⁻¹ * (y₀ * r₀) * g ∈ szA L T t := by
    refine hinvA _ (hPle ((hmemP _).mpr ⟨_, hz₀C, rfl⟩)) ?_
    rw [hconj_pow, hz21, mul_one, inv_mul_cancel]
  have hcentral : ∀ z ∈ C, (y₀ * r₀) * z = z * (y₀ * r₀) := by
    intro z hz
    have hsP : g⁻¹ * z * g ∈ szT₁ L T ⊔ zpowers t := hPle ((hmemP _).mpr ⟨z, hz, rfl⟩)
    have e := mem_centralizer_iff.mp (hAC hs₀A) _ hsP
    have e2 : g⁻¹ * (z * (y₀ * r₀)) * g = g⁻¹ * ((y₀ * r₀) * z) * g := by
      calc g⁻¹ * (z * (y₀ * r₀)) * g = g⁻¹ * z * g * (g⁻¹ * (y₀ * r₀) * g) := by group
        _ = g⁻¹ * (y₀ * r₀) * g * (g⁻¹ * z * g) := e
        _ = g⁻¹ * ((y₀ * r₀) * z) * g := by group
    exact (mul_left_cancel (mul_right_cancel e2)).symm
  have hz₀A : y₀ * r₀ ∈ szA₁ (szT₁ L T) :=
    h.outerNu_mem_szA₁_of_central hμV hlam hc hw ((hmemC _).mp hz₀C).1 ((hmemC _).mp hz₀C).2
      (fun y hy r hr hr2 => hcentral _ (hmemC' y hy r hr hr2))
  have hy₀V : y₀ ∈ V := by
    have := mul_mem (h.le hz₀A) (inv_mem hr₀)
    rwa [mul_inv_cancel_right] at this
  have hy₀A : y₀ ∈ szA₁ (szT₁ L T) := by
    rw [← h.inf_eq_szA₁]
    exact mem_inf.mpr ⟨hy₀, hy₀V⟩
  exact hb0 (by rw [← hy₀b]; exact (hA y₀ hy₀).mp hy₀A)

end U3C1OuterStage

theorem u3C1OuterNuInput_holds : U3C1OuterNuInput := by
  intro G _ _ L f t T R₂ D d V U U₁ k H hL hμV hlam _ hesc
  have h := H.outerStage hL
  obtain ⟨g, hgN, -, y, hy, u, hu, hgt, hyu⟩ := hesc
  obtain ⟨-, -, -, hTN₁, -, -, -⟩ := H.start.start_of_card_sylow H.card_sylow
  exact h.outerNu_inv H.outer (fun s hs => mem_normalizer_outerV₁ (hL.T_le hs) (hTN₁ hs)) hμV
    hlam hgN hy hu hgt hyu

end CFSG.SeitzReduction.RankOne

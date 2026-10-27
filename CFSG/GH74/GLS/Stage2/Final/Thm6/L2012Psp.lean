module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Basic
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20
open scoped commutatorElement

variable {G : Type} [Group G]

theorem Fm_conj_mem' {B C : Subgroup G} (hBnorm : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B) {c : G} (hc : c ∈ C)
    {y : G} (hy : y ∈ Fm B) : c * y * c⁻¹ ∈ Fm B := by
  obtain ⟨y', hy', rfl⟩ := hy
  set φ := conjRestrict B c (hBnorm c hc) (fun b hb => by
    simpa using hBnorm c⁻¹ (C.inv_mem hc) b hb) with hφ
  have hchar := (fittingSubgroup_characteristic (G := ↥B)).fixed φ
  have hmem : φ y' ∈ fittingSubgroup ↥B := by
    have : y' ∈ (fittingSubgroup ↥B).comap φ.toMonoidHom := by rw [hchar]; exact hy'
    exact this
  exact ⟨φ y', hmem, rfl⟩

theorem F20_conj_mem (z : G) {c : G} (hc : c ∈ Cen z) {y : G} (hy : y ∈ F20 z) : c * y * c⁻¹ ∈ F20 z :=
  Fm_conj_mem' (B := OddCore z) (C := Cen z) (fun c' hc' b hb => by
    obtain ⟨y', hy', rfl⟩ := hb
    exact ⟨⟨c', hc'⟩ * y' * ⟨c', hc'⟩⁻¹, (CFSG.pPrimeCore_normal).conj_mem y' hy' ⟨c', hc'⟩, rfl⟩) hc hy

theorem F20_le_OddCore (z : G) : F20 z ≤ OddCore z := Subgroup.map_subtype_le _

omit [Group G] in
theorem eq_one_or_eq_of_mem_zpowers {z y : G} [Group G] (hz2 : z * z = 1) (h : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp h
  have hsq : z ^ 2 = 1 := by rw [sq]; exact hz2
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · left
    rw [← Int.emod_add_mul_ediv n 2, h0, zero_add, zpow_mul]
    simp [hsq]
  · right
    rw [← Int.emod_add_mul_ediv n 2, h1, zpow_add, zpow_mul]
    simp [hsq]


section Main

variable [Finite G]

omit [Finite G] in
theorem mul_self_eq_one_of_conj {z y : G} (hz2 : z * z = 1) (h : IsConj z y) : y * y = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hz2]; group

theorem psp4_bc (h11 : Lemma20_11) {z : G} {k : Kind} {S M : Subgroup G} (hF : Fail20 G z k S M) (hMC : M = Cen z)
    (hpsp : ∃ q : ℕ, TypePSp4 z k S q) :
    (∀ u ∈ L20 z, IsConj z u → u = z) ∧
      ∀ y ∈ S, IsConj z y →
        (∃ (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), Stage1Pair G z S q L₁ L₂ ∧ Swaps z y L₁ L₂) →
        ∀ f ∈ F20 z, y * f * y⁻¹ = f⁻¹ := by
  subst hMC
  have hctx : Stage2Ctx G z k S := hF.ctx.ctx17.ctx
  obtain ⟨q', hk, L₁', L₂', hpsp4⟩ := hpsp
  have hT : TypeCl z k S := Or.inr ⟨q', hk, L₁', L₂', hpsp4⟩
  have h12b : ∀ u ∈ Em (Cen z), IsConj z u → u = z := by
    obtain ⟨x, hx⟩ := hpsp4.two
    exact layer_conj_eq_of_two hctx.central hx
  refine ⟨h12b, ?_⟩
  intro y hyS hyconj hsw
  have hSC : S ≤ Cen z := hctx.S_le_Cen
  have hz2 : z * z = 1 := by
    have := hctx.orderOf_z
    calc z * z = z ^ 2 := (sq z).symm
      _ = 1 := by rw [← this]; exact pow_orderOf_eq_one z
  have h4a : pLayerOf 2 (Cen z) = Em (Cen z) := hF.ctx.thm4.1
  have hidx := hpsp4.index
  obtain ⟨q, L₁, L₂, hpair, hswap⟩ := hsw
  obtain ⟨K₁, K₂, hK⟩ := exists_compData hpair h4a
  have hyC : y ∈ Cen z := hSC hyS
  have hy2 : y * y = 1 := mul_self_eq_one_of_conj hz2 hyconj
  obtain ⟨c0, hc0⟩ := isConj_iff.mp hyconj
  have hzcg : zc z c0⁻¹ = y := by
    simp only [zc, inv_inv]
    exact hc0
  have hyne : y ≠ z := by
    intro hyz
    obtain ⟨hy, hsw'⟩ := swaps_cj hswap
    have hcen : toBar z ⟨y, hy⟩ ∈ center (CentralizerBar z) := by
      have := toBar_z_mem_center z
      have e : (⟨y, hy⟩ : ↥(Cen z)) = ⟨z, mem_Cen_self z⟩ := Subtype.ext hyz
      rwa [e]
    have hfix : cj (toBar z ⟨y, hy⟩) L₁ = L₁ :=
      cj_eq_iff.mpr (Subgroup.center_le_normalizer (L₁ : Set (CentralizerBar z)) hcen)
    exact hpair.ne (hfix.symm.trans hsw')
  have hynot : y ∉ zpowers z := by
    intro h
    rcases eq_one_or_eq_of_mem_zpowers hz2 h with h1 | h1
    · rw [h1] at hyconj
      have h3 := orderOf_eq_two_of_conj hctx.orderOf_z hyconj
      rw [orderOf_one] at h3
      omega
    · exact hyne h1
  set g := c0⁻¹ with hg
  have hyC' : zc z g ∈ Cen z := by rw [hzcg]; exact hyC
  have hy2' : zc z g * zc z g = 1 := by rw [hzcg]; exact hy2
  have htC : g * z * g⁻¹ ∈ Cen z := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hyC'
    simp only [zc] at h1
    calc g * z * g⁻¹ * z = g * (z * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * z * g) * z) * g⁻¹ := by rw [← h1]
      _ = z * (g * z * g⁻¹) := by group
  have ht2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  obtain ⟨c, hcC, hc⟩ := exists_mem_conj_into_sylow hctx.sylow htC ht2
  set g₁ := c * g with hg₁
  have hzc : zc z g₁ = zc z g := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hcC
    simp only [zc, hg₁]
    calc (c * g)⁻¹ * z * (c * g) = g⁻¹ * (c⁻¹ * z * c) * g := by group
      _ = g⁻¹ * z * g := by
        have : c⁻¹ * z * c = z := by
          calc c⁻¹ * z * c = c⁻¹ * (z * c) := by group
            _ = c⁻¹ * (c * z) := by rw [h1]
            _ = z := by group
        rw [this]
  have hzc' : zc z g₁ = y := hzc.trans hzcg
  have hyC₁ : zc z g₁ ∈ Cen z := by rw [hzc']; exact hyC
  have hy₁2 : zc z g₁ * zc z g₁ = 1 := by rw [hzc']; exact hy2
  have hsw₁ : cj (toBar z ⟨zc z g₁, hyC₁⟩) L₁ = L₂ := by
    obtain ⟨hy, hsw'⟩ := swaps_cj hswap
    have e : (⟨zc z g₁, hyC₁⟩ : ↥(Cen z)) = ⟨y, hy⟩ := Subtype.ext hzc'
    rwa [e]
  have ht₁S : g₁ * z * g₁⁻¹ ∈ S := by
    have e : g₁ * z * g₁⁻¹ = c * (g * z * g⁻¹) * c⁻¹ := by simp only [hg₁]; group
    rwa [e]
  have ht₁C : g₁ * z * g₁⁻¹ ∈ Cen z := hSC ht₁S
  have ht₁2 : (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = 1 := by
    calc (g₁ * z * g₁⁻¹) * (g₁ * z * g₁⁻¹) = g₁ * (z * z) * g₁⁻¹ := by group
      _ = 1 := by rw [hz2]; group
  have ht₁conj : IsConj z (g₁ * z * g₁⁻¹) := isConj_iff.mpr ⟨g₁, rfl⟩
  have ht₁ne : g₁ * z * g₁⁻¹ ≠ z := by
    intro htz
    apply hyne
    rw [← hzc']
    have : g₁ * z = z * g₁ := by
      calc g₁ * z = (g₁ * z * g₁⁻¹) * g₁ := by group
        _ = z * g₁ := by rw [htz]
    simp only [zc]
    calc g₁⁻¹ * z * g₁ = g₁⁻¹ * (z * g₁) := by group
      _ = g₁⁻¹ * (g₁ * z) := by rw [this]
      _ = z := by group
  obtain ⟨ht₁C', htsw₁'⟩ :=
    exists_swap_of_mem_S hpair hK hSC hidx hyS hswap h12b ht₁S ht₁conj ht₁ne ht₁2
  have hfix : ∀ e ∈ F20 z, y * e * y⁻¹ = e → e = 1 := by
    intro e he hye
    have heA : e ∈ OddCore z := F20_le_OddCore z he
    have hodd : Odd (orderOf e) := odd_orderOf_of_mem_pPrimeCoreOf (F := Cen z) heA
    have heC : e ∈ Cen (zc z g₁) := by
      rw [hzc', Subgroup.mem_centralizer_singleton_iff]
      calc e * y = (y * e * y⁻¹) * y := by rw [hye]
        _ = y * e := by group
    have hxI : e ∈ centralizer (Em ((K₁ ⊔ K₂) ⊓ centralizer ({zc z g₁} : Set G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have hiL : i ∈ Em (Cen z) := by
        rw [hK.layer]
        exact (Subgroup.map_subtype_le _ hi).1
      exact hK.oddcomm e heA i hiL |>.symm
    have hmem := oddA_y hK hz2 hyC₁ hy₁2 hsw₁ ht₁C' htsw₁' heC hodd hxI
    have hbot := h11 G z k S (Cen z) hF rfl hT g₁ (by rw [hzc']; exact hyS) (by rw [hzc']; exact hynot)
    have : e ∈ F20 z ⊓ Ag z g₁ := ⟨he, hmem⟩
    rw [hbot] at this
    exact (Subgroup.mem_bot.mp this)
  intro f hf
  exact inverted_of_fixed_point_free hy2 (fun e he => F20_conj_mem z hyC he) hfix f hf

end Main

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

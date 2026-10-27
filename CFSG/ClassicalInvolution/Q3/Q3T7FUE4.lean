module

public import CFSG.ClassicalInvolution.Q3.Q3T7FUE3
public import CFSG.ClassicalInvolution.Asc77.AscE187EndC
public import CFSG.ClassicalInvolution.Q3.Q3T7FUL

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7FU

variable {MT : CFSG.ClassicalInvolution.Uniform.MemberType}
open CFSG.ClassicalInvolution.Q3.Q3T7M (omegaNbr_subset_kPerp_of_twin mem_kPerp_of_twin
  omegaStarDiff_subset_of_twin l6_3 le_of_sq_mem_of_oddGen odd_mem_of_mem_sup_central
      oddGen_conjSub)
open CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
    (HypOmegaMod L6_2 l6_2 L6_7 l6_7_proved L6_10 l6_10_proved
  L6_11 l6_11_proved L6_9 l6_9_proved)

section
namespace Asc77.AscE186
open CFSG.ClassicalInvolution.Asc77.AscE186
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G} {N : Subgroup G} [N.Normal]

theorem exists_lift_twin (hH : H ≠ ⊤) (hcent : E186Cent2 Ω K H) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot MT Ω N) (hK : K ∈ Ω) {Lb : Subgroup (G ⧸ N)}
    (hLb : Lb ∈ twinSet (quotFamily Ω N) (K.map (QuotientGroup.mk' N))) :
    ∃ L ∈ twinSet Ω K, L.map (QuotientGroup.mk' N) = Lb := by
  obtain ⟨hLbΩ, zb, hzbK, hzbL⟩ := hLb
  obtain ⟨L₀, hL₀, rfl⟩ := hLbΩ
  obtain ⟨z, hz⟩ := c.hyp.exists_uniqueInvolution hK
  obtain ⟨z₀, hz₀⟩ := c.hyp.exists_uniqueInvolution hL₀
  have e1 : QuotientGroup.mk' N z = zb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet K hK) hz).eq hzbK
  have e2 : QuotientGroup.mk' N z₀ = zb :=
    (AscQuot.isUniqueInvolution_map_mk (c.meet L₀ hL₀) hz₀).eq hzbL
  have hzz : z₀ = z := by
    by_cases hLK : L₀ = K
    · subst hLK
      exact (hz.eq hz₀).symm
    have hn : z₀⁻¹ * z ∈ N := by
      have : QuotientGroup.mk' N (z₀⁻¹ * z) = 1 := by
        rw [map_mul, map_inv, e1, e2, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hzn : z = z₀ * (z₀⁻¹ * z) := by group
    have hLc : L₀ ≤ Subgroup.centralizer ({z} : Set G) := by
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : z₀ * w = w * z₀ := hz₀.commute_of_mem hw
      have h2 : w * (z₀⁻¹ * z) = (z₀⁻¹ * z) * w :=
        Subgroup.mem_center_iff.mp (c.central hn) w
      calc w * z = w * (z₀ * (z₀⁻¹ * z)) := by rw [← hzn]
        _ = (w * z₀) * (z₀⁻¹ * z) := by group
        _ = (z₀ * w) * (z₀⁻¹ * z) := by rw [h1]
        _ = z₀ * (w * (z₀⁻¹ * z)) := by group
        _ = z₀ * ((z₀⁻¹ * z) * w) := by rw [h2]
        _ = z * w := by group
    have hnbr : L₀ ∈ omegaNbr Ω K :=
      mem_omegaNbr_of_le_centralizer c.hyp hK hL₀ hLK hz hLc
    obtain ⟨R₁, R₂, hR₁, hR₂, -, hcomm⟩ := exists_commuting_sylow_pair c.hyp hK hnbr
    have hR₁Ω : R₁ ∈ RSet Ω := mem_RSet_of_isSylow2In hK hR₁
    have hR₂Ω : R₂ ∈ RSet Ω := mem_RSet_of_isSylow2In hL₀ hR₂
    have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁.1 hR₁.2.1
      (by have := c.hyp.eight_le_of_mem_RSet hR₁Ω; omega)
    have hzR₂ : z₀ ∈ R₂ := AscL62.mem_of_uniqueInvolution_of_pGroup hz₀ hR₂.1 hR₂.2.1
      (by have := c.hyp.eight_le_of_mem_RSet hR₂Ω; omega)
    have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
    have hbot := inf_sup_central_eq_bot hH hcent c.central hN2 hKtw (Set.mem_insert_of_mem _ hnbr)
      hR₁Ω hR₁.1 hR₂Ω hR₂.1 (Or.inl hcomm)
    have hmem : z₀⁻¹ * z ∈ (R₁ ⊔ R₂) ⊓ N := by
      refine ⟨?_, hn⟩
      have hz₀inv : z₀⁻¹ = z₀ := inv_eq_of_mul_eq_one_right hz₀.sq
      rw [hz₀inv]
      exact (R₁ ⊔ R₂).mul_mem (Subgroup.mem_sup_right hzR₂) (Subgroup.mem_sup_left hzR₁)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : z = z₀ := by
      have := congrArg (fun w => z₀ * w) hmem
      simpa using this
    exact this.symm
  refine ⟨L₀, ⟨hL₀, z, hz, hzz ▸ hz₀⟩, rfl⟩

theorem E186Cent2.quot_cent (hH : H ≠ ⊤) (hN2 : IsPGroup 2 ↥N)
    (c : CentQuot MT Ω N) (hodd : ∀ K ∈ Ω, Subgroup.closure {x : G | x ∈ K ∧ Odd (orderOf x)} = K)
        (hK : K ∈ Ω) (hcent : E186Cent2 Ω K H)
    (h18 : ∀ M ∈ dstarComp Ω K, ∀ u ∈ M, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H) :
    E186Cent2 (quotFamily Ω N) (K.map (QuotientGroup.mk' N)) (H.map (QuotientGroup.mk' N)) := by
  intro Lb hLb Jb hJb Rb₁ Rb₂ hRb₁ hRb₁L hRb₂ hRb₂J hcb ab hab hab1 hab2
  obtain ⟨L, hL, rfl⟩ := exists_lift_twin hH hcent hN2 c hK hLb
  obtain ⟨J, hJ, rfl⟩ := exists_lift_kperp c hodd hL.1 hJb
  obtain ⟨R₁, R₂, hR₁, hR₁L, hR₂, hR₂J, rfl, rfl, hc⟩ :=
    exists_lift_sylow_pair hN2 c hodd hL.1 hJ hRb₁ hRb₁L hRb₂ hRb₂J hcb
  obtain ⟨b, hb, hb1, hb2, rfl⟩ :=
    exists_involution_lift hH hcent hN2 c.central hL hJ hR₁ hR₁L hR₂ hR₂J hc hab hab1 hab2
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hn : b⁻¹ * (g * b * g⁻¹) ∈ N := by
    have : QuotientGroup.mk' N (b⁻¹ * (g * b * g⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      have h1 : QuotientGroup.mk' N g * QuotientGroup.mk' N b * (QuotientGroup.mk' N g)⁻¹ =
          QuotientGroup.mk' N b := by
        rw [hx]
        group
      rw [h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp this
  have hQ : IsQuatSub R₁ := c.hyp.isQuatSub_of_mem_RSet hR₁
  obtain ⟨u, huR₁, hu4, hub⟩ : ∃ u ∈ R₁, orderOf u = 4 ∧ u * b = b * u := by
    rcases hc with hcomm | rfl
    · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ :=
        CFSG.ClassicalInvolution.Asc77.AscE186.exists_mul_of_mem_sup_of_commutes hcomm hb
      obtain ⟨u, huR₁, hu4, huy₁⟩ := exists_orderOf_four_commute_of_isQuatSub hQ hy₁
      refine ⟨u, huR₁, hu4, ?_⟩
      calc u * (y₁ * y₂) = (u * y₁) * y₂ := by group
        _ = (y₁ * u) * y₂ := by rw [huy₁]
        _ = y₁ * (u * y₂) := by group
        _ = y₁ * (y₂ * u) := by rw [hcomm u huR₁ y₂ hy₂]
        _ = (y₁ * y₂) * u := by group
    · rw [sup_idem] at hb
      exact exists_orderOf_four_commute_of_isQuatSub hQ hb
  have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (g * u * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * u * g⁻¹) := by
      calc (g * u * g⁻¹) * (g * b * g⁻¹) = g * (u * b) * g⁻¹ := by group
        _ = g * (b * u) * g⁻¹ := by rw [hub]
        _ = (g * b * g⁻¹) * (g * u * g⁻¹) := by group
    set n : G := b⁻¹ * (g * b * g⁻¹) with hndef
    have hgb : g * b * g⁻¹ = b * n := by rw [hndef]; group
    rw [hgb] at e
    have hcn : ∀ y : G, y * n = n * y := fun y => Subgroup.mem_center_iff.mp (c.central hn) y
    have e2 : ((g * u * g⁻¹) * b) * n = (b * (g * u * g⁻¹)) * n := by
      calc ((g * u * g⁻¹) * b) * n = (g * u * g⁻¹) * (b * n) := by group
        _ = (b * n) * (g * u * g⁻¹) := e
        _ = b * (n * (g * u * g⁻¹)) := by group
        _ = b * ((g * u * g⁻¹) * n) := by rw [hcn]
        _ = (b * (g * u * g⁻¹)) * n := by group
    exact mul_right_cancel e2
  have hgH : g * u * g⁻¹ ∈ H := hcent L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hc b hb hb1 hb2 hgu
  have hg : g ∈ H :=
    h18 L (mem_dstarComp_of_twin c.hyp hK hL) u (hR₁L huR₁) hu4 g hgH
  exact Subgroup.mem_map_of_mem _ hg

end Asc77.AscE186
end
section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem hbad_twImage (hΩ : HM MT Ω) {H : Subgroup G} {t : G}
    (hbad : ∀ M ∈ Ω, IsUniqueInvolution M t → ∀ u ∈ M, orderOf u = 4 → u ∉ H) :
    ∀ L ∈ twFamily Ω t, IsUniqueInvolution L (twT t) → ∀ ū ∈ L, orderOf ū = 4 →
      ū ∉ twImage t H :=
  E187C.hbad_twImage_of hΩ.conjInvariant (fun hM hMt => exists_twHom hΩ hM hMt) hbad

end Asc77
end
end CFSG.ClassicalInvolution.T7FU

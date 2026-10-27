module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEQuotCentLift
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmECent

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section QuotCentMain

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem quotCent_mem_of_map_mem_of_le {T : Subgroup G} (hNT : N ≤ T) {x : G}
    (hx : QuotientGroup.mk' N x ∈ T.map (QuotientGroup.mk' N)) : x ∈ T := by
  have h2 := (Subgroup.mem_comap).mpr hx
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNT] at h2

theorem MinCex.quotCent_exists_W (hr : 3 ≤ r) (c : MinCex r Ω K S R W H)
    (hNc : N ≤ Subgroup.center G) (hN2 : IsPGroup 2 ↥N) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) :
    ∃ Wb ∈ WSet (quotFamily Ω N), Wb ≤ (S : Subgroup G).map (QuotientGroup.mk' N) ∧
      (∀ s ∈ (S : Subgroup G).map (QuotientGroup.mk' N), conjSub s Wb = Wb) ∧
      CentPairs (quotFamily Ω N) ((S : Subgroup G).map (QuotientGroup.mk' N)) Wb
        (H.map (QuotientGroup.mk' N)) := by
  have hΩ := c.stand.hyp
  obtain ⟨hWmem, hWS, hWn⟩ := c.stand.hW
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK := c.stand.mem
  have cq : CentQuotGen Ω N := centQuotGen hr hΩ c.stand.quat hNc hmeet
  have hNS : N ≤ (S : Subgroup G) := hN2.le_sylow_of_normal S
  refine ⟨W.map (QuotientGroup.mk' N), quotCent_map_mem_WSet cq hN2 hWmem, Subgroup.map_mono hWS,
    ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [← AscQuot.map_conjSub, hWn s hs]
  intro Mb hMb hMbW Jb hJb Rb₁ Rb₂ hRb₁ hRb₁M hRb₁S hRb₂ hRb₂J hRb₂S hcb ab habR habW hab1 hab2
  obtain ⟨M, hMΩ, rfl⟩ := hMb
  have hMW : M ⊓ W ∈ USet Ω := by
    obtain ⟨U, hU, hUM, hUS, -⟩ := quotCent_lift_USet cq hNS hMbW
      (inf_le_right.trans (Subgroup.map_mono hWS)) hMΩ inf_le_left
    obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩ.exists_data_of_mem_USet hU
    refine inf_W_mem_USet_of_card hΩ hWmem hWS hMΩ ?_
    have := Subgroup.card_le_of_le (le_inf hUM hUS)
    omega
  obtain ⟨J, hJ, rfl⟩ := CentEng.exists_lift_kperp_cent cq hMΩ hJb
  obtain ⟨R₁, R₂, hR₁, hR₁M, hR₂, hR₂J, rfl, rfl, hcomm⟩ :=
    CentEng.exists_lift_sylow_pair_cent hN2 cq hMΩ hJ hRb₁ hRb₁M hRb₂ hRb₂J hcb
  have hR₁S : R₁ ≤ (S : Subgroup G) := fun x hx =>
    quotCent_mem_of_map_mem_of_le hNS (hRb₁S (Subgroup.mem_map_of_mem _ hx))
  have hR₂S : R₂ ≤ (S : Subgroup G) := fun x hx =>
    quotCent_mem_of_map_mem_of_le hNS (hRb₂S (Subgroup.mem_map_of_mem _ hx))
  have habX : ab ∈ (R₁ ⊔ R₂).map (QuotientGroup.mk' N) := by rwa [Subgroup.map_sup]
  obtain ⟨y, hy, rfl⟩ := habX
  obtain ⟨w, hw, hwy⟩ := habW
  obtain ⟨hy1, hyy, -, hCy, u, huM, hu4, huy⟩ :=
    c.quotCent_exists_lift hN2 hNc hmeet hMΩ hMW hJ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm hy hw hwy.symm
      hab1 hab2
  have hMsg : M ∈ dstarComp Ω K := mem_dstarComp_of_inf_W hΩ hWmem hK hMΩ
    (inf_W_mem_USet' hΩ hWmem hWS hK hRR hRK hRS) hMW
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hnN : y⁻¹ * (g * y * g⁻¹) ∈ N := by
    have h0 : QuotientGroup.mk' N (y⁻¹ * (g * y * g⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      have h1 : QuotientGroup.mk' N g * QuotientGroup.mk' N y * (QuotientGroup.mk' N g)⁻¹ =
          QuotientGroup.mk' N y := by
        rw [hx]
        group
      rw [h1, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hgu : g * u * g⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e : (g * u * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * u * g⁻¹) := by
      calc (g * u * g⁻¹) * (g * y * g⁻¹) = g * (u * y) * g⁻¹ := by group
        _ = g * (y * u) * g⁻¹ := by rw [huy]
        _ = (g * y * g⁻¹) * (g * u * g⁻¹) := by group
    set n : G := y⁻¹ * (g * y * g⁻¹) with hndef
    have hgy : g * y * g⁻¹ = y * n := by rw [hndef]; group
    rw [hgy] at e
    have hcn : ∀ t : G, t * n = n * t := fun t => Subgroup.mem_center_iff.mp (hNc hnN) t
    have e2 : ((g * u * g⁻¹) * y) * n = (y * (g * u * g⁻¹)) * n := by
      calc ((g * u * g⁻¹) * y) * n = (g * u * g⁻¹) * (y * n) := by group
        _ = (y * n) * (g * u * g⁻¹) := e
        _ = y * (n * (g * u * g⁻¹)) := by group
        _ = y * ((g * u * g⁻¹) * n) := by rw [hcn]
        _ = (y * (g * u * g⁻¹)) * n := by group
    exact mul_right_cancel e2
  have hgH : g * u * g⁻¹ ∈ H := hCy hgu
  exact Subgroup.mem_map_of_mem _ (c.mem_of_conj_mem_dstar hMsg huM hu4 hgH)

theorem EStand.three_le {K R W : Subgroup G} {S : Sylow 2 G} (h : EStand r Ω K S R W) : 3 ≤ r := by
  by_contra hr
  have hexp : 2 ^ (r - 2) = 1 := by
    have : r - 2 = 0 := by omega
    rw [this]; rfl
  obtain ⟨P, hP, ⟨e⟩⟩ := h.quat K h.mem
  rw [hexp] at e
  have hq : ∀ a b : QuaternionGroup 1, a * b = b * a := by decide
  obtain ⟨-, P', hP', hnc⟩ := h.hyp.omega1 K h.mem
  obtain ⟨g, -, hg⟩ := Sec6Gen.exists_conjSub_eq_of_isSylow2In hP hP'
  apply hnc
  have hmem : ∀ x : ↥P', g⁻¹ * (x : G) * g ∈ P := by
    intro x
    have : (x : G) ∈ conjSub g P := by rw [hg]; exact x.2
    exact mem_conjSub_iff.mp this
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hab : (⟨g⁻¹ * (a : G) * g, hmem a⟩ : ↥P) * ⟨g⁻¹ * (b : G) * g, hmem b⟩ =
      ⟨g⁻¹ * (b : G) * g, hmem b⟩ * ⟨g⁻¹ * (a : G) * g, hmem a⟩ :=
    e.injective (by rw [map_mul, map_mul, hq])
  have h1 : g⁻¹ * (a : G) * g * (g⁻¹ * (b : G) * g) = g⁻¹ * (b : G) * g * (g⁻¹ * (a : G) * g) :=
    congrArg Subtype.val hab
  have h2 : g⁻¹ * ((a : G) * b) * g = g⁻¹ * ((b : G) * a) * g := by
    calc g⁻¹ * ((a : G) * b) * g = g⁻¹ * (a : G) * g * (g⁻¹ * (b : G) * g) := by group
      _ = g⁻¹ * (b : G) * g * (g⁻¹ * (a : G) * g) := h1
      _ = g⁻¹ * ((b : G) * a) * g := by group
  exact mul_left_cancel (mul_right_cancel h2)

instance instPrintedQuotCent (r : ℕ) : PrintedQuotCent r :=
  ⟨fun G _ _ Ω K S R W H N _ c hNc hN2 _ hmeet =>
    c.quotCent_exists_W c.stand.three_le hNc hN2 hmeet⟩

end QuotCentMain

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4

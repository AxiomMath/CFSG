module

public import CFSG.ClassicalInvolution.Q3.Q3T7W21N07
public import CFSG.ClassicalInvolution.Q3.Q3T7W21B03
public import CFSG.ClassicalInvolution.Q3.Q3T7W21N02
public import CFSG.ClassicalInvolution.Q3.Q3T7W21N03
public import CFSG.ClassicalInvolution.Q3.Q3T7W21N04
public import CFSG.ClassicalInvolution.Q3.Q3T7W21N05
public import CFSG.ClassicalInvolution.Q3.Q3T7W21N06

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section
namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson


namespace T7N

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem le_exactLayer_of_sylow (hΩ : Q3T7M.HM Ω) {u : G} (hu2 : u * u = 1) {M R : Subgroup G}
    (hM : M ∈ Ω) (hR : IsSylow2In R M) (hRu : R ≤ Subgroup.centralizer ({u} : Set G)) :
    R ≤ ExactLayer.exactLayer Ω u := by
  have hcA : IsPGroup 2 (Subgroup.zpowers u) := ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hMt : M ∈ ExactLayer.tqMembers Ω u :=
    (ExactLayer.mem_tqMembers_iff_exists_sylow hΩ hcA).mpr ⟨hM, R, hR, hRu⟩
  refine le_trans ?_ (ExactLayer.exactCore_le_exactLayer hMt)
  rw [ExactLayer.exactCore_def]
  exact le_inf hR.1 hRu

end T7N

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem c21_normCent_of_Y_ne (hC3 : Q3T8.Asc77.C21_3) (hY : Q3T8.Asc77.C21_14_Y_ne_W) :
    Q3T8.Asc77.C21_NormCent := by
  classical
  intro G _ _ _ Ω K K' z u J t W h hα hD
  have hne : dComp Ω K ≠ dstarComp Ω K := fun heq =>
    hD (h.rLayer_tz_le_sigmaGen_of_eq hC3 hα heq)
  have hst := h.std.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hP : Q3T8.Asc77.PartIHyp Ω := ⟨hst.hyp, hst.cls, hst.aEmpty⟩
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := h.std.hK'.1
  have hJΩ : J ∈ Ω := h.hJ.1
  have hz : IsUniqueInvolution K z := h.std.hz
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz h.std.hK'
  have htz : t ≠ z := h.twinFrameData.t_ne_z
  have c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP h.hW
  have hnc : ¬ DbarConnected Ω W := h.not_dbarConnected hne
  have hKt : K ≤ Subgroup.centralizer ({t} : Set G) :=
    Hyp21.twin_le_centralizer_t h hC3 hα (mem_twinSet_self hK hz)
  have hK't : K' ≤ Subgroup.centralizer ({t} : Set G) :=
    Hyp21.twin_le_centralizer_t h hC3 hα h.std.hK'
  have hEt : K ⊔ K' ≤ Subgroup.centralizer ({t} : Set G) := sup_le hKt hK't
  have hEN : K ⊔ K' ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer (hΩ.le_normalizer_of_twin hK'Ω hK h.std.hne hzK' hz)
  obtain ⟨ρ₁, hρ₁⟩ := c.exists_rep_of_involution_mem hst.cls hK hz h.hzW
  obtain ⟨ρ₂, hρ₂⟩ := c.exists_rep_of_involution_mem hst.cls hK'Ω hzK' h.hzW
  obtain ⟨ρ_J, hρ_J⟩ := c.exists_rep_of_involution_mem hst.cls hJΩ h.ht h.htW
  obtain ⟨ρ_L, hL1', hL2'⟩ := T7N.exists_noncomm_rep c hnc ρ₁
  have hL1 : ρ_L.K ≠ K := by rw [← hρ₁]; exact hL1'
  have hL2 : ρ_L.K ∉ omegaNbr Ω K := by rw [← hρ₁]; exact hL2'
  have hK'K : K' ∈ omegaNbr Ω K :=
    Q3CL.T3.twin_mem_omegaNbr hst.hyp hK hK'Ω h.std.hne hz hzK'
  have hLK' : ρ_L.K ≠ K' := fun e => hL2 (e ▸ hK'K)
  obtain ⟨z_L, hzL⟩ := hΩ.exists_uniqueInvolution ρ_L.hK
  obtain ⟨u₀, hu₀W, hu₀mem, hu₀sq, hu₀1, hu₀z, hRL, hRσ⟩ := T7N.exists_adapted_involution c
    ρ₁ ρ₂ ρ_L (hρ₁ ▸ hz) (hρ₂ ▸ hzK') hzL (by rw [hρ₁, hρ₂]; exact h.std.hne.symm)
    (by rw [hρ₁]; exact hL1) (by rw [hρ₂]; exact hLK') (by rw [hρ₁]; exact hL2)
  rw [hρ₁, hρ₂] at hu₀mem
  have hJK : J ∈ omegaNbr Ω K := h.hJ.2 K (mem_twinSet_self hK hz)
  have hJK' : J ∈ omegaNbr Ω K' := h.hJ.2 K' h.std.hK'
  have hRJ : ρ_J.R ≤ Subgroup.centralizer ({u₀} : Set G) :=
    hRσ ρ_J (by rw [hρ_J, hρ₁]; exact hJK) (by rw [hρ_J, hρ₂]; exact hJK')
  have hzW : z ∈ W :=
    (Q3CL.Thompson.uniqueInvolution_mem_W hΩ h.hW hK ρ₁.hR (hρ₁ ▸ ρ₁.hRK) hz).2
  have hzK1 : z ∈ ρ₁.K ⊓ W := ⟨hρ₁ ▸ hz.mem, hzW⟩
  have hρJ₁ : ρ₁.K ∈ omegaNbr Ω ρ_J.K := by
    rw [hρ_J, hρ₁]
    exact Q3CL.T3.omegaNbr_symm l6_2 hst.hyp hK hJΩ hJK
  have hRJz : ρ_J.R ≤ Subgroup.centralizer ({z} : Set G) :=
    T7N.R_le_centralizer_of_r_comm c ρ_J hzW (c.centralizes ρ_J ρ₁ hρJ₁ hzK1)
  have htu₀ : t * u₀ = u₀ * t := (Subgroup.mem_centralizer_singleton_iff.mp (hEt hu₀mem)).symm
  have h₀ : Q3T8.Asc77.Hyp21 Ω K K' z u₀ J t W := Hyp21.of_involution h hu₀mem hu₀sq hu₀1 hu₀z htu₀
  have hrLS : ρ_L.r ∉ sigmaNorm Ω K := Hyp21.r_not_mem_sigmaNorm h hne ρ₁ ρ_L hρ₁ hL1 hL2
  have hY₀ : ¬ ExactLayer.exactLayer Ω u₀ ≤ sigmaGen Ω K :=
    T7N.not_exactLayer_le_sigmaGen_of hΩ hK hu₀sq ρ_L.hR.1 hRL ρ_L.hr hrLS
  have hYD : ExactLayer.exactLayer Ω u₀ ≤ Subgroup.centralizer ({t * z} : Set G) :=
    Hyp21.exactLayer_le_of_Y_ne h hC3 hY hα hne h₀ hu₀W hY₀
  intro n hn
  have hnK : conjSub n K = K := mem_normalizer_iff_conjSub_eq.mp hn
  have hnz : n * z = z * n := commute_involution_of_conjSub_eq hz hnK
  have hnK' : conjSub n K' = K' := Hyp21.conjSub_twin_eq h hne hn
  set u₁ : G := n * u₀ * n⁻¹ with hu₁
  have hu₁mem : u₁ ∈ K ⊔ K' := by
    have h1 : u₁ ∈ conjSub n (K ⊔ K') := conj_mem_conjSub hu₀mem
    rwa [T7A.conjSub_sup_eq, hnK, hnK'] at h1
  have hu₁sq : u₁ * u₁ = 1 := by
    calc u₁ * u₁ = n * (u₀ * u₀) * n⁻¹ := by rw [hu₁]; group
      _ = 1 := by rw [hu₀sq]; group
  have hu₁1 : u₁ ≠ 1 := by
    intro h1
    apply hu₀1
    have : u₀ = n⁻¹ * u₁ * n := by rw [hu₁]; group
    rw [this, h1]
    group
  have hu₁z : u₁ ≠ z := by
    intro h1
    apply hu₀z
    have hnzc : n⁻¹ * z * n = z := by
      calc n⁻¹ * z * n = n⁻¹ * (z * n) := by group
        _ = n⁻¹ * (n * z) := by rw [hnz]
        _ = z := by group
    have : u₀ = n⁻¹ * u₁ * n := by rw [hu₁]; group
    rw [this, h1, hnzc]
  obtain ⟨x, hx, hxu⟩ := T7N.exists_conj_of_involution_twin hΩ hK hK'Ω h.std.hne hz hzK'
    hu₀mem hu₀1 hu₀z hu₀sq hu₁mem hu₁1 hu₁z hu₁sq
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp (hEt hx)
  set c' : G := x⁻¹ * n with hc'
  have hcN : c' ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).mul_mem
      ((Subgroup.normalizer (K : Set G)).inv_mem (hEN hx)) hn
  have hcK : conjSub c' K = K := mem_normalizer_iff_conjSub_eq.mp hcN
  have hcz : c' * z = z * c' := commute_involution_of_conjSub_eq hz hcK
  have hcK' : conjSub c' K' = K' := Hyp21.conjSub_twin_eq h hne hcN
  have hcu' : c' * u₀ * c'⁻¹ = u₀ := by
    calc c' * u₀ * c'⁻¹ = x⁻¹ * u₁ * x := by rw [hc', hu₁]; group
      _ = x⁻¹ * (x * u₀ * x⁻¹) * x := by rw [hxu]
      _ = u₀ := by group
  have hcu : c' * u₀ = u₀ * c' := by
    calc c' * u₀ = (c' * u₀ * c'⁻¹) * c' := by group
      _ = u₀ * c' := by rw [hcu']
  have hcC : c' ∈ Subgroup.centralizer ({u₀} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcu
  have hcY : conjSub c' (ExactLayer.exactLayer Ω u₀) = ExactLayer.exactLayer Ω u₀ :=
    ExactLayer.conjSub_exactLayer hΩ.conjInvariant hcC
  have hρJS : IsSylow2In ρ_J.R J := hρ_J ▸ ρ_J.hRK
  have hR₁set : conjSub c' ρ_J.R ∈ RSet Ω := RSet.conj hΩ.conjInvariant ρ_J.hR.1 c'
  have hR₁Y : conjSub c' ρ_J.R ≤ ExactLayer.exactLayer Ω u₀ := by
    have hRJY : ρ_J.R ≤ ExactLayer.exactLayer Ω u₀ :=
      T7N.le_exactLayer_of_sylow hΩ hu₀sq hJΩ hρJS hRJ
    have h2 := conjSub_mono (n := c') hRJY
    rwa [hcY] at h2
  have hR₁tz : conjSub c' ρ_J.R ≤ Subgroup.centralizer ({t * z} : Set G) := fun y hy =>
    hYD (hR₁Y hy)
  have hR₁z : conjSub c' ρ_J.R ≤ Subgroup.centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyz : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.mp (hRJz hy)
    show (c' * y * c'⁻¹) * z = z * (c' * y * c'⁻¹)
    calc c' * y * c'⁻¹ * z = c' * y * (c'⁻¹ * z) := by group
      _ = c' * y * (z * c'⁻¹) := by
          have : c'⁻¹ * z = z * c'⁻¹ := by
            calc c'⁻¹ * z = c'⁻¹ * z * c' * c'⁻¹ := by group
              _ = z * c'⁻¹ := by
                have : c'⁻¹ * z * c' = z := by
                  calc c'⁻¹ * z * c' = c'⁻¹ * (z * c') := by group
                    _ = c'⁻¹ * (c' * z) := by rw [hcz]
                    _ = z := by group
                rw [this]
          rw [this]
      _ = c' * (y * z) * c'⁻¹ := by group
      _ = c' * (z * y) * c'⁻¹ := by rw [hyz]
      _ = z * (c' * y * c'⁻¹) := by
          calc c' * (z * y) * c'⁻¹ = (c' * z) * y * c'⁻¹ := by group
            _ = (z * c') * y * c'⁻¹ := by rw [hcz]
            _ = z * (c' * y * c'⁻¹) := by group
  have hR₁t : conjSub c' ρ_J.R ≤ Subgroup.centralizer ({t} : Set G) :=
    le_centralizer_of_le_centralizer_mul hR₁tz fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hR₁z hy)
  have hJn : conjSub c' J ∈ Ω := hΩ.conjInvariant c' J hJΩ
  have hR₁Sylow : IsSylow2In (conjSub c' ρ_J.R) (conjSub c' J) := hρJS.conj c'
  have ht₁ : IsUniqueInvolution (conjSub c' J) (c' * t * c'⁻¹) := h.ht.conj c'
  have hR₁2 : IsPGroup 2 (conjSub c' ρ_J.R) := hR₁Sylow.2.1
  have h8 : 8 ≤ Nat.card (conjSub c' ρ_J.R) := hΩ.eight_le_of_mem_RSet hR₁set
  have hcz' : c'⁻¹ * z * c' = z := by
    calc c'⁻¹ * z * c' = c'⁻¹ * (z * c') := by group
      _ = c'⁻¹ * (c' * z) := by rw [hcz]
      _ = z := by group
  have hJnK : conjSub c' J ≠ K := by
    intro e
    have h1 : c' * t * c'⁻¹ = z := ht₁.eq (e ▸ hz)
    apply htz
    have h2 : t = c'⁻¹ * z * c' := by rw [← h1]; group
    rw [h2, hcz']
  have hR₁N : conjSub c' ρ_J.R ≤ Subgroup.normalizer (K : Set G) :=
    hΩ.le_normalizer_of_le_centralizer hK hJn (fun e => hJnK e.symm) hz hR₁Sylow.1 hR₁2
      (by omega) hR₁z
  have htt : c' * t * c'⁻¹ = t := by
    by_cases hJnK' : conjSub c' J = K'
    · exfalso
      have h1 : c' * t * c'⁻¹ = z := ht₁.eq (hJnK' ▸ hzK')
      apply htz
      have h2 : t = c'⁻¹ * z * c' := by rw [← h1]; group
      rw [h2, hcz']
    · by_cases hJnJ : conjSub c' J = J
      · exact (h.ht.eq (hJnJ ▸ ht₁)).symm
      · exact Hyp21.involution_eq_of_sylow h hne hKt hK't hJn hR₁set hR₁Sylow.1 hR₁N hR₁t ht₁
          hJnK hJnK' hJnJ
  have hnt : n * t * n⁻¹ = t := by
    have hn' : n = x * c' := by rw [hc']; group
    rw [hn']
    calc x * c' * t * (x * c')⁻¹ = x * (c' * t * c'⁻¹) * x⁻¹ := by group
      _ = x * t * x⁻¹ := by rw [htt]
      _ = t := by rw [hxt]; group
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * (t * z) = (n * t * n⁻¹) * (n * z) := by group
    _ = t * (z * n) := by rw [hnt, hnz]
    _ = (t * z) * n := by group

end Asc77
end

end CFSG.ClassicalInvolution.Q3.Q3T8

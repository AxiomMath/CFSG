module

public import CFSG.ClassicalInvolution.Asc77.AscT7RF
import CFSG.ClassicalInvolution.Asc77.AscT8Layer
import CFSG.ClassicalInvolution.Asc77.AscIHSectMA
public import CFSG.ClassicalInvolution.Asc77.AscT7BAlpha
public import CFSG.ClassicalInvolution.Asc77.AscT7FF
public import CFSG.ClassicalInvolution.Asc77.AscT7RA
public import CFSG.ClassicalInvolution.Asc77.AscT7RC
public import CFSG.ClassicalInvolution.RouteD.G2D4G2NonToralFive

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
  T7R

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.alpha_u_tz (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f) :
    alphaOf (Subgroup.closure ({u, t * z} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hfr := h.twinFrameData
  have hzt : z * t = t * z := hfr.comm_zt hp hΩ
  have hne : u ≠ t * z := by
    intro h1
    apply hfr.t_not_mem_closure hp hq hΩ
    have hz' : z ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
    have hu' : u ∈ Subgroup.closure ({z, u} : Set G) := Subgroup.subset_closure (by simp)
    have : t = u * z := by
      calc t = (t * z) * z := by rw [mul_assoc, h.std.hz.sq, mul_one]
        _ = u * z := by rw [← h1]
    rw [this]
    exact Subgroup.mul_mem _ hu' hz'
  have hcomm : u * (t * z) = (t * z) * u := by
    calc u * (t * z) = (u * t) * z := by group
      _ = (t * u) * z := by rw [← h.htu]
      _ = t * (u * z) := by group
      _ = t * (z * u) := by rw [h.u_comm_z]
      _ = (t * z) * u := by group
  have hA : IsElemAbelian2 (Subgroup.closure ({u, t * z} : Set G)) 2 :=
    T7A.isElemAbelian2_closure_pair h.hu2 h.tz_sq h.hu1 h.tz_ne_one hne hcomm
  have hle : Subgroup.closure ({u, t * z} : Set G) ≤ Subgroup.closure ({z, u, t} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  exact (hC3 G Ω K K' z u J t W h).2 _ hle hA

theorem Hyp21.rLayer_u_le_normalizer_alpha_of_trivial (h : Hyp21 p f Ω K K' z u J t W)
    (hC3 : C21_3 p f) {c₀ : G} (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ rLayer Ω u, c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) :
    rLayer Ω u ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hzt : z * t = t * z := h.twinFrameData.comm_zt hp hΩ
  have hc₀2 : c₀ * c₀ = 1 := by
    rcases hc₀ with rfl | rfl
    · exact h.std.hz.sq
    · exact h.tz_sq
  have hc₀u : c₀ * u = u * c₀ := by
    rcases hc₀ with rfl | rfl
    · exact h.u_comm_z.symm
    · calc (t * z) * u = t * (z * u) := by group
        _ = t * (u * z) := by rw [h.u_comm_z.symm]
        _ = (t * u) * z := by group
        _ = (u * t) * z := by rw [h.htu]
        _ = u * (t * z) := by group
  have hα : alphaOf (Subgroup.closure ({u, c₀} : Set G)) =
      alphaOf (Subgroup.closure ({u, z} : Set G)) := by
    rcases hc₀ with rfl | rfl
    · rfl
    · exact h.alpha_u_tz hC3
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (rLayer Ω u) = rLayer Ω u :=
    T8.rLayer_conjSub_eq hΩ.conjInvariant hcC
  have hOY : oddCoreOf (rLayer Ω u) ≤ Subgroup.normalizer
      (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
    have h1 := oddCoreOf_sectionHull_le hΩ (Subgroup.zpowers u)
    rw [← rLayer_eq_sectionHull hp hq hΩ h.hu2,
      CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton'] at h1
    exact h1.trans (oddCoreOf_centralizer_le_normalizer_alphaOf h.std.hz.sq h.hu1 h.u_comm_z)
  refine iSup₂_le fun R hR => iSup_le fun hRC => ?_
  obtain ⟨J₁, -, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR (le_iSup_of_le hRC le_rfl)
  obtain ⟨n, hn, hnR⟩ := exists_conj_le_centralizer_of_comm_mem_oddCore hc₀2 hcY hRJ₁.2.1 hRY
    htriv
  have hnN := hOY hn
  have hnC : n ∈ Subgroup.centralizer ({u} : Set G) := by
    have h1 := oddCoreOf_sectionHull_le hΩ (Subgroup.zpowers u)
    rw [← rLayer_eq_sectionHull hp hq hΩ h.hu2,
      CFSG.ClassicalInvolution.Balance.Bootstrap.centralizer_zpowers_eq_singleton'] at h1
    exact oddCoreOf_le_self _ (h1 hn)
  intro r hr
  have hrC : r ∈ Subgroup.centralizer ({u} : Set G) := hRC hr
  have hxr : n * r * n⁻¹ ∈ conjSub n R := conj_mem_conjSub hr
  have hx1 : n * r * n⁻¹ ∈ Subgroup.centralizer ({c₀} : Set G) := hnR hxr
  have hx2 : n * r * n⁻¹ ∈ Subgroup.centralizer ({u} : Set G) :=
    (Subgroup.centralizer ({u} : Set G)).mul_mem
      ((Subgroup.centralizer ({u} : Set G)).mul_mem hnC hrC)
      ((Subgroup.centralizer ({u} : Set G)).inv_mem hnC)
  have hle : Subgroup.closure ({u, c₀} : Set G) ≤
      Subgroup.centralizer ({n * r * n⁻¹} : Set G) := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
        hx2).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp
        hx1).symm
  have hxA : n * r * n⁻¹ ∈ Subgroup.centralizer
      ((Subgroup.closure ({u, c₀} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hxN := T7B.centralizer_le_normalizer_alphaOf _ hxA
  rw [hα] at hxN
  have e : r = n⁻¹ * (n * r * n⁻¹) * n := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN) hxN) hnN

theorem Hyp21.normalizer_le_normalizer_alpha_of_mem_dComp (h : Hyp21 p f Ω K K' z u J t W)
    (hs : AlphaSteps p f) {J₀ : Subgroup G} (hJ₀ : J₀ ∈ dComp Ω K) :
    Subgroup.normalizer (J₀ : Set G) ≤
      Subgroup.normalizer (alphaOf (Subgroup.closure ({u, z} : Set G)) : Set G) := by
  obtain ⟨x₀, hx₀N, hx₀⟩ := hs.exists_mem_normalizer h hJ₀
  intro m hm
  have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
      mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
  have h2 := h.normalizer_le_normalizer_alpha hs hmK
  have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hx₀N h2) (Subgroup.inv_mem _ hx₀N)

end Frame

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C21_14_Y_disc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K K' : Subgroup G)
    (z u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Hyp21 p f Ω K K' z u J t W →
      ¬ SectionConnected Ω u →
        rLayer Ω u ≤ Subgroup.normalizer (alphaOf (Subgroup.closure {u, z}) : Set G) ∧
          (alphaOf (Subgroup.closure {u, z}) = ⊥ →
            rLayer Ω u ≤ sigmaGen Ω K ∨ rLayer Ω u ≤ rLayer Ω (t * z))

variable {p f}

theorem c21_14_Y_disc_of_c21_14 (h14 : C21_14 p f) : C21_14_Y_disc p f := by
  intro G _ _ _ Ω K K' z u J t W h _
  obtain ⟨hN, hY⟩ := h14 G Ω K K' z u J t W h
  refine ⟨(rLayer_le_centralizer Ω u).trans hN, fun hα => ?_⟩
  rcases hY with h1 | ⟨h2, -, -⟩
  · rw [hα, bot_sup_eq] at h1
    exact Or.inl h1
  · rw [hα, bot_sup_eq] at h2
    exact Or.inr h2

theorem c21_14_N_disc_of_Ydisc (hC3 : C21_3 p f) (hY : C21_14_Y_disc p f) :
    C21_14_N_disc p f := by
  intro G _ _ _ Ω K K' z u J t W h hconn
  have hs : AlphaSteps p f := ⟨hC3, twinNormAlpha_of p f hC3⟩
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
    G2D4Models.h3s_of_nonToral_free G2D4Models.g2NonToralGenerate_all
  exact h.centralizer_u_le_of_disc h3s hconn (hY G Ω K K' z u J t W h hconn).1 fun _ hJ₀ =>
    h.normalizer_le_normalizer_alpha_of_mem_dComp hs hJ₀

end CFSG.ClassicalInvolution.Asc77

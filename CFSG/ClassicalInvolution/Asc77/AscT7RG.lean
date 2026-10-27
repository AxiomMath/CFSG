module

public import CFSG.ClassicalInvolution.Asc77.AscT7RE
import CFSG.ClassicalInvolution.Asc77.AscT8Layer
public import CFSG.ClassicalInvolution.Asc77.AscT7RD

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic AscE184Sect ExactLayer
  T7R

section Frame

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {p f : ℕ} [Fact p.Prime]
  {Ω : Set (Subgroup G)} {K K' J W : Subgroup G} {z u t : G}

theorem Hyp21.oddCore_centralizer_u_comm_tz (h : Hyp21 p f Ω K K' z u J t W) (hC3 : C21_3 p f)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {n : G}
    (hn : n ∈ oddCoreOf (Subgroup.centralizer ({u} : Set G))) : n * (t * z) = (t * z) * n := by
  have hA : alphaOf (Subgroup.closure ({u, t * z} : Set G)) = ⊥ := by
    rw [h.alpha_u_tz hC3]
    exact hα
  have huA : u ∈ Subgroup.closure ({u, t * z} : Set G) := Subgroup.subset_closure (by simp)
  have htzA : t * z ∈ Subgroup.closure ({u, t * z} : Set G) := Subgroup.subset_closure (by simp)
  exact T8.oddCoreOf_centralizer_commutes hA huA h.hu1 htzA n hn

theorem Hyp21.conjSub_mem_dComp_of_comm (h : Hyp21 p f Ω K K' z u J t W) {g : G}
    (hg : g * z = z * g) : conjSub g K ∈ dComp Ω K := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  have hz : IsUniqueInvolution K z := h.std.hz
  have hgz : g * z * g⁻¹ = z := by
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [hg]
      _ = z := by group
  have hzg : IsUniqueInvolution (conjSub g K) z := by
    have := hz.conj g
    rwa [hgz] at this
  exact T7A.mem_dComp_of_mem_kPerp (mem_kPerp_of_twin hΩ (hΩ.conjInvariant g K hK) hK hzg hz)

theorem Hyp21.rSet_le_sigmaGen_of_le_centralizer (h : Hyp21 p f Ω K K' z u J t W) {R : Subgroup G}
    (hR : R ∈ RSet Ω) (hRz : R ≤ Subgroup.centralizer ({z} : Set G)) : R ≤ sigmaGen Ω K := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hq : 5 ≤ p ^ f := h.std.stand.five
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  obtain ⟨M₁, hM₁Ω, hRM₁⟩ := exists_isSylow2In_of_mem_RSet hR
  have hMd : M₁ ∈ dComp Ω K := by
    by_cases hM₁K : M₁ = K
    · rw [hM₁K]
      exact Relation.ReflTransGen.refl
    · have h8 := hΩ.eight_le_of_mem_RSet hp hR
      have hRN : R ≤ Subgroup.normalizer (K : Set G) :=
        hΩ.le_normalizer_of_le_centralizer hp hq hK hM₁Ω (Ne.symm hM₁K) h.std.hz hRM₁.1
          hRM₁.2.1 (by omega) hRz
      exact T7A.mem_dComp_of_mem_omegaNbr ⟨hM₁Ω, hM₁K, R, hR, hRM₁.1, hRN⟩
  exact hRM₁.1.trans (le_iSup₂_of_le M₁ hMd le_rfl)

theorem Hyp21.c₀_facts (h : Hyp21 p f Ω K K' z u J t W) {c₀ : G} (hc₀ : c₀ = z ∨ c₀ = t * z) :
    c₀ * c₀ = 1 ∧ c₀ * u = u * c₀ := by
  constructor
  · rcases hc₀ with rfl | rfl
    · exact h.std.hz.sq
    · exact h.tz_sq
  · rcases hc₀ with rfl | rfl
    · exact h.u_comm_z.symm
    · calc (t * z) * u = t * (z * u) := by group
        _ = t * (u * z) := by rw [h.u_comm_z.symm]
        _ = (t * u) * z := by group
        _ = (u * t) * z := by rw [h.htu]
        _ = u * (t * z) := by group

theorem Hyp21.rLayer_u_le_sigmaGen_of_trivial (h : Hyp21 p f Ω K K' z u J t W)
    (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥) {c₀ : G} (hc₀ : c₀ = z ∨ c₀ = t * z)
    (htriv : ∀ y ∈ rLayer Ω u, c₀ * y * c₀⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u))
    (hR : ∀ R ∈ RSet Ω, R ≤ Subgroup.centralizer ({c₀} : Set G) → R ≤ sigmaGen Ω K) :
    rLayer Ω u ≤ sigmaGen Ω K := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  have hK : K ∈ Ω := h.std.stand.mem
  obtain ⟨hc₀2, hc₀u⟩ := h.c₀_facts hc₀
  have hcC : c₀ ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub c₀ (rLayer Ω u) = rLayer Ω u :=
    T8.rLayer_conjSub_eq hΩ.conjInvariant hcC
  refine iSup₂_le fun R hR' => iSup_le fun hRC => ?_
  obtain ⟨J₁, -, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR' (le_iSup_of_le hRC le_rfl)
  obtain ⟨n, hn, hnR⟩ := exists_conj_le_centralizer_of_comm_mem_oddCore hc₀2 hcY hRJ₁.2.1 hRY
    htriv
  have hnz : n * z = z * n := h.oddCore_centralizer_u_comm hα (h.oddCore_rLayer_u_le hn)
  have hnz' : n⁻¹ * z = z * n⁻¹ := by
    have h1 := congrArg (fun y => n⁻¹ * y * n⁻¹) hnz
    simpa [mul_assoc] using h1.symm
  have hg : conjSub n⁻¹ K ∈ dComp Ω K := h.conjSub_mem_dComp_of_comm hnz'
  have hg' : conjSub n⁻¹⁻¹ K ∈ dComp Ω K := by
    rw [inv_inv]
    exact h.conjSub_mem_dComp_of_comm hnz
  have hσ := T7A.conjSub_sigmaGen_eq hΩ.conjInvariant hK hg hg'
  have h1 : conjSub n R ≤ sigmaGen Ω K := hR _ (RSet.conj hΩ.conjInvariant hR' n) hnR
  have h2 := conjSub_mono (n := n⁻¹) h1
  rw [conjSub_inv_conjSub, hσ] at h2
  exact h2

theorem Hyp21.rLayer_u_le_centralizer_tz_of_trivial (h : Hyp21 p f Ω K K' z u J t W)
    (hC3 : C21_3 p f) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (htriv : ∀ y ∈ rLayer Ω u, (t * z) * y * (t * z)⁻¹ * y⁻¹ ∈ oddCoreOf (rLayer Ω u)) :
    rLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  obtain ⟨hc₀2, hc₀u⟩ := h.c₀_facts (c₀ := t * z) (Or.inr rfl)
  have hcC : t * z ∈ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc₀u
  have hcY : conjSub (t * z) (rLayer Ω u) = rLayer Ω u :=
    T8.rLayer_conjSub_eq hΩ.conjInvariant hcC
  refine iSup₂_le fun R hR' => iSup_le fun hRC => ?_
  obtain ⟨J₁, -, hRJ₁⟩ := exists_isSylow2In_of_mem_RSet hR'
  have hRY : R ≤ rLayer Ω u := le_iSup₂_of_le R hR' (le_iSup_of_le hRC le_rfl)
  obtain ⟨n, hn, hnR⟩ := exists_conj_le_centralizer_of_comm_mem_oddCore hc₀2 hcY hRJ₁.2.1 hRY
    htriv
  have hnc : n ∈ Subgroup.centralizer ({t * z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (h.oddCore_centralizer_u_comm_tz hC3 hα (h.oddCore_rLayer_u_le hn))
  intro r hr
  have hxr : n * r * n⁻¹ ∈ conjSub n R := conj_mem_conjSub hr
  have hx := hnR hxr
  have e : r = n⁻¹ * (n * r * n⁻¹) * n := by group
  rw [e]
  exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set G)).mul_mem
      ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hnc) hx) hnc

theorem Hyp21.exists_mem_centralizer_tz_conj (h : Hyp21 p f Ω K K' z u J t W)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G)) :
    ∀ L ∈ dstarComp Ω K, ∃ x ∈ Subgroup.centralizer ({t * z} : Set G), conjSub x K = L :=
  h.exists_mem_conj_of_dstarComp hne
    ((h.mGrp_le_rLayer_tz hne).trans (rLayer_le_centralizer Ω (t * z))) hN

theorem Hyp21.centralizer_u_le_centralizer_tz_of_conn (h : Hyp21 p f Ω K K' z u J t W)
    (hC3 : C21_3 p f) (hα : alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G))
    (hconn : SectionConnected Ω u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) :=
  h.centralizer_u_le_of_conn hconn
    (fun _ hn => Subgroup.mem_centralizer_singleton_iff.mpr
      (h.oddCore_centralizer_u_comm_tz hC3 hα hn)) hN (h.exists_mem_centralizer_tz_conj hne hN)

theorem Hyp21.centralizer_u_le_centralizer_tz_of_disc (h : Hyp21 p f Ω K K' z u J t W)
    (h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n)
    (hne : dComp Ω K ≠ dstarComp Ω K)
    (hN : Subgroup.normalizer (K : Set G) ≤ Subgroup.centralizer ({t * z} : Set G))
    (hconn : ¬ SectionConnected Ω u) (hY : rLayer Ω u ≤ Subgroup.centralizer ({t * z} : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t * z} : Set G) := by
  have hp : p ≠ 2 := h.std.stand.odd
  have hΩ : HypOmegaMod p f Ω := h.std.stand.hyp
  refine h.centralizer_u_le_of_disc h3s hconn hY fun J₀ hJ₀ m hm => ?_
  obtain ⟨x₀, hx₀H, hx₀⟩ := h.exists_mem_centralizer_tz_conj hne hN J₀
    (T7A.mem_dstarComp_of_mem_dComp hp hΩ hJ₀)
  have hmK : x₀⁻¹ * m * x₀ ∈ Subgroup.normalizer (K : Set G) := by
    rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, conjSub_mul, hx₀,
      mem_normalizer_iff_conjSub_eq.mp hm, ← hx₀, conjSub_inv_conjSub]
  have e : m = x₀ * (x₀⁻¹ * m * x₀) * x₀⁻¹ := by group
  rw [e]
  exact (Subgroup.centralizer ({t * z} : Set G)).mul_mem
    ((Subgroup.centralizer ({t * z} : Set G)).mul_mem hx₀H (hN hmK))
    ((Subgroup.centralizer ({t * z} : Set G)).inv_mem hx₀H)

end Frame

variable {p f : ℕ} [Fact p.Prime]

theorem c21_14_alt_rest_of (hC3 : C21_3 p f) (hY : C21_14_Y_disc p f) (hN : C21_NormCent p f) :
    C21_14_alt_rest p f := by
  intro G _ _ _ Ω K K' z u J t W h hα hnot
  have h3s : ∀ n, CITBelowU p f n → T3.Thm3SectBelow p f n :=
    G2D4Models.h3s_of_nonToral_free G2D4Models.g2NonToralGenerate_all
  by_cases hconn : SectionConnected Ω u
  · have hne : dComp Ω K ≠ dstarComp Ω K := fun heq => hnot ⟨heq, hconn⟩
    exact Or.inr (h.centralizer_u_le_centralizer_tz_of_conn hC3 hα hne
      (hN G Ω K K' z u J t W h hα (h.not_rLayer_le_sigmaGen hne)) hconn)
  · rcases (hY G Ω K K' z u J t W h hconn).2 hα with hSig | hD
    · exact Or.inl hSig
    · by_cases heq : dComp Ω K = dstarComp Ω K
      · exact Or.inl (hD.trans (h.rLayer_tz_le_sigmaGen_of_eq hC3 hα heq))
      · exact Or.inr (h.centralizer_u_le_centralizer_tz_of_disc h3s heq
          (hN G Ω K K' z u J t W h hα (h.not_rLayer_le_sigmaGen heq)) hconn
          (hD.trans (rLayer_le_centralizer Ω (t * z))))

end CFSG.ClassicalInvolution.Asc77

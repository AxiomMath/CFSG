module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6h2Align

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S CFSG.Open CFSG.ClassicalInvolution.Generic

variable {Y : Type} [Group Y] {K M L L₂ L₃ : Subgroup Y} {V : Fin 3 → Subgroup Y}

structure AlignedFam (K : Subgroup Y) (V : Fin 3 → Subgroup Y) (ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k)) :
    Prop where
  carries : ∀ k, Carries (ψ k) (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK)
  edge : ∀ k l, l ≠ k → ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((ψ k g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l

section EdgeMembers

variable {k l : Fin 3} {ψ : ↥(V k) ≃* ↥(ae6ModelV k)}

theorem le_edge_of_corr (hS : AE6Shape K M L L₂ L₃ V)
    (he : ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((ψ g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l)
    {J : Subgroup Y} {J' : Subgroup AE6Om} (hJ : J ∈ ae6ConjIn (V k) K) (hc : Corr ψ J J')
    (hJ' : J' ≤ ae6ModelE k l) : J ≤ V k ⊓ V l := by
  intro z hz
  have hzk : z ∈ V k := shape_le_of_mem hS hJ hz
  refine ⟨hzk, ?_⟩
  exact (he ⟨z, hzk⟩).2 (hJ' ((hc ⟨z, hzk⟩).1 hz)).2

theorem edge_corr₂ (hS : AE6Shape K M L L₂ L₃ V) (hkl : k ≠ l)
    (hc : Carries ψ (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK))
    (he : ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((ψ g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l) :
    ∀ J' ∈ ae6ConjIn (ae6ModelE k l) ae6ModelK, ∃ J ∈ ae6ConjIn (V k ⊓ V l) K, Corr ψ J J' := by
  rintro _ ⟨e', he', rfl⟩
  have hJ'V : conjSub e' ae6ModelK ∈ ae6ConjIn (ae6ModelV k) ae6ModelK := ⟨e', he'.1, rfl⟩
  have hJ'E : conjSub e' ae6ModelK ≤ ae6ModelE k l := conjSub_le_of_mem he' (ae6ModelK_le_E k l)
  obtain ⟨J, hJ, hcJ⟩ := hc.2 _ hJ'V
  refine ⟨J, ?_, hcJ⟩
  rw [← shape_members hS hkl]
  exact ⟨hJ, le_edge_of_corr hS he hJ hcJ hJ'E⟩

theorem edge_corr₁ (hS : AE6Shape K M L L₂ L₃ V) (hkl : k ≠ l)
    (hc : Carries ψ (ae6ConjIn (V k) K) (ae6ConjIn (ae6ModelV k) ae6ModelK))
    (he : ∀ g : ↥(V k), (g : Y) ∈ V l ↔ ((ψ g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelV l) :
    ∀ J ∈ ae6ConjIn (V k ⊓ V l) K, ∃ J' ∈ ae6ConjIn (ae6ModelE k l) ae6ModelK, Corr ψ J J' := by
  rintro _ ⟨e, he_mem, rfl⟩
  have hJ : conjSub e K ∈ {J | J ∈ ae6ConjIn (V k) K ∧ J ≤ V k ⊓ V l} := by
    rw [shape_members hS hkl]
    exact ⟨e, he_mem, rfl⟩
  obtain ⟨J', hJ'M, hcJ'⟩ := hc.1 _ hJ.1
  have hK₀ : ae6ModelK ∈ ae6ConjIn (ae6ModelV k) ae6ModelK := ⟨1, one_mem _, conjSub_one _⟩
  obtain ⟨J₀, hJ₀, hcJ₀⟩ := hc.2 _ hK₀
  have hJ₀E : J₀ ∈ ae6ConjIn (V k ⊓ V l) K := by
    rw [← shape_members hS hkl]
    exact ⟨hJ₀, le_edge_of_corr hS he hJ₀ hcJ₀ (ae6ModelK_le_E k l)⟩
  obtain ⟨e₀, he₀, rfl⟩ := hJ₀E
  have hx : e * e₀⁻¹ ∈ V k ⊓ V l := mul_mem he_mem (inv_mem he₀)
  have hconj : conjSub e K = conjSub (e * e₀⁻¹) (conjSub e₀ K) := by
    rw [← conjSub_mul, inv_mul_cancel_right]
  have hc₂ := Corr.conj hcJ₀ (⟨e * e₀⁻¹, hx.1⟩ : ↥(V k))
  rw [← hconj] at hc₂
  have heq : J' = conjSub ((ψ ⟨e * e₀⁻¹, hx.1⟩ : ↥(ae6ModelV k)) : AE6Om) ae6ModelK :=
    Corr.unique hcJ' hc₂ (le_of_mem_conjIn_model hJ'M)
      (conjSub_le_of_mem (ψ ⟨e * e₀⁻¹, hx.1⟩).2 (ae6ModelK_le k))
  refine ⟨J', ?_, hcJ'⟩
  rw [heq]
  exact ⟨_, ⟨(ψ ⟨e * e₀⁻¹, hx.1⟩).2, (he ⟨e * e₀⁻¹, hx.1⟩).1 hx.2⟩, rfl⟩

end EdgeMembers

section MemM

variable {ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k)}

theorem AlignedFam.mem_M (hS : AE6Shape K M L L₂ L₃ V) (al : AlignedFam K V ψ) (k : Fin 3)
    (g : ↥(V k)) : (g : Y) ∈ M ↔ ((ψ k g : ↥(ae6ModelV k)) : AE6Om) ∈ ae6ModelM := by
  rw [shape_mem_M hS, mem_ae6ModelM_iff]
  refine forall_congr' fun i => ?_
  by_cases hi : i = k
  · subst hi
    exact ⟨fun _ => (ψ i g).2, fun _ => g.2⟩
  · exact al.edge k i hi g

end MemM

section Theta

variable {ψ : ∀ k, ↥(V k) ≃* ↥(ae6ModelV k)}

@[expose] noncomputable def theta (al : AlignedFam K V ψ) {k l : Fin 3} (hkl : k ≠ l) :
    MulAut ↥(ae6ModelE k l) :=
  edgeAut (ψ k) (ψ l) (al.edge k l hkl.symm) (al.edge l k hkl)

theorem theta_val (al : AlignedFam K V ψ) {k l : Fin 3} (hkl : k ≠ l) (x : ↥(V k)) (hx : (x : Y) ∈ V l)
    (g : ↥(ae6ModelE k l)) (hg : (g : AE6Om) = ((ψ k x : ↥(ae6ModelV k)) : AE6Om)) :
    ((theta al hkl g : ↥(ae6ModelE k l)) : AE6Om) = ((ψ l ⟨x, hx⟩ : ↥(ae6ModelV l)) : AE6Om) :=
  edgeAut_val (ψ k) (ψ l) (al.edge k l hkl.symm) (al.edge l k hkl) x hx g hg

theorem exists_pre (al : AlignedFam K V ψ) {k l : Fin 3} (hkl : k ≠ l) (g : ↥(ae6ModelE k l)) :
    ∃ (x : ↥(V k)) (hx : (x : Y) ∈ V l), (g : AE6Om) = ((ψ k x : ↥(ae6ModelV k)) : AE6Om) := by
  have hgk : (g : AE6Om) ∈ ae6ModelV k := g.2.1
  have hgl : (g : AE6Om) ∈ ae6ModelV l := g.2.2
  have hψ : ((ψ k ((ψ k).symm ⟨g, hgk⟩) : ↥(ae6ModelV k)) : AE6Om) = g := by
    rw [MulEquiv.apply_symm_apply]
  refine ⟨(ψ k).symm ⟨g, hgk⟩, (al.edge k l hkl.symm _).2 ?_, hψ.symm⟩
  rw [hψ]
  exact hgl

theorem theta_aut (hS : AE6Shape K M L L₂ L₃ V) (al : AlignedFam K V ψ) {k l : Fin 3} (hkl : k ≠ l) :
    AE6EdgeAut k l (theta al hkl) := by
  constructor
  · intro g
    obtain ⟨x, hx, hg⟩ := exists_pre al hkl g
    rw [theta_val al hkl x hx g hg, hg, ← al.mem_M hS k x, al.mem_M hS l ⟨x, hx⟩]
  · intro J hJ
    obtain ⟨J₁, hJ₁, hc₁⟩ := edge_corr₂ hS hkl (al.carries k) (al.edge k l hkl.symm) J hJ
    have hJ₁' : J₁ ∈ ae6ConjIn (V l ⊓ V k) K := by rw [inf_comm]; exact hJ₁
    obtain ⟨J', hJ', hc₂⟩ := edge_corr₁ hS hkl.symm (al.carries l) (al.edge l k hkl) J₁ hJ₁'
    refine ⟨J', ?_, fun g => ?_⟩
    · have : ae6ModelE l k = ae6ModelE k l := inf_comm _ _
      rwa [this] at hJ'
    · obtain ⟨x, hx, hg⟩ := exists_pre al hkl g
      rw [theta_val al hkl x hx g hg, hg]
      exact (hc₁ x).symm.trans (hc₂ ⟨x, hx⟩)

theorem theta_compat (al : AlignedFam K V ψ) :
    ∀ (g₁ : ↥(ae6ModelE 0 1)) (g₂ : ↥(ae6ModelE 0 2)) (g₃ : ↥(ae6ModelE 1 2)),
      (g₁ : AE6Om) ∈ ae6ModelM → (g₂ : AE6Om) = g₁ → (g₃ : AE6Om) = theta al (k := 0) (l := 1) (by decide) g₁ →
        ((theta al (k := 0) (l := 2) (by decide) g₂ : ↥(ae6ModelE 0 2)) : AE6Om) =
          ((theta al (k := 1) (l := 2) (by decide) g₃ : ↥(ae6ModelE 1 2)) : AE6Om) := by
  intro g₁ g₂ g₃ hM h₂ h₃
  obtain ⟨x, hx1, hg₁⟩ := exists_pre al (k := 0) (l := 1) (by decide) g₁
  have hx2 : (x : Y) ∈ V 2 := (al.edge 0 2 (by decide) x).2 (mem_ae6ModelM_iff.1 (hg₁ ▸ hM) 2)
  have e1 := theta_val al (k := 0) (l := 1) (by decide) x hx1 g₁ hg₁
  have e2 := theta_val al (k := 0) (l := 2) (by decide) x hx2 g₂ (h₂.trans hg₁)
  have e3 := theta_val al (k := 1) (l := 2) (by decide) ⟨x, hx1⟩ hx2 g₃ (h₃.trans e1)
  rw [e2, e3]

end Theta

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6h2

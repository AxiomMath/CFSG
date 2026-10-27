module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Derived

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12

open Subgroup CFSG.GH74.GLS.Stage1.Thm6

variable {G : Type*} [Group G] [Finite G] {x : G} {S T P Q Rd F : Subgroup G}

theorem omega1_T_le_Rd (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd) :
    omega1 T ≤ Rd := by
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨huT, hu2⟩
  by_contra hu
  obtain ⟨E, hEC, hE, hcard⟩ := hout u huT hu2 hu
  have := h.rank_le E hEC hE
  rw [hcard] at this
  norm_num at this

theorem involution_mem_Rd (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd) {u : G}
    (huT : u ∈ T) (hu2 : u * u = 1) : u ∈ Rd :=
  omega1_T_le_Rd h hout (Subgroup.subset_closure ⟨huT, hu2⟩)

theorem omega1_phi_cent_le (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) {V : Subgroup G} (hVP : V ≤ P) (hV : IsFour V) :
    omega1 (phi2 (centIn T (V ⊔ Subgroup.zpowers x))) ≤ Subgroup.zpowers x := by
  obtain ⟨W, hWT, hWRd, hVW, hdec⟩ := hcf V hVP hV
  have hphi : phi2 (centIn T (V ⊔ Subgroup.zpowers x)) ≤ W := by
    refine (Subgroup.closure_le _).2 ?_
    rintro s ⟨d, hd, rfl⟩
    have hdT : d ∈ T := (Subgroup.mem_inf.1 hd).1
    have hdC : d ∈ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
      (Subgroup.mem_inf.1 hd).2
    have hdc : ∀ v ∈ V, d * v = v * d := by
      intro v hv
      have hvmem : v ∈ ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) :=
        Subgroup.mem_sup_left hv
      exact (Subgroup.mem_centralizer_iff.1 hdC v hvmem).symm
    obtain ⟨v, hv, w, hw, rfl⟩ := hdec d hdT hdc
    have hv2 : v * v = 1 := (hV.1 v hv).1
    have e : v * w * (v * w) = (v * w * v⁻¹) * w := by
      have : v * w * (v * w) = (v * w * v⁻¹) * (v * v) * w := by group
      rw [this, hv2, mul_one]
    show v * w * (v * w) ∈ W
    rw [e]
    exact W.mul_mem (hVW v hv w hw) hw
  refine (Subgroup.closure_le _).2 ?_
  rintro u ⟨huphi, hu2⟩
  have huW : u ∈ W := hphi huphi
  have huT : u ∈ T := hWT huW
  have huRd : u ∈ Rd := involution_mem_Rd h hout huT hu2
  have huQ : u ∈ Q := by rw [← hWRd]; exact ⟨huW, huRd⟩
  rcases h.Q_invol ⟨V, hVP, hV⟩ huQ hu2 with h1 | h1
  · rw [h1]; exact Subgroup.one_mem _
  · rw [h1]; exact Subgroup.mem_zpowers x

theorem lemma_12_2 (h : HBase G x S T P Q Rd F) (hout : IP_outer x T Rd)
    (hcf : IP_cent_four T P Q Rd) :
    omega1 T ≤ Rd ∧ ∀ V : Subgroup G, V ≤ P → IsFour V →
      omega1 (phi2 (centIn T (V ⊔ Subgroup.zpowers x))) ≤ Subgroup.zpowers x :=
  ⟨omega1_T_le_Rd h hout, fun _ hVP hV => omega1_phi_cent_le h hout hcf hVP hV⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec12


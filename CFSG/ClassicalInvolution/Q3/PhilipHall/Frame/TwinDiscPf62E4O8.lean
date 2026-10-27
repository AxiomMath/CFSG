module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8D
public import Certificates.Certificate393005
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4CheckB

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TL4

namespace TwinDisc

namespace ExitE4

theorem ambientQuatDatum_map_of_twins {M G : Type} [Group M] [Group G] (φ : M →* G)
    (hφ : Function.Injective φ) {K : Subgroup M} {s : M}
    (hq : Nonempty (↥K ≃* QuaternionGroup 2)) (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M),
      conjSub c K = K ∨ ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) :
    Vtx.AmbientQuatDatum φ.range (K.map φ) (φ s) := by
  obtain ⟨eK⟩ := hq
  refine ⟨Subgroup.map_le_range _ K, ⟨(K.equivMapOfInjective _ hφ).symm.trans eK⟩,
    Vtx.isUniqueInvolution_map _ hφ hinv, ?_⟩
  rintro _ ⟨m, rfl⟩ hms
  have hm : m ∈ Subgroup.centralizer ({s} : Set M) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hφ (by rw [map_mul, map_mul, hms])
  rw [conjSub_map]
  rcases htw m hm with h | h
  · left
    rw [h]
  · right
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

section Twins

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEight

theorem wsA_getD (k : ℕ) :
    (E4O8.wsA ()).getD k (idA 360) = omegaW ((E4O8.wsW ()).getD k []) := by
  rw [E4O8.wsA, ← show omegaW [] = idA 360 from rfl, List.getD_map]

theorem twin3_facts :
    conjSub (E4O8.wsP.getD 3 1) E4O8.K0 ≠ E4O8.K0 ∧
      conjSub (E4O8.wsP.getD 3 1) E4O8.K0 ≤ Subgroup.normalizer (E4O8.K0 : Set _) ∧
      conjSub (E4O8.wsP.getD 1 1) E4O8.K0 ≠ conjSub (E4O8.wsP.getD 3 1) E4O8.K0 := by
  have h : Certificates.E4O8TwoTwins.check () = true := Certificates.certificate393005
  simp only [Certificates.E4O8TwoTwins.check, ← wsA_getD, Bool.and_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨he, hn⟩ := h
  have hw1 := E4A.rep_getD E4O8.forall₂_ws 1
  have hw3 := E4A.rep_getD E4O8.forall₂_ws 3
  rw [E4A.edgeCheckA_eq E4O8.forall₂_L0 E4O8.u0_spec.1 E4O8.v0_spec.1 hw3] at he
  rw [E4A.normsA_eq E4O8.forall₂_L0 E4O8.u0_spec.1 E4O8.v0_spec.1
    (rep_compA (E4A.rep_inv hw1) hw3)] at hn
  obtain ⟨hne, hle⟩ := E4C.edge_of_edgeCheck E4O8.mem_K0_iff he
  refine ⟨hne, hle, fun heq => ?_⟩
  have h1 : conjSub ((E4O8.wsP.getD 1 1)⁻¹ * E4O8.wsP.getD 3 1) E4O8.K0 = E4O8.K0 := by
    rw [conjSub_mul, ← heq, conjSub_inv_conjSub]
  rw [E4C.norms_of_conjSub_eq E4O8.mem_K0_iff h1] at hn
  exact Bool.noConfusion hn

theorem two_twins_of_emb
    {M : Type} [Group M] (φ : M →* Equiv.Perm (Fin 360))
    (hφ : Function.Injective φ) (hrange : φ.range = omegaT) {K : Subgroup M}
    (hK : K.map φ = E4O8.K0) :
    ∃ J₁ J₂ : Subgroup M, J₁ ∈ CoreAssembly.conjClass K ∧ J₂ ∈ CoreAssembly.conjClass K ∧
      J₁ ≠ K ∧ J₂ ≠ K ∧ J₁ ≠ J₂ ∧ J₁ ≤ Subgroup.normalizer (K : Set M) ∧
      J₂ ≤ Subgroup.normalizer (K : Set M) := by
  obtain ⟨hne3, hle3, hne13⟩ := twin3_facts
  obtain ⟨hne1, hle1⟩ := E4O8.edge
  obtain ⟨y₁, hy₁⟩ : ∃ y : M, φ y = E4O8.wsP.getD 1 1 := by
    have h := E4O8.ws_mem 1
    rwa [← hrange] at h
  obtain ⟨y₃, hy₃⟩ : ∃ y : M, φ y = E4O8.wsP.getD 3 1 := by
    have h := E4O8.ws_mem 3
    rwa [← hrange] at h
  have hmap : ∀ y : M, conjSub (φ y) E4O8.K0 = (conjSub y K).map φ := fun y => by
    rw [← hK, conjSub_map]
  refine ⟨conjSub y₁ K, conjSub y₃ K, ⟨y₁, rfl⟩, ⟨y₃, rfl⟩, fun h => hne1 ?_, fun h => hne3 ?_,
    fun h => hne13 ?_, ?_, ?_⟩
  · rw [← hy₁, hmap, h, hK]
  · rw [← hy₃, hmap, h, hK]
  · rw [← hy₁, ← hy₃, hmap, hmap, h]
  · rw [← hy₁, ← hK, conjSub_map] at hle1
    exact (Vtx.map_le_normalizer_map_iff φ hφ).mp hle1
  · rw [← hy₃, ← hK, conjSub_map] at hle3
    exact (Vtx.map_le_normalizer_map_iff φ hφ).mp hle3

theorem o82_two_twins
    {M : Type} [Group M]
    [Finite M] (hM : CFSG.Blueprint.LieModel M .POmegaPlus 4 2 1) {K : Subgroup M} {s : M}
    (hq : Nonempty (↥K ≃* QuaternionGroup 2)) (hinv : IsUniqueInvolution K s)
    (htw : ∀ c ∈ Subgroup.centralizer ({s} : Set M),
      conjSub c K = K ∨ ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) :
    ∃ J₁ J₂ : Subgroup M, J₁ ∈ CoreAssembly.conjClass K ∧ J₂ ∈ CoreAssembly.conjClass K ∧
      J₁ ≠ K ∧ J₂ ≠ K ∧ J₁ ≠ J₂ ∧ J₁ ≤ Subgroup.normalizer (K : Set M) ∧
      J₂ ≤ Subgroup.normalizer (K : Set M) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hM
  have hinj := E4O8.emb_injective e
  have hd := ambientQuatDatum_map_of_twins (E4O8.emb e) hinj hq hinv htw
  rw [E4O8.range_emb e] at hd
  obtain ⟨g, hg, hgK⟩ := E4O8.ident_omega hd
  rw [← E4O8.range_emb e] at hg
  obtain ⟨m, rfl⟩ := hg
  refine two_twins_of_emb ((MulAut.conj (E4O8.emb e m)).toMonoidHom.comp (E4O8.emb e))
    ((MulAut.conj (E4O8.emb e m)).injective.comp hinj) ?_ ?_
  · rw [MonoidHom.range_comp, E4O8.range_emb]
    exact conjSub_eq_self_of_mem (e m).2
  · rw [← Subgroup.map_map]
    exact hgK

end Twins

end ExitE4

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

module

public import CFSG.GH74.GLS.Stage1.Thm6.Prod.L145Main

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

open Subgroup CFSG

section Trans

variable {A B : Type} [Group A] [Group B]

theorem pPrimeCoreOf_map (f : A →* B) (hf : Function.Injective f) (K : Subgroup A) :
    GLS.pPrimeCoreOf 2 (K.map f) = (GLS.pPrimeCoreOf 2 K).map f := by
  let ψ : ↥K ≃* ↥(K.map f) := Subgroup.equivMapOfInjective K f hf
  have h1 : (pPrimeCore 2 ↥K).map ψ.toMonoidHom = pPrimeCore 2 ↥(K.map f) := pPrimeCore_map_iso 2 ψ
  have h2 : (K.map f).subtype.comp ψ.toMonoidHom = f.comp K.subtype := by ext g; rfl
  unfold GLS.pPrimeCoreOf
  rw [← h1, Subgroup.map_map, h2, ← Subgroup.map_map]

theorem pGLModO_map (f : A →* B) (hf : Function.Injective f) {K T : Subgroup A} {q : ℕ}
    (h : GLS.Stage2.Local.PGLModO K T q) : GLS.Stage2.Local.PGLModO (K.map f) (T.map f) q := by
  obtain ⟨hn, F, hF, hFin, hq, ⟨e⟩⟩ := h
  have hsup : K.map f ⊔ T.map f = (K ⊔ T).map f := (Subgroup.map_sup K T f).symm
  let φ : ↥(K ⊔ T) ≃* ↥(K.map f ⊔ T.map f) :=
    (Subgroup.equivMapOfInjective (K ⊔ T) f hf).trans (MulEquiv.subgroupCongr hsup.symm)
  have hφ : ∀ g : ↥(K ⊔ T), ((φ g : ↥(K.map f ⊔ T.map f)) : B) = f (g : A) := fun g => rfl
  have hcore := pPrimeCoreOf_map f hf K
  have hmapN : ((GLS.pPrimeCoreOf 2 K).subgroupOf (K ⊔ T)).map φ.toMonoidHom =
      (GLS.pPrimeCoreOf 2 (K.map f)).subgroupOf (K.map f ⊔ T.map f) := by
    ext g
    rw [Subgroup.mem_subgroupOf, hcore]
    constructor
    · rintro ⟨n, hn', rfl⟩
      exact ⟨(n : A), hn', (hφ n).symm⟩
    · rintro ⟨k, hk, hkg⟩
      have hkK : k ∈ K := by
        obtain ⟨k', hk', rfl⟩ := hk
        exact (Subgroup.map_subtype_le _ ⟨k', hk', rfl⟩)
      have hkKT : k ∈ K ⊔ T := Subgroup.mem_sup_left hkK
      refine ⟨⟨k, hkKT⟩, hk, ?_⟩
      exact Subtype.ext (by rw [← hkg]; exact hφ ⟨k, hkKT⟩)
  have hnorm : ((GLS.pPrimeCoreOf 2 (K.map f)).subgroupOf (K.map f ⊔ T.map f)).Normal := by
    rw [← hmapN]
    exact Subgroup.Normal.map hn φ.toMonoidHom φ.surjective
  refine ⟨hnorm, F, hF, hFin, hq, ⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ φ hmapN).symm.trans e

end Trans

section Back

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_self' (x : G) : x ∈ centralizer ({x} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]

theorem m12NonCentral_of_NC (x : G)
    (h : NC ↥(centralizer ({x} : Set G)) ⟨x, mem_centralizer_self' x⟩
      (fun u => IsConj x (u : G))) : GLS.Stage2.Local.M12NonCentral x := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  obtain ⟨K₀, y₀, q, hcomp, hL2, hq, hy2, hpgl, hinf, h7, hlast⟩ := h
  refine ⟨K₀.map C.subtype, (y₀ : G), q, ?_, ?_, hq, y₀.2, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Subgroup.map_subtype_le _, ?_⟩
    have : (K₀.map C.subtype).subgroupOf C = K₀ :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K₀
    rw [this]; exact hcomp
  · obtain ⟨F, hF, hFin, hq', ⟨e⟩⟩ := hL2
    let ψK : ↥K₀ ≃* ↥(K₀.map C.subtype) := Subgroup.equivMapOfInjective K₀ C.subtype C.subtype_injective
    let eq : ↥K₀ ⧸ pPrimeCore 2 ↥K₀ ≃* ↥(K₀.map C.subtype) ⧸ pPrimeCore 2 ↥(K₀.map C.subtype) :=
      QuotientGroup.congr _ _ ψK (pPrimeCore_map_iso 2 ψK)
    exact ⟨F, hF, hFin, hq', ⟨eq.symm.trans e⟩⟩
  · rw [← orderOf_coe y₀] at *
    exact hy2
  · have := pGLModO_map C.subtype C.subtype_injective hpgl
    rwa [MonoidHom.map_zpowers] at this
  · have h1 : (zpowers (⟨x, mem_centralizer_self' x⟩ : C) ⊓ (K₀ ⊔ zpowers y₀)).map C.subtype = ⊥ := by
      rw [hinf, Subgroup.map_bot]
    rw [Subgroup.map_inf _ _ _ C.subtype_injective, Subgroup.map_sup, MonoidHom.map_zpowers,
      MonoidHom.map_zpowers] at h1
    exact h1
  · have h1 := congrArg (Subgroup.map C.subtype) h7
    rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h1
    exact h1
  · intro u hu hu2 huK
    refine hlast ⟨u, hu⟩ ?_ ?_
    · rw [← Subgroup.orderOf_coe] at *; exact hu2
    · intro hmem; exact huK ⟨_, hmem, rfl⟩

end Back

end CFSG.GH74.GLS.Stage1.Thm6.Prod.L145

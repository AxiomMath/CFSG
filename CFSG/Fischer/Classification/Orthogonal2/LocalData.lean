module

public import CFSG.Fischer.Classification.Orthogonal2.Local
public import CFSG.Fischer.Classification.Symplectic.OrthoGen

import CFSG.Fischer.Classification.FischerTypeLocal
import CFSG.Fischer.Classification.Uniqueness.Triple

public section

namespace CFSG.Fischer.Classification.Orth2

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open Matrix
open CFSG.Fischer.Classification.Recognition.SymO
open CFSG.Blueprint.Fischer CFSG.Fischer

theorem nonabelianCommutator_of_mem_localClass {X : Type} [Group X] {E : Set X} (hH : Hyp X E)
    {d f : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d) : NonabelianCommutator X := by
  by_contra hna
  simp only [NonabelianCommutator, not_exists, not_not] at hna
  obtain ⟨φ, hφ⟩ := Pair.exists_mulEquiv_perm_three hH.pair hH.center hH.simple hna
  obtain ⟨a, b, hab, had⟩ := (hφ d).1 hd
  obtain ⟨c, e, hce, hfe⟩ := (hφ f).1 hf.1
  have hcomm : φ f * φ d = φ d * φ f := by rw [← map_mul, ← map_mul, hf.2.2]
  rw [had, hfe] at hcomm
  apply hf.2.1
  apply φ.injective
  rw [hfe, had]
  exact swap_commute_eq hce hab hcomm

theorem exists_mulEquiv_orthogonalGroup {G : Type} [Group G] {D : Set G} {m : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hO : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    ∃ Φ : G ≃* TauCeti.QuadraticMap.orthogonalGroup Q, Φ '' D = reflClass Q := by
  obtain ⟨φ, hφ⟩ := hO
  have hH : (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x).map
      (toLinEquiv (Fin (2 * m)) (ZMod 2) : GL (Fin (2 * m)) (ZMod 2) →* _) =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [fischerMatrixGroup_isometry_eq_comap]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv _ _).surjective _
  let Φ := φ.trans (((toLinEquiv (Fin (2 * m)) (ZMod 2)).subgroupMap _).trans
    (MulEquiv.subgroupCongr hH))
  have hΦ : ∀ g, ((Φ g : TauCeti.QuadraticMap.orthogonalGroup Q) :
      (Fin (2 * m) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * m) → ZMod 2)) =
        toLinEquiv _ _ (φ g : GL (Fin (2 * m)) (ZMod 2)) := fun g => rfl
  refine ⟨Φ, Set.ext fun q => ⟨?_, ?_⟩⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨v, hv, hgv⟩ := eq_orthTransvectionGL_of_mem_fischerTransvections ((hφ g).mp hg)
    exact ⟨v, hv, by rw [hΦ, hgv, toLinEquiv_orthTransvectionGL]⟩
  · rintro ⟨v, hv, hqv⟩
    refine ⟨Φ.symm q, (hφ _).mpr ?_, Φ.apply_symm_apply q⟩
    have h1 : (φ (Φ.symm q) : GL (Fin (2 * m)) (ZMod 2)) = orthTransvectionGL Q v := by
      apply (toLinEquiv (Fin (2 * m)) (ZMod 2)).injective
      rw [← hΦ, Φ.apply_symm_apply, hqv, toLinEquiv_orthTransvectionGL]
    rw [h1]
    exact orthTransvectionGL_mem_fischerTransvections hv

section Pair

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem localClass_reflClass_nonempty [FiniteDimensional (ZMod 2) V]
    (hnd : (polarBilin Q).Nondegenerate) (h4 : 4 ≤ finrank (ZMod 2) V)
    {t : TauCeti.QuadraticMap.orthogonalGroup Q} (htD : t ∈ reflClass Q) :
    (LocalClass (reflClass Q) t).Nonempty := by
  obtain ⟨v, hv, htv⟩ := htD
  have ht : ∀ x, (t : V ≃ₗ[ZMod 2] V) x = x + polar Q x v • v := fun x => by
    rw [htv, reflect_apply_of_map_eq_one hv]
  obtain ⟨y, hyv⟩ := exists_polar_eq_one hnd hv
  have hvy : bil Q v y = 1 := by rw [bil_apply, polar_comm]; exact hyv
  obtain ⟨-, hsplit⟩ := CFSG.ClassicalGroups.Alternating.alternating_hyperbolic_splitting
    (bil_isAlt Q) hnd (ne_zero_of_map_eq_one hv)
  obtain ⟨-, -, -, -, -, hdimW⟩ := hsplit y hvy
  have hpos : 0 < finrank (ZMod 2) (Recognition.SymO.perp Q v y) := by
    change 0 < finrank (ZMod 2) ((bil Q).orthogonal (Submodule.span (ZMod 2) {v, y}))
    omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  exact ⟨_, lift_mem_localClass hnd hv hyv t ht hw⟩

end Pair

theorem orth_pair_facts {G : Type} [Group G] {D : Set G} (hH : Hyp G D) {m : ℕ} (hm : 3 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hO : fischerLinearModel D (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    TripleProperty D ∧ NonabelianCommutator G ∧
      ∀ d ∈ D, IsSimpleGroup (commutator (LocalQuotient D d)) ∧
        ∃ a b : commutator (LocalQuotient D d), a * b ≠ b * a := by
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_orthogonalGroup hO
  have hnd' : (polarBilin Q).Nondegenerate :=
    ⟨fun x hx => hnd x fun y => by simpa using hx y,
      fun y hy => hnd y fun x => by rw [polar_comm]; simpa using hy x⟩
  have hdim : finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m := Module.finrank_fin_fun _
  have hmemD : ∀ d ∈ D, Φ d ∈ reflClass Q := fun d hd => hΦ ▸ Set.mem_image_of_mem Φ hd
  have hloc : ∀ d ∈ D, IsSimpleGroup (commutator (LocalQuotient D d)) ∧
      ∃ a b : commutator (LocalQuotient D d), a * b ≠ b * a := by
    intro d hd
    obtain ⟨hS, hna⟩ := localQuotient_simple hnd' hdim hm (hmemD d hd)
    let e : LocalQuotient D d ≃* LocalQuotient (reflClass Q) (Φ d) :=
      localQuotientCongr Φ hΦ rfl
    exact ⟨Recognition.R3.isSimpleGroup_commutator_of_mulEquiv e.symm,
      exists_ne_commutator_of_mulEquiv e.symm hna⟩
  refine ⟨(tripleProperty_congr Φ hΦ).2 (tripleProperty_reflClass hnd' (by omega)), ?_, hloc⟩
  obtain ⟨d, hd⟩ := Pair.nonempty hH.pair
  obtain ⟨r, hr⟩ := localClass_reflClass_nonempty hnd' (by omega) (hmemD d hd)
  have hrD : Φ.symm r ∈ D := by
    have : r ∈ Φ '' D := hΦ ▸ hr.1
    obtain ⟨g, hg, rfl⟩ := this
    simpa using hg
  refine nonabelianCommutator_of_mem_localClass hH hd ⟨hrD, fun h => hr.2.1 ?_, ?_⟩
  · rw [← h, Φ.apply_symm_apply]
  · apply Φ.injective
    rw [map_mul, map_mul, Φ.apply_symm_apply, hr.2.2]

end CFSG.Fischer.Classification.Orth2

module

public import CFSG.ClassicalInvolution.QuaternionStructure.Lifting

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG CFSG.GorensteinWalter
open scoped MatrixGroups

universe u

namespace QuaternionSetting

variable {G : Type u} [Group G] {z : G} {r : ℕ} (h : QuaternionSetting G z r)

include h

omit h in
theorem exists_hom_of_comap [Finite G] [(Subgroup.zpowers z).Normal]
    (L' : Subgroup (G ⧸ Subgroup.zpowers z)) {A : Type*} [Group A] (e : L' ≃* A) :
    ∃ φ : (L'.comap (QuotientGroup.mk' (Subgroup.zpowers z))) →* A,
      Function.Surjective φ ∧
        φ.ker.map (L'.comap (QuotientGroup.mk' (Subgroup.zpowers z))).subtype =
          Subgroup.zpowers z := by
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let M : Subgroup G := L'.comap π
  let ρ : M →* L' := (π.comp M.subtype).codRestrict L' (fun x => x.2)
  have hρ : Function.Surjective ρ := by
    intro y
    obtain ⟨x, hx⟩ := hπ y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change π x ∈ L'
    rw [hx]
    exact y.2
  refine ⟨e.toMonoidHom.comp ρ, e.surjective.comp hρ, ?_⟩
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have hker : ∀ x : M, (e.toMonoidHom.comp ρ) x = 1 ↔ (x : G) ∈ Subgroup.zpowers z := by
    intro x
    change e (ρ x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, ← QuotientGroup.eq_one_iff (x : G)]
    exact Subtype.ext_iff
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hker x).mp hx
  · intro hg
    have hgM : g ∈ M := by
      change π g ∈ L'
      have : π g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
      rw [this]
      exact one_mem _
    exact ⟨⟨g, hgM⟩, (hker ⟨g, hgM⟩).mpr hg, rfl⟩

theorem classification [Finite G] (hGW : gorensteinWalterStatement.{u}) :
    IsPGroup 2 G ∨
      (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
        ∃ L : Subgroup G, L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* SL(2, F))) ∨
      (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
        ∃ L : Subgroup G, L.Normal ∧ Odd L.index ∧
          (∃ φ : L →* PGL2 F, Function.Surjective φ ∧
            φ.ker.map L.subtype = Subgroup.zpowers z) ∧
          (∀ P : Sylow 2 L, ∃ k : ℕ, 1 ≤ k ∧
            Nonempty ((P : Subgroup L) ≃* QuaternionGroup (2 ^ k))) ∧
          ∃ M : Subgroup G, M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* SL(2, F))) ∨
      (commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G) ∧
        Nat.card (Subgroup.center G) = 2 ∧
        Nonempty ((G ⧸ Subgroup.center G) ≃* alternatingGroup (Fin 7))) := by
  have hN : (Subgroup.zpowers z).Normal := h.normal_zpowers
  have hr := h.three_le
  rcases h.gw_trichotomy hGW with hH | ⟨⟨e7⟩⟩ | ⟨K, _, _, hK, L', hL'n, hL'i, hmodel⟩
  · exact Or.inl (isPGroup_of_isPGroup_quotient _ h.natCard_zpowers hH)
  · obtain ⟨hcomm, -, hsimple, hcard, hiso⟩ := h.alt7_structure e7
    exact Or.inr (Or.inr (Or.inr ⟨hcomm, hsimple, hcard, hiso⟩))
  · have hchar : ringChar K ≠ 2 :=
      ringChar_ne_two_of_odd_natCard K (odd_natCard_of_isOddPrimePower hK)
    let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hLn : (L'.comap π).Normal := hL'n.comap π
    have hLi : Odd (L'.comap π).index := by
      rw [Subgroup.index_comap_of_surjective L' hπ]
      exact hL'i
    rcases hmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hchar, L'.comap π, hLn, hLi,
        h.exists_mulEquiv_specialLinearGroup hchar L' e⟩)
    · obtain ⟨φ, hφ, hφker⟩ := exists_hom_of_comap L' e
      obtain ⟨N, hNn, hNle, ⟨eN⟩⟩ := exists_normal_psl2_core_of_pgl2 L' hL'n hK e
      refine Or.inr (Or.inr (Or.inl ⟨K, inferInstance, inferInstance, hchar, L'.comap π, hLn,
        hLi, ⟨φ, hφ, hφker⟩, fun P => ⟨r - 2, by omega, ?_⟩,
        N.comap π, hNn.comap π, Subgroup.comap_mono hNle,
        h.exists_mulEquiv_specialLinearGroup hchar N eN⟩))
      exact h.sylow_equiv_of_odd_index (L'.comap π) hLi P

end QuaternionSetting

theorem quaternion_structure_of_hyps (hGW : gorensteinWalterStatement.{u})
    {X : Type u} [Group X] [Finite X] (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hBS : ∀ t ∈ (S : Subgroup X), orderOf t = 2 →
      (QuotientGroup.mk t : X ⧸ oddCore X) ∈ Subgroup.center (X ⧸ oddCore X)) :
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      (∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z) ∧
      (IsPGroup 2 (X ⧸ oddCore X) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧ Nonempty (L ≃* SL(2, F))) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F), ringChar F ≠ 2 ∧
          ∃ L : Subgroup (X ⧸ oddCore X), L.Normal ∧ Odd L.index ∧
            (∃ φ : L →* PGL2 F, Function.Surjective φ ∧
              φ.ker.map L.subtype = Subgroup.zpowers z) ∧
            (∀ P : Sylow 2 L, ∃ k : ℕ, 1 ≤ k ∧
              Nonempty ((P : Subgroup L) ≃* QuaternionGroup (2 ^ k))) ∧
            ∃ M : Subgroup (X ⧸ oddCore X), M.Normal ∧ M ≤ L ∧ Nonempty (M ≃* SL(2, F))) ∨
        (commutator (X ⧸ oddCore X) = ⊤ ∧
          IsSimpleGroup ((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ∧
          Nat.card (Subgroup.center (X ⧸ oddCore X)) = 2 ∧
          Nonempty (((X ⧸ oddCore X) ⧸ Subgroup.center (X ⧸ oddCore X)) ≃*
            alternatingGroup (Fin 7)))) := by
  obtain ⟨z, hz2, hzc, hzu⟩ := exists_central_unique_involution S hS hBS
  obtain ⟨r, hr, ⟨e⟩⟩ := hS
  have hset : QuaternionSetting (X ⧸ oddCore X) z r :=
    { three_le := hr
      orderOf_eq_two := hz2
      mem_center := hzc
      eq_of_orderOf_eq_two := hzu
      sylow_equiv := fun P => sylow_oddCore_quotient_quaternion S e P
      oddCore_eq_bot := oddCore_quotient_oddCore_eq_bot X }
  exact ⟨z, hz2, hzc, hzu, hset.classification hGW⟩

end CFSG.ClassicalInvolution.QuaternionStructure

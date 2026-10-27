module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv InClass
  IsClassicalMember LocalOddCentral ExactMembers centralizingMembers ConjInvariant LieSystemData
  centralizingLayer_le_centralizer)
open CFSG.ClassicalInvolution.RouteD

theorem charOf_add {r : ℕ} (v : Fin r → ZMod 2) (γ δ : Fin r → ℤ) :
    charOf v (γ + δ) = charOf v γ + charOf v δ := by
  simp only [charOf, Pi.add_apply, Int.cast_add, add_mul]
  exact Finset.sum_add_distrib

theorem charOf_zero {r : ℕ} (v : Fin r → ZMod 2) : charOf v 0 = 0 := by
  simp [charOf]

theorem charOf_sum {r : ℕ} {ι : Type} (v : Fin r → ZMod 2) (s : Finset ι)
    (g : ι → (Fin r → ℤ)) : charOf v (∑ i ∈ s, g i) = ∑ i ∈ s, charOf v (g i) :=
  map_sum (⟨⟨charOf v, charOf_zero v⟩, charOf_add v⟩ : (Fin r → ℤ) →+ ZMod 2) g s

theorem charOf_weylAction {K : Type*} [Group K] (D : UniversalRootDatum K)
    (v : Fin D.rank → ZMod 2) (W₀ : (coxeterMatrix D.isFiniteType).Group) (p₀ : Fin D.rank)
    (h : ∀ j, charOf v (weylAction D.isFiniteType W₀ (Pi.single j 1)) =
      (Pi.single p₀ 1 : Fin D.rank → ZMod 2) j) (γ : Fin D.rank → ℤ) :
    charOf v (weylAction D.isFiniteType W₀ γ) = ((γ p₀ : ℤ) : ZMod 2) := by
  have hγ : γ = ∑ j, γ j • (Pi.single j 1 : Fin D.rank → ℤ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hγ]
  rw [map_sum, charOf_sum]
  have : ∀ j, charOf v (weylAction D.isFiniteType W₀ (γ j • (Pi.single j 1 : Fin D.rank → ℤ))) =
      ((γ j : ℤ) : ZMod 2) * (Pi.single p₀ 1 : Fin D.rank → ZMod 2) j := fun j => by
    rw [map_zsmul, charOf_smul, h j]
  simp only [this]
  rw [Finset.sum_eq_single p₀]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem exists_adapted_frame_normal {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}
    (hΩ : ConjInvariant Ω) {Y : LieUniversal} (ψ : Y.K →* locQuot Ω z)
    {n : Fin Y.D.rank → Y.K} {H : Fin Y.D.rank → Subgroup Y.K}
    (hct : IsCTGroupDatum (coxeterMatrix Y.D.isFiniteType).toCoxeterSystem
      (weylAction Y.D.isFiniteType) Y.D.roots Y.D.rootGroup n H)
    (hPat : PatternLemma Y.D.cartan) {t : G} (ht : t * z * t⁻¹ = z)
    (v : Fin Y.D.rank → ZMod 2) (hv : v ≠ 0) (k₀ : Y.K)
    (hT : ∀ γ ∈ Y.D.roots,
      ((conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ).map
          (locAut hΩ ht).toMonoidHom = (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ ∧
        ((∀ x ∈ (conjSub k₀ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ))).map ψ, locAut hΩ ht x = x) ↔
          charOf v γ = 0))
    {j : Fin Y.D.rank → Subgroup G}
    (hjimg : ∀ a, locImg Ω z (j a) = (rankOne Y.D.rootGroup a).map ψ) :
    ∃ y ∈ locLayer Ω z, ∃ g : Y.K, ∃ p₀ : Fin Y.D.rank,
      (∀ a, locImg Ω z (conjSub y (j a)) =
        (rankOne Y.D.rootGroup a).map (ψ.comp (MulAut.conj g).toMonoidHom)) ∧
      ∀ γ ∈ Y.D.roots,
        ((Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map (ψ.comp (MulAut.conj g).toMonoidHom)).map
            (locAut hΩ ht).toMonoidHom =
          (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map (ψ.comp (MulAut.conj g).toMonoidHom) ∧
        ((∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map
            (ψ.comp (MulAut.conj g).toMonoidHom), locAut hΩ ht x = x) ↔
          ((γ p₀ : ℤ) : ZMod 2) = 0) := by
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (ψ k₀)
  let ψ₀ : Y.K →* locQuot Ω z := ψ.comp (MulAut.conj k₀).toMonoidHom
  have hmap : ∀ S : Subgroup Y.K, (conjSub k₀ S).map ψ = S.map ψ₀ := fun S => by
    unfold conjSub
    rw [Subgroup.map_map]
  have hT₀ : ∀ γ ∈ Y.D.roots,
      ((Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀).map (locAut hΩ ht).toMonoidHom =
          (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀ ∧
        ((∀ x ∈ (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map ψ₀, locAut hΩ ht x = x) ↔
          charOf v γ = 0) := fun γ hγ => by
    rw [← hmap]
    exact hT γ hγ
  have hjimg₀ : ∀ a, locImg Ω z (conjSub (y₀ : G) (j a)) =
      (rankOne Y.D.rootGroup a).map ψ₀ := fun a => by
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = ψ k₀ from hy₀,
      map_conj_map_hom, hmap]
  obtain ⟨w, hw, p₀, rfl⟩ := hPat v hv
  obtain ⟨W₀, k, hk, hW₀⟩ := exists_actsAs_of_charReach hct hw
  obtain ⟨y₁, hy₁⟩ := QuotientGroup.mk_surjective (ψ₀ k)
  have hψ₁ : ψ.comp (MulAut.conj (k₀ * k)).toMonoidHom =
      ψ₀.comp (MulAut.conj k).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ψ₀]
    congr 1
    group
  have hframe : ∀ γ ∈ Y.D.roots, (Y.D.rootGroup γ ⊔ Y.D.rootGroup (-γ)).map
      (ψ.comp (MulAut.conj (k₀ * k)).toMonoidHom) =
        (Y.D.rootGroup (weylAction Y.D.isFiniteType W₀ γ) ⊔
          Y.D.rootGroup (-weylAction Y.D.isFiniteType W₀ γ)).map ψ₀ := by
    intro γ hγ
    rw [hψ₁, ← Subgroup.map_map]
    congr 1
    exact conjSub_rankOne_of_actsAs hk hγ (CFSG.Timmesfeld.LevisExtras.neg_mem_roots hγ)
  refine ⟨(y₁ : G) * (y₀ : G), (locLayer Ω z).mul_mem y₁.2 y₀.2, k₀ * k, p₀, fun a => ?_,
    fun γ hγ => ?_⟩
  · rw [CFSG.ClassicalInvolution.Generic.conjSub_mul, locImg_conjSub_layer, hjimg₀ a,
      show locMk Ω z y₁ = ψ₀ k from hy₁, map_conj_map_hom, hψ₁]
    unfold conjSub
    rw [Subgroup.map_map]
  · rw [hframe γ hγ]
    obtain ⟨hstab, hfixiff⟩ := hT₀ _ (weylAction_mem_roots _ W₀ hγ)
    refine ⟨hstab, ?_⟩
    rw [hfixiff, charOf_weylAction Y.D v W₀ p₀ hW₀ γ]

end CFSG.ClassicalInvolution.RouteD.Gaps

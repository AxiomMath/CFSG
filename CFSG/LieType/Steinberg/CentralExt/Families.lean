module

public import CFSG.LieType.Steinberg.CentralExt.Split
public import CFSG.LieType.Steinberg.Classical.SpecialLinear
public import CFSG.LieType.Steinberg.Classical.SpinOdd.RankOne
public import CFSG.LieType.Steinberg.Classical.SpinPlus
public import CFSG.LieType.Steinberg.Classical.Symplectic.RankOne
public import CFSG.LieType.Steinberg.G2.Extras
public import CFSG.LieType.Steinberg.Minuscule.ChevExtras

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank

variable {E : Type*} [Group E] [Finite E]

theorem sl_central_two_extension_splitting (m : ℕ) {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) {π : E →* Matrix.SpecialLinearGroup (Fin (m + 1)) k}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : Matrix.SpecialLinearGroup (Fin (m + 1)) k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : Matrix.SpecialLinearGroup (Fin (m + 1)) k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (SpecialLinear.isCTGroupDatum m k) (SpecialLinear.steinbergExtras m k) SL.isParametrization
    SL.rankOne hπ hker h2)

section Symplectic

variable (r : ℕ) {k : Type} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {π : E →* StatedSp r k}

theorem sp_existsUnique_section_of_sl2_lift (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (hC : ¬ p ∣ Nat.card π.ker)
    (hlift : ∀ ρ : Matrix.SpecialLinearGroup (Fin 2) k →* StatedSp r k,
      ∃ ρ' : Matrix.SpecialLinearGroup (Fin 2) k →* E, ∀ g, π (ρ' g) = ρ g) :
    ∃! σ : StatedSp r k →* E, ∀ x, π (σ x) = x :=
  existsUnique_section_of_sl2_lift (Symplectic.isCTGroupDatum r k)
    (Symplectic.steinbergExtras r k) Sp.isParametrization Sp.rankOne hπ hker hC hlift

theorem odd_symplectic_central_two_extension_splitting {k : Type} [Field k] [Finite k]
    (hk : ringChar k ≠ 2) (r : ℕ) {E : Type*} [Group E] [Finite E] {π : E →* StatedSp r k}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : StatedSp r k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : StatedSp r k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (Symplectic.isCTGroupDatum r k) (Symplectic.steinbergExtras r k) Sp.isParametrization
    Sp.rankOne hπ hker h2)

end Symplectic

theorem spinOdd_central_two_extension_splitting {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) {π : E →* spinGroup (Spin.quadOdd n k)}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : spinGroup (Spin.quadOdd n k) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : spinGroup (Spin.quadOdd n k) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (Spin.oddDatum_isCTGroupDatum n k (Spin.oddDatum_iSup_eq_top n k (Ring.two_ne_zero hk) hn))
    (Spin.oddDatum_steinbergExtras (Ring.two_ne_zero hk)) SpinOdd.isParametrization
    SpinOdd.rankOne hπ hker h2)

theorem spinPlus_central_two_extension_splitting {n : ℕ} (hn : 3 ≤ n) {k : Type} [Field k]
    [Finite k] (hk : ringChar k ≠ 2) {π : E →* spinGroup (Spin.quadPlus n k)}
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : spinGroup (Spin.quadPlus n k) →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : spinGroup (Spin.quadPlus n k) →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (SpinPlus.isCTGroupDatum hn) (Spin.plusDatum_steinbergExtras hn)
    (SpinPlus.isParametrization hn) (SpinPlus.rankOne hn) hπ hker h2)

section Adjoint

open Adjoint

theorem Adjoint.exists_sl2_hom_xPar
    {τ : Tag} {K : Type} [Field K] {F : RootOperatorFamily τ}
    {i : Fin τ.rank}
    (h : ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = F.eltElement (simpleRoot τ i) c) ∧
        ∀ c, φ (sl2Lower c) = F.eltElement (-simpleRoot τ i) c) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup τ K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = xPar F (Pi.single i 1) c) ∧
        ∀ c, φ (sl2Lower c) = xPar F (-Pi.single i 1) c :=
  h.imp fun _ hφ => ⟨hφ.1, fun c => (hφ.2.1 c).trans (xPar_simple i c).symm,
    fun c => (hφ.2.2 c).trans (xPar_neg_simple i c).symm⟩

theorem g2_central_two_extension_splitting
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {π : E →* adjointGroup .G2 k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : adjointGroup .G2 k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : adjointGroup .G2 k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (g2_isCTGroupDatum k) (g2_steinbergExtras k)
    (adjDatum_isParametrization (F := rootOperatorFamily .G2) (K := k) _ (adjDatum_roots _ k))
    (fun i => Adjoint.exists_sl2_hom_xPar (g2_exists_sl2_hom i)) hπ hker h2)

theorem f4_central_two_extension_splitting
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {π : E →* adjointGroup .F4 k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : adjointGroup .F4 k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : adjointGroup .F4 k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (f4_isCTGroupDatum k) (f4_steinbergExtras k) (f4_isParametrization k)
    (fun i => Adjoint.exists_sl2_hom_xPar
      (exists_sl2_hom (rootOperatorFamily .F4) (neighbour_F4 i).choose_spec.1)) hπ hker h2)

theorem e8_central_two_extension_splitting
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {π : E →* adjointGroup .E8 k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : adjointGroup .E8 k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : adjointGroup .E8 k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (e8_isCTGroupDatum k) (e8_steinbergExtras k) (e8_isParametrization k)
    (fun i => Adjoint.exists_sl2_hom_xPar
      (exists_sl2_hom (rootOperatorFamily .E8) (neighbour_E8 i).choose_spec.1)) hπ hker h2)

end Adjoint

theorem e6_central_two_extension_splitting
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {π : E →* e6Data_valid.minGroup k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : e6Data_valid.minGroup k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : e6Data_valid.minGroup k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (e6Datum_isCTGroupDatum k) (e6Datum_steinbergExtras k)
    (e6Datum_isParametrization k _ (roots_eq isFiniteType_cartan_E6))
    (e6Data_valid.exists_sl2Hom k) hπ hker h2)

theorem e7_central_two_extension_splitting
    {k : Type} [Field k] [Finite k] (hk : ringChar k ≠ 2)
    {π : E →* e7Data_valid.minGroup k} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) :
    ∃ σ : e7Data_valid.minGroup k →* E, (∀ x, π (σ x) = x) ∧
      (∀ τ : e7Data_valid.minGroup k →* E, (∀ x, π (τ x) = x) → τ = σ) ∧
      ∃ e : π.ker × σ.range ≃* E, ∀ a, e a = (a.1 : E) * a.2 :=
  exists_section_mulEquiv_of_existsUnique hker (existsUnique_section_of_sl2 hk
    (e7Datum_isCTGroupDatum k) (e7Datum_steinbergExtras k)
    (e7Datum_isParametrization k _ (roots_eq isFiniteType_cartan_E7))
    (e7Data_valid.exists_sl2Hom k) hπ hker h2)

end CFSG.LieType.Steinberg

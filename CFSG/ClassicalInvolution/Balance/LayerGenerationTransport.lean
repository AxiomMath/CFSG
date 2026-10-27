module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationShort
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorus

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

section Transport

variable {K : Type*} [Group K] {X : Type*} [Group X]

@[expose] def fixedGroup (δ : K ≃* K) : Subgroup K where
  carrier := {y | δ y = y}
  mul_mem' := fun {a b} (ha : δ a = a) (hb : δ b = b) => by
    show δ (a * b) = a * b
    rw [map_mul, ha, hb]
  one_mem' := map_one δ
  inv_mem' := fun {a} (ha : δ a = a) => by
    show δ a⁻¹ = a⁻¹
    rw [map_inv, ha]

theorem mem_fixedGroup {δ : K ≃* K} {y : K} : y ∈ fixedGroup δ ↔ δ y = y := Iff.rfl

theorem isComponentOf_map_centralizer {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K) (g : K)
    (e : X) (δ : K ≃* K)
    (hδ : ∀ y : K, e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * δ y * g⁻¹)) {Q₀ : Subgroup K}
    (hQ : IsComponentOf Q₀ (fixedGroup δ)) :
    IsComponentOf (Q₀.map (ψ.comp (MulAut.conj g).toMonoidHom))
      ((ψ.comp (MulAut.conj g).toMonoidHom).range ⊓ Subgroup.centralizer ({e} : Set X)) := by
  set Ψ : K →* X := ψ.comp (MulAut.conj g).toMonoidHom with hΨ
  have hΨy : ∀ y, Ψ y = ψ (g * y * g⁻¹) := fun y => rfl
  have hδ' : ∀ y, e * Ψ y * e⁻¹ = Ψ (δ y) := fun y => by
    rw [hΨy, hΨy]
    exact hδ y
  have hkerΨ : Ψ.ker ≤ Subgroup.center K := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ Subgroup.center K := hker (by simpa [hΨy] using hy)
    have h2 := Subgroup.Normal.conj_mem (inferInstance : (Subgroup.center K).Normal) _ h1 g⁻¹
    have e1 : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e1] at h2
  set C' : Subgroup K := (Subgroup.centralizer ({e} : Set X)).comap Ψ with hC'
  have hmemC' : ∀ y, y ∈ C' ↔ Ψ y * e = e * Ψ y := fun y => by
    rw [hC', Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  have hfixC : fixedGroup δ ≤ C' := by
    intro y hy
    rw [hmemC']
    have h1 := hδ' y
    rw [mem_fixedGroup.mp hy] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hnormal : ((fixedGroup δ).subgroupOf C').Normal := by
    rw [Subgroup.normal_subgroupOf_iff hfixC]
    intro c y hc hy
    have hy' := (hmemC' y).mp hy
    have h1 : Ψ (δ y) = Ψ y := by
      rw [← hδ' y, mul_inv_eq_iff_eq_mul]
      exact hy'.symm
    have hz : y⁻¹ * δ y ∈ Subgroup.center K := hkerΨ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel])
    have hzc := Subgroup.mem_center_iff.mp hz
    show δ (y * c * y⁻¹) = y * c * y⁻¹
    have hδc : δ c = c := mem_fixedGroup.mp hc
    have e2 : δ y = y * (y⁻¹ * δ y) := by group
    rw [map_mul, map_mul, map_inv, hδc, e2]
    have e3 : y * (y⁻¹ * δ y) * c * (y * (y⁻¹ * δ y))⁻¹ = y * c * y⁻¹ := by
      have e4 : y * (y⁻¹ * δ y) * c * (y * (y⁻¹ * δ y))⁻¹ =
          y * ((y⁻¹ * δ y) * c * (y⁻¹ * δ y)⁻¹) * y⁻¹ := by group
      rw [e4]
      have e5 : (y⁻¹ * δ y) * c = c * (y⁻¹ * δ y) := (hzc c).symm
      rw [e5]
      group
    rw [← e2] at e3 ⊢
    exact e3
  obtain ⟨hQle, hQsub, hQq⟩ := hQ
  have hsubC : IsSubnormal Q₀ C' :=
    isSubnormal_trans hQsub (isSubnormal_of_normal_subgroupOf hfixC hnormal)
  have hmapsub := Components.chain_map Ψ hsubC
  have hW : C'.map Ψ = Ψ.range ⊓ Subgroup.centralizer ({e} : Set X) := by
    rw [hC', Subgroup.map_comap_eq, inf_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hW]
    exact Subgroup.map_mono (hQle.trans hfixC)
  · rw [← hW]
    exact hmapsub
  · set Φ : ↥Q₀ →* ↥(Q₀.map Ψ) := Ψ.subgroupMap Q₀ with hΦ
    have hΦs : Function.Surjective Φ := Ψ.subgroupMap_surjective Q₀
    have hΦker : Φ.ker ≤ Subgroup.center ↥Q₀ := by
      intro y hy
      rw [MonoidHom.mem_ker] at hy
      have hy1 : Ψ (y : K) = 1 := congrArg Subtype.val hy
      have hc := hkerΨ hy1
      rw [Subgroup.mem_center_iff]
      intro q
      exact Subtype.ext (Subgroup.mem_center_iff.mp hc (q : K))
    have hnat : CFSG.IsQuasisimple ↥Q₀ :=
      (AssemblyBPredicates.isQuasisimple_iff_native _).mp hQq
    have hq' := (CFSG.LocalAnalysis.ComponentInitial.quasisimple_central_quotient hnat
      (A := Φ.ker) hΦker).1
    have hiso := QuotientGroup.quotientKerEquivOfSurjective Φ hΦs
    have hq'' : CFSG.IsQuasisimple ↥(Q₀.map Ψ) :=
      (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr hiso).1 hq'
    exact (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq''

theorem range_comp_conj (ψ : K →* X) (g : K) :
    (ψ.comp (MulAut.conj g).toMonoidHom).range = ψ.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulAut.conj g).surjective,
    ← MonoidHom.range_eq_map]

theorem inComponentOfCentralizer_of_fixedGroup {ψ : K →* X} (hker : ψ.ker ≤ Subgroup.center K)
    (g : K) (e : X) (δ : K ≃* K)
    (hδ : ∀ y : K, e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * δ y * g⁻¹)) {Q₀ R₀ : Subgroup K}
    (hQ : IsComponentOf Q₀ (fixedGroup δ)) (hR : R₀ ≤ Q₀) :
    InComponentOfCentralizer ψ.range (R₀.map (ψ.comp (MulAut.conj g).toMonoidHom)) e := by
  refine ⟨_, Subgroup.map_mono hR, ?_⟩
  have h := isComponentOf_map_centralizer hker g e δ hδ hQ
  rwa [range_comp_conj] at h

theorem rankOneImage_eq_map {D : UniversalRootDatum K} (ψ : K →* X) (g : K)
    (γ : Fin D.rank → ℤ) :
    rankOneImage D ψ g γ =
      (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (ψ.comp (MulAut.conj g).toMonoidHom) := by
  unfold rankOneImage rankOneRoot
  rw [Subgroup.map_map]

theorem actsAs_automorphism_of_diagonal {D : UniversalRootDatum K} {k : Type*} [Field k]
    {x : (Fin D.rank → ℤ) → k → K}
    {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
    {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}
    (hX : ChevalleyExtras D k x C O)
    (hgen : ⨆ i : Fin D.rank, rankOne D.rootGroup i = ⊤)
    (ψ : K →* X) (g : K) (e : X) (b : Fin D.rank → kˣ)
    (hb : ∀ i, ActsDiagonallyOnSimple x ψ g i e (b i)) (δ : K ≃* K)
    (hδx : ∀ i c, δ (x (Pi.single i 1) c) = x (Pi.single i 1) ((b i : k) * c))
    (hδy : ∀ i c, δ (x (-Pi.single i 1) c) = x (-Pi.single i 1) (((b i)⁻¹ : kˣ) * c))
    (y : K) : e * ψ (g * y * g⁻¹) * e⁻¹ = ψ (g * δ y * g⁻¹) := by
  set Ψ : K →* X := ψ.comp (MulAut.conj g).toMonoidHom with hΨ
  have hle : (⊤ : Subgroup K) ≤ MonoidHom.eqLocus ((MulAut.conj e).toMonoidHom.comp Ψ)
      (Ψ.comp δ.toMonoidHom) := by
    rw [← hgen]
    refine iSup_le fun i => sup_le (fun z hz => ?_) (fun z hz => ?_)
    · obtain ⟨c, rfl⟩ := ((hX.param _ (single_mem_roots D i)).1 z).mp hz
      show e * ψ (g * x (Pi.single i 1) c * g⁻¹) * e⁻¹ = ψ (g * δ (x (Pi.single i 1) c) * g⁻¹)
      rw [(hb i).1 c, hδx]
    · obtain ⟨c, rfl⟩ := ((hX.param _ ((RootSystem.ofCartan D.isFiniteType D.divisible).neg_mem _
        (single_mem_roots D i))).1 z).mp hz
      show e * ψ (g * x (-Pi.single i 1) c * g⁻¹) * e⁻¹ = ψ (g * δ (x (-Pi.single i 1) c) * g⁻¹)
      rw [(hb i).2 c, hδy]
  exact hle (Subgroup.mem_top y)

end Transport

end CFSG.ClassicalInvolution.Balance

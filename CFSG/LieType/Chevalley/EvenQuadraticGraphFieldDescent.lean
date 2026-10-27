module

public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.ChevalleyLargeRootCentralizerFaithful
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
open CFSG.GroupTheory CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Conj

variable {G : Type*} [Group G]

theorem fixed_centralizer_of_conj_eq {α β ψ : MulAut G} (h : ψ * α * ψ⁻¹ = β) :
    (α.toMonoidHom.eqLocus (MonoidHom.id G)).map ψ.toMonoidHom =
        β.toMonoidHom.eqLocus (MonoidHom.id G) ∧
      (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id G)) ≃*
          ↥(β.toMonoidHom.eqLocus (MonoidHom.id G)), ∀ u, (e u : G) = ψ u) ∧
      (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom = Subgroup.centralizer {β} ∧
      ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
        ∀ γ, (e γ : MulAut G) = ψ * γ * ψ⁻¹ := by
  have hα : α = ψ⁻¹ * β * ψ := by rw [← h]; group
  have hfix : (α.toMonoidHom.eqLocus (MonoidHom.id G)).map ψ.toMonoidHom =
      β.toMonoidHom.eqLocus (MonoidHom.id G) := by
    ext w
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : α u = u := hu
      change β (ψ u) = ψ u
      rw [← h, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hu']
    · intro hw
      have hw' : β w = w := hw
      refine ⟨ψ⁻¹ w, ?_, MulAut.apply_inv_self _ ψ w⟩
      change α (ψ⁻¹ w) = ψ⁻¹ w
      rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hw']
  have hcent : (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
      Subgroup.centralizer {β} := by
    ext γ'
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hγ ⊢
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← h]
      calc ψ * γ * ψ⁻¹ * (ψ * α * ψ⁻¹) = ψ * (γ * α) * ψ⁻¹ := by group
        _ = ψ * (α * γ) * ψ⁻¹ := by rw [hγ]
        _ = ψ * α * ψ⁻¹ * (ψ * γ * ψ⁻¹) := by group
    · intro hγ'
      refine ⟨ψ⁻¹ * γ' * ψ, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_singleton_iff] at hγ' ⊢
        rw [hα]
        calc ψ⁻¹ * γ' * ψ * (ψ⁻¹ * β * ψ) = ψ⁻¹ * (γ' * β) * ψ := by group
          _ = ψ⁻¹ * (β * γ') * ψ := by rw [hγ']
          _ = ψ⁻¹ * β * ψ * (ψ⁻¹ * γ' * ψ) := by group
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  refine ⟨hfix, ⟨((α.toMonoidHom.eqLocus (MonoidHom.id G)).equivMapOfInjective ψ.toMonoidHom
      ψ.injective).trans (MulEquiv.subgroupCongr hfix), fun u => rfl⟩, hcent,
    ((Subgroup.centralizer {α}).equivMapOfInjective (MulAut.conj ψ).toMonoidHom
      (MulAut.conj ψ).injective).trans (MulEquiv.subgroupCongr hcent), fun γ => ?_⟩
  change MulAut.conj ψ (γ : MulAut G) = _
  rw [MulAut.conj_apply]

end Conj

@[expose] def adjointBaseChangeHom
    (τ : Tag) {K L : Type} [Field K] [Field L] (f : K →+* L) :
    adjointGroup τ K →* adjointGroup τ L :=
  ((baseChangeGL f).comp (adjointGroup τ K).subtype).codRestrict (adjointGroup τ L) fun u =>
    baseChangeGL_mem_adjointGroup f u.2

theorem coe_adjointBaseChangeHom
    (τ : Tag) {K L : Type} [Field K] [Field L] (f : K →+* L)
    (u : adjointGroup τ K) : (adjointBaseChangeHom τ f u : ModGL τ L) = baseChangeGL f u :=
  rfl

theorem adjointBaseChangeHom_injective
    (τ : Tag) {K L : Type} [Field K] [Field L]
    (f : K →+* L) : Function.Injective (adjointBaseChangeHom τ f) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective f (congrArg Subtype.val h))

theorem exists_conj_eq_of_sq_eq_frobenius
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (S : MulAut (adjointGroup τ L))
    (hS2 : ∀ g, ((S (S g) : adjointGroup τ L) : ModGL τ L) = Units.map (entrywiseHom Fr) g)
    (hLang : ∀ y : adjointGroup τ L, ∃ h, y = h⁻¹ * S h) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u, S (adjointBaseChangeHom τ (algebraMap K L) u) =
      adjointBaseChangeHom τ (algebraMap K L) (β u))
    (x : adjointGroup τ L) (α : MulAut (adjointGroup τ K))
    (hα : ∀ u, adjointBaseChangeHom τ (algebraMap K L) (α u) =
      x * S (adjointBaseChangeHom τ (algebraMap K L) u) * x⁻¹)
    (hα2 : α * α = 1) :
    ∃ ψ : MulAut (adjointGroup τ K), ψ * α * ψ⁻¹ = β := by
  classical
  set ι := adjointBaseChangeHom τ (algebraMap K L) with hιdef
  have hι : ∀ u, (ι u : ModGL τ L) = baseChangeGL (algebraMap K L) u := fun _ => rfl
  have hSS : ∀ u, S (S (ι u)) = ι u := fun u => Subtype.ext ((hS2 _).trans
    (units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr _))
  have hz : x * S x = 1 := by
    obtain ⟨-, -, hC, -⟩ :=
      Chevalley_large_finite_root_centralizer_faithfulness_of_four_le τ K hK L (algebraMap K L)
    refine Subtype.ext (hC _ (x * S x).2 fun g hg => ?_)
    obtain ⟨u, hu, rfl⟩ := hg
    set w : adjointGroup τ K := ⟨u, hu⟩
    have hαα : α (α w) = w := by rw [← MulAut.mul_apply, hα2, MulAut.one_apply]
    have h1 : ι (α (α w)) = x * S x * ι w * (x * S x)⁻¹ := by
      rw [hα, hα, map_mul, map_mul, map_inv, hSS]
      group
    rw [hαα] at h1
    have h2 : x * S x * ι w = ι w * (x * S x) := by
      calc x * S x * ι w = (x * S x * ι w * (x * S x)⁻¹) * (x * S x) := by group
        _ = ι w * (x * S x) := by rw [← h1]
    exact congrArg Subtype.val h2
  obtain ⟨h, hR, hxh, -⟩ := exceptional_Lang_norm_one_descent S.toMonoidHom (m := 2)
    (by norm_num) hLang x (by simpa [List.range_succ] using hz)
  have hxh' : x = h⁻¹ * S h := hxh
  have hSh : S (S h) = h := hR
  have hhF : Units.map (entrywiseHom Fr) (h : ModGL τ L) = h := by rw [← hS2, hSh]
  obtain ⟨-, -, hnorml⟩ := Chevalley_Frobenius_fixed_ambient_normalizer τ K L Fr hFr
  have hmap : ((adjointGroup τ K).map (baseChangeGL (algebraMap K L))).map
      (MulAut.conj (h : ModGL τ L)).toMonoidHom =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    map_conj_eq_of_mem_normalizer (hnorml ⟨h.2, hhF⟩)
  let eH : adjointGroup τ K ≃* (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    Subgroup.equivMapOfInjective (adjointGroup τ K) (baseChangeGL (algebraMap K L))
      (baseChangeGL_injective _)
  have heH : ∀ u, ((eH u : (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) :
      ModGL τ L) = baseChangeGL (algebraMap K L) u := fun u =>
    Subgroup.coe_equivMapOfInjective_apply _ _ _ _
  let ψ : MulAut (adjointGroup τ K) :=
    eH.trans ((mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap).trans eH.symm)
  have hψ0 : ∀ u, baseChangeGL (algebraMap K L) (ψ u : ModGL τ K) =
      (h : ModGL τ L) * baseChangeGL (algebraMap K L) u * (h : ModGL τ L)⁻¹ := by
    intro u
    rw [← heH, ← heH]
    change ((eH (eH.symm (mulAutRestrict _ (MulAut.conj (h : ModGL τ L)) hmap (eH u))) :
      (adjointGroup τ K).map (baseChangeGL (algebraMap K L))) : ModGL τ L) = _
    rw [MulEquiv.apply_symm_apply, coe_mulAutRestrict, MulAut.conj_apply]
  have hψ : ∀ u, ι (ψ u) = h * ι u * h⁻¹ := fun u => Subtype.ext (hψ0 u)
  have hψinv : ∀ u, ι (ψ⁻¹ u) = h⁻¹ * ι u * h := by
    intro u
    have h1 := hψ (ψ⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    rw [h1]
    group
  refine ⟨ψ, MulEquiv.ext fun u => adjointBaseChangeHom_injective τ (algebraMap K L) ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, hψ, hα, hψinv, ← hβ, map_mul, map_mul, map_inv, hxh']
  group

theorem quadratic_involution_descent_of_lang
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (hK : 4 ≤ Nat.card K) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (S : MulAut (adjointGroup τ L))
    (hS2 : ∀ g, ((S (S g) : adjointGroup τ L) : ModGL τ L) = Units.map (entrywiseHom Fr) g)
    (hLang : ∀ y : adjointGroup τ L, ∃ h, y = h⁻¹ * S h) (β : MulAut (adjointGroup τ K))
    (hβ : ∀ u, S (adjointBaseChangeHom τ (algebraMap K L) u) =
      adjointBaseChangeHom τ (algebraMap K L) (β u))
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) :
    (∃ α : MulAut (adjointGroup τ K), ∀ u, (α u : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * (β u : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹) ∧
    ∀ α : MulAut (adjointGroup τ K), (∀ u, (α u : ModGL τ K) =
      (g : ModGL τ K) * rootDiagUnit τ a * (β u : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹) → α * α = 1 →
      ∃ ψ : MulAut (adjointGroup τ K), ψ * α * ψ⁻¹ = β ∧
        (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
          β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
        (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
            ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))),
          ∀ u, (e u : adjointGroup τ K) = ψ u) ∧
        (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom = Subgroup.centralizer {β} ∧
        ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
          ∀ γ, (e γ : MulAut (adjointGroup τ K)) = ψ * γ * ψ⁻¹ := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  refine ⟨⟨MulAut.conj g * rootDiagAut τ K a * β, fun u => ?_⟩, fun α hα hα2 => ?_⟩
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
    group
  set ι := adjointBaseChangeHom τ (algebraMap K L) with hιdef
  let dL : adjointGroup τ L :=
    ⟨rootDiagUnit τ fun i => Units.map (algebraMap K L).toMonoidHom (a i),
      (exceptional_Lang_adjoint_diagonal_lift τ L _).1⟩
  have hαx : ∀ u, ι (α u) = (ι g * dL) * S (ι u) * (ι g * dL)⁻¹ := by
    intro u
    apply Subtype.ext
    have hβu : ((S (ι u) : adjointGroup τ L) : ModGL τ L) =
        baseChangeGL (algebraMap K L) (β u : ModGL τ K) := congrArg Subtype.val (hβ u)
    rw [coe_adjointBaseChangeHom, hα, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_mul, hβu, coe_adjointBaseChangeHom, map_mul, map_mul, map_mul, map_mul, map_inv,
      map_inv, baseChangeGL_rootDiagUnit]
    rfl
  obtain ⟨ψ, hψ⟩ := exists_conj_eq_of_sq_eq_frobenius τ K hK L Fr hFr S hS2 hLang β hβ
    (ι g * dL) α hαx hα2
  exact ⟨ψ, hψ, fixed_centralizer_of_conj_eq hψ⟩


theorem even_exceptional_quadratic_field_graph_field_involution_descent
    {e : ℕ} (he : 1 ≤ e)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ (2 * e)) (δ : K →+* K)
    (hδ : ∀ c, δ c = c ^ 2 ^ e) :
    (∀ τ : Tag, ∃ β : MulAut (adjointGroup τ K),
      (∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K)) ∧
      ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        (∃ α : MulAut (adjointGroup τ K), ∀ u, (α u : ModGL τ K) =
          (g : ModGL τ K) * rootDiagUnit τ a * Units.map (entrywiseHom δ) (u : ModGL τ K) *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) ∧
        ∀ α : MulAut (adjointGroup τ K), (∀ u, (α u : ModGL τ K) =
          (g : ModGL τ K) * rootDiagUnit τ a * Units.map (entrywiseHom δ) (u : ModGL τ K) *
            (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹) →
          α * α = 1 → ∃ ψ : MulAut (adjointGroup τ K),
            (∀ u, ((ψ * α * ψ⁻¹) u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K)) ∧
            (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
              β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
            (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))) ≃*
                ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ K))),
              ∀ u, (e u : adjointGroup τ K) = ψ u) ∧
            (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
              Subgroup.centralizer {β} ∧
            ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
              ∀ γ, (e γ : MulAut (adjointGroup τ K)) = ψ * γ * ψ⁻¹) ∧
    (∃ β : MulAut (adjointGroup TwistTag.E6.tag K),
      (∀ u, (β u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹) ∧
      ∀ (g : adjointGroup TwistTag.E6.tag K) (a : Fin TwistTag.E6.tag.rank → Kˣ),
        (∃ α : MulAut (adjointGroup TwistTag.E6.tag K), ∀ u, (α u : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹) ∧
        ∀ α : MulAut (adjointGroup TwistTag.E6.tag K), (∀ u, (α u : ModGL TwistTag.E6.tag K) =
          (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
            diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
              (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
                (g : ModGL TwistTag.E6.tag K)⁻¹) →
          α * α = 1 → ∃ ψ : MulAut (adjointGroup TwistTag.E6.tag K),
            (∀ u, ((ψ * α * ψ⁻¹) u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
              Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
                (diagramMap TwistTag.E6 K)⁻¹) ∧
            (α.toMonoidHom.eqLocus (MonoidHom.id _)).map ψ.toMonoidHom =
              β.toMonoidHom.eqLocus (MonoidHom.id _) ∧
            (∃ e : ↥(α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))) ≃*
                ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag K))),
              ∀ u, (e u : adjointGroup TwistTag.E6.tag K) = ψ u) ∧
            (Subgroup.centralizer {α}).map (MulAut.conj ψ).toMonoidHom =
              Subgroup.centralizer {β} ∧
            ∃ e : ↥(Subgroup.centralizer {α}) ≃* ↥(Subgroup.centralizer {β}),
              ∀ γ, (e γ : MulAut (adjointGroup TwistTag.E6.tag K)) = ψ * γ * ψ⁻¹) := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * e) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  set Fe := iterateFrobenius (AlgebraicClosure K) 2 e with hFedef
  have hFe : ∀ c, Fe c = c ^ 2 ^ e := fun c => by rw [hFedef, iterateFrobenius_def]
  have hFr : ∀ c, (Fe.comp Fe) c = c ^ Nat.card K := fun c => by
    rw [RingHom.comp_apply, hFe, hFe, ← pow_mul, hK, ← pow_add, two_mul]
  have hFeι : Fe.comp (algebraMap K (AlgebraicClosure K)) =
      (algebraMap K (AlgebraicClosure K)).comp δ := by
    ext c
    rw [RingHom.comp_apply, RingHom.comp_apply, hFe, hδ, map_pow]
  have hFeGL : ∀ {τ : Tag} (u : ModGL τ K), Units.map (entrywiseHom Fe)
      (baseChangeGL (algebraMap K (AlgebraicClosure K)) u) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (Units.map (entrywiseHom δ) u) := by
    intro τ u
    rw [units_map_entrywiseHom_eq_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hFeι]
  have hFeFe : ∀ {τ : Tag} (g : ModGL τ (AlgebraicClosure K)), Units.map (entrywiseHom Fe)
      (Units.map (entrywiseHom Fe) g) = Units.map (entrywiseHom (Fe.comp Fe)) g := by
    intro τ g
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact entrywise_entrywise (R := AlgebraicClosure K) _ _ _
  let δ' : K ≃+* K := RingEquiv.ofBijective δ
    ⟨δ.injective, Finite.surjective_of_injective δ.injective⟩
  have hδ' : δ'.toRingHom = δ := RingHom.ext fun _ => rfl
  refine ⟨fun τ => ?_, ?_⟩
  ·
    obtain ⟨S, hS, hLang⟩ :=
      (exceptional_all_characteristic_field_Lang_surjectivity 2 (AlgebraicClosure K) e he).1 τ
    set β := entrywiseAdjointAut τ δ' with hβdef
    have hβu : ∀ u, (β u : ModGL τ K) = Units.map (entrywiseHom δ) (u : ModGL τ K) := fun u => by
      rw [hβdef, coe_entrywiseAdjointAut, hδ']
    have hS2 : ∀ g, ((S (S g) : adjointGroup τ (AlgebraicClosure K)) :
        ModGL τ (AlgebraicClosure K)) = Units.map (entrywiseHom (Fe.comp Fe)) g := fun g => by
      rw [hS, hS, hFeFe]
    have hβS : ∀ u, S (adjointBaseChangeHom τ (algebraMap K (AlgebraicClosure K)) u) =
        adjointBaseChangeHom τ (algebraMap K (AlgebraicClosure K)) (β u) := fun u => by
      apply Subtype.ext
      rw [hS, coe_adjointBaseChangeHom, coe_adjointBaseChangeHom, hFeGL, hβu]
    refine ⟨β, hβu, fun g a => ?_⟩
    obtain ⟨hex, hdesc⟩ := quadratic_involution_descent_of_lang τ K hK4 (AlgebraicClosure K)
      (Fe.comp Fe) hFr S hS2 hLang β hβS g a
    refine ⟨?_, fun α hα hα2 => ?_⟩
    · obtain ⟨α, hα⟩ := hex
      exact ⟨α, fun u => by rw [hα, hβu]⟩
    · obtain ⟨ψ, hψ, hrest⟩ := hdesc α (fun u => by rw [hα, hβu]) hα2
      exact ⟨ψ, fun u => by rw [hψ, hβu], hrest⟩
  ·
    obtain ⟨S, hS, hLang⟩ :=
      (exceptional_all_characteristic_field_Lang_surjectivity 2 (AlgebraicClosure K) e he).2
        TwistTag.E6 1
    simp only [zpow_one] at hS
    set β := diagramConjAut TwistTag.E6 K * entrywiseAdjointAut TwistTag.E6.tag δ' with hβdef
    have hβu : ∀ u, (β u : ModGL TwistTag.E6.tag K) = diagramMap TwistTag.E6 K *
        Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) * (diagramMap TwistTag.E6 K)⁻¹ :=
      fun u => by
      rw [hβdef, MulAut.mul_apply, coe_diagramConjAut, coe_entrywiseAdjointAut, hδ']
    have hP2 : diagramMap TwistTag.E6 (AlgebraicClosure K) *
        diagramMap TwistTag.E6 (AlgebraicClosure K) = 1 := by
      have h := diagramMap_pow_order TwistTag.E6 (AlgebraicClosure K)
      rwa [show TwistTag.E6.order = 2 from rfl, sq] at h
    have hFeP : Units.map (entrywiseHom Fe) (diagramMap TwistTag.E6 (AlgebraicClosure K)) =
        diagramMap TwistTag.E6 (AlgebraicClosure K) :=
      Units.ext (entrywise_diagramMap Fe)
    have hS2 : ∀ g, ((S (S g) : adjointGroup TwistTag.E6.tag (AlgebraicClosure K)) :
        ModGL TwistTag.E6.tag (AlgebraicClosure K)) =
          Units.map (entrywiseHom (Fe.comp Fe)) g := fun g => by
      rw [hS, hS, map_mul, map_mul, map_inv, hFeP, hFeFe]
      calc diagramMap TwistTag.E6 (AlgebraicClosure K) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              Units.map (entrywiseHom (Fe.comp Fe)) (g : ModGL TwistTag.E6.tag _) *
              (diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹ =
          (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              diagramMap TwistTag.E6 (AlgebraicClosure K)) *
            Units.map (entrywiseHom (Fe.comp Fe)) (g : ModGL TwistTag.E6.tag _) *
            (diagramMap TwistTag.E6 (AlgebraicClosure K) *
              diagramMap TwistTag.E6 (AlgebraicClosure K))⁻¹ := by group
        _ = _ := by rw [hP2, one_mul, inv_one, mul_one]
    have hβS : ∀ u, S (adjointBaseChangeHom TwistTag.E6.tag (algebraMap K (AlgebraicClosure K)) u)
        = adjointBaseChangeHom TwistTag.E6.tag (algebraMap K (AlgebraicClosure K)) (β u) :=
      fun u => by
        apply Subtype.ext
        rw [hS, coe_adjointBaseChangeHom, coe_adjointBaseChangeHom, hFeGL, hβu, map_mul,
          map_mul, map_inv, baseChangeGL_diagramMap]
    refine ⟨β, hβu, fun g a => ?_⟩
    obtain ⟨hex, hdesc⟩ := quadratic_involution_descent_of_lang TwistTag.E6.tag K hK4
      (AlgebraicClosure K) (Fe.comp Fe) hFr S hS2 hLang β hβS g a
    have hform : ∀ u, (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
        (β u : ModGL TwistTag.E6.tag K) * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
          (g : ModGL TwistTag.E6.tag K)⁻¹ =
        (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a *
          diagramMap TwistTag.E6 K * Units.map (entrywiseHom δ) (u : ModGL TwistTag.E6.tag K) *
            (diagramMap TwistTag.E6 K)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
              (g : ModGL TwistTag.E6.tag K)⁻¹ := fun u => by
      rw [hβu]
      group
    refine ⟨?_, fun α hα hα2 => ?_⟩
    · obtain ⟨α, hα⟩ := hex
      exact ⟨α, fun u => by rw [hα, hform]⟩
    · obtain ⟨ψ, hψ, hrest⟩ := hdesc α (fun u => by rw [hα, hform]) hα2
      exact ⟨ψ, fun u => by rw [hψ, hβu], hrest⟩

end CFSG.LieType.Chevalley

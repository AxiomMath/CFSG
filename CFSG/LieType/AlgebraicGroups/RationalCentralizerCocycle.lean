module

public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleComponents
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycleLang
public import CFSG.LieType.AlgebraicGroups.ToralCentralizerIdentity
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley WithConv Topology

open scoped CFSG.ConvolutionPoints

section Fixed

variable {G : Type*} [Group G]

abbrev fixedPointsIn (X : Subgroup G) (S : G →* G) : Subgroup G :=
  X ⊓ S.eqLocus (MonoidHom.id G)

theorem mem_fixedPointsIn {X : Subgroup G} {S : G →* G} {y : G} :
    y ∈ fixedPointsIn X S ↔ y ∈ X ∧ S y = y :=
  Iff.rfl

end Fixed

section Twist

variable {τ : Tag} {k : Type} [Field k]

variable (τ k) in
@[expose] def IsDiagramTwistMatrix (D : ModGL τ k) : Prop :=
  D = 1 ∨ ∃ (t : TwistTag) (j : ℤ) (h : t.tag = τ), D = h ▸ (diagramMap t k ^ j)

theorem IsDiagramTwistMatrix.map_conj_eq
    {D : ModGL τ k} (hD : IsDiagramTwistMatrix τ k D) :
    (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k := by
  rcases hD with rfl | ⟨t, j, rfl, rfl⟩
  · exact map_conj_one_adjointGroup τ k
  · exact map_conj_diagramMap_zpow t k j

end Twist

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p] {τ : Tag}

theorem rational_centralizer_cocycle_reduction_of_map_conj
    (hp : p ≠ 2) {e : ℕ}
    (he : 1 ≤ e) {D : ModGL τ k}
    (hD : (adjointGroup τ k).map (MulAut.conj D).toMonoidHom = adjointGroup τ k)
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    {H : Subgroup (ModGL τ k)} (hHR : H ≤ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    [(H.subgroupOf (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))).Normal]
    [Group.IsSolvable (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⧸
      H.subgroupOf (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))]
    {x : ModGL τ k} {a : Fin τ.rank → kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) {g : ModGL τ k}
    (hg : g ∈ adjointGroup τ k) (hgx : g * x * g⁻¹ = rootDiagUnit τ a)
    (ht : frobTwistGL τ k p e D (rootDiagUnit τ a) = rootDiagUnit τ a)
    {v : ModGL τ k} (hv : v ∈ toralCentralizer τ k a)
    (hcv : ∃ m ∈ toralRootGroup τ k a, g * (frobTwistGL τ k p e D g)⁻¹ = m * v) :
    ∃ z ∈ toralRootGroup τ k a,
      z * g * (frobTwistGL τ k p e D (z * g))⁻¹ = v ∧
      (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⊓
          Subgroup.centralizer {x}).map (MulAut.conj (z * g)).toMonoidHom =
        fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
      Finite (fixedPointsIn (toralRootGroup τ k a)
        ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))) ∧
      fixedPointsIn (toralRootGroup τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ≤
        fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
      ((fixedPointsIn (toralRootGroup τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))).subgroupOf
        (fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))).Normal ∧
      ∀ ℓ : ℕ, ℓ.Prime →
        (∀ L : Subgroup (ModGL τ k),
          (L ≤ H ⊓ Subgroup.centralizer {x} ∧
            CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x}))) ↔
          (L.map (MulAut.conj (z * g)).toMonoidHom ≤ fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
            CFSG.IsPComponent ℓ ((L.map (MulAut.conj (z * g)).toMonoidHom).subgroupOf
              (fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))))) ∧
        (∃ eqv : {L : Subgroup (ModGL τ k) // L ≤ H ⊓ Subgroup.centralizer {x} ∧
              CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x}))} ≃
            {L : Subgroup (ModGL τ k) // L ≤ fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
              CFSG.IsPComponent ℓ (L.subgroupOf (fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))))},
          ∀ L, (eqv L : Subgroup (ModGL τ k)) =
            (L : Subgroup (ModGL τ k)).map (MulAut.conj (z * g)).toMonoidHom) ∧
        ((∀ L : Subgroup (ModGL τ k), L ≤ fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) →
            CFSG.IsPComponent ℓ (L.subgroupOf (fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))) →
            CFSG.IsQuasisimple L) →
          ∀ L : Subgroup (ModGL τ k), L ≤ H ⊓ Subgroup.centralizer {x} →
            CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x})) →
            CFSG.IsQuasisimple L) := by
  classical
  set F := frobTwistGL τ k p e D with hF
  set R := fixedPointsIn (adjointGroup τ k) F with hR
  set S := (MulAut.conj v).toMonoidHom.comp F with hS
  set Z := toralCentralizer τ k a with hZ
  set M := toralRootGroup τ k a with hM_def
  have hk : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp
  obtain ⟨-, ⟨hM, hcc, hMsm, -, -⟩, ⟨hMZ, hMn, -, -, -⟩, -⟩ :=
    exceptional_toral_centralizer_identity_component τ k hk a ha
  have hFG : ∀ y ∈ adjointGroup τ k, F y ∈ adjointGroup τ k := fun y hy =>
    conj_mem_adjointGroup_of_map_eq hD _ (entrywiseFrobGL_mem p e hy)
  have hFZ : ∀ y ∈ Z, F y ∈ Z := by
    intro y hy
    obtain ⟨hyG, hyc⟩ := mem_toralCentralizer.1 hy
    refine mem_toralCentralizer.2 ⟨hFG y hyG, ?_⟩
    rw [← ht, ← map_inv, ← map_mul, ← map_mul, hyc]
  have hSeq : ∀ y, S y = frobTwistGL τ k p e (v * D) y := by
    intro y
    simp only [hS, hF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      mul_inv_rev]
    group
  have hSZ : ∀ y ∈ Z, S y ∈ Z := fun y hy =>
    mul_mem (mul_mem hv (hFZ y hy)) (inv_mem hv)
  have hSM : ∀ y ∈ M, frobTwistGL τ k p e (v * D) y ∈ M := fun y hy =>
    frobTwistGL_mem_of_connectedComponentIn p e (v * D) hM hcc
      (fun g hg => by
        rw [← hSeq]
        exact hSZ g (hMZ hg)) hy
  obtain ⟨m, hm, hcm⟩ := hcv
  obtain ⟨z, hzM, hz⟩ := exists_eq_inv_mul_frobTwistGL p he (v * D) hM hMsm hSM hm
  rw [← hSeq] at hz
  set g₁ := z * g with hg₁_def
  have hg₁ : g₁ * (F g₁)⁻¹ = v := by
    have hSz : S z = v * F z * v⁻¹ := rfl
    rw [hg₁_def, map_mul, mul_inv_rev]
    calc z * g * ((F g)⁻¹ * (F z)⁻¹) = z * (g * (F g)⁻¹) * (F z)⁻¹ := by group
      _ = z * (z⁻¹ * S z * v) * (F z)⁻¹ := by rw [hcm, hz]
      _ = v := by rw [hSz]; group
  have hzZ : z ∈ Z := hMZ hzM
  have hg₁G : g₁ ∈ adjointGroup τ k := mul_mem (mem_toralCentralizer.1 hzZ).1 hg
  have hzt : z * rootDiagUnit τ a * z⁻¹ = rootDiagUnit τ a := by
    have hzc := (mem_toralCentralizer.1 hzZ).2
    calc z * rootDiagUnit τ a * z⁻¹ =
        (rootDiagUnit τ a * z * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a * z⁻¹ := by rw [hzc]
      _ = rootDiagUnit τ a := by group
  have hg₁x : g₁ * x * g₁⁻¹ = rootDiagUnit τ a := by
    calc g₁ * x * g₁⁻¹ = z * (g * x * g⁻¹) * z⁻¹ := by rw [hg₁_def]; group
      _ = rootDiagUnit τ a := by rw [hgx, hzt]
  have hFg₁ : F g₁ = v⁻¹ * g₁ := by
    calc F g₁ = (g₁ * (F g₁)⁻¹)⁻¹ * g₁ := by group
      _ = v⁻¹ * g₁ := by rw [hg₁]
  have hSconj : ∀ u, S (g₁ * u * g₁⁻¹) = g₁ * F u * g₁⁻¹ := by
    intro u
    change v * F (g₁ * u * g₁⁻¹) * v⁻¹ = _
    rw [map_mul, map_mul, map_inv, hFg₁]
    group
  have hconj : (R ⊓ Subgroup.centralizer {x}).map (MulAut.conj g₁).toMonoidHom =
      fixedPointsIn Z S := by
    ext y
    rw [Subgroup.mem_map, mem_fixedPointsIn]
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨⟨huG, huF⟩, hux⟩ := Subgroup.mem_inf.1 hu
      rw [Subgroup.mem_centralizer_singleton_iff] at hux
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      refine ⟨mem_toralCentralizer.2 ⟨mul_mem (mul_mem hg₁G huG) (inv_mem hg₁G), ?_⟩, ?_⟩
      · rw [← hg₁x]
        calc g₁ * x * g₁⁻¹ * (g₁ * u * g₁⁻¹) * (g₁ * x * g₁⁻¹)⁻¹ =
            g₁ * (x * u) * x⁻¹ * g₁⁻¹ := by group
          _ = g₁ * u * g₁⁻¹ := by rw [← hux]; group
      · rw [hSconj]
        exact congrArg (fun w => g₁ * w * g₁⁻¹) huF
    · rintro ⟨hyZ, hyS⟩
      obtain ⟨hyG, hyc⟩ := mem_toralCentralizer.1 hyZ
      refine ⟨g₁⁻¹ * y * g₁, Subgroup.mem_inf.2 ⟨mem_fixedPointsIn.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact mul_mem (mul_mem (inv_mem hg₁G) hyG) hg₁G
      · have h := hSconj (g₁⁻¹ * y * g₁)
        rw [show g₁ * (g₁⁻¹ * y * g₁) * g₁⁻¹ = y by group, hyS] at h
        change F (g₁⁻¹ * y * g₁) = g₁⁻¹ * y * g₁
        calc F (g₁⁻¹ * y * g₁) = g₁⁻¹ * (g₁ * F (g₁⁻¹ * y * g₁) * g₁⁻¹) * g₁ := by group
          _ = g₁⁻¹ * y * g₁ := by rw [← h]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : y * (g₁ * x * g₁⁻¹) = (g₁ * x * g₁⁻¹) * y := by
          rw [hg₁x]
          calc y * rootDiagUnit τ a =
              (rootDiagUnit τ a * y * (rootDiagUnit τ a)⁻¹) * rootDiagUnit τ a := by rw [hyc]
            _ = rootDiagUnit τ a * y := by group
        calc g₁⁻¹ * y * g₁ * x = g₁⁻¹ * (y * (g₁ * x * g₁⁻¹)) * g₁ := by group
          _ = g₁⁻¹ * ((g₁ * x * g₁⁻¹) * y) * g₁ := by rw [hc]
          _ = x * (g₁⁻¹ * y * g₁) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
  have hCRfin : Finite (R ⊓ Subgroup.centralizer {x} : Subgroup (ModGL τ k)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_left : R ⊓ Subgroup.centralizer {x} ≤ R))
  have hZSfin : Finite (fixedPointsIn Z S) := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj g₁).subgroupMap _).toEquiv
  have hQZ : fixedPointsIn M S ≤ fixedPointsIn Z S := inf_le_inf_right _ hMZ
  have hQfin : Finite (fixedPointsIn M S) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hQZ)
  have hQn : ((fixedPointsIn M S).subgroupOf (fixedPointsIn Z S)).Normal := by
    constructor
    rintro ⟨n, hnZS⟩ hn ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnM, hnS⟩ := mem_fixedPointsIn.1 hn
    obtain ⟨hyZ, hyS⟩ := mem_fixedPointsIn.1 hy
    change y * n * y⁻¹ ∈ fixedPointsIn M S
    refine mem_fixedPointsIn.2 ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.1 (toralCentralizer_le_normalizer a hyZ) n).1 hnM
    · rw [map_mul, map_mul, map_inv, hyS, hnS]
  have hCH : H ⊓ Subgroup.centralizer {x} = H ⊓ (R ⊓ Subgroup.centralizer {x}) := by
    rw [← inf_assoc, inf_eq_left.2 hHR]
  have hQ' : fixedPointsIn M S = M ⊓ fixedPointsIn Z S := by
    rw [fixedPointsIn, fixedPointsIn, ← inf_assoc, inf_eq_left.2 hMZ]
  have := normal_inf_subgroupOf (H := H) (B := R ⊓ Subgroup.centralizer {x}) (R := R) inf_le_left
  have := isSolvable_quotient_inf_subgroupOf (H := H) (B := R ⊓ Subgroup.centralizer {x})
    (R := R) inf_le_left
  have := normal_inf_subgroupOf (H := M) (B := fixedPointsIn Z S) (R := Z) inf_le_left
  have : Group.IsSolvable (Z ⧸ M.subgroupOf Z) :=
    Group.isSolvable_of_comm (toralQuotient_mul_comm hk ha)
  have := isSolvable_quotient_inf_subgroupOf (H := M) (B := fixedPointsIn Z S) (R := Z)
    inf_le_left
  have hchain : ∀ ℓ : ℕ, ℓ.Prime → ∀ L : Subgroup (ModGL τ k),
      (L ≤ H ⊓ Subgroup.centralizer {x} ∧
        CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x}))) ↔
      (L.map (MulAut.conj g₁).toMonoidHom ≤ fixedPointsIn M S ∧
        CFSG.IsPComponent ℓ ((L.map (MulAut.conj g₁).toMonoidHom).subgroupOf
          (fixedPointsIn M S))) := by
    intro ℓ hℓ L
    rw [hCH, hQ', ← isPComponent_subgroupOf_iff_of_isSolvable
        (A := H ⊓ (R ⊓ Subgroup.centralizer {x})) inf_le_right ℓ hℓ L,
      isPComponent_subgroupOf_map_conj_iff g₁ hconj ℓ hℓ L,
      isPComponent_subgroupOf_iff_of_isSolvable (A := M ⊓ fixedPointsIn Z S) inf_le_right ℓ hℓ]
  refine ⟨z, hzM, hg₁, hconj, hQfin, hQZ, hQn, fun ℓ hℓ => ⟨hchain ℓ hℓ,
    ⟨Equiv.subtypeEquiv (MulEquiv.mapSubgroup (MulAut.conj g₁)).toEquiv fun L => hchain ℓ hℓ L,
      fun L => rfl⟩, ?_⟩⟩
  intro hQq L hL hLc
  obtain ⟨hL', hLc'⟩ := (hchain ℓ hℓ L).1 ⟨hL, hLc⟩
  exact (isQuasisimple_congr ((MulAut.conj g₁).subgroupMap L)).2 (hQq _ hL' hLc')

variable (τ k) in
theorem exceptional_rational_centralizer_component_cocycle_reduction
    (hp : p ≠ 2) (e : ℕ)
    (he : 1 ≤ e) (D : ModGL τ k) (hD : IsDiagramTwistMatrix τ k D)
    (hRfin : Finite (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))
    (H : Subgroup (ModGL τ k)) (hHR : H ≤ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    [(H.subgroupOf (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))).Normal]
    [Group.IsSolvable (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⧸
      H.subgroupOf (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D)))]
    (x : ModGL τ k) (_hxR : x ∈ fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D))
    (_hx : x ^ 2 = 1) (a : Fin τ.rank → kˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) (g : ModGL τ k)
    (hg : g ∈ adjointGroup τ k) (hgx : g * x * g⁻¹ = rootDiagUnit τ a)
    (ht : frobTwistGL τ k p e D (rootDiagUnit τ a) = rootDiagUnit τ a)
    (v : ModGL τ k) (hv : v ∈ toralCentralizer τ k a)
    (hcv : ∃ m ∈ toralRootGroup τ k a, g * (frobTwistGL τ k p e D g)⁻¹ = m * v) :
    ∃ z ∈ toralRootGroup τ k a,
      z * g * (frobTwistGL τ k p e D (z * g))⁻¹ = v ∧
      (fixedPointsIn (adjointGroup τ k) (frobTwistGL τ k p e D) ⊓
          Subgroup.centralizer {x}).map (MulAut.conj (z * g)).toMonoidHom =
        fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
      Finite (fixedPointsIn (toralRootGroup τ k a)
        ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))) ∧
      fixedPointsIn (toralRootGroup τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ≤
        fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
      ((fixedPointsIn (toralRootGroup τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))).subgroupOf
        (fixedPointsIn (toralCentralizer τ k a)
          ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))).Normal ∧
      ∀ ℓ : ℕ, ℓ.Prime →
        (∀ L : Subgroup (ModGL τ k),
          (L ≤ H ⊓ Subgroup.centralizer {x} ∧
            CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x}))) ↔
          (L.map (MulAut.conj (z * g)).toMonoidHom ≤ fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
            CFSG.IsPComponent ℓ ((L.map (MulAut.conj (z * g)).toMonoidHom).subgroupOf
              (fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))))) ∧
        (∃ eqv : {L : Subgroup (ModGL τ k) // L ≤ H ⊓ Subgroup.centralizer {x} ∧
              CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x}))} ≃
            {L : Subgroup (ModGL τ k) // L ≤ fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) ∧
              CFSG.IsPComponent ℓ (L.subgroupOf (fixedPointsIn (toralRootGroup τ k a)
                ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D))))},
          ∀ L, (eqv L : Subgroup (ModGL τ k)) =
            (L : Subgroup (ModGL τ k)).map (MulAut.conj (z * g)).toMonoidHom) ∧
        ((∀ L : Subgroup (ModGL τ k), L ≤ fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)) →
            CFSG.IsPComponent ℓ (L.subgroupOf (fixedPointsIn (toralRootGroup τ k a)
              ((MulAut.conj v).toMonoidHom.comp (frobTwistGL τ k p e D)))) →
            CFSG.IsQuasisimple L) →
          ∀ L : Subgroup (ModGL τ k), L ≤ H ⊓ Subgroup.centralizer {x} →
            CFSG.IsPComponent ℓ (L.subgroupOf (H ⊓ Subgroup.centralizer {x})) →
            CFSG.IsQuasisimple L) :=
  rational_centralizer_cocycle_reduction_of_map_conj p hp he hD.map_conj_eq hRfin hHR ha hg hgx ht
    hv hcv

end CFSG.LieType.AlgebraicGroups

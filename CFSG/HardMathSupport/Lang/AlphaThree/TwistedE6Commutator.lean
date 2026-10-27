module

public import CFSG.HardMathSupport.Lang.AlphaThree.TwistedE6Orbits
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyTriangle

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.AlphaThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem commutator_mul_mul {G : Type*} [Group G] {X Y Z W : G} (hYZ : Commute Y Z)
    (hXW : Commute X W) (hqX : Commute ⁅Y, W⁆ X) (hqZ : Commute ⁅Y, W⁆ Z) :
    ⁅X * Y, Z * W⁆ = ⁅X, Z⁆ * ⁅Y, W⁆ := by
  set q := ⁅Y, W⁆ with hq
  have h2 : Y * W * Y⁻¹ = q * W := by simp only [hq, commutatorElement_def]; group
  have h1 : Y * Z * W * Y⁻¹ = Z * (q * W) := by
    rw [hYZ.eq, ← h2]; group
  have h3 : X * (Z * (q * W)) * X⁻¹ = (X * Z * X⁻¹) * q * W := by
    have e1 : X * W * X⁻¹ = W := by rw [hXW.eq]; group
    have e2 : X * q * X⁻¹ = q := by rw [hqX.symm.eq]; group
    calc X * (Z * (q * W)) * X⁻¹ = (X * Z * X⁻¹) * (X * q * X⁻¹) * (X * W * X⁻¹) := by group
      _ = (X * Z * X⁻¹) * q * W := by rw [e1, e2]
  have h4 : Z * q * Z⁻¹ = q := by rw [hqZ.symm.eq]; group
  calc ⁅X * Y, Z * W⁆ = X * (Y * Z * W * Y⁻¹) * X⁻¹ * W⁻¹ * Z⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = (X * (Z * (q * W)) * X⁻¹) * W⁻¹ * Z⁻¹ := by rw [h1]
    _ = ((X * Z * X⁻¹) * q * W) * W⁻¹ * Z⁻¹ := by rw [h3]
    _ = (X * Z * X⁻¹ * Z⁻¹) * (Z * q * Z⁻¹) := by group
    _ = ⁅X, Z⁆ * q := by rw [h4]; simp only [commutatorElement_def]

theorem exists_add_smul_eq {K : Type*} [Field K] (σ : K ≃+* K) (hσσ : ∀ c, σ (σ c) = c)
    (hσ1 : ∃ c, σ c ≠ c) {s : K} (hs : s = 1 ∨ s = -1) {e : K} (he : σ e = s * e) :
    ∃ c : K, e = c + s * σ c := by
  have hss : s * s = 1 := by rcases hs with h | h <;> simp [h]
  have hσs : σ s = s := by rcases hs with h | h <;> simp [h]
  by_cases h2 : (2 : K) = 0
  · have hs1 : s = 1 := by
      rcases hs with h | h
      · exact h
      · rw [h]; linear_combination -h2
    subst hs1
    obtain ⟨δ, hδ⟩ := hσ1
    have ht : δ + σ δ ≠ 0 := by
      intro h
      apply hδ
      linear_combination h - h2 * δ
    have hσt : σ (δ + σ δ) = δ + σ δ := by rw [map_add, hσσ]; ring
    refine ⟨e / (δ + σ δ) * δ, ?_⟩
    have hσc : σ (e / (δ + σ δ) * δ) = e / (δ + σ δ) * σ δ := by
      rw [map_mul, map_div₀, he, hσt, one_mul]
    rw [hσc, one_mul]
    field_simp
  · have h2' : (2 : K) ≠ 0 := h2
    refine ⟨e / 2, ?_⟩
    have : σ (e / 2) = s * e / 2 := by rw [map_div₀, he, map_ofNat]
    rw [this]
    field_simp
    linear_combination (-(e)) * hss


section E6

variable {K : Type} [Field K] {σ : K ≃+* K}

theorem commute_pinnedX_of_noSum {x y : E6Vec} (hx : IsRoot TwistTag.E6.tag x)
    (hy : IsRoot TwistTag.E6.tag y) (h : NoSum x y) (c d : K) :
    Commute (pinnedX TwistTag.E6.tag K x c) (pinnedX TwistTag.E6.tag K y d) :=
  (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag (Or.inr (Or.inl rfl)) hx hy h.1
    h.2.1).2 (fun hr => h.2.2 (mem_rootFinset.2 hr)) K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _
    (mem_rootSubgroup.2 ⟨d, rfl⟩)

theorem commutator_pinnedX {a b : E6Vec} (ha : IsRoot TwistTag.E6.tag a)
    (hb : IsRoot TwistTag.E6.tag b) (hne : a ≠ b) (hne' : a ≠ -b)
    (hsum : IsRoot TwistTag.E6.tag (a + b)) :
    ∃ N : K, (N = 1 ∨ N = -1) ∧ ∀ c d : K, ⁅pinnedX TwistTag.E6.tag K a c,
      pinnedX TwistTag.E6.tag K b d⁆ = pinnedX TwistTag.E6.tag K (a + b) (N * c * d) := by
  obtain ⟨hC, hcomm⟩ := (simply_laced_root_commutator_unit.{0} TwistTag.E6.tag
    (Or.inr (Or.inl rfl)) ha hb hne hne').1 hsum
  refine ⟨(commConst TwistTag.E6.tag a b (1, 1) : K), ?_, hcomm K⟩
  rcases hC with h | h <;> simp [h]

theorem twistHom_pinnedX_E6 {γ : E6Vec} (hγ : IsRoot TwistTag.E6.tag γ) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K, twistHom TwistTag.E6 K σ.toRingHom
      (pinnedX TwistTag.E6.tag K γ c) = pinnedX TwistTag.E6.tag K (rhoE6 γ) (ε * σ c) := by
  obtain ⟨ε, he, hε⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.E6 hγ
  refine ⟨ε, he, fun c => ?_⟩
  have h1 : twistHom TwistTag.E6 K σ.toRingHom (pinnedX TwistTag.E6.tag K γ c) =
      diagramMap TwistTag.E6 K * Units.map (entrywiseHom σ.toRingHom)
        (pinnedX TwistTag.E6.tag K γ c) * (diagramMap TwistTag.E6 K)⁻¹ := rfl
  rw [h1, show Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.E6.tag K γ c) =
    pinnedX TwistTag.E6.tag K γ (σ c) from Units.ext (entrywise_pinnedX σ.toRingHom γ c), hε]
  rfl

theorem isRoot_rhoE6 {γ : E6Vec} (hγ : IsRoot TwistTag.E6.tag γ) :
    IsRoot TwistTag.E6.tag (rhoE6 γ) := hγ.permLattice TwistTag.E6.cartan_perm

open CFSG.SeitzReduction.TwistedE6Pilot (twistHom_twistHom_E6)


theorem exists_orbitElt (hσσ : ∀ c, σ (σ c) = c) {α : E6Vec} (hα : IsRoot TwistTag.E6.tag α)
    (hn : NoSum α (rhoE6 α)) (c : K) :
    ∃ w : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (w : ModGL TwistTag.E6.tag K) = pinnedX TwistTag.E6.tag K α c *
        twistHom TwistTag.E6 K σ.toRingHom (pinnedX TwistTag.E6.tag K α c) ∧
      (w : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec) := by
  obtain ⟨ε, -, hF⟩ := twistHom_pinnedX_E6 (σ := σ) hα
  have hρ : IsRoot TwistTag.E6.tag (rhoE6 α) := isRoot_rhoE6 hα
  set X := pinnedX TwistTag.E6.tag K α c with hX
  have hFX : twistHom TwistTag.E6 K σ.toRingHom X =
      pinnedX TwistTag.E6.tag K (rhoE6 α) (ε * σ c) := hF c
  have hcomm : Commute X (twistHom TwistTag.E6 K σ.toRingHom X) := by
    rw [hFX]
    exact commute_pinnedX_of_noSum hα hρ hn c _
  have hF2 : twistHom TwistTag.E6 K σ.toRingHom (twistHom TwistTag.E6 K σ.toRingHom X) = X :=
    twistHom_twistHom_E6 (σ := σ.toRingHom) hσσ X
  have hFw : twistHom TwistTag.E6 K σ.toRingHom (X * twistHom TwistTag.E6 K σ.toRingHom X) =
      X * twistHom TwistTag.E6 K σ.toRingHom X := by
    rw [map_mul, hF2]
    exact hcomm.eq.symm
  have hadj : X * twistHom TwistTag.E6 K σ.toRingHom X ∈ adjointGroup TwistTag.E6.tag K := by
    refine mul_mem (pinnedX_mem_adjointGroup _ _) ?_
    rw [hFX]
    exact pinnedX_mem_adjointGroup _ _
  have hΓ : X * twistHom TwistTag.E6 K σ.toRingHom X ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom :=
    (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hadj, hFw⟩
  have hspan : X * twistHom TwistTag.E6 K σ.toRingHom X ∈
      rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec) := by
    refine mul_mem (pinnedX_mem_rootSpan (by simp) _) ?_
    rw [hFX]
    exact pinnedX_mem_rootSpan (by simp) _
  have hG : X * twistHom TwistTag.E6 K σ.toRingHom X ∈
      graphFixedRootGroup TwistTag.E6 K σ.toRingHom := by
    rcases IsRoot.height_pos_or_neg hα with hpos | hneg
    · have h1 : X ∈ posUnipotent TwistTag.E6.tag K :=
        pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β}) ⟨hα, hpos⟩ c
      have h2 : twistHom TwistTag.E6 K σ.toRingHom X ∈ posUnipotent TwistTag.E6.tag K := by
        rw [hFX]
        exact pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ 0 < height β})
          ⟨hρ, by rw [rhoE6, height_permLattice]; exact hpos⟩ _
      exact graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
        ⟨mul_mem h1 h2, hΓ⟩)
    · have h1 : X ∈ negUnipotent TwistTag.E6.tag K :=
        pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ height β < 0}) ⟨hα, hneg⟩ c
      have h2 : twistHom TwistTag.E6 K σ.toRingHom X ∈ negUnipotent TwistTag.E6.tag K := by
        rw [hFX]
        exact pinnedX_mem_rootSpan (S := {β | IsRoot TwistTag.E6.tag β ∧ height β < 0})
          ⟨hρ, by rw [rhoE6, height_permLattice]; exact hneg⟩ _
      exact graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _ (Subgroup.mem_inf.2
        ⟨mul_mem h1 h2, hΓ⟩)
  exact ⟨⟨_, hG⟩, rfl, hspan⟩

theorem bad_orbit_mem_of_good (hσσ : ∀ c, σ (σ c) = c) (hσ1 : ∃ c, σ c ≠ c)
    (M : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hM : ∀ α : E6Vec, IsRoot TwistTag.E6.tag α → PairGood α →
      ∀ u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        (u : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec) →
          u ∈ M) :
    ∀ γ ∈ badRoots, ∀ u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      (u : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K ({γ} : Set E6Vec) → u ∈ M := by
  intro γ hγ u hu
  have hγR : IsRoot TwistTag.E6.tag γ := mem_rootFinset.1 (not_pairGood_of_mem_badRoots γ hγ).1
  obtain ⟨t, ht, rfl⟩ := badDecomp_covers γ hγ
  obtain ⟨ha, hb, hab, -, -, -, hPa, hPb, -, -⟩ := badDecomp_ok t ht
  obtain ⟨hnaρ, hnbρ, hnρab, hnaρb, hnγa, hnγb, hane, hane', hργ⟩ := badDecomp_comm_ok t ht
  obtain ⟨γ, a, b⟩ := t
  simp only at ha hb hab hPa hPb hnaρ hnbρ hnρab hnaρb hnγa hnγb hane hane' hργ hγR hu
  have haR : IsRoot TwistTag.E6.tag a := mem_rootFinset.1 ha
  have hbR : IsRoot TwistTag.E6.tag b := mem_rootFinset.1 hb
  have hρa := isRoot_rhoE6 haR
  have hρb := isRoot_rhoE6 hbR
  set F := twistHom TwistTag.E6 K σ.toRingHom with hFdef
  obtain ⟨N, hN, hcomm⟩ := commutator_pinnedX (K := K) haR hbR hane hane'
    (by rw [hab]; exact hγR)
  obtain ⟨εγ, hεγ, hFγ⟩ := twistHom_pinnedX_E6 (σ := σ) hγR
  obtain ⟨εa, -, hFa⟩ := twistHom_pinnedX_E6 (σ := σ) haR
  obtain ⟨εb, -, hFb⟩ := twistHom_pinnedX_E6 (σ := σ) hbR
  have hNN : N * N = 1 := by rcases hN with h | h <;> simp [h]
  have hσN : σ N = N := by rcases hN with h | h <;> simp [h]
  have hεs : εγ = 1 ∨ εγ = -1 := mul_self_eq_one_iff.1 hεγ
  have hσε : σ εγ = εγ := by rcases hεs with h | h <;> simp [h]
  have key : ∀ c : K, pinnedX TwistTag.E6.tag K γ (N * c + εγ * (N * σ c)) ∈
      Subgroup.map (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype M := by
    intro c
    obtain ⟨w₁, hw₁, hs₁⟩ := exists_orbitElt (σ := σ) hσσ haR hnaρ c
    obtain ⟨w₂, hw₂, hs₂⟩ := exists_orbitElt (σ := σ) hσσ hbR hnbρ 1
    have hm₁ := hM a haR hPa w₁ hs₁
    have hm₂ := hM b hbR hPb w₂ hs₂
    refine ⟨⁅w₁, w₂⁆, ?_, ?_⟩
    · rw [commutatorElement_def]
      exact M.mul_mem (M.mul_mem (M.mul_mem hm₁ hm₂) (M.inv_mem hm₁)) (M.inv_mem hm₂)
    · set X := pinnedX TwistTag.E6.tag K a c with hX
      set Z := pinnedX TwistTag.E6.tag K b 1 with hZ
      have hFX : F X = pinnedX TwistTag.E6.tag K (rhoE6 a) (εa * σ c) := hFa c
      have hFZ : F Z = pinnedX TwistTag.E6.tag K (rhoE6 b) (εb * σ 1) := hFb 1
      have hp : ⁅X, Z⁆ = pinnedX TwistTag.E6.tag K γ (N * c * 1) := by
        rw [hX, hZ, hcomm, hab]
      have hq : ⁅F X, F Z⁆ = pinnedX TwistTag.E6.tag K γ (εγ * (N * σ c)) := by
        rw [← map_commutatorElement, hp, hFγ, hργ]
        congr 1
        rw [mul_one, map_mul, hσN]
      have hYZ : Commute (F X) Z := by
        rw [hFX]
        exact commute_pinnedX_of_noSum hρa hbR hnρab _ _
      have hXW : Commute X (F Z) := by
        rw [hFZ]
        exact commute_pinnedX_of_noSum haR hρb hnaρb _ _
      have hqX : Commute ⁅F X, F Z⁆ X := by
        rw [hq]
        exact commute_pinnedX_of_noSum hγR haR hnγa _ _
      have hqZ : Commute ⁅F X, F Z⁆ Z := by
        rw [hq]
        exact commute_pinnedX_of_noSum hγR hbR hnγb _ _
      have h1 : ((⁅w₁, w₂⁆ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
          ModGL TwistTag.E6.tag K) = ⁅X * F X, Z * F Z⁆ := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hw₁, hw₂]
        rfl
      show ((⁅w₁, w₂⁆ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
          ModGL TwistTag.E6.tag K) = _
      rw [h1, commutator_mul_mul hYZ hXW hqX hqZ, hp, hq, ← pinnedX_add]
      congr 1
      ring
  obtain ⟨hur, huG⟩ : (u : ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K γ ∧
      (u : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K σ.toRingHom := by
    refine ⟨?_, graphFixedRootGroup_le _ _ _ u.2⟩
    rwa [CFSG.LieType.Chevalley.rootSpan_singleton] at hu
  obtain ⟨e, he⟩ := mem_rootSubgroup.1 hur
  have hFu : F (u : ModGL TwistTag.E6.tag K) = u := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
    huG).2
  rw [← he, hFγ, hργ] at hFu
  have hσe : σ e = εγ * e := by
    have h1 : εγ * σ e = e := pinnedX_injective _ _ _ hFu
    calc σ e = (εγ * εγ) * σ e := by rw [hεγ, one_mul]
      _ = εγ * (εγ * σ e) := by ring
      _ = εγ * e := by rw [h1]
  obtain ⟨c, hc⟩ := exists_add_smul_eq σ hσσ hσ1 hεs (e := N * e)
    (by rw [map_mul, hσN, hσe]; ring)
  have hee : e = N * c + εγ * (N * σ c) := by
    calc e = N * (N * e) := by rw [← mul_assoc, hNN, one_mul]
      _ = N * c + εγ * (N * σ c) := by rw [hc]; ring
  obtain ⟨y, hyM, hy⟩ := key c
  have : u = y := Subtype.ext (by rw [← he, hee, ← hy]; rfl)
  rw [this]
  exact hyM

theorem commute_rootSpan_pair_rootPair {α β : E6Vec} (hα : IsRoot TwistTag.E6.tag α)
    (hβ : IsRoot TwistTag.E6.tag β) (h1 : OrthRoot α β) (h2 : OrthRoot (rhoE6 α) β) :
    ∀ u ∈ rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec),
      ∀ g ∈ rootSubgroup TwistTag.E6.tag K β ⊔ rootSubgroup TwistTag.E6.tag K (-β),
        Commute u g := by
  have hρ := isRoot_rhoE6 hα
  have hc1 := commute_rootSubgroup_of_orth (F := K) hα hβ h1
  have hc2 := commute_rootSubgroup_of_orth (F := K) hρ hβ h2
  have hx : ∀ δ : E6Vec, (∀ x ∈ rootSubgroup TwistTag.E6.tag K δ,
      (∀ y ∈ rootSubgroup TwistTag.E6.tag K β, Commute x y) ∧
        ∀ y ∈ rootSubgroup TwistTag.E6.tag K (-β), Commute x y) →
      ∀ x ∈ rootSubgroup TwistTag.E6.tag K δ,
        ∀ g ∈ rootSubgroup TwistTag.E6.tag K β ⊔ rootSubgroup TwistTag.E6.tag K (-β),
          Commute x g := by
    intro δ hδ x hxδ g hg
    have hle : rootSubgroup TwistTag.E6.tag K β ⊔ rootSubgroup TwistTag.E6.tag K (-β) ≤
        Subgroup.centralizer {x} := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 ((hδ x hxδ).1 y hy).symm.eq
      · exact Subgroup.mem_centralizer_singleton_iff.2 ((hδ x hxδ).2 y hy).symm.eq
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)).symm
  intro u hu g hg
  have hle : rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec) ≤ Subgroup.centralizer {g} := by
    refine iSup₂_le fun δ hδ => fun x hxδ => ?_
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    rcases hδ with rfl | hδ
    · exact (hx δ (fun x hx' => ⟨hc1.1 x hx', hc1.2 x hx'⟩) x hxδ g hg).eq
    · rw [Set.mem_singleton_iff] at hδ
      subst hδ
      exact (hx _ (fun x hx' => ⟨hc2.1 x hx', hc2.2 x hx'⟩) x hxδ g hg).eq
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hu)

theorem good_orbit_mem_closure (h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hmem : ∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K (fourRootsE i) ⊔
        rootSubgroup TwistTag.E6.tag K (-fourRootsE i))
    {α : E6Vec} (hα : IsRoot TwistTag.E6.tag α) (hP : PairGood α)
    (u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec)) :
    u ∈ Subgroup.closure {x : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) |
      ∃ j k : Fin 4, j ≠ k ∧ Commute x (h j) ∧ Commute x (h k)} := by
  obtain ⟨j, k, hjk, hj1, hk1, hj2, hk2⟩ := hP
  refine Subgroup.subset_closure ⟨j, k, hjk, ?_, ?_⟩
  · refine Subtype.ext ?_
    exact (commute_rootSpan_pair_rootPair hα (isRoot_fourRootsE j) hj1 hj2 _ hu _ (hmem j)).eq
  · refine Subtype.ext ?_
    exact (commute_rootSpan_pair_rootPair hα (isRoot_fourRootsE k) hk1 hk2 _ hu _ (hmem k)).eq

theorem diagramOrbit_E6 (α : E6Vec) :
    TwistTag.E6.diagramOrbit α = {α, rhoE6 α} := by
  ext x
  simp only [TwistTag.diagramOrbit, Finset.mem_image, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h2 : TwistTag.E6.order = 2 := rfl
    rw [h2] at hk
    interval_cases k
    · left
      funext i
      simp only [pow_zero]
      rfl
    · right
      simp [rhoE6]
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by simp only [pow_zero]; rfl⟩
    · exact ⟨1, by decide, by simp [rhoE6]⟩

theorem orbit_mem_closure (hσσ : ∀ c, σ (σ c) = c) (hσ1 : ∃ c, σ c ≠ c)
    (h : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hmem : ∀ i, ((h i : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
      ModGL TwistTag.E6.tag K) ∈ rootSubgroup TwistTag.E6.tag K (fourRootsE i) ⊔
        rootSubgroup TwistTag.E6.tag K (-fourRootsE i))
    {α : E6Vec} (hα : IsRoot TwistTag.E6.tag α)
    (u : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hu : (u : ModGL TwistTag.E6.tag K) ∈ rootSpan TwistTag.E6.tag K ({α, rhoE6 α} : Set E6Vec)) :
    u ∈ Subgroup.closure {x : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) |
      ∃ j k : Fin 4, j ≠ k ∧ Commute x (h j) ∧ Commute x (h k)} := by
  by_cases hP : PairGood α
  · exact good_orbit_mem_closure h hmem hα hP u hu
  · have hbad : α ∈ badRoots := by
      by_contra hn
      exact hP (pairGood_of_not_mem_badRoots α (mem_rootFinset.2 hα) hn)
    have hρ := rhoE6_of_mem_badRoots α hbad
    refine bad_orbit_mem_of_good hσσ hσ1 _ (fun β hβ hPβ v hv =>
      good_orbit_mem_closure h hmem hβ hPβ v hv) α hbad u ?_
    rw [hρ] at hu
    simpa using hu

end E6

end CFSG.HardMathSupport.Lang.AlphaThree

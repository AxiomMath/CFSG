module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Rank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117Two
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS04I117ZeroA
public import CFSG.HardMathSupport.Timmesfeld.DFour.CrossOdd

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open Module CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance
open CFSG.HardMathSupport.Timmesfeld.DFour
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

theorem eq_one_of_pow_two_pow_three {G : Type*} [Group G] {z : G} {n : ℕ} (h2 : z ^ 2 = 1)
    (h3 : z ^ (3 ^ n) = 1) : z = 1 := by
  have h2' := orderOf_dvd_of_pow_eq_one h2
  have h3' := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime 2 (3 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h2' h3')

variable {K : Type} [Field K] [Finite K]

theorem exists_lift_pow (n : ℕ) (hQv : ∃ v, coordinateQuadPlus 4 K v ≠ 0)
    (A : Subgroup (matrixProjectiveDerived (coordinateQuadPlus 4 K)))
    (hA : IsElemAbelian 3 A) (hcard : Nat.card A = 3 ^ n) :
    ∃ E : Subgroup (StatedOmega (StatedQuadPlus 4 K)), Nat.card E = 3 ^ n ∧
      (∀ x ∈ E, x ^ 3 = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      ∀ x ∈ E, omegaToProj K x ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ψ := omegaToProj K with hψ
  set Ã := A.comap ψ with hÃ
  have hsurj : Function.Surjective ((ψ.comp Ã.subtype).codRestrict A fun x => x.2) := by
    intro a
    obtain ⟨x, hx⟩ := omegaToProj_surjective (K := K) (a : matrixProjectiveDerived _)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change ψ x ∈ A
      rw [hψ, hx]
      exact a.2
    · apply Subtype.ext
      exact hx
  have hdvd : 3 ^ n ∣ Nat.card Ã := by
    have := Subgroup.card_dvd_of_surjective hsurj
    rw [hcard] at this
    exact this
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 3 hdvd
  set E := H.map Ã.subtype with hE
  have hEcard : Nat.card E = 3 ^ n := by
    rw [hE, Subgroup.card_map_of_injective Ã.subtype_injective, hH]
  have hEA : ∀ x ∈ E, ψ x ∈ A := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hpn : ∀ x ∈ E, x ^ (3 ^ n) = 1 := by
    intro x hx
    have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
    rw [hEcard] at this
    exact congrArg Subtype.val this
  have hker : ∀ z ∈ E, ψ z = 1 → z = 1 := by
    intro z hz hψz
    exact eq_one_of_pow_two_pow_three (sq_eq_one_of_omegaToProj hQv hψz) (hpn z hz)
  refine ⟨E, hEcard, fun x hx => ?_, fun x hx y hy => ?_, hEA⟩
  · have h3 : ψ (x ^ 3) = 1 := by rw [map_pow]; exact hA.2 _ (hEA x hx)
    have hx3 : x ^ 3 ∈ E := E.pow_mem hx 3
    exact hker _ hx3 h3
  · have hcomm : ψ x * ψ y = ψ y * ψ x :=
      congrArg Subtype.val (hA.1.is_comm.comm ⟨_, hEA x hx⟩ ⟨_, hEA y hy⟩)
    have hz : ψ (x * y * (y * x)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
    have hzE : x * y * (y * x)⁻¹ ∈ E :=
      E.mul_mem (E.mul_mem hx hy) (E.inv_mem (E.mul_mem hy hx))
    exact mul_inv_eq_one.mp (hker _ hzE hz)

theorem poly_lt (q : ℕ) (h5 : 5 ≤ q) : 4 * (1 + q + q ^ 2 + q ^ 3) < q ^ 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 5 := ⟨q - 5, by omega⟩
  ring_nf
  nlinarith [Nat.zero_le m, Nat.zero_le (m ^ 2), Nat.zero_le (m ^ 3), Nat.zero_le (m ^ 4)]

theorem ne_two_mul_of_root (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : 5 ≤ Nat.card K)
    {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K))
    (hsum : ∀ v, v + g v + g (g v) = 0) (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) :
    Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
      2 * Nat.card {L : Submodule K (Fin 4 ⊕ Fin 4 → K) // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  intro heq
  obtain ⟨F, hFinj, hF⟩ := exists_planes_family hg h2 h3 hsum hg3 hd hω
  have hge : Nat.card (Fin 4 → K) ≤ Nat.card {M : Submodule K (Fin 4 ⊕ Fin 4 → K) //
      M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} :=
    Nat.card_le_card_of_injective (fun c => ⟨F c, hF c⟩) fun a b h => hFinj (congrArg Subtype.val h)
  have hle := card_lines_inv_le hg h2 h3 hsum hg3 hd hω
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at hge
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at hle
  have hq := poly_lt (Nat.card K) h5
  linarith

theorem ne_two_mul_of_fixed_zero (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) (h5 : 5 ≤ Nat.card K)
    {g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K)) (hg3 : ∀ v, g (g (g v)) = v)
    (hd : finrank K (LinearMap.ker ((g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) - LinearMap.id)) = 0) :
    Nat.card {M // M ∈ singularSubspaces (quadPlus 4 K) 4 ∧
        M.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = M} ≠
      2 * Nat.card {L // L ∈ singularSubspaces (quadPlus 4 K) 1 ∧
        L.map (g : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) = L} := by
  have hsum := sum_eq_zero_of_fixed_zero h3 hg3 hd
  by_cases hroot : ∃ ω : K, ω ^ 2 + ω + 1 = 0
  · obtain ⟨ω, hω⟩ := hroot
    exact ne_two_mul_of_root h2 h3 h5 hg hsum hg3 hd hω
  · exact ne_two_mul_of_noRoot h2 hg hsum hg3 hroot

theorem d4TrialityCentRank_holds : D4TrialityCentRank := by
  intro K _ _ r f hr hr2 hr3 hK t ht3 htE A hA hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hlt
  push Not at hlt
  have hf : 1 ≤ f := one_le_of_card_field hK
  let e0 : D4Model K ≃* StatedProj (StatedOmega (StatedQuadPlus 4 K)) :=
    (statedProjectiveReindexEquiv (plusIndexEquiv 4) (quadPlus 4 K) (coe_quadPlus 4 K)).symm
  have hm : StatedClassicalModel (D4Model K) .POmegaPlus 4 r f :=
    ⟨⟨hr, hf, le_refl 4⟩, K, inferInstance, inferInstance, hK, ⟨e0⟩⟩
  obtain ⟨hchar, -⟩ := coordinate_model_witness_plus hm K hK e0
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hr2)
  have h3 : (3 : K) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : K) = 0 := by exact_mod_cast h
    have := (CharP.cast_eq_zero_iff K (ringChar K) 3).1 h'
    rw [hchar] at this
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 this)
  have hr5 : 5 ≤ r := by
    have h4 : r ≠ 4 := by
      rintro rfl
      norm_num at hr
    have := hr.two_le
    omega
  have h5 : 5 ≤ Nat.card K := by
    rw [hK]
    exact hr5.trans (Nat.le_self_pow (by omega) r)
  obtain ⟨hQ0, -, -⟩ := d4Facts2 hr hr2 hf hK
  have hQv := CFSG.ComponentClassification.CatalogueBOrthogonalSemilinearFiltration.exists_nonzero_value
    (coordinateQuadPlus 4 K) hQ0
  have hEA := coordinate_plus_family_eq_matrixImage hm K hK e0
  have hp : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hA.2 g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨A₀, hA₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 3) (G := A)
    (by rw [hk]; exact Nat.pow_dvd_pow 3 hk3)
  set A' := A₀.map A.subtype with hA'
  have hA'A : A' ≤ A := Subgroup.map_subtype_le _
  have hA'card : Nat.card A' = 3 ^ 3 := by
    rw [hA', Subgroup.card_map_of_injective A.subtype_injective, hA₀]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hA'el : IsElemAbelian 3 A' :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommA _ (hA'A a.2) _ (hA'A b.2))⟩⟩,
      fun x hx => hA.2 x (hA'A hx)⟩
  obtain ⟨E, hEcard, hE3, hEcomm, hEA'⟩ := exists_lift_pow 3 hQv A' hA'el hA'card
  have : IsMulCommutative E := ⟨⟨fun a b => Subtype.ext (hEcomm a.1 a.2 b.1 b.2)⟩⟩
  have : Finite E := inferInstance
  set ρ : E →* Module.End K (Fin 4 ⊕ Fin 4 → K) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
      ((toLinEquiv (Fin 4 ⊕ Fin 4) K).toMonoidHom.comp
        ((StatedOmega (StatedQuadPlus 4 K)).subtype.comp E.subtype)) with hρ
  have hρapp : ∀ x : E, ρ x = (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] (Fin 4 ⊕ Fin 4 → K)) := fun x => rfl
  have hρinj : Function.Injective ρ := by
    intro x y hxy
    rw [hρapp, hρapp] at hxy
    exact Subtype.ext (Subtype.ext ((toLinEquiv (Fin 4 ⊕ Fin 4) K).injective
      (LinearEquiv.toLinearMap_injective hxy)))
  have hO : ∀ x : E, toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 K) := fun x => by
    rw [← CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv_val 4 K
      (by norm_num) x.1]
    exact orthElementaryGroup_le _
      (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv 4 K
        (by norm_num) x.1).property
  have hcube : ∀ x : E, ∀ v, toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1
      (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1 v)) = v := by
    intro x v
    have h := hE3 x.1 x.2
    have h' : (toLinEquiv (Fin 4 ⊕ Fin 4) K x.1.1) ^ 3 = 1 := by
      rw [← map_pow, ← Subgroup.coe_pow, h, OneMemClass.coe_one, map_one]
    have := congrArg (fun g : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) => g v) h'
    simpa [pow_succ, LinearEquiv.mul_apply] using this
  have heven : ∀ x : E, Even (finrank K (LinearMap.ker (ρ x - 1))) := fun x =>
    even_finrank_ker_sub_one h2 h3 (hO x) (hcube x)
  refine false_of_fixDim_two_four h3 finrank_V8 ρ hρinj
    (fun x => Subtype.ext (by rw [Subgroup.coe_pow, hE3 x.1 x.2, OneMemClass.coe_one]))
    (by rw [hEcard]; norm_num) heven ?_
  intro x hx1
  have hxe := heven x
  have hx8 : finrank K (LinearMap.ker (ρ x - 1)) ≠ 8 := by
    intro h8
    apply hx1
    apply hρinj
    rw [map_one]
    have htop : LinearMap.ker (ρ x - 1) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h8, finrank_V8])
    exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp htop)
  have hxle : finrank K (LinearMap.ker (ρ x - 1)) ≤ 8 :=
    finrank_V8 (K := K) ▸ Submodule.finrank_le _
  have heq := card_maximal_eq_two_mul_card_lines hEA ht3 htE x.1 (hfix _ (hA'A (hEA' _ x.2)))
  have hx6 : finrank K (LinearMap.ker (ρ x - 1)) ≠ 6 := fun h6 =>
    card_maximal_ne_two_mul_card_lines h2 h3 (hO x) (hcube x) h6 heq
  have hx0 : finrank K (LinearMap.ker (ρ x - 1)) ≠ 0 := fun h0 =>
    ne_two_mul_of_fixed_zero h2 h3 h5 (hO x) (hcube x) h0 heq
  obtain ⟨m, hm'⟩ := hxe
  omega

end CFSG.LocalAnalysis.GLTheoremA

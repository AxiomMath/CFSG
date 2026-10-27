module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4ESplit

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.OutcomeLocal
open CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

theorem isComponentOf_map_of_ker_le_center {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : f.ker ≤ center G) {K L : Subgroup G} (hK : Assembly.IsComponentOf K L) :
    Assembly.IsComponentOf (K.map f) (L.map f) := by
  obtain ⟨hKL, hs, hq⟩ := hK
  refine ⟨Subgroup.map_mono hKL, ?_, ?_⟩
  · exact (AssemblyBPredicates.isSubnormal_iff_open _ _).2
      (Components.chain_map f ((AssemblyBPredicates.isSubnormal_iff_open K L).1 hs))
  · rw [AssemblyBPredicates.isQuasisimple_iff_native] at hq ⊢
    have : Group.IsPerfect K := hq.1
    exact (CatalogueBCentralQuotient.quasisimple_map_iff_of_perfect f hf K).1 hq

theorem map_ne_map_of_commute {G H : Type*} [Group G] [Group H] (f : G →* H)
    {J₁ J₂ : Subgroup G} (hq : Assembly.IsQuasisimple (J₁.map f))
    (hc : ∀ x ∈ J₁, ∀ y ∈ J₂, x * y = y * x) : J₁.map f ≠ J₂.map f := by
  intro heq
  refine not_commute_of_isQuasisimple hq fun x hx y hy => ?_
  rw [heq] at hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rw [← map_mul, ← map_mul, hc u hu v hv]

theorem ne_of_commute_of_isQuasisimple {G : Type*} [Group G] {M N : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥M) (hc : ∀ x ∈ M, ∀ y ∈ N, x * y = y * x) : M ≠ N := by
  rintro rfl
  exact not_commute_of_isQuasisimple ((AssemblyBPredicates.isQuasisimple_iff_native M).mpr hq) hc

theorem even_mul_sq_sub_div_two {s : ℕ} (hs : Odd s) : Even (s * (s ^ 2 - 1) / 2) := by
  obtain ⟨t, rfl⟩ := hs
  have h1 : (2 * t + 1) ^ 2 - 1 = 4 * (t * (t + 1)) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (2 * t + 1) * (4 * (t * (t + 1))) = 2 * (2 * ((2 * t + 1) * (t * (t + 1)))) := by
    ring
  rw [h1, h2, Nat.mul_div_cancel_left _ (by norm_num)]
  exact even_two_mul _

variable {k : Type} [Field k] [Finite k]

omit [Finite k] in
theorem conjAut_mem_inner_of_det {m : ℕ} {g : GL (Fin m) k}
    (hg : (g : Matrix (Fin m) (Fin m) k).det = 1) :
    conjAut m k g ∈ OuterAutomorphisms.inner (projectiveSL m k) := by
  let s : SpecialLinearGroup (Fin m) k := ⟨(g : Matrix (Fin m) (Fin m) k), hg⟩
  have h1 : SpecialLinearGroup.toGL s = g := Units.ext rfl
  have h2 := conjAut_toGL s
  rw [h1] at h2
  rw [h2]
  exact ⟨_, rfl⟩

theorem isComponentOf_map_conjAut_of_isometry (B : GL (Fin 4) k) {J : Subgroup (GL (Fin 4) k)}
    (hJ : Assembly.IsComponentOf J (CatalogueBGraphForm.isometryGroup 4 k B⁻¹))
    (hJI : J ≤ (OuterAutomorphisms.inner (projectiveSL 4 k)).comap (conjAut 4 k)) :
    Assembly.IsComponentOf (J.map (conjAut 4 k))
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓
        centralizer {conjAut 4 k B * dualAut 4 k}) := by
  set c := conjAut 4 k with hc
  set Hc := OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {c B * dualAut 4 k}
    with hHc
  set O := CatalogueBGraphForm.isometryGroup 4 k B⁻¹ with hO
  set I := (OuterAutomorphisms.inner (projectiveSL 4 k)).comap c with hI
  set Ct := Hc.comap c with hCt
  have hOC : O ≤ (centralizer {c B * dualAut 4 k}).comap c := isometryGroup_le_comap_centralizer B
  have hJ₁ : Assembly.IsComponentOf J (I ⊓ O) :=
    isComponentOf_of_le hJ (le_inf hJI hJ.1) inf_le_right
  have hIOC : I ⊓ O ≤ Ct := fun g hg => ⟨hg.1, hOC hg.2⟩
  have hcomm : ⁅Ct, Ct⁆ ≤ I ⊓ O := by
    refine le_inf ?_ (graph_commutator_le_isometry (by norm_num) B (comap_mono inf_le_right))
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : x ∈ I := hx.1
    have hy' : y ∈ I := hy.1
    rw [commutatorElement_def]
    exact I.mul_mem (I.mul_mem (I.mul_mem hx' hy') (I.inv_mem hx')) (I.inv_mem hy')
  have hn : ((I ⊓ O).subgroupOf Ct).Normal := by
    rw [normal_subgroupOf_iff hIOC]
    intro x y hx hy
    have h1 : y * x * y⁻¹ = ⁅y, x⁆ * x := by rw [commutatorElement_def]; group
    rw [h1]
    exact (I ⊓ O).mul_mem (hcomm (commutator_mem_commutator hy (hIOC hx))) hx
  have hJCt : Assembly.IsComponentOf J Ct :=
    ⟨hJ₁.1.trans hIOC, assembly_isSubnormal_trans hJ₁.2.1
      (Assembly.IsSubnormal.step hIOC hn (Assembly.IsSubnormal.refl _)), hJ₁.2.2⟩
  have hmap := isComponentOf_map_of_ker_le_center c (ker_conjAut_le_center (by norm_num)) hJCt
  rwa [hCt, map_comap_eq_self (inf_le_left.trans inner_le_range_conjAut)] at hmap

theorem exists_twin_component {A : Type} [Group A] {a : A} {L : Subgroup A} {ℓ e : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e)
    {ρ : A →* MulAut (projectiveSL 4 k)}
    (hL₁ : Assembly.IsComponentOf (L.map ρ)
      (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}))
    {B : GL (Fin 4) k} (hρa : ρ a = conjAut 4 k B * dualAut 4 k)
    (hB : (B : Matrix (Fin 4) (Fin 4) k)ᵀ = B)
    (hsplit : ∃ S : Submodule k (Fin 4 → k), Module.finrank k S = 2 ∧
      ∀ x ∈ S, CatalogueBLinearHigherB.matrixQuadraticForm B⁻¹ x = 0) :
    ∃ J : Subgroup (MulAut (projectiveSL 4 k)),
      Assembly.IsComponentOf J
        (OuterAutomorphisms.inner (projectiveSL 4 k) ⊓ centralizer {ρ a}) ∧ J ≠ L.map ρ ∧
        Nonempty (J ≃* GorensteinWalter.PSL2 k) := by
  classical
  have : CharP k ℓ := finite_field_prime_power_characteristic hℓ he hk
  have hk2 : ringChar k ≠ 2 := by rw [ringChar.eq k ℓ]; exact hℓ2
  have hodd : Odd (Nat.card k) := by rw [hk]; exact (hℓ.odd_of_ne_two hℓ2).pow
  rw [hρa] at hL₁ ⊢
  obtain ⟨hXh, hmap, -⟩ := graph_component_lift (by norm_num) B hL₁
  set Xh := ⁅(L.map ρ).comap (conjAut 4 k), (L.map ρ).comap (conjAut 4 k)⁆ with hXhdef
  set R : GL (Fin 4) k := B⁻¹ with hRdef
  set O := CatalogueBGraphForm.isometryGroup 4 k R with hOdef
  have hR : (R : Matrix (Fin 4) (Fin 4) k)ᵀ = R := transpose_inv_eq_of_transpose_eq hB
  set Q := CatalogueBLinearHigherB.matrixQuadraticForm R with hQdef
  have hQ : Q.polarBilin.Nondegenerate :=
    CatalogueBLinearHigherB.polarBilin_matrixQuadraticForm_nondegenerate hk2 R hR
  have hdim : Module.finrank k (Fin 4 → k) = 4 := Module.finrank_fin_fun k
  set eO := matrixOrthogonalEquiv hk2 R hR with heO
  set f : TauCeti.QuadraticMap.orthogonalGroup Q →* GL (Fin 4) k :=
    O.subtype.comp eO.toMonoidHom with hf
  have hfi : Function.Injective f := O.subtype_injective.comp eO.injective
  have hfr : (⊤ : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = O := by
    rw [← MonoidHom.range_eq_map, hf, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      eO.surjective, ← MonoidHom.range_eq_map, range_subtype]
  have hcov := orthogonal_low_dimensional_fixed_derived_component_coverage Q hQ
    (Or.inr (Or.inr ⟨hdim, hsplit⟩))
  have hXq := (AssemblyBPredicates.isQuasisimple_iff_native Xh).1 hXh.2.2
  have hq3 : Nat.card k ≠ 3 := by
    intro hq3
    obtain ⟨hexc, -⟩ := hcov
    obtain ⟨hprime, -⟩ := hexc (Or.inr ⟨⟨hdim, hsplit⟩, Or.inr hq3⟩)
    have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
      isSolvable_of_prime_dvd_card_eq_or_eq hprime
    have : Group.IsSolvable O :=
      Group.isSolvable_of_isSolvable_injective (f := eO.symm.toMonoidHom) eO.symm.injective
    have : Group.IsSolvable Xh :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hXh.1)
        (Subgroup.inclusion_injective hXh.1)
    have : Nontrivial Xh := CFSG.LocalCores.isQuasisimple_nontrivial hXq
    have : Group.IsPerfect Xh := hXq.1
    exact Group.IsPerfect.not_isSolvable Xh inferInstance
  have hq2 : Nat.card k ≠ 2 := by
    intro h
    rw [h] at hodd
    exact (Nat.not_odd_iff_even.mpr even_two) hodd
  have hq5 : 5 ≤ Nat.card k := by
    have h1 : 2 ≤ Nat.card k := by
      rw [hk]
      exact hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    have h4 : Nat.card k ≠ 4 := fun h => by
      rw [h] at hodd
      exact (Nat.not_odd_iff_even.mpr (by decide)) hodd
    omega
  obtain ⟨-, -, -, hsplitm, -, -, -⟩ := hcov
  obtain ⟨ψ, e, -, hψe, hsup, hq₁, hq₂, hn₁, hn₂, -⟩ := hsplitm hdim hsplit hq2 hq3
  have hfe : ∀ d : DeterminantIsometries k, f (e.symm d) = linearConjGL ψ d.val := by
    intro d
    apply eq_of_mulVec_eq
    intro v
    rw [linearConjGL_mulVec]
    change ((eO (e.symm d) : GL (Fin 4) k) : Matrix (Fin 4) (Fin 4) k) *ᵥ v = _
    rw [matrixOrthogonalEquiv_mulVec]
    have h1 := hψe (e.symm d) (ψ v)
    rw [MulEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] at h1
    rw [h1, LinearEquiv.symm_apply_apply]
  have hL₁r : ((determinantLeftFactor k).map e.symm.toMonoidHom).map f =
      (splitLeftHom ψ).range := by
    rw [determinantLeftFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext U : 1
    exact hfe _
  have hL₂r : ((determinantRightFactor k).map e.symm.toMonoidHom).map f =
      (splitRightHom ψ).range := by
    rw [determinantRightFactor, MonoidHom.range_eq_map, Subgroup.map_map, Subgroup.map_map,
      MonoidHom.range_eq_map]
    congr 1
    ext W : 1
    exact hfe _
  have hcomp : ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q),
      CFSG.IsQuasisimple M → M ≤ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) →
      (M.subgroupOf (commutator (TauCeti.QuadraticMap.orthogonalGroup Q))).Normal →
      Assembly.IsComponentOf (M.map f) O := by
    intro M hMq hMle hMn
    have hM : Assembly.IsComponentOf M ⊤ := by
      refine ⟨le_top, Assembly.IsSubnormal.step hMle hMn
        (Assembly.IsSubnormal.step le_top ?_ (Assembly.IsSubnormal.refl _)),
        (AssemblyBPredicates.isQuasisimple_iff_native M).2 hMq⟩
      exact Subgroup.Normal.subgroupOf inferInstance _
    have := SymmetricLocal.isComponentOf_map_of_injective f hfi hM
    rwa [hfr] at this
  have hc₁ := hcomp _ hq₁ (hsup ▸ le_sup_left) hn₁
  have hc₂ := hcomp _ hq₂ (hsup ▸ le_sup_right) hn₂
  rw [hL₁r] at hc₁
  rw [hL₂r] at hc₂
  have hcommO : (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).map f = ⁅O, O⁆ := by
    rw [hf, ← Subgroup.map_map, ← Subgroup.map_subtype_commutator]
    congr 1
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ eO.surjective]
  have hD : ⁅O, O⁆ = (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range := by
    rw [← hcommO, hsup, Subgroup.map_sup, hL₁r, hL₂r]
  have hXhD : Xh ≤ ⁅O, O⁆ := by
    have : Group.IsPerfect Xh := ⟨hXh.2.2.1⟩
    rw [← Subgroup.commutator_eq_self (H := Xh)]
    exact Subgroup.commutator_mono hXh.1 hXh.1
  have hX : Xh = (splitLeftHom ψ).range ∨ Xh = (splitRightHom ψ).range := by
    rcases isComponentOf_eq_or_commute hXh hc₁ with h1 | h1
    · exact Or.inl h1
    rcases isComponentOf_eq_or_commute hXh hc₂ with h2 | h2
    · exact Or.inr h2
    exfalso
    have h1' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    have h2' := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
    refine not_commute_of_isQuasisimple hXh.2.2 fun x hx y hy => ?_
    have hle : (splitLeftHom ψ).range ⊔ (splitRightHom ψ).range ≤ centralizer {x} :=
      sup_le (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h1' hx)) z hz))
        (fun z hz => mem_centralizer_singleton_iff.mpr
          ((mem_centralizer_iff.mp (h2' hx)) z hz))
    have hy' := hle (hD ▸ hXhD hy)
    exact (mem_centralizer_singleton_iff.mp hy').symm
  have hI₁ : (splitLeftHom ψ).range ≤
      (OuterAutomorphisms.inner (projectiveSL 4 k)).comap (conjAut 4 k) := by
    rintro _ ⟨U, rfl⟩
    exact conjAut_mem_inner_of_det (det_splitLeftHom ψ hq5 U)
  have hI₂ : (splitRightHom ψ).range ≤
      (OuterAutomorphisms.inner (projectiveSL 4 k)).comap (conjAut 4 k) := by
    rintro _ ⟨W, rfl⟩
    exact conjAut_mem_inner_of_det (det_splitRightHom ψ hq5 W)
  have hm₁ := isComponentOf_map_conjAut_of_isometry B hc₁ hI₁
  have hm₂ := isComponentOf_map_conjAut_of_isometry B hc₂ hI₂
  have hcm : ∀ x ∈ (splitLeftHom ψ).range, ∀ y ∈ (splitRightHom ψ).range, x * y = y * x := by
    rintro _ ⟨U, rfl⟩ _ ⟨W, rfl⟩
    exact splitLeftHom_commute ψ U W
  rw [← hmap]
  rcases hX with h | h
  · refine ⟨_, hm₂, ?_, Catalog7L4E.iso_of_factor (ρ := MonoidHom.id _) Function.injective_id
      (by rw [Subgroup.map_id]) (Catalog7L4E.ker_splitRight ψ)⟩
    rw [h]
    exact map_ne_map_of_commute _ hm₂.2.2 fun x hx y hy => (hcm y hy x hx).symm
  · refine ⟨_, hm₁, ?_, Catalog7L4E.iso_of_factor (ρ := MonoidHom.id _) Function.injective_id
      (by rw [Subgroup.map_id]) (Catalog7L4E.ker_splitLeft ψ)⟩
    rw [h]
    exact map_ne_map_of_commute _ hm₁.2.2 hcm

end CFSG.ComponentClassification.HarrisLit.N36

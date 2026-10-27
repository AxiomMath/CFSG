module

public import CFSG.FeitThompson.Representations.SquareZeroGeneratorsDimensionAtMostTwo
public import CFSG.FeitThompson.Representations.CommutingOperatorFiniteScalarField
import CFSG.FeitThompson.Representations.AnticommutatorSquareZeroOperators
import CFSG.FeitThompson.Representations.OddLinearGroupsDimTwo
public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Module

section Groups

theorem isPGroup_closure_singleton_of_orderOf_dvd_pow {H : Type*} [Group H] {p m : ℕ}
    (hp : p.Prime) {g : H} (hg : orderOf g ∣ p ^ m) :
    IsPGroup p (Subgroup.closure ({g} : Set H)) := by
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hg
  rw [← Subgroup.zpowers_eq_closure]
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem isPGroup_of_normal_sylow_of_closure_eq_top {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) {P : Subgroup H} [P.Normal] (hPp : IsPGroup p P) (hidx : ¬ p ∣ P.index)
    {S : Set H} (hS : Subgroup.closure S = ⊤) (hpow : ∀ g ∈ S, ∃ m, orderOf g ∣ p ^ m) :
    IsPGroup p H := by
  have hSP : S ⊆ (P : Set H) := by
    intro g hg
    obtain ⟨m, hm⟩ := hpow g hg
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1
      ((orderOf_map_dvd (QuotientGroup.mk' P) g).trans hm)
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · exact absurd (((dvd_pow_self p h.ne').trans (hj ▸ orderOf_dvd_natCard _)).trans
          (dvd_of_eq (P.index_eq_card).symm)) hidx
    have h1 : (QuotientGroup.mk' P) g = 1 := by rw [← orderOf_eq_one_iff, hj, hj0, pow_zero]
    exact (QuotientGroup.eq_one_iff g).1 h1
  have hPtop : P = ⊤ := top_le_iff.1 (hS ▸ (Subgroup.closure_le P).2 hSP)
  exact (hPtop ▸ hPp).of_equiv Subgroup.topEquiv

theorem isPGroup_range_of_ker_eq {A B C : Type*} [Group A] [Group B] [Group C] {p : ℕ}
    (f : A →* B) (g : A →* C) (h : f.ker = g.ker) (hg : IsPGroup p g.range) :
    IsPGroup p f.range :=
  hg.of_equiv (((QuotientGroup.quotientKerEquivRange g).symm.trans
    (QuotientGroup.quotientMulEquivOfEq h.symm)).trans (QuotientGroup.quotientKerEquivRange f))

end Groups

section Reps

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem mem_ker_asGroupHom_iff {A : Type*} [Group A] (σ : Representation K A V) (b : A) :
    b ∈ σ.asGroupHom.ker ↔ ∀ v, σ b v = v := by
  rw [MonoidHom.mem_ker]
  refine ⟨fun h v => ?_, fun h => Units.ext ?_⟩
  · have h2 : (σ b : Module.End K V) = 1 := by
      rw [← Representation.asGroupHom_apply, h, Units.val_one]
    exact congrArg (fun f : Module.End K V => f v) h2
  · rw [Representation.asGroupHom_apply, Units.val_one]
    exact LinearMap.ext h

theorem eq_bot_or_eq_top_of_forall_apply_mem {G : Type*} [Monoid G] (σ : Representation K G V)
    [σ.IsIrreducible] {U : Submodule K V} (h : ∀ g : G, ∀ v ∈ U, σ g v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨U, fun g v hv => h g v hv⟩ : Subrepresentation σ)
    with h1 | h1
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem isIrreducible_of_forall_eq_bot_or_eq_top {G : Type*} [Monoid G] (τ : Representation K G V)
    [Nontrivial V] (h : ∀ U : Submodule K V, (∀ g : G, ∀ v ∈ U, τ g v ∈ U) → U = ⊥ ∨ U = ⊤) :
    τ.IsIrreducible := by
  have : Nontrivial (Subrepresentation τ) :=
    nontrivial_of_ne ⊥ ⊤ fun h1 => (bot_ne_top (α := Submodule K V))
      (Subrepresentation.ext_iff.mp h1)
  refine ⟨fun W => ?_⟩
  rcases h W.toSubmodule (fun g v hv => W.apply_mem_toSubmodule g hv) with h1 | h1
  · exact Or.inl (Subrepresentation.ext h1)
  · exact Or.inr (Subrepresentation.ext h1)

theorem isIrreducible_ofDistribMulAction_of_range_le {G : Type*} [Group G]
    (σ : Representation K G V) [σ.IsIrreducible] {H : Subgroup (Module.End K V)ˣ}
    (hH : σ.asGroupHom.range ≤ H) :
    (Representation.ofDistribMulAction K H V).IsIrreducible := by
  have hV : Nontrivial V := nontrivial_of_isIrreducible σ
  refine isIrreducible_of_forall_eq_bot_or_eq_top _ fun U hU => ?_
  refine eq_bot_or_eq_top_of_forall_apply_mem σ (fun g v hv => ?_)
  have hu : σ.asGroupHom g ∈ H := hH ⟨g, rfl⟩
  have h2 := hU (⟨σ.asGroupHom g, hu⟩ : H) v hv
  rw [Representation.ofDistribMulAction_apply_apply] at h2
  have h3 : (⟨σ.asGroupHom g, hu⟩ : H) • v = σ g v :=
    congrArg (fun f : Module.End K V => f v) (Representation.asGroupHom_apply σ g)
  rwa [h3] at h2

theorem two_le_finrank_of_mul_self_eq_zero [FiniteDimensional K V] {f : Module.End K V}
    (hf : f * f = 0) (hf0 : f ≠ 0) : 2 ≤ finrank K V := by
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro v ⟨w, rfl⟩
    have h : (f * f) w = 0 := by rw [hf]; simp
    simpa [LinearMap.mem_ker, Module.End.mul_apply] using h
  have h1 : 1 ≤ finrank K (LinearMap.range f) :=
    Submodule.one_le_finrank_iff.2 (by simpa [LinearMap.range_eq_bot] using hf0)
  have h2 : finrank K (LinearMap.range f) ≤ finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hle
  have h3 := LinearMap.finrank_range_add_finrank_ker f
  omega

theorem range_asGroupHom_eq_closure_pair {A : Type*} [Group A] (ρ : Representation K A V) {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤) :
    ρ.asGroupHom.range
      = Subgroup.closure ({ρ.asGroupHom x, ρ.asGroupHom y} : Set (Module.End K V)ˣ) := by
  rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq]

theorem isPGroup_range_of_map_eq_one {A : Type*} [Group A] {p n : ℕ} (hp : p.Prime)
    (ρ : Representation K A V) {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx1 : ρ x = 1) (hy : orderOf y ∣ p ^ n) : IsPGroup p ρ.asGroupHom.range := by
  have h1 : ρ.asGroupHom x = 1 :=
    Units.ext (by rw [Representation.asGroupHom_apply, hx1, Units.val_one])
  rw [range_asGroupHom_eq_closure_pair ρ hgen, h1, Subgroup.closure_insert_one]
  exact isPGroup_closure_singleton_of_orderOf_dvd_pow hp
    ((orderOf_map_dvd ρ.asGroupHom y).trans hy)

theorem finrank_le_two_of_quadratic_generators {A : Type*} [Group A] (σ : Representation K A V)
    [σ.IsIrreducible] {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    {X Y : Module.End K V} {t : K} (hXd : σ x - 1 = X) (hYd : σ y - 1 = Y)
    (hX : X ^ 2 = 0) (hY : Y ^ 2 = 0) (hXY : X * Y + Y * X = t • 1) (hX0 : X ≠ 0) :
    finrank K V ≤ 2 := by
  refine finrank_le_two_of_sq_eq_zero_of_isIrreducible hX hY hXY hX0
    (isIrreducible_ofDistribMulAction_of_range_le σ ?_)
  rw [range_asGroupHom_eq_closure_pair σ hgen]
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl)
  · have h : σ.asGroupHom x = unitOneAddOfSqEqZero X hX := by
      refine Units.ext ?_
      rw [Representation.asGroupHom_apply, unitOneAddOfSqEqZero_val, ← hXd]
      abel
    rw [h]
    exact Subgroup.subset_closure (by simp)
  · have h : σ.asGroupHom y = unitOneAddOfSqEqZero Y hY := by
      refine Units.ext ?_
      rw [Representation.asGroupHom_apply, unitOneAddOfSqEqZero_val, ← hYd]
      abel
    rw [h]
    exact Subgroup.subset_closure (by simp)

end Reps

theorem isPGroup_range_of_finrank_eq_two {K V : Type*} [Field K] [Finite K] {p : ℕ} [CharP K p]
    (hp : p.Prime) [AddCommGroup V] [Module K V] (hdim : finrank K V = 2)
    {A : Type*} [Group A] (hAodd : Odd (Nat.card A)) (σ : Representation K A V)
    {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ n, orderOf y ∣ p ^ n) :
    IsPGroup p σ.asGroupHom.range := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Module.Finite K V := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq K V hdim
  let e : GL (Fin 2) K ≃* LinearMap.GeneralLinearGroup K V := Matrix.GeneralLinearGroup.toLin' b
  let ψ : LinearMap.GeneralLinearGroup K V →* GL (Fin 2) K := e.symm.toMonoidHom
  let φ : A →* GL (Fin 2) K := ψ.comp σ.asGroupHom
  set G := Subgroup.closure ({φ x, φ y} : Set (GL (Fin 2) K)) with hGdef
  have hGrange : φ.range = G := by
    rw [MonoidHom.range_eq_map, ← hgen, MonoidHom.map_closure, hGdef]
    congr 1
    simp [Set.image_insert_eq]
  have hGodd : Odd (Nat.card G) := hAodd.of_dvd_nat (hGrange ▸ Subgroup.card_range_dvd φ)
  obtain ⟨P, hPnorm, -⟩ := exists_normal_abelian_sylow_of_odd (k := K) hp (G := G) hGodd
  have hGp : IsPGroup p G := by
    have := hPnorm
    refine isPGroup_of_normal_sylow_of_closure_eq_top hp P.isPGroup' P.not_dvd_index
      (S := Subtype.val ⁻¹' ({φ x, φ y} : Set (GL (Fin 2) K)))
      Subgroup.closure_closure_coe_preimage ?_
    intro z hz
    have hz' : (z : GL (Fin 2) K) = φ x ∨ (z : GL (Fin 2) K) = φ y := by
      simpa [Set.mem_preimage] using hz
    rw [← Subgroup.orderOf_coe]
    rcases hz' with h | h <;> rw [h]
    · obtain ⟨m, hm⟩ := hx
      exact ⟨m, (orderOf_map_dvd φ x).trans hm⟩
    · obtain ⟨n, hn⟩ := hy
      exact ⟨n, (orderOf_map_dvd φ y).trans hn⟩
  have hφp : IsPGroup p φ.range := hGp.of_equiv (MulEquiv.subgroupCongr hGrange).symm
  have hmap : φ.range = Subgroup.map ψ σ.asGroupHom.range := MonoidHom.range_comp ψ σ.asGroupHom
  exact (hmap ▸ hφp).of_equiv (Subgroup.equivMapOfInjective σ.asGroupHom.range ψ
    (MulEquiv.injective e.symm)).symm

section Adjoin

variable {k V A : Type*} [Field k] [AddCommGroup V] [Module k V] [Group A]

def adjoinRestrict {T f : Module.End k V} (hf : Commute f T) :
    Module.End (Algebra.adjoin k ({T} : Set (Module.End k V))) V where
  toFun := f
  map_add' := map_add f
  map_smul' S v := congrArg (fun g : Module.End k V => g v)
    (Algebra.commute_of_mem_adjoin_singleton_of_commute S.2 hf).eq

@[simp]
theorem adjoinRestrict_apply {T f : Module.End k V} (hf : Commute f T) (v : V) :
    adjoinRestrict hf v = f v := (rfl)

theorem commute_anticommutator_of_closure_pair (ρ : Representation k A V) {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hX : (ρ x - 1) * (ρ x - 1) = 0) (hY : (ρ y - 1) * (ρ y - 1) = 0) (a : A) :
    Commute (ρ a) ((ρ x - 1) * (ρ y - 1) + (ρ y - 1) * (ρ x - 1)) := by
  have hux : ρ.asGroupHom x = sqZeroUnit hX :=
    Units.ext (by rw [Representation.asGroupHom_apply, sqZeroUnit_val]; abel)
  have huy : ρ.asGroupHom y = sqZeroUnit hY :=
    Units.ext (by rw [Representation.asGroupHom_apply, sqZeroUnit_val]; abel)
  have hmem : ρ.asGroupHom a ∈ Subgroup.closure ({sqZeroUnit hX, sqZeroUnit hY} :
      Set (Module.End k V)ˣ) := by
    rw [← hux, ← huy, ← range_asGroupHom_eq_closure_pair ρ hgen]
    exact ⟨a, rfl⟩
  have h := commute_anticommutator_of_mem_closure hX hY hmem
  rw [← Representation.asGroupHom_apply]
  exact h.symm

end Adjoin

theorem isPGroup_range_of_quadratic_pElement_generators {k V : Type*} [Field k] [Finite k] {p : ℕ}
    [CharP k p] (hp : p.Prime) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {A : Type*} [Group A] (hAodd : Odd (Nat.card A)) (ρ : Representation k A V)
    [ρ.IsIrreducible] {x y : A} (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : ∃ m, orderOf x ∣ p ^ m) (hy : ∃ n, orderOf y ∣ p ^ n)
    (hX : (ρ x - 1) * (ρ x - 1) = 0) (hY : (ρ y - 1) * (ρ y - 1) = 0) :
    IsPGroup p ρ.asGroupHom.range := by
  by_cases hX0 : ρ x - 1 = 0
  ·
    obtain ⟨n, hn⟩ := hy
    exact isPGroup_range_of_map_eq_one hp ρ hgen (by rw [← sub_eq_zero]; exact hX0) hn
  have hT : ∀ a, Commute (ρ a) ((ρ x - 1) * (ρ y - 1) + (ρ y - 1) * (ρ x - 1)) :=
    commute_anticommutator_of_closure_pair ρ hgen hX hY
  set T : Module.End k V := (ρ x - 1) * (ρ y - 1) + (ρ y - 1) * (ρ x - 1) with hTdef
  have hXT : Commute (ρ x - 1) T :=
    (hTdef ▸ commute_anticommutator_end_left (ρ x - 1) (ρ y - 1) hX).symm
  have hYT : Commute (ρ y - 1) T :=
    (hTdef ▸ commute_anticommutator_end_right (ρ x - 1) (ρ y - 1) hY).symm
  let _ := genField hT
  have _hKfin : Finite (Algebra.adjoin k ({T} : Set (Module.End k V))) := finite_adjoin T
  have _hKchar : CharP (Algebra.adjoin k ({T} : Set (Module.End k V))) p :=
    charP_of_injective_algebraMap (algebraMap_adjoin_injective (ρ := ρ) T) p
  have _hVK : Module.Finite (Algebra.adjoin k ({T} : Set (Module.End k V))) V :=
    finite_module_adjoin T
  have _hirrK : (genRepresentation ρ hT).IsIrreducible := isIrreducible_genRepresentation ρ hT
  set X' : Module.End (Algebra.adjoin k ({T} : Set (Module.End k V))) V :=
    adjoinRestrict hXT with hX'def
  set Y' : Module.End (Algebra.adjoin k ({T} : Set (Module.End k V))) V :=
    adjoinRestrict hYT with hY'def
  have hgx : (genRepresentation ρ hT) x - 1 = X' := by
    ext v; simp [hX'def, genRepresentation_apply]
  have hgy : (genRepresentation ρ hT) y - 1 = Y' := by
    ext v; simp [hY'def, genRepresentation_apply]
  have hX'2 : X' ^ 2 = 0 := by
    rw [pow_two]
    ext v
    have h : ((ρ x - 1) * (ρ x - 1)) v = 0 := by rw [hX]; simp
    simpa [hX'def, Module.End.mul_apply] using h
  have hY'2 : Y' ^ 2 = 0 := by
    rw [pow_two]
    ext v
    have h : ((ρ y - 1) * (ρ y - 1)) v = 0 := by rw [hY]; simp
    simpa [hY'def, Module.End.mul_apply] using h
  have hXY : X' * Y' + Y' * X'
      = (⟨T, Algebra.self_mem_adjoin_singleton k T⟩ :
        Algebra.adjoin k ({T} : Set (Module.End k V))) • (1 : Module.End _ V) := by
    ext v
    rw [LinearMap.smul_apply, Module.End.one_apply, adjoin_smul_def]
    simpa [hX'def, hY'def, Module.End.mul_apply] using
      (congrArg (fun f : Module.End k V => f v) hTdef).symm
  have hX'0 : X' ≠ 0 := by
    intro h
    refine hX0 (LinearMap.ext fun v => ?_)
    have h2 := congrArg
      (fun f : Module.End (Algebra.adjoin k ({T} : Set (Module.End k V))) V => f v) h
    simpa [hX'def] using h2
  have hle : finrank (Algebra.adjoin k ({T} : Set (Module.End k V))) V ≤ 2 :=
    finrank_le_two_of_quadratic_generators (genRepresentation ρ hT) hgen hgx hgy hX'2 hY'2 hXY hX'0
  have hge : 2 ≤ finrank (Algebra.adjoin k ({T} : Set (Module.End k V))) V :=
    two_le_finrank_of_mul_self_eq_zero (by rw [← pow_two]; exact hX'2) hX'0
  have hdim : finrank (Algebra.adjoin k ({T} : Set (Module.End k V))) V = 2 := le_antisymm hle hge
  have hKp : IsPGroup p (genRepresentation ρ hT).asGroupHom.range :=
    isPGroup_range_of_finrank_eq_two hp hdim hAodd (genRepresentation ρ hT) hgen hx hy
  refine isPGroup_range_of_ker_eq _ _ ?_ hKp
  ext b
  rw [mem_ker_asGroupHom_iff, mem_ker_asGroupHom_iff]
  simp [genRepresentation_apply]

theorem isPGroup_range_of_quadratic_pElement_generators_zmod {p : ℕ} [hp : Fact p.Prime]
    (_hpodd : Odd p) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] {A : Type*} [Group A] (hAodd : Odd (Nat.card A))
    (ρ : Representation (ZMod p) A V) [ρ.IsIrreducible] {x y : A}
    (hgen : Subgroup.closure ({x, y} : Set A) = ⊤)
    (hx : x ∈ pElements p A) (hy : y ∈ pElements p A)
    (hX : (ρ x - 1) * (ρ x - 1) = 0) (hY : (ρ y - 1) * (ρ y - 1) = 0) :
    IsPGroup p ρ.asGroupHom.range := by
  obtain ⟨m, hm⟩ := mem_pElements.1 hx
  obtain ⟨n, hn⟩ := mem_pElements.1 hy
  exact isPGroup_range_of_quadratic_pElement_generators hp.out hAodd ρ hgen ⟨m, hm ▸ dvd_rfl⟩
    ⟨n, hn ▸ dvd_rfl⟩ hX hY

end

end CFSG.FeitThompson

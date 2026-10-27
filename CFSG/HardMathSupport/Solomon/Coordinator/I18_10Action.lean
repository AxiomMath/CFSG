module

public import CFSG.HardMathSupport.Solomon.Coordinator.I18_10Basic
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open scoped commutatorElement
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section Action

variable {X : Type} [Group X] [Finite X]

theorem i1810_dvd_card_component {q : ℕ} [Fact q.Prime] (hO : CFSG.pPrimeCore q X = ⊥)
    {K : Subgroup X} (hK : CFSG.IsComponent K) : q ∣ Nat.card K := by
  by_contra hdvd
  set π : Set Nat.Primes := {r | (r : ℕ) ≠ q} with hπ
  have h1 := CFSG.LocalCores.prime_set_core_subnormal_intersection π hK.2
  have htop : CFSG.piCore π ↥K = ⊤ := by
    refine eq_top_iff.2 (le_sSup ⟨Subgroup.normal_top, fun r hr => ?_⟩)
    show (r : ℕ) ≠ q
    rintro hrq
    apply hdvd
    rw [← hrq, ← Subgroup.card_top (G := ↥K)]
    exact hr
  have hle : CFSG.piCore π X ≤ CFSG.pPrimeCore q X := by
    refine le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hq => ?_⟩
    have := CFSG.LocalCores.piCore_isPiSubgroup (G := X) π ⟨q, Fact.out⟩ hq
    exact this rfl
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  have hK1 : K = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact (le_of_eq h1).trans (inf_le_right.trans hle)
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  subst hK1
  exact (not_nontrivial_iff_subsingleton.2 inferInstance) this

theorem i1810_not_inf_le_center {q : ℕ} [Fact q.Prime] (hO : CFSG.pPrimeCore q X = ⊥)
    (Q : Sylow q X) {K : Subgroup X} (hK : CFSG.IsComponent K) :
    ¬ ((Q : Subgroup X) ⊓ K ≤ (Subgroup.center K).map K.subtype) := by
  intro hle
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hK.2
  have hPc : (P : Subgroup K) ≤ Subgroup.center K := by
    rw [← Subgroup.map_le_map_iff_of_injective K.subtype_injective, hP]
    exact hle
  have : Group.IsPerfect K := hK.1.1
  have h1 := i1810_card_sylow_eq_one_of_le_center P hPc
  have h2 := i1810_dvd_card_component hO hK
  apply P.not_dvd_index
  have h3 := Subgroup.card_mul_index (P : Subgroup K)
  rw [h1, one_mul] at h3
  rw [h3]
  exact h2

theorem i1810_map_component_eq {D : Type*} [Group D] {q : ℕ} [Fact q.Prime]
    (hO : CFSG.pPrimeCore q X = ⊥) (Q : Sylow q X) (ρ : D →* MulAut X)
    (hρQ : ∀ d : D, ∀ x ∈ (Q : Subgroup X), ρ d x = x) {K : Subgroup X}
    (hK : CFSG.IsComponent K) (d : D) : K.map (ρ d).toMonoidHom = K := by
  have hK' := CFSG.LocalCores.isComponent_map_mulEquiv (ρ d) hK
  rcases CFSG.LocalCores.distinct_components_commute hK' hK with h | h
  · exact h
  · exfalso
    apply i1810_not_inf_le_center hO Q hK
    intro x hx
    obtain ⟨hxQ, hxK⟩ := Subgroup.mem_inf.1 hx
    have hxK' : x ∈ K.map (ρ d).toMonoidHom := ⟨x, hxK, hρQ d x hxQ⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    have hc : ⁅x, (k : X)⁆ ∈ ⁅K.map (ρ d).toMonoidHom, K⁆ :=
      Subgroup.commutator_mem_commutator hxK' k.2
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    simp only [Subgroup.coe_mul]
    exact hc.symm

@[expose] noncomputable def i1810_restrict {D : Type*} [Group D] (ρ : D →* MulAut X)
    (K : Subgroup X) (hK : ∀ d : D, K.map (ρ d).toMonoidHom = K) : D →* MulAut K where
  toFun d := (MulEquiv.subgroupMap (ρ d) K).trans (MulEquiv.subgroupCongr (hK d))
  map_one' := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ρ 1 (x : X) = (x : X)
    simp
  map_mul' := by
    intro a b
    refine MulEquiv.ext fun x => Subtype.ext ?_
    show ρ (a * b) (x : X) = ρ a (ρ b (x : X))
    simp

omit [Finite X] in
theorem i1810_restrict_apply {D : Type*} [Group D] (ρ : D →* MulAut X) (K : Subgroup X)
    (hK : ∀ d : D, K.map (ρ d).toMonoidHom = K) (d : D) (x : K) :
    ((i1810_restrict ρ K hK d x : K) : X) = ρ d x :=
  rfl

theorem i1810_component_fixed (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hX : CFSG.Open.IsKGroup X) {p q : ℕ} [Fact q.Prime] (hpX : Nat.Coprime p (Nat.card X))
    (hO : CFSG.pPrimeCore q X = ⊥) (Q : Sylow q X) {D : Type*} [Group D] [Group.IsPerfect D]
    (ρ : D →* MulAut X) (hρQ : ∀ d : D, ∀ x ∈ (Q : Subgroup X), ρ d x = x)
    {K : Subgroup X} (hK : CFSG.IsComponent K) {d : D} {k : ℕ} (hd : d ^ p ^ k = 1) :
    ∀ x ∈ K, ρ d x = x := by
  have hinv := i1810_map_component_eq hO Q ρ hρQ hK
  set ρK := i1810_restrict ρ K hinv with hρK
  have : Group.IsSolvable (Outer K) :=
    CFSG.LocalAnalysis.GLTheoremB.outer_solvable_of_isQuasisimple hSch
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_subgroup' hX K)
      ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩
  obtain ⟨k0, hk0⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρK d
  have h1 : orderOf (ρK d) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hd, map_one]
  have h2 : orderOf (ρK d) ∣ Nat.card K := by
    rw [hk0]
    exact (orderOf_map_dvd _ _).trans (orderOf_dvd_natCard k0)
  have h3 : Nat.Coprime (p ^ k) (Nat.card K) :=
    Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card K) hpX)
  have h4 : ρK d = 1 := orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  intro x hx
  have h5 := congrArg (fun φ : MulAut K => ((φ ⟨x, hx⟩ : K) : X)) h4
  simp only [MulAut.one_apply] at h5
  rw [hρK, i1810_restrict_apply] at h5
  exact h5

theorem i1810_fixed_of_pElement (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hX : CFSG.Open.IsKGroup X) {p q : ℕ} [Fact q.Prime] (hpX : Nat.Coprime p (Nat.card X))
    (hO : CFSG.pPrimeCore q X = ⊥) (Q : Sylow q X) {D : Type*} [Group D] [Group.IsPerfect D]
    (ρ : D →* MulAut X) (hρQ : ∀ d : D, ∀ x ∈ (Q : Subgroup X), ρ d x = x)
    {d : D} {k : ℕ} (hd : d ^ p ^ k = 1) (x : X) : ρ d x = x := by
  set α := ρ d with hα
  set Fx : Subgroup X := MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X) with hFx
  have hmemFx : ∀ y : X, y ∈ Fx ↔ α y = y := fun y => Iff.rfl
  have hE : CFSG.layer X ≤ Fx := by
    refine sSup_le fun K hK y hy => ?_
    rw [hmemFx]
    exact i1810_component_fixed hSch hX hpX hO Q ρ hρQ hK hd y hy
  have hF : CFSG.fittingSubgroup X ≤ Fx := by
    rw [CFSG.Fitting_eq_pcore X q hO]
    intro y hy
    rw [hmemFx]
    exact hρQ d y (IsPGroup.le_sylow_of_normal (N := CFSG.pCore q X) CFSG.pCore_isPGroup Q hy)
  have hFs : CFSG.generalizedFitting X ≤ Fx := sup_le hF hE
  have hfix : ∀ y ∈ CFSG.generalizedFitting X, α y = y := fun y hy => (hmemFx y).1 (hFs hy)
  set c := x⁻¹ * α x with hc
  have hcC : c ∈ Subgroup.centralizer (CFSG.generalizedFitting X : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hxf : x * f * x⁻¹ ∈ CFSG.generalizedFitting X :=
      (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2.conj_mem f hf x
    have e1 := hfix _ hxf
    rw [map_mul, map_mul, map_inv, hfix f hf] at e1
    calc f * c = x⁻¹ * (x * f * x⁻¹) * α x := by rw [hc]; group
      _ = x⁻¹ * (α x * f * (α x)⁻¹) * α x := by rw [e1]
      _ = c * f := by rw [hc]; group
  have hcF : c ∈ CFSG.generalizedFitting X := CFSG.centralizer_generalizedFitting_le X hcC
  have hαc : α c = c := hfix c hcF
  have hαx : α x = x * c := by rw [hc]; group
  have hpow : ∀ n : ℕ, (α ^ n) x = x * c ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hαc, hαx, pow_succ', mul_assoc]
  have h1 : c ^ p ^ k = 1 := by
    have h := hpow (p ^ k)
    rw [hα, ← map_pow, hd, map_one, MulAut.one_apply] at h
    have h' : x * c ^ p ^ k = x * 1 := by rw [← h, mul_one]
    exact mul_left_cancel h'
  have h2 : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k hpX) (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_natCard c)
  rw [orderOf_eq_one_iff] at h2
  rw [hαx, h2, mul_one]

end Action

end CFSG.HardMathSupport.Solomon.Coordinator

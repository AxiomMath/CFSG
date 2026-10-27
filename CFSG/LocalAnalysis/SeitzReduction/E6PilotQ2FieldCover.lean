module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverFamilyNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotNeighbourParamLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Open CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.SeitzReduction.F4Pilot (F4Work QuadraticFrobenius centralizerPerfectCore)

local instance e6PilotQ2FieldCoverNeZeroRank : NeZero Tag.E6.rank := ⟨by decide⟩

section Lift

variable {E D : Type*} [Group E] [Group D]

theorem eq_of_map_eq_of_mul_self_eq_one [Finite E] {p : E →* D} (hker : p.ker ≤ center E)
    (hodd : Odd (Nat.card p.ker)) {y₁ y₂ : E} (hp : p y₁ = p y₂) (h₁ : y₁ * y₁ = 1)
    (h₂ : y₂ * y₂ = 1) : y₁ = y₂ := by
  set c := y₁⁻¹ * y₂ with hc
  have hck : c ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]
  have hcz := mem_center_iff.1 (hker hck)
  have hy₂ : y₂ = y₁ * c := by rw [hc, mul_inv_cancel_left]
  have hcc : c * c = 1 := by
    have h3 : y₂ * y₂ = y₁ * y₁ * (c * c) := by
      rw [hy₂]
      calc y₁ * c * (y₁ * c) = y₁ * (c * y₁) * c := by group
        _ = y₁ * (y₁ * c) * c := by rw [hcz y₁]
        _ = y₁ * y₁ * (c * c) := by group
    rw [h₁, h₂, one_mul] at h3
    exact h3.symm
  have hord : orderOf (⟨c, hck⟩ : p.ker) ∣ Nat.card p.ker := orderOf_dvd_natCard _
  have hord2 : orderOf (⟨c, hck⟩ : p.ker) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by rw [Subgroup.coe_pow, sq, hcc]; rfl))
  have h1 : orderOf (⟨c, hck⟩ : p.ker) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hord2 with h | h
    · exact h
    · rw [h] at hord
      exact absurd (hodd.of_dvd_nat hord) (by decide)
  have hc1 : c = 1 := congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  rw [hy₂, hc1, mul_one]

theorem exists_map_eq_mul_self_eq_one [Finite E] {p : E →* D} (hker : p.ker ≤ center E)
    (hodd : Odd (Nat.card p.ker)) {y₀ : E} (hu : p y₀ * p y₀ = 1) :
    ∃ y : E, p y = p y₀ ∧ y * y = 1 := by
  set z := y₀ * y₀ with hzdef
  have hz : z ∈ p.ker := by rw [MonoidHom.mem_ker, map_mul]; exact hu
  obtain ⟨m, hm⟩ := hodd
  have hzm : z ^ (2 * m + 1) = 1 := by
    have h1 : (⟨z, hz⟩ : p.ker) ^ Nat.card p.ker = 1 := pow_card_eq_one'
    rw [hm] at h1
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow] at h2
  set w : E := z ^ (m + 1) with hwdef
  have hw : w ∈ p.ker := pow_mem hz _
  have hww : w * w = z := by
    rw [hwdef, ← pow_add, show m + 1 + (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, hzm, one_mul]
  have hwz := mem_center_iff.1 (hker hw)
  refine ⟨y₀ * w⁻¹, by rw [map_mul, map_inv, MonoidHom.mem_ker.1 hw, inv_one, mul_one], ?_⟩
  have hwi : ∀ g : E, g * w⁻¹ = w⁻¹ * g := fun g => by
    have := hwz g
    calc g * w⁻¹ = w⁻¹ * (w * g) * w⁻¹ := by group
      _ = w⁻¹ * (g * w) * w⁻¹ := by rw [this]
      _ = w⁻¹ * g := by group
  calc y₀ * w⁻¹ * (y₀ * w⁻¹) = y₀ * (w⁻¹ * y₀) * w⁻¹ := by group
    _ = y₀ * (y₀ * w⁻¹) * w⁻¹ := by rw [hwi y₀]
    _ = z * (w * w)⁻¹ := by rw [hzdef]; group
    _ = 1 := by rw [hww, mul_inv_cancel]

theorem ker_comp_symm {X Y Z : Type*} [Group X] [Group Y] [Group Z] (ψ : X ≃* Y) (p : X →* Z) :
    (p.comp ψ.symm.toMonoidHom).ker = p.ker.map ψ.toMonoidHom := by
  ext y
  constructor
  · intro hy
    exact ⟨ψ.symm y, hy, by simp⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : p x = 1 := hx
    rw [MonoidHom.mem_ker]
    simpa using hx'

end Lift

section Cover

variable {K : Type} [Field K] (σ : K ≃+* K) {G : Type} [Group G] {L : Subgroup G}
  (e : L ≃* adjointGroup .E6 (fixSubfield σ))

structure TwoCover (N : E6Neighbour) (E : Subgroup G) where
  p : E →* N.levi K
  surjective : Function.Surjective p
  ker_le_center : p.ker ≤ center E
  odd_card_ker : Odd (Nat.card p.ker)
  fix : ∀ x : N.levi (fixSubfield σ), ∃ y : E,
    (y : G) = ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) ∧
      p y = leviInclusion σ N x

variable {σ e}

@[expose] noncomputable def TwoCover.congr {N : E6Neighbour} {E E' : Subgroup G}
    (h : TwoCover σ e N E) (hE : E = E') : TwoCover σ e N E' where
  p := h.p.comp (MulEquiv.subgroupCongr hE).symm.toMonoidHom
  surjective := h.surjective.comp (MulEquiv.subgroupCongr hE).symm.surjective
  ker_le_center := by
    rw [ker_comp_symm]
    exact map_le_center_of_le_center _ h.ker_le_center
  odd_card_ker := by
    rw [ker_comp_symm, card_map_of_injective (MulEquiv.subgroupCongr hE).injective]
    exact h.odd_card_ker
  fix x := by
    obtain ⟨y, hy, hpy⟩ := h.fix x
    exact ⟨MulEquiv.subgroupCongr hE y, hy, by simpa using hpy⟩

theorem TwoCover.congr_p_apply {N : E6Neighbour} {E E' : Subgroup G} (h : TwoCover σ e N E)
    (hE : E = E') (y : E') : (h.congr hE).p y = h.p ⟨(y : G), hE ▸ y.2⟩ :=
  rfl

@[expose] noncomputable def TwoCover.toNeighbour {E : Subgroup G} (h : TwoCover σ e .high E)
    (N : E6Neighbour) :
    TwoCover σ e N
      (E.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom) where
  p := (highLeviConjEquiv K N).toMonoidHom.comp (h.p.comp
    ((E.equivMapOfInjective
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).injective)).symm.toMonoidHom)
  surjective := by
    intro z
    obtain ⟨y, hy⟩ := h.surjective ((highLeviConjEquiv K N).symm z)
    refine ⟨(E.equivMapOfInjective
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).injective) y, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hy,
      MulEquiv.apply_symm_apply]
  ker_le_center := by
    rw [ker_comp_comp_symm]
    exact map_le_center_of_le_center _ h.ker_le_center
  odd_card_ker := by
    rw [ker_comp_comp_symm, card_map_of_injective (MulEquiv.injective _)]
    exact h.odd_card_ker
  fix x := by
    obtain ⟨x₀, rfl⟩ := (highLeviConjEquiv (fixSubfield σ) N).surjective x
    obtain ⟨y₀, hy₀, hpy₀⟩ := h.fix x₀
    refine ⟨(E.equivMapOfInjective
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).injective) y₀, ?_, ?_⟩
    · change ((e.symm (N.rep (fixSubfield σ)) : L) : G) * (y₀ : G) *
          ((e.symm (N.rep (fixSubfield σ)) : L) : G)⁻¹ =
        ((e.symm (N.rep (fixSubfield σ) * (x₀ : adjointGroup .E6 (fixSubfield σ)) *
          (N.rep (fixSubfield σ))⁻¹) : L) : G)
      rw [hy₀, map_mul, map_mul, map_inv, L.coe_mul, L.coe_mul, L.coe_inv]
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rw [hpy₀, leviInclusion, leviInclusion, leviBaseChange_highLeviConjEquiv]

theorem TwoCover.toNeighbour_p_apply {E : Subgroup G} (h : TwoCover σ e .high E) (N : E6Neighbour)
    (y : E) :
    (h.toNeighbour N).p ((E.equivMapOfInjective
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).injective) y) =
      highLeviConjEquiv K N (h.p y) := by
  simp only [TwoCover.toNeighbour, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

end Cover

section Lifts

variable {K : Type} [Field K] {σ : K ≃+* K} {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

@[expose] def TwoCover.IsLift {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    (u : N.levi K) (g : G) : Prop :=
  ∃ y : E, (y : G) = g ∧ h.p y = u ∧ y * y = 1

theorem TwoCover.IsLift.eq {N : E6Neighbour} {E : Subgroup G} {h : TwoCover σ e N E}
    {u : N.levi K} {g₁ g₂ : G} (h₁ : h.IsLift u g₁) (h₂ : h.IsLift u g₂) : g₁ = g₂ := by
  obtain ⟨y₁, rfl, hp₁, hy₁⟩ := h₁
  obtain ⟨y₂, rfl, hp₂, hy₂⟩ := h₂
  rw [eq_of_map_eq_of_mul_self_eq_one h.ker_le_center h.odd_card_ker (hp₁.trans hp₂.symm) hy₁ hy₂]

theorem TwoCover.exists_isLift {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    {u : N.levi K} (hu : u * u = 1) : ∃ g, h.IsLift u g := by
  obtain ⟨y₀, rfl⟩ := h.surjective u
  obtain ⟨y, hy, hyy⟩ := exists_map_eq_mul_self_eq_one h.ker_le_center h.odd_card_ker hu
  exact ⟨y, y, rfl, hy, hyy⟩

theorem TwoCover.IsLift.conj {N : E6Neighbour} {E : Subgroup G} {h : TwoCover σ e N E}
    {u : N.levi K} {g : G} (hg : h.IsLift u g) (x : N.levi (fixSubfield σ)) :
    h.IsLift (leviInclusion σ N x * u * (leviInclusion σ N x)⁻¹)
      (((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) * g *
        ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G)⁻¹) := by
  obtain ⟨y, rfl, hpy, hyy⟩ := hg
  obtain ⟨n, hn, hpn⟩ := h.fix x
  refine ⟨n * y * n⁻¹, by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hn], ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hpy, hpn]
  · calc n * y * n⁻¹ * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
      _ = 1 := by rw [hyy, mul_one, mul_inv_cancel]

theorem TwoCover.isLift_leviInclusion {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    (x : N.levi (fixSubfield σ)) (hx : x * x = 1) :
    h.IsLift (leviInclusion σ N x) ((e.symm (x : adjointGroup .E6 (fixSubfield σ)) : L) : G) := by
  obtain ⟨y, hy, hpy⟩ := h.fix x
  refine ⟨y, hy, hpy, Subtype.ext ?_⟩
  rw [Subgroup.coe_mul, hy, OneMemClass.coe_one, ← L.coe_mul, ← map_mul]
  have hx' : (x : adjointGroup .E6 (fixSubfield σ)) * x = 1 := congrArg Subtype.val hx
  rw [hx', map_one, L.coe_one]

end Lifts

@[expose] def tripleRoot : Fin (Tag.rank .E6) → ℤ := ![1, 0, 1, 1, 0, 0]

@[expose] def tripleLo : E6Neighbour → Fin 6
  | .high => 0
  | .six => 1
  | .three => 3

@[expose] def tripleHi : E6Neighbour → Fin 6
  | .high => 3
  | .six => 4
  | .three => 4

@[expose] def tripleFree : E6Neighbour → Fin 6
  | .high => 1
  | .six => 0
  | .three => 0

theorem tripleLo_ne_tripleHi (N : E6Neighbour) : tripleLo N ≠ tripleHi N := by
  cases N <;> decide

theorem tripleFree_ne (N : E6Neighbour) :
    tripleLo N ≠ tripleFree N ∧ tripleHi N ≠ tripleFree N := by
  cases N <;> decide

theorem weyl_smul_tripleA5 (N : E6Neighbour) :
    N.weyl • a5Root (tripleLo N) (tripleHi N) = tripleRoot := by
  cases N <;> simp only [E6Neighbour.weyl, E6Neighbour.word, CoxeterSystem.wordProd_cons,
    CoxeterSystem.wordProd_nil, mul_one, mul_smul, simple_smul, one_smul] <;>
    exact List.ofFn_injective (by decide +kernel)

theorem iform_root_tripleRoot (N : E6Neighbour) : iform N.root tripleRoot = 0 := by
  cases N <;> decide +kernel

section Triple

theorem isRoot_tripleRoot : IsRoot .E6 tripleRoot := by
  have h := isRoot_a5Root (tripleLo_ne_tripleHi .high)
  have h2 := weyl_smul_tripleA5 .high
  rw [← h2]
  exact IsRoot.smul h _

theorem tripleRoot_mem_orthRoots (N : E6Neighbour) : tripleRoot ∈ orthRoots N.root :=
  ⟨isRoot_tripleRoot, iform_root_tripleRoot N⟩

theorem neg_tripleRoot_mem_orthRoots (N : E6Neighbour) : -tripleRoot ∈ orthRoots N.root :=
  ⟨IsRoot.neg isRoot_tripleRoot, by rw [iform_neg_right_E6, iform_root_tripleRoot, neg_zero]⟩

variable (K : Type) [Field K]

@[expose] noncomputable def tripleRootSL2 : Subgroup (adjointGroup .E6 K) :=
  (rootSpan .E6 K {tripleRoot, -tripleRoot}).subgroupOf (adjointGroup .E6 K)

variable {K}

theorem tripleRootSL2_le_levi (N : E6Neighbour) : tripleRootSL2 K ≤ N.levi K := by
  refine Subgroup.subgroupOf_mono _ (rootSpan_mono_E6 ?_)
  intro γ hγ
  rcases hγ with rfl | hγ
  · exact tripleRoot_mem_orthRoots N
  · rw [Set.mem_singleton_iff] at hγ
    rw [hγ]
    exact neg_tripleRoot_mem_orthRoots N

end Triple

section Sections

variable {K : Type} [Field K] [Finite K] [CharP K 2] {σ : K ≃+* K} {G : Type} [Group G]
  {L : Subgroup G} {e : L ≃* adjointGroup .E6 (fixSubfield σ)}

theorem TwoCover.exists_sl6Lift {E : Subgroup G} (h : TwoCover σ e .high E) :
    ∃ Ψ : Matrix.SpecialLinearGroup (Fin 6) K →* E, ∀ A,
      ((h.p (Ψ A) : E6Neighbour.high.levi K) : adjointGroup .E6 K) = slToAdjointE6 K A := by
  set β : Matrix.SpecialLinearGroup (Fin 6) K →* E6Neighbour.high.levi K :=
    (MulEquiv.subgroupCongr (E6Neighbour.levi_high K).symm).toMonoidHom.comp slToA5Levi with hβ
  obtain ⟨s, hs⟩ := UnitaryPilot.exists_section_specialLinear_of_five_le (by norm_num : 3 ≤ 6)
    (Or.inr (by norm_num))
    (CFSG.LieType.Steinberg.pullbackFst_surjective (β := β) h.surjective)
    (CFSG.LieType.Steinberg.ker_pullbackFst_le_center h.ker_le_center)
  refine ⟨((MonoidHom.snd _ _).comp (CFSG.LieType.Steinberg.pullback β h.p).subtype).comp s,
    fun A => ?_⟩
  have hmem := CFSG.LieType.Steinberg.mem_pullback.1 (s A).2
  have h1 : ((s A : CFSG.LieType.Steinberg.pullback β h.p) :
      Matrix.SpecialLinearGroup (Fin 6) K × E).1 = A := hs A
  change (((h.p ((s A : CFSG.LieType.Steinberg.pullback β h.p) :
    Matrix.SpecialLinearGroup (Fin 6) K × E).2 : E6Neighbour.high.levi K)) :
      adjointGroup .E6 K) = _
  rw [← hmem, h1]
  rfl

theorem TwoCover.exists_sl6Lift_toNeighbour {E : Subgroup G} (h : TwoCover σ e .high E)
    (N : E6Neighbour) :
    ∃ Ψ : Matrix.SpecialLinearGroup (Fin 6) K →*
        E.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom, ∀ A,
      (((h.toNeighbour N).p (Ψ A) : N.levi K) : adjointGroup .E6 K) =
        N.rep K * slToAdjointE6 K A * (N.rep K)⁻¹ := by
  obtain ⟨Ψ, hΨ⟩ := h.exists_sl6Lift
  refine ⟨(E.equivMapOfInjective
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom
      (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).injective).toMonoidHom.comp Ψ,
    fun A => ?_⟩
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, TwoCover.toNeighbour_p_apply]
  apply Subtype.ext
  rw [coe_highLeviConjEquiv, hΨ]
  rfl

theorem TwoCover.exists_section_of_sl6 {N : E6Neighbour} {E : Subgroup G} (h : TwoCover σ e N E)
    {Ψ : Matrix.SpecialLinearGroup (Fin 6) K →* E}
    (hΨ : ∀ A, ((h.p (Ψ A) : N.levi K) : adjointGroup .E6 K) =
      N.rep K * slToAdjointE6 K A * (N.rep K)⁻¹)
    {x : Fin 6} {H : Subgroup (adjointGroup .E6 K)}
    (hH : ∀ y ∈ H, (N.rep K)⁻¹ * y * N.rep K ∈ (fixBasisSL x).map (slToAdjointE6 K)) :
    ∃ s : H →* E, ∀ y, ((h.p (s y) : N.levi K) : adjointGroup .E6 K) = y := by
  set φB := (slToAdjointE6 K).comp (fixBasisSL x).subtype with hφB
  have hinj := injective_slToAdjointE6_restrict_fixBasisSL (K := K) x
  have hrange : φB.range = (fixBasisSL x).map (slToAdjointE6 K) := by
    rw [hφB, MonoidHom.range_comp, range_subtype]
  set ι' : H →* φB.range :=
    (((MulAut.conj (N.rep K)⁻¹).toMonoidHom.comp H.subtype).codRestrict φB.range fun y => by
      rw [hrange]
      simpa [MulAut.conj_apply] using hH y y.2) with hι'
  refine ⟨Ψ.comp ((fixBasisSL x).subtype.comp
    ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp ι')), fun y => ?_⟩
  rw [MonoidHom.comp_apply, hΨ]
  have h1 := (MonoidHom.ofInjective hinj).apply_symm_apply (ι' y)
  have h2 := congrArg Subtype.val h1
  rw [MonoidHom.ofInjective_apply] at h2
  change N.rep K * φB ((MonoidHom.ofInjective hinj).symm (ι' y)) * (N.rep K)⁻¹ = y
  rw [h2]
  change N.rep K * ((N.rep K)⁻¹ * y * (N.rep K)⁻¹⁻¹) * (N.rep K)⁻¹ = y
  group

theorem conj_rep_mem_map_fixBasisSL {N : E6Neighbour} {S : Set (Fin (Tag.rank .E6) → ℤ)}
    {x : Fin 6} (hS : ∀ γ ∈ S, ∃ a b : Fin 6, ∃ _ : a ≠ b, b ≠ x ∧ a5Root a b = γ)
    {y : adjointGroup .E6 K}
    (hy : (y : ModGL .E6 K) ∈ rootSpan .E6 K ((fun α => N.weyl • α) '' S)) :
    (N.rep K)⁻¹ * y * N.rep K ∈ (fixBasisSL x).map (slToAdjointE6 K) := by
  have hSroot : ∀ γ ∈ S, IsRoot .E6 γ := by
    intro γ hγ
    obtain ⟨a, b, hab, -, rfl⟩ := hS γ hγ
    exact isRoot_a5Root hab
  rw [← map_conj_rep_rootSpan N hSroot] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨w, hw, hwz⟩ := rootSpan_le_map_fixBasisSL hS hz
  have hzy' : (N.rep K : ModGL .E6 K) * z * (N.rep K : ModGL .E6 K)⁻¹ = (y : ModGL .E6 K) := hzy
  have h3 : (N.rep K)⁻¹ * y * N.rep K = w := by
    apply Subtype.ext
    have hwz' : (w : ModGL .E6 K) = z := hwz
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hzy', hwz']
    group
  rw [h3]
  exact hw

theorem TwoCover.exists_section_tripleRootSL2 {E : Subgroup G} (h : TwoCover σ e .high E)
    (N : E6Neighbour) :
    ∃ s : tripleRootSL2 K →*
        E.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom,
      ∀ y, (((h.toNeighbour N).p (s y) : N.levi K) : adjointGroup .E6 K) = y := by
  obtain ⟨Ψ, hΨ⟩ := h.exists_sl6Lift_toNeighbour N
  refine (h.toNeighbour N).exists_section_of_sl6 hΨ (x := tripleFree N) fun y hy => ?_
  refine conj_rep_mem_map_fixBasisSL (S := {a5Root (tripleLo N) (tripleHi N),
    a5Root (tripleHi N) (tripleLo N)}) ?_ ?_
  · intro γ hγ
    rcases hγ with rfl | hγ
    · exact ⟨_, _, tripleLo_ne_tripleHi N, (tripleFree_ne N).2, rfl⟩
    · rw [Set.mem_singleton_iff] at hγ
      exact ⟨_, _, (tripleLo_ne_tripleHi N).symm, (tripleFree_ne N).1, hγ.symm⟩
  · have himage : (fun α => N.weyl • α) '' {a5Root (tripleLo N) (tripleHi N),
        a5Root (tripleHi N) (tripleLo N)} = {tripleRoot, -tripleRoot} := by
      rw [Set.image_pair, weyl_smul_tripleA5, a5Root_swap_E6, smul_neg, weyl_smul_tripleA5]
    rw [himage]
    exact mem_subgroupOf.1 hy

theorem TwoCover.exists_section_levi {E : Subgroup G} (h : TwoCover σ e .high E)
    (N : E6Neighbour) {J : Finset (Fin (Tag.rank .E6))} (hJ : J ⊆ N.nodes) (hJ2 : J.card ≤ 2) :
    ∃ s : CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J →*
        E.map (MulAut.conj ((e.symm (N.rep (fixSubfield σ)) : L) : G)).toMonoidHom,
      ∀ y, (((h.toNeighbour N).p (s y) : N.levi K) : adjointGroup .E6 K) = y := by
  obtain ⟨Ψ, hΨ⟩ := h.exists_sl6Lift_toNeighbour N
  have hy0 : ∀ y ∈ CFSG.LieType.CurtisTits.levi (adjDatumE6 K).rootGroup J,
      (y : ModGL .E6 K) ∈ rootSpan .E6 K (amalgamRoots J) := fun y hy => by
    rw [levi_adjDatumE6_eq, mem_subgroupOf] at hy
    exact hy
  set S : Set (Fin (Tag.rank .E6) → ℤ) := {γ | ∃ j ∈ J,
    γ = a5Root (nbLo N j) (nbHi N j) ∨ γ = a5Root (nbHi N j) (nbLo N j)} with hSdef
  have hw : ∀ j ∈ J, N.weyl • a5Root (nbLo N j) (nbHi N j) = Pi.single j 1 := by
    intro j hj
    by_cases hN : N = .high
    · subst hN
      have hj1 : j ≠ 1 := by
        intro h1
        have := hJ hj
        rw [h1, nodes_high_eq] at this
        exact one_not_mem_nodes_high this
      simp only [E6Neighbour.weyl, E6Neighbour.word, CoxeterSystem.wordProd_nil, one_smul]
      exact (a5Root_lo_hi_check j hj1).1
    · exact (nb_data (by cases N <;> simp_all) (hJ hj)).1
  have himage : amalgamRoots J ⊆ (fun α => N.weyl • α) '' S := by
    rintro γ ⟨j, hj, rfl | rfl⟩
    · exact ⟨_, ⟨j, hj, Or.inl rfl⟩, hw j hj⟩
    · refine ⟨_, ⟨j, hj, Or.inr rfl⟩, ?_⟩
      change N.weyl • a5Root (nbHi N j) (nbLo N j) = _
      rw [a5Root_swap_E6, smul_neg, hw j hj]
  obtain ⟨x, hx⟩ : ∃ x : Fin 6, ∀ j ∈ J, nbLo N j ≠ x ∧ nbHi N j ≠ x := by
    by_cases hN : N = .high
    · subst hN
      exact exists_coord_not_mem_check (J : Finset (Fin 6)) (fun l hl => by
        have := hJ hl
        rw [nodes_high_eq] at this
        exact this) hJ2
    · refine ⟨nbFree N, fun j hj => ?_⟩
      have := nb_data (by cases N <;> simp_all) (hJ hj)
      exact ⟨this.2.1, this.2.2⟩
  refine (h.toNeighbour N).exists_section_of_sl6 hΨ (x := x) fun y hy =>
    conj_rep_mem_map_fixBasisSL (S := S) ?_ (rootSpan_mono_E6 himage (hy0 y hy))
  rintro γ ⟨j, hj, rfl | rfl⟩
  · exact ⟨_, _, nbLo_ne_nbHi N j, (hx j hj).2, rfl⟩
  · exact ⟨_, _, (nbLo_ne_nbHi N j).symm, (hx j hj).1, rfl⟩

end Sections

end CFSG.SeitzReduction.E6Pilot

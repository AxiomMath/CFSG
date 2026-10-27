module

public import CFSG.Holt.H78.SEModel
public import CFSG.Holt.H78.Defs
public import CFSG.Holt.PSL2Natural.Basic

public section

namespace CFSG.Holt.H78

open MulAction CFSG.GH74.Uniqueness.Bender
open scoped Pointwise LinearAlgebra.Projectivization

namespace IsBenderAction

variable {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω] {n i e : ℕ}

theorem of_equiv {Y : Type*} [Group Y] {Ω' : Type*} [MulAction Y Ω']
    (hA : IsBenderAction X Ω n i e) (φ : X ≃* Y) (ψ : Ω ≃ Ω')
    (hψ : ∀ (x : X) (ω : Ω), ψ (x • ω) = φ x • ψ ω) : IsBenderAction Y Ω' n i e where
  benderType := hA.benderType.of_mulEquiv φ
  isPretransitive := by
    have := hA.isPretransitive
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, hx⟩ := exists_smul_eq X (ψ.symm a) (ψ.symm b)
    exact ⟨φ x, by rw [← ψ.apply_symm_apply a, ← hψ, hx, ψ.apply_symm_apply]⟩
  card_eq := by rw [← Nat.card_congr ψ, hA.card_eq]

theorem nontrivial (hA : IsBenderAction X Ω n i e) : Nontrivial Ω := by
  have := hA.finite
  exact Finite.one_lt_card_iff_nontrivial.mp (by rw [hA.card_eq]; have := hA.four_le_pow; omega)

theorem faithfulSMul [Finite X] (hA : IsBenderAction X Ω n i e) : FaithfulSMul X Ω := by
  have := hA.isPretransitive
  have : IsSimpleGroup X := hA.benderType.isSimple
  have hker : (toPermHom X Ω).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (toPermHom X Ω).ker with h | h
    · exact h
    · exfalso
      have := hA.nontrivial
      obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
      obtain ⟨x, hx⟩ := exists_smul_eq X a b
      have hxk : x ∈ (toPermHom X Ω).ker := h ▸ Subgroup.mem_top x
      have hxa : x • a = a := by
        simpa using congrArg (fun π : Equiv.Perm Ω => π a) (MonoidHom.mem_ker.mp hxk)
      exact hab (hxa.symm.trans hx)
  refine ⟨fun {x y} h => ?_⟩
  have hmem : x⁻¹ * y ∈ (toPermHom X Ω).ker := by
    rw [MonoidHom.mem_ker]
    ext ω
    simp [mul_smul, ← h ω]
  rw [hker, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

theorem exists_equiv [Finite X] {Y : Type*} [Group Y] [Finite Y] {Ω' : Type*} [MulAction Y Ω']
    {n' i' e' : ℕ} (hA : IsBenderAction X Ω n i e) (hB : IsBenderAction Y Ω' n' i' e')
    (φ : X ≃* Y) : ∃ ψ : Ω ≃ Ω', ∀ (x : X) (ω : Ω), ψ (x • ω) = φ x • ψ ω := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hA.isPretransitive
  have := hB.isPretransitive
  have := hA.nontrivial
  obtain ⟨ω₀⟩ : Nonempty Ω := inferInstance
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer ω₀
  set Q' : Sylow 2 Y := Q.mapSurjective (f := φ.toMonoidHom) φ.surjective
  have hQ' : (Q' : Subgroup Y) = (Q : Subgroup X).map φ.toMonoidHom :=
    Sylow.coe_mapSurjective φ.surjective Q
  obtain ⟨ω₁, hω₁, -⟩ := hB.existsUnique_le_stabilizer Q'
  have hstab : ∀ x : X, x • ω₀ = ω₀ ↔ φ x • ω₁ = ω₁ := by
    intro x
    rw [← mem_stabilizer_iff, ← mem_stabilizer_iff (a := ω₁), hA.stabilizer_eq_borel hQ,
      hB.stabilizer_eq_borel hω₁, hQ', borel_map, Subgroup.mem_map_equiv]
    simp
  choose g hg using fun ω : Ω => exists_smul_eq X ω₀ ω
  set f : Ω → Ω' := fun ω => φ (g ω) • ω₁ with hf
  have key : ∀ x : X, f (x • ω₀) = φ x • ω₁ := by
    intro x
    have h1 : (x⁻¹ * g (x • ω₀)) • ω₀ = ω₀ := by rw [mul_smul, hg, inv_smul_smul]
    have h2 := (hstab _).mp h1
    rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff] at h2
    exact h2
  have hequiv : ∀ (x : X) (ω : Ω), f (x • ω) = φ x • f ω := by
    intro x ω
    conv_lhs => rw [← hg ω, ← mul_smul, key, map_mul, mul_smul]
  have hinj : Function.Injective f := by
    intro ω ω' hω
    have h1 : φ ((g ω)⁻¹ * g ω') • ω₁ = ω₁ := by
      rw [map_mul, mul_smul, map_inv, inv_smul_eq_iff]
      exact hω.symm
    have h2 := (hstab _).mpr h1
    rw [mul_smul, inv_smul_eq_iff, hg, hg] at h2
    exact h2.symm
  have hsurj : Function.Surjective f := by
    intro ω'
    obtain ⟨y, hy⟩ := exists_smul_eq Y ω₁ ω'
    refine ⟨φ.symm y • ω₀, ?_⟩
    rw [key, MulEquiv.apply_symm_apply, hy]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hequiv⟩

end IsBenderAction

theorem isBenderAction_projectiveLine {n : ℕ} (hn : 2 ≤ n) :
    IsBenderAction (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) n 1 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) = 2 ^ n + 1 := by
    rw [PSL2Natural.card_projectiveLine, GaloisField.card 2 n (by omega)]
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : Finite (ℙ (GaloisField 2 n) (Fin 2 → GaloisField 2 n)) :=
    Nat.finite_of_card_ne_zero (by omega)
  exact ⟨.linear n hn (MulEquiv.refl _),
    (PSL2Natural.isSharplyThreeTransitive (GaloisField 2 n)).isPretransitive (by omega),
    by rw [hcard, pow_one]⟩

theorem IsBenderAction.isNaturalPSL2 {Δ : Type*} {M : Subgroup (Equiv.Perm Δ)} [Finite M]
    {n e : ℕ} (hA : IsBenderAction M Δ n 1 e) : IsNaturalPSL2 M n := by
  obtain ⟨hn, ⟨φ⟩⟩ : 2 ≤ n ∧ Nonempty (M ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    have h := hA.benderType
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hB := isBenderAction_projectiveLine hn
  have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
    Finite.of_equiv _ φ.toEquiv
  obtain ⟨ψ, hψ⟩ := hB.exists_equiv hA φ.symm
  exact ⟨φ.symm, ψ, fun g p => hψ g p⟩

theorem fusionBenderBorel_of_benderType {X : Type*} [Group X] [Finite X] {n i e : ℕ}
    (hX : BenderType X n i e) : CFSG.Open.fusionBenderBorel X (2 ^ n) i := by
  intro Q
  obtain ⟨t, hc⟩ := hX.exists_benderCore Q
  refine ⟨hc.strong, ⟨cartan Q t, hc.isCyclic, hc.odd_card_cartan, hc.inf_eq, hc.sup_eq⟩, ?_, ?_,
    hc.card_eq⟩
  · intro z hz
    have hz' : (z : X) ∈ rootCenter (Q : Subgroup X) := by
      rw [rootCenter_eq_map_center]
      exact ⟨z, hz, rfl⟩
    exact Subtype.ext (by simpa [sq] using hc.center_sq _ hz')
  · rw [← hc.card_center, rootCenter_eq_map_center,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

namespace IsBenderNormal

variable {K : Type*} [Group K] {Ω : Type*} [MulAction K Ω] {N : Subgroup K} {q i : ℕ}

theorem isBenderAction (h : IsBenderNormal Ω N q i) :
    ∃ n e : ℕ, q = 2 ^ n ∧ IsBenderAction N Ω n i e := by
  have hpre := h.isPretransitive
  have hcard := h.card_eq
  rcases h.model with ⟨rfl, f, hf, rfl, ⟨φ⟩⟩ | ⟨rfl, a, ha, rfl, ⟨φ⟩⟩ | ⟨rfl, f, hf, rfl, ⟨φ⟩⟩
  · exact ⟨f, 1, rfl, .linear f hf φ, hpre, hcard⟩
  · exact ⟨2 * a + 1, 1, rfl,
      .suzuki a ha (φ.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)), hpre, hcard⟩
  · have hmodel : CFSG.Open.PSU3 2 f = CFSG.Theory.Comparator.PSU3Model f := by
      simp only [CFSG.Open.PSU3, CFSG.Theory.Comparator.PSU3Model]
    exact ⟨f, _, rfl, .unitary f hf (φ.trans (MulEquiv.subgroupCongr hmodel)), hpre, hcard⟩

theorem benderType (h : IsBenderNormal Ω N q i) : ∃ n e : ℕ, q = 2 ^ n ∧ BenderType N n i e := by
  obtain ⟨n, e, hq, hA⟩ := isBenderAction h
  exact ⟨n, e, hq, hA.benderType⟩

theorem of_isBenderAction [Finite K] {n e : ℕ} (hN : N.Normal) (hodd : Odd N.index)
    (hA : IsBenderAction N Ω n i e)
    (hnat : i = 1 → IsNaturalPSL2 (N.map (MulAction.toPermHom K Ω)) n) :
    IsBenderNormal Ω N (2 ^ n) i where
  normal := hN
  odd_index := hodd
  model := by
    have h := hA.benderType
    cases h with
    | linear n hn φ => exact Or.inl ⟨rfl, n, hn, rfl, ⟨φ⟩⟩
    | suzuki a ha φ =>
      exact Or.inr (Or.inl ⟨rfl, a, ha, rfl,
        ⟨φ.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a))⟩⟩)
    | unitary n hn φ =>
      have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
          CFSG.Models.benderPSU3Model_eq_psu3 n
      exact Or.inr (Or.inr ⟨rfl, n, hn, rfl, ⟨φ.trans (MulEquiv.subgroupCongr hmodel)⟩⟩)
  benderBorel := fusionBenderBorel_of_benderType hA.benderType
  isPretransitive := hA.isPretransitive
  card_eq := hA.card_eq
  stabilizer_eq_normalizer := fun _ _ hQ => hA.stabilizer_eq_borel hQ
  natural := fun f hi hq => by
    obtain rfl : n = f := Nat.pow_right_injective (le_refl 2) hq
    exact hnat hi

end IsBenderNormal

section NaturalSE

variable {Δ : Type*}

theorem toPermHom_subgroup_eq (M : Subgroup (Equiv.Perm Δ)) :
    MulAction.toPermHom M Δ = M.subtype :=
  MonoidHom.ext fun _ => Equiv.ext fun _ => rfl

theorem isNaturalSE_iff [Finite Δ] {M : Subgroup (Equiv.Perm Δ)} :
    IsNaturalSE M ↔ ∃ n i e : ℕ, IsBenderAction M Δ n i e := by
  constructor
  · rintro ⟨q, i, h⟩
    obtain ⟨n, e, -, hA⟩ := IsBenderNormal.isBenderAction h
    exact ⟨n, i, e, hA.of_equiv Subgroup.topEquiv (Equiv.refl Δ) fun _ _ => rfl⟩
  · rintro ⟨n, i, e, hA⟩
    have hA' : IsBenderAction (⊤ : Subgroup M) Δ n i e :=
      hA.of_equiv Subgroup.topEquiv.symm (Equiv.refl Δ) fun _ _ => rfl
    refine ⟨2 ^ n, i, IsBenderNormal.of_isBenderAction inferInstance
      (by rw [Subgroup.index_top]; exact odd_one) hA' fun hi => ?_⟩
    rw [toPermHom_subgroup_eq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    subst hi
    exact hA.isNaturalPSL2

theorem isNaturalSE_of_isBenderNormal {K : Type*} [Group K] [Finite K] {Ω : Type*}
    [MulAction K Ω] [Finite Ω] {N : Subgroup K} {q i : ℕ} (h : IsBenderNormal Ω N q i) :
    IsNaturalSE (N.map (MulAction.toPermHom K Ω)) := by
  obtain ⟨n, e, -, hA⟩ := IsBenderNormal.isBenderAction h
  have := hA.faithfulSMul
  set ρ : N →* Equiv.Perm Ω := (MulAction.toPermHom K Ω).comp N.subtype
  have hρ : Function.Injective ρ := fun x y hxy =>
    eq_of_smul_eq_smul (α := Ω) fun ω => congrArg (fun π : Equiv.Perm Ω => π ω) hxy
  have hrange : ρ.range = N.map (MulAction.toPermHom K Ω) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact isNaturalSE_iff.mpr ⟨n, i, e, hA.of_equiv
    ((MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hrange)) (Equiv.refl Ω)
    fun _ _ => rfl⟩

theorem IsNaturalSE.map_permCongrHom [Finite Δ] {Δ' : Type*} [Finite Δ']
    {M : Subgroup (Equiv.Perm Δ)} (hM : IsNaturalSE M) (e : Δ ≃ Δ') :
    IsNaturalSE (M.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) := by
  obtain ⟨n, i, e', hA⟩ := isNaturalSE_iff.mp hM
  refine isNaturalSE_iff.mpr ⟨n, i, e', hA.of_equiv (e.permCongrHom.subgroupMap M) e
    fun m δ => ?_⟩
  change e ((m : Equiv.Perm Δ) δ) = ((e.permCongrHom.subgroupMap M m : Equiv.Perm Δ')) (e δ)
  rw [MulEquiv.coe_subgroupMap_apply, Equiv.permCongrHom_coe, Equiv.permCongr_apply,
    Equiv.symm_apply_apply]

theorem isNaturalSE_map_permCongrHom_iff [Finite Δ] {Δ' : Type*} [Finite Δ']
    {M : Subgroup (Equiv.Perm Δ)} (e : Δ ≃ Δ') :
    IsNaturalSE (M.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) ↔ IsNaturalSE M := by
  refine ⟨fun h => ?_, fun h => h.map_permCongrHom e⟩
  have h' := h.map_permCongrHom e.symm
  rwa [Subgroup.map_map, show ((e.symm.permCongrHom : Equiv.Perm Δ' →* Equiv.Perm Δ).comp
    (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) = MonoidHom.id _ from
      MonoidHom.ext fun p => Equiv.ext fun x => by simp, Subgroup.map_id] at h'

end NaturalSE

section Factors

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ] {Δ' : Type*} [Fintype Δ'] [DecidableEq Δ']

theorem map_alternatingGroup_permCongrHom (e : Δ ≃ Δ') :
    (alternatingGroup Δ).map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ') =
      alternatingGroup Δ' := by
  ext σ
  simp only [Subgroup.mem_map, Equiv.Perm.mem_alternatingGroup]
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    simpa [Equiv.Perm.sign_permCongr] using hτ
  · intro hσ
    refine ⟨e.symm.permCongr σ, by rwa [Equiv.Perm.sign_permCongr], ?_⟩
    ext x
    simp [Equiv.permCongr_apply]

private theorem map_permCongrHom_eq_alternatingGroup_iff (e : Δ ≃ Δ')
    {M : Subgroup (Equiv.Perm Δ)} :
    M.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ') = alternatingGroup Δ' ↔
      M = alternatingGroup Δ := by
  rw [← map_alternatingGroup_permCongrHom e]
  exact (Subgroup.map_injective e.permCongrHom.injective).eq_iff

theorem isHoltFactor_map_permCongrHom_iff (e : Δ ≃ Δ') {M : Subgroup (Equiv.Perm Δ)} :
    IsHoltFactor (M.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) ↔ IsHoltFactor M := by
  simp only [IsHoltFactor, map_permCongrHom_eq_alternatingGroup_iff,
    Fintype.card_congr e, isNaturalSE_map_permCongrHom_iff]

theorem isOuterFactor_map_permCongrHom_iff (e : Δ ≃ Δ') {M : Subgroup (Equiv.Perm Δ)} :
    IsOuterFactor (M.map (e.permCongrHom : Equiv.Perm Δ →* Equiv.Perm Δ')) ↔
      IsOuterFactor M := by
  simp only [IsOuterFactor, map_permCongrHom_eq_alternatingGroup_iff, Fintype.card_congr e]

theorem factorImage_toPermHom {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω] {L : Subgroup G}
    (hL : L ≤ jHull G Ω) :
    factorImage G Ω L ((MulAction.toPermHom G Ω).comp (jHull G Ω).subtype) =
      L.map (MulAction.toPermHom G Ω) := by
  rw [factorImage, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hL]

theorem isHoltFactor_factorImage_of_isBenderNormal {G : Type*} [Group G] [Finite G]
    {Ω : Type*} [MulAction G Ω] [Fintype Ω] [DecidableEq Ω] {N : Subgroup G} {q i : ℕ}
    (h : IsBenderNormal Ω N q i) (hN : N ≤ jHull G Ω) :
    IsHoltFactor (factorImage G Ω N ((MulAction.toPermHom G Ω).comp (jHull G Ω).subtype)) := by
  rw [factorImage_toPermHom hN]
  exact Or.inr (isNaturalSE_of_isBenderNormal h)

end Factors

namespace IsBenderAction

variable {X : Type*} [Group X] [Finite X] {Ω : Type*} [MulAction X Ω] {n i e : ℕ}

section LongInvolutions

theorem mem_longInv_iff (hA : IsBenderAction X Ω n i e) {x : X} :
    x ∈ longInv X Ω ↔ orderOf x = 2 :=
  ⟨fun h => h.1, fun h => ⟨h, hA.existsUnique_fixed h⟩⟩

theorem isConj_of_orderOf_eq_two (hA : IsBenderAction X Ω n i e) {x y : X}
    (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
  have hy2 : y * y = 1 := by rw [← sq, ← hy, pow_orderOf_eq_one]
  refine hA.benderType.lemma_3_4_a hx2 ?_ hy2 ?_
  · rintro rfl
    simp at hx
  · rintro rfl
    simp at hy

theorem mem_longInvAt_iff (hA : IsBenderAction X Ω n i e) {α : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X α) {x : X} :
    x ∈ longInvAt X Ω α ↔ x ∈ rootCenter (Q : Subgroup X) ∧ x ≠ 1 := by
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [← hc.involution_iff, mem_longInvAt, hA.mem_longInv_iff, hA.mem_borel_iff hQ, and_comm]

theorem closure_longInvAt (hA : IsBenderAction X Ω n i e) {α : Ω} {Q : Sylow 2 X}
    (hQ : (Q : Subgroup X) ≤ stabilizer X α) :
    Subgroup.closure (longInvAt X Ω α) = rootCenter (Q : Subgroup X) := by
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  rw [← hc.closure_involutions]
  congr 1
  ext x
  rw [Set.mem_ofPred_eq, mem_longInvAt, hA.mem_longInv_iff, hA.mem_borel_iff hQ, and_comm]

theorem ncard_longInvAt (hA : IsBenderAction X Ω n i e) (α : Ω) :
    (longInvAt X Ω α).ncard = 2 ^ n - 1 := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  obtain ⟨t, hc⟩ := hA.benderType.exists_benderCore Q
  have hset : longInvAt X Ω α = ((rootCenter (Q : Subgroup X) : Subgroup X) : Set X) \ {1} := by
    ext x
    rw [hA.mem_longInvAt_iff hQ, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
  rw [hset, Set.ncard_sdiff_singleton_of_mem (one_mem (rootCenter (Q : Subgroup X))),
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hc.card_center]

theorem mem_longInvSwap_iff (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) {t : X}
    (ht : t * t = 1) (htα : t • α = β) {x : X} :
    x ∈ longInvSwap X Ω α β ↔
      ∃ d ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆, x = t * d := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  have hti : t⁻¹ = t := inv_eq_of_mul_self ht
  rw [hA.stabilizer_inf_eq_cartan hQ ht htα, mem_longInvSwap, hA.mem_longInv_iff]
  constructor
  · rintro ⟨hx, hxα⟩
    have hx2 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    have hxB : x ∉ borel (Q : Subgroup X) := by
      rw [hA.mem_borel_iff hQ, hxα]
      exact hαβ.symm
    obtain ⟨m, hm, rfl⟩ := hc.exists_conj_eq hx2 hxB
    have hmα := (hA.mem_borel_iff hQ).mp hm
    have hmD : m ∈ cartan (Q : Subgroup X) t := by
      rw [hA.mem_cartan_iff hQ ht, htα]
      rw [mul_smul, mul_smul, hmα, htα] at hxα
      exact ⟨hmα, (inv_smul_eq_iff.mp hxα).symm⟩
    refine ⟨t * m⁻¹ * t * m, hc.mem_commutator_cartan_iff.mpr
      ⟨mul_mem (hc.cartan_mul_mul (inv_mem hmD)) hmD, ?_⟩, ?_⟩
    · calc t * (t * m⁻¹ * t * m) * t = (t * t) * (m⁻¹ * t * m * t) := by group
        _ = m⁻¹ * t⁻¹ * m * t⁻¹ := by rw [ht, one_mul, hti]
        _ = (t * m⁻¹ * t * m)⁻¹ := by group
    · calc m⁻¹ * t * m = (t * t) * (m⁻¹ * t * m) := by rw [ht, one_mul]
        _ = t * (t * m⁻¹ * t * m) := by group
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨hdD, hinv⟩ := hc.mem_commutator_cartan_iff.mp hd
    have hdα := ((hA.mem_cartan_iff hQ ht).mp hdD).1
    refine ⟨orderOf_eq_prime ?_ ?_, by rw [mul_smul, hdα, htα]⟩
    · rw [sq]
      calc t * d * (t * d) = (t * d * t) * d := by group
        _ = 1 := by rw [hinv, inv_mul_cancel]
    · intro h1
      have h2 : t = d⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : t • α = α := by
        rw [h2]
        exact ((hA.mem_cartan_iff hQ ht).mp (inv_mem hdD)).1
      exact hαβ (h3.symm.trans htα)

theorem mem_longInvSwap_iff_conj (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β)
    {t : X} (ht : t * t = 1) (htα : t • α = β) {x : X} :
    x ∈ longInvSwap X Ω α β ↔
      ∃ c ∈ ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆, x = c * t * c⁻¹ := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  have key : ∀ c ∈ ⁅cartan (Q : Subgroup X) t, Subgroup.zpowers t⁆, c * t * c⁻¹ = t * (c * c)⁻¹ :=
    fun c hcm => by
      have h1 := (hc.mem_commutator_cartan_iff.mp hcm).2
      calc c * t * c⁻¹ = t * (t * c * t) * c⁻¹ := by
            rw [show t * (t * c * t) = (t * t) * c * t by group, ht, one_mul]
        _ = t * (c * c)⁻¹ := by rw [h1, mul_inv_rev, mul_assoc]
  rw [hA.mem_longInvSwap_iff hαβ ht htα, hA.stabilizer_inf_eq_cartan hQ ht htα]
  constructor
  · rintro ⟨d, hd, rfl⟩
    have hodd : Odd (orderOf d⁻¹) := by
      rw [orderOf_inv]
      exact Odd.of_dvd_nat hc.odd_card_cartan
        (Subgroup.orderOf_dvd_natCard _ (hc.commutator_cartan_le hd))
    obtain ⟨k, hk⟩ := exists_sq_eq_of_odd_orderOf hodd
    refine ⟨d⁻¹ ^ k, pow_mem (inv_mem hd) k, ?_⟩
    rw [key _ (pow_mem (inv_mem hd) k), hk, inv_inv]
  · rintro ⟨c, hcm, rfl⟩
    exact ⟨(c * c)⁻¹, inv_mem (mul_mem hcm hcm), key c hcm⟩

end LongInvolutions

section Delta

omit [Finite X] in
private theorem orderOf_conj' (d x : X) : orderOf (d * x * d⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq d (show d * x = d * x * d⁻¹ * d by group)).symm

omit [Finite X] in
private theorem fixed_ne {α β : Ω} (hαβ : α ≠ β) {t : X}
    (ht : t * t = 1) (htα : t • α = β) {γ : Ω} (htγ : t • γ = γ) : γ ≠ α ∧ γ ≠ β := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    exact hαβ (htγ.symm.trans htα)
  · rintro rfl
    have h1 : t • γ = α := by rw [← htα, smul_smul, ht, one_smul]
    exact hαβ (h1.symm.trans htγ)

theorem holtDelta_eq_orbit (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) {t : X}
    (ht : t * t = 1) (htα : t • α = β) {γ₀ : Ω} (htγ : t • γ₀ = γ₀) :
    holtDelta X Ω α β =
      orbit ↥(⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ : Subgroup X) γ₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) (by
    rintro rfl
    rw [one_smul] at htα
    exact hαβ htα)
  obtain ⟨δ, -, hδ⟩ := hA.existsUnique_fixed htord
  ext γ
  rw [mem_holtDelta, mem_orbit_iff]
  constructor
  · rintro ⟨x, hx, hxγ⟩
    obtain ⟨c, hcm, rfl⟩ := (hA.mem_longInvSwap_iff_conj hαβ ht htα).mp hx
    have h1 : t • (c⁻¹ • γ) = c⁻¹ • γ := by
      rw [mul_smul, mul_smul] at hxγ
      simpa using congrArg (c⁻¹ • ·) hxγ
    refine ⟨⟨c, hcm⟩, ?_⟩
    change c • γ₀ = γ
    rw [(hδ γ₀ htγ).trans (hδ _ h1).symm, smul_inv_smul]
  · rintro ⟨⟨c, hcm⟩, rfl⟩
    refine ⟨c * t * c⁻¹, (hA.mem_longInvSwap_iff_conj hαβ ht htα).mpr ⟨c, hcm, rfl⟩, ?_⟩
    change (c * t * c⁻¹) • (c • γ₀) = c • γ₀
    rw [mul_smul, mul_smul, inv_smul_smul, htγ]

theorem ncard_holtDelta (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    (holtDelta X Ω α β).ncard = 2 ^ n - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht, htα⟩ := hA.exists_involution_smul_eq hαβ
  have htord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht) (by
    rintro rfl
    rw [one_smul] at htα
    exact hαβ htα)
  obtain ⟨γ₀, hγ₀, -⟩ := hA.existsUnique_fixed htord
  obtain ⟨hγα, hγβ⟩ := fixed_ne hαβ ht htα hγ₀
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hc := hA.benderCore hQ ht (htα.trans_ne hαβ.symm)
  set S : Subgroup X := ⁅stabilizer X α ⊓ stabilizer X β, Subgroup.zpowers t⁆ with hS
  have horb : orbit ↥S γ₀ = (fun c : X => c • γ₀) '' (S : Set X) := by
    ext γ
    simp only [mem_orbit_iff, Set.mem_image, SetLike.mem_coe, Subtype.exists, Subgroup.mk_smul,
      exists_prop]
  have hinj : Set.InjOn (fun c : X => c • γ₀) (S : Set X) := by
    intro c hc' c' hc'' h
    have h' : c • γ₀ = c' • γ₀ := h
    have h1 : (c'⁻¹ * c) • γ₀ = γ₀ := by
      rw [mul_smul]
      exact inv_smul_eq_iff.mpr h'
    have h2 := hA.eq_one_of_mem_commutator_of_smul_eq hαβ ht htα
      (mul_mem (inv_mem hc'') hc') hγα hγβ h1
    exact (inv_mul_eq_one.mp h2).symm
  rw [hA.holtDelta_eq_orbit hαβ ht htα hγ₀, horb, hinj.ncard_image,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hS, hA.stabilizer_inf_eq_cartan hQ ht htα,
    hc.card_commutator_cartan]

theorem holtDelta_eq_orbit_of_mem (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β)
    {γ : Ω} (hγ : γ ∈ holtDelta X Ω α β) :
    holtDelta X Ω α β = orbit ↥(stabilizer X α ⊓ stabilizer X β) γ := by
  obtain ⟨x, hx, hxγ⟩ := hγ
  have hx2 : x * x = 1 := by rw [← sq, ← hx.1.1, pow_orderOf_eq_one]
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hc := hA.benderCore hQ hx2 (hx.2.trans_ne hαβ.symm)
  ext δ
  constructor
  · intro hδ
    rw [hA.holtDelta_eq_orbit hαβ hx2 hx.2 hxγ] at hδ
    obtain ⟨⟨c, hcm⟩, rfl⟩ := hδ
    have hcD : c ∈ stabilizer X α ⊓ stabilizer X β := by
      rw [hA.stabilizer_inf_eq_cartan hQ hx2 hx.2] at hcm ⊢
      exact hc.commutator_cartan_le hcm
    exact ⟨⟨c, hcD⟩, rfl⟩
  · rintro ⟨⟨d, hd⟩, rfl⟩
    refine ⟨d * x * d⁻¹, ⟨hA.mem_longInv_iff.mpr ?_, ?_⟩, ?_⟩
    · rw [orderOf_conj']
      exact hx.1.1
    · rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hd.1.symm, hx.2, hd.2]
    · change (d * x * d⁻¹) • (d • γ) = d • γ
      rw [mul_smul, mul_smul, inv_smul_smul, hxγ]

theorem ncard_holtDelta' (hA : IsBenderAction X Ω n i e) {α β : Ω} (hαβ : α ≠ β) :
    (holtDelta' X Ω α β).ncard = 2 ^ n - 1 := by
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer α
  have hset : holtDelta' X Ω α β = (fun s : X => s • β) '' longInvAt X Ω α := by
    ext γ
    simp only [mem_holtDelta', Set.mem_image]
  have hinj : Set.InjOn (fun s : X => s • β) (longInvAt X Ω α) := by
    intro s hs s' hs' h
    have h' : s • β = s' • β := h
    have hsQ := rootCenter_le _ ((hA.mem_longInvAt_iff hQ).mp hs).1
    have hs'Q := rootCenter_le _ ((hA.mem_longInvAt_iff hQ).mp hs').1
    have h1 : (s'⁻¹ * s) • β = β := by
      rw [mul_smul]
      exact inv_smul_eq_iff.mpr h'
    have h2 := hA.eq_one_of_smul_eq hQ (mul_mem (inv_mem hs'Q) hsQ) (Ne.symm hαβ) h1
    exact (inv_mul_eq_one.mp h2).symm
  rw [hset, hinj.ncard_image, hA.ncard_longInvAt α]

end Delta

end IsBenderAction

end CFSG.Holt.H78

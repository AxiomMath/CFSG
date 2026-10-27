module

public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvariant
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherStabilizerIndex

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

@[expose] noncomputable def flagStabP (h : UnitaryFieldData p f K) (r ε : ℕ)
    (W : ℕ → Submodule K (HypIndex r ε → K)) : Subgroup (hypPSU h r ε) :=
  ⨅ i, ⨅ (_ : i ≤ r), MulAction.stabilizer (hypPSU h r ε) (W i)

theorem mem_flagStabP {h : UnitaryFieldData p f K} {W : ℕ → Submodule K (HypIndex r ε → K)}
    {x : hypPSU h r ε} : x ∈ flagStabP h r ε W ↔ ∀ i ≤ r, x • W i = W i := by
  simp only [flagStabP, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff]

theorem exists_hypSU_of_mem (h : UnitaryFieldData p f K)
    {g' : LinearMap.GeneralLinearGroup K (HypIndex r ε → K)}
    (hg' : g' ∈ sesqSpecialUnitaryGroup (hypForm h r ε)) :
    ∃ g : hypSU h r ε, ∀ L : Submodule K (HypIndex r ε → K),
      g • L = L.map (g' : (HypIndex r ε → K) →ₗ[K] HypIndex r ε → K) := by
  set A := Matrix.GeneralLinearGroup.toLin.symm g' with hAdef
  have hgA : g' = Matrix.GeneralLinearGroup.toLin A := by
    rw [hAdef, MulEquiv.apply_symm_apply]
  have hA : A ∈ hypSU h r ε := by
    rw [hgA] at hg'
    exact (toLin_mem_sesqSpecialUnitaryGroup_iff h _ A).mp hg'
  refine ⟨⟨A, hA⟩, fun L => ?_⟩
  rw [hgA]
  rfl

theorem hypSU_exists_smul_chain (h : UnitaryFieldData p f K) {k : ℕ}
    {W W' : ℕ → Submodule K (HypIndex r ε → K)} (hW : IsIsotropicChain (hypForm h r ε) k W)
    (hW' : IsIsotropicChain (hypForm h r ε) k W') :
    ∃ g : hypSU h r ε, ∀ i ≤ k, g • W i = W' i := by
  obtain ⟨g', hg', hgW⟩ := (isotropic_flag_extension h (hypForm_isSymm h)
    (hypForm_separatingLeft h) rfl).2.1 k W W' hW hW'
  obtain ⟨g, hg⟩ := exists_hypSU_of_mem h hg'
  exact ⟨g, fun i hi => by rw [hg, hgW i hi]⟩

theorem IsIsotropicChain.smul {h : UnitaryFieldData p f K} {k : ℕ}
    {W : ℕ → Submodule K (HypIndex r ε → K)} (hW : IsIsotropicChain (hypForm h r ε) k W)
    (g : hypSU h r ε) : IsIsotropicChain (hypForm h r ε) k (fun i => g • W i) :=
  ⟨fun i hi => by rw [finrank_smul, hW.1 i hi],
    fun i hi x hx => by
      obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x g (W i)).mp hx
      exact (Submodule.mem_smul_pointwise_iff_exists _ g _).mpr ⟨y, hW.2.1 i hi hy, rfl⟩,
    fun i hi => smul_isotropic g (hW.2.2 i hi)⟩

theorem isIsotropicChain_hypFlag (h : UnitaryFieldData p f K) (hε : ε ≤ 1) :
    IsIsotropicChain (hypForm h r ε) r (hypFlag h r ε) := by
  have hF : ∀ d ≤ r, hypFlag h r ε d = posFlag r ε K d := fun d hd =>
    hypFlag_eq_posFlag h hε (by omega)
  refine ⟨fun i hi => by rw [hF i hi, finrank_posFlag hi], fun i hi => ?_,
    fun i hi => by rw [hF i hi]; exact posFlag_isotropic h hi⟩
  rw [hF i hi.le, hF (i + 1) hi]
  exact fun v hv a ha => hv a (by omega)

theorem mem_hypBorel_of_conj (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1)
    {g : hypSU h r ε}
    (hg : ∀ u ∈ hypUnitriangular h r ε, ∀ i ≤ r, u • g • hypFlag h r ε i = g • hypFlag h r ε i) :
    g ∈ hypBorel h r ε := by
  have hth := unitriangular_invariant_isotropic_subspaces h hr hε
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  rw [mem_hypBorel]
  intro i _ hir
  obtain ⟨d, hd, hdeq⟩ := hth.2.2.1 (g • hypFlag h r ε i) (smul_isotropic g (hchain.2.2 i hir))
    fun u hu => hg u hu i hir
  have hdim := finrank_smul g (hypFlag h r ε i)
  rw [hdeq, hchain.1 d hd, hchain.1 i hir] at hdim
  rw [hdeq, hdim]

theorem normalizer_hypUnitriangular (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Subgroup.normalizer (hypUnitriangular h r ε : Set (hypSU h r ε)) = hypBorel h r ε := by
  have hth := unitriangular_invariant_isotropic_subspaces h hr hε
  apply le_antisymm
  · intro g hg
    refine mem_hypBorel_of_conj h hr hε fun u hu i hi => ?_
    have hu' : g⁻¹ * u * g ∈ hypUnitriangular h r ε := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) u).mp hu
      rwa [inv_inv] at this
    calc u • g • hypFlag h r ε i = g • (g⁻¹ * u * g) • hypFlag h r ε i := by
          rw [smul_smul, smul_smul]
          group
      _ = g • hypFlag h r ε i := by rw [(hth.2.2.2.1 i hi).2 _ hu']
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_hypBorel h)).mp
      ((unitary_triangular_structure h hr).1 ε hε).2.2.2.2

theorem normalizer_hypProjUnitriangular (h : UnitaryFieldData p f K) (hr : 1 ≤ r)
    (hε : ε ≤ 1) :
    Subgroup.normalizer (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) =
      hypProjBorel h r ε := by
  have hth := unitriangular_invariant_isotropic_subspaces h hr hε
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
    refine ⟨g, mem_hypBorel_of_conj h hr hε fun u hu i hi => ?_, rfl⟩
    have hmem : hypProj h r ε (g⁻¹ * u * g) ∈ hypProjUnitriangular h r ε := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) (hypProj h r ε u)).mp ⟨u, hu, rfl⟩
      rwa [inv_inv, ← map_inv, ← map_mul, ← map_mul] at this
    obtain ⟨u', hu', hu'eq⟩ := hmem
    calc u • g • hypFlag h r ε i = g • (g⁻¹ * u * g) • hypFlag h r ε i := by
          rw [smul_smul, smul_smul]
          group
      _ = g • hypFlag h r ε i := by
          rw [show (g⁻¹ * u * g) • hypFlag h r ε i =
              hypProj h r ε (g⁻¹ * u * g) • hypFlag h r ε i from (hypProj_smul h _ _).symm,
            ← hu'eq, hypProj_smul, (hth.2.2.2.1 i hi).2 _ hu']
  · rw [hypProjBorel, ← normalizer_hypUnitriangular h hr hε, hypProjUnitriangular]
    exact Subgroup.le_normalizer_map _

theorem flagStabP_hypFlag (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    flagStabP h r ε (hypFlag h r ε) = hypProjBorel h r ε := by
  ext x
  obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
  rw [mem_flagStabP, hypProjBorel, ← Subgroup.mem_comap, Subgroup.comap_map_eq_self
    (by rw [ker_hypProj]; exact fun z hz => mem_hypBorel.mpr fun i _ _ =>
      smul_submodule_of_mem_normOneScalars hz _), mem_hypBorel]
  simp only [hypProj_smul]
  constructor
  · intro hg i hi1 hir
    exact hg i hir
  · intro hg i hir
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h0 : hypFlag h r ε 0 = ⊥ := by
        rw [hypFlag_eq_posFlag h hε (by omega), posFlag_zero]
      rw [h0, eq_bot_iff]
      intro y hy
      obtain ⟨y', hy', rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y g ⊥).mp hy
      rw [(Submodule.mem_bot K).mp hy', smul_zero]
      exact Submodule.zero_mem _
    · exact hg i hi hir

theorem flagStabP_smul (h : UnitaryFieldData p f K) (W : ℕ → Submodule K (HypIndex r ε → K))
    (x : hypPSU h r ε) :
    flagStabP h r ε (fun i => x • W i) =
      (flagStabP h r ε W).map (MulAut.conj x).toMonoidHom := by
  ext y
  rw [Subgroup.mem_map_equiv, mem_flagStabP, mem_flagStabP]
  simp only [MulAut.conj_symm_apply]
  constructor
  · intro hy i hi
    rw [mul_smul, mul_smul, hy i hi, ← mul_smul, inv_mul_cancel, one_smul]
  · intro hy i hi
    have := hy i hi
    rw [mul_smul, mul_smul] at this
    calc y • x • W i = x • (x⁻¹ • y • x • W i) := by rw [smul_inv_smul]
      _ = x • W i := by rw [this]

theorem unitary_Sylow_normalizers (h : UnitaryFieldData p f K) (hr : 1 ≤ r) (hε : ε ≤ 1) :
    Subgroup.normalizer (hypUnitriangular h r ε : Set (hypSU h r ε)) = hypBorel h r ε ∧
    Subgroup.normalizer (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) =
      hypProjBorel h r ε ∧
    sylowNormalizers h r ε = {H | ∃ W : ℕ → Submodule K (HypIndex r ε → K),
      IsIsotropicChain (hypForm h r ε) r W ∧ flagStabP h r ε W = H} ∧
    ∀ W W' : ℕ → Submodule K (HypIndex r ε → K), IsIsotropicChain (hypForm h r ε) r W →
      IsIsotropicChain (hypForm h r ε) r W' → flagStabP h r ε W = flagStabP h r ε W' →
      ∀ i ≤ r, W i = W' i := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨-, -, -, -, ⟨U₀, hU₀⟩, -, -⟩ := unitary_order_and_Sylow h hr hε
  have hNU := normalizer_hypProjUnitriangular h hr hε
  have hstd := flagStabP_hypFlag h hr hε
  have hchain := isIsotropicChain_hypFlag h (r := r) hε
  have hconj : ∀ x : hypPSU h r ε,
      Subgroup.normalizer (((x • U₀ : Sylow p (hypPSU h r ε)) : Subgroup (hypPSU h r ε)) :
        Set (hypPSU h r ε)) = (hypProjBorel h r ε).map (MulAut.conj x).toMonoidHom := by
    intro x
    rw [Sylow.coe_subgroup_smul, ← hNU, Subgroup.map_equiv_normalizer_eq, hU₀]
    rfl
  have htrans : ∀ W : ℕ → Submodule K (HypIndex r ε → K),
      IsIsotropicChain (hypForm h r ε) r W →
      ∃ x : hypPSU h r ε, ∀ i ≤ r, x • hypFlag h r ε i = W i := by
    intro W hW
    obtain ⟨g, hg⟩ := hypSU_exists_smul_chain h hchain hW
    exact ⟨hypProj h r ε g, fun i hi => by rw [hypProj_smul, hg i hi]⟩
  have hstab_eq : ∀ (W : ℕ → Submodule K (HypIndex r ε → K)) (x : hypPSU h r ε),
      (∀ i ≤ r, x • hypFlag h r ε i = W i) →
      flagStabP h r ε W = (hypProjBorel h r ε).map (MulAut.conj x).toMonoidHom := by
    intro W x hx
    rw [← hstd, ← flagStabP_smul]
    ext y
    rw [mem_flagStabP, mem_flagStabP]
    constructor
    · intro hy i hi
      rw [hx i hi]
      exact hy i hi
    · intro hy i hi
      rw [← hx i hi]
      exact hy i hi
  refine ⟨normalizer_hypUnitriangular h hr hε, hNU, ?_, ?_⟩
  · ext H
    constructor
    · rintro ⟨T, rfl⟩
      obtain ⟨x, rfl⟩ := MulAction.exists_smul_eq (hypPSU h r ε) U₀ T
      refine ⟨fun i => x • hypFlag h r ε i, ?_, ?_⟩
      · obtain ⟨g, rfl⟩ := hypProj_surjective h r ε x
        simp only [hypProj_smul]
        exact hchain.smul g
      · rw [hconj, hstab_eq _ x fun i _ => rfl]
    · rintro ⟨W, hW, rfl⟩
      obtain ⟨x, hx⟩ := htrans W hW
      exact ⟨x • U₀, by rw [hconj, hstab_eq W x hx]⟩
  · intro W W' hW hW' hWW' i hi
    obtain ⟨x, hx⟩ := htrans W hW
    have hinv : ∀ j ≤ r, ∀ u ∈ hypUnitriangular h r ε, u • (x⁻¹ • W' j) = x⁻¹ • W' j := by
      intro j hj u hu
      have hmem : x * hypProj h r ε u * x⁻¹ ∈ flagStabP h r ε W' := by
        rw [← hWW', hstab_eq W x hx]
        exact ⟨hypProj h r ε u, ⟨u, hypUnitriangular_le_hypBorel h hu, rfl⟩, rfl⟩
      have hfix := (mem_flagStabP.mp hmem) j hj
      calc u • (x⁻¹ • W' j) = hypProj h r ε u • (x⁻¹ • W' j) := (hypProj_smul h u _).symm
        _ = x⁻¹ • ((x * hypProj h r ε u * x⁻¹) • W' j) := by
          rw [smul_smul, smul_smul]
          group
        _ = x⁻¹ • W' j := by rw [hfix]
    have hchain' : IsIsotropicChain (hypForm h r ε) r (fun j => x⁻¹ • W' j) := by
      obtain ⟨g, hg⟩ := hypProj_surjective h r ε x⁻¹
      have hfun : (fun j => x⁻¹ • W' j) = fun j => g • W' j := by
        funext j
        rw [← hg, hypProj_smul]
      rw [hfun]
      exact hW'.smul g
    have hstd' := (unitriangular_invariant_isotropic_subspaces h hr hε).2.2.2.2 _ hchain'
      hinv i hi
    rw [← hx i hi, ← hstd', smul_inv_smul]

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

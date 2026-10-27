module

public import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
public import CFSG.RankThree.PartOne.KC.SymplecticTorusBlock

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven CFSG.RankThree.PartOne.KCSymplectic
  CFSG.RankThree.PartOne.KCSpIsotypic CFSG.RankThree.PartOne.KCSpComm

open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

theorem not_isSolvable_gl {m : ℕ} (hm : 3 ≤ m) (F : Type*) [Field F] :
    ¬ Group.IsSolvable (Matrix.GeneralLinearGroup (Fin m) F) := by
  intro h
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin m) F) :=
    CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hm)
  have hnt : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin m) F) :=
    CFSG.LinearGroups.linear_projective_nontrivial (by omega)
  have : Nontrivial (Matrix.SpecialLinearGroup (Fin m) F) :=
    (QuotientGroup.mk'_surjective
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F))).nontrivial
  refine CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect (G := Matrix.SpecialLinearGroup (Fin m) F) ?_
  exact Group.isSolvable_of_isSolvable_injective
    (f := Matrix.SpecialLinearGroup.toGL) (by
      intro A B hAB
      exact Subtype.ext (congrArg (fun g : Matrix.GeneralLinearGroup (Fin m) F =>
        (g : Matrix (Fin m) (Fin m) F)) hAB))

theorem not_isSolvable_statedSp {s : ℕ} (hs : 3 ≤ s) {K : Type} [Field K] [Finite K] :
    ¬ Group.IsSolvable (StatedSp s K) := by
  intro h
  obtain ⟨hsimple, hperf⟩ := simple_perfect_statedProj (r := s) (k := K) (by omega)
    (by omega)
  have hsolv : Group.IsSolvable (StatedProj (StatedSp s K)) :=
    Group.isSolvable_of_surjective
      (SymplecticHigher.proj_surjective (r := s) (K := K))
  have : Nontrivial (StatedProj (StatedSp s K)) := hsimple.toNontrivial
  exact CFSG.LieType.SteinbergBR.not_isSolvable_of_isPerfect hsolv

theorem perm_embeds_selfDual {ℓ f p n : ℕ} {K : Type} [Field K] {x : StatedSp n K}
    {h : primaryFactors (spEnd x)} (hS : SpSelfDualBlock ℓ f p x h) :
    ∃ ι : Equiv.Perm (Fin (primaryMultiplicity (spEnd x) (h : K[X]))) →* StatedSp n K,
      Function.Injective ι ∧ ∀ τ, ι τ ∈ Subgroup.centralizer ({x} : Set (StatedSp n K)) := by
  obtain ⟨d, -, -, σ, -, -, -, hσroot, -, hE, hbar, Hf, -, -, -, ⟨e, he⟩, φ, hφ⟩ :=
    hS.exists_half
  let E := AdjoinRoot (h : K[X])
  let W := primaryComponent (spEnd x) (h : K[X])
  let m := primaryMultiplicity (spEnd x) (h : K[X])
  let gl := LinearMap.GeneralLinearGroup.generalLinearEquiv E W
  have hcoe : ∀ (δ : W ≃ₗ[E] W) u,
      (((gl.symm δ : blockGL (spEnd x) (h : K[X])) : Module.End E W) u) = δ u :=
    fun δ u => congrArg (fun f => f u) (gl.apply_symm_apply δ)
  let pe : Equiv.Perm (Fin m) →* (W ≃ₗ[E] W) :=
    { toFun := permEquiv e
      map_one' := by
        refine LinearEquiv.toLinearMap_injective (e.ext fun j => ?_)
        change permEquiv e 1 (e j) = e j
        rw [permEquiv_apply_basis]
        rfl
      map_mul' := fun τ σ' => by
        refine LinearEquiv.toLinearMap_injective (e.ext fun j => ?_)
        change permEquiv e (τ * σ') (e j) = permEquiv e τ (permEquiv e σ' (e j))
        rw [permEquiv_apply_basis, permEquiv_apply_basis, permEquiv_apply_basis]
        rfl }
  have hmem : ∀ τ, gl.symm (pe τ) ∈ sesqUnitaryGroup Hf := by
    intro τ
    refine mem_sesqUnitaryGroup.2 fun u v => ?_
    rw [hcoe, hcoe]
    exact herm_perm e Hf he τ u v
  let ι0 : Equiv.Perm (Fin m) →* sesqUnitaryGroup Hf :=
    (gl.symm.toMonoidHom.comp pe).codRestrict _ hmem
  let ι : Equiv.Perm (Fin m) →* StatedSp n K :=
    (spSupported x {(h : K[X])}).subtype.comp (φ.symm.toMonoidHom.comp ι0)
  refine ⟨ι, ?_, ?_⟩
  · intro τ τ' hττ
    have h1 : φ.symm (ι0 τ) = φ.symm (ι0 τ') := Subtype.ext hττ
    have h2 : ι0 τ = ι0 τ' := φ.symm.injective h1
    have h3 : gl.symm (pe τ) = gl.symm (pe τ') := congrArg Subtype.val h2
    have h4 : pe τ = pe τ' := gl.symm.injective h3
    have h5 : ∀ j, e (τ j) = e (τ' j) := by
      intro j
      have := congrArg (fun δ : W ≃ₗ[E] W => δ (e j)) h4
      simpa [pe, permEquiv_apply_basis] using this
    exact Equiv.ext fun j => e.injective (h5 j)
  · intro τ
    have hg := (mem_spSupported.1 (φ.symm (ι0 τ)).2).1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact hg.symm



theorem ker_proj_eq_bot {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : (proj n K).ker = ⊥ := by
  rw [SymplecticHigher.ker_proj]
  have hc := CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K hn
  rw [hK] at hc
  have h1 : Nat.gcd 2 (2 ^ f - 1) = 1 := by
    have h2 : Odd (2 ^ f - 1) := by
      have : Even (2 ^ f) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
      have h3 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      exact Nat.Even.sub_odd h3 this odd_one
    exact Nat.coprime_two_left.2 h2
  rw [h1] at hc
  exact Subgroup.eq_bot_of_card_eq _ hc



theorem not_isSolvable_centralizer_of_mult {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : StatedSp n K} (hxp : orderOf x = p) (h : primaryFactors (spEnd x))
    (hm : 5 ≤ primaryMultiplicity (spEnd x) (h : K[X])) :
    ¬ Group.IsSolvable ↥(Subgroup.centralizer ({x} : Set (StatedSp n K))) := by
  intro hsolv
  have hker := ker_proj_eq_bot hn hf hK
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxp
    exact hp.one_lt.ne hxp
  have ha : orderOf (proj n K x) = p := by
    have : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hxp, pow_orderOf_eq_one, map_one]
    · intro h1
      apply hx1
      have : x ∈ (proj n K).ker := h1
      rwa [hker, Subgroup.mem_bot] at this
  obtain ⟨-, hblocks⟩ := symplectic_cross_prime_primary_centralizer_blocks (K := K)
    Nat.prime_two hf hK hp hp2 hp2 hn (proj n K x) ha
  have blocks := hblocks x rfl hxp
  have hsubsolv : ∀ H : Subgroup (StatedSp n K),
      H ≤ Subgroup.centralizer ({x} : Set (StatedSp n K)) → Group.IsSolvable H := by
    intro H hH
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hH)
      (Subgroup.inclusion_injective hH)
  by_cases hX : (h : K[X]) = X - 1
  ·
    have hmem1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x) := by
      rw [← hX]; exact h.2
    obtain ⟨φ, -⟩ := blocks.fixedFactor hmem1
    have : Fact (Irreducible (X - 1 : K[X])) := ⟨irreducible_X_sub_one⟩
    have hdim := finrank_primaryComponent (spEnd x) (X - 1 : K[X])
    rw [hX] at hm
    have hnat : (X - 1 : K[X]).natDegree = 1 := natDegree_X_sub_C 1
    rw [hnat, one_mul] at hdim
    have hB : ((spForm n K).restrict (primaryComponent (spEnd x) (X - 1))).IsAlt :=
      fun v => spForm_isAlt (r := n) (K := K) (v : Fin n ⊕ Fin n → K)
    obtain ⟨s, hs, ⟨ψ⟩⟩ := exists_mulEquiv_sesqUnitaryGroup_statedSp hB blocks.fixed_nondegenerate
    have hs3 : 3 ≤ s := by
      have h2s : 2 * s = primaryMultiplicity (spEnd x) (X - 1 : K[X]) := by rw [← hs, hdim]
      omega
    have hle : spSupported x {X - 1} ≤ Subgroup.centralizer ({x} : Set (StatedSp n K)) := by
      intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact ((mem_spSupported.1 hg).1).symm
    have h1 := hsubsolv _ hle
    have h2 : Group.IsSolvable (StatedSp s K) :=
      Group.isSolvable_of_isSolvable_injective (f := (φ.trans ψ).symm.toMonoidHom)
        (φ.trans ψ).symm.injective
    exact not_isSolvable_statedSp hs3 h2
  · have hnt := blocks.nontrivial h h.2 hX
    by_cases hself : reciprocalPolynomial (h : K[X]) = h
    · obtain ⟨ι, hι, hιc⟩ := perm_embeds_selfDual (blocks.selfDual h hX hself)
      have hsolvP : Group.IsSolvable (Equiv.Perm (Fin (primaryMultiplicity (spEnd x) (h : K[X])))) := by
        have : Group.IsSolvable (Subgroup.centralizer ({x} : Set (StatedSp n K))) := hsolv
        have hrange : ι.range ≤ Subgroup.centralizer ({x} : Set (StatedSp n K)) := by
          rintro _ ⟨τ, rfl⟩
          exact hιc τ
        have h3 : Group.IsSolvable ι.range := hsubsolv _ hrange
        exact Group.isSolvable_of_isSolvable_injective (f := ι.rangeRestrict)
          (by
            intro a b hab
            exact hι (congrArg Subtype.val hab))
      exact Equiv.Perm.not_isSolvable (Fin (primaryMultiplicity (spEnd x) (h : K[X])))
        (by rw [Cardinal.mk_fin]; exact_mod_cast hm) hsolvP
    · have hP := blocks.paired h (Ne.symm hself)
      obtain ⟨M⟩ := hP.matrixFactor
      have : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
      have hle : spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} ≤
          Subgroup.centralizer ({x} : Set (StatedSp n K)) := by
        intro g hg
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact ((mem_spSupported.1 hg).1).symm
      have h1 := hsubsolv _ hle
      have h2 : Group.IsSolvable (GL (Fin (primaryMultiplicity (spEnd x) (h : K[X])))
          (AdjoinRoot (h : K[X]))) :=
        Group.isSolvable_of_isSolvable_injective (f := M.symm.toMonoidHom) M.symm.injective
      exact not_isSolvable_gl (by omega) _ h2

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

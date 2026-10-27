module

public import CFSG.HardMathSupport.Dickson.Bal207.SpFCBlock
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.HardMathSupport.Dickson.Bal207.SpShape
import CFSG.HardMathSupport.Dickson.Bal207.UniModel
import CFSG.HardMathSupport.Dickson.Bal207.UniNormal
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSU
import CFSG.RankThree.PartOne.KC.SymplecticNoninnerPlaneDescent

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Polynomial Matrix CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.Assembly.LowTwoRank CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
theorem blockSU_eq_commutator {f n : ℕ} {E : Type} [Field E] (h : UnitaryFieldData 2 f E)
    (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ 2 ^ f = 2)) :
    blockSU h n = commutator ↥(primeFormUnitary h (oneGram E n)) := by
  haveI := h.finite
  haveI := Fintype.ofFinite E
  have hEcard : Fintype.card E = (2 ^ f) ^ 2 := by
    rw [Fintype.card_eq_nat_card]
    exact h.card_eq_sq
  have hnq : (n, 2 ^ f) ≠ (3, 2) := fun h' => hne ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  have hT : commutator ↥(gramSU h (oneGram E n)) = ⊤ := by
    have hSU : StatedSU n (2 ^ f) E = gramSU h (oneGram E n) := unitarySU_eq_gramSU h n
    rw [← hSU]
    exact (suFactorFacts_holds E n (2 ^ f) hEcard hn hnq).perfect
  refine le_antisymm ?_ fun g hg => ?_
  · show (gramSU h (oneGram E n)).subgroupOf (primeFormUnitary h (oneGram E n)) ≤ _
    rw [← Subgroup.inclusion_range (gramSU_le_primeFormUnitary h), MonoidHom.range_eq_map, ← hT,
      commutator_def, Subgroup.map_commutator, commutator_def]
    exact Subgroup.commutator_mono le_top le_top
  · have hdet := Abelianization.commutator_subset_ker
      (Matrix.GeneralLinearGroup.det.comp (primeFormUnitary h (oneGram E n)).subtype) hg
    have h1 := congrArg Units.val (MonoidHom.mem_ker.mp hdet)
    rw [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.val_det_apply] at h1
    exact Subgroup.mem_subgroupOf.mpr (mem_gramSU.mpr ⟨g.2, h1⟩)

@[expose] def BlockFrame {X : Type} [Group X] {K : Subgroup X} {S : Type} [Group S]
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* S) (B J : Subgroup X)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) : Prop :=
  ∃ (E : Type) (_ : Field E) (f : ℕ) (h : UnitaryFieldData 2 f E) (n : ℕ), (f = 1 ∨ f = 3) ∧
    3 ≤ n ∧ ¬(n = 3 ∧ 2 ^ f = 2) ∧ ∃ ι : ↥(primeFormUnitary h (oneGram E n)) →* S,
      Function.Injective ι ∧ (J.comap K.subtype).map (uniMap e) = (blockSU h n).map ι ∧
      ∃ x : ↥B → blockGamma h n,
        (∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E n))),
          uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left)) ∧
        ∃ P : ↥(primeFormUnitary h (oneGram E n)), ∀ b : ↥B,
          ∃ D : ↥(primeFormUnitary h (oneGram E n)),
            ((D : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).IsDiag ∧ ∃ φ : E ≃+* E,
              (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
                (SemidirectProduct.inl P)⁻¹ * x b * SemidirectProduct.inl P =
                  SemidirectProduct.inl D * SemidirectProduct.inr φ

theorem isStronglyLocallyOneBalanced_of_blockFrame {X : Type} [Group X] [Finite X]
    {K B J : Subgroup X} {S : Type} [Group S] {a : X} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (hF : BlockFrame e B J hBK) : IsStronglyLocallyOneBalanced 3 B a J := by
  obtain ⟨E, _, f, h, n, hf, hn, hne, ι, hι, hJι, x, hx, P, hP⟩ := hF
  exact isStronglyLocallyOneBalanced_of_block hB hBK hZ e hJ hJK hBJ h rfl hf hn hne hι hJι x hx
    P hP

section Form

variable {E : Type} [Field E] {ℓ f : ℕ} (hE : UnitaryFieldData ℓ f E) {W : Type*}
  [AddCommGroup W] [Module E W] {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} {η : E}

theorem smul_form_apply (c : E) (v w : W) : (c • Hf) v w = c * Hf v w := rfl

theorem isSymm_inv_smul [CharP E 2] (hHf : Hf.IsSymm) (hη : hE.bar η = -η) :
    (η⁻¹ • Hf).IsSymm := by
  refine LinearMap.isSymm_def.mpr fun v w => ?_
  rw [smul_form_apply, smul_form_apply, map_mul, map_inv₀, hη, CharTwo.neg_eq,
    LinearMap.isSymm_def.mp hHf]

theorem separatingLeft_inv_smul (hHfl : Hf.SeparatingLeft) (hη : η ≠ 0) :
    (η⁻¹ • Hf).SeparatingLeft := fun v hv => hHfl v fun w => by
  have h1 := hv w
  rw [smul_form_apply] at h1
  exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hη)

theorem sesqUnitaryGroup_inv_smul (hη : η ≠ 0) :
    sesqUnitaryGroup (η⁻¹ • Hf) = sesqUnitaryGroup Hf := by
  ext g
  rw [mem_sesqUnitaryGroup, mem_sesqUnitaryGroup]
  refine forall₂_congr fun v w => ?_
  rw [smul_form_apply, smul_form_apply]
  exact mul_right_inj' (inv_ne_zero hη)

end Form

section Lift

variable {r f : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_spSemilinearAutGroup_of_pow_three (hF : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hr : 2 ≤ r) {β : MulAut (StatedProj (StatedSp r F))} (hβ : β ^ 3 = 1) :
    β ∈ spSemilinearAutGroup r F := by
  have hO := CFSG.RankThree.PartOne.KCSpComm.spOuter (K := F) Nat.prime_two hf1 hr hF
  have hodd : Odd (orderOf β) :=
    (Nat.prime_three.odd_of_ne_two (by norm_num)).of_dvd_nat (orderOf_dvd_of_pow_eq_one hβ)
  exact CFSG.RankThree.PartOne.KCSpComm.mem_of_odd_orderOf_of_index_dvd_two _ hO.index_dvd hodd

theorem exists_semiStab_lift {X : Type} [Group X] {K B : Subgroup X} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hF : Nat.card F = 2 ^ f) (hf1 : 1 ≤ f)
    (hr : 2 ≤ r) (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {a : X}
    (ha : a ∈ B) {x : StatedSp r F}
    (hax : uniAut e ⟨a, hBK ha⟩ = MulAut.conj (SymplecticFlag.proj r F x)) :
    ∃ lam : ↥B →* semiStab x, ∀ b : ↥B,
      spNormalFormHom r F (lam b : SemiSp r F) = uniAut e ⟨b, hBK b.2⟩ := by
  haveI : NeZero r := ⟨by omega⟩
  haveI := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  have hinj := spNormalFormHom_injective (r := r) (K := F)
  let μ : ↥B →* MulAut (StatedProj (StatedSp r F)) := (uniAut e).comp (Subgroup.inclusion hBK)
  have hμ : ∀ b, μ b ∈ (spNormalFormHom r F).range := fun b => by
    rw [range_spNormalFormHom]
    refine mem_spSemilinearAutGroup_of_pow_three hF hf1 hr ?_
    have hb3 : b ^ 3 = 1 := Subtype.ext (hB.2.1.2 b b.2)
    rw [← map_pow, hb3, map_one]
  let ν : ↥B →* SemiSp r F :=
    (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (μ.codRestrict _ hμ)
  have hν : ∀ b, spNormalFormHom r F (ν b) = μ b := fun b => by
    rw [← MonoidHom.ofInjective_apply hinj]
    exact congrArg Subtype.val ((MonoidHom.ofInjective hinj).apply_symm_apply ⟨μ b, hμ b⟩)
  have hνa : ν ⟨a, ha⟩ = SemidirectProduct.inl x := hinj (by
    rw [hν]
    show uniAut e ⟨a, hBK ha⟩ = spNormalFormHom r F ⟨x, 1⟩
    rw [spNormalFormHom_apply, map_one, mul_one, conjAut_statedSp, hax])
  have hmem : ∀ b, ν b ∈ semiStab x := fun b => by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hνa, ← map_mul, ← map_mul]
    exact congrArg ν (hB.2.1.1.is_comm.comm b ⟨a, ha⟩)
  exact ⟨ν.codRestrict _ hmem, hν⟩

end Lift

theorem blockFrame_of_selfDual {Y : Type} [Group Y] {K B J : Subgroup Y} (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set Y)) {r f : ℕ} {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ f) (hf : f = 1 ∨ f = 3) (hr : 2 ≤ r)
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* StatedProj (StatedSp r F)) {a : Y} (ha : a ∈ B)
    {x : StatedSp r F} (hx : x ^ 3 = 1)
    (hax : uniAut e ⟨a, hBK ha⟩ = MulAut.conj (SymplecticFlag.proj r F x))
    {g : primaryFactors (spEnd x)} (hg : (g : F[X]) = X ^ 2 + X + 1)
    (hS : SpSelfDualBlock 2 f 3 x g) (hm : 3 ≤ primaryMultiplicity (spEnd x) (g : F[X]))
    (hmq : ¬(primaryMultiplicity (spEnd x) (g : F[X]) = 3 ∧ 2 ^ f = 2))
    (hJ : (J.comap K.subtype).map (uniMap e) =
      (⁅spSupported x {(g : F[X])}, spSupported x {(g : F[X])}⁆).map (SymplecticFlag.proj r F)) :
    BlockFrame e B J hBK := by
  classical
  have hf1 : 1 ≤ f := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (f := f) (by rw [Fintype.card_eq_nat_card, hF])
  obtain ⟨d, hd, -, -, -, -, -, -, -, hE, -, Hf, hHf, hHfl, ⟨η, hη0, hηbar, htrf⟩, ⟨e₀, -⟩, φ,
    hφ⟩ := hS.exists_half
  have hdeg : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  have hd1 : d = 1 := by
    rw [hg, hdeg] at hd
    omega
  subst hd1
  haveI : CharP (AdjoinRoot (g : F[X])) 2 := hE.charP
  haveI : FiniteDimensional (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) :=
    Module.Finite.of_basis e₀
  have htr : ∀ (v w : primaryComponent (spEnd x) (g : F[X])) (c : AdjoinRoot (g : F[X])),
      Algebra.trace F (AdjoinRoot (g : F[X])) (c * (η⁻¹ • Hf) v w) =
        spForm r F (v : Fin r ⊕ Fin r → F)
          ((c • w : primaryComponent (spEnd x) (g : F[X])) : Fin r ⊕ Fin r → F) := fun v w c => by
    rw [smul_form_apply, ← mul_assoc, htrf, mul_assoc, inv_mul_cancel₀ hη0, mul_one]
  obtain ⟨b, hb⟩ := hE.exists_orthonormal_basis (isSymm_inv_smul hE hHf hηbar)
    (separatingLeft_inv_smul hE hHfl hη0)
  have hfin : Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) =
      primaryMultiplicity (spEnd x) (g : F[X]) := by
    rw [Module.finrank_eq_card_basis e₀, Fintype.card_fin]
  let φ' : spSupported x {(g : F[X])} ≃* sesqUnitaryGroup (η⁻¹ • Hf) :=
    φ.trans (MulEquiv.subgroupCongr (sesqUnitaryGroup_inv_smul hE hη0).symm)
  have hφ' : ∀ (γ : spSupported x {(g : F[X])}) (v : Fin r ⊕ Fin r → F)
      (hv : v ∈ primaryComponent (spEnd x) (g : F[X])),
      blockApply (φ' γ : blockGL (spEnd x) (g : F[X])) v hv = spEnd (γ : StatedSp r F) v := hφ
  have hfac : ∀ k ∈ primaryFactors (spEnd x), k = X - 1 ∨ k = X ^ 2 + X + 1 := fun k hk =>
    primaryFactor_cases_of_card hF hf (spEnd_pow hx) hk
  have hπ : Function.Injective (SymplecticFlag.proj r F) :=
    (MonoidHom.ker_eq_bot_iff _).1 (ker_proj_eq_bot_of_two (by omega) hF hf)
  have hn3 : 3 ≤ Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) :=
    hfin ▸ hm
  have hne : ¬(Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])) = 3 ∧
      2 ^ (f * 1) = 2) := by
    rw [mul_one, hfin]
    exact hmq
  have hcomm : (commutator ↥(primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X]))
      (Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])))))).map
        (blockIota hE b φ' hb).toMonoidHom = commutator ↥(spSupported x {(g : F[X])}) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top_of_surjective _ (blockIota hE b φ' hb).surjective]
  have hJι : (J.comap K.subtype).map (uniMap e) = (blockSU hE _).map
      ((SymplecticFlag.proj r F).comp ((spSupported x {(g : F[X])}).subtype.comp
        (blockIota hE b φ' hb).toMonoidHom)) := by
    rw [hJ, blockSU_eq_commutator hE hn3 hne, ← Subgroup.map_map, ← Subgroup.map_map, hcomm,
      Subgroup.map_subtype_commutator]
  obtain ⟨lam, hlam⟩ := exists_semiStab_lift hB hBK hF hf1 hr e ha hax
  let xb := (blockRho hE b hg htr hb).comp lam
  have hx' : ∀ (c : ↥B) (M : ↥(primeFormUnitary hE (oneGram (AdjoinRoot (g : F[X]))
      (Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])))))),
      uniAut e ⟨c, hBK c.2⟩ (((SymplecticFlag.proj r F).comp ((spSupported x
        {(g : F[X])}).subtype.comp (blockIota hE b φ' hb).toMonoidHom)) M) =
      ((SymplecticFlag.proj r F).comp ((spSupported x {(g : F[X])}).subtype.comp
        (blockIota hE b φ' hb).toMonoidHom))
          ((xb c * SemidirectProduct.inl M * (xb c)⁻¹).left) := by
    intro c M
    rw [← hlam c]
    show (SymplecticHigher.conjAut r F (semiA (lam c : SemiSp r F)) *
      SymplecticHigher.fieldAut r F (lam c : SemiSp r F).right)
        (SymplecticFlag.proj r F (blockIota hE b φ' hb M : StatedSp r F)) = _
    rw [alpha_apply_proj]
    exact congrArg (SymplecticFlag.proj r F)
      (semiConj_blockIota hE b φ' hφ' hg hfac htr hb (lam c) M)
  have hc : ∀ y ∈ Set.range xb, ∀ z ∈ Set.range xb, y * z = z * y := by
    rintro _ ⟨c, rfl⟩ _ ⟨c', rfl⟩
    rw [← map_mul, ← map_mul, hB.2.1.1.is_comm.comm c c']
  have hcube : ∀ y ∈ Set.range xb, y ^ 3 = 1 := by
    rintro _ ⟨c, rfl⟩
    have hc3 : c ^ 3 = 1 := Subtype.ext (hB.2.1.2 c c.2)
    rw [← map_pow, hc3, map_one]
  have h3 : 3 ∣ 2 ^ (f * 1) + 1 := by
    rcases hf with rfl | rfl <;> norm_num
  obtain ⟨P, τ, hτ, hP⟩ := uni_normal_form_mat (n := Module.finrank (AdjoinRoot (g : F[X]))
    (primaryComponent (spEnd x) (g : F[X]))) hE h3 (Set.range xb) hc hcube
  have hι : Function.Injective ((SymplecticFlag.proj r F).comp ((spSupported x
      {(g : F[X])}).subtype.comp (blockIota hE b φ' hb).toMonoidHom)) :=
    hπ.comp (Subtype.val_injective.comp (blockIota hE b φ' hb).injective)
  refine ⟨AdjoinRoot (g : F[X]), inferInstance, f * 1, hE,
    Module.finrank (AdjoinRoot (g : F[X])) (primaryComponent (spEnd x) (g : F[X])),
    by rw [mul_one]; exact hf, hn3, hne, _, hι, hJι, xb, hx', P, fun c => ?_⟩
  have hmem : xb c ∈ Set.range xb := ⟨c, rfl⟩
  have hPc := hP (xb c) hmem
  obtain ⟨D, hD, -, k, hk⟩ := hPc
  have hτk : (τ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hτ, one_pow]
  exact ⟨D, hD, τ ^ k, fun z hz => uni_fix_cube_root hτk hz, hk⟩

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end

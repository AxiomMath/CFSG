module

public import CFSG.RankThree.PartOne.KE.SLnFamily
public import CFSG.RankThree.PartOne.KE.SLnShapeHom
public import CFSG.RankThree.PartOne.KF4.A2Frame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwFrob

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Frame

variable {τ : Tag} {L : Type}
  [Field L] {ν : ℕ}

@[expose] def frameRoots (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) : Set (Fin τ.rank → ℤ) :=
  {r | ∃ i j : Fin ν, i ≠ j ∧ r = σ i j}

structure IsSLFrame (ρ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ) : Prop where
  isRoot : ∀ i j, i ≠ j → IsRoot τ (σ i j)
  neg : ∀ i j, σ j i = -σ i j
  add : ∀ i j k, σ i j + σ j k = σ i k
  transv : ∀ (i j : Fin ν) (hij : i ≠ j), ∃ ε : Lˣ, ∀ t : L,
    ρ (Matrix.SpecialLinearGroup.transvection hij t) = pinnedX τ L (σ i j) ((ε : L) * t)
  range : ρ.range = rootSpan τ L (frameRoots σ)

namespace IsSLFrame

variable {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem of_isA2Frame {ρ : SL(3, L) →* ModGL τ L} {σ : Fin 3 → Fin 3 → Fin τ.rank → ℤ}
    (h : CFSG.RankThree.PartOne.KF4.IsA2Frame ρ σ) : IsSLFrame ρ σ where
  isRoot := h.isRoot
  neg := h.neg
  add := h.add
  transv := h.transv
  range := h.range

theorem frameRoots_isRoot (h : IsSLFrame ρ σ) : ∀ r ∈ frameRoots σ, IsRoot τ r := by
  rintro r ⟨i, j, hij, rfl⟩
  exact h.isRoot i j hij

theorem eq_sub (h : IsSLFrame ρ σ) (i j k : Fin ν) : σ i j = σ i k - σ j k := by
  have h1 := h.add i k j
  rw [h.neg j k] at h1
  rw [← h1]
  abel

theorem range_le_adjointGroup (h : IsSLFrame ρ σ) : ρ.range ≤ adjointGroup τ L := by
  rw [h.range]
  exact CFSG.LieType.Chevalley.rootSpan_le_adjointGroup L _

end IsSLFrame

end Frame

section Torus

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ}

namespace IsSLFrame

variable {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem torus (h : IsSLFrame ρ σ) (k : Fin ν) (b : Fin τ.rank → Lˣ) (A : SL(ν, L)) :
    rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ =
      ρ (conjDiagn (fun i => rootChar b (σ i k)) A) := by
  set d : Fin ν → Lˣ := fun i => rootChar b (σ i k) with hd
  have hh : (MulAut.conj (rootDiagUnit τ b)).toMonoidHom.comp ρ = ρ.comp (conjDiagnHom d) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := ν) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    obtain ⟨ε, hε⟩ := h.transv i j hij
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      conjDiagnHom_apply]
    rw [hε, conjDiagn_transvection, hε, rootDiagUnit_conj_pinnedX b (h.isRoot i j hij)]
    congr 1
    rw [h.eq_sub i j k, rootChar_sub]
    simp only [hd, Units.val_mul, Units.val_inv_eq_inv_val]
    ring
  exact DFunLike.congr_fun hh A

theorem exists_torus (h : IsSLFrame ρ σ) (hν : 0 < ν) (b : Fin τ.rank → Lˣ) :
    ∃ d : Fin ν → Lˣ, ∀ A : SL(ν, L),
      rootDiagUnit τ b * ρ A * (rootDiagUnit τ b)⁻¹ = ρ (conjDiagn d A) :=
  ⟨_, h.torus ⟨0, hν⟩ b⟩

end IsSLFrame

end Torus

section Transport

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ}

namespace IsSLFrame

variable {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem transport (h : IsSLFrame ρ σ) (v : WeylGroup τ) :
    IsSLFrame ((MulAut.conj (canonicalRep (coxeterSystem τ) L v)).toMonoidHom.comp ρ)
      (fun i j => v • σ i j) where
  isRoot i j hij := IsRoot.smul (h.isRoot i j hij) v
  neg i j := by rw [h.neg i j, smul_neg]
  add i j k := by rw [← smul_add, h.add]
  transv i j hij := by
    obtain ⟨ε₀, h₀⟩ := h.transv i j hij
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX (canonicalRep_mem_monomialSubgroup L v)
      (h.isRoot i j hij)
    have hπ : weylQuotientHom τ L ⟨canonicalRep (coxeterSystem τ) L v,
        canonicalRep_mem_monomialSubgroup L v⟩ = v :=
      weylQuotientHom_eq (mapsRootLines_canonicalRep v)
    refine ⟨μ * ε₀, fun t => ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [h₀, hμ, hπ, Units.val_mul, mul_assoc]
  range := by
    rw [MonoidHom.range_comp, h.range, map_conj_rootSpan v h.frameRoots_isRoot]
    congr 1
    ext r
    constructor
    · rintro ⟨γ, ⟨i, j, hij, rfl⟩, rfl⟩
      exact ⟨i, j, hij, rfl⟩
    · rintro ⟨i, j, hij, rfl⟩
      exact ⟨σ i j, ⟨i, j, hij, rfl⟩, rfl⟩

theorem frameRoots_smul (v : WeylGroup τ) :
    frameRoots (fun i j => v • σ i j) = (fun γ => v • γ) '' frameRoots σ := by
  ext r
  constructor
  · rintro ⟨i, j, hij, rfl⟩
    exact ⟨σ i j, ⟨i, j, hij, rfl⟩, rfl⟩
  · rintro ⟨γ, ⟨i, j, hij, rfl⟩, rfl⟩
    exact ⟨i, j, hij, rfl⟩

end IsSLFrame

end Transport

section Fixed

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ}

namespace IsSLFrame

variable {ρ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ}

theorem exists_aut (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ)
    (tgt : Fin ν → Fin ν → Fin ν × Fin ν) (htne : ∀ i j, i ≠ j → (tgt i j).1 ≠ (tgt i j).2)
    (htsurj : ∀ i j, i ≠ j → ∃ i' j', i' ≠ j' ∧ tgt i' j' = (i, j))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L, Ψ (pinnedX τ L (σ i j) c) =
      pinnedX τ L (σ (tgt i j).1 (tgt i j).2) ((b : L) * Fr c)) :
    ∃ Φ' : SL(ν, L) ≃* SL(ν, L), (∀ X, Ψ (ρ X) = ρ (Φ' X)) ∧
      ∃ b : Fin ν → Fin ν → Lˣ, ∀ (i j : Fin ν) (hij : i ≠ j) (t : L),
        ((Φ' (Matrix.SpecialLinearGroup.transvection hij t) : SL(ν, L)) :
          Matrix (Fin ν) (Fin ν) L) = 1 + single (tgt i j).1 (tgt i j).2 ((b i j : L) * Fr t) := by
  classical
  choose! ε hε using fun (i j : Fin ν) (hij : i ≠ j) => h.transv i j hij
  exact exists_aut_of_rootData_hom ρ hinj σ ε hε Fr hFr Ψ hΨinj tgt htne htsurj hΨ

theorem range_inf_eqLocus_eq_map {ρ : SL(ν, L) →* ModGL τ L} (hinj : Function.Injective ρ)
    (Ψ : ModGL τ L →* ModGL τ L) (Φ' : SL(ν, L) ≃* SL(ν, L)) (hΦ' : ∀ X, Ψ (ρ X) = ρ (Φ' X)) :
    ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) = (fixSubgroup Φ').map ρ := by
  ext u
  constructor
  · rintro ⟨⟨X, rfl⟩, hX⟩
    refine ⟨X, ?_, rfl⟩
    have h1 : Ψ (ρ X) = ρ X := hX
    exact hinj ((hΦ' X).symm.trans h1)
  · rintro ⟨X, hX, rfl⟩
    refine ⟨⟨X, rfl⟩, ?_⟩
    have h1 : Φ' X = X := hX
    change Ψ (ρ X) = ρ X
    rw [hΦ' X, h1]

theorem fix_unitary (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (Ψ : ModGL τ L →* ModGL τ L)
    (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin ν))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c)) :
    (∃ H : SL(ν, L), ∀ X : SL(ν, L), Ψ (ρ X) = ρ X ↔
      ∃ Y ∈ unitarySet (ℓ ^ f) ν, Matrix.SpecialLinearGroup.toGL X =
        Matrix.SpecialLinearGroup.toGL H * Y * (Matrix.SpecialLinearGroup.toGL H)⁻¹) ∧
    Finite ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) ∧
    ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) ∧
      Nat.card (Subgroup.center ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _))) =
        Nat.gcd ν (ℓ ^ f + 1)) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have htne : ∀ i j : Fin ν, i ≠ j →
      ((fun i j => (π j, π i) : Fin ν → Fin ν → Fin ν × Fin ν) i j).1 ≠
        ((fun i j => (π j, π i) : Fin ν → Fin ν → Fin ν × Fin ν) i j).2 :=
    fun i j hij => (π.injective.ne hij).symm
  have htsurj : ∀ i j : Fin ν, i ≠ j → ∃ i' j' : Fin ν, i' ≠ j' ∧
      (fun i j => (π j, π i) : Fin ν → Fin ν → Fin ν × Fin ν) i' j' = (i, j) :=
    fun i j hij => ⟨π.symm j, π.symm i, (π.symm.injective.ne hij).symm, by simp⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := h.exists_aut hinj Fr hFrbij Ψ hΨinj
    (fun i j => (π j, π i)) htne htsurj hΨ
  obtain ⟨-, ⟨H, hH⟩, hfin, hbig, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk hν π Φ' b
      (fun i j hij t => by rw [hshape i j hij t, hFr])
  have heq := range_inf_eqLocus_eq_map hinj Ψ Φ' hΦ'
  let e : ↥(fixSubgroup Φ') ≃* ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) :=
    (Subgroup.equivMapOfInjective _ ρ hinj).trans (MulEquiv.subgroupCongr heq.symm)
  refine ⟨⟨H, fun X => ?_⟩, Finite.of_equiv _ e.toEquiv, fun hq => ?_⟩
  · rw [hΦ' X, ← hH X]
    exact ⟨fun h1 => hinj h1, fun h1 => by rw [h1]⟩
  · obtain ⟨hqs, -, hcard⟩ := hbig hq
    exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs,
      (natCard_center_eq_of_mulEquiv e).symm.trans hcard⟩

theorem fix_split (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L] (hk : Nat.card k = ℓ ^ f)
    (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (Ψ : ModGL τ L →* ModGL τ L)
    (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin ν))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π i) (π j)) ((b : L) * Fr c)) :
    (∃ H : SL(ν, L), ∀ X : SL(ν, L), Ψ (ρ X) = ρ X ↔
      ∃ Y : SL(ν, k), X = H * Matrix.SpecialLinearGroup.map (algebraMap k L) Y * H⁻¹) ∧
    Finite ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) ∧
    CFSG.IsQuasisimple ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) ∧
    Nat.card (Subgroup.center ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _))) =
      Nat.gcd ν (ℓ ^ f - 1) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < ℓ ^ f from pow_pos hℓ.pos f)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  have htne : ∀ i j : Fin ν, i ≠ j →
      ((fun i j => (π i, π j) : Fin ν → Fin ν → Fin ν × Fin ν) i j).1 ≠
        ((fun i j => (π i, π j) : Fin ν → Fin ν → Fin ν × Fin ν) i j).2 :=
    fun i j hij => π.injective.ne hij
  have htsurj : ∀ i j : Fin ν, i ≠ j → ∃ i' j' : Fin ν, i' ≠ j' ∧
      (fun i j => (π i, π j) : Fin ν → Fin ν → Fin ν × Fin ν) i' j' = (i, j) :=
    fun i j hij => ⟨π.symm i, π.symm j, π.symm.injective.ne hij, by simp⟩
  obtain ⟨Φ', hΦ', b, hshape⟩ := h.exists_aut hinj Fr hFrbij Ψ hΨinj
    (fun i j => (π i, π j)) htne htsurj hΨ
  obtain ⟨-, ⟨H, hH⟩, hfin, hqs, -, hcard⟩ :=
    sln_root_permuting_frobenius_fixed_split hℓ hf hk hν π Φ' b
      (fun i j hij t => by rw [hshape i j hij t, hFr])
  have heq := range_inf_eqLocus_eq_map hinj Ψ Φ' hΦ'
  let e : ↥(fixSubgroup Φ') ≃* ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) :=
    (Subgroup.equivMapOfInjective _ ρ hinj).trans (MulEquiv.subgroupCongr heq.symm)
  refine ⟨⟨H, fun X => ?_⟩, Finite.of_equiv _ e.toEquiv,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqs,
    (natCard_center_eq_of_mulEquiv e).symm.trans hcard⟩
  rw [hΦ' X, ← hH X]
  exact ⟨fun h1 => hinj h1, fun h1 => by rw [h1]⟩

theorem conj_entrywise_pinnedX {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) (Fr : L →+* L)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ μ : Lˣ, ∀ c : L, ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr)))
      (pinnedX τ L γ c) = pinnedX τ L (weylQuotientHom τ L ⟨n, hn⟩ • γ) ((μ : L) * Fr c) := by
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hγ
  refine ⟨μ, fun c => ?_⟩
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [units_map_entrywiseHom_pinnedX, hμ]

theorem conj_entrywise_injective (n : ModGL τ L) (Fr : L →+* L) :
    Function.Injective ((MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom Fr))) :=
  (MulAut.conj n).injective.comp
    (Units.map_injective (f := entrywiseHom Fr) (entrywise_injective Fr))

theorem range_inf_fixModel (h : IsSLFrame ρ σ) (Ψ : ModGL τ L →* ModGL τ L) :
    ρ.range ⊓ fixModel Ψ = ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _) := by
  rw [fixModel, ← inf_assoc, inf_eq_left.2 h.range_le_adjointGroup]

theorem fixModel_unitary (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin ν))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c)) :
    Finite ↥(ρ.range ⊓ fixModel Ψ) ∧
    ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple ↥(ρ.range ⊓ fixModel Ψ) ∧
      Nat.card (Subgroup.center ↥(ρ.range ⊓ fixModel Ψ)) = Nat.gcd ν (ℓ ^ f + 1)) := by
  rw [h.range_inf_fixModel Ψ]
  obtain ⟨-, hfin, hq⟩ := h.fix_unitary hinj hℓ hf hk hν Fr hFr Ψ hΨinj π hΨ
  exact ⟨hfin, hq⟩

theorem fixModel_split (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    (Ψ : ModGL τ L →* ModGL τ L) (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin ν))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π i) (π j)) ((b : L) * Fr c)) :
    Finite ↥(ρ.range ⊓ fixModel Ψ) ∧ CFSG.IsQuasisimple ↥(ρ.range ⊓ fixModel Ψ) ∧
      Nat.card (Subgroup.center ↥(ρ.range ⊓ fixModel Ψ)) = Nat.gcd ν (ℓ ^ f - 1) := by
  rw [h.range_inf_fixModel Ψ]
  obtain ⟨-, hfin, hq, hc⟩ := h.fix_split hinj hℓ hf hk hν Fr hFr Ψ hΨinj π hΨ
  exact ⟨hfin, hq, hc⟩

theorem twModel_unitary (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L) (π : Equiv.Perm (Fin ν))
    (hw : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hn⟩ • σ i j = σ (π j) (π i)) :
    Finite ↥(ρ.range ⊓ twModel n Fr) ∧
    ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple ↥(ρ.range ⊓ twModel n Fr) ∧
      Nat.card (Subgroup.center ↥(ρ.range ⊓ twModel n Fr)) = Nat.gcd ν (ℓ ^ f + 1)) := by
  rw [twModel_eq_fixModel]
  refine h.fixModel_unitary hinj hℓ hf hk hν Fr hFr _ (conj_entrywise_injective n Fr) π
    fun i j hij => ?_
  obtain ⟨μ, hμ⟩ := conj_entrywise_pinnedX hn Fr (h.isRoot i j hij)
  exact ⟨μ, fun c => by rw [hμ c, hw i j hij]⟩

theorem twModel_neg (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ) {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f))
    {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    (hw : ∀ i j, i ≠ j → weylQuotientHom τ L ⟨n, hn⟩ • σ i j = -σ i j) :
    Finite ↥(ρ.range ⊓ twModel n Fr) ∧
    ((ν, ℓ ^ f) ≠ (3, 2) → CFSG.IsQuasisimple ↥(ρ.range ⊓ twModel n Fr) ∧
      Nat.card (Subgroup.center ↥(ρ.range ⊓ twModel n Fr)) = Nat.gcd ν (ℓ ^ f + 1)) :=
  h.twModel_unitary hinj hℓ hf hk hν Fr hFr hn (Equiv.refl _) fun i j hij => by
    rw [hw i j hij, Equiv.refl_apply, Equiv.refl_apply, h.neg j i, neg_neg]

theorem inf_eq_of_le {G : Type*} [Group G] {X A M : Subgroup G} (hAM : A ≤ M)
    (hle : X ⊓ M ≤ A) : X ⊓ A = X ⊓ M :=
  le_antisymm (inf_le_inf_left _ hAM) (le_inf inf_le_left hle)

end IsSLFrame

end Fixed

end CFSG.HardMathSupport.Timmesfeld.CrossChar

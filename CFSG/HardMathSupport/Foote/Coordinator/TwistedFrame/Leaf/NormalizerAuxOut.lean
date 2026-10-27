module

public import CFSG.LieType.Universal.Unitary.Clause0
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherClassicalSchreier
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSL
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.NormalizerAuxBridge

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LieType.BorelTits

theorem outer_solvable_statedSU {F : Type} [Field F] [Finite F] {n p f : ℕ} [Fact p.Prime]
    [CharP F p] (hn : 3 ≤ n) (hnq : (n, p ^ f) ≠ (3, 2)) (hf : 1 ≤ f)
    (hF : Nat.card F = (p ^ f) ^ 2) : Group.IsSolvable (Outer ↥(StatedSU n (p ^ f) F)) := by
  have hadm : StatedLieAdmissible .PSU n p f := ⟨Fact.out, hf, hn, hnq⟩
  have hmod := Unitary.statedClassicalModel_center_quotient (n := n) (F := F) (p := p) (f := f)
    hadm hF
  have hs := (unitary_classical_model_schreier hmod).2
  have hqs := Unitary.isQuasisimple_SU (n := n) (p := p) (f := f) hF hn hnq
  have : Group.IsPerfect (Unitary.SU (unitaryInvolution F p f) n) := hqs.1
  have : Group.IsSolvable (Outer (Unitary.SU (unitaryInvolution F p f) n ⧸
      Subgroup.center (Unitary.SU (unitaryInvolution F p f) n))) := hs
  have h1 : Group.IsSolvable (Outer (Unitary.SU (unitaryInvolution F p f) n)) :=
    solvable_of_centerQuotient _
  exact solvable_of_equiv (Unitary.equivStatedSU hF n)

section FixUnitary

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable
  {τ : Tag} {L : Type} [Field L] {ν : ℕ}

theorem quasisimple_outer_solvable_fix_unitary {ρ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (h : IsSLFrame ρ σ) (hinj : Function.Injective ρ)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k L] [IsAlgClosure k L]
    (hk : Nat.card k = ℓ ^ f) (hν : 3 ≤ ν) (hνq : (ν, ℓ ^ f) ≠ (3, 2)) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (Ψ : ModGL τ L →* ModGL τ L)
    (hΨinj : Function.Injective Ψ) (π : Equiv.Perm (Fin ν))
    (hΨ : ∀ i j, i ≠ j → ∃ b : Lˣ, ∀ c : L,
      Ψ (pinnedX τ L (σ i j) c) = pinnedX τ L (σ (π j) (π i)) ((b : L) * Fr c)) :
    CFSG.IsQuasisimple ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) ∧
      Group.IsSolvable (Outer ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _))) := by
  classical
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed k
  have : Fact ℓ.Prime := ⟨hℓ⟩
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
  obtain ⟨-, ⟨H, hH⟩, -, hbig, -⟩ :=
    sln_root_permuting_frobenius_fixed_unitary hℓ hf hk hν π Φ' b
      (fun i j hij t => by rw [hshape i j hij t, hFr])
  have heq := IsSLFrame.range_inf_eqLocus_eq_map hinj Ψ Φ' hΦ'
  let e₂ : ↥(fixSubgroup Φ') ≃* ↥(ρ.range ⊓ Ψ.eqLocus (MonoidHom.id _)) :=
    (Subgroup.equivMapOfInjective _ ρ hinj).trans (MulEquiv.subgroupCongr heq.symm)
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; exact (pow_pos hℓ.pos f).ne')
  have : Fintype k := Fintype.ofFinite k
  have : CharP k ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hk])
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap k L).injective ℓ
  set F : Subfield L := (iterateFrobenius L ℓ (2 * f)).eqLocusField (RingHom.id L) with hFdef
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hF2 : ∀ c : L, c ∈ F ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hFdef, RingHom.mem_eqLocusField, iterateFrobenius_def, RingHom.id_apply]
  have hF : ∀ c : L, c ∈ F ↔ c ^ (ℓ ^ f) ^ 2 = c := fun c => by
    rw [hq2]
    exact hF2 c
  have hFcard : Nat.card F = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := L) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hF2)
  have : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hFcard]
    exact (pow_pos (pow_pos hℓ.pos f) 2).ne')
  have : Fintype F := Fintype.ofFinite F
  have : CharP F ℓ := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hFcard, hq2])
  let Θ : StatedSU ν (ℓ ^ f) F →* SL(ν, L) :=
    (MulAut.conj H).toMonoidHom.comp (statedSUToSL F ν (ℓ ^ f))
  have hΘmem : ∀ Y, Θ Y ∈ fixSubgroup Φ' := by
    intro Y
    rw [hH]
    refine ⟨Matrix.SpecialLinearGroup.toGL (statedSUToSL F ν (ℓ ^ f) Y),
      (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mp ⟨Y, rfl⟩, ?_⟩
    change Matrix.SpecialLinearGroup.toGL (H * statedSUToSL F ν (ℓ ^ f) Y * H⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hΘsurj : ∀ X ∈ fixSubgroup Φ', ∃ Y, Θ Y = X := by
    intro X hX
    obtain ⟨Y', hY', hXY⟩ := (hH X).mp hX
    have hW : Matrix.SpecialLinearGroup.toGL (H⁻¹ * X * H) = Y' := by
      rw [map_mul, map_mul, map_inv, hXY]
      group
    obtain ⟨Y, hY⟩ := (mem_range_statedSUToSL_iff hℓ F hF hFcard (by omega) _).mpr (hW ▸ hY')
    refine ⟨Y, ?_⟩
    change H * statedSUToSL F ν (ℓ ^ f) Y * H⁻¹ = X
    rw [show statedSUToSL F ν (ℓ ^ f) Y = H⁻¹ * X * H from hY]
    group
  let e₁ : StatedSU ν (ℓ ^ f) F ≃* fixSubgroup Φ' :=
    MulEquiv.ofBijective (Θ.codRestrict _ hΘmem)
      ⟨fun Y Z hYZ => statedSUToSL_injective F ν (ℓ ^ f)
        ((MulAut.conj H).injective (congrArg Subtype.val hYZ)), fun X => by
          obtain ⟨Y, hY⟩ := hΘsurj X X.2
          exact ⟨Y, Subtype.ext hY⟩⟩
  haveI : Group.IsSolvable (Outer ↥(StatedSU ν (ℓ ^ f) F)) :=
    outer_solvable_statedSU hν hνq hf hFcard
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂ (hbig hνq).1,
    solvable_of_equiv (e₁.trans e₂)⟩

end FixUnitary

section LangLeviUnitary

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


theorem quasisimple_outer_solvable_fixedRoot_unitary {τ : Tag} {K : Type} [Field K] [Finite K]
    {w : WeylGroup τ} (D : LangLevi τ K w) {ν : ℕ} (hν : 3 ≤ ν) (hq2 : (ν, Nat.card K) ≠ (3, 2))
    {ρ : SL(ν, D.L) →* ModGL τ D.L} {r : Fin ν → Fin ν → Fin τ.rank → ℤ} (h : IsSLFrame ρ r)
    (hinj : Function.Injective ρ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ i j, i ≠ j → w • r i j = r (π j) (π i)) :
    CFSG.IsQuasisimple ↥(fixedRoot D (frameRoots r)) ∧
      Group.IsSolvable (Outer ↥(fixedRoot D (frameRoots r))) := by
  classical
  haveI : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  obtain ⟨p, hpK⟩ := CharP.exists K
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hpp, hcard⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hpp⟩
  have hcard' : Nat.card K = p ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hFr : ∀ c, D.Fr c = c ^ (p ^ (m : ℕ)) := fun c => by rw [D.hFr, hcard']
  have hnm : nW D ∈ monomialSubgroup τ D.L := canonicalRep_mem_monomialSubgroup D.L w
  have hΨ : ∀ i j : Fin ν, i ≠ j → ∃ b : (D.L)ˣ, ∀ c : D.L,
      ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D)) (pinnedX τ D.L (r i j) c) =
        pinnedX τ D.L (r (π j) (π i)) ((b : D.L) * D.Fr c) := by
    intro i j hij
    obtain ⟨μ, hμ⟩ := IsSLFrame.conj_entrywise_pinnedX hnm D.Fr (h.isRoot i j hij)
    refine ⟨μ, fun c => ?_⟩
    rw [hμ c, weylQuotientHom_eq (mapsRootLines_canonicalRep w), hπ i j hij]
  have hq2' : (ν, p ^ (m : ℕ)) ≠ (3, 2) := by rw [← hcard']; exact hq2
  have key := quasisimple_outer_solvable_fix_unitary h hinj hpp m.pos (k := K) hcard' hν hq2'
    D.Fr hFr ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D))
    (IsSLFrame.conj_entrywise_injective (nW D) D.Fr) π hΨ
  have e : fixedRoot D (frameRoots r) =
      ρ.range ⊓ ((MulAut.conj (nW D)).toMonoidHom.comp (frobGL D)).eqLocus (MonoidHom.id _) := by
    rw [h.range]
    rfl
  rw [e]
  exact key

end LangLeviUnitary

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.NormalizerAux

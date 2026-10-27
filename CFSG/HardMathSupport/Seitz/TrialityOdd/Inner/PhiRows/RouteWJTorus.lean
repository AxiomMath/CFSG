module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeP
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWInvolution

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Matrix

section Pure

variable {L : Type} [Field L]

@[expose] def coinvProj (m : Fin TwistTag.D4.tag.rank → ℤ) : Fin Tag.G2.rank → ℤ :=
  ![m 0 + m 1 + m 3, m 2]

@[expose] def invTuple (xy : Fin Tag.G2.rank → Lˣ) : Fin TwistTag.D4.tag.rank → Lˣ :=
  ![xy 0, xy 0, xy 1, xy 0]

theorem prod_rank_d4 {M : Type*} [CommMonoid M] (f : Fin TwistTag.D4.tag.rank → M) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 := Fin.prod_univ_four f

theorem prod_rank_g2 {M : Type*} [CommMonoid M] (f : Fin Tag.G2.rank → M) :
    ∏ i, f i = f 0 * f 1 := Fin.prod_univ_two f

theorem rootChar_invTuple (xy : Fin Tag.G2.rank → Lˣ) (m : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar (invTuple xy) m = rootChar xy (coinvProj m) := by
  unfold rootChar
  rw [prod_rank_d4, prod_rank_g2]
  change (xy 0) ^ m 0 * (xy 0) ^ m 1 * (xy 1) ^ m 2 * (xy 0) ^ m 3 =
    (xy 0) ^ (m 0 + m 1 + m 3) * (xy 1) ^ m 2
  rw [zpow_add, zpow_add]
  ac_rfl

@[expose] def invBar (b : Fin TwistTag.D4.tag.rank → Lˣ) : Fin Tag.G2.rank → Lˣ := ![b 0, b 2]

theorem eq_invTuple_of_invariant (b : Fin TwistTag.D4.tag.rank → Lˣ)
    (hb : ∀ i, b (TwistTag.D4.perm i) = b i) : b = invTuple (invBar b) := by
  have h1 : b 1 = b 0 := hb 0
  have h3 : b 3 = b 0 := ((hb 1 : b 3 = b 1)).trans h1
  funext i
  fin_cases i
  · rfl
  · exact h1
  · rfl
  · exact h3

end Pure


section TorusLang

variable {L : Type} [Field L] [IsAlgClosed L]

theorem torus_lang_of_char (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x =
      M *ᵥ permLattice TwistTag.D4.perm.symm x)
    (a b : Fin TwistTag.D4.tag.rank → Lˣ)
    (hkey : ∀ m, rootChar a m ^ q = rootChar a (M *ᵥ m) * rootChar b (M *ᵥ m)) :
    n * twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag a * rootDiagUnit TwistTag.D4.tag b := by
  classical
  set ρ := TwistTag.D4.perm
  set v := weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩
  set c := canonicalRep (coxeterSystem TwistTag.D4.tag) L v with hc
  have hh : c * n⁻¹ ∈ torusGroup TwistTag.D4.tag L :=
    canonicalRep_mul_inv_mem_torusGroup hn v rfl
  have hh' : n * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
    simpa using inv_mem hh
  set a' : Fin TwistTag.D4.tag.rank → Lˣ := fun i => Units.map Fr.toMonoidHom (a (ρ.symm i))
    with ha'
  have e1 : twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag a' := twistHom_rootDiagUnit_eq a
  have e2 : n * rootDiagUnit TwistTag.D4.tag a' * n⁻¹ =
      rootDiagUnit TwistTag.D4.tag (weylTuple v a') := by
    have hcy : c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹ ∈ torusGroup TwistTag.D4.tag L := by
      rw [hc, canonicalRep_conj_rootDiagUnit]
      exact rootDiagUnit_mem_torusGroup _
    have hcomm := torusGroup_comm hh' hcy
    calc n * rootDiagUnit TwistTag.D4.tag a' * n⁻¹ =
          (n * c⁻¹) * (c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹) * (n * c⁻¹)⁻¹ := by group
      _ = c * rootDiagUnit TwistTag.D4.tag a' * c⁻¹ := by rw [hcomm, mul_inv_cancel_right]
      _ = _ := canonicalRep_conj_rootDiagUnit v a'
  rw [e1, e2, ← rootDiagUnit_mul]
  congr 1
  have hchar : ∀ u, rootChar (weylTuple v a') u = rootChar (a * b) u := fun u => by
    obtain ⟨x, rfl⟩ : ∃ x, u = v • x := ⟨v⁻¹ • u, (smul_inv_smul v u).symm⟩
    rw [rootChar_weylTuple, inv_smul_smul, CTTorus.rootChar_mul, ha',
      rootChar_map_tuple Fr (fun i => a (ρ.symm i)) x, ← rootChar_permLattice a ρ.symm x,
      CTTorus.map_units_eq_pow hFr, hM x]
    exact hkey _
  funext i
  have := hchar (Pi.single i 1)
  rwa [CTTorus.rootChar_single, CTTorus.rootChar_single] at this

theorem exists_invariant_torus_adjust (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x =
      M *ᵥ permLattice TwistTag.D4.perm.symm x)
    (Mbar : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ)
    (hproj : ∀ m, coinvProj (M *ᵥ m) = Mbar *ᵥ coinvProj m)
    (hdet : ((q : ℤ) • (1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) - Mbar).det ≠ 0)
    (b : Fin TwistTag.D4.tag.rank → Lˣ) (hb : ∀ i, b (TwistTag.D4.perm i) = b i) :
    ∃ xy : Fin Tag.G2.rank → Lˣ,
      n * twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (invTuple xy)) * n⁻¹ =
        rootDiagUnit TwistTag.D4.tag (invTuple xy) * rootDiagUnit TwistTag.D4.tag b := by
  obtain ⟨xy, hxy⟩ := exists_tuple_of_char_eq (L := L) (τ := Tag.G2)
    ((q : ℤ) • (1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) - Mbar) Mbar hdet (invBar b)
  refine ⟨xy, torus_lang_of_char Fr hFr hn M hM _ _ fun m => ?_⟩
  have hbm := eq_invTuple_of_invariant b hb
  have hb' : ∀ u, rootChar b u = rootChar (invBar b) (coinvProj u) := fun u => by
    conv_lhs => rw [hbm]
    exact rootChar_invTuple _ _
  rw [rootChar_invTuple, rootChar_invTuple, hb', hproj m]
  have h := hxy (coinvProj m)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, rootChar_sub, rootChar_zsmul,
    zpow_natCast, mul_inv_eq_iff_eq_mul] at h
  rw [h, mul_comm]

theorem exists_invariant_tuple_of_comm {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L)
    (hP : diagramMap TwistTag.D4 L * t = t * diagramMap TwistTag.D4 L) :
    ∃ b : Fin TwistTag.D4.tag.rank → Lˣ, t = rootDiagUnit TwistTag.D4.tag b ∧
      ∀ i, b (TwistTag.D4.perm i) = b i := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  refine ⟨b, rfl, fun i => ?_⟩
  have h1 := diagramMap_pow_conj_rootDiagUnit (L := L) b 1
  have h0 : diagramMap TwistTag.D4 L * rootDiagUnit TwistTag.D4.tag b *
      (diagramMap TwistTag.D4 L ^ 1)⁻¹ = rootDiagUnit TwistTag.D4.tag b := by
    rw [pow_one, hP]
    group
  rw [pow_one] at h1 h0
  have h2 := congrArg (fun a => a (TwistTag.D4.perm i)) (rootDiagUnit_injective (h0.symm.trans h1))
  simpa using h2

theorem exists_invariant_lang_opposition (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {n : ModGL TwistTag.D4.tag L} (hn : n ∈ monomialSubgroup TwistTag.D4.tag L)
    (hnP : diagramMap TwistTag.D4 L * n = n * diagramMap TwistTag.D4 L)
    (M : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ)
    (hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • x =
      M *ᵥ permLattice TwistTag.D4.perm.symm x)
    (Mbar : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ)
    (hproj : ∀ m, coinvProj (M *ᵥ m) = Mbar *ᵥ coinvProj m)
    (hdet : ((q : ℤ) • (1 : Matrix (Fin Tag.G2.rank) (Fin Tag.G2.rank) ℤ) - Mbar).det ≠ 0) :
    ∃ xy : Fin Tag.G2.rank → Lˣ,
      n * twistHom TwistTag.D4 L Fr
        (rootDiagUnit TwistTag.D4.tag (invTuple xy) * trialityOpposition L) * n⁻¹ =
        rootDiagUnit TwistTag.D4.tag (invTuple xy) * trialityOpposition L := by
  set z := trialityOpposition L with hz
  set t' := n * z * n⁻¹ * z⁻¹ with ht'
  have ht'T : t' ∈ torusGroup TwistTag.D4.tag L := n_conj_opposition_mem_torus hn
  have hzP : Commute (diagramMap TwistTag.D4 L) z := diagramMap_comm_trialityOpposition
  have hnP' : Commute (diagramMap TwistTag.D4 L) n := hnP
  have ht'P : Commute (diagramMap TwistTag.D4 L) t'⁻¹ :=
    (((hnP'.mul_right hzP).mul_right hnP'.inv_right).mul_right hzP.inv_right).inv_right
  obtain ⟨b, hb, hbi⟩ := exists_invariant_tuple_of_comm (inv_mem ht'T) ht'P
  obtain ⟨xy, hxy⟩ := exists_invariant_torus_adjust Fr hFr hn M hM Mbar hproj hdet b hbi
  refine ⟨xy, ?_⟩
  rw [← hb] at hxy
  have hzz : twistHom TwistTag.D4 L Fr z = z := twistHom_trialityOpposition Fr
  rw [map_mul, hzz]
  calc n * (twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (invTuple xy)) * z) * n⁻¹
      = (n * twistHom TwistTag.D4 L Fr (rootDiagUnit TwistTag.D4.tag (invTuple xy)) * n⁻¹) *
          (n * z * n⁻¹) := by group
    _ = (rootDiagUnit TwistTag.D4.tag (invTuple xy) * t'⁻¹) * (t' * z) := by
        rw [hxy]
        congr 1
        rw [ht']
        group
    _ = rootDiagUnit TwistTag.D4.tag (invTuple xy) * z := by group

end TorusLang

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

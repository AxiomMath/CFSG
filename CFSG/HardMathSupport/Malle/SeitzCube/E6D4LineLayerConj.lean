module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6D4LineTransport
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4TorusLang
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneLeaf

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.RankThree.PartOne.KE6 (phi3N phi3Matrix det_phi3Matrix weylMatrix_e6T3W_eq)
open CFSG.GH74.GLS.Stage2.Bender.Thm1 (exists_tuple_of_char_eq)
open scoped Matrix

section Group

theorem twisted_conj_iff {G : Type*} [Group G] (Φ : G →* G) (τ mm n' c nu : G)
    (hnu : nu = τ * (mm * n' * mm⁻¹)) (hΦm : Φ mm = mm) (hc : nu * Φ c * nu⁻¹ = c * τ⁻¹)
    (x : G) :
    n' * Φ x * n'⁻¹ = x ↔
      nu * Φ (c * mm * x * (c * mm)⁻¹) * nu⁻¹ = c * mm * x * (c * mm)⁻¹ := by
  have e : nu * Φ (c * mm * x * (c * mm)⁻¹) * nu⁻¹ =
      c * mm * (n' * Φ x * n'⁻¹) * (c * mm)⁻¹ := by
    have e1 : nu * Φ (c * mm * x * (c * mm)⁻¹) * nu⁻¹ =
        (nu * Φ c * nu⁻¹) * (nu * mm * Φ x * mm⁻¹ * nu⁻¹) * (nu * Φ c * nu⁻¹)⁻¹ := by
      simp only [map_mul, map_inv, hΦm]
      group
    have e2 : nu * mm * Φ x * mm⁻¹ * nu⁻¹ = τ * mm * (n' * Φ x * n'⁻¹) * mm⁻¹ * τ⁻¹ := by
      rw [hnu]
      group
    rw [e1, hc, e2]
    group
  rw [e]
  constructor
  · intro h
    rw [h]
  · intro h
    have := (MulAut.conj (c * mm)).injective (a₁ := n' * Φ x * n'⁻¹) (a₂ := x) (by
      simpa [MulAut.conj_apply] using h)
    exact this

end Group

section Torus

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem rootChar_mul_e6 (a b : Fin Tag.E6.rank → Ωˣ) (v : Fin Tag.E6.rank → ℤ) :
    rootChar (a * b) v = rootChar a v * rootChar b v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem phi3_torus_adjust {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {t : ModGL Tag.E6 Ω} (ht : t ∈ torusGroup Tag.E6 Ω) :
    ∃ s ∈ torusGroup Tag.E6 Ω,
      phi3N Ω * Units.map (entrywiseHom Fr) s * (phi3N Ω)⁻¹ = s * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hM : ∀ v : Fin Tag.E6.rank → ℤ, CFSG.RankThree.PartOne.KE6.e6T3Matrix *ᵥ v =
      CFSG.RankThree.Lattice.e6T3W • v := fun v => by
    rw [← weylMatrix_e6T3W_eq, weylMatrix_mulVec]
  have hdet : (((q : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) -
      CFSG.RankThree.PartOne.KE6.e6T3Matrix).det ≠ 0) := by
    have e : ((q : ℤ) • (1 : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) -
        CFSG.RankThree.PartOne.KE6.e6T3Matrix) = -phi3Matrix q := by
      ext i j
      simp [phi3Matrix]
    rw [e, Matrix.det_neg, Fintype.card_fin, det_phi3Matrix]
    have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
    rw [h6, one_mul]
    exact pow_ne_zero _ (by positivity)
  obtain ⟨a, ha⟩ := exists_tuple_of_char_eq ((q : ℤ) • 1 -
    CFSG.RankThree.PartOne.KE6.e6T3Matrix) CFSG.RankThree.PartOne.KE6.e6T3Matrix hdet b
  have hkey : ∀ v, rootChar a v ^ q =
      rootChar a (CFSG.RankThree.Lattice.e6T3W • v) *
        rootChar b (CFSG.RankThree.Lattice.e6T3W • v) := fun v => by
    have h := ha v
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, rootChar_sub, rootChar_zsmul,
      zpow_natCast, mul_inv_eq_iff_eq_mul, hM] at h
    rw [h, mul_comm]
  refine ⟨rootDiagUnit Tag.E6 a, rootDiagUnit_mem_torusGroup a, ?_⟩
  rw [entrywise_frob_rootDiagUnit Fr hFr, ← rootDiagUnit_mul]
  exact ((rootDiagUnit_eq_conj_canonicalRep_iff (a * b) (a ^ q)
    CFSG.RankThree.Lattice.e6T3W).2 fun v => by
      rw [rootChar_mul_e6, ← hkey, rootChar_pow_tuple]).symm

end Torus

section Conj

set_option linter.unusedSectionVars false

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem e6D4_twistedFixedPoints_conj {Fr : Ω →+* Ω} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (n' : ModGL Tag.E6 Ω) (hn' : n' ∈ monomialSubgroup Tag.E6 Ω)
    (hw : weylQuotientHom Tag.E6 Ω ⟨n', hn'⟩ = e6D4wp) :
    ∃ c ∈ torusGroup Tag.E6 Ω,
      (twistedFixedPoints n' (Units.map (entrywiseHom Fr))).map
        (MulAut.conj (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)).toMonoidHom =
      twistedFixedPoints (phi3N Ω) (Units.map (entrywiseHom Fr)) := by
  have hFrb : Function.Bijective Fr := by
    refine ⟨Fr.injective, fun y => ?_⟩
    have hq : 0 < q := by
      rcases Nat.eq_zero_or_pos q with rfl | h
      · have := hFr 0
        simp at this
      · exact h
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨z, by rw [hFr, hz]⟩
  set Φ : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := Units.map (entrywiseHom Fr) with hΦ
  set mm := canonicalRep (coxeterSystem Tag.E6) Ω e6D4m with hmmdef
  have hmm : mm ∈ monomialSubgroup Tag.E6 Ω := canonicalRep_mem_monomialSubgroup Ω e6D4m
  have hΦm : Φ mm = mm := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrb) e6D4m
  set n'' := mm * n' * mm⁻¹ with hn''def
  have hn'' : n'' ∈ monomialSubgroup Tag.E6 Ω := mul_mem (mul_mem hmm hn') (inv_mem hmm)
  have hwm : weylQuotientHom Tag.E6 Ω ⟨mm, hmm⟩ = e6D4m :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep e6D4m)
  have hwu : weylQuotientHom Tag.E6 Ω ⟨n'', hn''⟩ = CFSG.RankThree.Lattice.e6T3W := by
    have : (⟨n'', hn''⟩ : monomialSubgroup Tag.E6 Ω) =
        ⟨mm, hmm⟩ * ⟨n', hn'⟩ * ⟨mm, hmm⟩⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hw, hwm, e6D4m_mul_wp]
    group
  have hτ : phi3N Ω * n''⁻¹ ∈ torusGroup Tag.E6 Ω :=
    CFSG.RankThree.PartOne.KE.canonicalRep_mul_inv_mem_torusGroup hn'' CFSG.RankThree.Lattice.e6T3W hwu
  obtain ⟨c, hcT, hc⟩ := phi3_torus_adjust hFr (inv_mem hτ)
  refine ⟨c, hcT, ?_⟩
  have hnu : phi3N Ω = (phi3N Ω * n''⁻¹) * (mm * n' * mm⁻¹) := by
    rw [← hn''def]
    group
  have key := twisted_conj_iff Φ (phi3N Ω * n''⁻¹) mm n' c (phi3N Ω) hnu hΦm hc
  ext z
  simp only [Subgroup.mem_map, mem_twistedFixedPoints, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (key x).1 hx
  · intro hz
    refine ⟨(c * mm)⁻¹ * z * (c * mm), (key _).2 ?_, by group⟩
    convert hz using 2 <;> group

theorem torus_conj_mul_canonicalRep {c x : ModGL Tag.E6 Ω} (hc : c ∈ torusGroup Tag.E6 Ω)
    (hx : x ∈ torusGroup Tag.E6 Ω) :
    c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * x *
        (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹ =
      canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * x *
        (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹ := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have hT : canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * rootDiagUnit Tag.E6 a *
      (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹ ∈ torusGroup Tag.E6 Ω := by
    rw [canonicalRep_conj_rootDiagUnit]
    exact rootDiagUnit_mem_torusGroup _
  have hcomm := CFSG.RankThree.PartOne.KE.torusGroup_comm hc hT
  calc c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * rootDiagUnit Tag.E6 a *
        (c * canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹
      = c * (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m * rootDiagUnit Tag.E6 a *
        (canonicalRep (coxeterSystem Tag.E6) Ω e6D4m)⁻¹) * c⁻¹ := by group
    _ = _ := by rw [hcomm, mul_inv_cancel_right]

end Conj

end CFSG.HardMathSupport.Malle.SeitzCube

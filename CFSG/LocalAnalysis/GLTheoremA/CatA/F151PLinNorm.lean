module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.F151Defs
import CFSG.Assembly.GL83StatedBridge
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamInLinTransPsl
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA.F151

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.T171Sh
open CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem charP_two_of_card {F : Type} [Field F] [Finite F] {n : ℕ}
    (h : Nat.card F = 2 ^ n) : CharP F 2 := by
  letI : Fintype F := Fintype.ofFinite F
  obtain ⟨m, hp, hm⟩ := FiniteField.card F (ringChar F)
  rw [← Nat.card_eq_fintype_card, h] at hm
  have hd : ringChar F ∣ 2 ^ n := by
    rw [hm]
    exact dvd_pow_self _ (by have := m.pos; omega)
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  exact (ringChar.eq_iff).1 h2

private theorem map_centralizer_singleton {A B : Type*} [Group A] [Group B]
    (f : A ≃* B) (t : A) :
    (Subgroup.centralizer ({t} : Set A)).map f.toMonoidHom =
      Subgroup.centralizer ({f t} : Set B) := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa [map_mul] using congrArg f hx
  · intro hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨f.symm y, ?_, by simp⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply f.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]

private theorem shapeModelNormAt_of_mulEquiv {R R' : Type} [Group R] [Finite R] [Group R']
    [Finite R'] (e : R ≃* R') {p : ℕ} (hp : p.Prime) (h : ShapeModelNormAt R p) :
    ShapeModelNormAt R' p := by
  intro x' y' hx1 hxp hyp hcomm J' hJ'
  set x : R := e.symm x' with hx
  set y : R := e.symm y' with hy
  have hx1' : x ≠ 1 := fun h1 => hx1 (by
    have := congrArg e h1
    simpa [hx] using this)
  have hxp' : x ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simpa [hx] using hxp
  have hyp' : y ^ p = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    simpa [hy] using hyp
  have hcomm' : Commute x y := by
    have := hcomm.map e.symm.toMonoidHom
    simpa [hx, hy] using this
  let J : Subgroup R := J'.comap e.toMonoidHom
  have hJmap : J.map e.toMonoidHom = J' := by
    dsimp [J]
    exact Subgroup.map_comap_eq_self (by
      rw [MonoidHom.range_eq_top.mpr e.surjective]
      exact le_top)
  have hJmap' : J'.map e.symm.toMonoidHom = J := by
    dsimp [J]
    ext z
    constructor
    · rintro ⟨z', hz', rfl⟩
      show e (e.symm z') ∈ J'
      simpa using hz'
    · intro hz
      exact ⟨e z, by simpa using hz, by simp⟩
  have hJ : GLAPComponent p (Subgroup.centralizer ({x} : Set R)) J := by
    have hmap := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv hp e.symm hJ'
    rw [map_centralizer_singleton e.symm x', hJmap'] at hmap
    simpa [hx] using hmap
  have hy' : y ∈ Subgroup.normalizer (J : Set R) := h x y hx1' hxp' hyp' hcomm' J hJ
  have hmap : (Subgroup.normalizer (J : Set R)).map e.toMonoidHom =
      Subgroup.normalizer (J' : Set R') := by
    rw [Subgroup.map_normalizer_eq_of_bijective J e.bijective, hJmap]
  rw [← hmap]
  simpa [hy] using Subgroup.mem_map_of_mem e.toMonoidHom hy'

private theorem commute_lifts_of_proj_commute {K : Type} [Field K] [Finite K]
    {N p : ℕ} (hp : p.Prime) (hN : 2 ≤ N)
    (hnot : ¬ p ∣ Nat.gcd N (Nat.card K - 1))
    {A B : ↥(StatedSL N K)}
    (hA : (LargeEvenProjMk (StatedSL N K) A) ^ p = 1)
    (hcomm : (LargeEvenProjMk (StatedSL N K) A) * (LargeEvenProjMk (StatedSL N K) B) =
      (LargeEvenProjMk (StatedSL N K) B) * (LargeEvenProjMk (StatedSL N K) A)) :
    (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      (B : GL (Fin N) K) * (A : GL (Fin N) K) := by
  classical
  have hπ : LargeEvenProjMk (StatedSL N K) (A * B * A⁻¹ * B⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨c, hc⟩ := (projMk_eq_iff (d := N) (K := K) (x := (1 : ↥(StatedSL N K)))
    (y := A * B * A⁻¹ * B⁻¹)).mp (by rw [map_one, hπ])
  have hc' : Matrix.GeneralLinearGroup.scalar (Fin N) c =
      (A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ *
        (B : GL (Fin N) K)⁻¹ := by
    simpa using hc
  have hπAp : LargeEvenProjMk (StatedSL N K) (A ^ p) = 1 := by rw [map_pow, hA]
  obtain ⟨cA, hcA⟩ := (projMk_eq_iff (d := N) (K := K) (x := (1 : ↥(StatedSL N K)))
    (y := A ^ p)).mp (by rw [map_one, hπAp])
  have hcA' : Matrix.GeneralLinearGroup.scalar (Fin N) cA = (A : GL (Fin N) K) ^ p := by
    simpa using hcA
  have hAB : (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      Matrix.GeneralLinearGroup.scalar (Fin N) c *
        ((B : GL (Fin N) K) * (A : GL (Fin N) K)) := by
    rw [hc']; group
  have hconj : (A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin N) c * (B : GL (Fin N) K) := by
    rw [hAB]; group
  have hiter : ∀ k : ℕ, (A : GL (Fin N) K) ^ k * (B : GL (Fin N) K) *
      ((A : GL (Fin N) K) ^ k)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) * (B : GL (Fin N) K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : (A : GL (Fin N) K) ^ (k + 1) * (B : GL (Fin N) K) *
          ((A : GL (Fin N) K) ^ (k + 1))⁻¹ =
          (A : GL (Fin N) K) * ((A : GL (Fin N) K) ^ k * (B : GL (Fin N) K) *
            ((A : GL (Fin N) K) ^ k)⁻¹) * (A : GL (Fin N) K)⁻¹ := by group
      rw [e, ih]
      have hs : (A : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) =
          Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) * (A : GL (Fin N) K) :=
        (Matrix.GeneralLinearGroup.scalar_commute (c ^ k) (A : GL (Fin N) K)).symm
      calc (A : GL (Fin N) K) * (Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) *
            (B : GL (Fin N) K)) * (A : GL (Fin N) K)⁻¹
          = Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) *
              ((A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹) := by
            rw [← mul_assoc (A : GL (Fin N) K)
              (Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k)) (B : GL (Fin N) K), hs]
            group
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ k) *
              (Matrix.GeneralLinearGroup.scalar (Fin N) c * (B : GL (Fin N) K)) := by
            rw [hconj]
        _ = Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ (k + 1)) * (B : GL (Fin N) K) := by
            rw [← mul_assoc, ← map_mul, ← pow_succ]
  have hinj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin N) : Kˣ → GL (Fin N) K) := by
    intro a b hab
    have he := congrArg (fun g : GL (Fin N) K =>
      ((g : Matrix (Fin N) (Fin N) K) ⟨0, by omega⟩ ⟨0, by omega⟩)) hab
    exact Units.ext (by
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using he)
  have hζp : c ^ p = 1 := by
    have h := hiter p
    rw [← hcA'] at h
    have h2 : Matrix.GeneralLinearGroup.scalar (Fin N) cA * (B : GL (Fin N) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin N) cA)⁻¹ = (B : GL (Fin N) K) := by
      rw [Matrix.GeneralLinearGroup.scalar_commute cA (B : GL (Fin N) K), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [h2] at h
    have h3 : Matrix.GeneralLinearGroup.scalar (Fin N) (c ^ p) = 1 := by
      have h5 := congrArg (fun x : GL (Fin N) K => x * (B : GL (Fin N) K)⁻¹) h
      simpa using h5.symm
    exact hinj (h3.trans (map_one _).symm)
  have hζN : c ^ N = 1 := by
    have hdet : Matrix.GeneralLinearGroup.det ((A : GL (Fin N) K) * (B : GL (Fin N) K) *
        (A : GL (Fin N) K)⁻¹ * (B : GL (Fin N) K)⁻¹) = 1 := by simp [map_mul]
    rw [← hc'] at hdet
    simpa [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin] using hdet
  have hζcard : c ^ (Nat.card K - 1) = 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    have hcardu : Nat.card Kˣ = Nat.card K - 1 := by
      simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
    rw [← hcardu]
    exact pow_card_eq_one'
  have hζ1 : c = 1 := by
    have hdvd : orderOf c ∣ Nat.gcd N (Nat.card K - 1) :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.2 hζN) (orderOf_dvd_iff_pow_eq_one.2 hζcard)
    have hcop : (Nat.gcd N (Nat.card K - 1)).Coprime p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      exact hnot
    have hpdvd : orderOf c ∣ p := orderOf_dvd_iff_pow_eq_one.2 hζp
    have hone : orderOf c ∣ 1 := by
      have h := Nat.dvd_gcd hdvd hpdvd
      rwa [Nat.Coprime.gcd_eq_one hcop] at h
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hone)
  rw [hζ1] at hc'
  have h4 : (A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ *
      (B : GL (Fin N) K)⁻¹ = 1 := by rw [← hc', map_one]
  calc (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      ((A : GL (Fin N) K) * (B : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ *
        (B : GL (Fin N) K)⁻¹) * ((B : GL (Fin N) K) * (A : GL (Fin N) K)) := by group
    _ = (B : GL (Fin N) K) * (A : GL (Fin N) K) := by rw [h4, one_mul]

private theorem shapeModelNormAt_statedSL {K : Type} [Field K] [Finite K]
    {N m p : ℕ} (hN : 2 ≤ N) (hcard : Nat.card K = 2 ^ m) (hp : p.Prime) (hp2 : p ≠ 2)
    (hnot : ¬ p ∣ Nat.gcd N (2 ^ m - 1)) :
    ShapeModelNormAt (LargeEvenProj (StatedSL N K)) p := by
  haveI hKchar : CharP K 2 := charP_two_of_card hcard
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hnot' : ¬ p ∣ Nat.gcd N (Nat.card K - 1) := by
    rw [hcard]; exact hnot
  intro x y hx1 hxp hyp hcomm J hJ
  obtain ⟨A, hA⟩ : ∃ A : ↥(StatedSL N K), LargeEvenProjMk (StatedSL N K) A = x :=
    QuotientGroup.mk'_surjective _ x
  obtain ⟨B, hB⟩ : ∃ B : ↥(StatedSL N K), LargeEvenProjMk (StatedSL N K) B = y :=
    QuotientGroup.mk'_surjective _ y
  have hxpA : (LargeEvenProjMk (StatedSL N K) A) ^ p = 1 := by rw [hA]; exact hxp
  have hcommAB : (LargeEvenProjMk (StatedSL N K) A) * (LargeEvenProjMk (StatedSL N K) B) =
      (LargeEvenProjMk (StatedSL N K) B) * (LargeEvenProjMk (StatedSL N K) A) := by
    rw [hA, hB]; exact hcomm
  have hABcomm : (A : GL (Fin N) K) * (B : GL (Fin N) K) =
      (B : GL (Fin N) K) * (A : GL (Fin N) K) :=
    commute_lifts_of_proj_commute hp hN hnot' hxpA hcommAB
  let u : MulAut (LargeEvenProj (StatedSL N K)) := MulAut.conj x
  have hu : ∀ h h' : ↥(StatedSL N K), (h' : GL (Fin N) K) =
      (A : GL (Fin N) K) * (h : GL (Fin N) K) * (A : GL (Fin N) K)⁻¹ →
      u (LargeEvenProjMk (StatedSL N K) h) = LargeEvenProjMk (StatedSL N K) h' := by
    intro h h' hh
    change x * LargeEvenProjMk (StatedSL N K) h * x⁻¹ = LargeEvenProjMk (StatedSL N K) h'
    rw [← hA, ← map_mul, ← map_inv, ← map_mul,
      show ((A * h) * A⁻¹ : ↥(StatedSL N K)) = h' from Subtype.ext hh.symm]
  have hpow : u ^ p = 1 := by
    change (MulAut.conj x) ^ p = 1
    rw [← map_pow, hxp, map_one]
  have hfix : fixSubgroup u =
      Subgroup.centralizer ({x} : Set (LargeEvenProj (StatedSL N K))) := by
    ext z
    rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
    show MulAut.conj x z = z ↔ z * x = x * z
    rw [MulAut.conj_apply]
    constructor
    · intro hz
      calc z * x = (x * z * x⁻¹) * x := by rw [hz]
        _ = x * z := by group
    · intro hz
      calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [hz]
        _ = z := by group
  have hJ' : GLAPComponent p (fixSubgroup u) J := by
    rw [hfix]; exact hJ
  obtain ⟨d₁, D₁, hF, hFin, ι, ιSL, h2', hd₁, h22, h23, hιinj, hιSL, hJeq, hBk, _hSc, _E,
    _hE, _hT⟩ :=
    exists_linPsl_block (K := K) (d := N) h2 (by omega) (A : GL (Fin N) K) hp hp2 u hu hpow J hJ'
  letI : Field D₁ := hF
  letI : Finite D₁ := hFin
  have hblock : ∀ (z : ↥(StatedSL N K)),
      (z : GL (Fin N) K) * (A : GL (Fin N) K) = (A : GL (Fin N) K) * (z : GL (Fin N) K) →
      ∀ j ∈ J, LargeEvenProjMk (StatedSL N K) z * j *
        (LargeEvenProjMk (StatedSL N K) z)⁻¹ ∈ J := by
    intro z hz j hj
    rw [hJeq] at hj
    rw [hJeq]
    obtain ⟨jj, hjj, hjjeq⟩ := Subgroup.mem_map.mp hj
    obtain ⟨m, hm⟩ := MonoidHom.mem_range.mp hjj
    rw [← hjjeq, ← hm]
    obtain ⟨B₁, hB₁⟩ := hBk (z : GL (Fin N) K) (Subgroup.mem_centralizer_singleton_iff.mpr hz)
    let w : ↥(StatedSL N K) := z * ιSL m * z⁻¹
    have hw : (w : GL (Fin N) K) = ι (B₁ * (m : GL (Fin d₁) D₁) * B₁⁻¹) := by
      show (z : GL (Fin N) K) * (ιSL m : GL (Fin N) K) * (z : GL (Fin N) K)⁻¹ =
        ι (B₁ * (m : GL (Fin d₁) D₁) * B₁⁻¹)
      exact hB₁ m
    have hπw : LargeEvenProjMk (StatedSL N K) z *
        LargeEvenProjMk (StatedSL N K) (ιSL m) *
        (LargeEvenProjMk (StatedSL N K) z)⁻¹ = LargeEvenProjMk (StatedSL N K) w := by
      rw [← map_mul, ← map_inv, ← map_mul]
    rw [hπw]
    refine Subgroup.mem_map_of_mem _ ?_
    refine ⟨⟨B₁ * (m : GL (Fin d₁) D₁) * B₁⁻¹,
      (inferInstance : (StatedSL d₁ D₁).Normal).conj_mem m m.2 B₁⟩, ?_⟩
    apply Subtype.ext
    rw [hιSL]
    exact hw.symm
  have hBinvcomm : (B⁻¹ : GL (Fin N) K) * (A : GL (Fin N) K) =
      (A : GL (Fin N) K) * (B⁻¹ : GL (Fin N) K) := by
    have h : (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K) =
        (A : GL (Fin N) K) := by
      rw [mul_assoc, hABcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) =
        (B : GL (Fin N) K)⁻¹ * (A : GL (Fin N) K) * (B : GL (Fin N) K) *
          (B : GL (Fin N) K)⁻¹ := by group
      _ = (A : GL (Fin N) K) * (B : GL (Fin N) K)⁻¹ := by rw [h]
  refine Subgroup.mem_normalizer_iff.2 fun j => ⟨fun hj => ?_, fun hj => ?_⟩
  · simpa [hB] using hblock B hABcomm.symm j hj
  · have hBinv : LargeEvenProjMk (StatedSL N K) B⁻¹ = y⁻¹ := by rw [map_inv, hB]
    have hk := hblock (B⁻¹) (by simpa using hBinvcomm) (y * j * y⁻¹) hj
    rw [hBinv] at hk
    have heq : y⁻¹ * (y * j * y⁻¹) * (y⁻¹)⁻¹ = j := by group
    rwa [heq] at hk

theorem linNormModel_holds : LinNormModel := by
  intro N m K _ _ hN hcard p hp hp2 hnot
  let e : LargeEvenProj (LargeEvenSLGroup (Fin N) K) ≃*
      LargeEvenProj (StatedSL N K) :=
    QuotientGroup.equivQuotientSubgroupOfOfEq (A' := LargeEvenScalars (Fin N) K)
      (B' := LargeEvenScalars (Fin N) K) (A := LargeEvenSLGroup (Fin N) K)
      (B := StatedSL N K) rfl (largeEvenSLGroup_eq_statedSL N)
  exact shapeModelNormAt_of_mulEquiv e.symm hp (shapeModelNormAt_statedSL hN hcard hp hp2 hnot)

end CFSG.LocalAnalysis.GLTheoremA.F151

end

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Block
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Lift
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7CombCount
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Idem
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Proj
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Field
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1KerA7Conj

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

open Matrix Finset

open scoped Classical

variable {K : Type} [Field K]

theorem center_eq_one_seven {x : Matrix.SpecialLinearGroup (Fin 7) K}
    (hx : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) K)) (h3 : x ^ 3 = 1) : x = 1 := by
  obtain ⟨r, hr7, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have hr7' : r ^ 7 = 1 := by simpa using hr7
  have hscal3 : (Matrix.scalar (Fin 7) (r ^ 3) : Matrix (Fin 7) (Fin 7) K) = 1 := by
    have := congrArg Subtype.val h3
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, Matrix.SpecialLinearGroup.coe_one] at this
    exact this
  have hr3 : r ^ 3 = 1 := by
    have h00 := congrFun (congrFun hscal3 0) 0
    simpa [Matrix.scalar_apply] using h00
  have hg : r ^ (Nat.gcd 7 3) = 1 := pow_gcd_eq_one.mpr ⟨hr7', hr3⟩
  have hgcd : Nat.gcd 7 3 = 1 := by norm_num
  rw [hgcd, pow_one] at hg
  apply Subtype.ext
  rw [← hrx, hg, Matrix.SpecialLinearGroup.coe_one]
  rfl

theorem piSL7_inj_pow3 {x : Matrix.SpecialLinearGroup (Fin 7) K} (h3 : x ^ 3 = 1)
    (h : piSL7 K x = 1) : x = 1 := by
  apply center_eq_one_seven _ h3
  exact (QuotientGroup.eq_one_iff x).mp h

theorem H0_inj {x : Matrix.SpecialLinearGroup (Fin 7) K} (hx : x ∈ (H0 (K := K)))
    (h : piSL7 K x = 1) : x = 1 := by
  have hc : x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) K) :=
    (QuotientGroup.eq_one_iff x).mp h
  obtain ⟨r, hr7, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hxH : InH0 (x : Matrix (Fin 7) (Fin 7) K) := hx
  have hD : Dg K *ᵥ (Pi.single (6 : Fin 7) (1 : K)) = 0 := by
    funext i
    rw [Dg_eq, Matrix.mulVec_diagonal, Pi.zero_apply]
    by_cases hi : i = 6
    · subst hi
      simp
    · have hi6 : (i : ℕ) ≠ 6 := fun h => hi (Fin.ext h)
      by_cases h3 : (i : ℕ) < 3
      · simp [h3, Pi.single_apply, hi]
      · have : (i : ℕ) ≠ 6 := hi6
        simp [h3, Pi.single_apply, hi]
  have hfix := hxH.2 _ hD
  rw [← hrx] at hfix
  have hcoord := congrFun hfix 6
  simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Pi.single_apply] at hcoord
  have hr : r = 1 := by simpa using hcoord
  apply Subtype.ext
  rw [← hrx, hr, Matrix.SpecialLinearGroup.coe_one]
  rfl

theorem commute_of_pi {x y : Matrix.SpecialLinearGroup (Fin 7) K} (hy : y ^ 3 = 1)
    (h : piSL7 K x * piSL7 K y = piSL7 K y * piSL7 K x) : x * y = y * x := by
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hc1 : piSL7 K c = 1 := by
    rw [hcdef, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h' : piSL7 K x * piSL7 K y * (piSL7 K x)⁻¹ * (piSL7 K y)⁻¹ = 1 := by
      have h2 : piSL7 K x * piSL7 K y = piSL7 K y * piSL7 K x := h
      calc piSL7 K x * piSL7 K y * (piSL7 K x)⁻¹ * (piSL7 K y)⁻¹
          = piSL7 K y * piSL7 K x * (piSL7 K x)⁻¹ * (piSL7 K y)⁻¹ := by rw [h2]
        _ = 1 := by simp [mul_assoc]
    exact h'
  have hcmem : c ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 7) K) :=
    (QuotientGroup.eq_one_iff _).mp hc1
  have hcommute : Commute c y := (Subgroup.mem_center_iff.mp hcmem y).symm
  have hxyx : x * y * x⁻¹ = c * y := by
    rw [hcdef]
    simp [mul_assoc]
  have hpow : (x * y * x⁻¹) ^ 3 = 1 := by
    have e : (x * y * x⁻¹) ^ 3 = x * y ^ 3 * x⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left]
    rw [e, hy]
    simp
  have h5 : c ^ 3 * y ^ 3 = 1 := by
    rw [← hcommute.mul_pow 3, ← hxyx, hpow]
  have hc3 : c ^ 3 = 1 := by
    rw [hy, mul_one] at h5
    exact h5
  have hc : c = 1 := center_eq_one_seven hcmem hc3
  calc x * y = c * (y * x) := by
        rw [hcdef]
        simp [mul_assoc]
    _ = y * x := by rw [hc, one_mul]

theorem kerConcl_of_block (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K))
    (hP3 : ∀ x ∈ P', x ^ 3 = 1)
    (F' : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K)) (hF'P : F' ≤ P')
    (hF'card : Nat.card F' = 9)
    (hF'D : ∀ f ∈ F', (f : Matrix (Fin 7) (Fin 7) K) * Dg K = Dg K ∧
      Dg K * (f : Matrix (Fin 7) (Fin 7) K) = Dg K)
    (hcent : ∀ g : Matrix.SpecialLinearGroup (Fin 7) K, (∀ f ∈ F', g * f = f * g) →
      (g : Matrix (Fin 7) (Fin 7) K) * Dg K = Dg K * (g : Matrix (Fin 7) (Fin 7) K)) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl (P'.map (piSL7 K)) := by
  refine ⟨F'.map (piSL7 K), Subgroup.map_mono hF'P, ?_, ?_⟩
  · rw [card_map_eq_of_injOn (piSL7 K) F' (fun x hx h => piSL7_inj_pow3 (hP3 x (hF'P hx)) h)]
    exact hF'card
  · let H'' : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 7) K) :=
      (H0 (K := K)).map (piSL7 K)
    let ψhom : (H0 (K := K)) →* H'' :=
      ((piSL7 K).comp (H0 (K := K)).subtype).codRestrict H'' (fun x => ⟨x.1, x.2, rfl⟩)
    have hψinj : Function.Injective ψhom := by
      rw [injective_iff_map_eq_one]
      intro x hx
      apply Subtype.ext
      have h1 : piSL7 K x.1 = 1 := congrArg Subtype.val hx
      exact H0_inj x.2 h1
    have hψsurj : Function.Surjective ψhom := by
      rintro ⟨y, hy⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨x, hx⟩, rfl⟩
    let ψ : (H0 (K := K)) ≃* H'' := MulEquiv.ofBijective ψhom ⟨hψinj, hψsurj⟩
    have hle : H'' ≤ Subgroup.centralizer ((F'.map (piSL7 K) : Subgroup _) : Set _) := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hz
      have hxf : (x : Matrix (Fin 7) (Fin 7) K) * (f : Matrix (Fin 7) (Fin 7) K) =
          (f : Matrix (Fin 7) (Fin 7) K) * (x : Matrix (Fin 7) (Fin 7) K) :=
        InH0_comm hx (hF'D f hf).1 (hF'D f hf).2
      have hxf' : x * f = f * x := Subtype.ext (by
        simpa [Matrix.SpecialLinearGroup.coe_mul] using hxf)
      rw [← map_mul, ← map_mul, hxf']
    refine ⟨H'', hle, ?_, ?_, ?_⟩
    · refine CFSG.Open.IsSubnormal.step hle ?_ (CFSG.Open.IsSubnormal.refl _)
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (g : Matrix.ProjectiveSpecialLinearGroup (Fin 7) K)
      have hc' : piSL7 K c = (g : Matrix.ProjectiveSpecialLinearGroup (Fin 7) K) := hc
      have hcF : ∀ f ∈ F', c * f = f * c := by
        intro f hf
        have hgf := Subgroup.mem_centralizer_iff.mp g.2 (piSL7 K f)
          (Subgroup.mem_map.mpr ⟨f, hf, rfl⟩)
        apply commute_of_pi (hP3 f (hF'P hf))
        rw [hc']
        exact hgf.symm
      have hcD := hcent c hcF
      obtain ⟨n', hn'H0, hn'eq⟩ := Subgroup.mem_map.mp hn
      have hconj := H0_conj_mem c hcD n' hn'H0
      apply Subgroup.mem_map.mpr
      refine ⟨c * n' * c⁻¹, hconj, ?_⟩
      rw [map_mul, map_mul, map_inv, hc', hn'eq]
      rfl
    · exact CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.isQuasisimple_equiv ψ H0_isQuasisimple
    · rw [← CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.card_quotient_center_equiv ψ]
      exact H0_three_dvd

def kerSub {G : Type} [Group G] {L : Type} [Field L] (c : G → L) (hcmul : ∀ x y, c (x * y) = c x * c y)
    (hc1 : c 1 = 1) (hcinv : ∀ x, c x⁻¹ = (c x)⁻¹) : Subgroup G where
  carrier := {x | c x = 1}
  mul_mem' := fun {a b} ha hb => by
    show c (a * b) = 1
    rw [hcmul, Set.mem_setOf_eq.mp ha, Set.mem_setOf_eq.mp hb, one_mul]
  one_mem' := hc1
  inv_mem' := fun {a} ha => by
    show c a⁻¹ = 1
    rw [hcinv, Set.mem_setOf_eq.mp ha, inv_one]

theorem nine_ne_zero_of_three_ne {F : Type} [Field F] (h3 : (3 : F) ≠ 0) :
    ((9 : ℕ) : F) ≠ 0 := by
  intro h
  apply h3
  have h33 : (3 : F) * 3 = 0 := by
    have e : (3 : F) * 3 = ((9 : ℕ) : F) := by norm_num
    rw [e]
    exact h
  exact (mul_eq_zero.mp h33).elim id id

theorem conj_projE {K : Type} [Field K] {P : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K)}
    (AK : Matrix.GeneralLinearGroup (Fin 7) K) (T : Finset P) :
    (AK : Matrix (Fin 7) (Fin 7) K) * projE T * ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K) =
      ((T.card : K))⁻¹ • ∑ x ∈ T, ((conjSL7 AK (x : Matrix.SpecialLinearGroup (Fin 7) K) :
        Matrix.SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
  unfold projE
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1

theorem conj_mul_conj {K : Type} [Field K] (A : Matrix.GeneralLinearGroup (Fin 7) K)
    (x y : Matrix (Fin 7) (Fin 7) K) :
    ((A : Matrix (Fin 7) (Fin 7) K) * x * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) :
      Matrix (Fin 7) (Fin 7) K)) *
      ((A : Matrix (Fin 7) (Fin 7) K) * y * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) :
        Matrix (Fin 7) (Fin 7) K)) =
      (A : Matrix (Fin 7) (Fin 7) K) * (x * y) * ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) :
        Matrix (Fin 7) (Fin 7) K) := by
  have hinv : ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *
      (A : Matrix (Fin 7) (Fin 7) K) = 1 := Units.inv_mul A
  calc _ = (A : Matrix (Fin 7) (Fin 7) K) * x * (((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) :
        Matrix (Fin 7) (Fin 7) K) * (A : Matrix (Fin 7) (Fin 7) K)) * y *
        ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [hinv, Matrix.mul_one]
        simp only [Matrix.mul_assoc]

theorem kerConcl_PSL7 [Finite K] (hnr : ∀ x : K, x ^ 2 + x + 1 ≠ 0)
    {E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 7) K)}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hc : Nat.card E = 27) :
    CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.KerConcl E := by
  obtain ⟨P, hPE, hcomm, hpow, hPcard⟩ := lift_of_elemAbelian7 hE hc
  haveI hirr : Fact (Irreducible (quad K)) := ⟨quad_irreducible hnr⟩
  have hζ : IsPrimitiveRoot (zetaQ K) 3 := prim_root_quad hnr
  have hmonic : (quad K).Monic := by
    unfold quad
    monicity!
  haveI : Module.Finite K (AdjoinRoot (quad K)) := Polynomial.Monic.finite_adjoinRoot hmonic
  haveI : Finite (AdjoinRoot (quad K)) := Module.finite_of_finite K
  haveI : Finite (Matrix.SpecialLinearGroup (Fin 7) K) := inferInstance
  haveI : Fintype P := Fintype.ofFinite P
  obtain ⟨A, hoff, hmul, hpowd, hsymmD, hfaith⟩ :=
    diag_eigen hζ (sigmaQuad K) (sigmaQuad_zeta K) (sigmaQuad_sigmaQuad K) P hcomm hpow
  have hPcardF : Fintype.card P = 27 := by
    rw [← Nat.card_eq_fintype_card]
    exact hPcard
  obtain ⟨c, hcmul, hcpow, hcnt, hker9, hcount⟩ :=
    exists_good_char hζ (d := fun i (x : P) => Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i)
      hmul hpowd hsymmD hfaith hPcardF
  have hcount' : (univ.filter fun i => ∀ x : P, c x = 1 →
      Dm A (x : Matrix.SpecialLinearGroup (Fin 7) K) i i = 1).card = 3 := hcount
  have hc1 : c 1 = 1 := char_one hcmul hcpow
  have hcinv : ∀ x, c x⁻¹ = (c x)⁻¹ := fun x => by
    have h := hcmul x⁻¹ x
    rw [inv_mul_cancel, hc1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have h3K : (3 : K) ≠ 0 := fun h => hnr 1 (by linear_combination h)
  have h9K : ((univ.filter fun x : P => c x = 1).card : K) ≠ 0 := by
    rw [hker9]
    exact nine_ne_zero_of_three_ne h3K
  have hidem := projE_mul_self (P := P) c hcmul hcpow h9K
  have hL9 : ((9 : ℕ) : AdjoinRoot (quad K)) ≠ 0 :=
    nine_ne_zero_of_three_ne (three_ne_zero_quad hnr)
  have hrankL := rank_projE_map A hoff c hcmul hcpow hker9 hL9
  have hrankK : (projE (univ.filter fun x : P => c x = 1)).rank = 3 := by
    rw [← rank_map_field (algebraMap K (AdjoinRoot (quad K)))]
    rw [hrankL, hcount']
  obtain ⟨AK, hAK⟩ := exists_idem_normal _ hidem hrankK
  have hDg : (AK : Matrix (Fin 7) (Fin 7) K) * projE (univ.filter fun x : P => c x = 1) *
      ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = Dg K := hAK
  have hDsum : Dg K = ((9 : K))⁻¹ • ∑ x ∈ univ.filter (fun x : P => c x = 1),
      ((conjSL7 AK (x : Matrix.SpecialLinearGroup (Fin 7) K) :
        Matrix.SpecialLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) := by
    rw [← hDg, conj_projE, hker9]
    norm_num
  let Fsub : Subgroup P := kerSub c hcmul hc1 hcinv
  have hFsub_card : Nat.card Fsub = 9 := by
    have e1 : Nat.card Fsub = Nat.card {x : P // c x = 1} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
    rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hker9]
  let F0 : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K) := Fsub.map P.subtype
  let F' : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K) := F0.map (conjSL7 AK).toMonoidHom
  let P' : Subgroup (Matrix.SpecialLinearGroup (Fin 7) K) := P.map (conjSL7 AK).toMonoidHom
  have hF0card : Nat.card F0 = 9 := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective P), hFsub_card]
  have hF'card : Nat.card F' = 9 := by
    rw [Subgroup.card_map_of_injective (conjSL7 AK).injective, hF0card]
  have hF0P : F0 ≤ P := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  have hF'P : F' ≤ P' := Subgroup.map_mono hF0P
  have hP3 : ∀ x ∈ P', x ^ 3 = 1 := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hpow y hy, map_one]
  have hF'D : ∀ f ∈ F', (f : Matrix (Fin 7) (Fin 7) K) * Dg K = Dg K ∧
      Dg K * (f : Matrix (Fin 7) (Fin 7) K) = Dg K := by
    intro f hf
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hf
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hz1 : c z = 1 := hz
    rw [← hDg]
    constructor
    · show ((AK : Matrix (Fin 7) (Fin 7) K) * (z : Matrix (Fin 7) (Fin 7) K) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
          ((AK : Matrix (Fin 7) (Fin 7) K) * projE (univ.filter fun x : P => c x = 1) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) =
          (AK : Matrix (Fin 7) (Fin 7) K) * projE (univ.filter fun x : P => c x = 1) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
      rw [conj_mul_conj, projE_left c hcmul hcpow hz1]
    · show ((AK : Matrix (Fin 7) (Fin 7) K) * projE (univ.filter fun x : P => c x = 1) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) *
          ((AK : Matrix (Fin 7) (Fin 7) K) * (z : Matrix (Fin 7) (Fin 7) K) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)) =
          (AK : Matrix (Fin 7) (Fin 7) K) * projE (univ.filter fun x : P => c x = 1) *
          ((AK⁻¹ : Matrix.GeneralLinearGroup (Fin 7) K) : Matrix (Fin 7) (Fin 7) K)
      rw [conj_mul_conj, projE_right c hcmul hcpow hz1]
  have hcent : ∀ g : Matrix.SpecialLinearGroup (Fin 7) K, (∀ f ∈ F', g * f = f * g) →
      (g : Matrix (Fin 7) (Fin 7) K) * Dg K = Dg K * (g : Matrix (Fin 7) (Fin 7) K) := by
    intro g hg
    rw [hDsum, Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    have hcx : c x = 1 := (Finset.mem_filter.mp hx).2
    have hmem : conjSL7 AK (x : Matrix.SpecialLinearGroup (Fin 7) K) ∈ F' :=
      Subgroup.mem_map.mpr ⟨(x : Matrix.SpecialLinearGroup (Fin 7) K),
        Subgroup.mem_map.mpr ⟨x, (show c x = 1 from hcx), rfl⟩, rfl⟩
    have hgc := congrArg (fun y : Matrix.SpecialLinearGroup (Fin 7) K =>
      (y : Matrix (Fin 7) (Fin 7) K)) (hg _ hmem)
    simpa [Matrix.SpecialLinearGroup.coe_mul] using hgc
  have hEP : E.map (conjPSL7 AK).toMonoidHom = P'.map (piSL7 K) := by
    rw [← hPE, Subgroup.map_map, Subgroup.map_map]
    congr 1
  refine CFSG.LocalAnalysis.GLTheoremA.KD264LieA4.kerConcl_of_equiv (conjPSL7 AK) E ?_
  rw [hEP]
  exact kerConcl_of_block P' hP3 F' hF'P hF'card hF'D hcent

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KA7

end

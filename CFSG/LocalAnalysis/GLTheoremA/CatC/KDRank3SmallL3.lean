module

public import CFSG.Adapters.LinearCatalog
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Matrix
open CFSG.Open

namespace KDRank3SmallL3

section Unipotent

variable {K : Type} [Field K]

@[expose] def uni (a b : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, a; 0, 1, b; 0, 0, 1]

theorem uni_mul (a b a' b' : K) : uni a b * uni a' b' = uni (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uni_det (a b : K) : (uni a b).det = 1 := by
  simp [uni, Matrix.det_fin_three]

@[expose] def uniSL (a b : K) : Matrix.SpecialLinearGroup (Fin 3) K := ⟨uni a b, uni_det a b⟩

theorem uniSL_mul (a b a' b' : K) : uniSL a b * uniSL a' b' = uniSL (a + a') (b + b') :=
  Subtype.ext (uni_mul a b a' b')

theorem uniSL_zero : uniSL (0 : K) 0 = 1 :=
  Subtype.ext (by
    show uni (0 : K) 0 = 1
    unfold uni
    rw [Matrix.one_fin_three])

@[expose] def uniHom : Multiplicative (K × K) →* Matrix.SpecialLinearGroup (Fin 3) K where
  toFun x := uniSL (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2
  map_one' := by simpa using uniSL_zero
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    rw [uniSL_mul]

theorem eq_zero_of_mem_center {a b : K}
    (h : uniSL a b ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) :
    a = 0 ∧ b = 0 := by
  have hc := Subgroup.mem_center_iff.1 h
  let e₁ : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩
  let e₂ : Matrix.SpecialLinearGroup (Fin 3) K :=
    ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by simp [Matrix.det_fin_three]⟩
  have h1 : ((e₁ : Matrix (Fin 3) (Fin 3) K) * uni a b) 0 2
      = (uni a b * (e₁ : Matrix (Fin 3) (Fin 3) K)) 0 2 :=
    congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 2)
      (hc e₁)
  have h2 : ((e₂ : Matrix (Fin 3) (Fin 3) K) * uni a b) 0 1
      = (uni a b * (e₂ : Matrix (Fin 3) (Fin 3) K)) 0 1 :=
    congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1)
      (hc e₂)
  simp [e₁, e₂, uni, Matrix.mul_apply, Fin.sum_univ_three] at h1 h2
  refine ⟨?_, ?_⟩ <;> first | exact h2.symm | exact h2 | exact h1.symm | exact h1

theorem uniHom_injective_mod_center :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 3) K))).comp (uniHom (K := K))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : uniHom x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    (QuotientGroup.eq_one_iff _).1 hx
  have hx' : uniSL (Multiplicative.toAdd x).1 (Multiplicative.toAdd x).2 ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := hmem
  obtain ⟨h1, h2⟩ := eq_zero_of_mem_center hx'
  apply Multiplicative.toAdd.injective
  exact Prod.ext h1 h2

end Unipotent

theorem isElemAbelian_three_range {A G : Type} [CommGroup A] [Group G] (f : A →* G)
    (hexp : ∀ a : A, a ^ 3 = 1) : IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · rcases x with ⟨x, a, rfl⟩
    rcases y with ⟨y, b, rfl⟩
    apply Subtype.ext
    show f a * f b = f b * f a
    rw [← map_mul, ← map_mul, mul_comm]
  · obtain ⟨a, rfl⟩ := hx
    rw [← map_pow, hexp, map_one]

theorem card_range_eq {A G : Type} [Group A] [Group G] (f : A →* G)
    (hf : Function.Injective f) : Nat.card f.range = Nat.card A :=
  (Nat.card_congr (Equiv.ofInjective f hf)).symm

section Field

variable {K : Type} [Field K] [Finite K] [CharP K 3]

theorem exists_pow_six_of_field (hK : Nat.card K = 27) :
    ∃ P : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K),
      IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  let Θ : Multiplicative (K × K) →* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))).comp uniHom
  have hΘ : Function.Injective Θ := uniHom_injective_mod_center
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hexp : ∀ a : Multiplicative (K × K), a ^ 3 = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    ext
    · simp [toAdd_pow, h3]
    · simp [toAdd_pow, h3]
  refine ⟨Θ.range, isElemAbelian_three_range Θ hexp, ?_⟩
  rw [card_range_eq Θ hΘ,
    (Nat.card_congr (Multiplicative.ofAdd : K × K ≃ Multiplicative (K × K))).symm,
    Nat.card_prod, hK]
  norm_num

end Field

theorem prime_eq_three_of_card_eq_27 (q : TauCeti.PrimePower) (hq : q.card = 27) : q.p = 3 := by
  have hcard : q.p ^ q.exponent = 3 ^ 3 := by
    rw [← TauCeti.PrimePower.card_def, hq]
    norm_num
  have hdvd : q.p ∣ 3 := by
    have : q.p ∣ 3 ^ 3 := by
      rw [← hcard]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact q.prime_p.dvd_of_dvd_pow this
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd

theorem exists_six_of_A2 {S : Type} [Group S] (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (hq : q.card = 27)
    (e : S ≃* (TauCeti.ValidLieTypeIndex.Group ⟨TauCeti.LieTypeIndex.A 2 q, hv⟩)) :
    ∃ P : Subgroup S, IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 6 := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp3 : q.p = 3 := prime_eq_three_of_card_eq_27 q hq
  haveI : CharP (GaloisField q.p q.exponent) 3 := by
    rw [← hp3]
    infer_instance
  have hK : Nat.card (GaloisField q.p q.exponent) = 27 := by
    rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', ← TauCeti.PrimePower.card_def, hq]
  obtain ⟨P₀, hP₀, hcard⟩ := exists_pow_six_of_field (K := GaloisField q.p q.exponent) hK
  let e' : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField q.p q.exponent) :=
    e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
  refine ⟨P₀.map e'.symm.toMonoidHom, ?_, ?_⟩
  · exact CFSG.SectionRank.isElemAbelian_map hP₀ e'.symm.toMonoidHom
  · rw [Subgroup.card_map_of_injective e'.symm.injective]
    exact hcard

end KDRank3SmallL3

end CFSG.LocalAnalysis.GLTheoremA

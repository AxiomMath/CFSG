module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsUniBound
public import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.Open.StatedDefs
public import CFSG.Open.MatrixModelCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Matrix CFSG.RankThree.PartOne.LIT CFSG.Open

variable {K : Type} [Field K]

theorem frob_add_pow {p f : ℕ} [CharP K p] [Fact p.Prime] (x y : K) :
    (x + y) ^ (p ^ f) = x ^ (p ^ f) + y ^ (p ^ f) :=
  add_pow_char_pow x y p f

@[expose] def stdSesqForm (ι : Type) [Fintype ι] {p f : ℕ} [CharP K p] [Fact p.Prime] :
    SesqForm K (p ^ f) (ι → K) where
  h v w := ∑ i, v i ^ (p ^ f) * w i
  add_left v v' w := by
    simp only [Pi.add_apply, frob_add_pow (p := p) (f := f), add_mul, Finset.sum_add_distrib]
  smul_left a v w := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum, mul_assoc]
  add_right v w w' := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right a v w := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]
  nondeg v hv := by
    classical
    funext j
    have h := hv (Pi.single j 1)
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    show v j = 0
    exact (pow_eq_zero_iff (pow_ne_zero f (Fact.out : Nat.Prime p).ne_zero)).mp h

theorem stdSesqForm_h {ι : Type} [Fintype ι] {p f : ℕ} [CharP K p] [Fact p.Prime]
    (v w : ι → K) : (stdSesqForm ι (K := K) (p := p) (f := f)).h v w =
      (fun i => v i ^ (p ^ f)) ⬝ᵥ w := rfl

theorem stdSesqForm_preserved {m : ℕ} {p f : ℕ} [CharP K p] [Fact p.Prime]
    (A : Matrix (Fin m) (Fin m) K) (hA : (A.map (· ^ (p ^ f)))ᵀ * A = 1) (v w : Fin m → K) :
    (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).h (A *ᵥ v) (A *ᵥ w) =
      (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).h v w := by
  rw [stdSesqForm_h, stdSesqForm_h]
  have hfrob : (fun i => (A *ᵥ v) i ^ (p ^ f)) = (A.map (· ^ (p ^ f))) *ᵥ (fun i => v i ^ (p ^ f)) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [sum_pow_char_pow]
    simp only [mul_pow]
  rw [hfrob, ← Matrix.vecMul_transpose (A.map (· ^ (p ^ f))) (fun i => v i ^ (p ^ f)),
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hA, Matrix.one_mulVec]

theorem statedSU_preserves {m p f : ℕ} [CharP K p] [Fact p.Prime] {g : GL (Fin m) K}
    (hg : g ∈ StatedSU m (p ^ f) K) (v w : Fin m → K) :
    (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).h ((g : Matrix (Fin m) (Fin m) K) *ᵥ v)
      ((g : Matrix (Fin m) (Fin m) K) *ᵥ w) =
      (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).h v w := by
  unfold StatedSU at hg
  induction hg using Subgroup.closure_induction generalizing v w with
  | mem x hx => exact stdSesqForm_preserved (K := K) (p := p) (f := f) _ hx.2 v w
  | one => simp
  | mul x y _ _ hx hy =>
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    rw [hx (↑y *ᵥ v) (↑y *ᵥ w), hy v w]
  | inv x _ hx =>
    have key := hx (((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v)
      (((x⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ w)
    simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at key
    exact key.symm

theorem statedSU_card_le {m p f : ℕ} [CharP K p] [Fact p.Prime] (h3 : (3 : K) ≠ 0)
    (hq : ∀ c : K, c ^ 3 = 1 → c ^ (p ^ f + 1) = 1 → c = 1)
    (E : Subgroup (GL (Fin m) K)) [Finite E] (hE : E ≤ StatedSU m (p ^ f) K)
    (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g) (hexp : ∀ g ∈ E, g ^ 3 = 1) :
    Nat.card E ≤ 3 ^ (m / 2) := by
  have hfin : Finite (E.map (glAut (Fin m) K)) :=
    Finite.of_equiv E (E.equivMapOfInjective (glAut (Fin m) K) glAut_injective).toEquiv
  have h := card_le_pow_half_of_sesq (K := K) h3 hq m (Fin m → K)
    (stdSesqForm (Fin m) (K := K) (p := p) (f := f))
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]) (E.map (glAut (Fin m) K))
    (map_glAut_comm hcomm) (map_glAut_exp hexp) (by
      rintro _ ⟨g, hg, rfl⟩ v w
      rw [glAut_apply, glAut_apply]
      exact statedSU_preserves (hE hg) v w)
  rwa [card_map_glAut] at h

theorem not_dvd_card_statedScalars {m p f : ℕ} [Finite K] [CharP K p] [Fact p.Prime]
    (hq : ∀ c : K, c ^ 3 = 1 → c ^ (p ^ f + 1) = 1 → c = 1) :
    ¬ 3 ∣ Nat.card ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K)) := by
  intro h
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K)) :=
    Fintype.ofFinite _
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 (by rwa [Nat.card_eq_fintype_card] at h)
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hz
    norm_num at hz
  have hzS : ((z : StatedSU m (p ^ f) K) : GL (Fin m) K) ∈ StatedScalars (Fin m) K :=
    (Subgroup.mem_subgroupOf).mp z.2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hzS
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact hz1 (Subtype.ext (Subtype.ext (Subsingleton.elim _ _)))
  · have hzH : ((z : StatedSU m (p ^ f) K) : GL (Fin m) K) ∈ StatedSU m (p ^ f) K :=
      (z : StatedSU m (p ^ f) K).2
    have h3GL : ((z : StatedSU m (p ^ f) K) : GL (Fin m) K) ^ 3 = 1 := by
      have h' := congrArg (fun g : (StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K) =>
        ((g : StatedSU m (p ^ f) K) : GL (Fin m) K)) hz3
      simpa using h'
    have hc3' : Matrix.GeneralLinearGroup.scalar (Fin m) (c ^ 3) = 1 := by
      rw [map_pow, hc, h3GL]
    have hc3 : c ^ 3 = 1 := by
      have h' := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) ⟨0, hm⟩ ⟨0, hm⟩)
        hc3'
      simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
        Units.val_one, Matrix.one_apply_eq] at h'
      apply Units.ext
      simpa using h'
    set v : Fin m → K := Pi.single ⟨0, hm⟩ 1 with hv
    have hself : (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).h v v = 1 := by
      simp [hv, stdSesqForm_h, Pi.single_apply]
    have hsv : ∀ (a : K) (w : Fin m → K), (Matrix.scalar (Fin m) a) *ᵥ w = a • w := by
      intro a w
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hsc : (c : K) ^ (p ^ f + 1) = 1 := by
      have key := statedSU_preserves (K := K) (p := p) (f := f) hzH v v
      rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, hsv,
        (stdSesqForm (Fin m) (K := K) (p := p) (f := f)).smul_smul_self, hself, mul_one] at key
      exact key
    have hc3K : (c : K) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    have hcK : (c : K) = 1 := hq c hc3K hsc
    have hcu : c = 1 := Units.ext (by simpa using hcK)
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, hcu]
    simp

theorem statedProj_pRank_le [Finite K] {m p f : ℕ} [CharP K p] [Fact p.Prime] (h3 : (3 : K) ≠ 0)
    (hq : ∀ c : K, c ^ 3 = 1 → c ^ (p ^ f + 1) = 1 → c = 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU m (p ^ f) K))) ≤ m / 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [CFSG.SectionRank.pRank_quotient_eq
    ((StatedScalars (Fin m) K).subgroupOf (StatedSU m (p ^ f) K))
    (not_dvd_card_statedScalars (m := m) hq)]
  refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt fun E _ hE => ?_
  have hEH : E.map (StatedSU m (p ^ f) K).subtype ≤ StatedSU m (p ^ f) K := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hcomm' : ∀ g ∈ E.map (StatedSU m (p ^ f) K).subtype,
      ∀ h ∈ E.map (StatedSU m (p ^ f) K).subtype, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  have hexp' : ∀ g ∈ E.map (StatedSU m (p ^ f) K).subtype, g ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE.2 a ha, map_one]
  have hcard : Nat.card (E.map (StatedSU m (p ^ f) K).subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hb := statedSU_card_le h3 hq (E.map (StatedSU m (p ^ f) K).subtype) hEH hcomm' hexp'
  rwa [hcard] at hb

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

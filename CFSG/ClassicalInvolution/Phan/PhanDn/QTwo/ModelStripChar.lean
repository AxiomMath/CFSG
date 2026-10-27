module

public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.ModelParabSwap
public import CFSG.ClassicalInvolution.Phan.PhanDn.QTwo.StdFamilyFaithful

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Unitary
open Matrix

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {σ : K ≃+* K}

theorem prod_eq_one_of_suEndN_apply_single {n : ℕ} (s : SUid σ n)
    (τ : Fin n → normOne σ)
    (h : ∀ c : Fin n, suEndN (F := F) σ n s (Pi.single c 1) =
      (((τ c : normOne σ) : Kˣ) : K) • Pi.single c 1) :
    ∏ c, τ c = 1 := by
  have hmat : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal (fun c => (((τ c : normOne σ) : Kˣ) : K)) := by
    ext i j
    have hc := congrFun (h j) i
    rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
      Matrix.mulVec_single_one, Matrix.col_apply] at hc
    by_cases hij : i = j
    · subst hij
      simpa using hc
    · have hsingle : (Pi.single j (1 : K) : Fin n → K) i = 0 :=
        Pi.single_eq_of_ne hij 1
      rw [Pi.smul_apply, hsingle, smul_eq_mul, mul_zero] at hc
      rw [hc, Matrix.diagonal_apply_ne _ hij]
  have hdet : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := s.2.1
  rw [hmat, Matrix.det_diagonal] at hdet
  apply Subtype.ext
  apply Units.ext
  have hcoe1 : ((∏ c, τ c : normOne σ) : Kˣ) =
      ∏ c, ((τ c : normOne σ) : Kˣ) :=
    map_prod (normOne σ).subtype τ Finset.univ
  have hcoe2 : ((∏ c, ((τ c : normOne σ) : Kˣ) : Kˣ) : K) =
      ∏ c, (((τ c : normOne σ) : Kˣ) : K) :=
    map_prod (Units.coeHom K) (fun c => ((τ c : normOne σ) : Kˣ)) Finset.univ
  have hcoe : (((∏ c, τ c : normOne σ) : Kˣ) : K) = 1 := by
    rw [hcoe1, hcoe2]
    exact hdet
  simpa using hcoe

end CFSG.ClassicalInvolution.PhanDn

namespace CFSG.ClassicalInvolution.PhanDn.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.StandardType.QTwo

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
variable (E : QuadExt F K (unitaryInvolution K 2 1))

private theorem qTwoStdFamily_exists_suEndN_of_last_not_mem
    (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))} (hC : Fin.last m ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hx : x ∈ (qTwoStdFamily E hK m hm).levi C) :
    ∃ s : SUid (unitaryInvolution K 2 1) (m + 1),
      (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
        suEndN (F := F) (unitaryInvolution K 2 1) (m + 1) s := by
  classical
  let σ := unitaryInvolution K 2 1
  let H : Subgroup ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))) :=
    (suEndN (F := F) σ (m + 1)).range.comap
      (Subgroup.subtype (CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1))))
  have hle : (qTwoStdFamily E hK m hm).levi C ≤ H := by
    refine QTwoPhanFamily.levi_le_of_forall_lt (qTwoStdFamily E hK m hm) ?_ ?_
    · intro i hi
      rcases Fin.eq_castSucc_or_eq_last (n := m) i with ⟨k, rfl⟩ | rfl
      · rintro _ ⟨a, rfl⟩
        refine Subgroup.mem_comap.mpr ⟨blockEmb2 K 2 1 m k a, ?_⟩
        change suEndN (F := F) σ (m + 1) (blockEmb2 K 2 1 m k a) =
          ((qTwoStdIota E m hm (Fin.castSucc k)) a :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        rw [coe_qTwoStdIota_castSucc]
      · exact absurd hi hC
    · intro i hi j hj hij h3
      rcases Fin.eq_castSucc_or_eq_last (n := m) j with ⟨j', rfl⟩ | rfl
      · rintro _ ⟨b, rfl⟩
        have hij' : i.val + 1 = j'.val := by
          rw [Fin.lt_def, Fin.val_castSucc] at hij
          have h := (qtwoLabel_three_iff hm i (Fin.castSucc j')).mp h3
          rw [Fin.val_castSucc] at h
          rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · omega
          · omega
          · omega
          · omega
        refine Subgroup.mem_comap.mpr
          ⟨blockEmb3 K 2 1 m ⟨i.val, by have := j'.2; omega⟩
              (by have := j'.2; change i.val + 1 < m; omega) b, ?_⟩
        change suEndN (F := F) σ (m + 1)
            (blockEmb3 K 2 1 m ⟨i.val, by have := j'.2; omega⟩
              (by have := j'.2; change i.val + 1 < m; omega) b) =
          ((qTwoStdTheta E m hm i (Fin.castSucc j')) b :
            (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
        rw [coe_qTwoStdTheta_chain E m hm hij' b]
      · exact absurd hj hC
  have hxH : x ∈ H := hle hx
  rw [Subgroup.mem_comap] at hxH
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hxH
  exact ⟨s, by simpa using hs.symm⟩

theorem prod_ite_le_eq_one_of_mem_qTwoStdFamily_levi (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))}
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hxL : x ∈ (qTwoStdFamily E hK m hm).levi C)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 1)}
    (hx : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F (unitaryInvolution K 2 1) (m + 1) t)
    {k : Fin (m + 1)} (hk : k ∉ C) (hk2 : k.val + 2 ≤ m) :
    ∏ c, (if c.val ≤ k.val then t c else 1) = 1 := by
  classical
  let σ := unitaryInvolution K 2 1
  let C₁ : Set (Fin (m + 1)) := {i | i ∈ C ∧ i.val < k.val}
  let C₂ : Set (Fin (m + 1)) := {i | i ∈ C ∧ k.val < i.val}
  have hCeq : C = C₁ ∪ C₂ := by
    ext i
    constructor
    · intro hi
      by_cases hik : i.val < k.val
      · exact Or.inl ⟨hi, hik⟩
      · have hki : k.val < i.val := by
          have hne : i.val ≠ k.val := by
            intro h
            exact hk (Fin.ext h ▸ hi)
          omega
        exact Or.inr ⟨hi, hki⟩
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩)
      · exact hi
      · exact hi
  have hcross : ∀ i ∈ C₁, ∀ j ∈ C₂,
      CFSG.StandardType.ggCoxeterMatrixD (m + 1) i j = 2 := by
    intro i hi j hj
    have hik : i.val < k.val := hi.2
    have hkj : k.val < j.val := hj.2
    have hij : i ≠ j := by
      intro h
      rw [h] at hik
      omega
    rw [qtwoLabel_two_iff hm i j hij]
    intro hedge
    rcases hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
    · omega
    · omega
  have hxUnion : x ∈ (qTwoStdFamily E hK m hm).levi (C₁ ∪ C₂) := by
    rw [← hCeq]
    exact hxL
  obtain ⟨a, ha, b, hb, hab⟩ :=
    QTwoPhanFamily.exists_mul_of_mem_levi_union (qTwoStdFamily E hK m hm) hcross hxUnion
  have hlast₁ : Fin.last m ∉ C₁ := by
    intro hmem
    have hlt := hmem.2
    simp only [Fin.val_last] at hlt
    omega
  obtain ⟨s, hs⟩ :=
    qTwoStdFamily_exists_suEndN_of_last_not_mem (E := E) hK hm hlast₁ ha
  let τ : Fin (m + 1) → normOne σ := fun c => if c.val ≤ k.val then t c else 1
  have haction : ∀ c : Fin (m + 1),
      suEndN (F := F) σ (m + 1) s (Pi.single c 1) =
        (((τ c : normOne σ) : Kˣ) : K) • Pi.single c 1 := by
    intro c
    by_cases hc : c.val ≤ k.val
    · have hbfix : (b : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) = Pi.single c 1 :=
        qTwoStdFamily_levi_single_of_gt (E := E) hK hm hk2
          (C := C₂) (fun i hi => hi.2) hc hb
      have hxe : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) =
          (a : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) (Pi.single c 1) := by
        rw [← hab, Subgroup.coe_mul, LinearEquiv.mul_apply, hbfix]
      have hxt : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) =
          (((t c : normOne σ) : Kˣ) : K) • Pi.single c 1 := by
        rw [hx, diagHom_single]
      have hae : (a : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) =
          (((t c : normOne σ) : Kˣ) : K) • Pi.single c 1 := by
        rw [← hxe, hxt]
      rw [← hs]
      change (a : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) =
        (((if c.val ≤ k.val then t c else 1 : normOne σ) : Kˣ) : K) •
          Pi.single c 1
      rw [if_pos hc]
      exact hae
    · have hkc : k.val < c.val := Nat.lt_of_not_ge hc
      have hafix : (a : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))
          (Pi.single c 1) = Pi.single c 1 :=
        qTwoStdFamily_levi_single_of_lt (E := E) hK hm
          (C := C₁) (fun i hi => hi.2) hkc ha
      have hτ : τ c = 1 := by
        simp only [τ]
        rw [if_neg hc]
      rw [← hs, hafix, hτ]
      simp
  have hprod := prod_eq_one_of_suEndN_apply_single (F := F) s τ haction
  simpa [τ] using hprod

theorem prod_eq_one_of_mem_qTwoStdFamily_levi (hK : Nat.card K = 4) {m : ℕ} (hm : 3 ≤ m)
    {C : Set (Fin (m + 1))} (hC : Fin.last m ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hxL : x ∈ (qTwoStdFamily E hK m hm).levi C)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 1)}
    (hx : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F (unitaryInvolution K 2 1) (m + 1) t) :
    ∏ c, t c = 1 := by
  obtain ⟨s, hs⟩ :=
    qTwoStdFamily_exists_suEndN_of_last_not_mem (E := E) hK hm hC hxL
  refine prod_eq_one_of_suEndN_apply_single (F := F) s t ?_
  intro c
  rw [← hs, hx, diagHom_single]

theorem prod_update_last_eq_one_of_mem_qTwoStdFamily_levi (hK : Nat.card K = 4) {m : ℕ}
    (hm : 3 ≤ m) {C : Set (Fin (m + 1))} (hC : (⟨m - 1, by omega⟩ : Fin (m + 1)) ∉ C)
    {x : ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))}
    (hxL : x ∈ (qTwoStdFamily E hK m hm).levi C)
    {t : Fin (m + 1) → normOne (unitaryInvolution K 2 1)}
    (hx : (x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F (unitaryInvolution K 2 1) (m + 1) t) :
    ∏ c, Function.update t (Fin.last m) (t (Fin.last m))⁻¹ c = 1 := by
  let σ := unitaryInvolution K 2 1
  let s := qTwoForkSwap m hm
  have hlast' : Fin.last m ∉ s '' C := by
    rintro ⟨i, hi, hsi⟩
    have hpen : i = (⟨m - 1, by omega⟩ : Fin (m + 1)) := by
      calc
        i = s (s i) := (qTwoForkSwap_apply_apply m hm i).symm
        _ = s (Fin.last m) := by rw [hsi]
        _ = (⟨m - 1, by omega⟩ : Fin (m + 1)) := qTwoForkSwap_apply_last m hm
    exact hC (hpen ▸ hi)
  have hmem : conjTau E x ∈ (qTwoStdFamily E hK m hm).levi (s '' C) := by
    have h := Subgroup.mem_map_of_mem (conjTau E).toMonoidHom hxL
    rwa [map_qTwoLevi_conjTau E hK m hm C] at h
  let t' : Fin (m + 1) → normOne σ :=
    Function.update t (Fin.last m) ((t (Fin.last m))⁻¹)
  have hxval : (conjTau E x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K)) =
      diagHom F σ (m + 1) t' := by
    rw [coe_conjTau]
    change (stdConj E m).toMonoidHom
        ((x : (Fin (m + 1) → K) ≃ₗ[F] (Fin (m + 1) → K))) =
      diagHom F σ (m + 1) t'
    rw [hx, stdConj_diagHom]
  exact prod_eq_one_of_mem_qTwoStdFamily_levi (E := E) hK hm hlast' hmem hxval

end CFSG.ClassicalInvolution.PhanDn.QTwo

end

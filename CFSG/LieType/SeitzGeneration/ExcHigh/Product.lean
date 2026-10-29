module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.Open

section SL2

theorem natCast_ne_zero_of_not_dvd_card {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) : (p : K) ≠ 0 := by
  classical
  intro h0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hd : ringChar K ∣ p := ringChar.dvd h0
  have hℓp : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hℓ hp).1 hd
  exact hpK (by rw [hK, ← hℓp]; exact dvd_pow_self _ n.ne_zero)

variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime]

theorem card_le_of_isElemAbelian_specialLinear_two (hpK : (p : K) ≠ 0)
    {F : Subgroup SL(2, K)} [Finite F] (hF : IsElemAbelian p F) : Nat.card F ≤ p := by
  classical
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  let φ : SL(2, K) →* GL (Fin 2) (AlgebraicClosure K) :=
    (Matrix.GeneralLinearGroup.map (algebraMap K (AlgebraicClosure K))).comp
      Matrix.SpecialLinearGroup.toGL
  have hφi : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    have h := congrArg (fun z : GL (Fin 2) (AlgebraicClosure K) =>
      (z : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K))) hxy
    simp only [φ, MonoidHom.comp_apply] at h
    exact Matrix.map_injective (algebraMap K (AlgebraicClosure K)).injective h
  have hcomm : ∀ x ∈ F.map φ, ∀ y ∈ F.map φ, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hF.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hexp : ∀ x ∈ F.map φ, x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hF.2 a ha, map_one]
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartOne.CTP.exists_conj_diagonal_of_exponent_prime
    ⟨ζ, hζ⟩ (F.map φ) hcomm hexp
  have hd : ∀ x : F, ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
      Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 0 1 = 0 ∧
      ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 1 0 = 0 :=
    fun x => ⟨hg _ ⟨x, x.2, rfl⟩ 0 1 (by decide), hg _ ⟨x, x.2, rfl⟩ 1 0 (by decide)⟩
  let lam : F →* AlgebraicClosure K :=
    { toFun := fun x => ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 0 0
      map_one' := by simp
      map_mul' := fun x y => by
        have e : (g * φ ((x * y : F) : SL(2, K)) * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) =
            (g * φ x * g⁻¹) * (g * φ y * g⁻¹) := by
          simp only [Subgroup.coe_mul, map_mul]
          group
        rw [e, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (hd x).1, zero_mul, add_zero] }
  have hlam : Function.Injective lam := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h00 : ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 0 0 = 1 := hx
    have hdet0 : ((φ x : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)).det = 1 := by
      have h1 : ((φ x : GL (Fin 2) (AlgebraicClosure K)) :
          Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) =
          ((x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).map (algebraMap K (AlgebraicClosure K)) :=
        rfl
      rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe,
        map_one]
    have hdet : ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)).det = 1 := by
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdet0, mul_one,
        ← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have h11 : ((g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) :
        Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) 1 1 = 1 := by
      rw [Matrix.det_fin_two, (hd x).1, (hd x).2, h00] at hdet
      simpa using hdet
    have hM : (g * φ x * g⁻¹ : GL (Fin 2) (AlgebraicClosure K)) = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h00, h11, (hd x).1, (hd x).2]
    have : φ x = 1 := by
      have := congrArg (fun z => g⁻¹ * z * g) hM
      simpa [mul_assoc] using this
    exact Subtype.ext (hφi (this.trans (map_one φ).symm))
  haveI : Finite F := inferInstance
  have hcyc : IsCyclic F := isCyclic_of_injective_ringHom lam hlam
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  have hord : orderOf c = Nat.card F := orderOf_eq_card_of_forall_mem_zpowers hc
  have hdvd : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hF.2 c c.2))
  rw [← hord]
  exact Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd

end SL2

section Prod

variable {A B : Type*} [Group A] [Group B] {p : ℕ} [Fact p.Prime]

theorem closure_centralizers_prod_of_plane
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p)
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {b : B | ∃ x ∈ F, x ≠ 1 ∧ Commute b x} = ⊤)
    (F : Subgroup (A × B)) (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {h : A × B | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤ := by
  classical
  set S : Set (A × B) := {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} with hS
  have h1 : ∃ y ∈ F, y ≠ 1 ∧ y.1 = 1 := by
    by_contra hcon
    push Not at hcon
    have hdis : Disjoint F (MonoidHom.fst A B).ker := by
      rw [Subgroup.disjoint_def]
      intro x hx hx1
      by_contra hne
      exact hcon x hx hne (MonoidHom.mem_ker.1 hx1)
    have hcard := card_map_eq_of_disjoint_ker (MonoidHom.fst A B) hdis
    have hle := hA _ (hF.map (MonoidHom.fst A B))
    rw [hcard, hc] at hle
    have hp2 := (Fact.out : p.Prime).two_le
    nlinarith
  obtain ⟨y, hyF, hy1, hyfst⟩ := h1
  have hA1 : ∀ a : A, (a, (1 : B)) ∈ Subgroup.closure S := fun a =>
    Subgroup.subset_closure ⟨y, hyF, hy1, Prod.ext (by simp [hyfst]) (by simp)⟩
  have hB1 : ∀ b : B, ((1 : A), b) ∈ Subgroup.closure S := by
    by_cases hx : ∃ x ∈ F, x ≠ 1 ∧ x.2 = 1
    · obtain ⟨x, hxF, hx1, hx2⟩ := hx
      exact fun b => Subgroup.subset_closure ⟨x, hxF, hx1, Prod.ext (by simp) (by simp [hx2])⟩
    · push Not at hx
      have hdis : Disjoint F (MonoidHom.snd A B).ker := by
        rw [Subgroup.disjoint_def]
        intro x hx' hx1
        by_contra hne
        exact hx x hx' hne (MonoidHom.mem_ker.1 hx1)
      have hFB : IsElemAbelian p (F.map (MonoidHom.snd A B)) := hF.map _
      have hcardFB : Nat.card (F.map (MonoidHom.snd A B)) = p ^ 2 := by
        rw [card_map_eq_of_disjoint_ker _ hdis, hc]
      have htop := hB _ hFB hcardFB
      intro b
      have hb : b ∈ Subgroup.closure {b : B | ∃ f ∈ F.map (MonoidHom.snd A B), f ≠ 1 ∧
          Commute b f} := by
        rw [htop]
        exact Subgroup.mem_top _
      have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
      rw [MonoidHom.map_closure] at hmap
      refine Subgroup.closure_mono ?_ hmap
      rintro _ ⟨b', ⟨_, ⟨x, hxF, rfl⟩, hf1, hcb⟩, rfl⟩
      refine ⟨x, hxF, fun h => hf1 (by simp [h]), ?_⟩
      exact Prod.ext (by simp) (by simpa using hcb.eq)
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have := (Subgroup.closure S).mul_mem (hA1 a) (hB1 b)
  simpa using this

end Prod

end CFSG.LieType.SeitzGeneration.ExcHigh

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ClsLinField

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419

open CFSG.Open CFSG.Open.StatedAPI Matrix

theorem k1419ClsLinCentral {F : Type} [Field F] [Finite F] {n r : ℕ} {D : Fin r → Type} {d : Fin r → ℕ}
    [∀ i, Field (D i)] [∀ i, Finite (D i)] [∀ i, Algebra F (D i)]
    (Φ : (∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) →ₐ[F] Matrix (Fin n) (Fin n) F)
    (θ : (∀ i, GL (Fin (d i)) (D i)) →* GL (Fin n) F)
    (hd : ∀ i, 1 ≤ d i) (hΦ : Function.Injective Φ) (hθ : Function.Injective θ)
    (hθΦ : ∀ w, ((θ w : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Φ (fun i => ((w i : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i))))
    (A : GL (Fin n) F) (hθA : θ.range = Subgroup.centralizer ({A} : Set (GL (Fin n) F)))
    (hA3 : ∃ c : F, ((A ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      c • (1 : Matrix (Fin n) (Fin n) F))
    (hAns : ∀ c : F, (A : Matrix (Fin n) (Fin n) F) ≠ c • (1 : Matrix (Fin n) (Fin n) F))
    (i : Fin r) (hi : 2 ≤ d i) (M : Subgroup (GL (Fin n) F))
    (hM : M = ((StatedSL (d i) (D i)).map
      (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i)).map θ) :
    3 ∣ Module.finrank F (D i) ∨
      ((3 ∣ d i ∧ 3 ∣ Nat.card (D i) - 1) →
        ∃ z : GL (Fin n) F, z ∈ M ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧ (∀ y ∈ M, z * y = y * z) ∧
          z ∉ StatedScalars (Fin n) F) := by
  classical
  have hA_range : A ∈ θ.range := by
    rw [hθA, Subgroup.mem_centralizer_iff]
    intro b hb
    rw [Set.mem_singleton_iff] at hb
    subst hb
    rfl
  obtain ⟨wA, hwA⟩ := MonoidHom.mem_range.mp hA_range
  have hwA_center : wA ∈ Subgroup.center (∀ k, GL (Fin (d k)) (D k)) := by
    rw [Subgroup.mem_center_iff]
    intro v
    apply hθ
    rw [map_mul, map_mul, hwA]
    have hv : θ v ∈ Subgroup.centralizer ({A} : Set (GL (Fin n) F)) := by
      rw [← hθA]; exact ⟨v, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hv A (by simp)).symm
  have hcenter (j : Fin r) : wA j ∈ Subgroup.center (GL (Fin (d j)) (D j)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.mp hwA_center
      (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) j g)
    have h2 := congrFun h j
    simp only [Pi.mul_apply, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at h2
    exact h2
  have hwA_scalar (j : Fin r) : ∃ a : (D j)ˣ,
      Matrix.GeneralLinearGroup.scalar (Fin (d j)) a = wA j := by
    have h : wA j ∈ (Matrix.GeneralLinearGroup.scalar (Fin (d j))).range := by
      rw [← Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact hcenter j
    exact MonoidHom.mem_range.mp h
  by_cases hfin : 3 ∣ Module.finrank F (D i)
  · exact Or.inl hfin
  · right
    rintro ⟨h3d, h3card⟩
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have h3u : 3 ∣ Nat.card (D i)ˣ := by rw [Nat.card_units]; exact h3card
    obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := (D i)ˣ) 3 h3u
    have hω3 : ω ^ 3 = 1 := by simpa [hω] using pow_orderOf_eq_one ω
    have hωne : ω ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hω
      omega
    set Ω : GL (Fin (d i)) (D i) :=
      Matrix.GeneralLinearGroup.scalar (Fin (d i)) ω with hΩdef
    have hω3' : (ω : D i) ^ 3 = 1 := by
      simpa using congrArg (fun u : (D i)ˣ => (u : D i)) hω3
    have hΩ3 : Ω ^ 3 = 1 := by
      rw [hΩdef, ← map_pow, hω3, map_one]
    have hΩne : Ω ≠ 1 := by
      intro h
      apply hωne
      apply Units.ext
      have hmat : (Ω : Matrix (Fin (d i)) (Fin (d i)) (D i)) = 1 := by
        simpa using congrArg
          (fun x : GL (Fin (d i)) (D i) => (x : Matrix (Fin (d i)) (Fin (d i)) (D i))) h
      rw [hΩdef, Matrix.GeneralLinearGroup.coe_scalar] at hmat
      have hp : Fin (d i) := ⟨0, by have := hd i; omega⟩
      have hentry := congrFun (congrFun hmat hp) hp
      simpa [Matrix.scalar_apply] using hentry
    have hΩSL : Ω ∈ StatedSL (d i) (D i) := by
      refine Subgroup.subset_closure ?_
      change ((Ω : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i)).det = 1
      rw [hΩdef, Matrix.GeneralLinearGroup.coe_scalar]
      have hscalar : Matrix.scalar (Fin (d i)) (ω : D i)
          = (ω : D i) • (1 : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
        ext p q
        by_cases hpq : p = q <;> simp [Matrix.scalar_apply, hpq]
      rw [hscalar, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
      obtain ⟨k, hk⟩ := h3d
      rw [hk, pow_mul, hω3', one_pow]
    set z : GL (Fin n) F :=
      θ (MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i Ω) with hzdef
    refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hM, hzdef]
      exact Subgroup.mem_map_of_mem θ (Subgroup.mem_map_of_mem _ hΩSL)
    · intro h
      have hm : MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i Ω = 1 := by
        apply hθ
        simpa [hzdef] using h
      have hm' : Pi.mulSingle (M := fun j => GL (Fin (d j)) (D j)) i Ω = 1 := by
        simpa [MonoidHom.mulSingle_apply] using hm
      exact hΩne (Pi.mulSingle_eq_one_iff.mp hm')
    · rw [hzdef, ← map_pow, MonoidHom.mulSingle_apply, ← Pi.mulSingle_pow, hΩ3,
        Pi.mulSingle_one, map_one]
    · intro y hy
      rw [hM] at hy
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp hy
      obtain ⟨g, -, hgw⟩ := Subgroup.mem_map.mp hw
      rw [← hwy, ← hgw, hzdef]
      have hsingle : MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i Ω
          * MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i g
          = MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i g
          * MonoidHom.mulSingle (fun j => GL (Fin (d j)) (D j)) i Ω := by
        simp only [MonoidHom.mulSingle_apply, ← Pi.mulSingle_mul]
        rw [Pi.mulSingle_inj, hΩdef]
        exact Matrix.GeneralLinearGroup.scalar_commute ω g
      simpa [← map_mul] using congrArg θ hsingle
    ·
      intro hzS
      rw [StatedScalars, MonoidHom.mem_range] at hzS
      obtain ⟨c, hc⟩ := hzS
      have hzc : (z : Matrix (Fin n) (Fin n) F) = c.1 • 1 := by
        rw [← hc]
        ext p q
        by_cases hpq : p = q <;>
          simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hpq]
      have hleft : Φ (fun j =>
            (((MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i Ω) j
              : GL (Fin (d j)) (D j)) : Matrix (Fin (d j)) (Fin (d j)) (D j)))
          = (z : Matrix (Fin n) (Fin n) F) := by
        rw [← hθΦ (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i Ω), hzdef]
      have hright : Φ (fun j => algebraMap F (Matrix (Fin (d j)) (Fin (d j)) (D j)) c.1)
          = (z : Matrix (Fin n) (Fin n) F) := by
        change Φ (algebraMap F (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) c.1)
          = (z : Matrix (Fin n) (Fin n) F)
        rw [AlgHom.commutes, hzc, Algebra.algebraMap_eq_smul_one]
      have hcoords := hΦ (hleft.trans hright.symm)
      by_cases hex : ∃ j : Fin r, j ≠ i
      ·
        obtain ⟨j, hj⟩ := hex
        have hcoordj := congrFun hcoords j
        have hj1 : (MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i Ω) j = 1 := by
          rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne' (Ne.symm hj)]
        have hmat : algebraMap F (Matrix (Fin (d j)) (Fin (d j)) (D j)) c.1 = 1 := by
          simpa [hj1] using hcoordj.symm
        have hc1 : c.1 = 1 := by
          have hp : Fin (d j) := ⟨0, by have := hd j; omega⟩
          have hentry := congrFun (congrFun hmat hp) hp
          rw [Matrix.algebraMap_matrix_apply, Matrix.one_apply_eq, if_pos rfl] at hentry
          exact RingHom.injective (algebraMap F (D j)) (by simpa using hentry)
        have hΩmat : (Ω : Matrix (Fin (d i)) (Fin (d i)) (D i)) = 1 := by
          have hcoordi := congrFun hcoords i
          have hsame : (((MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i Ω) i
              : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i))
              = (Ω : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by simp
          rw [hsame] at hcoordi
          rw [hcoordi, hc1]
          simp
        exact hΩne (Units.ext (by simpa using hΩmat))
      ·
        push Not at hex
        obtain ⟨a₀, ha₀⟩ := hwA_scalar i
        have hω_eq : (ω : D i) = algebraMap F (D i) c.1 := by
          have hcoordi := congrFun hcoords i
          have hsame : (((MonoidHom.mulSingle (fun k => GL (Fin (d k)) (D k)) i Ω) i
              : GL (Fin (d i)) (D i)) : Matrix (Fin (d i)) (Fin (d i)) (D i))
              = (Ω : Matrix (Fin (d i)) (Fin (d i)) (D i)) := by simp
          rw [hsame] at hcoordi
          have hp : Fin (d i) := ⟨0, by have := hd i; omega⟩
          have hentry := congrFun (congrFun hcoordi hp) hp
          simpa [hΩdef, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
            Matrix.algebraMap_matrix_apply] using hentry
        have hc3 : c.1 ^ 3 = 1 := by
          apply RingHom.injective (algebraMap F (D i))
          rw [map_pow, map_one, ← hω_eq]
          simpa using congrArg (fun u : (D i)ˣ => (u : D i)) hω3
        have hcne : c.1 ≠ 1 := by
          intro hc1
          apply hωne
          apply Units.ext
          rw [hω_eq, hc1]
          simp
        have hAexpr : (A : Matrix (Fin n) (Fin n) F) =
            Φ (fun j => (((wA j : GL (Fin (d j)) (D j))
              : Matrix (Fin (d j)) (Fin (d j)) (D j)))) := by
          rw [← hwA, hθΦ wA]
        have ha₀_notmem : (a₀ : D i) ∉ (algebraMap F (D i)).range := by
          rintro ⟨c', hc'⟩
          apply hAns c'
          rw [hAexpr]
          have hfun : (fun j => (((wA j : GL (Fin (d j)) (D j))
                : Matrix (Fin (d j)) (Fin (d j)) (D j))))
              = (fun j => algebraMap F (Matrix (Fin (d j)) (Fin (d j)) (D j)) c') := by
            funext j
            rw [hex j, ← ha₀, Matrix.GeneralLinearGroup.coe_scalar, ← hc']
            rfl
          rw [hfun]
          change Φ (algebraMap F (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) c') = c' • 1
          rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
        have ha₀_pow_mem : (a₀ : D i) ^ 3 ∈ (algebraMap F (D i)).range := by
          obtain ⟨c₀, hc₀⟩ := hA3
          have hA3expr : ((A ^ 3 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
              Φ (fun j => (((wA j) ^ 3 : GL (Fin (d j)) (D j))
                : Matrix (Fin (d j)) (Fin (d j)) (D j))) := by
            have hpow : A ^ 3 = θ (wA ^ 3) := by rw [← hwA, ← map_pow]
            rw [hpow, hθΦ (wA ^ 3)]
            congr 1
          have hcoords3 : (fun j => (((wA j) ^ 3 : GL (Fin (d j)) (D j))
                : Matrix (Fin (d j)) (Fin (d j)) (D j)))
              = algebraMap F (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j)) c₀ := by
            apply hΦ
            rw [AlgHom.commutes, ← hA3expr, hc₀, Algebra.algebraMap_eq_smul_one]
          refine ⟨c₀, ?_⟩
          have hcoord_i := (congrFun hcoords3 i).symm
          have hp : Fin (d i) := ⟨0, by have := hd i; omega⟩
          have hentry := congrFun (congrFun hcoord_i hp) hp
          rw [show ((algebraMap F (∀ j, Matrix (Fin (d j)) (Fin (d j)) (D j))) c₀) i
              = algebraMap F (Matrix (Fin (d i)) (Fin (d i)) (D i)) c₀ from rfl] at hentry
          rw [Matrix.algebraMap_matrix_apply, if_pos rfl] at hentry
          rw [← ha₀, ← map_pow, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
            Matrix.diagonal_apply_eq] at hentry
          exact hentry
        haveI : FiniteDimensional F (D i) :=
          (Module.finite_iff_finite (R := F) (M := D i)).2 inferInstance
        exact hfin (k1419ClsLinField_dvd_finrank ⟨c.1, hc3, hcne⟩ ha₀_notmem ha₀_pow_mem)

end CFSG.LocalAnalysis.GLTheoremA.K1419

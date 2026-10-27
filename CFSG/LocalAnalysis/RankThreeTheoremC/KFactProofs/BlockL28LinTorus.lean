module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

variable {K : Type} [Field K]

@[expose] def linTorusVec {r n : ℕ} (t : Fin r → Kˣ) (i : Fin n) : Kˣ :=
  if h : (i : ℕ) < r then t ⟨i, h⟩ else if (i : ℕ) = r then (∏ j, t j)⁻¹ else 1

theorem linTorusVec_one {r n : ℕ} : linTorusVec (n := n) (1 : Fin r → Kˣ) = 1 := by
  funext i
  simp only [linTorusVec, Pi.one_apply, Finset.prod_const_one, inv_one]
  split_ifs <;> rfl

theorem linTorusVec_mul {r n : ℕ} (t s : Fin r → Kˣ) :
    linTorusVec (n := n) (t * s) = linTorusVec t * linTorusVec s := by
  funext i
  simp only [linTorusVec, Pi.mul_apply, Finset.prod_mul_distrib, mul_inv]
  split_ifs <;> simp

theorem prod_linTorusVec {r n : ℕ} (hn : r + 1 ≤ n) (t : Fin r → Kˣ) :
    ∏ i, linTorusVec (n := n) t i = 1 := by
  let g : ℕ → Kˣ := fun k => if h : k < r then t ⟨k, h⟩ else if k = r then (∏ j, t j)⁻¹ else 1
  have e : ∏ i, linTorusVec (n := n) t i = ∏ i : Fin n, g i := rfl
  have hg : ∏ k ∈ Finset.range r, g k = ∏ j, t j := by
    rw [← Fin.prod_univ_eq_prod_range g r]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp [g, j.isLt]
  rw [e, Fin.prod_univ_eq_prod_range g n, ← Finset.prod_range_mul_prod_Ico g hn,
    Finset.prod_eq_one (s := Finset.Ico (r + 1) n) fun k hk => ?_, mul_one,
    Finset.prod_range_succ, hg]
  · simp [g]
  · rw [Finset.mem_Ico] at hk
    have h1 : ¬ k < r := by omega
    have h2 : k ≠ r := by omega
    simp only [g, h1, h2, ↓reduceDIte, ↓reduceIte]

variable (K) in
@[expose] noncomputable def linTorus (r : ℕ) {n : ℕ} (hn : r + 1 ≤ n) :
    (Fin r → Kˣ) →* SpecialLinearGroup (Fin n) K where
  toFun t := ⟨diagonal fun i => (linTorusVec t i : K), by
    rw [det_diagonal, ← Units.coe_prod, prod_linTorusVec hn, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    simp [linTorusVec_one]
  map_mul' t s := by
    apply Subtype.ext
    change diagonal (fun i => (linTorusVec (t * s) i : K)) =
      diagonal (fun i => (linTorusVec t i : K)) * diagonal (fun i => (linTorusVec s i : K))
    rw [diagonal_mul_diagonal, linTorusVec_mul]
    rfl

theorem coe_linTorus {r n : ℕ} (hn : r + 1 ≤ n) (t : Fin r → Kˣ) :
    ((linTorus K r hn t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (linTorusVec t i : K) :=
  rfl

theorem linTorus_mem_flagStabilizer {r n : ℕ} (hn : r + 1 ≤ n) (I : Set ℕ) (t : Fin r → Kˣ) :
    linTorus K r hn t ∈ flagStabilizer n K I := by
  refine CFSG.QuasithinUnique.Vol2Native.A312L.mem_flagStabilizer_of_entries
    fun k l c _ hl hk => ?_
  rw [coe_linTorus, diagonal_apply_ne]
  intro e
  subst e
  omega

theorem eq_one_of_linTorus_mem_center {r n : ℕ} (hn : r + 1 ≤ n)
    (hcop : Nat.Coprime (r + 1) (Nat.card Kˣ)) {t : Fin r → Kˣ}
    (ht : linTorus K r hn t ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) : t = 1 := by
  have hr : r < n := by omega
  have hsc := SpecialLinearGroup.scalar_eq_self_of_mem_center ht ⟨r, hr⟩
  have hentry : ∀ i : Fin n, ((linTorus K r hn t : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i = (linTorusVec t i : K) := fun i => by
    rw [coe_linTorus, diagonal_apply_eq]
  have hcr : (linTorusVec t ⟨r, hr⟩ : K) = ((∏ j, t j)⁻¹ : Kˣ) := by
    simp [linTorusVec]
  have htj : ∀ j : Fin r, t j = (∏ j, t j)⁻¹ := fun j => by
    have hjn : (j : ℕ) < n := by omega
    have hj := congrArg (fun A : Matrix (Fin n) (Fin n) K => A ⟨j, hjn⟩ ⟨j, hjn⟩) hsc
    simp only [scalar_apply, diagonal_apply_eq, hentry] at hj
    rw [hcr] at hj
    have hj' : (linTorusVec t ⟨j, hjn⟩ : K) = (t j : K) := by
      simp [linTorusVec, j.isLt]
    exact Units.ext (hj'.symm.trans hj.symm)
  set c : Kˣ := (∏ j, t j)⁻¹ with hc
  have hprod : ∏ j, t j = c ^ r := by
    rw [Finset.prod_congr rfl fun j _ => htj j, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hpow : c ^ (r + 1) = 1 := by
    rw [pow_succ', ← hprod, hc, inv_mul_cancel]
  have hdvd : orderOf c ∣ Nat.gcd (r + 1) (Nat.card Kˣ) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpow) (orderOf_dvd_natCard c)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  funext j
  rw [htj j, hdvd]
  rfl

theorem exists_linTorus_embedding {Y : Type} [Group Y] {L P : Subgroup Y} {r n : ℕ}
    (hn : r + 1 ≤ n) (hcop : Nat.Coprime (r + 1) (Nat.card Kˣ)) {I : Set ℕ}
    (ρ : SpecialLinearGroup (Fin n) K →* ↥L)
    (hker : ρ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K)
    (hcompat : ∀ g, e (QuotientGroup.mk (ρ g)) = proj n K g)
    (hcomap : (P.subgroupOf L).comap ρ = flagStabilizer n K I) :
    ∃ φ : (Fin r → Kˣ) →* Y, Function.Injective φ ∧ φ.range ≤ P ∧
      ∀ a, φ a ∈ Subgroup.centralizer (L : Set Y) → a = 1 := by
  refine ⟨L.subtype.comp (ρ.comp (linTorus K r hn)), ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro t ht
    have h1 : ρ (linTorus K r hn t) = 1 := Subtype.ext ht
    exact eq_one_of_linTorus_mem_center hn hcop (hker h1)
  · rintro _ ⟨t, rfl⟩
    have h1 : linTorus K r hn t ∈ (P.subgroupOf L).comap ρ :=
      hcomap ▸ linTorus_mem_flagStabilizer hn I t
    exact h1
  · intro a ha
    have hZ : ρ (linTorus K r hn a) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp ha g g.2
    have h2 : linTorus K r hn a ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center, ← proj_eq_one_iff, ← hcompat,
        (QuotientGroup.eq_one_iff _).mpr hZ, map_one]
    exact eq_one_of_linTorus_mem_center hn hcop h2

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

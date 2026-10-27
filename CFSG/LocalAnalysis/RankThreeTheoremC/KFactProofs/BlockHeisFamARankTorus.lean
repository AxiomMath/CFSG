module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

private def heisARVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) : Fin (5 + m) → G :=
  Fin.append (![c 0, c 1, c 2, c 3, (c 0 * c 1 * c 2 * c 3)⁻¹] : Fin 5 → G) (fun _ => 1)

private theorem heisARVec_mul {G : Type*} [CommGroup G] (m : ℕ) (c c' : Fin 4 → G) :
    heisARVec m (c * c') = heisARVec m c * heisARVec m c' := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [heisARVec, mul_comm, mul_left_comm, mul_assoc, mul_inv]
  · simp [heisARVec]

private theorem prod_heisARVec {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) :
    ∏ i, heisARVec m c i = 1 := by
  rw [Fin.prod_univ_add]
  simp [heisARVec, Fin.prod_univ_five]

private theorem heisARVec_castAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G)
    (j : Fin 4) : heisARVec m c (Fin.castAdd m j.castSucc) = c j := by
  fin_cases j <;> simp [heisARVec]

private theorem heisARVec_natAdd {G : Type*} [CommGroup G] (m : ℕ) (c : Fin 4 → G) (j : Fin m) :
    heisARVec m c (Fin.natAdd 5 j) = 1 := by
  simp [heisARVec]

private def heisARDiag {K : Type*} [Field K] {n : ℕ} (u : Fin n → Kˣ) (hu : ∏ i, u i = 1) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨Matrix.diagonal fun i => (u i : K), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, hu, Units.val_one]⟩

private def heisARTorus (K : Type*) [Field K] (Z : Subgroup Kˣ) (m : ℕ) :
    (Fin 4 → Z) →* Matrix.SpecialLinearGroup (Fin (5 + m)) K :=
  MonoidHom.mk' (fun c => heisARDiag (fun i => ((heisARVec m c i : Z) : Kˣ)) (by
      simpa using congrArg (fun z : Z => (z : Kˣ)) (prod_heisARVec m c)))
    (fun c c' => by
      apply Subtype.ext
      simp only [heisARDiag, heisARVec_mul, Pi.mul_apply, Subgroup.coe_mul, Units.val_mul]
      exact (Matrix.diagonal_mul_diagonal _ _).symm)

private theorem coe_heisARTorus (K : Type*) [Field K] (Z : Subgroup Kˣ) (m : ℕ) (c : Fin 4 → Z) :
    ((heisARTorus K Z m c : Matrix.SpecialLinearGroup (Fin (5 + m)) K) :
      Matrix (Fin (5 + m)) (Fin (5 + m)) K) =
      Matrix.diagonal fun i => (((heisARVec m c i : Z) : Kˣ) : K) :=
  rfl

private theorem heisARTorus_center {K : Type*} [Field K] {ζ : Kˣ} {r : ℕ} (hr : r.Prime)
    (hζ : orderOf ζ = r) {m : ℕ} (hm : 1 ≤ m ∨ ¬ r ∣ 5 + m) {c : Fin 4 → Subgroup.zpowers ζ}
    (hc : heisARTorus K (Subgroup.zpowers ζ) m c ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (5 + m)) K)) : c = 1 := by
  obtain ⟨s, -, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have hentry : ∀ i, (((heisARVec m c i : Subgroup.zpowers ζ) : Kˣ) : K) = s := by
    intro i
    have h := congrFun (congrFun hs i) i
    rw [coe_heisARTorus, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
      Matrix.diagonal_apply_eq] at h
    exact h.symm
  obtain ⟨w, hw⟩ : ∃ w, heisARVec m c 0 = w := ⟨_, rfl⟩
  have hall : ∀ i, heisARVec m c i = w := fun i =>
    hw ▸ Subtype.ext (Units.ext ((hentry i).trans (hentry 0).symm))
  have hw1 : w = 1 := by
    rcases hm with hm | hm
    · have h := hall (Fin.natAdd 5 ⟨0, by omega⟩)
      rw [heisARVec_natAdd] at h
      exact h.symm
    · have hcard : Nat.card (Subgroup.zpowers ζ) = r := by rw [Nat.card_zpowers, hζ]
      have h3 : w ^ (5 + m) = 1 := by
        have h := prod_heisARVec m c
        simpa [hall, Finset.prod_const] using h
      have h4 : w ^ r = 1 := by rw [← hcard]; exact pow_card_eq_one'
      have hcop : Nat.Coprime r (5 + m) := (Nat.Prime.coprime_iff_not_dvd hr).2 hm
      have h5 : w ^ r.gcd (5 + m) = 1 := pow_gcd_eq_one.2 ⟨h4, h3⟩
      rwa [hcop.gcd_eq_one, pow_one] at h5
  funext j
  have h := hall (Fin.castAdd m j.castSucc)
  rw [heisARVec_castAdd, hw1] at h
  simpa using h

theorem heisAR_false_of_cover {L : Type*} [Group L] (hrk : OddRankLeThree L) {K : Type*}
    [Field K] {n r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hn : 5 ≤ n) (hnr : 6 ≤ n ∨ ¬ r ∣ n)
    {ζ : Kˣ} (hζ : orderOf ζ = r) (ρ : Matrix.SpecialLinearGroup (Fin n) K →* L)
    (hρ : ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 5 + m := ⟨n - 5, by omega⟩
  set Z := Subgroup.zpowers ζ with hZ
  let φ : (Fin 4 → Z) →* L := ρ.comp (heisARTorus K Z m)
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    exact heisARTorus_center hr hζ (hnr.imp (fun h => by omega) id) (hρ hc)
  have hZcard : Nat.card Z = r := by rw [hZ, Nat.card_zpowers, hζ]
  have hZpow : ∀ x : Z, x ^ r = 1 := fun x => by rw [← hZcard]; exact pow_card_eq_one'
  have hcard : Nat.card φ.range = r ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv, Nat.card_fun, hZcard,
      Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin]
  have hcomm : IsMulCommutative φ.range := ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm x y]⟩⟩
  have hexp : ∀ x ∈ φ.range, x ^ r = 1 := by
    rintro _ ⟨c, rfl⟩
    rw [← map_pow, show c ^ r = 1 from funext fun i => hZpow _, map_one]
  have h3 := hrk r hr hr2 φ.range hcomm hexp
  rw [hcard] at h3
  have h4 : r ^ 3 < r ^ 4 := Nat.pow_lt_pow_right hr.one_lt (by norm_num)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

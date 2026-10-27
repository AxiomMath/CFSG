module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Base
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Geo
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
public import CFSG.GH74.GLS.Stage2.OddAut.Lin3Aut

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.SubgroupLists
open scoped commutatorElement

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem u3_diag_comm {σ : K ≃+* K} {k : Fin 3} {g : Matrix (Fin 3) (Fin 3) K}
    (hu : conjTr σ g * g = 1) (hg : g *ᵥ (Pi.single k (1 : K) : Fin 3 → K) = Pi.single k 1)
    {d : Fin 3 → K} (hd : ∀ a b, a ≠ k → b ≠ k → d a = d b) :
    diagonal d * g = g * diagonal d := by
  have hcol : ∀ a, g a k = (Pi.single k (1 : K) : Fin 3 → K) a := fun a => by
    have := congrFun hg a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hrow : ∀ b, b ≠ k → g k b = 0 := fun b hb => by
    have := congrFun (congrFun hu k) b
    have e : (conjTr σ g * g) k b = g k b := by
      simp only [Matrix.mul_apply, conjTr, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_eq_single k]
      · rw [hcol k]; simp
      · intro c _ hc
        rw [hcol c]
        simp [hc]
      · simp
    rw [← e, this]
    simp [hb.symm]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases ha : a = k
  · subst ha
    by_cases hb : b = a
    · subst hb; ring
    · rw [hrow b hb]; ring
  · by_cases hb : b = k
    · subst hb
      rw [hcol a]
      simp [ha]
    · rw [hd a b ha hb]; ring

theorem u3_diag_ne_zero {F x : GL (Fin 3) K} {d : Fin 3 → K}
    (hxd : (x : Matrix (Fin 3) (Fin 3) K) * (F : Matrix (Fin 3) (Fin 3) K) =
      (F : Matrix (Fin 3) (Fin 3) K) * diagonal d) : ∀ k, d k ≠ 0 := by
  have h1 := congrArg Matrix.det hxd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h1
  have hF := GeneralLinearGroup.det_ne_zero F
  have hx := GeneralLinearGroup.det_ne_zero x
  have h2 : (x : Matrix (Fin 3) (Fin 3) K).det = ∏ k, d k := by
    apply mul_right_cancel₀ hF
    rw [h1, mul_comm]
  intro k hk
  apply hx
  rw [h2]
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

theorem u3_exists_plane_fix {r : ℕ} (hr : r.Prime) (V : Subgroup (MulAut (U3T h)))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1) (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d)
    {i j : Fin 3} :
    ∃ w ∈ V, w ≠ 1 ∧ ∃ (x : U3U h) (d : Fin 3 → K),
      w = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d ∧ d i = d j := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hr.ne_zero)
  have : Fintype V := Fintype.ofFinite V
  set c := primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hc
  have hdata : ∀ v ∈ V, ∃ (ℓ : K) (x : U3U h) (d : Fin 3 → K), v = c x ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          diagonal d ∧ d i = ℓ * d j := by
    intro v hv
    obtain ⟨x, d, hvx, hxd⟩ := hF v hv
    exact ⟨d i / d j, x, d, hvx, hxd, by rw [div_mul_cancel₀ _ (u3_diag_ne_zero hxd j)]⟩
  have hroot : ∀ v ∈ V, ∀ (ℓ : K) (x : U3U h) (d : Fin 3 → K), v = c x →
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          diagonal d → d i = ℓ * d j → ℓ ^ r = 1 := by
    intro v hv ℓ x d hvx hxd hdij
    have hdn := u3_diag_ne_zero hxd
    have hxr : c (x ^ r) = 1 := by rw [map_pow, ← hvx]; exact hVe v hv
    obtain ⟨z, hz⟩ := (u3_conj_eq_one_iff h (x ^ r)).1 hxr
    have hxr' : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ r *
        ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (d ^ r) := mul_pow_diag hxd r
    have hzm : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ r =
        (z : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hz, coe_scalar_smul]
    have h1 : (z : K) • ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (d ^ r) := by
      rw [← hxr', hzm, Matrix.smul_mul, Matrix.one_mul]
    have hD : diagonal (d ^ r) = (z : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
      calc diagonal (d ^ r)
          = ((F⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (d ^ r) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        _ = ((F⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              ((z : K) • ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
            rw [Matrix.mul_assoc, ← h1]
        _ = (z : K) • 1 := by
            rw [Matrix.mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hk : ∀ k, d k ^ r = z := fun k => by
      have := congrFun (congrFun hD k) k
      simpa using this
    have h2 : (ℓ * d j) ^ r = d j ^ r := by rw [← hdij, hk i, hk j]
    rw [mul_pow] at h2
    have hdj : d j ^ r ≠ 0 := pow_ne_zero r (hdn j)
    exact mul_right_cancel₀ hdj (by rw [h2, one_mul])
  obtain ⟨S, hSdef⟩ : ∃ S : Finset K, S = Polynomial.nthRootsFinset r (1 : K) := ⟨_, rfl⟩
  have hS : S.card ≤ r := by
    rw [hSdef]
    unfold Polynomial.nthRootsFinset
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  have hex : ∀ v : V, ∃ (ℓ : K) (x : U3U h) (d : Fin 3 → K), (v : MulAut (U3T h)) = c x ∧
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          diagonal d ∧ d i = ℓ * d j := fun v => hdata v v.2
  choose ρ x d hvx hxd hdij using hex
  have hmaps : Set.MapsTo ρ ((Finset.univ : Finset V) : Set V) (S : Set K) := by
    intro v _
    rw [Finset.mem_coe, hSdef, Polynomial.mem_nthRootsFinset (hr.pos)]
    exact hroot v v.2 (ρ v) (x v) (d v) (hvx v) (hxd v) (hdij v)
  have hcard : S.card < (Finset.univ : Finset V).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hVc]
    calc S.card ≤ r := hS
      _ < r ^ 2 := by nlinarith [hr.two_le]
  obtain ⟨v₁, -, v₂, -, hne, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  have hd1 := u3_diag_ne_zero (hxd v₁)
  have hd2 := u3_diag_ne_zero (hxd v₂)
  refine ⟨(v₁ : MulAut (U3T h))⁻¹ * (v₂ : MulAut (U3T h)),
    V.mul_mem (V.inv_mem v₁.2) v₂.2, ?_, (x v₁)⁻¹ * x v₂, fun k => d v₂ k / d v₁ k, ?_, ?_, ?_⟩
  · intro h1
    apply hne
    have : (v₁ : MulAut (U3T h)) = v₂ := by
      have h' := congrArg (fun a => (v₁ : MulAut (U3T h)) * a) h1
      simpa using h'.symm
    exact Subtype.ext this
  · rw [map_mul, map_inv, ← hvx v₁, ← hvx v₂]
  · set x₁ : GL (Fin 3) K := ((x v₁ : U3U h) : GL (Fin 3) K) with hx₁
    have e1 := hxd v₁
    have e2 := hxd v₂
    have hDD : diagonal (d v₁) * diagonal (fun k => (d v₁ k)⁻¹) =
        (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      exact mul_inv_cancel₀ (hd1 k)
    have hinv : ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal (fun k => (d v₁ k)⁻¹) := by
      calc ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
          = ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (diagonal (d v₁) * diagonal (fun k => (d v₁ k)⁻¹))) := by
            rw [hDD, Matrix.mul_one]
        _ = ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              (((x₁ : Matrix (Fin 3) (Fin 3) K) *
                ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) *
                  diagonal (fun k => (d v₁ k)⁻¹)) := by
            rw [← Matrix.mul_assoc ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ← e1]
        _ = ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
              diagonal (fun k => (d v₁ k)⁻¹) := by
            rw [← Matrix.mul_assoc ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
              ((x₁ : Matrix (Fin 3) (Fin 3) K) *
                ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
              ← Matrix.mul_assoc ((x₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
              (x₁ : Matrix (Fin 3) (Fin 3) K),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    show (((x₁⁻¹ * ((x v₂ : U3U h) : GL (Fin 3) K) : GL (Fin 3) K)) :
      Matrix (Fin 3) (Fin 3) K) * _ = _
    rw [Units.val_mul, Matrix.mul_assoc, e2, ← Matrix.mul_assoc, hinv, Matrix.mul_assoc,
      diagonal_mul_diagonal]
    congr 2
    funext k
    ring
  · have hρ0 : ρ v₁ ≠ 0 := by
      intro h0
      have := hdij v₁
      rw [h0, zero_mul] at this
      exact hd1 i this
    show d v₂ i / d v₁ i = d v₂ j / d v₁ j
    rw [hdij v₁, hdij v₂, ← hfeq]
    have := hd1 j
    have := hd2 j
    field_simp

theorem u3_conj_fix_aux {F x g : GL (Fin 3) K} {d : Fin 3 → K} (hd0 : ∀ k, d k ≠ 0)
    (hxF : (x : Matrix (Fin 3) (Fin 3) K) * (F : Matrix (Fin 3) (Fin 3) K) =
      (F : Matrix (Fin 3) (Fin 3) K) * diagonal d)
    (hcomm : diagonal d * (g : Matrix (Fin 3) (Fin 3) K) =
      (g : Matrix (Fin 3) (Fin 3) K) * diagonal d) :
    x * (F * g * F⁻¹) * x⁻¹ = F * g * F⁻¹ := by
  set Dg : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k) with hDg
  have hxF' : x * F = F * Dg := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxF)
  have hcomm' : Dg * g = g * Dg := Units.ext (by
    rw [Units.val_mul, Units.val_mul]; exact hcomm)
  have h1 : Dg * g * Dg⁻¹ = g := by rw [hcomm']; group
  calc x * (F * g * F⁻¹) * x⁻¹ = (x * F) * g * (x * F)⁻¹ := by group
    _ = F * (Dg * g * Dg⁻¹) * F⁻¹ := by rw [hxF']; group
    _ = F * g * F⁻¹ := by rw [h1]

theorem u3_psi_fix [Finite K] [Fact p.Prime] [CharP K p] (F : U3U h) {k : Fin 3}
    {x : U3U h} {d : Fin 3 → K}
    (hxF : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d)
    (hd : ∀ a b, a ≠ k → b ≠ k → d a = d b)
    (g : ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)))
    (hg : (g : GL (Fin 3) K) ∈ u3Stab (CFSG.LieType.BorelTits.unitaryInvolution K p f) k) :
    primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x (u3Psi h F g) =
      u3Psi h F g := by
  obtain ⟨hgS, hgk⟩ := mem_u3Stab.1 hg
  have hu := (mem_SUid.1 hgS).2
  have hcomm := u3_diag_comm hu hgk hd
  have e := u3_conj_fix_aux (F := (F : GL (Fin 3) K)) (x := (x : GL (Fin 3) K))
    (g := (g : GL (Fin 3) K)) (u3_diag_ne_zero hxF) hxF hcomm
  show primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x
    ((primeFormConjSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) F g : _) :
      U3T h) = _
  rw [primeFormConjHom_mk]
  congr 1
  exact Subtype.ext e

theorem u3_fin3_aux : ∀ i j k a : Fin 3, i ≠ j → i ≠ k → j ≠ k → a ≠ k → a = i ∨ a = j := by
  decide

theorem u3_exists_stab_fix [Finite K] [Fact p.Prime] [CharP K p] {r : ℕ} (hr : r.Prime)
    (V : Subgroup (MulAut (U3T h))) (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1)
    (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) (k : Fin 3) :
    ∃ w ∈ V, w ≠ 1 ∧ ∀ g : ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)),
      (g : GL (Fin 3) K) ∈ u3Stab (CFSG.LieType.BorelTits.unitaryInvolution K p f) k →
        w (u3Psi h F g) = u3Psi h F g := by
  obtain ⟨i, j, hij, hik, hjk⟩ : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    revert k; decide
  obtain ⟨w, hwV, hw1, x, d, hwx, hxF, hdij⟩ :=
    u3_exists_plane_fix h hr V hVc hVe F hF (i := i) (j := j)
  refine ⟨w, hwV, hw1, fun g hg => ?_⟩
  have hd : ∀ a b, a ≠ k → b ≠ k → d a = d b := by
    intro a b ha hb
    rcases u3_fin3_aux i j k a hij hik hjk ha with ha' | ha' <;>
      rcases u3_fin3_aux i j k b hij hik hjk hb with hb' | hb' <;> rw [ha', hb']
    · exact hdij
    · exact hdij.symm
  rw [hwx]
  exact u3_psi_fix h F hxF hd g hg

theorem u3_generation_deriv (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f) {r : ℕ}
    (hr : r.Prime) (V : Subgroup (MulAut (U3T h))) (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) :
    (⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆) = ⊤ := by
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K p f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1 := by
    refine exists_norm_ne_one h.card_eq_sq fun hp => ?_
    have : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    rw [hp] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  have hP : Group.IsPerfect (SUid σ 2) := by
    have := isPerfect_statedSU_two h.card_eq_sq h4
    rwa [← SUid_eq_statedSU h.card_eq_sq 2] at this
  set Hπ := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆ with hHπ
  set N : Subgroup ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Hπ.comap (u3Psi h F) with hN
  set H : Subgroup (GL (Fin 3) K) := N.map (gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)).subtype with hH
  have hHk : ∀ k, ⁅u3Stab σ k, u3Stab σ k⁆ ≤ H := by
    intro k
    obtain ⟨w, hwV, hw1, hfix⟩ := u3_exists_stab_fix h hr V hVc hVe F hF k
    set S' : Subgroup ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      (u3Stab σ k).comap (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype
      with hS'
    have hle0 : u3Stab σ k ≤ (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      (inf_le_left : u3Stab σ k ≤ SUid σ 3).trans (le_of_eq (u3_SUid_eq h))
    have hmap : S'.map (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype =
        u3Stab σ k := by
      rw [hS']
      exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
    intro x hx
    rw [← hmap, ← Subgroup.map_commutator] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    have hle : S'.map (u3Psi h F) ≤ fixSub w := by
      rintro _ ⟨g, hg, rfl⟩
      exact mem_fixSub.2 (hfix g hg)
    have h1 : (⁅S', S'⁆).map (u3Psi h F) ≤ ⁅fixSub w, fixSub w⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    have h2 : ⁅fixSub w, fixSub w⁆ ≤ Hπ :=
      le_iSup₂_of_le w hwV (le_iSup (fun _ : w ≠ 1 => ⁅fixSub w, fixSub w⁆) hw1)
    exact h2 (h1 ⟨y, hy, rfl⟩)
  have hSU := u3_le_of_derived_stab hσ hq hP H hHk
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (g : GL (Fin 3) K) ∈ H := hSU (by rw [u3_SUid_eq h]; exact g.2)
    obtain ⟨y, hy, hyg⟩ := hg
    have : y = g := Subtype.ext hyg
    rw [← this]
    exact hy
  rw [eq_top_iff]
  intro t _
  obtain ⟨g, rfl⟩ := u3Psi_surjective h F t
  have : g ∈ N := hNtop ▸ Subgroup.mem_top g
  exact this

theorem u3_generation (hp2 : p ≠ 2) {r : ℕ}
    (hr : r.Prime) (V : Subgroup (MulAut (U3T h))) (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) :
    (⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v) = ⊤ := by
  have : Finite K := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  set σ := CFSG.LieType.BorelTits.unitaryInvolution K p f with hσdef
  have hσ : IsUnitaryInvolution σ := isUnitaryInvolution_unitaryInvolution h.card_eq_sq
  have hq : ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1 := by
    refine exists_norm_ne_one h.card_eq_sq fun hp => ?_
    have : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
    rw [hp] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 this)
  set Hπ := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v with hHπ
  set N : Subgroup ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    Hπ.comap (u3Psi h F) with hN
  set H : Subgroup (GL (Fin 3) K) := N.map (gramSU h ((1 : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K)).subtype with hH
  have hHk : ∀ k, u3Stab σ k ≤ H := by
    intro k
    obtain ⟨w, hwV, hw1, hfix⟩ := u3_exists_stab_fix h hr V hVc hVe F hF k
    set S' : Subgroup ↥(gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      (u3Stab σ k).comap (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype
      with hS'
    have hle0 : u3Stab σ k ≤ (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
      (inf_le_left : u3Stab σ k ≤ SUid σ 3).trans (le_of_eq (u3_SUid_eq h))
    have hmap : S'.map (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).subtype =
        u3Stab σ k := by
      rw [hS']
      exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
    intro x hx
    rw [← hmap] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    have h2 : fixSub w ≤ Hπ :=
      le_iSup₂_of_le w hwV (le_iSup (fun _ : w ≠ 1 => fixSub w) hw1)
    exact h2 (mem_fixSub.2 (hfix y hy))
  have hSU := u3_le_of_stab hσ hq H hHk
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (g : GL (Fin 3) K) ∈ H := hSU (by rw [u3_SUid_eq h]; exact g.2)
    obtain ⟨y, hy, hyg⟩ := hg
    have : y = g := Subtype.ext hyg
    rw [← this]
    exact hy
  rw [eq_top_iff]
  intro t _
  obtain ⟨g, rfl⟩ := u3Psi_surjective h F t
  have : g ∈ N := hNtop ▸ Subgroup.mem_top g
  exact this

theorem false_of_u3_toral (hp2 : p ≠ 2) {r : ℕ}
    {V Z : Subgroup (MulAut (U3T h))} (hs : IsSimpleGroup (U3T h))
    (hn : ∃ a b : U3T h, a * b ≠ b * a) (h2 : N2Cfg (U3T h) r V Z) (h3 : N3Full (U3T h) V Z)
    (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) : False := by
  obtain ⟨hr, -, hVe, hVc, -, -, -, -, -⟩ := id h2
  exact false_of_generation hs hn h2 h3
    (u3_generation h hp2 hr V hVc (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) F hF)

theorem false_of_u3_toral_deriv (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    {r : ℕ} {V Z : Subgroup (MulAut (U3T h))} (hs : IsSimpleGroup (U3T h))
    (hn : ∃ a b : U3T h, a * b ≠ b * a) (h2 : N2Cfg (U3T h) r V Z)
    (h3 : N3Deriv (U3T h) V Z) (F : U3U h)
    (hF : ∀ v ∈ V, ∃ (x : U3U h) (d : Fin 3 → K),
      v = primeFormConjHom h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) x ∧
        ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * ((F : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) =
          ((F : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * diagonal d) : False := by
  obtain ⟨hr, -, hVe, hVc, -, -, -, -, -⟩ := id h2
  exact false_of_generation_deriv hs hn h2 h3
    (u3_generation_deriv h hp2 h4 hr V hVc
      (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) F hF)


end CFSG.GH74.GLS.Stage2.Bender.Thm1

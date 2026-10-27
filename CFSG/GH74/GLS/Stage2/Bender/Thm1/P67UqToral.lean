module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqBase
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UqGeo
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core
import CFSG.GH74.GLS.Stage2.OddAut.LinNAut
import CFSG.RankThree.SubgroupLists.UnitaryThreeFamily

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.GH74.GLS.Stage2.OddAut CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.SubgroupLists
open scoped commutatorElement

section Pigeon

variable {p f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem uq_diag_comm {σ : K ≃+* K} {i j : Fin n} {g : Matrix (Fin n) (Fin n) K}
    (hu : conjTr σ g * g = 1)
    (hg : ∀ k, k ≠ i → k ≠ j → g *ᵥ (Pi.single k (1 : K) : Fin n → K) = Pi.single k 1)
    {d : Fin n → K} (hd : d i = d j) :
    diagonal d * g = g * diagonal d := by
  have hcol : ∀ k, k ≠ i → k ≠ j → ∀ a, g a k = (Pi.single k (1 : K) : Fin n → K) a := by
    intro k hki hkj a
    have := congrFun (hg k hki hkj) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hrow : ∀ k, k ≠ i → k ≠ j → ∀ b, b ≠ k → g k b = 0 := by
    intro k hki hkj b hb
    have := congrFun (congrFun hu k) b
    have e : (conjTr σ g * g) k b = g k b := by
      simp only [Matrix.mul_apply, conjTr, Matrix.transpose_apply, Matrix.map_apply]
      rw [Finset.sum_eq_single k]
      · rw [hcol k hki hkj k]; simp
      · intro c _ hc
        rw [hcol k hki hkj c]
        simp [hc]
      · simp
    rw [← e, this]
    simp [hb.symm]
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · have hdab : d a = d b := by
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
          first | rfl | exact hd | exact hd.symm
      rw [hdab]; ring
    · push Not at hb
      rw [hcol b hb.1 hb.2 a]
      have hab : a ≠ b := by
        rintro rfl
        rcases ha with h' | h'
        · exact hb.1 h'
        · exact hb.2 h'
      simp [hab]
  · push Not at ha
    by_cases hb : b = a
    · subst hb; ring
    · rw [hrow a ha.1 ha.2 b hb]; ring

theorem uq_diag_ne_zero {F x : GL (Fin n) K} {d : Fin n → K}
    (hxd : (x : Matrix (Fin n) (Fin n) K) * (F : Matrix (Fin n) (Fin n) K) =
      (F : Matrix (Fin n) (Fin n) K) * diagonal d) : ∀ k, d k ≠ 0 := by
  have h1 := congrArg Matrix.det hxd
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h1
  have hF := GeneralLinearGroup.det_ne_zero F
  have hx := GeneralLinearGroup.det_ne_zero x
  have h2 : (x : Matrix (Fin n) (Fin n) K).det = ∏ k, d k := by
    apply mul_right_cancel₀ hF
    rw [h1, mul_comm]
  intro k hk
  apply hx
  rw [h2]
  exact Finset.prod_eq_zero (Finset.mem_univ k) hk

theorem uq_exists_plane_fix (hn : 3 ≤ n) {r : ℕ} (hr : r.Prime) (V : Subgroup (MulAut (UqT h n)))
    (hVc : Nat.card V = r ^ 2) (hVe : ∀ v ∈ V, v ^ r = 1) (F : UqU h n)
    (hF : ∀ v ∈ V, ∃ (x : UqU h n) (d : Fin n → K),
      v = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d)
    {i j : Fin n} :
    ∃ w ∈ V, w ≠ 1 ∧ ∃ (x : UqU h n) (d : Fin n → K),
      w = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d ∧ d i = d j := by
  classical
  have hfin : Finite V := Nat.finite_of_card_ne_zero (by rw [hVc]; exact pow_ne_zero 2 hr.ne_zero)
  have : Fintype V := Fintype.ofFinite V
  set c := primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hc
  have hdata : ∀ v ∈ V, ∃ (ℓ : K) (x : UqU h n) (d : Fin n → K), v = c x ∧
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          diagonal d ∧ d i = ℓ * d j := by
    intro v hv
    obtain ⟨x, d, hvx, hxd⟩ := hF v hv
    exact ⟨d i / d j, x, d, hvx, hxd, by rw [div_mul_cancel₀ _ (uq_diag_ne_zero hxd j)]⟩
  have hroot : ∀ v ∈ V, ∀ (ℓ : K) (x : UqU h n) (d : Fin n → K), v = c x →
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          diagonal d → d i = ℓ * d j → ℓ ^ r = 1 := by
    intro v hv ℓ x d hvx hxd hdij
    have hdn := uq_diag_ne_zero hxd
    have hxr : c (x ^ r) = 1 := by rw [map_pow, ← hvx]; exact hVe v hv
    obtain ⟨z, hz⟩ := (uq_conj_eq_one_iff h hn (x ^ r)).1 hxr
    have hxr' : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ r *
        ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal (d ^ r) := mul_pow_diag_n hxd r
    have hzm : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ r =
        (z : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hz, coe_scalar_smul_n]
    have h1 : (z : K) • ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal (d ^ r) := by
      rw [← hxr', hzm, Matrix.smul_mul, Matrix.one_mul]
    have hD : diagonal (d ^ r) = (z : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      calc diagonal (d ^ r)
          = ((F⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal (d ^ r) := by
            rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
        _ = ((F⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((z : K) • ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
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
  have hex : ∀ v : V, ∃ (ℓ : K) (x : UqU h n) (d : Fin n → K), (v : MulAut (UqT h n)) = c x ∧
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
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
  have hd1 := uq_diag_ne_zero (hxd v₁)
  have hd2 := uq_diag_ne_zero (hxd v₂)
  refine ⟨(v₁ : MulAut (UqT h n))⁻¹ * (v₂ : MulAut (UqT h n)),
    V.mul_mem (V.inv_mem v₁.2) v₂.2, ?_, (x v₁)⁻¹ * x v₂, fun k => d v₂ k / d v₁ k, ?_, ?_, ?_⟩
  · intro h1
    apply hne
    have : (v₁ : MulAut (UqT h n)) = v₂ := by
      have h' := congrArg (fun a => (v₁ : MulAut (UqT h n)) * a) h1
      simpa using h'.symm
    exact Subtype.ext this
  · rw [map_mul, map_inv, ← hvx v₁, ← hvx v₂]
  · set x₁ : GL (Fin n) K := ((x v₁ : UqU h n) : GL (Fin n) K) with hx₁
    have e1 := hxd v₁
    have e2 := hxd v₂
    have hDD : diagonal (d v₁) * diagonal (fun k => (d v₁ k)⁻¹) =
        (1 : Matrix (Fin n) (Fin n) K) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext k
      exact mul_inv_cancel₀ (hd1 k)
    have hinv : ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal (fun k => (d v₁ k)⁻¹) := by
      calc ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
          = ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
                (diagonal (d v₁) * diagonal (fun k => (d v₁ k)⁻¹))) := by
            rw [hDD, Matrix.mul_one]
        _ = ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((x₁ : Matrix (Fin n) (Fin n) K) *
                ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
                  diagonal (fun k => (d v₁ k)⁻¹)) := by
            rw [← Matrix.mul_assoc ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K), ← e1]
        _ = ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              diagonal (fun k => (d v₁ k)⁻¹) := by
            rw [← Matrix.mul_assoc ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
              ((x₁ : Matrix (Fin n) (Fin n) K) *
                ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
              ← Matrix.mul_assoc ((x₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
              (x₁ : Matrix (Fin n) (Fin n) K),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    show (((x₁⁻¹ * ((x v₂ : UqU h n) : GL (Fin n) K) : GL (Fin n) K)) :
      Matrix (Fin n) (Fin n) K) * _ = _
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


theorem uq_conj_fix_aux {F x g : GL (Fin n) K} {d : Fin n → K} (hd0 : ∀ k, d k ≠ 0)
    (hxF : (x : Matrix (Fin n) (Fin n) K) * (F : Matrix (Fin n) (Fin n) K) =
      (F : Matrix (Fin n) (Fin n) K) * diagonal d)
    (hcomm : diagonal d * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * diagonal d) :
    x * (F * g * F⁻¹) * x⁻¹ = F * g * F⁻¹ := by
  set Dg : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero (diagonal d)
    (by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun k _ => hd0 k) with hDg
  have hxF' : x * F = F * Dg := Units.ext (by rw [Units.val_mul, Units.val_mul]; exact hxF)
  have hcomm' : Dg * g = g * Dg := Units.ext (by
    rw [Units.val_mul, Units.val_mul]; exact hcomm)
  have h1 : Dg * g * Dg⁻¹ = g := by rw [hcomm']; group
  calc x * (F * g * F⁻¹) * x⁻¹ = (x * F) * g * (x * F)⁻¹ := by group
    _ = F * (Dg * g * Dg⁻¹) * F⁻¹ := by rw [hxF']; group
    _ = F * g * F⁻¹ := by rw [h1]

theorem uq_psi_fix [Finite K] [Fact p.Prime] [CharP K p] (F : UqU h n) {i j : Fin n}
    {x : UqU h n} {d : Fin n → K}
    (hxF : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d) (hd : d i = d j)
    (g : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hg : (g : GL (Fin n) K) ∈ uqPairStab (CFSG.LieType.BorelTits.unitaryInvolution K p f) n i j) :
    primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x (uqPsi h n F g) =
      uqPsi h n F g := by
  obtain ⟨hgS, hgk⟩ := mem_uqPairStab.1 hg
  have hu := (mem_SUid.1 hgS).2
  have hcomm := uq_diag_comm hu hgk hd
  have e := uq_conj_fix_aux (F := (F : GL (Fin n) K)) (x := (x : GL (Fin n) K))
    (g := (g : GL (Fin n) K)) (uq_diag_ne_zero hxF) hxF hcomm
  show primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x
    ((primeFormConjSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) F g : _) :
      UqT h n) = _
  rw [primeFormConjHom_mk]
  congr 1
  exact Subtype.ext e

theorem uq_exists_pair_fix [Finite K] [Fact p.Prime] [CharP K p] (hn : 3 ≤ n) {r : ℕ}
    (hr : r.Prime) (V : Subgroup (MulAut (UqT h n))) (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (F : UqU h n)
    (hF : ∀ v ∈ V, ∃ (x : UqU h n) (d : Fin n → K),
      v = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d) {i j : Fin n} :
    ∃ w ∈ V, w ≠ 1 ∧ ∀ g : ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)),
      (g : GL (Fin n) K) ∈ uqPairStab (CFSG.LieType.BorelTits.unitaryInvolution K p f) n i j →
        w (uqPsi h n F g) = uqPsi h n F g := by
  obtain ⟨w, hwV, hw1, x, d, hwx, hxF, hdij⟩ :=
    uq_exists_plane_fix h hn hr V hVc hVe F hF (i := i) (j := j)
  refine ⟨w, hwV, hw1, fun g hg => ?_⟩
  rw [hwx]
  exact uq_psi_fix h F hxF hdij g hg

theorem uq_generation_deriv (hn : 3 ≤ n) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f) {r : ℕ}
    (hr : r.Prime) (V : Subgroup (MulAut (UqT h n))) (hVc : Nat.card V = r ^ 2)
    (hVe : ∀ v ∈ V, v ^ r = 1) (F : UqU h n)
    (hF : ∀ v ∈ V, ∃ (x : UqU h n) (d : Fin n → K),
      v = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d) :
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
  have h2K : (2 : K) ≠ 0 := by
    intro h20
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h20
    rw [CharP.cast_eq_zero_iff K p] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).1 h2)
  have hP : Group.IsPerfect (SUid σ 2) := by
    have := isPerfect_statedSU_two h.card_eq_sq h4
    rwa [← SUid_eq_statedSU h.card_eq_sq 2] at this
  set Hπ := ⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆ with hHπ
  set N : Subgroup ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Hπ.comap (uqPsi h n F) with hN
  set H : Subgroup (GL (Fin n) K) := N.map (gramSU h ((1 : GL (Fin n) K) :
    Matrix (Fin n) (Fin n) K)).subtype with hH
  have hHk : ∀ i j : Fin n, i ≠ j → ⁅uqPairStab σ n i j, uqPairStab σ n i j⁆ ≤ H := by
    intro i j _
    obtain ⟨w, hwV, hw1, hfix⟩ := uq_exists_pair_fix h hn hr V hVc hVe F hF (i := i) (j := j)
    set S' : Subgroup ↥(gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
      (uqPairStab σ n i j).comap (gramSU h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)).subtype with hS'
    have hle0 : uqPairStab σ n i j ≤ (gramSU h ((1 : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K)) :=
      (inf_le_left : uqPairStab σ n i j ≤ SUid σ n).trans (le_of_eq (uq_SUid_eq h))
    have hmap : S'.map (gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).subtype =
        uqPairStab σ n i j := by
      rw [hS']
      exact Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
    intro x hx
    rw [← hmap, ← Subgroup.map_commutator] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨y, ?_, rfl⟩
    have hle : S'.map (uqPsi h n F) ≤ fixSub w := by
      rintro _ ⟨g, hg, rfl⟩
      exact mem_fixSub.2 (hfix g hg)
    have h1 : (⁅S', S'⁆).map (uqPsi h n F) ≤ ⁅fixSub w, fixSub w⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    have h2 : ⁅fixSub w, fixSub w⁆ ≤ Hπ :=
      le_iSup₂_of_le w hwV (le_iSup (fun _ : w ≠ 1 => ⁅fixSub w, fixSub w⁆) hw1)
    exact h2 (h1 ⟨y, hy, rfl⟩)
  have hSU := uq_le_of_pair_derived hσ hq h2K hP hn H hHk
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : (g : GL (Fin n) K) ∈ H := hSU (by rw [uq_SUid_eq h]; exact g.2)
    obtain ⟨y, hy, hyg⟩ := hg
    have : y = g := Subtype.ext hyg
    rw [← this]
    exact hy
  rw [eq_top_iff]
  intro t _
  obtain ⟨g, rfl⟩ := uqPsi_surjective h F t
  have : g ∈ N := hNtop ▸ Subgroup.mem_top g
  exact this

theorem false_of_uq_toral_deriv (hn : 3 ≤ n) (hp2 : p ≠ 2) (h4 : 4 ≤ p ^ f)
    {r : ℕ} {V Z : Subgroup (MulAut (UqT h n))} (hs : IsSimpleGroup (UqT h n))
    (hnab : ∃ a b : UqT h n, a * b ≠ b * a) (h2 : N2Cfg (UqT h n) r V Z)
    (h3 : N3Deriv (UqT h n) V Z) (F : UqU h n)
    (hF : ∀ v ∈ V, ∃ (x : UqU h n) (d : Fin n → K),
      v = primeFormConjHom h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) x ∧
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((F : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
          ((F : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal d) : False := by
  obtain ⟨hr, -, hVe, hVc, -, -, -, -, -⟩ := id h2
  exact false_of_generation_deriv hs hnab h2 h3
    (uq_generation_deriv h hn hp2 h4 hr V hVc
      (fun v hv => elemPow_eq_one_of_isElementaryAbelian v hv) F hF)

end Pigeon

end CFSG.GH74.GLS.Stage2.Bender.Thm1

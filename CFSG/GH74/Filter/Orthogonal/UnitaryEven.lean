module

public import CFSG.GH74.Filter.Statements
public import CFSG.GH74.Filter.Witness
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Basic
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.GH74.Filter

open CFSG.SectionRank.ClassicalOdd CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary Matrix

section PointRadical

variable {K : Type} [Field K] (σ : K ≃+* K) {m : ℕ}

@[expose] def radPtVec : Fin (m + 2) → K := Fin.cons 1 (Fin.cons 1 0)

@[expose] def tailVec (a : Fin m → K) : Fin (m + 2) → K := Fin.cons 0 (Fin.cons 0 a)

@[expose] def eichF {n : ℕ} (e y : Fin n → K) (c : K) (x : Fin n → K) : Fin n → K :=
  x + herm σ e x • (y + c • e) - herm σ y x • e

theorem herm_radPtVec_radPtVec [CharP K 2] : herm σ (radPtVec : Fin (m + 2) → K) radPtVec = 0 := by
  simp only [radPtVec, herm_cons, map_one, mul_one, herm_zero_left, add_zero]
  exact CharTwo.add_self_eq_zero (1 : K)

theorem herm_radPtVec_tailVec (a : Fin m → K) :
    herm σ (radPtVec : Fin (m + 2) → K) (tailVec a) = 0 := by
  simp [radPtVec, tailVec, herm_cons]

theorem herm_tailVec_radPtVec (a : Fin m → K) :
    herm σ (tailVec a) (radPtVec : Fin (m + 2) → K) = 0 := by
  simp [radPtVec, tailVec, herm_cons]

theorem tailVec_add (a b : Fin m → K) : tailVec (a + b) = tailVec a + tailVec b := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [tailVec]

theorem tailVec_neg (a : Fin m → K) : tailVec (-a) = -tailVec a := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [tailVec]

theorem tailVec_zero : tailVec (0 : Fin m → K) = 0 := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> simp [tailVec]

variable {σ}

theorem eichF_zero {n : ℕ} (e : Fin n → K) (x : Fin n → K) : eichF σ e 0 0 x = x := by
  simp [eichF]

theorem eichF_eichF {n : ℕ} (hσ : ∀ c, σ (σ c) = c) {e y y' : Fin n → K} (he : herm σ e e = 0)
    (hey : herm σ e y = 0) (hey' : herm σ e y' = 0) (c c' : K) (x : Fin n → K) :
    eichF σ e y c (eichF σ e y' c' x) = eichF σ e (y + y') (c + c' - herm σ y y') x := by
  have hye : herm σ y e = 0 := herm_eq_zero_comm σ hσ hey
  simp only [eichF, herm_add_right, herm_sub_right, herm_smul_right, herm_add_left, he, hey', hye,
    mul_zero, add_zero, sub_zero]
  match_scalars <;> ring

theorem trace_mul_valid (hσ : ∀ c, σ (σ c) = c) {n : ℕ} {y y' : Fin n → K} {c c' : K}
    (hc : c + σ c = -herm σ y y) (hc' : c' + σ c' = -herm σ y' y') :
    (c + c' - herm σ y y') + σ (c + c' - herm σ y y') = -herm σ (y + y') (y + y') := by
  have h1 : σ (herm σ y y') = herm σ y' y := (herm_conj σ hσ y y').symm
  simp only [map_sub, map_add, h1, herm_add_left, herm_add_right]
  linear_combination hc + hc'

variable (σ) in
@[expose] def pointRadical [CharP K 2] (hσ : ∀ c, σ (σ c) = c) :
    Subgroup (Multiplicative (Fin m → K) × SUid σ (m + 2)) where
  carrier := {p | ∃ c : K, c + σ c = -herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd) ∧
    ∀ x, p.2 • x = eichF σ radPtVec (tailVec p.1.toAdd) c x}
  one_mem' := ⟨0, by simp [tailVec_zero], fun x => by simp [tailVec_zero, eichF_zero]⟩
  mul_mem' := by
    rintro p q ⟨c, hc, hp⟩ ⟨c', hc', hq⟩
    refine ⟨c + c' - herm σ (tailVec p.1.toAdd) (tailVec q.1.toAdd), ?_, fun x => ?_⟩
    · have := trace_mul_valid hσ hc hc'
      rwa [← tailVec_add] at this
    · show (p.2 * q.2) • x = eichF σ radPtVec (tailVec (p.1.toAdd + q.1.toAdd)) _ x
      rw [mul_smul, hq, hp, tailVec_add,
        eichF_eichF hσ (herm_radPtVec_radPtVec σ) (herm_radPtVec_tailVec σ _)
          (herm_radPtVec_tailVec σ _)]
  inv_mem' := by
    rintro p ⟨c, hc, hp⟩
    have hH : σ (herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd)) =
        herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd) := herm_self_fixed σ hσ _
    refine ⟨-c - herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd), ?_, fun x => ?_⟩
    · simp only [Prod.fst_inv, toAdd_inv, tailVec_neg, herm_neg_left, herm_neg_right, neg_neg]
      rw [map_sub, map_neg, hH]
      linear_combination -hc
    · simp only [Prod.fst_inv, toAdd_inv, Prod.snd_inv]
      symm
      refine (_root_.smul_eq_iff_eq_inv_smul p.2).1 ?_
      rw [hp, eichF_eichF hσ (herm_radPtVec_radPtVec σ) (herm_radPtVec_tailVec σ _)
        (herm_radPtVec_tailVec σ _), tailVec_neg, add_neg_cancel, herm_neg_right]
      have : c + (-c - herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd)) -
          -herm σ (tailVec p.1.toAdd) (tailVec p.1.toAdd) = 0 := by ring
      rw [this, eichF_zero]

end PointRadical

section Witness

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {m : ℕ} [CharP K 2]

noncomputable def radicalToProj (hσ : ∀ c, σ (σ c) = c) :
    pointRadical (m := m) σ hσ →* StatedProj (SUid σ (m + 2)) :=
  (QuotientGroup.mk' _).comp ((MonoidHom.snd _ _).comp (pointRadical (m := m) σ hσ).subtype)

noncomputable def radicalToAdd (hσ : ∀ c, σ (σ c) = c) :
    pointRadical (m := m) σ hσ →* Multiplicative (Fin m → K) :=
  (MonoidHom.fst _ _).comp (pointRadical (m := m) σ hσ).subtype

theorem not_gen4_statedProj_SUid (hσ : IsUnitaryInvolution σ)
    (hcard : 2 ^ 4 < Nat.card (Multiplicative (Fin m → K))) :
    ¬ Gen4 (StatedProj (SUid σ (m + 2))) := by
  refine not_gen4_of_surjection (radicalToProj hσ.invol) (radicalToAdd hσ.invol) ?_
    multiplicative_comm (fun a => pow_char_eq_one (K := K) (p := 2) a) hcard ?_
  · intro a
    obtain ⟨c, hc⟩ := hσ.trace_surj (-herm σ (tailVec a.toAdd) (tailVec a.toAdd))
      (by rw [map_neg, herm_self_fixed σ hσ.invol])
    have he := herm_radPtVec_radPtVec (m := m) σ
    have hey := herm_radPtVec_tailVec (m := m) σ a.toAdd
    exact ⟨⟨(a, eichler hσ.invol he hey hc), c, hc, fun x => eichler_smul hσ.invol he hey hc x⟩,
      rfl⟩
  · intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    obtain ⟨c, hc, hx⟩ := p.2
    have hmem : (p.1.2 : GL (Fin (m + 2)) K) ∈ StatedScalars (Fin (m + 2)) K := by
      have h := hp
      simp only [radicalToProj, MonoidHom.comp_apply, MonoidHom.coe_snd, Subgroup.coe_subtype,
        QuotientGroup.mk'_apply] at h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      exact h
    obtain ⟨u, hu⟩ := hmem
    have hsmul : ∀ x : Fin (m + 2) → K, p.1.2 • x = (u : K) • x := by
      intro x
      rw [smul_def, ← hu, Matrix.GeneralLinearGroup.coe_scalar]
      ext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hee : p.1.2 • (radPtVec : Fin (m + 2) → K) = radPtVec := by
      rw [hx, eichF, herm_radPtVec_radPtVec σ, herm_tailVec_radPtVec σ]
      simp
    have hu1 : (u : K) = 1 := by
      have h0 := congrFun (((hsmul radPtVec).symm).trans hee) 0
      simpa [radPtVec] using h0
    set x₀ : Fin (m + 2) → K := Fin.cons 1 (0 : Fin (m + 1) → K) with hx₀
    have h1 : eichF σ radPtVec (tailVec p.1.1.toAdd) c x₀ = x₀ := by
      rw [← hx x₀, hsmul x₀, hu1, one_smul]
    have e1 : herm σ (radPtVec : Fin (m + 2) → K) x₀ = 1 := by
      simp [radPtVec, hx₀, herm_cons]
    have e2 : herm σ (tailVec p.1.1.toAdd) x₀ = 0 := by
      simp [tailVec, hx₀, herm_cons]
    rw [eichF, e1, e2, one_smul, zero_smul, sub_zero] at h1
    have h2 : tailVec p.1.1.toAdd + c • (radPtVec : Fin (m + 2) → K) = 0 := by
      simpa using h1
    have h3 : p.1.1.toAdd = 0 := by
      funext i
      have := congrFun h2 i.succ.succ
      simpa [tailVec, radPtVec] using this
    exact Multiplicative.toAdd.injective h3


theorem not_gen4_statedProj_of_eq (hσ : IsUnitaryInvolution σ)
    {H : Subgroup (GL (Fin (m + 2)) K)} (hH : SUid σ (m + 2) = H)
    (hcard : 2 ^ 4 < Nat.card (Multiplicative (Fin m → K))) : ¬ Gen4 (StatedProj H) := by
  subst hH
  exact not_gen4_statedProj_SUid hσ hcard

end Witness

theorem t_PSU_even : S_PSU_even := by
  intro G _ _ n f hm h3
  obtain ⟨⟨hp, hf, hn3, hnq⟩, K, _, _, hK, ⟨e⟩⟩ := hm
  have hn3' : 3 ≤ n := hn3
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP K 2 := charP_of_card_sq hK
  have hσ := isUnitaryInvolution_unitaryInvolution hK
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  have hm3 : 3 ≤ f * m := by simpa using h3
  have h4 : 2 * f * m = 2 * (f * m) := by ring
  have hcard : 2 ^ 4 < Nat.card (Multiplicative (Fin m → K)) := by
    rw [card_multiplicative_fun (P := Fin m) hK', Fintype.card_fin]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact not_gen4_of_mulEquiv e.symm
    (not_gen4_statedProj_of_eq hσ (SUid_eq_statedSU hK (m + 2)) hcard)

end CFSG.GH74.Filter

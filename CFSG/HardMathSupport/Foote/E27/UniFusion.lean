module

public import CFSG.HardMathSupport.Foote.E27.UniDiag
public import CFSG.HardMathSupport.Foote.E27.Fusion

public section

namespace CFSG.HardMathSupport.Foote.E27.Uni

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

variable {E : Type} [Field E] {n : ℕ}

theorem pm_conj_dg' (σ : Equiv.Perm (Fin n)) (c : Fin n → Eˣ) :
    pmHom n E σ * dgHom n E c = dgHom n E (c ∘ σ.symm) * pmHom n E σ := by
  have := pm_conj_dg (E := E) σ c
  calc pmHom n E σ * dgHom n E c = (pmHom n E σ * dgHom n E c * (pmHom n E σ)⁻¹) * pmHom n E σ := by
        group
    _ = _ := by rw [this]

theorem cube_dg_pm (σ : Equiv.Perm (Fin n)) (c : Fin n → Eˣ) :
    (dgHom n E c * pmHom n E σ) ^ 3 =
      dgHom n E (c * (c ∘ σ.symm) * (c ∘ σ.symm ∘ σ.symm)) * pmHom n E (σ ^ 3) := by
  have h1 := pm_conj_dg (E := E) σ c
  have h2 := pm_conj_dg (E := E) σ (c ∘ σ.symm)
  have e : (dgHom n E c * pmHom n E σ) ^ 3 =
      dgHom n E c * (pmHom n E σ * dgHom n E c * (pmHom n E σ)⁻¹) *
        (pmHom n E σ * (pmHom n E σ * dgHom n E c * (pmHom n E σ)⁻¹) * (pmHom n E σ)⁻¹) *
        pmHom n E σ ^ 3 := by
    rw [pow_three']
    group
  rw [e, h1, h2, map_pow, map_mul, map_mul]
  rfl

variable (hU : UnitaryFieldData 2 1 E)

theorem cube_mem_Z (c : ↥(prodKer n E)) (σ : Equiv.Perm (Fin n))
    (hz : (dgG hU n c * pmG hU n σ) ^ 3 ∈ Zsc hU n) :
    σ ^ 3 = 1 ∧ ∃ c0 : Eˣ, c0 ^ n = 1 ∧
      ∀ i, c.1 i * c.1 (σ.symm i) * c.1 (σ.symm (σ.symm i)) = c0 := by
  obtain ⟨c0, -, hcn, hc⟩ := hz
  have hcube : (dgHom n E c.1 * pmHom n E σ) ^ 3 =
      Matrix.GeneralLinearGroup.scalar (Fin n) c0 := by
    have h := hc
    rw [Subgroup.coe_pow] at h
    exact h
  rw [cube_dg_pm, ← dgHom_const] at hcube
  have h2 := eq_inv_mul_of_mul_eq hcube
  rw [← map_inv, ← map_mul] at h2
  have hσ3 : σ ^ 3 = 1 := eq_one_of_dg_eq_pm h2.symm
  rw [hσ3, map_one, mul_one] at hcube
  have h3 := dgHom_injective hcube
  refine ⟨hσ3, c0, hcn, fun i => ?_⟩
  exact congrFun h3 i

theorem c0_eq_one_of_coprime (hU : UnitaryFieldData 2 1 E) (hn : Nat.Coprime n 3) {c0 : Eˣ}
    (h : c0 ^ n = 1) : c0 = 1 := by
  have := (pow_gcd_eq_one (a := c0) (m := n) (n := 3)).mpr ⟨h, unit_cube hU c0⟩
  rwa [hn, pow_one] at this

theorem six_orbits : ∀ σ : Equiv.Perm (Fin 6), σ ^ 3 = 1 → (∀ i, σ i ≠ i) →
    ∃ a b : Fin 6, Function.Bijective ![a, σ a, σ (σ a), b, σ b, σ (σ b)] := by
  decide +kernel

theorem c0_eq_one_six (hU : UnitaryFieldData 2 1 E) (c : Fin 6 → Eˣ) (hc : ∏ i, c i = 1)
    (σ : Equiv.Perm (Fin 6)) (hσ : σ ^ 3 = 1) {c0 : Eˣ}
    (hν : ∀ i, c i * c (σ.symm i) * c (σ.symm (σ.symm i)) = c0) : c0 = 1 := by
  by_cases hfix : ∃ j, σ j = j
  · obtain ⟨j, hj⟩ := hfix
    have hj' : σ.symm j = j := by rw [Equiv.symm_apply_eq]; exact hj.symm
    have := hν j
    rw [hj', hj'] at this
    rw [← this, ← pow_three']
    exact unit_cube hU (c j)
  · push Not at hfix
    have hτ3 : (σ⁻¹) ^ 3 = 1 := by rw [inv_pow, hσ, inv_one]
    have hτ : ∀ x, σ⁻¹ x = σ.symm x := fun x => rfl
    have hfix' : ∀ i, σ⁻¹ i ≠ i := by
      intro i h
      apply hfix i
      rw [hτ, Equiv.symm_apply_eq] at h
      exact h.symm
    obtain ⟨a, b, hbij⟩ := six_orbits (σ⁻¹) hτ3 hfix'
    have hprod : ∏ i, c i = ∏ i, c (![a, σ⁻¹ a, σ⁻¹ (σ⁻¹ a), b, σ⁻¹ b, σ⁻¹ (σ⁻¹ b)] i) :=
      (Equiv.prod_comp (Equiv.ofBijective _ hbij) c).symm
    simp only [Fin.prod_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at hprod
    rw [Fin.prod_univ_six] at hc
    have ha := hν a
    have hb := hν b
    simp only [← hτ] at ha hb
    have hsq : c0 * c0 = 1 := by
      calc c0 * c0 = (c a * c (σ⁻¹ a) * c (σ⁻¹ (σ⁻¹ a))) *
            (c b * c (σ⁻¹ b) * c (σ⁻¹ (σ⁻¹ b))) := by rw [ha, hb]
        _ = c a * c (σ⁻¹ a) * c (σ⁻¹ (σ⁻¹ a)) * c b * c (σ⁻¹ b) * c (σ⁻¹ (σ⁻¹ b)) := by
            simp only [mul_assoc]
        _ = 1 := hprod.symm.trans hc
    calc c0 = c0 ^ 3 * (c0 * c0)⁻¹ := by group
      _ = 1 := by rw [unit_cube hU c0, hsq]; simp

theorem det_dgHom (d : Fin n → Eˣ) :
    ((dgHom n E d : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).det = ((∏ i, d i : Eˣ) : E) := by
  rw [dgHom_val, det_diagonal]
  simp [Units.coe_prod]

theorem fusGood_Smono (P : Subgroup (Equiv.Perm (Fin n)))
    (hcube1 : ∀ (c : ↥(prodKer n E)) (σ : Equiv.Perm (Fin n)), σ ∈ P →
      (dgG hU n c * pmG hU n σ) ^ 3 ∈ Zsc hU n → (dgG hU n c * pmG hU n σ) ^ 3 = 1)
    (hA81 : 81 ∣ Nat.card (Amono hU n)) {s : primeFormP hU (1 : Matrix (Fin n) (Fin n) E)}
    (hs : s ∈ Smono hU n P) (h3 : orderOf s = 3) : FusGood (Smono hU n P) s := by
  have hs' : s ∈ (MS hU n P).map (piU hU n) := hs
  obtain ⟨m, hm, rfl⟩ := hs'
  have hm' : m ∈ (SetLike.coe (AtS hU n)) * (SetLike.coe (PtS hU n P)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ (PtS_le_normalizer hU n P)]
    exact hm
  obtain ⟨a, ha, p, hp, rfl⟩ := hm'
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨σ, hσP, rfl⟩ := hp
  set m : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) := dgG hU n c * pmG hU n σ with hmdef
  have hm3 : m ^ 3 ∈ Zsc hU n := by
    have h1 : (piU hU n m) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
    rw [← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hm31 : m ^ 3 = 1 := hcube1 c σ hσP hm3
  have hg3 : ((m : GL (Fin n) E)) ^ 3 = 1 := by
    have := congrArg (fun x : ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E)) => (x : GL (Fin n) E)) hm31
    simpa using this
  have hgu : (((m : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map hU.bar)ᵀ *
      ((m : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = 1 := by
    have := m.2.1
    simpa using this
  obtain ⟨k, hk, d, hkd⟩ := exists_conj_diag hU hgu hg3
  have hdet : ((∏ i, d i : Eˣ) : E) = 1 := by
    have h1 := Matrix.det_units_conj k ((m : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
    have h2 : (((k * (m : GL (Fin n) E) * k⁻¹ : GL (Fin n) E)) : Matrix (Fin n) (Fin n) E) =
        ((dgHom n E d : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by rw [hkd]
    rw [Units.val_mul, Units.val_mul] at h2
    rw [← det_dgHom, ← h2, h1]
    exact m.2.2
  have hprod : (∏ i, d i : Eˣ) = 1 := Units.ext hdet
  have hdmem : d ∈ prodKer n E := by
    change ∏ i, d i = 1
    exact hprod
  have hkU : k ∈ primeFormUnitary hU (1 : Matrix (Fin n) (Fin n) E) := by
    rw [mem_primeFormUnitary]; simpa using hk
  let σk := primeFormConjHom hU (1 : Matrix (Fin n) (Fin n) E) ⟨k, hkU⟩
  have hσk : σk (piU hU n m) = piU hU n (dgG hU n ⟨d, hdmem⟩) := by
    have h := primeFormConjHom_mk hU (1 : Matrix (Fin n) (Fin n) E) ⟨k, hkU⟩ m
    have e : (⟨k * (m : GL (Fin n) E) * ((⟨k, hkU⟩ : primeFormUnitary hU
        (1 : Matrix (Fin n) (Fin n) E)) : GL (Fin n) E)⁻¹,
        conj_mem_gramSU hU (1 : Matrix (Fin n) (Fin n) E) hkU m.2⟩ :
          ↥(gramSU hU (1 : Matrix (Fin n) (Fin n) E))) = dgG hU n ⟨d, hdmem⟩ :=
      Subtype.ext hkd
    rw [e] at h
    exact h
  have hAS : Amono hU n ≤ Smono hU n P := Subgroup.map_mono le_sup_left
  have hmem : σk (piU hU n m) ∈ Amono hU n := by
    rw [hσk]
    exact ⟨_, ⟨⟨d, hdmem⟩, rfl⟩, rfl⟩
  refine ⟨σk, hAS hmem, ?_⟩
  refine hA81.trans (Subgroup.card_dvd_of_le ?_)
  intro y hy
  refine ⟨hAS hy, ?_⟩
  show y ∈ Subgroup.centralizer ({σk (piU hU n m)} : Set (primeFormP hU (1 : Matrix (Fin n) (Fin n) E)))
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Amono_comm hU n _ hy _ hmem

theorem cube_eq_one_of (hc0 : ∀ c : Fin n → Eˣ, ∏ i, c i = 1 → ∀ σ : Equiv.Perm (Fin n),
      σ ^ 3 = 1 → ∀ c0 : Eˣ, c0 ^ n = 1 →
      (∀ i, c i * c (σ.symm i) * c (σ.symm (σ.symm i)) = c0) → c0 = 1)
    (c : ↥(prodKer n E)) (σ : Equiv.Perm (Fin n))
    (hz : (dgG hU n c * pmG hU n σ) ^ 3 ∈ Zsc hU n) :
    (dgG hU n c * pmG hU n σ) ^ 3 = 1 := by
  obtain ⟨hσ3, c0, hcn, hν⟩ := cube_mem_Z hU c σ hz
  have h1 : c0 = 1 := hc0 c.1 (prod_eq_one_of_mem c.2) σ hσ3 c0 hcn hν
  apply Subtype.ext
  change (dgHom n E c.1 * pmHom n E σ) ^ 3 = 1
  have hν1 : c.1 * (c.1 ∘ σ.symm) * (c.1 ∘ σ.symm ∘ σ.symm) = 1 := by
    funext i
    exact (hν i).trans h1
  rw [cube_dg_pm, hν1, hσ3, map_one, map_one, mul_one]

end CFSG.HardMathSupport.Foote.E27.Uni

end

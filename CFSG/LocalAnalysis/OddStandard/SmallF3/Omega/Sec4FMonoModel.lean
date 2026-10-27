module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FMonoDim
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBCent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private lemma sec4F_permVec_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    permVec (σ * τ) v = permVec σ (permVec τ v) :=
  rfl

private lemma sec4F_invDim_eq_six_or_one (hQ : Q.Nondegenerate) {y : ProjOrth Q}
    (hy : HasType y 6 1) {g : OGroup Q} (hg : toProj Q g = y)
    (hfin : Module.finrank (ZMod 3) V = 7) : invDim g = 6 ∨ invDim g = 1 := by
  obtain ⟨-, t, htt, httype, htproj⟩ := hy
  have hmem : g⁻¹ * t ∈ piGroup Q := by
    apply (QuotientGroup.eq_one_iff (N := piGroup Q) (g⁻¹ * t)).mp
    change toProj Q (g⁻¹ * t) = 1
    rw [map_mul, map_inv, hg, htproj, inv_mul_cancel]
  have hdimt : invDim t = 6 := by
    simpa only [invType] using congrArg Prod.fst httype
  rcases (mem_piGroup_iff (Q := Q)).mp hmem with h1 | h1
  · left
    have ht : t = g := by
      have h2 := congrArg (fun z => g * z) h1
      rwa [mul_inv_cancel_left, mul_one] at h2
    rw [← ht]
    exact hdimt
  · right
    have ht : t = g * piOrth Q := by
      have h2 := congrArg (fun z => g * z) h1
      rwa [mul_inv_cancel_left] at h2
    have hgt : g = piOrth Q * t := by
      have h2 : g = t * piOrth Q := by
        rw [ht, mul_assoc, piOrth_mul_self, mul_one]
      exact h2.trans (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) t)
    rw [hgt]
    have hmain : invDim (piOrth Q * t) = Module.finrank (ZMod 3) V - invDim t := by
      simpa only [invType] using congrArg Prod.fst (invType_piOrth_mul hQ htt)
    rw [hmain, hdimt, hfin]

theorem sec4F_mono_model (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q) {a b : Fin 7} (hab : a ≠ b)
    {y : ProjOrth Q} (hy : HasType y 6 1)
    (hact : ∀ v, IsEvenVec v →
      y * sec4IPsi fr v * y⁻¹ = sec4IPsi fr (permVec (Equiv.swap a b) v))
    {v : Fin 7 → ZMod 2} (hv : IsEvenVec v) (hcomm : y * sec4IPsi fr v = sec4IPsi fr v * y)
    (hyv : HasType (y * sec4IPsi fr v) 6 1) :
    v = 0 ∨ v = Pi.single a 1 + Pi.single b 1 := by
  have hfin : Module.finrank (ZMod 3) V = 7 := by
    rw [Module.finrank_eq_card_basis fr.b, Fintype.card_fin]
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  have hswapsq : Equiv.swap a b * Equiv.swap a b = 1 := by
    ext i
    simp [Equiv.Perm.mul_apply]
  have hgN : toProj Q g ∈ Subgroup.normalizer (sec4IB0 fr : Set (ProjOrth Q)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨w, hw, rfl⟩ := (mem_sec4IB0_iff fr).mp hh
      rw [hg, hact w hw]
      exact sec4IPsi_mem_sec4IB0 fr (sec4I_isEvenVec_permVec (Equiv.swap a b) hw)
    · intro hh
      rw [hg] at hh
      obtain ⟨w', hw', hw'eq⟩ := (mem_sec4IB0_iff fr).mp hh
      refine ⟨permVec (Equiv.swap a b) w',
        sec4I_isEvenVec_permVec (Equiv.swap a b) hw', ?_⟩
      have hconj : y * sec4IPsi fr (permVec (Equiv.swap a b) w') * y⁻¹ =
          sec4IPsi fr w' := by
        rw [hact (permVec (Equiv.swap a b) w')
          (sec4I_isEvenVec_permVec (Equiv.swap a b) hw')]
        congr 1
        funext i
        simp [permVec]
      calc sec4IPsi fr (permVec (Equiv.swap a b) w')
          = y⁻¹ * (y * sec4IPsi fr (permVec (Equiv.swap a b) w') * y⁻¹) * y := by
            group
        _ = y⁻¹ * (y * h * y⁻¹) * y := by rw [hconj, hw'eq]
        _ = h := by group
  obtain ⟨σ, u, hgu⟩ := sec4I_mono_of_normalizes_B0 hQ fr hgN
  have hproj : toProj Q (sec4IMono fr σ u) = y := by rw [← hgu, hg]
  have hσ : σ = Equiv.swap a b := by
    have hfix : ∀ w : Fin 7 → ZMod 2, IsEvenVec w →
        permVec ((Equiv.swap a b)⁻¹ * σ) w = w := by
      intro w hw
      have heq : sec4IPsi fr (permVec σ w) = sec4IPsi fr (permVec (Equiv.swap a b) w) := by
        rw [← sec4IPsi_conj_mono fr σ u w, hproj, hact w hw]
      have hperm : permVec σ w = permVec (Equiv.swap a b) w :=
        sec4IPsi_injOn fr (sec4I_isEvenVec_permVec σ hw)
          (sec4I_isEvenVec_permVec (Equiv.swap a b) hw) heq
      have h3 : permVec (Equiv.swap a b)⁻¹ (permVec σ w) = w := by
        rw [hperm, ← sec4F_permVec_mul, inv_mul_cancel]
        rfl
      rw [sec4F_permVec_mul]
      exact h3
    have hτ : (Equiv.swap a b)⁻¹ * σ = 1 := sec4I_perm_eq_one_of_fix _ hfix
    calc σ = Equiv.swap a b * ((Equiv.swap a b)⁻¹ * σ) := (mul_inv_cancel_left _ _).symm
      _ = Equiv.swap a b * 1 := by rw [hτ]
      _ = Equiv.swap a b := mul_one _
  have hmem : g * g ∈ piGroup Q := by
    obtain ⟨-, t, htt, -, htproj⟩ := hy
    have hyy : y * y = 1 := by rw [← htproj, ← map_mul, htt, map_one]
    apply (QuotientGroup.eq_one_iff (N := piGroup Q) (g * g)).mp
    change toProj Q (g * g) = 1
    rw [map_mul, hg, hyy]
  have hgg : g * g = sec4IMono fr 1 (fun i => u i + u (Equiv.swap a b i)) := by
    rw [hgu, hσ, sec4IMono_mul, hswapsq]
  have huab : u a = u b := by
    have hself : ∀ x : ZMod 2, x + x = 0 := by decide
    rcases (mem_piGroup_iff (Q := Q)).mp hmem with h1 | h2
    · have hf : (fun i => u i + u (Equiv.swap a b i)) = 0 := by
        have hEq : sec4IMono fr 1 (fun i => u i + u (Equiv.swap a b i)) =
            sec4IMono fr 1 0 := by
          rw [← hgg, h1, sec4IMono_one]
        exact (sec4IMono_injective fr hEq).2
      have hfa : u a + u b = 0 := by
        have := congrFun hf a
        simpa [Equiv.swap_apply_left] using this
      have hcancel : u a + u b = u b + u b := by rw [hfa, hself (u b)]
      exact add_right_cancel hcancel
    · exfalso
      have hf : (fun i => u i + u (Equiv.swap a b i)) = sec4IOnes := by
        have hEq : sec4IMono fr 1 (fun i => u i + u (Equiv.swap a b i)) =
            sec4IMono fr 1 sec4IOnes := by
          rw [← hgg, h2, ← sec4IT_ones fr]
          rfl
        exact (sec4IMono_injective fr hEq).2
      obtain ⟨k, hka, hkb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by decide : 2 < 7)
      have hk := congrFun hf k
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb, hself (u k)] at hk
      exact one_ne_zero (by simpa only [sec4IOnes] using hk.symm)
  have hvab : v a = v b := by
    have hconj : y * sec4IPsi fr v * y⁻¹ = sec4IPsi fr v := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have heq : sec4IPsi fr (permVec (Equiv.swap a b) v) = sec4IPsi fr v := by
      rw [← hact v hv, hconj]
    have hperm : permVec (Equiv.swap a b) v = v :=
      sec4IPsi_injOn fr (sec4I_isEvenVec_permVec (Equiv.swap a b) hv) hv heq
    have h1 : (permVec (Equiv.swap a b) v) a = v a := congrFun hperm a
    rw [permVec, Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_left] at h1
    exact h1.symm
  have hgdim : invDim g = 1 + sec4FOffCount a b u := by
    rw [hgu, hσ]
    exact sec4F_invDim_mono_swap fr hab huab
  have h1 : sec4FOffCount a b u = 0 ∨ sec4FOffCount a b u = 5 := by
    rcases sec4F_invDim_eq_six_or_one hQ hy hg hfin with h | h
    · right
      rw [hgdim] at h
      omega
    · left
      rw [hgdim] at h
      omega
  have hg' : g * sec4IT fr v = sec4IMono fr (Equiv.swap a b) (u + v) := by
    rw [hgu, hσ, sec4IT, sec4IMono_mul, mul_one]
    congr 1
    funext i
    show v i + u i = u i + v i
    exact add_comm _ _
  have hg'proj : toProj Q (g * sec4IT fr v) = y * sec4IPsi fr v := by
    rw [map_mul, hg]
    rfl
  have huvab : (u + v) a = (u + v) b := by
    simp only [Pi.add_apply]
    rw [huab, hvab]
  have hg'dim : invDim (g * sec4IT fr v) = 1 + sec4FOffCount a b (u + v) := by
    rw [hg']
    exact sec4F_invDim_mono_swap fr hab huvab
  have h2 : sec4FOffCount a b (u + v) = 0 ∨ sec4FOffCount a b (u + v) = 5 := by
    rcases sec4F_invDim_eq_six_or_one hQ hyv hg'proj hfin with h | h
    · right
      rw [hg'dim] at h
      omega
    · left
      rw [hg'dim] at h
      omega
  exact sec4F_mono_count hab hv hvab h1 h2

end CFSG.OddStandard.SmallF3.Omega

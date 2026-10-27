module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.EightNormalizer

public section

namespace CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

open Equiv Equiv.Perm CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

theorem mem_alternatingGroup_of_mem_pCore_perm_four {σ : Perm (Fin 4)}
    (hσ : σ ∈ CFSG.pCore 2 (Perm (Fin 4))) : σ ∈ alternatingGroup (Fin 4) := by
  by_contra hodd
  have hs : sign σ = -1 := by
    rcases Int.units_eq_one_or (sign σ) with h | h
    · exact absurd (mem_alternatingGroup.2 h) hodd
    · exact h
  have hdec : ∀ σ : Perm (Fin 4), sign σ = -1 → ∃ τ : Perm (Fin 4),
      (σ * τ * σ⁻¹ * τ⁻¹) ^ 3 = 1 ∧ σ * τ * σ⁻¹ * τ⁻¹ ≠ 1 := by decide +kernel
  obtain ⟨τ, h3, h1⟩ := hdec σ hs
  set K := CFSG.pCore 2 (Perm (Fin 4)) with hK
  have hx : σ * τ * σ⁻¹ * τ⁻¹ ∈ K := by
    have : τ * σ⁻¹ * τ⁻¹ ∈ K := (CFSG.pCore_normal (p := 2)).conj_mem σ⁻¹ (K.inv_mem hσ) τ
    simpa [mul_assoc] using K.mul_mem hσ this
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Perm (Fin 4))) ⟨_, hx⟩
  have hk' : (σ * τ * σ⁻¹ * τ⁻¹) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd1 : orderOf (σ * τ * σ⁻¹ * τ⁻¹) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (σ * τ * σ⁻¹ * τ⁻¹) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd1 hcop) hd2
  exact h1 (orderOf_eq_one_iff.mp this)

theorem exists_sumCongr_of_normal_isPGroup {r s : ℕ} (hr : r = 1 ∨ r = 3 ∨ 5 ≤ r)
    (U : Subgroup (Perm (OmegaE r s))) (hU : IsPGroup 2 U)
    (hUN : ∀ g ∈ U, g ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))))
    (hnorm : ∀ h ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))), ∀ u ∈ U,
      h * u * h⁻¹ ∈ U) :
    ∀ u ∈ U, ∃ σ₁ ∈ blockFix (Fin r), ∃ σ₂ ∈ CFSG.pCore 2 (Perm (Fin s)),
      u = Perm.sumCongr σ₁ σ₂ := by
  classical
  let ι : ↥(wStab (Fin r) Bool) × Perm (Fin s) →* Perm (OmegaE r s) :=
    (Perm.sumCongrHom (Fin r × Bool) (Fin s)).comp
      (MonoidHom.prodMap (wStab (Fin r) Bool).subtype (MonoidHom.id _))
  have hι : ∀ x, ι x = Perm.sumCongr x.1.1 x.2 := fun x => rfl
  have hιinj : Function.Injective ι := by
    intro x y h
    have h1 := Perm.sumCongrHom_injective (α := Fin r × Bool) (β := Fin s)
      (show Perm.sumCongrHom (Fin r × Bool) (Fin s) (x.1.1, x.2) =
        Perm.sumCongrHom (Fin r × Bool) (Fin s) (y.1.1, y.2) from h)
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.snd h1
    exact Prod.ext (Subtype.ext e1) e2
  have hιN : ∀ x, ι x ∈ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := fun x => by
    rw [hι]; exact sumCongr_mem_normalizer x.1.2 x.2
  let Uh : Subgroup (↥(wStab (Fin r) Bool) × Perm (Fin s)) := U.comap ι
  have hUh2 : IsPGroup 2 Uh := hU.comap_of_injective ι hιinj
  have hUhn : Uh.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ι (g * n * g⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ (hιN g) _ hn
  let Φ1 : ↥(wStab (Fin r) Bool) × Perm (Fin s) →* Perm (Fin r) :=
    (wStabAction (Fin r)).comp (MonoidHom.fst _ _)
  have hΦ1 : Function.Surjective Φ1 := by
    intro π
    refine ⟨(⟨wLift π, wLift_mem_wStab π⟩, 1), ?_⟩
    refine Equiv.ext fun a => ?_
    have := wStabAction_apply (ι := Fin r) ⟨wLift π, wLift_mem_wStab π⟩ (a, false)
    show wStabAction (Fin r) ⟨wLift π, wLift_mem_wStab π⟩ a = π a
    simpa [wLift_apply] using this
  have hΦ2 : Function.Surjective (MonoidHom.snd ↥(wStab (Fin r) Bool) (Perm (Fin s))) :=
    fun b => ⟨(1, b), rfl⟩
  have hle1 : Uh.map Φ1 ≤ CFSG.pCore 2 (Perm (Fin r)) :=
    le_sSup ⟨Subgroup.Normal.map hUhn Φ1 hΦ1, hUh2.map Φ1⟩
  have hle2 : Uh.map (MonoidHom.snd _ _) ≤ CFSG.pCore 2 (Perm (Fin s)) :=
    le_sSup ⟨Subgroup.Normal.map hUhn _ hΦ2, hUh2.map _⟩
  rw [pCore_perm_eq_bot (by omega)] at hle1
  intro u hu
  obtain ⟨σ1, h1, σ2, rfl⟩ := mem_normalizer_Wr_iff.1 (hUN u hu)
  have hx : (⟨σ1, h1⟩, σ2) ∈ Uh := by
    show ι (⟨σ1, h1⟩, σ2) ∈ U
    rw [hι]; exact hu
  refine ⟨σ1, ?_, σ2, ?_, rfl⟩
  · have h0 : Φ1 (⟨σ1, h1⟩, σ2) = 1 := by
      have : Φ1 (⟨σ1, h1⟩, σ2) ∈ (⊥ : Subgroup _) := hle1 ⟨_, hx, rfl⟩
      simpa using this
    intro p
    have h4 : wStabAction (Fin r) ⟨σ1, h1⟩ = 1 := h0
    have h3 := wStabAction_apply (ι := Fin r) ⟨σ1, h1⟩ p
    rw [h4] at h3
    exact h3.symm
  · exact hle2 ⟨_, hx, rfl⟩

theorem exists_threeCycle_not_mem_normalizer_Wr {r s : ℕ} (hr : 3 ≤ r) :
    ∃ c : Perm (OmegaE r s), c ∈ alternatingGroup (OmegaE r s) ∧ c ^ 3 = 1 ∧
      (∃ T : Finset (OmegaE r s), T.card ≤ 3 ∧ (∀ x ∈ T, ∃ p, x = Sum.inl p) ∧ ∀ x ∉ T, c x = x) ∧
      c ∉ Subgroup.normalizer (Wr r s : Set (Perm (OmegaE r s))) := by
  classical
  let a : Fin 3 → OmegaE r s := fun i => Sum.inl (⟨i.1, by omega⟩, false)
  let b0 : OmegaE r s := Sum.inl (⟨0, by omega⟩, true)
  have ha : ∀ i j : Fin 3, a i = a j → i = j := by
    intro i j h
    simp only [a, Sum.inl.injEq, Prod.mk.injEq, and_true, Fin.mk.injEq] at h
    exact Fin.ext h
  have h01 : a 0 ≠ a 1 := fun h => by simpa using ha _ _ h
  have h02 : a 0 ≠ a 2 := fun h => by simpa using ha _ _ h
  have h12 : a 1 ≠ a 2 := fun h => by simpa using ha _ _ h
  have hb : ∀ i, b0 ≠ a i := fun i h => by simp [a, b0] at h
  have hinr : ∀ (j : Fin s) i, (Sum.inr j : OmegaE r s) ≠ a i := fun j i h => by simp [a] at h
  let c : Perm (OmegaE r s) := swap (a 0) (a 1) * swap (a 1) (a 2)
  have hc : ∀ x, c x = swap (a 0) (a 1) (swap (a 1) (a 2) x) := fun x => rfl
  have hfix : ∀ x, x ≠ a 0 → x ≠ a 1 → x ≠ a 2 → c x = x := fun x h0 h1 h2 => by
    rw [hc, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h0 h1]
  have c0 : c (a 0) = a 1 := by rw [hc, swap_apply_of_ne_of_ne h01 h02, swap_apply_left]
  have c1 : c (a 1) = a 2 := by
    rw [hc, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm h02) (Ne.symm h12)]
  have c2 : c (a 2) = a 0 := by
    rw [hc, swap_apply_right, swap_apply_right]
  refine ⟨c, ?_, ?_, ⟨{a 0, a 1, a 2}, Finset.card_le_three, fun x hx => ?_, fun x hx => ?_⟩, ?_⟩
  · rw [mem_alternatingGroup, Perm.sign_mul, sign_swap h01, sign_swap h12]; decide
  · ext x
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
    by_cases x0 : x = a 0
    · subst x0; rw [c0, c1, c2]
    by_cases x1 : x = a 1
    · subst x1; rw [c1, c2, c0]
    by_cases x2 : x = a 2
    · subst x2; rw [c2, c0, c1]
    rw [hfix x x0 x1 x2, hfix x x0 x1 x2, hfix x x0 x1 x2]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hfix x hx.1 hx.2.1 hx.2.2
  · intro hN
    obtain ⟨σ1, h1, σ2, hcc⟩ := mem_normalizer_Wr_iff.1 hN
    have e1 : c (a 0) = a 1 := by
      rw [hc, swap_apply_of_ne_of_ne h01 h02, swap_apply_left]
    have e2 : c b0 = b0 := by
      rw [hc, swap_apply_of_ne_of_ne (hb 1) (hb 2), swap_apply_of_ne_of_ne (hb 0) (hb 1)]
    rw [hcc] at e1 e2
    have e1' : σ1 (⟨0, by omega⟩, false) = (⟨1, by omega⟩, false) := by
      simpa [a, Perm.sumCongr_apply] using e1
    have e2' : σ1 (⟨0, by omega⟩, true) = (⟨0, by omega⟩, true) := by
      simpa [b0, Perm.sumCongr_apply] using e2
    have := (mem_wStab.1 h1) (⟨0, by omega⟩, false) (⟨0, by omega⟩, true)
    rw [e1', e2'] at this
    simp at this

end CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure

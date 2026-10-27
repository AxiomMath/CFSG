module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8FrameJ0

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

open CFSG.Open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.EvenSmallLie.OmegaEightMinus

theorem psi_ok :
    (∀ σ τ : Equiv.Perm (Fin 5),
        eqA 136 (psiArr (σ * τ)) (compA 136 (psiArr σ) (psiArr τ)) = true) ∧
      (∀ σ : Equiv.Perm (Fin 5), isInvA 136 (psiArr σ) (invCand 136 (psiArr σ)) = true) ∧
      (∀ σ : Equiv.Perm (Fin 5),
        eqA 136 (compA 136 (psiArr σ) betaArrs[0]!) (compA 136 betaArrs[0]! (psiArr σ)) = true) ∧
      (∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 →
        siftA 136 omegaLevels (omegaBase.map Fin.val).toArray 0 (psiArr σ) = true) ∧
      eqA 136 (psiArr (Equiv.swap 0 1 * Equiv.swap 1 2)) (idA 136) = false := by
  have h := (Certificates.certificate9490).2.2.2
  simp only [psiCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', and_assoc] at h
  exact h

@[expose] def psiP (σ : Equiv.Perm (Fin 5)) : Equiv.Perm (Fin 136) := permOfArr 136 (psiArr σ)

theorem rep_psi (σ : Equiv.Perm (Fin 5)) :
    Rep 136 (psiArr σ) (psiP σ) :=
  (rep_permOfArr (psi_ok.2.1 σ)).1

theorem psiP_mul (σ τ : Equiv.Perm (Fin 5)) :
    psiP (σ * τ) = psiP σ * psiP τ :=
  eq_of_eqA (rep_psi (σ * τ)) (rep_compA (rep_psi σ) (rep_psi τ)) (psi_ok.1 σ τ)

@[expose] def psiHom :
    Equiv.Perm (Fin 5) →* Equiv.Perm (Fin 136) where
  toFun := psiP
  map_one' := by
    have h : psiP 1 * psiP 1 = psiP 1 * 1 := by rw [mul_one, ← psiP_mul, one_mul]
    exact mul_left_cancel h
  map_mul' := psiP_mul

@[expose] def psiA :
    alternatingGroup (Fin 5) →* Equiv.Perm (Fin 136) :=
  psiHom.comp (alternatingGroup (Fin 5)).subtype

theorem threeCycle_mem :
    (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem psiA_injective : Function.Injective psiA := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker psiA) with h | h
  · exact h
  · exfalso
    have hmem : (⟨_, threeCycle_mem⟩ : alternatingGroup (Fin 5)) ∈ MonoidHom.ker psiA := by
      rw [h]
      exact Subgroup.mem_top _
    have h1 : psiP (Equiv.swap 0 1 * Equiv.swap 1 2) = 1 := hmem
    have h2 := psi_ok.2.2.2.2
    rw [← Bool.not_eq_true, eqA_iff (rep_psi _) rep_idA] at h2
    exact h2 h1

@[expose] def W0 : Subgroup (Equiv.Perm (Fin 136)) := psiA.range

@[expose] def W0Equiv : alternatingGroup (Fin 5) ≃* W0 :=
  MonoidHom.ofInjective psiA_injective

@[expose] def HasW (x : Equiv.Perm (Fin 136)) : Prop :=
  ∃ W : Subgroup (Equiv.Perm (Fin 136)), W ≤ omegaT ⊓ Subgroup.centralizer ({x} : Set _) ∧
    IsSimpleGroup W ∧ (∃ a b : W, a * b ≠ b * a) ∧ 3 ∣ Nat.card W

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  have h := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin] at h
  simp only [Nat.factorial] at h
  omega

theorem hasW_beta_zero :
    HasW (betaP 0) := by
  refine ⟨W0, ?_, W0Equiv.symm.isSimpleGroup, ?_, ?_⟩
  · rintro _ ⟨⟨σ, hσ⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨mem_omegaT_of_sift (rep_psi σ) (psi_ok.2.2.2.1 σ hσ), ?_⟩
    have hψ : psiA ⟨σ, hσ⟩ = psiP σ := rfl
    have h0 : (0 : ℕ) < 3 := by norm_num
    have hc : psiP σ * betaP 0 = betaP 0 * psiP σ :=
      eq_of_eqA (rep_compA (rep_psi σ) (rep_beta h0)) (rep_compA (rep_beta h0) (rep_psi σ))
        (psi_ok.2.2.1 σ)
    rw [Subgroup.mem_centralizer_singleton_iff, hψ]
    exact hc
  · set a : alternatingGroup (Fin 5) := ⟨_, threeCycle_mem⟩
    have hb : (Equiv.swap (1 : Fin 5) 2 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide
    set b : alternatingGroup (Fin 5) := ⟨_, hb⟩
    refine ⟨W0Equiv a, W0Equiv b, fun h => ?_⟩
    rw [← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (W0Equiv.injective h)
    have hne : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) * (Equiv.swap 1 2 * Equiv.swap 2 3) ≠
        (Equiv.swap 1 2 * Equiv.swap 2 3) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
    exact hne h'
  · rw [← Nat.card_congr W0Equiv.toEquiv, card_alternatingGroup_five]
    norm_num

theorem hasW_conj {x g : Equiv.Perm (Fin 136)} (hx : HasW x)
    (hg : g ∈ omegaT) : HasW (g * x * g⁻¹) := by
  obtain ⟨W, hW, hs, ⟨a, b, hab⟩, h3⟩ := hx
  let e : W ≃* W.map (MulAut.conj g).toMonoidHom :=
    W.equivMapOfInjective _ (MulAut.conj g).injective
  refine ⟨W.map (MulAut.conj g).toMonoidHom, ?_, e.symm.isSimpleGroup, ⟨e a, e b, ?_⟩, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyo, hyc⟩ := Subgroup.mem_inf.1 (hW hy)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · change g * y * g⁻¹ ∈ omegaT
      exact omegaT.mul_mem (omegaT.mul_mem hg hyo) (omegaT.inv_mem hg)
    · rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
      change g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hyc]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  · intro h
    rw [← map_mul, ← map_mul] at h
    exact hab (e.injective h)
  · rw [← Nat.card_congr e.toEquiv]
    exact h3

theorem hasW_inv {x : Equiv.Perm (Fin 136)} (hx : HasW x) : HasW x⁻¹ := by
  obtain ⟨W, hW, hrest⟩ := hx
  refine ⟨W, fun y hy => Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (hW hy)).1, ?_⟩, hrest⟩
  have h := (Subgroup.mem_inf.1 (hW hy)).2
  rw [Subgroup.mem_centralizer_singleton_iff] at h ⊢
  calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
    _ = x⁻¹ * (y * x) * x⁻¹ := by rw [← h]
    _ = x⁻¹ * y := by group

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Omega8Frame

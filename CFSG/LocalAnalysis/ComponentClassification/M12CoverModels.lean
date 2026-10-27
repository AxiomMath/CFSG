module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsBeta
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverModelsGroups
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverSylowSplit

public section

namespace CFSG.ComponentClassification.M12Cover.InternalSylow

open CFSG.Blueprint CFSG.ComponentClassification.CentralCover

@[expose] noncomputable def equivNative : S ≃* M12Cover.S :=
  (MulEquiv.subgroupCongr S_eq_map).trans
    (((M12Cover.S.subgroupOf NativeSporadic.M12).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe S_le_M12))

theorem involutionCocyclesSplit : InvolutionCocyclesSplit S :=
  involutionCocyclesSplit_S.of_mulEquiv equivNative

theorem f_class_unique (f' : NormCocycle S) (hd : ∀ q : S, orderOf q = 2 → f' q q = f q q) :
    ∃ ν : S → ZMod 2, ∀ s t, f' s t = f s t + ν s + ν t + ν (s * t) := by
  obtain ⟨ν, hν⟩ := involutionCocyclesSplit (fun s t => f' s t + f s t)
    (fun t => by simp [f'.map_one_left, f_one_left]) (fun s => by
      simp [f'.map_one_right, f_one_right])
    (fun s t u => by
      have h1 := f'.cocycle s t u
      have h2 := f_cocycle s t u
      grind)
    (fun q hq => by rw [hd q hq]; exact zmod2_add_self _)
  refine ⟨ν, fun s t => ?_⟩
  have := hν s t
  have h := zmod2_add_self (f s t)
  grind

theorem transport_beta {E : Type*} [Group E] [Group.IsPerfect E]
    {π : E →* NativeSporadic.M12} {z : E} (hπ : IsCentralDoubleExt π z) (ι : S.comap π ≃* R)
    (hι : ∀ x, ((ι x).snd : NativeSporadic.M12) = π x) :
    ∃ ι' : S.comap π ≃* R, (∀ x : S.comap π, ((ι' x).snd : NativeSporadic.M12) = π x) ∧
      ((ι'.symm ⟨1, 1⟩ : S.comap π) : E) = z ∧
      ∀ φ : E ≃* E, (∀ x, π (φ x) = beta (π x)) →
        ∀ (x : E) (hx : π x ∈ S) (hφx : π (φ x) ∈ S), ι' ⟨φ x, hφx⟩ = tau (ι' ⟨x, hx⟩) := by
  have hodd : Odd (Fintype.card (Fin 1485)) := by
    rw [Fintype.card_fin]
    decide
  obtain ⟨-, -, -, -, -, -, Ψ, -, -, -, ι', hι', hz, -, hact⟩ :=
    isRightTransversal.odd_index_central_double_cover_transfer_and_automorphism_transport hodd
      tau0_snd mu transfer₂_add_coboundary_mu hπ ι hι
  refine ⟨ι', fun x => by rw [hι'], hz, fun φ hφ x hx hφx => ?_⟩
  rw [hact φ hφ x hx hφx, restrictAut_eq_tau]

theorem ctss_m12_internal_sylow_transfer_models_and_center_root_counts :
    ((∃ P : Sylow 2 NativeSporadic.M12, (P : Subgroup NativeSporadic.M12) = S) ∧
      Nat.card S = 64 ∧ d 0 = 1 ∧ Function.Bijective d ∧
      (List.ofFn fun j : Fin 64 => imageArray (dPerm j)).Pairwise (· < ·) ∧
      (∀ i j, d (mTab i j) = d i * d j) ∧
      (∀ j, beta (d j : NativeSporadic.M12) = d (bTab j)) ∧ S.map beta.toMonoidHom = S) ∧
    ((∀ s : S, s ∈ Subgroup.center S ↔ s = 1 ∨ s = d 27) ∧
      imageArray (dPerm 27) = [3, 6, 9, 0, 4, 5, 1, 8, 7, 2, 10, 11] ∧ orderOf (d 27) = 2 ∧
      (Finset.univ.filter fun p : Fin 12 => dPerm 27 p = p).card = 4) ∧
    (((∀ t, f 1 t = 0) ∧ (∀ s, f s 1 = 0) ∧
        ∀ s t w, f s t + f (s * t) w = f t w + f s (t * w)) ∧
      ∀ q : S, orderOf q = 2 →
        ((Finset.univ.filter fun p : Fin 12 =>
            ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 4 ∧ f q q = 0) ∨
        ((Finset.univ.filter fun p : Fin 12 =>
            ((q : NativeSporadic.M12) : Equiv.Perm (Fin 12)) p = p).card = 0 ∧ f q q = 1)) ∧
    (IsTableModel star encR ∧ (∀ x, encR (tau0F x) = tau0 (encR x)) ∧
      (∀ x, encR (tauF x) = tau (encR x)) ∧ (∀ x, tau0 (tau0 x) = x) ∧ (∀ x, tau (tau x) = x) ∧
      tau0 (encR 64) = encR 64 ∧ tau (encR 64) = encR 64 ∧
      (∀ x : R, ((tau0 x).snd : NativeSporadic.M12) = beta x.snd) ∧
      ∀ x : R, ((tau x).snd : NativeSporadic.M12) = beta x.snd) ∧
    ((∀ i, r i = g * r0 i * g⁻¹) ∧ r 0 = 1 ∧ IsRightTransversal S r ∧
      Function.Bijective (fun x : Fin 64 × Fin 1485 => (d x.1 : NativeSporadic.M12) * r x.2) ∧
      (∀ i (h : S), r i * h = pS i h * r (iS i h)) ∧
      (∀ i (h : S), isRightTransversal.coef i h = pS i h ∧ isRightTransversal.act i h = iS i h) ∧
      (∀ i, beta (r i) = aS i * r (σI i)) ∧ Function.Bijective σI ∧
      (∀ i, isRightTransversal.autCoef beta i = aS i ∧
        isRightTransversal.autIndex beta i = σI i) ∧
      ∀ i (h : S), (A i)⁻¹ * tau0 ⟨0, pS i h⟩ * A (iS i h) = ⟨coef i h, pS (σI i) (βS h)⟩) ∧
    ((∀ h k : S, F h k = isRightTransversal.transfer₂ f h k) ∧
      (∀ h : S, Λ h = isRightTransversal.transportSum beta tau0 h) ∧
      (∀ h k : S, F h k + mu h + mu k + mu (h * k) = f h k) ∧
      (∀ h : S, lam h = Λ h + mu h + mu (βS h)) ∧
      isRightTransversal.restrictAut tau0_snd mu transfer₂_add_coboundary_mu = tau) ∧
    (Nat.card R = 128 ∧ (∀ ε, Nat.card (T ε) = 256) ∧
      (∀ ε : ZMod 2, IsTableModel (tmul ε.val) (encT ε)) ∧
      (∀ w : R, w ∈ Subgroup.center R ↔ w = encR 0 ∨ w = encR 27 ∨ w = encR 64 ∨ w = encR 91) ∧
      (∀ ε : ZMod 2, ∀ w : T ε, w ∈ Subgroup.center (T ε) ↔
        w = encT ε 0 ∨ w = encT ε 27 ∨ w = encT ε 64 ∨ w = encT ε 91) ∧
      (IsElementaryAbelian 2 (Subgroup.center R) ∧ Nat.card (Subgroup.center R) = 4) ∧
      ∀ ε : ZMod 2, IsElementaryAbelian 2 (Subgroup.center (T ε)) ∧
        Nat.card (Subgroup.center (T ε)) = 4) ∧
    (((rootCount 2 (encR 27), rootCount 4 (encR 27)) = (0, 0) ∧
        (rootCount 2 (encR 64), rootCount 4 (encR 64)) = (24, 0) ∧
        (rootCount 2 (encR 91), rootCount 4 (encR 91)) = (24, 32)) ∧
      ((rootCount 2 (encT 0 27), rootCount 4 (encT 0 27)) = (0, 0) ∧
        (rootCount 2 (encT 0 64), rootCount 4 (encT 0 64)) = (24, 32) ∧
        (rootCount 2 (encT 0 91), rootCount 4 (encT 0 91)) = (40, 32)) ∧
      ((rootCount 2 (encT 1 27), rootCount 4 (encT 1 27)) = (16, 0) ∧
        (rootCount 2 (encT 1 64), rootCount 4 (encT 1 64)) = (40, 32) ∧
        (rootCount 2 (encT 1 91), rootCount 4 (encT 1 91)) = (24, 32))) ∧
    ((∀ φ : MulAut R, ∀ w ∈ Subgroup.center R, φ w = w) ∧
      ∀ ε : ZMod 2, ∀ φ : MulAut (T ε), ∀ w ∈ Subgroup.center (T ε), φ w = w) := by
  refine ⟨⟨exists_sylow_eq_S, card_S, d_zero, d_bijective, sorted_imageArray, d_mul, beta_d,
    beta_map_S⟩, ⟨mem_center_iff, imageArray_d27, orderOf_d27, card_fixed_d27⟩,
    ⟨⟨f_one_left, f_one_right, f_cocycle⟩, f_diag⟩, ⟨isTableModel_star, encR_tau0F, encR_tauF,
    tau0_tau0, tau_tau, by rw [encR_64, tau0_z], by rw [encR_64, tau_z], tau0_snd, tau_snd⟩,
    ⟨fun _ => rfl, r_zero, isRightTransversal, bijective_d_mul_r, r_mul,
    fun i h => ⟨coef_eq i h, act_eq i h⟩, beta_r, σI_bijective,
    fun i => ⟨autCoef_eq i, autIndex_eq i⟩, A_conj⟩,
    ⟨fun _ _ => rfl, fun h => (transportSum_eq h).symm, F_add_mu, lam_eq, restrictAut_eq_tau⟩,
    ⟨card_R, card_T, isTableModel_tmul, mem_center_R, mem_center_T,
    center_R_elementary, center_T_elementary⟩, ⟨rootCounts_R, rootCounts_T0, rootCounts_T1⟩,
    ⟨aut_fixes_center_R, aut_fixes_center_T⟩⟩

end CFSG.ComponentClassification.M12Cover.InternalSylow

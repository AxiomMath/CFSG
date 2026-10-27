module

public import CFSG.CharacterTheory.Semidihedral.Principal.SignSymmetricFivePowerInvolutionSumSupport

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers SignSymmetric Equiv

universe u

theorem sign_symmetric_five_power_normalizer_generator_column_involution_sum
    {H : Type u} [Group H] [Fintype H] (a : ℕ) (_ha : 1 ≤ a) (W E : Subgroup H) [W.Normal]
    [IsCyclic W] (hWcard : Nat.card W = 5 ^ a) (hWE : W ⊔ E = ⊤) (hdisj : W ⊓ E = ⊥)
    (σ : E ≃* Perm (Fin 5))
    (hact : ∀ (e : E), ∀ w ∈ W, (e : H) * w * (e : H)⁻¹ =
      w ^ ((Perm.sign (σ e) : ℤˣ) : ℤ))
    (basisH : FiniteIrreducibleCharacterBasis H) (lam : W →* ℂˣ) (hlam : orderOf lam = 5) :
    let J : Subgroup H := ((alternatingGroup (Fin 5)).comap σ.toMonoidHom).map E.subtype
    let K : Subgroup H := W ⊔ J
    let θ : J → ℂ := fun j => (Nat.card (MulAction.fixedBy (Sylow 5 J) j) : ℂ) - 1
    (∀ basisJ : FiniteIrreducibleCharacterBasis J,
      (∃ l : basisJ.index, (basisJ.representation l).character = θ) ∧
      ∀ l : basisJ.index, Module.finrank ℂ (basisJ.representation l).vector = 5 →
        (basisJ.representation l).character = θ) ∧
    θ 1 = 5 ∧
    (∃ ψ : K → ℂ, ∀ (k : K) (w : W) (j : J), (k : H) = w * j →
      ψ k = θ j * ((lam w : ℂ) - 1)) ∧
    ∀ ψ : K → ℂ, (∀ (k : K) (w : W) (j : J), (k : H) = w * j →
      ψ k = θ j * ((lam w : ℂ) - 1)) →
    let A := inducedFunction K ψ
    let hval : basisH.index → ℂ := fun α => (Nat.card H : ℂ)⁻¹ *
      ∑ u ∈ Finset.univ.filter (fun u : H => orderOf u = 2), (basisH.representation α).character u
    ∀ t ∈ J, orderOf t = 2 → ∀ x : E, (σ x).IsSwap →
      (∃ μ θp θm : basisH.index, μ ≠ θp ∧ μ ≠ θm ∧ θp ≠ θm ∧
        A = (basisH.representation μ).character - (basisH.representation θp).character -
          (basisH.representation θm).character ∧
        (basisH.representation μ).character 1 = 10 ∧
        (basisH.representation θp).character 1 = 5 ∧
        (basisH.representation θm).character 1 = 5 ∧
        (basisH.representation μ).character t = 2 ∧
        (basisH.representation θp).character t = 1 ∧
        (basisH.representation θm).character t = 1 ∧
        (basisH.representation μ).character x = 0 ∧
        (basisH.representation θp).character x = -1 ∧
        (basisH.representation θm).character x = 1) ∧
      (∀ u : H, orderOf u = 2 ↔ IsConj t u ∨ IsConj (x : H) u) ∧ ¬ IsConj t (x : H) ∧
      Nat.card {u : H // IsConj t u} = 15 ∧ Nat.card {u : H // IsConj (x : H) u} = 10 * 5 ^ a ∧
      Nat.card (Subgroup.centralizer {t}) = 8 * 5 ^ a ∧
      Nat.card (Subgroup.centralizer {(x : H)}) = 12 ∧
      (∀ α : basisH.index, hval α = (basisH.representation α).character t / (8 * 5 ^ a) +
        (basisH.representation α).character x / 12) ∧
      ∑ α : basisH.index, characterPairing A (basisH.representation α).character * hval α ^ 2 /
          (basisH.representation α).character 1 = -1 / 360 ∧
      (Nat.card H : ℂ) * ∑ α : basisH.index, characterPairing A
          (basisH.representation α).character * hval α ^ 2 /
          (basisH.representation α).character 1 = -(5 ^ a : ℂ) / 3 := by
  intro J K θ
  have hθdef : ∀ j, θ j = FiveKernel.sylowAugmentation (jSub σ) j := fun _ => rfl
  have hcomm : ∀ w ∈ W, ∀ j ∈ jSub σ, Commute w j := fun _ hw _ hj => commute_jSub σ hact hw hj
  have hWJ := disjoint_jSub hdisj σ
  refine ⟨fun basisJ => ⟨FiveKernel.exists_label_sylowAugmentation (eJ σ) basisJ,
    fun l hl => FiveKernel.eq_sylowAugmentation_of_five_dvd (eJ σ) basisJ l (by rw [hl])⟩,
    FiveKernel.sylowAugmentation_one (eJ σ), ⟨fun k => θ ((kEquiv hdisj σ hact).symm k).2 *
    ((lam ((kEquiv hdisj σ hact).symm k).1 : ℂ) - 1), fun k w j hk => ?_⟩, ?_⟩
  · beta_reduce
    rw [supEquiv_symm_apply hcomm hWJ hk]
  intro ψ hψ A hval t htJ ht2 x hx
  obtain ⟨dataL, hdataL⟩ := exists_rep_mul hdisj σ hact lam
  obtain ⟨data1, hdata1⟩ := exists_rep_mul hdisj σ hact 1
  have hψeq : ψ = dataL.character - data1.character := by
    funext k
    obtain ⟨w, j, hk⟩ := exists_sup_eq_mul hcomm hWJ k
    rw [Pi.sub_apply, hψ k w j hk, hdataL k w j hk, hdata1 k w j hk, MonoidHom.one_apply,
      Units.val_one, hθdef]
    ring
  have hA : A = inducedFunction K dataL.character - inducedFunction K data1.character := by
    change inducedFunction K ψ = _
    rw [hψeq, CyclicInversion.inducedFunction_sub]
  have hind : ∀ h, (coinducedFiniteComplexRepresentation K dataL).character h =
      inducedFunction K dataL.character h :=
    fun h => coinducedFiniteComplexRepresentation_character K dataL h
  obtain ⟨μ, hμ⟩ := character_norm_one_basis_character basisH
    (coinducedFiniteComplexRepresentation K dataL) (by
      rw [show (coinducedFiniteComplexRepresentation K dataL).character =
        inducedFunction K dataL.character from funext hind]
      exact characterPairing_induced_mul hWE hdisj σ hact a hWcard lam hlam _ hdataL)
  have hμ' : ∀ h, (basisH.representation μ).character h = inducedFunction K dataL.character h :=
    fun h => by rw [hμ, hind]
  obtain ⟨θp, hθp⟩ := FiveKernel.exists_label_of_virtual_norm_one basisH (thetaP hWE hdisj σ)
    (thetaP_mem_virtualCharacters hWE hdisj σ basisH) (characterPairing_thetaP hWE hdisj σ a hWcard)
    5 (by norm_num) (by rw [thetaP_one]; norm_num)
  obtain ⟨θm, hθm⟩ := exists_twist_label basisH (sgnH hWE hdisj σ) θp
  have hθm' : ∀ h, (basisH.representation θm).character h =
      (sgnH hWE hdisj σ h : ℂ) * thetaP hWE hdisj σ h := fun h => by rw [hθm, hθp]
  have hind1 : ∀ h, inducedFunction K data1.character h =
      thetaP hWE hdisj σ h + (sgnH hWE hdisj σ h : ℂ) * thetaP hWE hdisj σ h :=
    induced_theta_eq hWE hdisj σ hact a hWcard _ (fun k w j hk => by
      rw [hdata1 k w j hk, MonoidHom.one_apply, Units.val_one, mul_one])
  have hAeq : A = (basisH.representation μ).character - (basisH.representation θp).character -
      (basisH.representation θm).character := by
    funext h
    rw [hA, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, hμ', hind1, hθm', hθp]
    ring
  obtain ⟨e⟩ : Nonempty (jSub σ ≃* alternatingGroup (Fin 5)) := ⟨eJ σ⟩
  have htK : t ∈ (W ⊔ jSub σ : Subgroup H) := Subgroup.mem_sup_right htJ
  have hxK : (x : H) ∉ (W ⊔ jSub σ : Subgroup H) := by
    rw [mem_sup_iff hWE hdisj σ, rho_coe]
    obtain ⟨c, d, hcd, hxcd⟩ := hx
    rw [hxcd, Perm.sign_swap hcd]
    decide
  have hθ1 : θ 1 = 5 := FiveKernel.sylowAugmentation_one e
  have hθt : θ ⟨t, htJ⟩ = 1 :=
    FiveKernel.sylowAugmentation_of_orderOf_two e (by rw [Subgroup.orderOf_mk]; exact ht2)
  have hind_mul := induced_apply_mul hWE hdisj σ hact a hWcard (fun w => (lam w : ℂ))
    dataL.character hdataL
  have hμ1 : (basisH.representation μ).character 1 = 10 := by
    rw [hμ', show (1 : H) = ((1 : W) : H) * ((1 : jSub σ) : H) by simp, hind_mul]
    change θ 1 * _ = _
    rw [hθ1, inv_one, map_one, Units.val_one]
    norm_num
  have hμt : (basisH.representation μ).character t = 2 := by
    rw [hμ', show t = ((1 : W) : H) * ((⟨t, htJ⟩ : jSub σ) : H) by simp, hind_mul]
    change θ ⟨t, htJ⟩ * _ = _
    rw [hθt, inv_one, map_one, Units.val_one]
    norm_num
  have hμx : (basisH.representation μ).character x = 0 := by
    rw [hμ', induced_eq_zero hWE hdisj σ _ hxK]
  have hp1 : (basisH.representation θp).character 1 = 5 := by rw [hθp, thetaP_one]
  have hpt : (basisH.representation θp).character t = 1 := by
    rw [hθp, show t = ((⟨t, htJ⟩ : jSub σ) : H) from rfl, thetaP_jSub]
    exact hθt
  have hpx : (basisH.representation θp).character x = -1 := by
    rw [hθp, thetaP_of_swap hWE hdisj σ hx]
  have hm1 : (basisH.representation θm).character 1 = 5 := by
    rw [hθm', map_one, Units.val_one, thetaP_one, one_mul]
  have hmt : (basisH.representation θm).character t = 1 := by
    rw [hθm', sgnH_of_mem_sup hWE hdisj σ htK, one_mul, ← hθp, hpt]
  have hmx : (basisH.representation θm).character x = 1 := by
    rw [hθm', sgnH_of_not_mem_sup hWE hdisj σ hxK, ← hθp, hpx]
    norm_num
  have hμp : μ ≠ θp := fun h => by
    have h' := hμ1
    rw [h, hp1] at h'
    norm_num at h'
  have hμm : μ ≠ θm := fun h => by
    have h' := hμ1
    rw [h, hm1] at h'
    norm_num at h'
  have hpm : θp ≠ θm := fun h => by
    have h' := hpx
    rw [h, hmx] at h'
    norm_num at h'
  have hconjt := isConj_iff_of_mem_jSub hWE hdisj σ hact htJ ht2
  have hconjx := isConj_iff_of_swap hWE hdisj σ hact a hWcard hx
  have hclass : ∀ u : H, orderOf u = 2 ↔ IsConj t u ∨ IsConj (x : H) u := by
    intro u
    rw [orderOf_eq_two_iff hWE hdisj σ hact a hWcard, hconjt, hconjx]
  have hcardH : (Nat.card H : ℂ) = 5 ^ a * 120 := by
    rw [card_H hWE hdisj σ a hWcard]
    push_cast
    ring
  have hhval : ∀ α : basisH.index, hval α = (basisH.representation α).character t /
      (8 * 5 ^ a) + (basisH.representation α).character x / 12 := by
    intro α
    change (Nat.card H : ℂ)⁻¹ * _ = _
    rw [sum_involutions hWE hdisj σ hact a hWcard _ (fun y c => Representation.char_conj _ y c)
      htJ ht2 hx, hcardH]
    field_simp
    ring
  have hpair : ∀ β α : basisH.index, characterPairing (basisH.representation β).character
      (basisH.representation α).character = if β = α then 1 else 0 := by
    intro β α
    rw [characterPairing_irreducible _ _ (basisH.irreducible β) (basisH.irreducible α)]
    by_cases h : β = α
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right (fun h' => h (basisH.distinct h')), ite_eq_right h]
  have hcoeff : ∀ α : basisH.index, characterPairing A (basisH.representation α).character =
      (if μ = α then 1 else 0) - (if θp = α then 1 else 0) - (if θm = α then 1 else 0) := by
    intro α
    rw [hAeq, characterPairing_sub_left, characterPairing_sub_left, hpair, hpair, hpair]
  have hsum : ∑ α : basisH.index, characterPairing A (basisH.representation α).character *
      hval α ^ 2 / (basisH.representation α).character 1 = -1 / 360 := by
    simp_rw [hcoeff, sub_mul, sub_div, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      ite_div, zero_div, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [hhval μ, hhval θp, hhval θm, hμ1, hp1, hm1, hμt, hpt, hmt, hμx, hpx, hmx]
    have h5 : (5 : ℂ) ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
    ring
  refine ⟨⟨μ, θp, θm, hμp, hμm, hpm, hAeq, hμ1, hp1, hm1, hμt, hpt, hmt, hμx, hpx, hmx⟩,
    hclass, not_isConj_of_swap hWE hdisj σ hact htJ ht2 hx,
    card_class_of_mem_jSub hWE hdisj σ hact htJ ht2,
    card_class_of_swap hWE hdisj σ hact a hWcard hx,
    card_centralizer_of_mem_jSub hWE hdisj σ hact a hWcard htJ ht2,
    card_centralizer_of_swap hWE hdisj σ hact a hWcard hx, hhval, hsum, ?_⟩
  rw [hsum, hcardH]
  field_simp
  ring

end CFSG.Semidihedral.Principal

module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.UnitaryBlockCommute
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainPmGlue
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockRestrictAux

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module Matrix CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank

theorem finrank_pieceQ_bot {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F' : Submodule K V) :
    finrank K (PieceQ (⊥ : Submodule K V) F') = finrank K F' := by
  have h1 := Submodule.finrank_quotient_add_finrank ((⊥ : Submodule K V).comap F'.subtype)
  have h2 : (⊥ : Submodule K V).comap F'.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  have h3 : finrank K ((⊥ : Submodule K V).comap F'.subtype) = 0 := by
    rw [h2]; exact finrank_bot K _
  rw [h3] at h1
  exact h1

theorem hBR_core {K : Type} [Field K] [Finite K] [CharP K 2] {r ε f : ℕ}
    (hr : 1 ≤ r) (hε : ε ≤ 1) (hn : 4 ≤ 2 * r + ε) (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    (J : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K))
    (S₀ : Sylow 2 (StatedSU (2 * r + ε) (2 ^ f) K))
    (hNJ : Subgroup.normalizer ((S₀ : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) :
      Set (StatedSU (2 * r + ε) (2 ^ f) K)) ≤ J) (hJ : J ≠ ⊤)
    (Dt : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K)) (hDtJ : Dt ≤ J) (hDt : ⁅Dt, Dt⁆ = Dt)
    (d : StatedSU (2 * r + ε) (2 ^ f) K) (hd : d ∈ Dt)
    (hds : (d : GL (Fin (2 * r + ε)) K) ∉ StatedScalars (Fin (2 * r + ε)) K)
    (hd3 : (d : GL (Fin (2 * r + ε)) K) ^ 3 ∈ StatedScalars (Fin (2 * r + ε)) K)
    (hfree : ∀ H : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), ⁅H, H⁆ = H →
      (∀ w ∈ H, Commute w d) → H = ⊥)
    (hcyc : ∀ V : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), V ≤ J → ⁅V, V⁆ = V →
      ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ V → IsPGroup 3 A →
        IsCyclic (A.map (QuotientGroup.mk' (Subgroup.center (StatedSU (2 * r + ε) (2 ^ f) K)))))
    (hrank : ∀ A : Subgroup (StatedSU (2 * r + ε) (2 ^ f) K), A ≤ J →
      CFSG.Open.IsElemAbelian 3 A →
      A ⊓ (StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (2 ^ f) K) = ⊥ →
      ∀ j : ℕ, Nat.card A = 3 ^ j → j ≤ 3)
    (Et : Subgroup (GL (Fin (2 * r + ε)) K))
    (hUiso : ∀ u ∈ Et, ∀ x y : Fin (2 * r + ε) → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ x)
        ((u : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y)
    (hUthree : ∀ u ∈ Et, ∃ k : ℕ, u ^ 3 ^ k = 1)
    (hUnorm : ∀ u ∈ Et, ∀ y y' : StatedSU (2 * r + ε) (2 ^ f) K,
      (y' : GL (Fin (2 * r + ε)) K) = u * y * u⁻¹ → (y ∈ J ↔ y' ∈ J))
    (hUcomm : ∀ u ∈ Et, ∀ x ∈ Dt,
      u * (x : GL (Fin (2 * r + ε)) K) * u⁻¹ * (x : GL (Fin (2 * r + ε)) K)⁻¹ ∈
        StatedScalars (Fin (2 * r + ε)) K)
    (hcard : Nat.card Et = 27)
    (hscal : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin (2 * r + ε)) c ∈ Et)
    (φ : K ≃+* K) (At : GL (Fin (2 * r + ε)) K)
    (hAt : ∀ x y : Fin (2 * r + ε) → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
        ((At : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ x)
        ((At : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ y) =
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y)
    (hAtφ : ∀ x y : Fin (2 * r + ε) → K,
      stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε)
        ((At : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ (fun i => φ (x i)))
        ((At : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K) *ᵥ (fun i => φ (y i))) =
      φ (stdHermForm (ToralCensus.unitaryFieldData_of_card_eq_sq hK hf) (2 * r + ε) x y))
    (hAtE : ∀ A ∈ Et, At * glAut φ A * At⁻¹ ∈ Et) :
    ∃ F : Subgroup (GL (Fin (2 * r + ε)) K), F ≤ Et ∧ Nat.card F = 9 ∧
      (∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin (2 * r + ε)) c ∈ F) ∧
      ∀ A ∈ F, At * glAut φ A * At⁻¹ ∈ F := by
  obtain ⟨hf1, I, ψ, hIne, hIsub, hJI, hZψ, s, m, k₀, W', hW0, hs, hlt, hiso, -, hk1, hk2,
      hplane, hother, hm, htab, hcsd⟩ :=
    chainStabData_of_normalizer hr hε hn hK hf J S₀ hNJ hJ Dt hDtJ hDt d hd hds hd3 hfree hcyc Et
      hUiso hUthree hUnorm hUcomm
  subst hf1
  by_cases hm2 : m ≤ 2
  · set h := ToralCensus.unitaryFieldData_of_card_eq_sq hK hf with hh
    have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
    have hUcard : Nat.card (Et.map (glToLin (2 * r + ε) K)) = 27 := by
      rw [Subgroup.card_map_of_injective glToLin_injective, hcard]
    have hσ : Function.Surjective h.bar := fun c => ⟨h.bar c, h.bar_bar c⟩
    have hB := stdHermForm_separatingLeft h (2 * r + ε)
    have hσc : ∀ c : K, h.bar c = c ^ 2 := fun c => by rw [h.bar_apply]; simp
    have hiso' : W' s ≤ (W' s).orthogonalBilin (stdHermForm h (2 * r + ε)) := fun w hw =>
      Submodule.mem_orthogonalBilin.2 fun y hy => hiso s hs le_rfl y hy w hw
    have hs3 : 3 ≤ s + m := by
      by_contra hlt3
      have hdvd := ChainStabData.card_dvd_of_finrank hW0 hlt hs hcsd hK4 hm hm2
      rw [hUcard] at hdvd
      have h1 : 27 ≤ 3 ^ (s + m) := Nat.le_of_dvd (by positivity) hdvd
      have h2 : 3 ^ (s + m) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
    set Z : Subgroup (GL (Fin (2 * r + ε)) K) :=
      (Matrix.GeneralLinearGroup.scalar (Fin (2 * r + ε)) :
        Kˣ →* GL (Fin (2 * r + ε)) K).range with hZdef
    have hZE : Z ≤ Et := by rintro _ ⟨c, rfl⟩; exact hscal c
    have hZc : Nat.card Z ∣ 3 := hKu ▸ Subgroup.card_range_dvd _
    have keyD : ∀ dd : Fin 3 → ℕ,
        (∀ S T : Finset (Fin 3), ∑ i ∈ S, dd i = ∑ i ∈ T, dd i → S = T) → s = 2 → m = 1 →
        dd 0 = 2 * finrank K (PieceQ (W' 0) (W' 1)) →
        dd 1 = 2 * finrank K (PieceQ (W' 1) (W' 2)) → dd 2 = 1 →
        ∃ F : Subgroup (GL (Fin (2 * r + ε)) K), F ≤ Et ∧ Nat.card F = 9 ∧
          (∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin (2 * r + ε)) c ∈ F) ∧
          ∀ A ∈ F, At * glAut φ A * At⁻¹ ∈ F := by
      intro dd hdd hs2 hm1 hd0 hd1 hd2
      subst hs2
      have hpm : ∀ A ∈ Et, At * glAut φ A * At⁻¹ = A ∨ At * glAut φ A * At⁻¹ = A⁻¹ := by
        intro A hA
        have key := pm_of_chain_two hK4 hσ hB hσc hcsd hW0 hlt hiso' (hm.trans hm1) dd hdd hd0 hd1
          hd2 φ (semilinearTau φ At) (semilinearTau_smul φ At)
          ⟨glToLin (2 * r + ε) K A, A, hA, rfl⟩
          ⟨glToLin (2 * r + ε) K (At * glAut φ A * At⁻¹), _, hAtE A hA, rfl⟩
          (fun v => glToLin_conj_tau φ At A v)
        rcases key with h1 | h1
        · exact Or.inl (glToLin_injective (congrArg Subtype.val h1))
        · refine Or.inr (glToLin_injective ?_)
          rw [map_inv]
          exact congrArg Subtype.val h1
      obtain ⟨F, hFE, hZF, hFc⟩ := exists_order_nine Et Z hZE hZc hcard
      refine ⟨F, hFE, hFc, fun c => hZF ⟨c, rfl⟩, fun A hA => ?_⟩
      rcases hpm A (hFE hA) with h1 | h1
      · rw [h1]; exact hA
      · rw [h1]; exact F.inv_mem hA
    rcases htab with ⟨hr', hε', hI, hs', hk', hm'⟩ | ⟨hr', hε', hI, hs', hk', hm'⟩ |
      ⟨hr', hε', hI, hs', hk', hm'⟩ | ⟨hr', hε', hI, hs', hk', hm'⟩ |
      ⟨hr', hε', hI, hs', hk', hm'⟩ | ⟨hr', hε', hI, hs', hk', hm'⟩ |
      ⟨hr', hε', hI, hs', hk', hm'⟩ | ⟨hr', hε', hI, hs', hk', hm'⟩
    · omega
    · omega
    ·
      subst hs' hk'
      have hn6 : 2 * r + ε = 6 := by omega
      have ha : finrank K (W' 1) = 2 := by
        have := hplane
        rw [show (W' (1 - 1)) = (⊥ : Submodule K _) from hW0, finrank_pieceQ_bot] at this
        exact this
      obtain ⟨u, ⟨A, hA, rfl⟩, hdet⟩ := exists_det_ne_one_chain_one hK4 hσ hB hσc hcsd hW0 hlt hiso'
        ha (by rw [hm]; omega) (by rw [hUcard])
      refine exists_order_nine_of_det hK4 φ At hn6 Et hcard hscal hAtE ⟨A, hA, fun h1 => hdet ?_⟩
      have : LinearMap.det ((glToLin (2 * r + ε) K A :
          LinearMap.GeneralLinearGroup K (Fin (2 * r + ε) → K)) :
          Module.End K (Fin (2 * r + ε) → K)) = (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K).det :=
        LinearMap.det_toLin' (A : Matrix (Fin (2 * r + ε)) (Fin (2 * r + ε)) K)
      rw [this, ← Matrix.GeneralLinearGroup.val_det_apply, h1]
      rfl
    · omega
    · omega
    ·
      have e0 : finrank K (PieceQ (W' 0) (W' 1)) = 1 :=
        hother 1 le_rfl (by omega) (by omega)
      have e1 : finrank K (PieceQ (W' 1) (W' 2)) = 2 := by
        have := hplane
        rw [hk'] at this
        exact this
      exact keyD ![2, 4, 1] (by decide) hs' hm' (by rw [e0]; rfl) (by rw [e1]; rfl) rfl
    ·
      have e0 : finrank K (PieceQ (W' 0) (W' 1)) = 2 := by
        have := hplane
        rw [hk'] at this
        exact this
      have e1 : finrank K (PieceQ (W' 1) (W' 2)) = 1 :=
        hother 2 (by omega) (by omega) (by omega)
      exact keyD ![4, 2, 1] (by decide) hs' hm' (by rw [e0]; rfl) (by rw [e1]; rfl) rfl
    · omega
  · obtain ⟨rfl, rfl, rfl⟩ := htab.eq_last_of_not_le_two hm2
    exact (false_of_rank_survivor _ J ψ hJI hZψ hrank).elim

end CFSG.HardMathSupport.Curtis.UnitaryLevi

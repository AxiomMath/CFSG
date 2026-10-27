module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs196
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL28Facts
public import CFSG.LocalAnalysis.SteinbergCCPowerTwoDegreeTransport
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairRes3L28

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight

open CFSG.HardMathSupport.Solomon.LocalBalance (innerAut)

section L28

variable {S : Type} [Group S] [Finite S]

noncomputable def l2EightEquiv {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    S ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2BinaryMatrixGroup 3 :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP F 2 := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196.charP_two_of_card hF
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  e.trans (CFSG.LocalAnalysis.PowerTwoDegree.pslMapEquiv
    (GaloisField.algEquivGaloisField 2 3 hF).toRingEquiv)

theorem map_centralizer_singleton {T : Type} [Group T] (e : S ≃* T) (t : S) :
    (Subgroup.centralizer ({t} : Set S)).map e.toMonoidHom =
      Subgroup.centralizer ({e t} : Set T) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg e h
    simpa [map_mul] using h'
  · intro h
    apply e.injective
    simpa [map_mul] using h

theorem centralizer_three_l2Eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) {t : S} (ht : orderOf t = 3) :
    Nat.card (Subgroup.centralizer ({t} : Set S)) = 9 ∧
      IsCyclic (Subgroup.centralizer ({t} : Set S)) := by
  set e' := l2EightEquiv hF e
  have ht' : orderOf (e' t) = 3 := by rw [MulEquiv.orderOf_eq]; exact ht
  obtain ⟨h9, hcyc⟩ :=
    CFSG.BenderSuzuki.MatrixGroups.psl28_orderThree_centralizer_cyclic_order_nine (e' t) ht'
  have eC : Subgroup.centralizer ({t} : Set S) ≃* Subgroup.centralizer ({e' t} : Set _) :=
    (e'.subgroupMap _).trans (MulEquiv.subgroupCongr (map_centralizer_singleton e' t))
  refine ⟨by rw [Nat.card_congr eC.toEquiv]; exact h9, ?_⟩
  exact isCyclic_of_surjective eC.symm.toMonoidHom eC.symm.surjective

theorem card_l2Eight {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 3)
    (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) : Nat.card S = 504 := by
  rw [Nat.card_congr (l2EightEquiv hF e).toEquiv]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.card_psl2_eight

theorem card_sylow_three_of_card_504 (hS : Nat.card S = 504) (Q : Sylow 3 S) :
    Nat.card (Q : Subgroup S) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  have hidx := (Q : Subgroup S).card_mul_index
  have hndvd := Q.not_dvd_index
  rw [hk, hS] at hidx
  have hk5 : k ≤ 5 := by
    by_contra hk'
    have h1 : 3 ^ 6 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ k ≤ 504 := by
      rw [← hidx]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero fun h => by rw [h] at hidx; omega)
    norm_num at h1
    omega
  rw [hk]
  interval_cases k <;> norm_num at hidx ⊢ <;> omega

theorem exists_pow_four_or_seven_of_plane {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 3) (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (A : Subgroup (MulAut S)) (hA : CFSG.Open.IsElemAbelian 3 A) (hA9 : Nat.card A = 9) :
    ∃ ψ ∈ A, ∃ s : S, orderOf s = 9 ∧ (ψ s = s ^ 4 ∨ ψ s = s ^ 7) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 2) (by rw [hA9]; norm_num)
  obtain ⟨Q, hQ⟩ : ∃ Q : Sylow 3 S, ∀ ψ : A, ψ • Q = Q := by
    have h1 := card_sylow_modEq_one 3 S
    have h2 := hAp.card_modEq_card_fixedPoints (Sylow 3 S)
    have h3 : Nat.card (MulAction.fixedPoints A (Sylow 3 S)) ≡ 1 [MOD 3] := h2.symm.trans h1
    have h4 : Nat.card (MulAction.fixedPoints A (Sylow 3 S)) ≠ 0 := by
      intro h0
      rw [h0] at h3
      exact absurd h3 (by decide)
    obtain ⟨⟨Q, hQ⟩⟩ := (Nat.card_ne_zero.1 h4).1
    exact ⟨Q, fun ψ => hQ ψ⟩
  have hmapQ : ∀ ψ ∈ A, ∀ x ∈ (Q : Subgroup S), ψ x ∈ (Q : Subgroup S) := by
    intro ψ hψ x hx
    have h := hQ ⟨ψ, hψ⟩
    have hmem : ψ x ∈ (((⟨ψ, hψ⟩ : A) • Q : Sylow 3 S) : Subgroup S) := by
      show ψ x ∈ ((ψ • Q : Sylow 3 S) : Subgroup S)
      rw [Sylow.pointwise_smul_def]
      exact Subgroup.smul_mem_pointwise_smul x ψ _ hx
    rwa [h] at hmem
  have hS : Nat.card S = 504 := card_l2Eight hF e
  have hQ9 : Nat.card (Q : Subgroup S) = 9 := card_sylow_three_of_card_504 hS Q
  have hQcomm : ∀ a b : (Q : Subgroup S), a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hQ9]; norm_num)
  obtain ⟨t₀, ht₀⟩ := exists_prime_orderOf_dvd_card' (G := (Q : Subgroup S)) 3
    (by rw [hQ9]; norm_num)
  set t : S := (t₀ : S) with htdef
  have ht : orderOf t = 3 := by rw [htdef, Subgroup.orderOf_coe]; exact ht₀
  obtain ⟨hC9, hCcyc⟩ := centralizer_three_l2Eight hF e ht
  have hQC : (Q : Subgroup S) = Subgroup.centralizer ({t} : Set S) := by
    have hle : (Q : Subgroup S) ≤ Subgroup.centralizer ({t} : Set S) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := hQcomm ⟨x, hx⟩ t₀
      exact congrArg Subtype.val this
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hC9, hQ9])
  haveI : IsCyclic (Q : Subgroup S) := by rw [hQC]; exact hCcyc
  by_cases hcase : ∀ ψ ∈ A, ∀ x ∈ (Q : Subgroup S), ψ x = x
  · exfalso
    have hle : A ≤ (Q : Subgroup S).map (MulAut.conj : S →* MulAut S) := by
      intro ψ hψ
      by_cases hψ1 : ψ = 1
      · rw [hψ1]
        exact Subgroup.one_mem _
      have hψ3 : orderOf ψ = 3 := orderOf_eq_prime (hA.2 ψ hψ) hψ1
      by_cases hin : ψ ∈ innerAut S
      · obtain ⟨y, rfl⟩ := hin
        refine ⟨y, ?_, rfl⟩
        rw [SetLike.mem_coe, hQC, Subgroup.mem_centralizer_singleton_iff]
        have h := hcase _ hψ t t₀.2
        rw [MulAut.conj_apply] at h
        calc y * t = y * t * y⁻¹ * y := by group
          _ = t * y := by rw [h]
      · have h6 :=
          (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs196.l2Eight_outer_fixSubgroup hF e
            hψ3 hin).1
        have hQfix : (Q : Subgroup S) ≤ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup ψ :=
          fun x hx => hcase ψ hψ x hx
        have hcard := Subgroup.card_le_of_le hQfix
        rw [h6, hQ9] at hcard
        omega
    haveI : IsCyclic ((Q : Subgroup S).map (MulAut.conj : S →* MulAut S)) :=
      isCyclic_of_surjective ((MulAut.conj : S →* MulAut S).subgroupMap (Q : Subgroup S))
        ((MulAut.conj : S →* MulAut S).subgroupMap_surjective (Q : Subgroup S))
    haveI : IsCyclic A := Subgroup.isCyclic_of_le hle
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
    rw [hA9] at hg
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hA.2 g g.2)
    have hdvd := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at hdvd
    norm_num at hdvd
  · push Not at hcase
    obtain ⟨ψ, hψ, x, hx, hψx⟩ := hcase
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Q : Subgroup S))
    set s : S := (g : S) with hsdef
    have hs9 : orderOf s = 9 := by
      rw [hsdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hQ9]
    have hQs : ∀ y ∈ (Q : Subgroup S), y ∈ Subgroup.zpowers s := by
      intro y hy
      obtain ⟨n, hn⟩ := hg ⟨y, hy⟩
      refine ⟨n, ?_⟩
      have := congrArg Subtype.val hn
      simpa [hsdef] using this
    obtain ⟨k, hk9, hk⟩ : ∃ k : ℕ, k < 9 ∧ ψ s = s ^ k := by
      have hmem := hQs _ (hmapQ ψ hψ s g.2)
      rw [mem_zpowers_iff_mem_range_orderOf, hs9] at hmem
      obtain ⟨k, hk, hk'⟩ := Finset.mem_image.1 hmem
      exact ⟨k, Finset.mem_range.1 hk, hk'.symm⟩
    have hpow : ∀ j : ℕ, ψ (s ^ j) = s ^ (k * j) := fun j => by rw [map_pow, hk, ← pow_mul]
    have hψ3 : ψ ^ 3 = 1 := hA.2 ψ hψ
    have hk3 : s ^ (k * (k * k)) = s ^ 1 := by
      have h := congrArg (fun φ : MulAut S => φ s) hψ3
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h
      rw [hk, hpow, hpow] at h
      rw [pow_one]
      exact h
    have hmod : k * (k * k) ≡ 1 [MOD 9] := by
      rw [← hs9]
      exact (pow_eq_pow_iff_modEq).1 hk3
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hψx
      obtain ⟨n, rfl⟩ := hQs x hx
      rw [map_zpow, hk, pow_one]
    refine ⟨ψ, hψ, s, hs9, ?_⟩
    rw [hk]
    unfold Nat.ModEq at hmod
    interval_cases k <;> simp_all

end L28

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSEight

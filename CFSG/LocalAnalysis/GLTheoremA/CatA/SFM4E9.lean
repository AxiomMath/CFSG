module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM4Twist
public import CFSG.RankThree.PartTwo.Census.Exceptional.Geck
public import CFSG.LocalAnalysis.GLTheoremA.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open
open CFSG.LieType.Chevalley (graphFixedRootGroup fieldActor fixSubfield ringEquiv_cube_apply_eq)
open CFSG.Blueprint.Chevalley (TwistTag)


private def sfm4M (K : Type) [Field K] : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, -1], by rw [Matrix.det_fin_two_of]; ring⟩

private theorem sfm4M_pow_three (K : Type) [Field K] : sfm4M K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, pow_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sfm4M, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sfm4M_ne_one (K : Type) [Field K] : sfm4M K ≠ 1 := by
  intro h
  have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K) 1 0) h
  simp [sfm4M] at this

private theorem sfm4M_not_comm (K : Type) [Field K] :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, A * sfm4M K ≠ sfm4M K * A := by
  refine ⟨⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; ring⟩, fun h => ?_⟩
  have h00 := congrArg
    (fun B : Matrix.SpecialLinearGroup (Fin 2) K => (B : Matrix (Fin 2) (Fin 2) K) 0 0) h
  change (((!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) * (sfm4M K : Matrix (Fin 2) (Fin 2) K)) 0 0 =
    (((sfm4M K : Matrix (Fin 2) (Fin 2) K)) * (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) K)) 0 0 at h00
  simp [sfm4M, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem sfm4_e9_of_commuting {K G : Type} [Field K] [Group G] [Finite G]
    (ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) K →* G) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂)
    (hc : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) K, ι₁ A * ι₂ B = ι₂ B * ι₁ A)
    (H : Subgroup G) (hH₁ : ∀ A, ι₁ A ∈ H) (hH₂ : ∀ A, ι₂ A ∈ H) :
    ∃ P : Subgroup G, P ≤ H ∧ IsElemAbelian 3 P ∧ Nat.card P = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3 : ι₁ (sfm4M K) ^ 3 = 1 := by rw [← map_pow, sfm4M_pow_three, map_one]
  have hy3 : ι₂ (sfm4M K) ^ 3 = 1 := by rw [← map_pow, sfm4M_pow_three, map_one]
  have hx1 : ι₁ (sfm4M K) ≠ 1 := fun h => sfm4M_ne_one K (h₁ (by rw [h, map_one]))
  have hxy : Commute (ι₁ (sfm4M K)) (ι₂ (sfm4M K)) := hc _ _
  have hox : orderOf (ι₁ (sfm4M K)) = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf (ι₂ (sfm4M K)) = 3 := by
    rw [orderOf_injective ι₂ h₂, orderOf_eq_prime (sfm4M_pow_three K) (sfm4M_ne_one K)]
  have hxR : ι₁ (sfm4M K) ∉ ι₂.range := by
    intro hmem
    obtain ⟨B, hB⟩ := MonoidHom.mem_range.1 hmem
    obtain ⟨A, hA⟩ := sfm4M_not_comm K
    apply hA
    apply h₁
    rw [map_mul, map_mul]
    have := hc A B
    rw [hB] at this
    exact this
  have hpow : ∀ k : ℤ, ι₁ (sfm4M K) ^ k ∈ ι₂.range → ι₁ (sfm4M K) ^ k = 1 := by
    intro k hk
    have e1 : ι₁ (sfm4M K) ^ (k % ((3 : ℕ) : ℤ)) = ι₁ (sfm4M K) ^ k := by
      rw [← hox]
      exact zpow_mod_orderOf _ _
    rw [← e1] at hk ⊢
    have hk3 : k % ((3 : ℕ) : ℤ) = 0 ∨ k % ((3 : ℕ) : ℤ) = 1 ∨ k % ((3 : ℕ) : ℤ) = 2 := by
      omega
    rcases hk3 with h | h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hk
      exact absurd hk hxR
    · rw [h] at hk
      have h2 : ι₁ (sfm4M K) ^ (2 : ℕ) ∈ ι₂.range := by simpa using hk
      have h4 : ι₁ (sfm4M K) ^ (4 : ℕ) = ι₁ (sfm4M K) := by
        rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hx3, one_mul, pow_one]
      exact absurd (by
        rw [← h4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
        exact Subgroup.pow_mem _ h2 2) hxR
  have hint : Subgroup.zpowers (ι₁ (sfm4M K)) ⊓ Subgroup.zpowers (ι₂ (sfm4M K)) = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgx, hgy⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hgy
    have hgR : g ∈ ι₂.range := by
      rw [← hk]
      exact Subgroup.zpow_mem _ (MonoidHom.mem_range.2 ⟨sfm4M K, rfl⟩) k
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hgx
    rw [Subgroup.mem_bot, ← hj]
    rw [← hj] at hgR
    exact hpow j hgR
  have hcx : Nat.card (Subgroup.zpowers (ι₁ (sfm4M K))) = 3 := by
    rw [Nat.card_zpowers, hox]
  have hcy : Nat.card (Subgroup.zpowers (ι₂ (sfm4M K))) = 3 := by
    rw [Nat.card_zpowers, hoy]
  have hnorm : Subgroup.zpowers (ι₂ (sfm4M K)) ≤
      Subgroup.normalizer ((Subgroup.zpowers (ι₁ (sfm4M K)) : Subgroup G) : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [Subgroup.mem_centralizer_iff]
    rintro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hxy.zpow_zpow j k).eq
  have hcard := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hint, hcx, hcy, Subgroup.card_bot] at hcard
  have hPeq : Subgroup.closure ({ι₁ (sfm4M K), ι₂ (sfm4M K)} : Set G) =
      Subgroup.zpowers (ι₁ (sfm4M K)) ⊔ Subgroup.zpowers (ι₂ (sfm4M K)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure, ← Subgroup.closure_union,
      Set.insert_eq]
  have hcomm : Set.Pairwise ({ι₁ (sfm4M K), ι₂ (sfm4M K)} : Set G) Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxy
    · exact hxy.symm
    · exact Commute.refl _
  haveI : IsMulCommutative (Subgroup.closure ({ι₁ (sfm4M K), ι₂ (sfm4M K)} : Set G)) :=
    Subgroup.isMulCommutative_closure hcomm
  have hexp : ∀ g ∈ Subgroup.closure ({ι₁ (sfm4M K), ι₂ (sfm4M K)} : Set G), g ^ 3 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hx3
      · exact hy3
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      have hab : Commute a b :=
        congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : Subgroup.closure _) ⟨b, hb⟩)
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  refine ⟨Subgroup.closure ({ι₁ (sfm4M K), ι₂ (sfm4M K)} : Set G), ?_, ⟨inferInstance, hexp⟩, ?_⟩
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hH₁ _
    · exact hH₂ _
  · rw [hPeq]
    simpa using hcard

private def sfm4α : Fin 2 → Fin CFSG.Blueprint.Chevalley.Tag.G2.rank → ℤ := ![![1, 0], ![1, 2]]

theorem sfm4_two_eq_zero {F : Type} [Field F] [Finite F] {f : ℕ} (hf : 1 ≤ f)
    (hF : Nat.card F = 2 ^ f) : (2 : F) = 0 := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  have hcard : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
  have hd : ringChar F ∣ 2 ^ f := by
    rw [← hcard, hn]
    exact dvd_pow_self _ (Nat.pos_iff_ne_zero.1 n.pos)
  have h2 : ringChar F = 2 :=
    (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd)
  have h0 := CharP.cast_eq_zero F (ringChar F)
  rw [h2] at h0
  exact_mod_cast h0

theorem sfm4_commuting_fix {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    ∃ ι₁ ι₂ : Matrix.SpecialLinearGroup (Fin 2) ↥(fixSubfield σ) →*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Function.Injective ι₁ ∧ Function.Injective ι₂ ∧
      (∀ A B, ι₁ A * ι₂ B = ι₂ B * ι₁ A) ∧
      (∀ A, fieldActor (t := TwistTag.D4) σ σ (ι₁ A) = ι₁ A) ∧
      (∀ A, fieldActor (t := TwistTag.D4) σ σ (ι₂ A) = ι₂ A) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  have hσ3' : σ ^ 3 = 1 := sfm4_cube_eq_one hK hσ
  have hσ1 : σ ≠ 1 := sfm4_frob_ne_one Nat.prime_two hf hK hσ
  have hK3 : Nat.card K = 2 ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, hF⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield Nat.prime_two (by omega) hK3 σ
  rw [orderOf_eq_prime hσ3' hσ1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 3)] at hF
  have h2 : (2 : ↥(fixSubfield σ)) = 0 := sfm4_two_eq_zero hf hF
  obtain ⟨ι, hι, hc⟩ := CFSG.RankThree.PartTwo.Census.Exceptional.exists_commuting_rootSL2
    (K := ↥(fixSubfield σ)) CFSG.Blueprint.Chevalley.Tag.G2 sfm4α (by decide)
  let Θ : CFSG.Blueprint.Chevalley.adjointGroup CFSG.Blueprint.Chevalley.Tag.G2 ↥(fixSubfield σ) ≃*
      ↥(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (fieldActor (t := TwistTag.D4) σ σ)) :=
    (CFSG.RankThree.PartTwo.KFacts.d4FixedG2Equiv _ h2).symm.trans
      ((MulEquiv.subgroupCongr
        (CFSG.RankThree.PartTwo.KFacts.d4_twistedFixedGroup_id_eq_graphFixedRootGroup _)).trans
        ((CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.trialityFieldImageEquivRoot σ).symm.trans
          (CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.fixSubgroupFieldActorEquiv
            K σ hσ3).symm))
  set H := CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
    (fieldActor (t := TwistTag.D4) σ σ) with hH
  have e1 : ∀ x y, H.subtype (Θ (ι 0 x)) * H.subtype (Θ (ι 1 y)) =
      H.subtype (Θ (ι 0 x * ι 1 y)) := fun x y => by rw [map_mul, map_mul]
  have e2 : ∀ x y, H.subtype (Θ (ι 1 y)) * H.subtype (Θ (ι 0 x)) =
      H.subtype (Θ (ι 1 y * ι 0 x)) := fun x y => by rw [map_mul, map_mul]
  have hcomm : ∀ A B, H.subtype (Θ (ι 0 A)) * H.subtype (Θ (ι 1 B)) =
      H.subtype (Θ (ι 1 B)) * H.subtype (Θ (ι 0 A)) := fun A B => by
    rw [e1, e2, hc 0 1 (by decide) A B]
  exact ⟨(CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (fieldActor (t := TwistTag.D4) σ σ)).subtype.comp (Θ.toMonoidHom.comp (ι 0)),
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (fieldActor (t := TwistTag.D4) σ σ)).subtype.comp (Θ.toMonoidHom.comp (ι 1)),
    Subtype.val_injective.comp (Θ.injective.comp (hι 0)),
    Subtype.val_injective.comp (Θ.injective.comp (hι 1)),
    fun A B => hcomm A B,
    fun A => (Θ (ι 0 A)).2,
    fun A => (Θ (ι 1 A)).2⟩

end CFSG.LocalAnalysis.GLTheoremA.I2023

end

module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1525dCoreBorel
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpRk
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbLeviRad
public import CFSG.Timmesfeld.ARS.LinearLevis

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K1525dCoreProof

open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbeddingD2.Tits.GN516.Levi

variable (m : ℕ)

theorem blockHom_upper (i : Fin m) (c : ZMod 2) :
    SL.blockHom (ZMod 2) i (sl2Upper c) = SL.x m (ZMod 2) (Pi.single i 1) c := by
  have hne := SL.castSucc_ne_succ i
  rw [SL.x_eq hne (toStd_single m i)]
  exact Subtype.ext (SL.blockMat_transvection_upper i c)

theorem blockHom_lower (i : Fin m) (c : ZMod 2) :
    SL.blockHom (ZMod 2) i (sl2Lower c) = SL.x m (ZMod 2) (-Pi.single i 1) c := by
  have hne := SL.castSucc_ne_succ i
  rw [SL.x_eq hne.symm (SL.toStd_neg_single i)]
  exact Subtype.ext (SL.blockMat_transvection_lower i c)

theorem rankOne_le_range_blockHom (i : Fin m) :
    rankOne (dat m).rootGroup i ≤ (SL.blockHom (ZMod 2) i).range := by
  have hL := CFSG.Timmesfeld.ARS.simplyLacedLevis_specialLinear m (ZMod 2)
  have hα : (Pi.single i 1 : Fin m → ℤ) ∈ (dat m).roots :=
    (RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin m → ℤ) ∈ (dat m).roots :=
    (RootSystem.ofCartan (dat m).isFiniteType (dat m).divisible).neg_mem _ hα
  refine sup_le ?_ ?_
  · intro g hg
    obtain ⟨c, rfl⟩ := hL.surj _ hα g hg
    exact ⟨sl2Upper c, blockHom_upper m i c⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := hL.surj _ hα' g hg
    exact ⟨sl2Lower c, blockHom_lower m i c⟩

theorem blockMat_apply_of_not_mem (j : Fin m) (B : Matrix (Fin 2) (Fin 2) (ZMod 2))
    {a b : Fin (m + 1)} (ha : ¬ (a = j.castSucc ∨ a = j.succ))
    (hb : ¬ (b = j.castSucc ∨ b = j.succ)) :
    SL.blockMat j B a b = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) a b := by
  have h := SL.blockMat_apply j B (Sum.inr ⟨a, ha⟩) (Sum.inr ⟨b, hb⟩)
  rw [SL.blockEquiv_inr, SL.blockEquiv_inr] at h
  rw [h]
  simp [Matrix.fromBlocks_apply₂₂, Matrix.one_apply, Subtype.ext_iff]

theorem blockRange_inf_eq_bot {i j : Fin m} (hij : i.val + 2 ≤ j.val) :
    (SL.blockHom (ZMod 2) i).range ⊓ (SL.blockHom (ZMod 2) j).range = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨A, rfl⟩, ⟨B, hB⟩⟩
  rw [Subgroup.mem_bot]
  have h1 : i.castSucc ≠ j.castSucc := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h2 : i.castSucc ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h3 : i.succ ≠ j.castSucc := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h4 : i.succ ≠ j.succ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have hne := SL.castSucc_ne_succ i
  have hA : (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
    ext p q
    have key : ∀ (a b : Fin (m + 1)), ¬ (a = j.castSucc ∨ a = j.succ) →
        ¬ (b = j.castSucc ∨ b = j.succ) →
        (SL.blockHom (ZMod 2) i A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) a b =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) a b := fun a b ha hb => by
      rw [← hB]
      exact blockMat_apply_of_not_mem m j _ ha hb
    have hbi := SL.blockMat_apply i (A : Matrix (Fin 2) (Fin 2) (ZMod 2))
    fin_cases p <;> fin_cases q
    · have := key i.castSucc i.castSucc (by tauto) (by tauto)
      have h5 := hbi (Sum.inl 0) (Sum.inl 0)
      rw [SL.blockEquiv_zero] at h5
      change (SL.blockMat i (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) i.castSucc i.castSucc =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.castSucc i.castSucc at this
      rw [h5] at this
      simpa using this
    · have := key i.castSucc i.succ (by tauto) (by tauto)
      have h5 := hbi (Sum.inl 0) (Sum.inl 1)
      rw [SL.blockEquiv_zero, SL.blockEquiv_one] at h5
      change (SL.blockMat i (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) i.castSucc i.succ =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.castSucc i.succ at this
      rw [h5] at this
      simpa [Matrix.one_apply, hne] using this
    · have := key i.succ i.castSucc (by tauto) (by tauto)
      have h5 := hbi (Sum.inl 1) (Sum.inl 0)
      rw [SL.blockEquiv_zero, SL.blockEquiv_one] at h5
      change (SL.blockMat i (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) i.succ i.castSucc =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ i.castSucc at this
      rw [h5] at this
      simpa [Matrix.one_apply, hne.symm] using this
    · have := key i.succ i.succ (by tauto) (by tauto)
      have h5 := hbi (Sum.inl 1) (Sum.inl 1)
      rw [SL.blockEquiv_one] at h5
      change (SL.blockMat i (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) i.succ i.succ =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) i.succ i.succ at this
      rw [h5] at this
      simpa using this
  have hA1 : A = 1 := Subtype.ext (by rw [hA]; rfl)
  rw [hA1, map_one]

theorem three_dvd_card_rankOne (i : Fin m) :
    3 ∣ Nat.card ↥(rankOne (dat m).rootGroup i) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx, y, hy, h3, c, hc⟩ := (hasSL2Node_sl (m := m) (F := ZMod 2) i).hasOrderThree
  have hmem : x * y ∈ rankOne (dat m).rootGroup i :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hy)
  have hne : x * y ≠ 1 := fun h => hc (by rw [h, one_mul, mul_one])
  have hord : orderOf (x * y) = 3 := orderOf_eq_prime h3 hne
  have h := orderOf_dvd_natCard (⟨x * y, hmem⟩ : ↥(rankOne (dat m).rootGroup i))
  rwa [← Subgroup.orderOf_coe, Subgroup.coe_mk, hord] at h

theorem cartan_eq_zero {i j : Fin m} (hij : i.val + 2 ≤ j.val) :
    (dat m).cartan i j = 0 := by
  have h1 : i ≠ j := fun h => by subst h; omega
  have h2 : ¬ i.val + 1 = j.val := by omega
  have h3 : ¬ j.val + 1 = i.val := by omega
  show CartanMatrix.A m i j = 0
  simp [CartanMatrix.A, Matrix.of_apply, h1, h2, h3]

theorem two_le_pRank_of_orthogonal {i j : Fin m} (hij : i.val + 2 ≤ j.val)
    {A : Subgroup (SLF2 m)} (hi : rankOne (dat m).rootGroup i ≤ A)
    (hj : rankOne (dat m).rootGroup j ≤ A) : 2 ≤ CFSG.Open.pRank 3 A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hct := isCTGroupDatum m (ZMod 2)
  have hext := steinbergExtras m (ZMod 2)
  have hne : i ≠ j := fun h => by subst h; omega
  have hcomm : ∀ (x : ↥(rankOne (dat m).rootGroup i)) (y : ↥(rankOne (dat m).rootGroup j)),
      Commute ((rankOne (dat m).rootGroup i).subtype x) ((rankOne (dat m).rootGroup j).subtype y) :=
    fun x y => rankOne_commute hct hext hne (cartan_eq_zero m hij) x.2 y.2
  let φ : ↥(rankOne (dat m).rootGroup i) × ↥(rankOne (dat m).rootGroup j) →* SLF2 m :=
    MonoidHom.noncommCoprod (rankOne (dat m).rootGroup i).subtype
      (rankOne (dat m).rootGroup j).subtype hcomm
  have hφ : ∀ x y, φ (x, y) = (x : SLF2 m) * y := fun x y => MonoidHom.noncommCoprod_apply _ _ _ _
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ h
    rw [hφ] at h
    have hxy : (x : SLF2 m) = ((y : SLF2 m))⁻¹ := eq_inv_of_mul_eq_one_left h
    have hxj : (x : SLF2 m) ∈ rankOne (dat m).rootGroup j := by
      rw [hxy]
      exact Subgroup.inv_mem _ y.2
    have hbot : (x : SLF2 m) ∈ (SL.blockHom (ZMod 2) i).range ⊓ (SL.blockHom (ZMod 2) j).range :=
      ⟨rankOne_le_range_blockHom m i x.2, rankOne_le_range_blockHom m j hxj⟩
    rw [blockRange_inf_eq_bot m hij, Subgroup.mem_bot] at hbot
    have hy1 : (y : SLF2 m) = 1 := by
      rw [hbot, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext hbot) (Subtype.ext hy1)
  exact CFSG.LocalAnalysis.RankThreeUC.S15.K421SpRkProof.two_le_pRank_of_prod
    (three_dvd_card_rankOne m i) (three_dvd_card_rankOne m j) φ hinj (C := A) (by
      rintro _ ⟨⟨x, y⟩, rfl⟩
      rw [hφ]
      exact Subgroup.mul_mem _ (hi x.2) (hj y.2))

end K1525dCoreProof

end CFSG.LocalAnalysis.RankThreeUC.S15

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp5
public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp3
public import CFSG.GroupTheory.CommutingMovingElemAbelian

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.SubgroupLists (spForm)

namespace SpEngine

noncomputable def statedSpEquivLinIsometryGroup (ℓ : ℕ) (F : Type) [Field F] :
    StatedSp ℓ F ≃* linIsometryGroup (spForm ℓ F) :=
  (CFSG.ClassicalGroups.Symplectic.spEquiv (m := ℓ) (K := F)).trans
    (MulEquiv.subgroupMap
      (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin ℓ ⊕ Fin ℓ → F))
      (bilinIsometryGroup (spForm ℓ F)))

theorem statedSpEquivLinIsometryGroup_apply (ℓ : ℕ) (F : Type) [Field F]
    (A : StatedSp ℓ F) (v : Fin ℓ ⊕ Fin ℓ → F) :
    ((statedSpEquivLinIsometryGroup ℓ F A :
        (Fin ℓ ⊕ Fin ℓ → F) ≃ₗ[F] (Fin ℓ ⊕ Fin ℓ → F))) v =
      ((A : GL (Fin ℓ ⊕ Fin ℓ) F) : Matrix (Fin ℓ ⊕ Fin ℓ) (Fin ℓ ⊕ Fin ℓ) F) *ᵥ v := by
  change (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin ℓ ⊕ Fin ℓ → F)
    (Matrix.GeneralLinearGroup.toLin A)) v = _
  rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
  exact Matrix.GeneralLinearGroup.toLin_apply (A := A) v

open CFSG.RankThree.SubgroupLists (spForm)

theorem planeThreeLin_eq_matVec {F : Type} [Field F] [CharP F 2] {s : ℕ} (i : Fin s)
    (x : Fin s ⊕ Fin s → F) :
    planeThreeLin (F := F) s i x = planeThreeMat (F := F) s i *ᵥ x :=
  (planeThree_mulVec i x).symm

theorem planeThreeLin_single_inl {F : Type} [Field F] [CharP F 2] {s : ℕ} (i : Fin s) :
    planeThreeLin (F := F) s i (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inr i) 1 := by
  rw [planeThreeLin_eq_matVec]
  exact planeThree_single_inl i

theorem planeThreeLin_sq_single_inl {F : Type} [Field F] [CharP F 2] {s : ℕ} (i : Fin s) :
    (planeThreeLin (F := F) s i ^ 2) (Pi.single (Sum.inl i) 1) =
      Pi.single (Sum.inl i) 1 + Pi.single (Sum.inr i) 1 := by
  rw [pow_two, LinearEquiv.mul_apply, planeThreeLin_eq_matVec, planeThreeLin_eq_matVec,
    Matrix.mulVec_mulVec, ← pow_two]
  exact planeThree_sq_single_inl i

theorem planeThreeLin_apply_single_inl_of_ne {F : Type} [Field F] [CharP F 2] {s : ℕ}
    {i j : Fin s} (hij : i ≠ j) :
    planeThreeLin (F := F) s j (Pi.single (Sum.inl i) 1) = Pi.single (Sum.inl i) 1 := by
  rw [planeThreeLin_eq_matVec]
  exact planeThree_apply_single_inl_of_ne hij

theorem spF2QTorus_holds :
    ∀ (s : ℕ) (F : Type) [Field F] [Finite F] [CharP F 2],
      Nat.card F = 2 → 3 ≤ s →
        ∃ Q : Subgroup (StatedSp s F), IsElemAbelian 3 Q ∧ 3 ≤ CFSG.Open.pRank 3 Q := by
  intro s F hField hFinite hChar hcard hs
  letI : Field F := hField
  letI : Finite F := hFinite
  letI : CharP F 2 := hChar
  classical
  haveI : Finite (StatedSp s F) := Subtype.finite
  let idx : Fin 3 → Fin s := fun i => ⟨i.val, by have := i.isLt; omega⟩
  have hidx : Function.Injective idx := by
    intro i j h
    have h' := congrArg Fin.val h
    exact Fin.ext (by simpa [idx] using h')
  let act : StatedSp s F →* ((Fin s ⊕ Fin s → F) ≃ₗ[F] (Fin s ⊕ Fin s → F)) :=
    (linIsometryGroup (spForm s F)).subtype.comp
      (statedSpEquivLinIsometryGroup (ℓ := s) F).toMonoidHom
  have hact_apply : ∀ (A : StatedSp s F) (v : Fin s ⊕ Fin s → F),
      act A v = ((A : GL (Fin s ⊕ Fin s) F) :
        Matrix (Fin s ⊕ Fin s) (Fin s ⊕ Fin s) F) *ᵥ v := by
    intro A v
    exact statedSpEquivLinIsometryGroup_apply (ℓ := s) F A v
  have hact_planeThree : ∀ i : Fin s,
      act (planeThree (F := F) s i) = planeThreeLin (F := F) s i := by
    intro i
    refine LinearEquiv.ext fun v => ?_
    rw [hact_apply]
    exact (planeThreeLin_eq_matVec i v).symm
  let u : Fin 3 → (Fin s ⊕ Fin s → F) := fun i => Pi.single (Sum.inl (idx i)) 1
  have hord : ∀ i : Fin 3, orderOf (planeThree (F := F) s (idx i)) = 3 := by
    intro i
    exact orderOf_eq_prime (planeThree_pow_three (idx i)) (planeThree_ne_one (idx i))
  have hcomm : ∀ i j : Fin 3,
      Commute (planeThree (F := F) s (idx i)) (planeThree (F := F) s (idx j)) := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact Commute.refl _
    · exact planeThree_commute (fun h => hij (hidx h))
  have hmove : ∀ (i : Fin 3) (a : ℤ),
      act (planeThree (F := F) s (idx i) ^ a) (u i) = u i → (3 : ℤ) ∣ a := by
    intro i a ha
    have ht : orderOf (planeThree (F := F) s (idx i)) = 3 := hord i
    have hmem : (planeThree (F := F) s (idx i) ^ a) ∈
        Subgroup.zpowers (planeThree (F := F) s (idx i)) :=
      Subgroup.mem_zpowers_iff.mpr ⟨a, rfl⟩
    rw [mem_zpowers_iff_mem_range_orderOf, ht] at hmem
    obtain ⟨k, hk, hka⟩ := Finset.mem_image.1 hmem
    rw [Finset.mem_range] at hk
    rw [← hka] at ha
    have hpow : act (planeThree (F := F) s (idx i) ^ k) =
        (planeThreeLin (F := F) s (idx i)) ^ k := by
      rw [map_pow, hact_planeThree]
    rw [hpow] at ha
    interval_cases k
    · have hta : planeThree (F := F) s (idx i) ^ a = 1 := by
        rw [← hka]; exact pow_zero _
      have ht' : (3 : ℤ) = (orderOf (planeThree (F := F) s (idx i)) : ℤ) := by rw [ht]; norm_num
      rw [ht', orderOf_dvd_iff_zpow_eq_one]
      exact hta
    · rw [pow_one, planeThreeLin_single_inl] at ha
      have hne : (Pi.single (Sum.inr (idx i)) (1 : F) : Fin s ⊕ Fin s → F) ≠
          (Pi.single (Sum.inl (idx i)) (1 : F) : Fin s ⊕ Fin s → F) := by
        intro h
        have := congrFun h (Sum.inr (idx i))
        simp at this
      exact absurd ha hne
    · rw [planeThreeLin_sq_single_inl] at ha
      have hne : (Pi.single (Sum.inl (idx i)) (1 : F) : Fin s ⊕ Fin s → F) +
          (Pi.single (Sum.inr (idx i)) (1 : F) : Fin s ⊕ Fin s → F) ≠
          (Pi.single (Sum.inl (idx i)) (1 : F) : Fin s ⊕ Fin s → F) := by
        intro h
        have := congrFun h (Sum.inr (idx i))
        simp at this
      exact absurd ha hne
  have hfix : ∀ i j : Fin 3, i ≠ j →
      act (planeThree (F := F) s (idx i)) (u j) = u j := by
    intro i j hij
    rw [hact_planeThree]
    exact planeThreeLin_apply_single_inl_of_ne (fun h => hij (hidx h).symm)
  obtain ⟨Q, -, hQe, -, hQrank⟩ := CFSG.exists_elemAbelian_of_commuting_moving
    (F := F) (X := Fin s ⊕ Fin s → F) (G := StatedSp s F) (ι := Fin 3) (r := 3)
    (by norm_num) (fun i => planeThree (F := F) s (idx i)) u act
    (fun i => Subgroup.mem_top _) hord hcomm hmove hfix
  exact ⟨Q, hQe, by simpa using hQrank⟩

theorem exists_elemAbelian_three_of_mulEquiv_card_two
    {F J : Type} [Field F] [Finite F] [CharP F 2] [Group J] [Finite J] {s : ℕ}
    (hcard : Nat.card F = 2) (hs : 3 ≤ s) (e : J ≃* StatedSp s F) :
    ∃ Q : Subgroup J, IsElemAbelian 3 Q ∧ 3 ≤ CFSG.Open.pRank 3 Q := by
  obtain ⟨Q₀, hQ₀, hrank₀⟩ := spF2QTorus_holds s F hcard hs
  refine ⟨Q₀.map e.symm.toMonoidHom, CFSG.SectionRank.isElemAbelian_map hQ₀ _, ?_⟩
  have htop : (⊤ : Subgroup Q₀).map (e.symm.toMonoidHom.comp Q₀.subtype) =
      Q₀.map e.symm.toMonoidHom := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  have hrank : CFSG.Open.pRank 3 (Q₀.map e.symm.toMonoidHom) =
      CFSG.Open.pRank 3 Q₀ := by
    rw [← htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q₀]
    exact CFSG.LocalAnalysis.GLTheoremB.pRank_map_eq_of_injective (by norm_num) _
      (fun x y h => Subtype.ext (e.symm.injective h)) ⊤
  rwa [hrank]

end SpEngine

end CFSG.LocalAnalysis.GLTheoremA.Y10F

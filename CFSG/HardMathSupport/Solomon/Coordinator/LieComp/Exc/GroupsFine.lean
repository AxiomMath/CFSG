module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsFine
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSL
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.FieldCopy
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.G2TwoChev
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Ree
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.LinearPlane

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.RankThree.PartTwo

set_option linter.unusedSectionVars false

section G2


theorem exists_primePower_card_field {k : Type} [Field k] [Finite k] {ℓ : ℕ} (hℓ : ringChar k = ℓ) :
    ∃ q : TauCeti.PrimePower, q.p = ℓ ∧ Nat.card k = q.card := by
  classical
  haveI : Fintype k := Fintype.ofFinite _
  haveI : CharP k ℓ := hℓ ▸ ringChar.charP k
  obtain ⟨n, hp, hcard⟩ := FiniteField.card k ℓ
  exact ⟨⟨ℓ, n, hp, n.pos⟩, rfl, by
    rw [Nat.card_eq_fintype_card, hcard, TauCeti.PrimePower.card_def]⟩

theorem compsFine_adjointGroup_G2 {k : Type} [Field k] [Finite k] {ℓ : ℕ} (hℓ : ringChar k = ℓ) :
    CompsFine ℓ ↥(adjointGroup .G2 k) := by
  classical
  haveI : Finite (ModGL .G2 k) := finite_modGL
  haveI : Finite ↥(adjointGroup .G2 k) := Subtype.finite
  by_cases hk2 : Nat.card k = 2
  · obtain ⟨hDs, hDcard⟩ := ExcCopy.g2Two_derived_exc hk2
    obtain ⟨q, hqp, hqcard⟩ := exists_primePower_card_field hℓ
    have hℓ2 : ℓ = 2 := by
      have h1 : ℓ ^ q.exponent = 2 := by
        rw [← hqp, ← TauCeti.PrimePower.card_def, ← hqcard]
        exact hk2
      exact (Nat.prime_dvd_prime_iff_eq (hqp ▸ q.prime_p) Nat.prime_two).1
        (by rw [← h1]; exact dvd_pow_self _ q.exponent_pos.ne')
    subst hℓ2
    haveI := hDs
    have hDnc : ∃ a b : ↥(commutator ↥(adjointGroup .G2 k)), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      let _ : CommGroup ↥(commutator ↥(adjointGroup .G2 k)) :=
        { (inferInstance : Group ↥(commutator ↥(adjointGroup .G2 k))) with mul_comm := hcon }
      have hp := IsSimpleGroup.prime_card (α := ↥(commutator ↥(adjointGroup .G2 k)))
      rw [hDcard] at hp
      exact absurd hp (by norm_num)
    have hZ : Subgroup.center ↥(commutator ↥(adjointGroup .G2 k)) = ⊥ :=
      b3Lie_center_eq_bot hDnc
    refine compsFine_of_commutator (LieSemisimple.isQuasisimple_of_isSimpleGroup hDs hDnc)
      ⟨_, inferInstance, inferInstance,
        lieFactorData_of_simple hDnc (isChevSimple_two_derived_G2 hk2), MonoidHom.id _,
        Function.surjective_id, by simp⟩ ?_
    exact isEmpty_quotient_center_alt6 hZ
      (isEmpty_mulEquiv_alt6_of_card_ne (by rw [hDcard]; norm_num))
  · have hk3 : 3 ≤ Nat.card k := by
      have h2 : 1 < Nat.card k := Finite.one_lt_card
      omega
    have hperf := ExcCopy.isPerfect_adjointGroup .G2 k (fun _ => hk3)
    obtain ⟨hs, hnc⟩ := ExcCopy.isSimpleGroup_adjointGroup_of_perfect .G2 k hperf
    obtain ⟨q, hqp, hqcard⟩ := exists_primePower_card_field hℓ
    have hq3 : 3 ≤ q.card := by rw [← hqcard]; exact hk3
    have hv : (TauCeti.LieTypeIndex.G2 q).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hq3, by simp⟩
    obtain ⟨eq⟩ := CFSG.TauCetiBridge.Even.chevalleyBridgesAll.g2 q hv k hqcard
    have hZ : Subgroup.center ↥(adjointGroup .G2 k) = ⊥ := center_adjointGroup_eq_bot
    let eX : ↥(adjointGroup .G2 k) ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans eq
    have hchev := isChevSimple_of_lie (q := ℓ) ⟨.G2 q, hv⟩
      (by rw [TauCeti.LieTypeIndex.characteristic_G2]; exact hqp) eX
    haveI := hs
    exact compsFine_of_simple hnc hchev
      ⟨fun f => (isEmpty_cat_alt6 ⟨.G2 q, hv⟩ (Or.inl rfl)).false (eX.symm.trans f)⟩

end G2

section PGL

open CFSG.PGLModel CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec8

theorem ker_subgroupMap_mk_le_center {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (S : Subgroup (GL ι K)) :
    ((Matrix.ProjGenLinGroup.mk : GL ι K →* Matrix.ProjGenLinGroup ι K).subgroupMap S).ker ≤
      Subgroup.center ↥S := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h1 : (Matrix.ProjGenLinGroup.mk (x : GL ι K) : Matrix.ProjGenLinGroup ι K) = 1 :=
    congrArg Subtype.val hx
  have h2 : (x : GL ι K) ∈ Subgroup.center (GL ι K) := (QuotientGroup.eq_one_iff _).1 h1
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext ((Subgroup.mem_center_iff.1 h2) (y : GL ι K))


variable {K : Type} [Field K]

theorem compsFine_projImage_glPi_of_cover {π : Bool} {p f : ℕ} (hK : Sec4.PiField π p f K)
    (hq2 : 2 < p ^ f) {X : Type} [Group X] [Finite X] (hXd : LieFactorData p X)
    (g : X →* ↥(projImage (Sec4.slPi π 3 (p ^ f) K))) (hg : Function.Surjective g)
    (hgk : g.ker ≤ Subgroup.center X)
    (hA6 : IsEmpty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin 6))) :
    CompsFine p ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _)
      (QuotientGroup.mk'_surjective _)
  haveI : Finite ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := Subtype.finite
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hR := Item8KFacts2Proof.perfectResidual_projImage_glPi_eq hK hq2
  let eR : ↥(CFSG.perfectResidual ↥(projImage (Sec4.glPi π 3 (p ^ f) K))) ≃*
      ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    (MulEquiv.subgroupCongr hR).trans (Subgroup.subgroupOfEquivOfLe hSP)
  have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  have hsS := Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  haveI := hsS
  have hqS : CFSG.IsQuasisimple ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperfS)).1
  refine compsFine_of_perfectResidual (CFSG.IsQuasisimple.of_mulEquiv eR hqS)
    ⟨X, inferInstance, inferInstance, hXd, eR.symm.toMonoidHom.comp g,
      eR.symm.surjective.comp hg, ?_⟩ ?_
  · intro x hx
    apply hgk
    rw [MonoidHom.mem_ker] at hx ⊢
    apply eR.symm.injective
    rw [map_one]
    exact hx
  · refine ⟨fun a => hA6.false ?_⟩
    have e₁ := (nonempty_centralQuotient_mulEquiv hXd.perfect g hg hgk).some
    exact (e₁.trans ((quotientCenterEquiv eR).symm)).trans a

theorem compsFine_projImage_glPi {π : Bool} {p f : ℕ} (hK : Sec4.PiField π p f K)
    (hπ2 : π = true → 2 < p ^ f) :
    CompsFine p ↥(projImage (Sec4.glPi π 3 (p ^ f) K)) := by
  classical
  haveI := hK.finite
  haveI : Fintype K := Fintype.ofFinite K
  have hp := hK.prime
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hq2 : 2 < p ^ f
  · let g₀ : ↥(Sec4.slPi π 3 (p ^ f) K) →* ↥(projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _).subgroupMap (Sec4.slPi π 3 (p ^ f) K)
    have hg₀ : Function.Surjective g₀ := MonoidHom.subgroupMap_surjective _ _
    have hg₀k := ker_subgroupMap_mk_le_center (Sec4.slPi π 3 (p ^ f) K)
    cases π
    · have hKcard : Fintype.card K = (p ^ f) ^ 2 := by
        rw [← Nat.card_eq_fintype_card, hK.card]
        rfl
      have hcharP : CharP K p :=
        charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hKcard, ← pow_mul, mul_comm])
      have hring : ringChar K = p := ringChar.eq K p
      have hmq : ((3 : ℕ), p ^ f) ≠ ((3 : ℕ), 2) := fun h => by
        have := (Prod.mk.inj h).2
        omega
      have hFD := suFactorFacts_holds K 3 (p ^ f) hKcard (by norm_num) hmq
      rw [hring] at hFD
      exact compsFine_projImage_glPi_of_cover hK hq2 (X := ↥(CFSG.Open.StatedSU 3 (p ^ f) K))
        hFD g₀ hg₀ hg₀k (suAltSixFacts_holds K 3 (p ^ f) hKcard (by norm_num))
    · have hKcard : Fintype.card K = p ^ f := by
        rw [← Nat.card_eq_fintype_card, hK.card]
        rfl
      have hcharP : CharP K p := charP_of_card_eq_prime_pow hKcard
      have hring : ringChar K = p := ringChar.eq K p
      have hFD := slFactorFacts_holds K 3 (by norm_num) (fun h => absurd h (by norm_num))
      rw [hring] at hFD
      let eSL : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥(Sec4.slPi true 3 (p ^ f) K) :=
        (MonoidHom.ofInjective
          (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 3) (R := K))).trans
          (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 3 K).symm)
      refine compsFine_projImage_glPi_of_cover hK hq2 (X := Matrix.SpecialLinearGroup (Fin 3) K)
        hFD (g₀.comp eSL.toMonoidHom) (hg₀.comp eSL.surjective) ?_ ⟨fun a => ?_⟩
      · intro x hx
        rw [MonoidHom.mem_ker] at hx
        have h2 := hg₀k (show eSL x ∈ g₀.ker from hx)
        rw [Subgroup.mem_center_iff] at h2 ⊢
        intro y
        apply eSL.injective
        rw [map_mul, map_mul]
        exact h2 (eSL y)
      · obtain ⟨h3, -⟩ := slAltSixFacts_holds K 3 (by norm_num) ⟨a⟩
        omega
  · have h2 : p ^ f = 2 := by
      have := hp.two_le
      have h3 : p ≤ p ^ f := Nat.le_self_pow (by have := hK.one_le; omega) p
      omega
    cases π
    · haveI := Sec13.isSolvable_projImage_glPi_two hK h2
      exact compsFine_of_isSolvable
    · exact absurd (hπ2 rfl) hq2

end PGL

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieCompHolds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TLevel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCount
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TOuter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace D4T

theorem exists_noncomm_of_simple_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)

theorem fixSubgroup_one {G : Type} [Group G] : fixSubgroup (1 : MulAut G) = ⊤ := by
  ext g
  rw [mem_fixSubgroup, MulAut.one_apply]
  simp

theorem card_pSimple_dvd {S : Type} [Group S] [Finite S] (p : ℕ) (J : Subgroup S) :
    Nat.card (PSimple p J) ∣ Nat.card J :=
  (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _)

theorem center_eq_bot_of_simple {T : Type} [Group T] [IsSimpleGroup T]
    (hnc : ∃ a b : T, a * b ≠ b * a) : Subgroup.center T = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center T) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    apply hab
    have ha : a ∈ Subgroup.center T := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 ha b).symm

theorem mem_center_of_conj_eq_one {G : Type} [Group G] {z : G} (h : MulAut.conj z = 1) :
    z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have := congrArg (fun φ : MulAut G => φ g) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

theorem fixSubgroup_conj_eq {G : Type} [Group G] (s : G) :
    fixSubgroup (MulAut.conj s) = Subgroup.centralizer {s} := by
  ext x
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    have : s * x = x * s := by
      calc s * x = s * x * s⁻¹ * s := by group
        _ = x * s := by rw [h]
    exact this.symm
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

section Row

set_option linter.unusedSectionVars false


theorem exists_model (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    (hq2 : q.card = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      Nonempty ((TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group ≃*
        StatedProj (StatedOmega (StatedQuadPlus 4 F))) := by
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq2] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq2
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
  rw [hp, he] at hmodel
  obtain ⟨-, F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  exact ⟨F, hF, hfin, by simpa using hcard, ⟨e⟩⟩

theorem noA8_inner (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq2 : q.card = 2)
    (a : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (J : Subgroup (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
    (hJ : GLAPComponent 3 (fixSubgroup (MulAut.conj a)) J) :
    ¬ Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨f⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_model q hv hq2
  obtain ⟨hfin, -⟩ := CFSG.Assembly.lie_finite_simple ⟨.D 4 q, hv⟩
  have h7 : 7 ∣ Nat.card J := by
    have h1 : Nat.card (PSimple 3 J) = 20160 := by
      rw [Nat.card_congr f.toEquiv, card_alt_eight]
    have h2 := card_pSimple_dvd 3 J
    rw [h1] at h2
    exact (by norm_num : 7 ∣ 20160).trans h2
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := J) 7 h7
  have hu7 : (u : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) ^ 7 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg Subtype.val this
  have hu1 : (u : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) ≠ 1 := by
    intro h
    have : u = 1 := Subtype.ext h
    rw [this, orderOf_one] at hu
    omega
  have hcomm : a * (u : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) =
      (u : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) * a := by
    have : (u : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) ∈ fixSubgroup (MulAut.conj a) := hJ.1 u.2
    rw [fixSubgroup_conj_eq, Subgroup.mem_centralizer_singleton_iff] at this
    exact this.symm
  haveI : CharP F 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by rw [hF]; norm_num)
  let ψ := e.trans (CFSG.HardMathSupport.Curtis.Coordinator.projEquivElementary F hF (by norm_num : 3 ≤ 4))
  have hmem : ∀ g, ((ψ g : ↥(CFSG.ClassicalGroups.Orthogonal.elementaryGroup
      (CFSG.LieType.Universal.Spin.quadPlus 4 F))) : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) ∈
      TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 4 F) := fun g =>
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_le_orthogonalGroup _ (ψ g).2
  have key := no_commuting_three_seven hF (hmem a) (hmem (u : _))
    (by rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hcomm])
    (by rw [← Subgroup.coe_pow, ← map_pow, ha3, map_one]; rfl)
    (by rw [← Subgroup.coe_pow, ← map_pow, hu7, map_one]; rfl)
  rcases key with h | h
  · exact ha1 (ψ.injective (Subtype.ext (by rw [map_one]; exact h)))
  · exact hu1 (ψ.injective (Subtype.ext (by rw [map_one]; exact h)))

theorem noA8_outer (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq2 : q.card = 2)
    (β : MulAut (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group) (hβ3 : β ^ 3 = 1)
    (hout : ∀ a : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, MulAut.conj a ≠ β)
    (J : Subgroup (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
    (hJ : GLAPComponent 3 (fixSubgroup β) J) :
    ¬ Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 8)) := by
  rintro ⟨f⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_model q hv hq2
  obtain ⟨hfin, -⟩ := CFSG.Assembly.lie_finite_simple ⟨.D 4 q, hv⟩
  obtain ⟨eC⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.D4Bridge.nonempty_statedProj_equiv_adjointGroup F
  let e₂ := e.trans eC
  have hα : MulAut.congr e₂ β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hout' : ∀ h : adjointGroup Tag.D4 F, MulAut.conj h ≠ MulAut.congr e₂ β := by
    intro h hh
    apply hout (e₂.symm h)
    refine MulEquiv.ext fun y => e₂.injective ?_
    have h1 := congrArg (fun φ : MulAut (adjointGroup Tag.D4 F) => φ (e₂ y)) hh
    simp only [MulAut.conj_apply, MulAut.congr_apply] at h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simpa using h1
  have hdvd := outer_card_dvd hF (MulAut.congr e₂ β) hα hout'
  have hcardβ : Nat.card ↥(fixSubgroup β) = Nat.card ↥(fixSubgroup (MulAut.congr e₂ β)) :=
    Nat.card_congr (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroupCongrEquiv e₂ β).toEquiv
  have h5 : 5 ∣ Nat.card (PSimple 3 J) := by
    rw [Nat.card_congr f.toEquiv, card_alt_eight]
    norm_num
  have hdiv : Nat.card (PSimple 3 J) ∣ Nat.card ↥(fixSubgroup β) :=
    (card_pSimple_dvd 3 J).trans (Subgroup.card_dvd_of_le hJ.1)
  have h5' : 5 ∣ CFSG.Open.ordTrialityD4 2 := h5.trans (hdiv.trans (hcardβ ▸ hdvd))
  revert h5'
  unfold CFSG.Open.ordTrialityD4
  decide +kernel

theorem hcard_S (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid) (hq2 : q.card = 2) :
    Nat.card (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group = N8 := by
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq2] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq2
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have hmodel := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
  rw [hp, he] at hmodel
  have := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
  rw [this]
  decide +kernel

theorem noA8_holds :
    ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.card = 2 →
      ∀ β : MulAut (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, β ^ 3 = 1 → β ≠ 1 →
        ∀ J : Subgroup (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group,
          GLAPComponent 3 (fixSubgroup β) J → ¬ Nonempty (PSimple 3 J ≃* alternatingGroup (Fin 8)) := by
  intro q hv hq2 β hβ3 hβ1 J hJ
  by_cases hin : ∃ a : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, MulAut.conj a = β
  · obtain ⟨a, rfl⟩ := hin
    obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.D 4 q, hv⟩
    have hcardS : Nat.card (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group = N8 :=
      hcard_S q hv hq2
    have hnc : ∃ x y : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, x * y ≠ y * x :=
      exists_noncomm_of_simple_not_prime (by rw [hcardS]; unfold N8; norm_num)
    have ha3 : a ^ 3 = 1 := by
      have h1 : MulAut.conj (a ^ 3) = 1 := by rw [map_pow]; exact hβ3
      have h2 := mem_center_of_conj_eq_one h1
      rw [center_eq_bot_of_simple hnc, Subgroup.mem_bot] at h2
      exact h2
    have ha1 : a ≠ 1 := fun h => hβ1 (by rw [h, map_one])
    exact noA8_inner q hv hq2 a ha3 ha1 J hJ
  · push Not at hin
    exact noA8_outer q hv hq2 β hβ3 hin J hJ

theorem kdLieRowOmega8PlusTwo_of_noA8 :
    KDLieRowOmega8PlusTwo := by
  have hno := noA8_holds
  intro q hv hq2
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq2] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq2
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  obtain ⟨hfin, hsimp⟩ := CFSG.Assembly.lie_finite_simple ⟨.D 4 q, hv⟩
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group .POmegaPlus 4 2 1 := by
    have := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv
      (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group)
    rwa [hp, he] at this
  have hcardS : Nat.card (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group = N8 := by
    have := (CFSG.Timmesfeld.card_statedClassicalModel_two hmodel).2.2.2.1 rfl
    rw [this]
    decide +kernel
  have hnc : ∃ a b : (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group, a * b ≠ b * a :=
    exists_noncomm_of_simple_not_prime (by rw [hcardS]; unfold N8; norm_num)
  intro α hα J hJ
  by_cases hα1 : α = 1
  · subst hα1
    rw [fixSubgroup_one] at hJ
    obtain ⟨f⟩ := chevQ_pSimple_top_equiv Nat.prime_three hnc hJ
    rw [kLevel_congr 3 f]
    exact kLevel_le_two_of_k2 ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, ⟨rfl, hq2⟩, ⟨MulEquiv.refl _⟩⟩
  · have hLC := lieComp_holds (TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩).Group hsimp hnc ⟨.D 4 q, hv⟩
      ⟨MulEquiv.refl _⟩ α hα J hJ
    have hchev : IsChevSimple 2 (PSimple 3 J) := by
      have h1 := hLC.1.chev
      rw [show CFSG.HardMathSupport.Solomon.Coordinator.lieIndexChar (TauCeti.LieTypeIndex.D 4 q) = 2
        from hp] at h1
      exact h1
    refine kLevel_le_two_of_chev2 hchev ?_ (hno q hv hq2 α hα hα1 J hJ)
    rw [← hcardS]
    exact (card_pSimple_dvd 3 J).trans (Subgroup.card_subgroup_dvd_card J)

end Row

end D4T

set_option linter.unusedSectionVars false in
theorem kdLieRowOmega8PlusTwo_holds :
    KDLieRowOmega8PlusTwo :=
  D4T.kdLieRowOmega8PlusTwo_of_noA8

end CFSG.LocalAnalysis.GLTheoremA

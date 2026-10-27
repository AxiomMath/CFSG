module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabSuzU43

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U43
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest
open scoped commutatorElement

theorem exists_hom_of_isPresentation {X G : Type*} [Group X] [Group G] {ι : Type*} {g : ι → X}
    {R : Set (FreeGroup ι)} (hP : IsPresentation g R) (h : ι → G)
    (hrel : ∀ r ∈ R, FreeGroup.lift h r = 1) : ∃ ψ : X →* G, ∀ i, ψ (g i) = h i := by
  have hker : (FreeGroup.lift g).ker ≤ (FreeGroup.lift h).ker := by
    rw [hP.ker_lift]
    exact Subgroup.normalClosure_le_normal (fun r hr => hrel r hr)
  refine ⟨MonoidHom.liftOfSurjective (FreeGroup.lift g) hP.lift_surjective
    ⟨FreeGroup.lift h, hker⟩, fun i => ?_⟩
  have := MonoidHom.liftOfRightInverse_comp_apply (FreeGroup.lift g)
    (Function.surjInv hP.lift_surjective) (Function.rightInverse_surjInv hP.lift_surjective)
    ⟨FreeGroup.lift h, hker⟩ (FreeGroup.of i)
  simpa using this


theorem u43_central_ext_gen {T : Type} [Group T] [Finite T] (Z : Subgroup T) (a b : T)
    (hZ : Z ≤ Subgroup.center T) (hgen : Subgroup.closure ({a, b} : Set T) ⊔ Z = ⊤)
    (hrel : ∀ w ∈ rels, evalW ![a, b] w ∈ Z) (hnc : a * b ≠ b * a)
    (hZK : Z ≤ commutator T) :
    CFSG.Open.IsQuasisimple T ∧ Subgroup.center T = Z ∧
      Nonempty ((T ⧸ Subgroup.center T) ≃* X₀) := by
  classical
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZ
  let π : T →* T ⧸ Z := QuotientGroup.mk' Z
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hπker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hgenG : Subgroup.closure ({π a, π b} : Set (T ⧸ Z)) = ⊤ := by
    have h1 : (Subgroup.closure ({a, b} : Set T) ⊔ Z).map π =
        Subgroup.closure (π '' ({a, b} : Set T)) ⊔ Z.map π := by
      rw [Subgroup.map_sup, MonoidHom.map_closure]
    have htop : (⊤ : Subgroup T).map π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 hπs
    have hZbot : Z.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨z, hz, rfl⟩
      exact (QuotientGroup.eq_one_iff z).2 hz
    rw [hgen, htop, hZbot, sup_bot_eq, Set.image_insert_eq, Set.image_singleton] at h1
    exact h1.symm
  have hrelG : ∀ r ∈ wordSet rels, FreeGroup.lift (![π a, π b] : Fin 2 → T ⧸ Z) r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    have h1 := map_evalW π ![a, b] w
    have h2 : (fun i => π (![a, b] i)) = (![π a, π b] : Fin 2 → T ⧸ Z) := by
      funext i
      fin_cases i <;> rfl
    rw [h2] at h1
    rw [lift_mk_eq_evalW, ← h1]
    exact (QuotientGroup.eq_one_iff _).2 (hrel w hw)
  obtain ⟨ψ, hψ⟩ := exists_hom_of_isPresentation isPresentation_X₀ ![π a, π b] hrelG
  have hψx : ψ xElt = π a := by simpa [CFSG.Sporadic.Bridge.TwoGen.img2] using hψ 0
  have hψy : ψ yElt = π b := by simpa [CFSG.Sporadic.Bridge.TwoGen.img2] using hψ 1
  haveI := isSimpleGroup_X₀'
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgenG, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨xElt, hψx⟩
    · exact ⟨yElt, hψy⟩
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      have h1 : π a = 1 := by
        rw [← hψx]
        exact (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top xElt))
      have h2 : a ∈ Z := (QuotientGroup.eq_one_iff a).1 h1
      exact hnc (Subgroup.mem_center_iff.1 (hZ h2) b).symm
  have eG : (T ⧸ Z) ≃* X₀ := (MulEquiv.ofBijective ψ ⟨hinj, hsurj⟩).symm
  have hsimpleG : IsSimpleGroup (T ⧸ Z) := eG.isSimpleGroup_congr.2 isSimpleGroup_X₀'
  have hGcard : Nat.card (T ⧸ Z) = 3265920 := by
    rw [Nat.card_congr eG.toEquiv]
    exact card_X₀
  have hnab : ∃ x y : T ⧸ Z, x * y ≠ y * x :=
    exists_noncomm_of_simple_sq_dvd Nat.prime_two (by rw [hGcard]; norm_num)
  have hcenG : Subgroup.center (T ⧸ Z) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (T ⧸ Z))
      with h | h
    · exact h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      exact hxy (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top y) x)
  have hcommG : commutator (T ⧸ Z) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (T ⧸ Z))
      with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hnab
      have h1 : ⁅x, y⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      exact hxy (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  have hcenT : Subgroup.center T = Z := by
    refine le_antisymm (fun g hg => ?_) hZ
    have hπg : π g ∈ Subgroup.center (T ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨t, rfl⟩ := hπs h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hg t]
    rw [hcenG, Subgroup.mem_bot] at hπg
    rw [← hπker]
    exact hπg
  have hperf : commutator T = ⊤ := by
    have htop : (⊤ : Subgroup T).map π = ⊤ := by
      rw [← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.2 hπs
    have hmapc : (commutator T).map π = commutator (T ⧸ Z) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator, htop]
    rw [eq_top_iff]
    intro t _
    have ht : π t ∈ (commutator T).map π := by rw [hmapc, hcommG]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkt⟩ := Subgroup.mem_map.1 ht
    have hkz : k⁻¹ * t ∈ Z := by
      rw [← hπker]
      change π (k⁻¹ * t) = 1
      rw [map_mul, map_inv, hkt, inv_mul_cancel]
    have : t = k * (k⁻¹ * t) := by group
    rw [this]
    exact (commutator T).mul_mem hk (hZK hkz)
  have eT : (T ⧸ Subgroup.center T) ≃* X₀ := (QuotientGroup.quotientMulEquivOfEq hcenT).trans eG
  exact ⟨⟨hperf, eT.isSimpleGroup_congr.2 isSimpleGroup_X₀'⟩, hcenT, ⟨eT⟩⟩

end CFSG.HardMathSupport.Dickson.I271

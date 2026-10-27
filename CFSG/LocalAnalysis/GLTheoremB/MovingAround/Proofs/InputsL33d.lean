module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotTorus
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUAll
import CFSG.HardMathSupport.Timmesfeld.CrossChar.G2LongFrame
import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodUntwist
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidRank

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33 (card_of_isLpType_three_three
  exists_card_eq_three_pow sl_l33 su_l33_false)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Order

theorem not_dvd_of_sl2_card {a : ℕ} (ha : 2 ≤ a) : ¬ 3 ^ a * ((3 ^ a) ^ 2 - 1) ∣ 11232 := by
  intro h
  have h3 : 3 ^ a ∣ 11232 := (Dvd.intro _ rfl).trans h
  have ha3 : a ≤ 3 := by
    by_contra hlt
    push Not at hlt
    have h81 : 3 ^ 4 ∣ 11232 := (pow_dvd_pow 3 hlt).trans h3
    omega
  interval_cases a <;> norm_num at h

theorem false_of_sl2_hom {E : Type*} [Field E] [Finite E] (hE : ringChar E = 3)
    (h9 : 9 ≤ Nat.card E) {T : Type*} [Group T] (g : SL(2, E) →* T)
    (hker : g.ker ≤ Subgroup.center SL(2, E)) (hL : IsLpType 3 3 (T ⧸ Subgroup.center T)) :
    False := by
  classical
  obtain ⟨a, -, hEa⟩ := exists_card_eq_three_pow hE
  have ha : 2 ≤ a := by
    by_contra hlt
    push Not at hlt
    have : 3 ^ a ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hq : CFSG.IsQuasisimple SL(2, E) :=
    CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
      (Or.inr (by omega))
  have hKZ := card_of_isLpType_three_three hL
  let φ : SL(2, E) →* T ⧸ Subgroup.center T := (QuotientGroup.mk' (Subgroup.center T)).comp g
  rcases quasisimple_subnormal_subgroups hq (MonoidHom.normal_ker φ).isSubnormal with htop | hcen
  ·
    exfalso
    have hcomm : commutator SL(2, E) ≤ g.ker := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have hx : g x ∈ Subgroup.center T := by
        have : x ∈ φ.ker := htop ▸ Subgroup.mem_top x
        rw [MonoidHom.mem_ker] at this
        exact (QuotientGroup.eq_one_iff (g x)).1 this
      rw [commutatorElement_eq_one_iff_commute]
      exact ((Subgroup.mem_center_iff.1 hx) (g y)).symm
    have hZ : Subgroup.center SL(2, E) = ⊤ := by
      rw [eq_top_iff, ← hq.1.commutator_eq_top]
      exact hcomm.trans hker
    haveI := hq.2.1.toNontrivial
    obtain ⟨u, hu⟩ := exists_ne (1 : SL(2, E) ⧸ Subgroup.center SL(2, E))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    exact hu ((QuotientGroup.eq_one_iff x).2 (hZ ▸ Subgroup.mem_top x))
  ·
    have hN : Nat.card φ.ker ∣ 2 := by
      have h1 : Nat.card φ.ker ∣ Nat.card (Subgroup.center SL(2, E)) :=
        Subgroup.card_dvd_of_le hcen
      rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center E 2 (by norm_num)] at h1
      exact h1.trans (Nat.gcd_dvd_left 2 _)
    have hR : Nat.card φ.range ∣ 5616 := by
      rw [← hKZ]
      exact Subgroup.card_subgroup_dvd_card _
    have hcard : Nat.card SL(2, E) = Nat.card φ.ker * Nat.card φ.range := by
      rw [φ.ker.card_eq_card_quotient_mul_card_subgroup, mul_comm,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    have hSL : Nat.card SL(2, E) = 3 ^ a * ((3 ^ a) ^ 2 - 1) := by
      rw [CFSG.OrderReductions.LinearOrders.card_specialLinear E 2 (by norm_num), hEa]
      simp
    apply not_dvd_of_sl2_card ha
    rw [← hSL, hcard, show (11232 : ℕ) = 2 * 5616 by norm_num]
    exact Nat.mul_dvd_mul hN hR

end Order

section Inner

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem exists_mem_componentRoots {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    ∃ γ, γ ∈ componentRoots χ i := by
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  exact ⟨γ, hγ, rfl⟩

theorem le_pow_orbit {r e s : ℕ} (hr : 0 < r) (hs : 0 < s) : r ^ e ≤ r ^ (e * s) :=
  Nat.pow_le_pow_right hr (Nat.le_mul_of_pos_right e hs)

theorem noL33_rationalComponent_inner (hL3 : ringChar L = 3) (hq9 : 9 ≤ S.D.q)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwistT S hT i hs0 hinner
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ9 : 9 ≤ r ^ (e * s) := by
    calc 9 ≤ S.D.q := hq9
      _ = r ^ e := hq
      _ ≤ r ^ (e * s) := le_pow_orbit hr.pos hs0
  obtain ⟨t, ht⟩ := exists_unit_sq_ne_one (L := L) σ hσ' (Nat.mul_pos he hs0) (by omega)
  have hsL : ∃ u : Lˣ, u ^ 2 ≠ 1 := by
    refine ⟨Units.map (fixSubfield σ).subtype.toMonoidHom t, fun h => ht ?_⟩
    apply Units.ext
    apply Subtype.ext
    simpa using congrArg (fun x : Lˣ => (x : L)) h
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := r)
      (n := e * s)
    (Nat.mul_pos he hs0) σ hσ'
  have hperfC := isPerfect_componentRootSpan_of_sq_ne_one (K := fixSubfield σ)
    (χ := rootCharHom a) ht i
  obtain ⟨f, hf1, hker, hf2⟩ :=
    rationalComponent_eq_range_componentRootSpanT S hT i hs hmin σ z hnorm hz hsL
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (Subgroup.isPerfect_iff.1 hperfC)) hf1
  obtain ⟨γ, hγ⟩ := exists_mem_componentRoots i
  have hγr : IsRoot τ γ := isRoot_of_mem_componentRoots hγ
  have hneg : -γ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem γ hγ
  have hle : (rootSL2 τ (fixSubfield σ) γ).range ≤
      componentRootSpan (fixSubfield σ) (rootCharHom a) i := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hγr]
    exact sup_le (le_iSup₂_of_le γ hγ le_rfl) (le_iSup₂_of_le (-γ) hneg le_rfl)
  let ι : SL(2, ↥(fixSubfield σ)) →* ↥(componentRootSpan (fixSubfield σ) (rootCharHom a) i) :=
    (rootSL2 τ (fixSubfield σ) γ).codRestrict _ (fun A => hle ⟨A, rfl⟩)
  have hι : Function.Injective ι := fun A B h =>
    CFSG.RankThree.Chevalley.rootSL2_injective_of_field γ (congrArg Subtype.val h)
  let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (f.comp ι).codRestrict _ (fun A => hRf ▸ ⟨ι A, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
    intro A hA
    have hA' : ι A ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hA ⊢
      exact congrArg Subtype.val hA
    have hAZ := hker hA'
    rw [Subgroup.mem_center_iff] at hAZ ⊢
    intro B
    exact hι (by rw [map_mul, map_mul]; exact hAZ (ι B))
  have hring : ringChar (fixSubfield σ) = 3 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield' _).trans hL3
  intro hL
  exact false_of_sl2_hom hring (by rw [hKcard]; exact hQ9) g hgker hL

end Inner

section TypeA

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem noL33_of_split_frame (hL3 : ringChar L = 3) (hq9 : 9 ≤ S.D.q)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π x) (π y)) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.split_exists_hom S hT i hν hψ hΨ π hπ hr
      hchar he hq
  obtain ⟨hfinK, hKcard⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield
    (L := L) (r := r) (n := e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))
    (Nat.mul_pos he hs0) σQ hσc
  have hperf : Group.IsPerfect SL(ν, ↥(fixSubfield σQ)) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hν
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 hperf) hf1
  let g : SL(ν, ↥(fixSubfield σQ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgsurj : Function.Surjective g := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    exact ⟨c, Subtype.ext hc⟩
  have hgker : g.ker ≤ Subgroup.center SL(ν, ↥(fixSubfield σQ)) := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  have hring : ringChar (fixSubfield σQ) = 3 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield' _).trans hL3
  intro hL
  have h3 := (sl_l33 hring (by omega) g hgsurj hgker hL).2
  have hQ9 : 9 ≤ r ^ (e * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    calc 9 ≤ S.D.q := hq9
      _ = r ^ e := hq
      _ ≤ _ := le_pow_orbit hr.pos hs0
  rw [hKcard] at h3
  omega

theorem noL33_of_unitary_frame (hL3 : ringChar L = 3) (hq9 : 9 ≤ S.D.q)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) {ν : ℕ} (hν : 3 ≤ ν)
    {ψ : SL(ν, L) →* ModGL τ L} {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    (hΨ : componentRoots (rootCharHom a) i = frameRoots σ) (π : Equiv.Perm (Fin ν))
    (hπ : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
      (componentRoots (rootCharHom a) i)] (σ x y) = σ (π y) (π x)) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hes : 0 < e * s := Nat.mul_pos he hs0
  have hr3 : r = 3 := by rw [← hL3]; exact (ringChar.eq L r).symm
  have hQ9 : 9 ≤ r ^ (e * s) := by
    calc 9 ≤ S.D.q := hq9
      _ = r ^ e := hq
      _ ≤ _ := le_pow_orbit hr.pos hs0
  obtain ⟨σQ, hσc, f, hf1, hfker, hf2⟩ := two_suN_exists_hom S hT i hν hψ hΨ π hπ hr hchar he hq
  obtain ⟨-, hqsC, -⟩ := stdUnitary_fixSubgroup (ν := ν) hr hes σQ hσc hν
  have h32 : (ν, r ^ (e * s)) ≠ (3, 2) := fun h => by
    have := congrArg Prod.snd h
    simp only at this
    omega
  have hRf : f.range = rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    le_antisymm (hf2 (hqsC h32).1) hf1
  obtain ⟨F, hFcard, ⟨eC⟩⟩ := two_suN_exists_equiv hr hes σQ hσc hν
  let g : _ →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    f.codRestrict _ (fun c => hRf ▸ ⟨c, rfl⟩)
  have hgker : g.ker ≤ Subgroup.center _ := by
    intro c hc
    apply hfker
    rw [MonoidHom.mem_ker] at hc ⊢
    exact congrArg Subtype.val hc
  let g' : ↥(StatedSU ν (r ^ (e * s)) F) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    g.comp eC.toMonoidHom
  have hg'surj : Function.Surjective g' := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ : x ∈ f.range := hRf ▸ hx
    obtain ⟨c', rfl⟩ := eC.surjective c
    exact ⟨c', Subtype.ext hc⟩
  have hg'ker : g'.ker ≤ Subgroup.center ↥(StatedSU ν (r ^ (e * s)) F) :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ker_comp_mulEquiv_le_center eC g hgker
  have hU : UnitaryFieldData r (e * s) F :=
    ⟨hr, hes, by rw [hFcard, ← pow_mul, mul_comm]⟩
  intro hL
  exact su_l33_false hU hr3 hν g' hg'surj hg'ker hL

theorem noL33_rationalComponent_typeA (hL3 : ringChar L = 3) (hq9 : 9 ≤ S.D.q) {p : ℕ}
    (hp : p.Prime) (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  have hℓp : ringChar L ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓp
  obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
    g2LongA2Frame_proved S hp hpL hTp i h2 hn
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
    rw [hs, hΨ] at h2
    exact h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
      (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact noL33_of_split_frame S hL3 hq9 hT i hν hψ hΨ π hπ
  · exact noL33_of_unitary_frame S hL3 hq9 hT i hν hψ hΨ π hπ

end TypeA

section WeylConj

variable {τ : Tag}

theorem iform_self_eq_two_of_simplyLaced' (hτ : SimplyLacedTag τ) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : iform α α = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hα
  rcases hτ with rfl | rfl | rfl | rfl <;> simpa [Tag.symmetrizer] using hj

theorem corootPair_eq_iform (hτ : SimplyLacedTag τ) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (v : Fin τ.rank → ℤ) : corootPair β v = iform β v := by
  have h := corootPair_mul hβ v
  rw [iform_self_eq_two_of_simplyLaced' hτ hβ] at h
  linarith

theorem exists_weyl_smul_eq_of_iform_ne_zero (hτ : SimplyLacedTag τ) {Ψ : Set (Fin τ.rank → ℤ)}
    {α β : Fin τ.rank → ℤ} (hα : α ∈ Ψ) (hβ : β ∈ Ψ) (hαr : IsRoot τ α) (hβr : IsRoot τ β)
    (h : iform α β ≠ 0) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ}, w • α = β := by
  have hrα : rootReflection α ∈
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    Subgroup.subset_closure ⟨α, hα, rfl⟩
  have hrβ : rootReflection β ∈
      Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ Ψ, s = rootReflection γ} :=
    Subgroup.subset_closure ⟨β, hβ, rfl⟩
  have hαα := iform_self_eq_two_of_simplyLaced' hτ hαr
  have hββ := iform_self_eq_two_of_simplyLaced' hτ hβr
  by_cases heq : α = β
  · exact ⟨1, one_mem _, by rw [one_smul, heq]⟩
  by_cases hneg : α = -β
  · refine ⟨rootReflection α, hrα, ?_⟩
    rw [CFSG.LieType.Chevalley.rootReflection_smul_self hαr, hneg, neg_neg]
  have hlt := iform_sq_lt hαr hβr heq hneg
  rw [hαα, hββ] at hlt
  have hcases : iform α β = 1 ∨ iform α β = -1 := by
    have h1 : iform α β ≤ 1 := by nlinarith
    have h2 : -1 ≤ iform α β := by nlinarith
    omega
  have hcβ : corootPair β α = iform α β := by rw [corootPair_eq_iform hτ hβr, iform_comm]
  rcases hcases with h1 | h1
  · have e1 : rootReflection β • α = α - β := by
      rw [CFSG.LieType.Chevalley.rootReflection_smul hβr, hcβ, h1, one_smul]
    have e2 : rootReflection α • (α - β) = -β := by
      rw [CFSG.LieType.Chevalley.rootReflection_smul hαr, corootPair_eq_iform hτ hαr,
        iform_sub_right, hαα, h1]
      simp only [show (2 : ℤ) - 1 = 1 by norm_num, one_smul]
      abel
    have e3 : rootReflection β • (-β) = β := by
      rw [smul_neg, CFSG.LieType.Chevalley.rootReflection_smul_self hβr, neg_neg]
    refine ⟨rootReflection β * rootReflection α * rootReflection β,
      mul_mem (mul_mem hrβ hrα) hrβ, ?_⟩
    rw [mul_smul, mul_smul, e1, e2, e3]
  · have e1 : rootReflection β • α = α + β := by
      rw [CFSG.LieType.Chevalley.rootReflection_smul hβr, hcβ, h1, neg_smul, one_smul,
        sub_neg_eq_add]
    have e2 : rootReflection α • (α + β) = β := by
      rw [CFSG.LieType.Chevalley.rootReflection_smul hαr, corootPair_eq_iform hτ hαr,
        iform_add_right, hαα, h1]
      simp only [show (2 : ℤ) + -1 = 1 by norm_num, one_smul]
      abel
    refine ⟨rootReflection α * rootReflection β, mul_mem hrα hrβ, ?_⟩
    rw [mul_smul, e1, e2]

theorem exists_weyl_smul_eq_of_mem_componentRoots (hτ : SimplyLacedTag τ) {M : Type*}
    [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}
    {α β : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i) (hβ : β ∈ componentRoots χ i) :
    ∃ w ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots χ i, s = rootReflection γ},
      w • α = β := by
  obtain ⟨hαk, hαi⟩ := hα
  obtain ⟨hβk, hβi⟩ := hβ
  have hrel : (kernelRootSetoid χ).r ⟨α, hαk⟩ ⟨β, hβk⟩ := Quotient.exact (hαi.trans hβi.symm)
  suffices key : ∀ x y : kernelRoots χ, (kernelRootSetoid χ).r x y →
      (⟦x⟧ : KernelComponent χ) = i → ∃ w ∈ Subgroup.closure
        {s : WeylGroup τ | ∃ γ ∈ componentRoots χ i, s = rootReflection γ},
        w • (x : Fin τ.rank → ℤ) = y from key _ _ hrel hαi
  intro x y hxy
  induction hxy with
  | rel x y hr =>
    intro hx
    have hr' : iform (x : Fin τ.rank → ℤ) y ≠ 0 := by rwa [← dotProduct_mulVec_eq_iform]
    have hy : (⟦y⟧ : KernelComponent χ) = i := (mk_eq_of_iform_ne_zero hr').symm.trans hx
    exact exists_weyl_smul_eq_of_iform_ne_zero hτ ⟨x.2, hx⟩ ⟨y.2, hy⟩ x.2.1 y.2.1 hr'
  | refl x => exact fun _ => ⟨1, one_mem _, one_smul _ _⟩
  | symm x y hxy ih =>
    intro hy
    have hx : (⟦x⟧ : KernelComponent χ) = i := (Quotient.sound hxy).trans hy
    obtain ⟨w, hw, hw'⟩ := ih hx
    exact ⟨w⁻¹, inv_mem hw, by rw [← hw', inv_smul_smul]⟩
  | trans x y z hxy hyz ih1 ih2 =>
    intro hx
    obtain ⟨w₁, hw₁, e₁⟩ := ih1 hx
    have hy : (⟦y⟧ : KernelComponent χ) = i := (Quotient.sound hxy).symm.trans hx
    obtain ⟨w₂, hw₂, e₂⟩ := ih2 hy
    exact ⟨w₂ * w₁, mul_mem hw₂ hw₁, by rw [mul_smul, e₁, e₂]⟩

end WeylConj

section SimplyLaced

open CFSG.HardMathSupport.Timmesfeld.LangTorus (pairChar kernelRoots_pairChar
  componentRoots_pairChar)

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem exists_untwist_root (hτ : SimplyLacedTag τ) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) {s : ℕ} (hs : 0 < s) {θ : Fin τ.rank → ℤ}
    (hθ : θ ∈ componentRoots (rootCharHom a) i) {w : WeylGroup τ}
    (hw : w ∈ Subgroup.closure
      {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i, s = rootReflection γ})
    (hwθ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ = w • θ) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent (rootCharHom a), ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots (rootCharHom a) j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots (rootCharHom a) j)) ∧
      ∀ g ∈ rootSpan τ L {θ, -θ}, iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by rw [← hσ]; rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨g, hgS, hgM, hgmaps⟩ := exists_lift_mem_closure_reflections (L := L) i hw
  have hhM : g⁻¹ ∈ monomialSubgroup τ L := inv_mem hgM
  have hπ : weylQuotientHom τ L ⟨g⁻¹, hhM⟩ = w⁻¹ := weylQuotientHom_eq hgmaps.inv
  let φ : ModGL τ L →* ModGL τ L := (MulAut.conj g⁻¹).toMonoidHom.comp (iterHom S.D.step s)
  have hφ : ∀ x, φ x = g⁻¹ * iterHom S.D.step s x * g⁻¹⁻¹ := fun x => rfl
  have hlen : ∀ α, IsRoot τ α → iform α α = iform θ θ := fun α hα => by
    rw [iform_self_eq_two_of_simplyLaced' hτ hα, iform_self_eq_two_of_simplyLaced' hτ hθr]
  have hker : kernelRoots (pairChar θ) = {θ, -θ} := kernelRoots_pairChar hθr hlen
  have hθk : θ ∈ kernelRoots (pairChar θ) := by rw [hker]; exact Or.inl rfl
  have hcomp : componentRoots (pairChar θ)
      (⟦⟨θ, hθk⟩⟧ : KernelComponent (pairChar θ)) = {θ, -θ} :=
    componentRoots_pairChar hθr hlen hθk
  have hφpin : ∀ γ ∈ componentRoots (pairChar θ) (⟦⟨θ, hθk⟩⟧ : KernelComponent (pairChar θ)),
      ∃ m' : L, m' ≠ 0 ∧ ∀ c : L,
        φ (pinnedX τ L γ c) = pinnedX τ L ((1 : WeylGroup τ) • γ) (m' * σ c) := by
    intro γ hγ
    rw [hcomp] at hγ
    have hγr : IsRoot τ γ := by
      rcases hγ with rfl | hγ
      · exact hθr
      · rw [Set.mem_singleton_iff.1 hγ]; exact IsRoot.neg hθr
    have hργ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] γ = w • γ := by
      rcases hγ with rfl | hγ
      · exact hwθ
      · rw [Set.mem_singleton_iff.1 hγ, rho_iterate_neg, hwθ, smul_neg]
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s hγr
    obtain ⟨ν, hν⟩ := monomial_conj_pinnedX hhM (IsRoot.smul hγr w)
    refine ⟨(ν : L) * μ, mul_ne_zero ν.ne_zero hμ0, fun c => ?_⟩
    rw [hφ, iterHom_eq_iterate, hμ, hργ, hν, hπ, inv_smul_smul, one_smul, hσc, mul_assoc]
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin _ σ φ (one_mem _) hφpin
  rw [hcomp] at hy₁ hpin
  have hpairle : rootSpan τ L {θ, -θ} ≤ rootSpan τ L (kernelRoots (rootCharHom a)) := by
    refine rootSpan_mono fun γ hγ => ?_
    rcases hγ with rfl | hγ
    · exact hθ.1
    · rw [Set.mem_singleton_iff.1 hγ]
      exact ((isRootComponent_componentRoots i).neg_mem θ hθ).1
  have hhK : g⁻¹ ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    Subgroup.mem_sup_right (rootSpan_mono (fun γ hγ => hγ.1) (inv_mem hgS))
  have hy : y₁ * g⁻¹ ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots (rootCharHom a)) :=
    mul_mem ((sup_le_sup_left hpairle _) hy₁) hhK
  obtain ⟨z, hφz, hnorm⟩ := outer_exists_lang S hT hs hy
  refine ⟨σ, z, hσc, hnorm, fun g' hg' => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  have h1 := hpin g' hg'
  rw [hφ] at h1
  calc z * (y₁ * g⁻¹) * iterHom S.D.step s g' * (z * (y₁ * g⁻¹))⁻¹ =
      z * (y₁ * (g⁻¹ * iterHom S.D.step s g' * g⁻¹⁻¹) * y₁⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g' * z⁻¹ := by rw [h1]

theorem noL33_rationalComponent_simplyLaced (hτ : SimplyLacedTag τ) (hL3 : ringChar L = 3)
    (hq9 : 9 ≤ S.D.q) (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  classical
  obtain ⟨hs0, hs, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  haveI : NeZero s := ⟨hs0.ne'⟩
  obtain ⟨θ, hθ⟩ := exists_mem_componentRoots i
  have hθr : IsRoot τ θ := isRoot_of_mem_componentRoots hθ
  have hneg : -θ ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem θ hθ
  have hρθ : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] θ ∈ componentRoots (rootCharHom a) i := by
    rw [← hs]
    exact ⟨θ, hθ, rfl⟩
  obtain ⟨w, hw, hwθ⟩ := exists_weyl_smul_eq_of_mem_componentRoots hτ hθ hρθ
  obtain ⟨σ, z, hσ, hnorm, hz⟩ := exists_untwist_root S hτ hT i hs0 hθ hw hwθ.symm
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP L r := hchar
  have hσ' : ∀ c, σ c = c ^ (r ^ (e * s)) := fun c => by rw [hσ, hq, ← pow_mul]
  have hQ9 : 9 ≤ r ^ (e * s) := by
    calc 9 ≤ S.D.q := hq9
      _ = r ^ e := hq
      _ ≤ r ^ (e * s) := le_pow_orbit hr.pos hs0
  obtain ⟨hfinK, hKcard⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.finite_card_fixSubfield (L := L) (r := r)
      (n := e * s) (Nat.mul_pos he hs0) σ hσ'
  let ι : SL(2, ↥(fixSubfield σ)) →* SL(2, L) :=
    Matrix.SpecialLinearGroup.map (fixSubfield σ).subtype
  let θ₁ : SL(2, ↥(fixSubfield σ)) →* ModGL τ L :=
    (MulAut.conj z).toMonoidHom.comp ((rootSL2 τ L θ).comp ι)
  have hθ₁ : ∀ A, θ₁ A = z * rootSL2 τ L θ (ι A) * z⁻¹ := fun A => rfl
  have hpair : rootSpan τ L {θ, -θ} = rootSubgroup τ L θ ⊔ rootSubgroup τ L (-θ) := by
    simp only [rootSpan, iSup_insert, iSup_singleton]
  have hρmem : ∀ B, rootSL2 τ L θ B ∈ rootSpan τ L {θ, -θ} := by
    intro B
    have h1 : rootSL2 τ L θ B ∈ (rootSL2 τ L θ).range := ⟨B, rfl⟩
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hθr, ← hpair] at h1
    exact h1
  have hpairS : rootSpan τ L {θ, -θ} ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    refine rootSpan_mono fun γ hγ => ?_
    rcases hγ with rfl | hγ
    · exact hθ
    · rw [Set.mem_singleton_iff.1 hγ]
      exact hneg
  have hθS : ∀ A, θ₁ A ∈ rootSpan τ L (componentRoots (rootCharHom a) i) := fun A => by
    rw [hθ₁]
    exact (hnorm i _).1 (hpairS (hρmem (ι A)))
  have hθfix : ∀ A, iterHom S.D.step s (θ₁ A) = θ₁ A := by
    intro A
    rw [hθ₁, hz _ (hρmem (ι A)), frobGL_rootSL2 σ hθr]
    congr 3
    ext j k
    exact (A j k).2
  have hθinj : Function.Injective θ₁ := by
    intro A B hAB
    rw [hθ₁, hθ₁] at hAB
    have h1 : rootSL2 τ L θ (ι A) = rootSL2 τ L θ (ι B) := by
      have := congrArg (fun x => z⁻¹ * x * z) hAB
      simpa [mul_assoc] using this
    have h2 := CFSG.RankThree.Chevalley.rootSL2_injective_of_field θ h1
    ext j k
    exact congrArg (fun M : SL(2, L) => (M : Matrix (Fin 2) (Fin 2) L) j k) h2
  set P := outerOrbitFamily S hT i hs hmin with hP
  have hP0 : P.S 0 = rootSpan τ L (componentRoots (rootCharHom a) i) := by
    rw [hP, outerOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
  let θ₀ : SL(2, ↥(fixSubfield σ)) →* P.S 0 :=
    θ₁.codRestrict (P.S 0) fun A => by rw [hP0]; exact hθS A
  have hfix0 : ∀ A, iterHom S.D.step s ((θ₀ A : P.S 0) : ModGL τ L) = θ₀ A := fun A => hθfix A
  have hperf : Group.IsPerfect SL(2, ↥(fixSubfield σ)) :=
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_specialLinearGroup_of_le le_rfl
      (Or.inr (by rw [hKcard]; omega))).1
  have hfR : ∀ A, P.norm (θ₀ A) ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    outer_norm_mem_rationalComponent S hT i hs hmin hperf θ₀ hfix0
  let g : SL(2, ↥(fixSubfield σ)) →* ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) :=
    (P.norm.comp θ₀).codRestrict _ hfR
  have hgker : g.ker ≤ Subgroup.center SL(2, ↥(fixSubfield σ)) := by
    intro A hA
    have h1 : P.norm (θ₀ A) = 1 := congrArg Subtype.val hA
    have h2 := P.mem_Z_of_norm_eq_one h1
    rw [Subgroup.mem_center_iff]
    intro B
    have h3 := P.mem_Z.1 h2 (θ₁ B) (P.S_le_A 0 (by rw [hP0]; exact hθS B))
    exact hθinj (by rw [map_mul, map_mul]; exact h3)
  have hring : ringChar (fixSubfield σ) = 3 :=
    (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_subfield' _).trans hL3
  intro hL
  exact false_of_sl2_hom hring (by rw [hKcard]; exact hQ9) g hgker hL

end SimplyLaced

section OuterDEHolds

theorem noL33OuterDE_holds :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀),
      ringChar L = 3 → 9 ≤ S.D.q → ∀ (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus →
      ∀ p : ℕ, p.Prime → p ≠ 2 → (∀ i, a i ^ p = 1) → rootDiagUnit τ a ≠ 1 →
      ∀ i : KernelComponent (rootCharHom a),
        ¬ twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)]) →
        ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
        CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
          ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
            Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  intro τ L _ _ p₀ S hL3 hq9 a hT p hp hp2 hap h1 i hout hnA hqs
  have hℓp : ringChar L ≠ p :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  cases τ with
  | G2 =>
    exact (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.false_of_g2Class_nonAP hp S hpL hTp
      h1 i hnA).elim
  | F4 =>
    have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
    rcases CFSG.HardMathSupport.Solomon.Coordinator.LieComp.f4_nonA_casesP hp hp2' S hpL hTp h1 i
      hnA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
    · exact (hout (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 2 8
        hr hn (by omega) (by omega) (by omega) (by omega))).elim
    · exact (hout (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 3 18
        hr hn (by omega) (by omega) (by omega) (by omega))).elim
  | D4 => exact noL33_rationalComponent_simplyLaced S (Or.inl rfl) hL3 hq9 hT i
  | E6 => exact noL33_rationalComponent_simplyLaced S (Or.inr (Or.inl rfl)) hL3 hq9 hT i
  | E7 => exact noL33_rationalComponent_simplyLaced S (Or.inr (Or.inr (Or.inl rfl))) hL3 hq9 hT i
  | E8 => exact noL33_rationalComponent_simplyLaced S (Or.inr (Or.inr (Or.inr rfl))) hL3 hq9 hT i

end OuterDEHolds

section Dispatch

variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
  {a : Fin τ.rank → Lˣ}

theorem noL33_rationalComponent (hL3 : ringChar L = 3) (hq9 : 9 ≤ S.D.q)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ i, a i ^ p = 1)
    (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hqs : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    ¬ IsLpType 3 3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
      Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) := by
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact noL33_rationalComponent_inner S hL3 hq9 hT i hinner
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by
      by_contra hlt
      have hr1 : compRank (componentRoots (rootCharHom a) i) = 1 := by omega
      exact hinner (CFSG.HardMathSupport.Solomon.Coordinator.LieComp.twistInner_of_shape S hT i 1 2
        hr1 (by rw [hA.2, hr1]) (by omega) (by omega) (by omega) (by omega))
    exact noL33_rationalComponent_typeA S hL3 hq9 hp hT hap h1 i h2 hA.2
  · exact noL33OuterDE_holds τ L p₀ S hL3 hq9 a hT p hp hp2 hap h1 i hinner hA hqs

end Dispatch

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d

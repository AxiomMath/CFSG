module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6ParamA
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphTwistedNorm
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.ComponentClassification.UnbalancedCatalog.UnitaryFieldTransfer
  (fixedField_charP fixedField_finite)
open CFSG.LieType.Steinberg.TwistedE6 (fixedGroup)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.Quasithin (perfectCore perfectCore_le)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Ree (ReeTag)

section OddLift

theorem exists_lift_of_central_odd {M Q : Type} [Group M] [Finite M] [Group Q] (π : M →* Q)
    (hπ : Function.Surjective π)
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → Odd (Nat.card π'.ker) → ∃ s : M →* E', ∀ g, π' (s g) = g)
    {E : Type} [Group E] [Finite E] [Group.IsPerfect E] (ρ : E →* Q) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center E) (hodd : Odd (Nat.card ρ.ker)) :
    ∃ Φ : M →* E, Function.Surjective Φ ∧ ∀ g, ρ (Φ g) = π g := by
  set P : Subgroup (E × M) :=
    MonoidHom.eqLocus (ρ.comp (MonoidHom.fst _ _)) (π.comp (MonoidHom.snd _ _)) with hPdef
  have hmemP : ∀ p : E × M, p ∈ P ↔ ρ p.1 = π p.2 := fun p => Iff.rfl
  set p₂ : P →* M := (MonoidHom.snd _ _).comp P.subtype
  have hp₂ : Function.Surjective p₂ := by
    intro g
    obtain ⟨y, hy⟩ := hρ (π g)
    exact ⟨⟨(y, g), (hmemP _).2 hy⟩, rfl⟩
  have hker1 : ∀ x : P, x ∈ p₂.ker → (x : E × M).1 ∈ ρ.ker := by
    intro x hx
    have hx2 : (x : E × M).2 = 1 := hx
    rw [MonoidHom.mem_ker, (hmemP _).1 x.2, hx2, map_one]
  have hp₂ker : p₂.ker ≤ center P := by
    intro x hx
    rw [mem_center_iff]
    intro z
    have hx2 : (x : E × M).2 = 1 := hx
    have hc := mem_center_iff.1 (hker (hker1 x hx)) z.1.1
    apply Subtype.ext
    apply Prod.ext
    · exact hc
    · change z.1.2 * x.1.2 = x.1.2 * z.1.2
      rw [hx2, mul_one, one_mul]
  set ψ : p₂.ker →* ρ.ker :=
    { toFun := fun x => ⟨((x : P) : E × M).1, hker1 x x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : ((x : P) : E × M).1 = ((y : P) : E × M).1 := congrArg Subtype.val hxy
    have hx2 : ((x : P) : E × M).2 = 1 := x.2
    have hy2 : ((y : P) : E × M).2 = 1 := y.2
    exact Subtype.ext (Subtype.ext (Prod.ext h1 (hx2.trans hy2.symm)))
  have hoddP : Odd (Nat.card p₂.ker) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective ψ hψ)
  obtain ⟨σ, hσ⟩ := hsplit P p₂ hp₂ hp₂ker hoddP
  set Φ : M →* E := (MonoidHom.fst _ _).comp (P.subtype.comp σ)
  have hΦ : ∀ g, ρ (Φ g) = π g := by
    intro g
    have h1 := (hmemP _).1 (σ g).2
    have h2 : (σ g).1.2 = g := hσ g
    calc ρ (Φ g) = ρ (σ g).1.1 := rfl
      _ = π (σ g).1.2 := h1
      _ = π g := by rw [h2]
  refine ⟨Φ, ?_, hΦ⟩
  have htop : (⊤ : Subgroup E) ≤ Φ.range := by
    refine perfect_le_of_forall_exists_commute (by
      rw [← _root_.commutator_def]
      exact Group.IsPerfect.commutator_eq_top) le_top fun a _ => ?_
    obtain ⟨g, hg⟩ := hπ (ρ a)
    refine ⟨Φ g, ⟨g, rfl⟩, (Φ g)⁻¹ * a, by group, fun b _ => ?_⟩
    have hz : (Φ g)⁻¹ * a ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hΦ, hg, inv_mul_cancel]
    exact (mem_center_iff.1 (hker hz) b).symm
  intro a
  obtain ⟨g, hg⟩ := htop (mem_top a)
  exact ⟨g, hg⟩

end OddLift

section OddLiftT

variable {M : Type} [Group M] [Finite M] {G : Type} [Group G] [Finite G]

theorem exists_mulAut_comp_eq_conj_of_oddClosed [Group.IsPerfect M]
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → Odd (Nat.card π'.ker) → ∃ s : M →* E', ∀ g, π' (s g) = g)
    (Φ : M →* G) (hker : Φ.ker ≤ center M) (hodd : Odd (Nat.card Φ.ker)) {t : G}
    (ht : t ∈ normalizer (Φ.range : Set G)) :
    ∃ β : MulAut M, ∀ g, Φ (β g) = t * Φ g * t⁻¹ := by
  set c : MulAut Φ.range := Φ.range.normalizerMonoidHom ⟨t, ht⟩ with hc
  have hcapp : ∀ y : Φ.range, ((c y : Φ.range) : G) = t * y * t⁻¹ := fun y =>
    coe_normalizerMonoidHom_mk_apply Φ.range ht y
  set π : M →* Φ.range := c.toMonoidHom.comp Φ.rangeRestrict
  have hπ : Function.Surjective π := c.surjective.comp Φ.rangeRestrict_surjective
  have hρker : Φ.rangeRestrict.ker ≤ center M := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hρodd : Odd (Nat.card Φ.rangeRestrict.ker) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hodd
  obtain ⟨θ, hθs, hθ⟩ := exists_lift_of_central_odd π hπ hsplit Φ.rangeRestrict
    Φ.rangeRestrict_surjective hρker hρodd
  have hθb : Function.Bijective θ := ⟨Finite.injective_iff_surjective.mpr hθs, hθs⟩
  refine ⟨MulEquiv.ofBijective θ hθb, fun g => ?_⟩
  have h1 := congrArg Subtype.val (hθ g)
  change Φ (θ g) = ((c (Φ.rangeRestrict g) : Φ.range) : G) at h1
  rw [hcapp] at h1
  exact h1

end OddLiftT

section Cover


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_twoSu6Cover {t : G} (hw : F4Work L K t 1) (e : L ≃* adjointGroup .F4 K)
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ 1) ^ 2 ∧
      ∃ Φ : StatedSU 6 (2 ^ 1) F →* G, Φ.range = centralizerPerfectCore (subgroupToG e X₀) ∧
        Φ.ker ≤ center (StatedSU 6 (2 ^ 1) F) := by
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  obtain ⟨S, _, hS, ρ, hρ, hker, hodd⟩ :=
    exists_surjective_centralizerPerfectCore_nonsplit_F4_two_graph hw e hXJ hcyc hX₀
      (κ := .unitary6) (by decide) hk
  obtain ⟨F, _, _, hF, ⟨ε⟩⟩ : ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = (2 ^ 1) ^ 2 ∧ Nonempty (S ≃* StatedProj (StatedSU 6 (2 ^ 1) F)) := by
    rcases hS with ⟨-, -, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * 1) (by
    rw [hF, ← pow_mul, mul_comm])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := StatedSU 6 (2 ^ 1) F
  set π : M →* StatedProj M := QuotientGroup.mk' ((StatedScalars (Fin 6) F).subgroupOf M)
  set ρ' : E →* StatedProj M := ε.toMonoidHom.comp ρ
  have hρ' : Function.Surjective ρ' := ε.surjective.comp hρ
  have hkerρ : ρ'.ker = ρ.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      ε.map_eq_one_iff]
  have hker' : ρ'.ker ≤ center E := hkerρ ▸ hker
  have hodd' : Odd (Nat.card ρ'.ker) := hkerρ ▸ hodd
  have : Group.IsPerfect E := isPerfect_iff.mpr (commutator_centralizerPerfectCore _)
  obtain ⟨Φ₀, hΦ₀s, hΦ₀⟩ := exists_lift_of_central_odd π (QuotientGroup.mk'_surjective _)
    (fun E' _ _ π' hπ' hcen' hodd'' =>
      CFSG.SeitzReduction.UnitaryPilot.exists_section_statedSU_of_coprime hF (m := 6)
        (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num)) hπ' hcen'
        (fun _ => Nat.coprime_two_left.2 hodd'')) ρ' hρ' hker' hodd'
  refine ⟨F, inferInstance, inferInstance, hF, E.subtype.comp Φ₀, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 hΦ₀s, ← MonoidHom.range_eq_map,
      range_subtype]
  · intro g hg
    have hg₀ : Φ₀ g = 1 := E.subtype_injective (by rw [map_one]; exact hg)
    have h1 := hΦ₀ g
    rw [hg₀, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact statedScalars_subgroupOf_le_center M h1

theorem exists_twoGraphLift_of_oddClosed {t : G} (hw : F4Work L K t 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {κ : Sp6Kind} (hκ : κ.IsGraphKind) (hk : TwoKindAt e t X₀ κ)
    {M : Type} [Group M] [Finite M] [Group.IsPerfect M]
    (hsplit : ∀ (E' : Type) [Group E'] [Finite E'] (π' : E' →* M), Function.Surjective π' →
      π'.ker ≤ center E' → Odd (Nat.card π'.ker) → ∃ s : M →* E', ∀ g, π' (s g) = g)
    (Φ : M →* G) (hE : Φ.range = centralizerPerfectCore (subgroupToG e X₀))
    (hker : Φ.ker ≤ center M) (hodd : Odd (Nat.card Φ.ker)) :
    ∃ β : MulAut M, (∀ g, Φ (β g) = t * Φ g * t⁻¹) ∧ β * β = 1 ∧
      centerQuotientAut β * centerQuotientAut β = 1 ∧
      centerQuotientAut β ∉ (MulAut.conj : M ⧸ center M →* MulAut (M ⧸ center M)).range ∧
      LieModel (fixedSubgroup (centerQuotientAut β)) .PSp 3 2 1 := by
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htX : t ∈ centralizer (subgroupToG e X₀ : Set G) := hk.1
  have htN : t ∈ normalizer (Φ.range : Set G) := by
    rw [hE]
    exact normalizer_le_normalizer_centralizerPerfectCore _ (centralizer_le_normalizer _ htX)
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_conj_of_oddClosed hsplit Φ hker hodd htN
  have hββ := mulAut_mul_self_of_comp_eq_conj_of_perfect Φ hker htt hβ
  set E := centralizerPerfectCore (subgroupToG e X₀) with hEdef
  obtain ⟨Kb, _, τ, qh, hqs, hqker, hτo, hτfix, -, hqt⟩ :=
    exists_twoNeighbourData hw e hXJ hcyc hX₀ hκ hk
  have hmemE : ∀ g, Φ g ∈ E := fun g => hE ▸ ⟨g, rfl⟩
  set Φ' : M →* E := Φ.codRestrict _ hmemE
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hE] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hΦ'ker : Φ'.ker ≤ center M := fun g hg =>
    hker (by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact congrArg Subtype.val hg)
  set χ : M →* Kb := qh.comp Φ'
  have hχs : Function.Surjective χ := hqs.comp hΦ's
  have hχker : χ.ker ≤ center M := fun g hg =>
    CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center Φ' hΦ'ker (hqker hg)
  have hχβ : ∀ g, χ (β g) = τ (χ g) := by
    intro g
    have hy : t * ((Φ' g : E) : G) * t⁻¹ ∈ E := by
      change t * Φ g * t⁻¹ ∈ E
      rw [← hβ]
      exact hmemE _
    have e1 : Φ' (β g) = ⟨t * ((Φ' g : E) : G) * t⁻¹, hy⟩ := Subtype.ext (hβ g)
    change qh (Φ' (β g)) = τ (qh (Φ' g))
    rw [e1, hqt]
  refine ⟨β, hβ, hββ, by rw [← centerQuotientAut_mul, hββ, centerQuotientAut_one],
    fun hin => hτo (mem_range_conj_of_centerQuotientAut χ hχs hχβ hin), ?_⟩
  obtain ⟨ε⟩ := nonempty_fixedSubgroup_centerQuotientAut_equiv χ hχs hχker hχβ
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv ε.symm hτfix

end Cover

section Setting


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem exists_twoTwParamX_normalized {t : G} {f : ℕ} (hw : F4Work L K t f) (hf1 : f = 1)
    (e : L ≃* adjointGroup .F4 K) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) (hk : TwoKindAt e t X₀ .unitary6) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (h : UnitaryFieldData 2 f F)
      (ε : h.fixedField ≃+* K)
      (ΦX : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes →* G),
      ΦX.range = centralizerPerfectCore (subgroupToG e X₀) ∧
      ΦX.ker ≤ center (twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes) ∧
      (∀ x y : twLevi F h.barEquiv.toRingHom AmalgamNeighbour.X.nodes,
        (y : fixedGroup F h.barEquiv.toRingHom) = sigmaHat h.barEquiv.toRingHom x →
          t * ΦX x * t⁻¹ = ΦX y) ∧
      IsLeviNormalizedU h ε e ΦX := by
  have hw1 : F4Work L K t 1 := hf1 ▸ hw
  obtain ⟨F, _, _, hF1, Φ₀, hE₀, hker₀⟩ := exists_twoSu6Cover hw1 e hXJ hcyc hX₀ hk
  have hF : Nat.card F = (2 ^ f) ^ 2 := by rw [hF1, hf1]
  have : CharP F 2 := charP_two_of_natCard_eq_two_pow (f := 2 * 1) (by
    rw [hF1, ← pow_mul, mul_comm])
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : UnitaryFieldData 2 f F := unitaryFieldData_of_card (by omega) hF
  have eS : StatedSU 6 (2 ^ 1) F =
      gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    have e1 : (2 : ℕ) ^ 1 = 2 ^ f := by rw [hf1]
    rw [Units.val_one, e1]
    exact unitarySU_eq_gramSU h 6
  set eM := MulEquiv.subgroupCongr eS
  set Φ₁ := Φ₀.comp eM.symm.toMonoidHom with hΦ₁
  have hE₁ : Φ₁.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₁, MonoidHom.range_comp, MonoidHom.range_eq_top.2 eM.symm.surjective,
      ← MonoidHom.range_eq_map, hE₀]
  have hker₁ := ker_comp_mulEquiv_le_center Φ₀ hker₀ eM.symm
  have := finite_gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
  have := CFSG.RankThree.Classical.isPerfect_gramSU_one h (n := 6) (by norm_num) (by omega)
  have hsplit : ∀ (E' : Type) [Group E'] [Finite E']
      (π' : E' →* gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)),
      Function.Surjective π' → π'.ker ≤ center E' → Odd (Nat.card π'.ker) →
        ∃ s : gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) →* E',
          ∀ g, π' (s g) = g := by
    intro E' _ _ π' hπ' hcen hodd
    have hkerE : (eM.symm.toMonoidHom.comp π').ker = π'.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ eM.symm.injective]
    obtain ⟨s, hs⟩ :=
      CFSG.SeitzReduction.UnitaryPilot.exists_section_statedSU_of_coprime hF1
        (m := 6) (by norm_num) (fun h => absurd (congrArg Prod.fst h) (by norm_num))
        (π := eM.symm.toMonoidHom.comp π') (eM.symm.surjective.comp hπ') (hkerE ▸ hcen)
        (fun _ => Nat.coprime_two_left.2 (hkerE ▸ hodd))
    refine ⟨s.comp eM.symm.toMonoidHom, fun g => eM.symm.injective ?_⟩
    exact hs (eM.symm g)
  have hoddZ : Odd (Nat.card (center (StatedSU 6 (2 ^ 1) F))) := by
    rw [← Nat.card_congr (Subgroup.centerCongr
      (CFSG.LieType.Universal.Unitary.equivStatedSU hF1 6)).toEquiv]
    exact CFSG.SeitzReduction.SymplecticPilot.odd_card_center_SU hF1 le_rfl (by norm_num)
      (by decide)
  have hodd₁ : Odd (Nat.card Φ₁.ker) := by
    have h1 : Nat.card (center (gramSU h ((1 : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F))) =
        Nat.card (center (StatedSU 6 (2 ^ 1) F)) :=
      Nat.card_congr (Subgroup.centerCongr eM.symm).toEquiv
    exact Odd.of_dvd_nat (h1 ▸ hoddZ) (Subgroup.card_dvd_of_le hker₁)
  obtain ⟨β, hβ, -, hβ2, hβo, hβfix⟩ := exists_twoGraphLift_of_oddClosed hw1 e hXJ hcyc hX₀
    (κ := .unitary6) (by decide) hk hsplit Φ₁ hE₁ hker₁ hodd₁
  obtain ⟨Ψ, hΨ⟩ := exists_unitary6_normal_form h β hβ2 hβo hβfix
  set Φ₂ := Φ₁.comp Ψ.toMonoidHom with hΦ₂
  have hE₂ : Φ₂.range = centralizerPerfectCore (subgroupToG e X₀) := by
    rw [hΦ₂, MonoidHom.range_comp, MonoidHom.range_eq_top.2 Ψ.surjective,
      ← MonoidHom.range_eq_map, hE₁]
  have hker₂ := ker_comp_mulEquiv_le_center Φ₁ hker₁ Ψ
  have hc : ∀ g, t * Φ₂ g * t⁻¹ = Φ₂ (barSU6 h g) := by
    intro g
    change t * Φ₁ (Ψ g) * t⁻¹ = Φ₁ (Ψ (primeFormFieldSU h _ h.barEquiv g))
    rw [← hΨ, hβ]
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hw1.card_eq, pow_one]
  have hD : perfectCore (Φ₂.range ⊓ centralizer ({t} : Set G)) = neighbourLeviG e .X := by
    rw [hE₂, perfectCore_centralizerPerfectCore_inf_centralizer_nonsplit_F4 hw1 e hXJ hcyc hX₀']
    rfl
  have := fixedField_charP h
  have := fixedField_finite h
  obtain ⟨ε⟩ := graphTorus_nonempty_ringEquiv h.card_fixedField hw.card_eq
  obtain ⟨Φ', hr', hk', hc', hn'⟩ := exists_normalized_coverU h e ε Φ₂ hker₂ hc hD
  refine ⟨F, inferInstance, inferInstance, inferInstance, h, ε,
    Φ'.comp (twParamEquiv h).symm.toMonoidHom, ?_, ?_, conj_comp_twParamEquiv_symm h hc', ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (twParamEquiv h).symm.surjective,
      ← MonoidHom.range_eq_map, hr', hE₂]
  · exact ker_comp_mulEquiv_le_center Φ' hk' (twParamEquiv h).symm
  · intro s
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hn']

end Setting

end CFSG.SeitzReduction.F4Pilot

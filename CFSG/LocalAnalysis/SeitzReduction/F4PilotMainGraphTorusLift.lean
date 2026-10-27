module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesLift

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.EvenSmallLie
  CFSG.Assembly.LowTwoRank
open Matrix
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

local instance f4PilotMainGraphTorusLiftNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

section SLAut

variable {n : ℕ} {F : Type} [Field F]

theorem graphTorus_mulAut_eq_of_inv_mul_mem_center {P : Type*} [Group P] [Group.IsPerfect P]
    {γ₁ γ₂ : MulAut P} (h : ∀ g, (γ₁ g)⁻¹ * γ₂ g ∈ center P) : γ₁ = γ₂ := by
  let c : P →* center P :=
    { toFun := fun g => ⟨(γ₁ g)⁻¹ * γ₂ g, h g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g g' => Subtype.ext (by
        simp only [map_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
        have hc := mem_center_iff.mp (h g) (γ₁ g')⁻¹
        calc (γ₁ g')⁻¹ * (γ₁ g)⁻¹ * (γ₂ g * γ₂ g') =
            ((γ₁ g')⁻¹ * ((γ₁ g)⁻¹ * γ₂ g)) * γ₂ g' := by group
          _ = (((γ₁ g)⁻¹ * γ₂ g) * (γ₁ g')⁻¹) * γ₂ g' := by rw [hc]
          _ = (γ₁ g)⁻¹ * γ₂ g * ((γ₁ g')⁻¹ * γ₂ g') := by group) }
  have hker : ∀ g, c g = 1 := by
    intro g
    have hg : g ∈ commutator P := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact mem_top g
    rw [_root_.commutator_def] at hg
    refine closure_induction (p := fun x _ => c x = 1) ?_ (map_one c)
      (fun x y _ _ hx hy => by rw [map_mul, hx, hy, one_mul])
      (fun x _ hx => by rw [map_inv, hx, inv_one]) hg
    rintro _ ⟨x, -, y, -, rfl⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext ((mem_center_iff.mp (c y).2 (c x : P)))
  refine MulEquiv.ext fun g => ?_
  have h1 := congrArg Subtype.val (hker g)
  change (γ₁ g)⁻¹ * γ₂ g = 1 at h1
  exact (inv_mul_eq_one.mp h1)

theorem graphTorus_isPerfect_SL (hn : 3 ≤ n) : Group.IsPerfect (SpecialLinearGroup (Fin n) F) :=
  CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le hn

theorem graphTorus_descendAut_injective (hn : 3 ≤ n) :
    Function.Injective (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.descendAut n F) := by
  have := graphTorus_isPerfect_SL (F := F) hn
  intro γ₁ γ₂ h
  refine graphTorus_mulAut_eq_of_inv_mul_mem_center fun g => ?_
  have h1 := congrArg (fun α : MulAut (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL
    n F) => α (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj n F g)) h
  simp only [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.descendAut_proj] at h1
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  exact CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff.mp h1

theorem graphTorus_mulAut_eq_of_comp_eq (hn : 3 ≤ n) {G : Type*} [Group G]
    (Φ : SpecialLinearGroup (Fin n) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {γ₁ γ₂ : MulAut (SpecialLinearGroup (Fin n) F)} (h : ∀ g, Φ (γ₁ g) = Φ (γ₂ g)) : γ₁ = γ₂ := by
  have := graphTorus_isPerfect_SL (F := F) hn
  refine graphTorus_mulAut_eq_of_inv_mul_mem_center fun g => hker ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]

end SLAut

section TLift

variable {m : ℕ} {F : Type} [Field F] [Finite F] {G : Type} [Group G]

theorem exists_mulAut_comp_eq_conj (hm : 4 ≤ m) (Φ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F)) {t : G}
    (ht : t ∈ normalizer (Φ.range : Set G)) :
    ∃ β : MulAut (SpecialLinearGroup (Fin (m + 1)) F), ∀ g, Φ (β g) = t * Φ g * t⁻¹ := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) F) := graphTorus_isPerfect_SL (by omega)
  set c : MulAut Φ.range := Φ.range.normalizerMonoidHom ⟨t, ht⟩ with hc
  have hcapp : ∀ y : Φ.range, ((c y : Φ.range) : G) = t * y * t⁻¹ := fun y =>
    coe_normalizerMonoidHom_mk_apply Φ.range ht y
  set π : SpecialLinearGroup (Fin (m + 1)) F →* Φ.range := c.toMonoidHom.comp Φ.rangeRestrict
  have hπ : Function.Surjective π := c.surjective.comp Φ.rangeRestrict_surjective
  have hρker : Φ.rangeRestrict.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  obtain ⟨θ, hθs, hθ⟩ := exists_lift_of_central π hπ
    (fun E' _ _ π' hπ' hcen =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le hm hπ' hcen)
    Φ.rangeRestrict Φ.rangeRestrict_surjective hρker
  have hθb : Function.Bijective θ := ⟨Finite.injective_iff_surjective.mpr hθs, hθs⟩
  refine ⟨MulEquiv.ofBijective θ hθb, fun g => ?_⟩
  have h1 := congrArg Subtype.val (hθ g)
  change Φ (θ g) = ((c (Φ.rangeRestrict g) : Φ.range) : G) at h1
  rw [hcapp] at h1
  exact h1

omit [Finite F] in
theorem mulAut_mul_self_of_comp_eq_conj (hm : 4 ≤ m) (Φ : SpecialLinearGroup (Fin (m + 1)) F →* G)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F)) {t : G} (htt : t * t = 1)
    {β : MulAut (SpecialLinearGroup (Fin (m + 1)) F)} (hβ : ∀ g, Φ (β g) = t * Φ g * t⁻¹) :
    β * β = 1 := by
  refine graphTorus_mulAut_eq_of_comp_eq (by omega) Φ hker fun g => ?_
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [MulAut.mul_apply, hβ, hβ, MulAut.one_apply, ht']
  calc t * (t * Φ g * t) * t = (t * t) * Φ g * (t * t) := by group
    _ = Φ g := by rw [htt, one_mul, mul_one]

end TLift

section Fix

variable {P : Type*} [Group P] [Finite P] {G : Type*} [Group G] [Finite G]

theorem map_perfectCore_fixedSubgroup_eq (Φ : P →* G) (hker : Φ.ker ≤ center P) {t : G}
    {β : MulAut P} (hβ : ∀ g, Φ (β g) = t * Φ g * t⁻¹) :
    (perfectCore (fixedSubgroup β)).map Φ = perfectCore (Φ.range ⊓ centralizer ({t} : Set G)) := by
  set M : Subgroup P := (centralizer ({t} : Set G)).comap Φ with hM
  have hmemM : ∀ g, g ∈ M ↔ (β g)⁻¹ * g ∈ Φ.ker := by
    intro g
    rw [hM, mem_comap, mem_centralizer_singleton_iff, MonoidHom.mem_ker, map_mul, map_inv, hβ]
    constructor
    · intro h
      have h' : t * Φ g * t⁻¹ = Φ g := by
        calc t * Φ g * t⁻¹ = Φ g * t * t⁻¹ := by rw [h]
          _ = Φ g := by group
      rw [h', inv_mul_cancel]
    · intro h
      have h' : t * Φ g * t⁻¹ = Φ g := inv_mul_eq_one.mp h
      calc Φ g * t = t * Φ g * t⁻¹ * t := by rw [h']
        _ = t * Φ g := by group
  have hfixM : fixedSubgroup β ≤ M := by
    intro g hg
    rw [hmemM]
    have hg' : β g = g := hg
    rw [hg', inv_mul_cancel]
    exact one_mem _
  have hcomm : ⁅M, M⁆ ≤ fixedSubgroup β := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have za := hker ((hmemM a).1 ha)
    have zb := hker ((hmemM b).1 hb)
    change β ⁅a, b⁆ = ⁅a, b⁆
    have ea : β a = a * ((β a)⁻¹ * a)⁻¹ := by group
    have eb : β b = b * ((β b)⁻¹ * b)⁻¹ := by group
    rw [map_commutatorElement, ea, eb]
    set z := ((β a)⁻¹ * a)⁻¹
    set w := ((β b)⁻¹ * b)⁻¹
    have hz : z ∈ center P := inv_mem za
    have hw : w ∈ center P := inv_mem zb
    simp only [commutatorElement_def]
    have h1 := mem_center_iff.mp hz
    have h2 := mem_center_iff.mp hw
    calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
        a * (z * (b * w)) * z⁻¹ * a⁻¹ * (w⁻¹ * b⁻¹) := by group
      _ = a * ((b * w) * z) * z⁻¹ * a⁻¹ * (w⁻¹ * b⁻¹) := by rw [← h1 (b * w)]
      _ = a * b * (w * a⁻¹) * (w⁻¹ * b⁻¹) := by group
      _ = a * b * (a⁻¹ * w) * (w⁻¹ * b⁻¹) := by rw [← h2 a⁻¹]
      _ = a * b * a⁻¹ * b⁻¹ := by group
  have hcore : perfectCore M = perfectCore (fixedSubgroup β) := by
    refine le_antisymm ?_ (CFSG.Quasithin.perfectCore_mono hfixM)
    refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ (CFSG.Quasithin.perfectCore_perfect M)
    exact (CFSG.Quasithin.perfectCore_le_derivedSeriesOf M 1).trans hcomm
  have hmapM : M.map Φ = Φ.range ⊓ centralizer ({t} : Set G) := by
    rw [hM, map_comap_eq]
  rw [← hcore, CFSG.Quasithin.map_perfectCore, hmapM]

end Fix

section Data


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_neighbourCoreData_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {κ : Sp6Kind} (hκ : κ ≠ .swap) (hX : HR8Kind e t f .X κ)
    (hOut : ∀ (Kb : Type) [Group Kb] [Finite Kb], Group.IsPerfect Kb →
      Sp6KindType (Kb ⧸ center Kb) f κ → Group.IsSolvable
        (CFSG.ComponentClassification.OuterAutomorphisms.Outer Kb)) :
    ∃ (Kb : Type) (_ : Group Kb) (τ : MulAut Kb) (qh : neighbourCore e .X →* Kb),
      Function.Surjective qh ∧ qh.ker ≤ center (neighbourCore e .X) ∧
      τ ∉ (MulAut.conj : Kb →* MulAut Kb).range ∧
      LieModel (fixedSubgroup (centerQuotientAut τ)) .PSp 3 2 f ∧
      ∀ (y : neighbourCore e .X) (hy : t * (y : G) * t⁻¹ ∈ neighbourCore e .X),
        qh ⟨t * y * t⁻¹, hy⟩ = τ (qh y) := by
  have := finite_of_natCard_eq_two_pow hw.card_eq
  have := charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  set X : Subgroup G := neighbourTorusG e .X with hXdef
  set H : Subgroup G := centralizer (X : Set G) with hHdef
  set D : Subgroup G := neighbourLeviG e .X with hDdef
  obtain ⟨htX, Kb, hKb, -, hcase⟩ := hX
  obtain ⟨-, -, hlt, hsK, hsN, hov, hty⟩ := hcase.resolve_right fun h => hκ h.1
  set π := QuotientGroup.mk' (oddCore H) with hπ
  set Db : Subgroup (H ⧸ oddCore H) := (D.subgroupOf H).map π with hDbdef
  set t' : H := ⟨t, htX⟩ with ht'def
  set s : H ⧸ oddCore H := π t' with hsdef
  have ht't' : t' * t' = 1 := Subtype.ext htt
  have hss : s * s = 1 := by rw [hsdef, ← map_mul, ht't', map_one]
  have hsC : s ∉ centralizer (Kb : Set (H ⧸ oddCore H)) := by
    intro hc
    refine hov.1 ⟨1, MulEquiv.ext fun k => Subtype.ext ?_⟩
    rw [map_one, MulAut.one_apply, coe_normalizerMonoidHom_mk_apply Kb hsN,
      ← mem_centralizer_iff.1 hc k k.2, mul_inv_cancel_right]
  have hs1 : s ≠ 1 := fun h => hsK (h ▸ one_mem Kb)
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  have hsD : s ∈ centralizer (Db : Set (H ⧸ oddCore H)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨d, hd, rfl⟩
    rw [hsdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hDt (mem_subgroupOf.1 hd)))
  obtain ⟨-, hsyl, -⟩ := neighbour_standard_torusLineR hw.standard.standard htC hw.orderOf_eq
    hw.inf_eq hf hw.card_eq e (X := X) rfl htX (D := D) rfl
  have hKbP : Group.IsPerfect Kb := hKb.1.1
  have hOutK := hOut Kb hKbP hty
  have hcore := LinearPilot.perfectCore_top_eq_of_isComponent
    (pPrimeCore_two_quotient_oddCore_eq_bot H) hKb hlt.le hs2 hsD hsN hsC hsyl hOutK
  have hTodd : Odd (Nat.card ((torusLineR K).subgroupOf (adjointGroup .F4 K))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe torusLineR_le_adjointGroup).toEquiv]
    exact odd_card_torusLineR hw.one_le hw.card_eq
  have hC := mem_center_of_mem_oddCore_of_commute_sup hw.card_eq hw.standard.standard htC
    hw.orderOf_eq hw.inf_eq e (centralizer_torusLineR_eq hq) torusLineR_subgroupOf_le_centralizer
    torusLineR_subgroupOf_le_centralizer_self hTodd le_rfl (X := X) rfl htX (D := D) rfl
  have hB : HasBLift Kb := hasBLift_of_le_center ht't' (isPerfect_iff.mp hKbP) hsN
    (le_commutator_zpowers_of_isQuasisimple hKb.1 hsN hsC) hC
  obtain ⟨qh, hqs, hqker, hqapp⟩ :=
    LinearPilot.exists_surjective_centralizerPerfectCore_of_perfectCore_eq hcore hB
  refine ⟨Kb, inferInstance, Kb.normalizerMonoidHom ⟨s, hsN⟩, qh, hqs, hqker, hov.1, hov.2.2.2,
    fun y hy => ?_⟩
  apply Subtype.ext
  rw [coe_normalizerMonoidHom_mk_apply Kb hsN]
  have h1 := hqapp ⟨t * (y : G) * t⁻¹, hy⟩
  have h2 := hqapp y
  have hyH : (y : G) ∈ H := centralizerPerfectCore_le_centralizer X y.2
  refine h1.trans ?_
  have e1 : π ⟨t * (y : G) * t⁻¹, centralizerPerfectCore_le_centralizer X hy⟩ =
      π t' * π ⟨(y : G), hyH⟩ * (π t')⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  refine e1.trans ?_
  exact congrArg (fun z => π t' * z * (π t')⁻¹) h2.symm

end Data

section Transfer

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj descendAut descendAut_proj
  proj_surjective scalars_eq_center)

variable {n : ℕ} {F : Type} [Field F] {Kb : Type} [Group Kb]

theorem graphTorus_descendAut_conj (g : SpecialLinearGroup (Fin n) F) :
    descendAut n F (MulAut.conj g) = MulAut.conj (proj n F g) := by
  ext x
  obtain ⟨h, rfl⟩ := proj_surjective n F x
  rw [descendAut_proj, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem graphTorus_mem_range_conj_of_descendAut (hn : 3 ≤ n)
    (χ : SpecialLinearGroup (Fin n) F →* Kb) (hχ : Function.Surjective χ)
    {β : MulAut (SpecialLinearGroup (Fin n) F)} {τ : MulAut Kb} (hβτ : ∀ g, χ (β g) = τ (χ g))
    (h : descendAut n F β ∈ (MulAut.conj : projectiveSL n F →* MulAut (projectiveSL n F)).range) :
    τ ∈ (MulAut.conj : Kb →* MulAut Kb).range := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨g, rfl⟩ := proj_surjective n F x
  have hβ : β = MulAut.conj g := by
    apply graphTorus_descendAut_injective hn
    rw [graphTorus_descendAut_conj, ← hx]
  refine ⟨χ g, MulEquiv.ext fun k => ?_⟩
  obtain ⟨h', rfl⟩ := hχ k
  rw [← hβτ, hβ, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

@[expose] noncomputable def graphTorusCenterQuotientEquiv (hn : 3 ≤ n)
    (χ : SpecialLinearGroup (Fin n) F →* Kb) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ center (SpecialLinearGroup (Fin n) F)) :
    projectiveSL n F ≃* Kb ⧸ center Kb :=
  have : Group.IsPerfect (SpecialLinearGroup (Fin n) F) := graphTorus_isPerfect_SL hn
  (QuotientGroup.quotientMulEquivOfEq (show
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars n F =
        ((QuotientGroup.mk' (center Kb)).comp χ).ker by
    rw [scalars_eq_center]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      rw [mem_center_iff]
      intro k
      obtain ⟨h, rfl⟩ := hχ k
      rw [← map_mul, ← map_mul, mem_center_iff.mp hx h]
    · exact CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center χ hker)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective (center Kb)).comp hχ))

theorem graphTorusCenterQuotientEquiv_proj (hn : 3 ≤ n) (χ : SpecialLinearGroup (Fin n) F →* Kb)
    (hχ : Function.Surjective χ) (hker : χ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    (g : SpecialLinearGroup (Fin n) F) :
    graphTorusCenterQuotientEquiv hn χ hχ hker (proj n F g) =
      QuotientGroup.mk' (center Kb) (χ g) :=
  rfl

theorem nonempty_fixedSubgroup_descendAut_equiv (hn : 3 ≤ n)
    (χ : SpecialLinearGroup (Fin n) F →* Kb) (hχ : Function.Surjective χ)
    (hker : χ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {β : MulAut (SpecialLinearGroup (Fin n) F)} {τ : MulAut Kb} (hβτ : ∀ g, χ (β g) = τ (χ g)) :
    Nonempty (fixedSubgroup (descendAut n F β) ≃* fixedSubgroup (centerQuotientAut τ)) := by
  set ρ := graphTorusCenterQuotientEquiv hn χ hχ hker with hρ
  have hcongr : MulAut.congr ρ (descendAut n F β) = centerQuotientAut τ := by
    ext y
    obtain ⟨x, rfl⟩ := ρ.surjective y
    obtain ⟨g, rfl⟩ := proj_surjective n F x
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, descendAut_proj, hρ,
      graphTorusCenterQuotientEquiv_proj, graphTorusCenterQuotientEquiv_proj, hβτ,
      centerQuotientAut_mk]
  exact ⟨(CFSG.ComponentClassification.CatLeafProof.fixedSubgroupCongrEquiv ρ _).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hcongr))⟩

end Transfer

section Setting

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL descendAut)


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem exists_graphLift_X {t : G} {f : ℕ} (hw : F4Work L K t f) (hf : 2 ≤ f)
    (e : L ≃* adjointGroup .F4 K) {κ : Sp6Kind} (hκF : κ ≠ .field) (hκS : κ ≠ .swap)
    (hX : HR8Kind e t f .X κ) {m : ℕ} (hm : 4 ≤ m) {F : Type} [Field F] [Finite F]
    (Φ : SpecialLinearGroup (Fin (m + 1)) F →* G) (hE : Φ.range = neighbourCore e .X)
    (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F)) :
    ∃ β : MulAut (SpecialLinearGroup (Fin (m + 1)) F), (∀ g, Φ (β g) = t * Φ g * t⁻¹) ∧
      β * β = 1 ∧ descendAut (m + 1) F β * descendAut (m + 1) F β = 1 ∧
      descendAut (m + 1) F β ∉
        (MulAut.conj : projectiveSL (m + 1) F →* MulAut (projectiveSL (m + 1) F)).range ∧
      LieModel (fixedSubgroup (descendAut (m + 1) F β)) .PSp 3 2 f := by
  have hn3 : 3 ≤ m + 1 := by omega
  have : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) F) := graphTorus_isPerfect_SL hn3
  have htt : t * t = 1 := by rw [← sq, ← hw.orderOf_eq, pow_orderOf_eq_one]
  have htN : t ∈ normalizer (Φ.range : Set G) := by
    rw [hE]
    exact le_normalizer_neighbourCore e hw.mem_centralizer .X
  obtain ⟨β, hβ⟩ := exists_mulAut_comp_eq_conj hm Φ hker htN
  have hββ := mulAut_mul_self_of_comp_eq_conj hm Φ hker htt hβ
  obtain ⟨Kb, _, τ, qh, hqs, hqker, hτo, hτfix, hqt⟩ := exists_neighbourCoreData_X hw hf e hκS hX
    fun _ _ _ hKb hty => isSolvable_outer_of_sp6KindType_graph hKb hκF hκS hty
  have hmemE : ∀ g, Φ g ∈ neighbourCore e .X := fun g => hE ▸ ⟨g, rfl⟩
  set Φ' : SpecialLinearGroup (Fin (m + 1)) F →* neighbourCore e .X := Φ.codRestrict _ hmemE
  have hΦ's : Function.Surjective Φ' := by
    rintro ⟨y, hy⟩
    rw [← hE] at hy
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, rfl⟩
  have hΦ'ker : Φ'.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := fun g hg =>
    hker (by
      rw [MonoidHom.mem_ker] at hg ⊢
      exact congrArg Subtype.val hg)
  set χ : SpecialLinearGroup (Fin (m + 1)) F →* Kb := qh.comp Φ'
  have hχs : Function.Surjective χ := hqs.comp hΦ's
  have hχker : χ.ker ≤ center (SpecialLinearGroup (Fin (m + 1)) F) := fun g hg =>
    CFSG.ComponentClassification.OddSelector.mem_center_of_map_mem_center Φ' hΦ'ker (hqker hg)
  have hχβ : ∀ g, χ (β g) = τ (χ g) := by
    intro g
    have hy : t * ((Φ' g : neighbourCore e .X) : G) * t⁻¹ ∈ neighbourCore e .X := by
      change t * Φ g * t⁻¹ ∈ neighbourCore e .X
      rw [← hβ]
      exact hmemE _
    have e1 : Φ' (β g) = ⟨t * ((Φ' g : neighbourCore e .X) : G) * t⁻¹, hy⟩ :=
      Subtype.ext (hβ g)
    change qh (Φ' (β g)) = τ (qh (Φ' g))
    rw [e1, hqt]
  refine ⟨β, hβ, hββ, by rw [← map_mul, hββ, map_one], fun hin => hτo ?_, ?_⟩
  · exact graphTorus_mem_range_conj_of_descendAut hn3 χ hχs hχβ hin
  · obtain ⟨ε⟩ := nonempty_fixedSubgroup_descendAut_equiv hn3 χ hχs hχker hχβ
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv ε.symm hτfix

end Setting

end CFSG.SeitzReduction.F4Pilot

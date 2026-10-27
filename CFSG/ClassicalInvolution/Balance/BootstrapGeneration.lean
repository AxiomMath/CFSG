module

public import CFSG.ClassicalInvolution.Balance.BootstrapBridge
public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
public import CFSG.ClassicalInvolution.Balance.BootstrapAlpha
public import CFSG.ClassicalInvolution.Balance.BootstrapBalance
public import CFSG.ClassicalInvolution.Balance.BootstrapClosure

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure

section KG8

variable {X : Type} [Group X] [Finite X]

theorem kg8_generation (hmodel : LayerGenerationModel) {Y Q F : Subgroup X} (hQY : Q ≤ Y)
    (hQN : (Q.subgroupOf Y).Normal) (hqs : CFSG.Open.IsQuasisimple ↥Q)
    (hbig : IsOddLieComponentBig Q) (hFY : F ≤ Y) (hF4 : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) (hFN : F ≤ Subgroup.normalizer (Q : Set X))
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ Q, f * x = x * f) :
    Q ≤ ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) := by
  set L : Subgroup ↥Y := Q.subgroupOf Y with hL
  set F' : Subgroup ↥Y := F.subgroupOf Y with hF'
  have : L.Normal := hQN
  have hqsL : CFSG.Open.IsQuasisimple ↥L :=
    Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hQY) hqs
  have hcomp : CFSG.IsComponent L := by
    rw [CFSG.isComponent_iff_open]
    exact ⟨le_top, isSubnormal_of_normal_subgroupOf le_top Subgroup.normal_subgroupOf, hqsL⟩
  have hnt : ∃ x : ↥Q, (Subgroup.subgroupOfEquivOfLe hQY).symm x ≠ 1 := by
    have : Nontrivial (↥Q ⧸ Subgroup.center ↥Q) := hqs.2.toNontrivial
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥Q ⧸ Subgroup.center ↥Q)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨x, fun h => hy ?_⟩
    have hx1 : x = 1 := (MulEquiv.map_eq_one_iff _).mp h
    rw [hx1]
    rfl
  have hbigL : IsOddLieComponentBig L := by
    obtain ⟨t, n, p, f, hp, h5, hn, ht, hm⟩ := hbig
    exact isOddLieComponentBig_of_surjective hqs
      (Subgroup.subgroupOfEquivOfLe hQY).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQY).symm.surjective hnt hp h5 hn ht hm
  have hF'4 : Nat.card F' = 4 := by
    rw [← hF4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFY).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hF'N : F' ≤ Subgroup.normalizer (L : Set ↥Y) := fun f hf => by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact Subgroup.mem_normalizer_iff.mp (hFN (show f.1 ∈ F from hf)) h.1
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f := by
    intro f hf hf1 hcomm
    refine hfaith f.1 (show f.1 ∈ F from hf) (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    exact congrArg Subtype.val (hcomm ⟨x, hQY hx⟩ hx)
  have hKG := hmodel ↥Y L hcomp hbigL F' hF'4 hF'2 hF'N hfaith'
  have hle : (⨆ f ∈ F', ⨆ (_ : f ≠ 1), centralizerLayer f) ≤
      (⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X)).comap Y.subtype := by
    refine iSup₂_le fun f hf => iSup_le fun hf1 => ?_
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ({f} : Set ↥Y) := Subgroup.map_subtype_le _ hx
    have hcomm : x * f = f * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    have hf1' : (f : X) ≠ 1 := fun h => hf1 (Subtype.ext h)
    have hmem : (x : X) ∈ Y ⊓ Subgroup.centralizer ({f.1} : Set X) :=
      ⟨x.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hcomm)⟩
    have hsub : (Y ⊓ Subgroup.centralizer ({f.1} : Set X)) ≤
        ⨆ f ∈ F, ⨆ (_ : f ≠ 1), Y ⊓ Subgroup.centralizer ({f} : Set X) :=
      le_iSup₂_of_le f.1 (show f.1 ∈ F from hf) (le_iSup_of_le hf1' le_rfl)
    exact hsub hmem
  intro x hx
  exact hle (hKG (show (⟨x, hQY hx⟩ : ↥Y) ∈ L from hx))

end KG8

section Lifting

open CFSG.SignalizerFunctor.Helpers

variable {GroupType ImageType : Type} [Group GroupType] [Group ImageType]

theorem map_inf_centralizer_eq (φ : GroupType →* ImageType) (hker : Odd (Nat.card φ.ker))
    (actor target : Subgroup GroupType) (hact : IsPGroup 2 actor)
    (hnorm : actor ≤ Subgroup.normalizer (target : Set GroupType)) :
    (target ⊓ Subgroup.centralizer (actor : Set GroupType)).map φ =
      target.map φ ⊓ Subgroup.centralizer (actor.map φ : Set ImageType) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _action := conjugationAction actor target hnorm
  apply le_antisymm
  · rintro imageElement ⟨element, member, rfl⟩
    refine ⟨⟨element, member.1, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro imageActor ⟨actorElement, actor_member, rfl⟩
    simpa only [map_mul] using congrArg φ
      (Subgroup.mem_centralizer_iff.mp member.2 actorElement actor_member)
  · intro imageElement member
    obtain ⟨element, element_member, image_eq⟩ := member.1
    let restricted := φ.domRestrict target
    let fibre : SubMulAction actor target :=
      ⟨{representative | restricted representative = imageElement}, by
        intro actorElement representative representative_member
        change φ (actorElement.val * representative.val * actorElement.val⁻¹) = imageElement
        rw [map_mul, map_mul, map_inv]
        change φ actorElement.val * restricted representative * (φ actorElement.val)⁻¹ =
          imageElement
        rw [representative_member]
        have commutes := Subgroup.mem_centralizer_iff.mp member.2
          (φ actorElement.val) (Subgroup.mem_map_of_mem φ actorElement.property)
        rw [commutes, mul_assoc, mul_inv_cancel, mul_one]⟩
    have fibre_card : Nat.card fibre = Nat.card restricted.ker := by
      have fibre_eq : {representative : target | restricted representative = imageElement} =
          restricted ⁻¹' {restricted (⟨element, element_member⟩ : target)} := by
        ext representative
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
        change (restricted representative = imageElement) ↔ restricted representative = φ element
        rw [image_eq]
      exact (Nat.card_congr (Set.equivOfEq fibre_eq)).trans
        (Nat.card_congr (restricted.fiberEquivKer (⟨element, element_member⟩ : target)))
    have hkerdvd : Nat.card restricted.ker ∣ Nat.card φ.ker := by
      let ι : restricted.ker →* φ.ker :=
        { toFun := fun x => ⟨x.1.1, MonoidHom.mem_ker.mp x.2⟩
          map_one' := rfl
          map_mul' := fun x y => rfl }
      refine Subgroup.card_dvd_of_injective ι fun x y hxy => ?_
      have h1 := congrArg (fun z : ↥φ.ker => (z : GroupType)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have not_divides : ¬ 2 ∣ Nat.card fibre := by
      rw [fibre_card]
      exact Nat.prime_two.coprime_iff_not_dvd.mp
        ((Nat.coprime_two_left.mpr hker).of_dvd_right hkerdvd)
    obtain ⟨representative, fixed⟩ :=
      hact.nonempty_fixed_point_of_prime_not_dvd_card fibre not_divides
    refine ⟨representative.val.val, ⟨representative.val.property, ?_⟩, representative.property⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro actorElement actor_member
    have equality := congrArg (fun fixedElement : fibre => fixedElement.val.val)
      (fixed (⟨actorElement, actor_member⟩ : actor))
    change actorElement * representative.val.val * actorElement⁻¹ = representative.val.val
      at equality
    exact mul_inv_eq_iff_eq_mul.mp equality

end Lifting

section Subgroups

variable {G : Type} [Group G]

theorem card_closure_pair_eq_four [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) (hc : x * y = y * x) :
    Nat.card (Subgroup.closure ({x, y} : Set G)) = 4 := by
  refine le_antisymm (card_closure_pair_le_four hx hy hc) ?_
  have hnot : y ∉ Subgroup.closure ({x} : Set G) := by
    intro hyc
    have key : ∀ g (hg : g ∈ Subgroup.closure ({x} : Set G)), g = 1 ∨ g = x := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => g = 1 ∨ g = x) ?_ ?_ ?_ ?_ hg
      · intro u hu
        right
        simpa using hu
      · left
        rfl
      · rintro u v - - (hu | hu) (hv | hv) <;> subst hu <;> subst hv
        · left; simp
        · right; simp
        · right; simp
        · left; exact hx
      · rintro u - (hu | hu) <;> subst hu
        · left; simp
        · right; exact inv_eq_of_mul_eq_one_right hx
    rcases key y hyc with h | h
    · exact hy1 h
    · exact hxy h.symm
  set A₁ : Subgroup G := Subgroup.closure ({x} : Set G) with hA₁
  set A₂ : Subgroup G := Subgroup.closure ({x, y} : Set G) with hA₂
  have h1 : (⊥ : Subgroup G) < A₁ := by
    refine lt_of_le_of_ne bot_le fun hh => hx1 ?_
    have : x ∈ A₁ := Subgroup.subset_closure rfl
    rwa [← hh, Subgroup.mem_bot] at this
  have h2 : A₁ < A₂ := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by simp)) fun hh => ?_
    have : y ∈ A₂ := Subgroup.subset_closure (by simp)
    rw [← hh] at this
    exact hnot this
  have c1 := ExactTriple.two_mul_card_le_of_lt' h1
  have c2 := ExactTriple.two_mul_card_le_of_lt' h2
  have hbot : Nat.card (⊥ : Subgroup G) = 1 := Subgroup.card_bot
  omega

theorem exists_four_subgroup_inf_eq_bot [Finite G] {A Z : Subgroup G} (hA : IsElemAbelian 2 A)
    (hcard : Nat.card A = 8) (hZA : Z ≤ A)
    (hZ : ¬ ∃ F ∈ signalizerFunctorEk 2 2 A, F ≤ Z) :
    ∃ F ∈ signalizerFunctorEk 2 2 A, F ⊓ Z = ⊥ := by
  have hZel : IsElemAbelian 2 Z :=
    CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hZA
  have hZcard : Nat.card Z < 4 := by
    by_contra hge
    push Not at hge
    obtain ⟨F, hF⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
      Nat.prime_two Z hZel (by simpa using hge)
    exact hZ ⟨F, ⟨hF.1.trans hZA, hF.2⟩, hF.1⟩
  obtain ⟨C', hC'A, -, hZC', hsup⟩ := CFSG.SignalizerFunctorTheorem.exists_complement_containing
    Nat.prime_two hA hZA (bot_le : (⊥ : Subgroup G) ≤ A) (inf_bot_eq Z)
  have hmul := CFSG.SignalizerFunctorTheorem.card_mul_card_complement hA hZA hC'A hZC' hsup
  have hC'4 : 4 ≤ Nat.card C' := by
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    rw [hcard] at hmul
    have hdvd : Nat.card Z ∣ 8 := ⟨Nat.card C', hmul.symm⟩
    generalize Nat.card Z = n at hZpos hZcard hdvd hmul
    interval_cases n <;> omega
  obtain ⟨F, hF⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
    Nat.prime_two C' (CFSG.SignalizerFunctor.Helpers.elementary_abelian_of_le 2 hA hC'A)
    (by simpa using hC'4)
  refine ⟨F, ⟨hF.1.trans hC'A, hF.2⟩, ?_⟩
  rw [eq_bot_iff, ← hZC']
  exact inf_le_inf_right Z hF.1 |>.trans (by rw [inf_comm])

end Subgroups

section Local

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem isPGroup_two_of_sq_eq_one {H : Type} [Group H] {S : Subgroup H}
    (h : ∀ x ∈ S, x * x = 1) : IsPGroup 2 S := fun x =>
  ⟨1, by rw [pow_one, pow_two]; exact Subtype.ext (h x x.2)⟩

theorem le_normalizer_of_normal_subgroupOf {X : Type} [Group X] {Q Y : Subgroup X} (hQY : Q ≤ Y)
    (hQN : (Q.subgroupOf Y).Normal) : Y ≤ Subgroup.normalizer (Q : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (Subgroup.normal_subgroupOf_iff hQY).mp hQN h x hh hx
  · intro hh
    have := (Subgroup.normal_subgroupOf_iff hQY).mp hQN _ x⁻¹ hh (inv_mem hx)
    simpa [mul_assoc] using this

omit [Finite G] in
theorem oddQuotMk_mem_memberJoin {y : G} (hy : y ∈ centLayer Ω a)
    (hyC : y ∈ Subgroup.centralizer ({a} : Set G)) : oddQuotMk a ⟨y, hyC⟩ ∈ memberJoin Ω a := by
  rw [← range_layerToOddQuot_eq]
  exact ⟨⟨y, hy⟩, rfl⟩

omit [Finite G] in
theorem modOdd_le_memberJoin {F : Subgroup G} (hF : F ≤ centLayer Ω a) :
    modOdd a F ≤ memberJoin Ω a := by
  rintro _ ⟨x, hx, rfl⟩
  exact oddQuotMk_mem_memberJoin (hF (Subgroup.mem_subgroupOf.mp hx)) x.2

omit [Finite G] in
theorem oddQuotMk_central (haC : a ∈ Subgroup.centralizer ({a} : Set G)) (y : OddQuot a) :
    oddQuotMk a ⟨a, haC⟩ * y = y * oddQuotMk a ⟨a, haC⟩ := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective
    (componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G))) y
  change oddQuotMk a ⟨a, haC⟩ * oddQuotMk a c = oddQuotMk a c * oddQuotMk a ⟨a, haC⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp c.2).symm

theorem exists_lift_centralizer {E : Subgroup G}
    (hE2 : ∀ e ∈ E, e * e = 1) (hEY : E ≤ centLayer Ω a) {q : OddQuot a}
    (hq : q ∈ memberJoin Ω a)
    (hcent : ∀ (e : G) (_ : e ∈ E) (hC : e ∈ Subgroup.centralizer ({a} : Set G)),
      oddQuotMk a ⟨e, hC⟩ * q = q * oddQuotMk a ⟨e, hC⟩) :
    ∃ (y : G) (hyC : y ∈ Subgroup.centralizer ({a} : Set G)), y ∈ centLayer Ω a ∧
      y ∈ Subgroup.centralizer (E : Set G) ∧ oddQuotMk a ⟨y, hyC⟩ = q := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hYC : centLayer Ω a ≤ C := centLayer_le_centralizer Ω a
  have hker : Odd (Nat.card (oddQuotMk a).ker) := by
    rw [show (oddQuotMk a).ker = componentClassificationOddCore ↥C from
      QuotientGroup.ker_mk' _]
    exact OddCore.odd_card _
  have hnorm : E.subgroupOf C ≤ Subgroup.normalizer (((centLayer Ω a).subgroupOf C : Subgroup ↥C) :
      Set ↥C) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have heY : (e : G) ∈ centLayer Ω a := hEY (Subgroup.mem_subgroupOf.mp he)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro hh
      exact mul_mem (mul_mem heY hh) (inv_mem heY)
    · intro hh
      have := mul_mem (mul_mem (inv_mem heY) hh) heY
      simpa [mul_assoc] using this
  have key := map_inf_centralizer_eq (oddQuotMk a) hker (E.subgroupOf C)
    ((centLayer Ω a).subgroupOf C)
    (isPGroup_two_of_sq_eq_one fun x hx => Subtype.ext (hE2 _ (Subgroup.mem_subgroupOf.mp hx)))
    hnorm
  have hqmem : q ∈ ((centLayer Ω a).subgroupOf C).map (oddQuotMk a) ⊓
      Subgroup.centralizer ((E.subgroupOf C).map (oddQuotMk a) : Set (OddQuot a)) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [← range_layerToOddQuot_eq] at hq
      obtain ⟨y, rfl⟩ := hq
      exact ⟨⟨y, centLayer_le_centralizer Ω a y.2⟩, y.2, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      exact hcent e (Subgroup.mem_subgroupOf.mp he) e.2
  rw [← key] at hqmem
  obtain ⟨g, ⟨hgY, hgE⟩, hgq⟩ := hqmem
  refine ⟨g, g.2, Subgroup.mem_subgroupOf.mp hgY, fun e he => ?_, hgq⟩
  have := Subgroup.mem_centralizer_iff.mp hgE ⟨e, hYC (hEY he)⟩
    (Subgroup.mem_subgroupOf.mpr he)
  exact congrArg Subtype.val this

end Local

section Component

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem component_le_modOdd (hmodel : LayerGenerationModel) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) (haA : a ∈ A) (ha1 : a ≠ 1)
    (hAY : A ≤ centLayer Ω a) {Q : Subgroup (OddQuot a)} (hQJ : Q ≤ memberJoin Ω a)
    (hQN : (Q.subgroupOf (memberJoin Ω a)).Normal) (hqs : CFSG.Open.IsQuasisimple ↥Q)
    (hQ : (∀ g ∈ A, ∀ (hgC : g ∈ Subgroup.centralizer ({a} : Set G)),
        ∀ y ∈ Q, oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩) ∨
      IsOddLieComponentBig Q) :
    Q ≤ modOdd a (⨆ F ∈ signalizerFunctorEk 2 2 A,
      (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a)) := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  set Y : Subgroup G := centLayer Ω a with hY
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ Y) with hJ
  have hA2 : ∀ x ∈ A, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hA.2 x hx
  have hAC : A ≤ C := fun e he => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.is_comm.comm (⟨e, he⟩ : A) ⟨a, haA⟩))
  have haC : a ∈ C := hAC haA
  have hJmem : ∀ (F : Subgroup G), F ∈ signalizerFunctorEk 2 2 A → ∀ (y : G),
      y ∈ Subgroup.centralizer (F : Set G) → y ∈ Y → y ∈ J := fun F hF y hyF hyY =>
    (le_iSup₂ (f := fun (F : Subgroup G) (_ : F ∈ signalizerFunctorEk 2 2 A) =>
      Subgroup.centralizer (F : Set G) ⊓ Y) F hF) ⟨hyF, hyY⟩
  set Z : Subgroup G := A ⊓ ((Subgroup.centralizer (Q : Set (OddQuot a))).comap
    (oddQuotMk a)).map C.subtype with hZ
  have hZmem : ∀ x : ↥C, (x : G) ∈ A → oddQuotMk a x ∈ Subgroup.centralizer (Q : Set (OddQuot a)) →
      (x : G) ∈ Z := fun x hxA hx => ⟨hxA, ⟨x, hx, rfl⟩⟩
  have hZcent : ∀ (g : G) (hgC : g ∈ C), g ∈ Z → ∀ y ∈ Q,
      oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩ := by
    rintro g hgC ⟨-, ⟨c, hc, rfl⟩⟩ y hy
    exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
  by_cases hF : ∃ F ∈ signalizerFunctorEk 2 2 A, F ≤ Z
  ·
    obtain ⟨F, hFE, hFZ⟩ := hF
    intro q hq
    obtain ⟨y, hyC, hyY, hyF, hyq⟩ := exists_lift_centralizer (E := F)
      (fun e he => hA2 e (hFE.1 he)) (hFE.1.trans hAY) (hQJ hq)
      (fun e he heC => hZcent e heC (hFZ he) q hq)
    exact ⟨⟨y, hyC⟩, hJmem F hFE y hyF hyY, hyq⟩
  · rcases hQ with hQc | hbig
    · exfalso
      obtain ⟨F, hFE⟩ := CFSG.SignalizerFunctor.Helpers.signalizerFunctorEk_nonempty 2 2
        Nat.prime_two A hA (by rw [hcard]; norm_num)
      refine hF ⟨F, hFE, fun x hx => ?_⟩
      have hxA : x ∈ A := hFE.1 hx
      exact hZmem ⟨x, hAC hxA⟩ hxA (Subgroup.mem_centralizer_iff.mpr fun y hy =>
        (hQc x hxA (hAC hxA) y hy).symm)
    ·
      obtain ⟨F', hF'E, hF'Z⟩ := exists_four_subgroup_inf_eq_bot hA hcard inf_le_left hF
      have hF'A : F' ≤ A := hF'E.1
      have hF'2 : ∀ x ∈ F', x * x = 1 := fun x hx => hA2 x (hF'A hx)
      have hF'C : F' ≤ C := hF'A.trans hAC
      set Fb : Subgroup (OddQuot a) := modOdd a F' with hFb
      have hFb4 : Nat.card Fb = 4 := by
        rw [hFb, card_modOdd_of_exponent_two hF'C hF'2, hF'E.2]
        norm_num
      have hFb2 : ∀ x ∈ Fb, x * x = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : (x : G) ∈ F' := hx
        rw [← map_mul]
        have : x * x = 1 := Subtype.ext (hF'2 _ hx')
        rw [this, map_one]
      have hFbJ : Fb ≤ memberJoin Ω a := modOdd_le_memberJoin (hF'A.trans hAY)
      have hFbN : Fb ≤ Subgroup.normalizer (Q : Set (OddQuot a)) :=
        hFbJ.trans (le_normalizer_of_normal_subgroupOf hQJ hQN)
      have hfaith : ∀ x ∈ Fb, x ≠ 1 → ¬ ∀ y ∈ Q, x * y = y * x := by
        intro x hx hx1 hcomm
        obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
        have hkZ : (k : G) ∈ Z := hZmem k (hF'A hk)
          (Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm y hy).symm)
        have hk1 : (k : G) ∈ F' ⊓ Z := ⟨hk, hkZ⟩
        rw [hF'Z, Subgroup.mem_bot] at hk1
        exact hx1 (by rw [show k = 1 from Subtype.ext hk1, map_one])
      have hKG := kg8_generation hmodel hQJ hQN hqs hbig hFbJ hFb4 hFb2 hFbN hfaith
      refine hKG.trans (iSup₂_le fun x hx => iSup_le fun hx1 => ?_)
      obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
      have hkF' : (k : G) ∈ F' := hk
      have hk1 : (k : G) ≠ 1 := fun h => hx1 (by rw [show k = 1 from Subtype.ext h, map_one])
      have hka : (k : G) ≠ a := by
        intro h
        refine hfaith _ hx hx1 fun y _ => ?_
        have : k = ⟨a, haC⟩ := Subtype.ext h
        rw [this]
        exact oddQuotMk_central haC y
      have hkA : (k : G) ∈ A := hF'A hkF'
      have hcomm : a * (k : G) = (k : G) * a :=
        congrArg Subtype.val (hA.1.is_comm.comm (⟨a, haA⟩ : A) ⟨k, hkA⟩)
      have hE4 : Nat.card (Subgroup.closure ({a, (k : G)} : Set G)) = 4 :=
        card_closure_pair_eq_four (hA2 a haA) (hA2 _ hkA) ha1 hk1 (Ne.symm hka) hcomm
      have hEA : Subgroup.closure ({a, (k : G)} : Set G) ≤ A := by
        rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        exacts [haA, hkA]
      have hEmem : Subgroup.closure ({a, (k : G)} : Set G) ∈ signalizerFunctorEk 2 2 A :=
        ⟨hEA, by rw [hE4]; norm_num⟩
      rintro q ⟨hqJ, hqk⟩
      have hkq : oddQuotMk a k * q = q * oddQuotMk a k :=
        (Subgroup.mem_centralizer_singleton_iff.mp hqk).symm
      obtain ⟨y, hyC, hyY, hyk, hyq⟩ := exists_lift_centralizer (E := Subgroup.zpowers (k : G))
        (fun e he => by
          rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
          exacts [one_mul 1, hF'2 _ hkF'])
        (Subgroup.zpowers_le.mpr (hAY hkA)) hqJ
        (fun e he heC => by
          rcases mem_zpowers_involution (hF'2 _ hkF') he with rfl | rfl
          · change oddQuotMk a 1 * q = q * oddQuotMk a 1
            rw [map_one, one_mul, mul_one]
          · exact hkq)
      have hyE : y ∈ Subgroup.centralizer
          ((Subgroup.closure ({a, (k : G)} : Set G) : Subgroup G) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hsub : ({a, (k : G)} : Set G) ⊆
            ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
          rintro z (rfl | rfl)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_singleton_iff.mp hyC).symm
          · exact Subgroup.mem_centralizer_singleton_iff.mpr
              (Subgroup.mem_centralizer_iff.mp hyk _ (Subgroup.mem_zpowers _))
        exact Subgroup.mem_centralizer_singleton_iff.mp ((Subgroup.closure_le _).mpr hsub hx)
      exact ⟨⟨y, hyC⟩, hJmem _ hEmem y hyE hyY, hyq⟩

end Component

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem centralizerGenerationModOTwo_of_model (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationModel) {A : Subgroup G}
    (hA : IsElemAbelian 2 A) (hcard : Nat.card A = 8) (haA : a ∈ A)
    (hnc : ¬ ({a} : Set G) ⊆ Subgroup.center G) (hAY : A ≤ centLayer Ω a)
    (hrk : ∀ L : Subgroup (OddQuot a), RankOneAt Ω a L → ∀ g ∈ A,
      ∀ (hgC : g ∈ Subgroup.centralizer ({a} : Set G)), ∀ y ∈ L,
        oddQuotMk a ⟨g, hgC⟩ * y = y * oddQuotMk a ⟨g, hgC⟩) :
    CentralizerGenerationModOTwo Ω A a := by
  classical
  have ha1 : a ≠ 1 := fun h => hnc (by simp [h])
  obtain ⟨D, hD⟩ := lieDecomposition_memberImages_big hp2 h0 hA1 hq hΩ hIH hnc
    (NoComponentOverF3.of_ne_27 a hq h27)
  have hΩc : ConjInvariant Ω := hΩ.conjInvariant
  set J : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 A,
    (Subgroup.centralizer (F : Set G) ⊓ centLayer Ω a) with hJ
  have hQ : ∀ i, D.Q i ≤ modOdd a J := by
    intro i
    refine component_le_modOdd hmodel hA hcard haA ha1 hAY (D.le_join i) (D.normal_subgroupOf i)
      (D.quasisimple i) ?_
    rcases hD i with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hbig
    · left
      have hr1 : RankOneAt Ω a (D.Q i) := by
        refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
        obtain ⟨j, hj⟩ := D.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
        by_cases hji : j = i
        · subst hji
          exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
        · exact Or.inr fun x hx y hy => D.commute j i hji x (hj hx) y hy
      exact fun g hg hgC y hy => hrk _ hr1 g hg hgC y hy
    · right
      exact hbig
  have hJY : J ≤ centLayer Ω a := iSup₂_le fun _ _ => inf_le_right
  show centLayer Ω a ≤ oddCoreIn (centLayer Ω a) ⊔ J
  intro y hy
  have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := centLayer_le_centralizer Ω a hy
  have hyJ := oddQuotMk_mem_memberJoin hy hyC
  rw [← D.iSup_eq] at hyJ
  obtain ⟨k, hkJ, hk⟩ := mem_modOdd_iff.mp ((iSup_le hQ) hyJ)
  have hkY : (k : G) ∈ centLayer Ω a := hJY hkJ
  have hker : (⟨k, hkY⟩ : ↥(centLayer Ω a))⁻¹ * ⟨y, hy⟩ ∈ (layerToOddQuot Ω a).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    change (oddQuotMk a k)⁻¹ * oddQuotMk a ⟨y, hyC⟩ = 1
    rw [hk, inv_mul_cancel]
  rw [ker_layerToOddQuot hΩc] at hker
  have hodd : (k : G)⁻¹ * y ∈ oddCoreIn (centLayer Ω a) := ⟨_, hker, rfl⟩
  have hmem : (k : G) * ((k : G)⁻¹ * y) ∈ J ⊔ oddCoreIn (centLayer Ω a) :=
    Subgroup.mul_mem_sup hkJ hodd
  rwa [mul_inv_cancel_left, sup_comm] at hmem

end Main

section Triple

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizerGenerationModOTwo_of_exactTriple [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (h27 : p ^ f ≠ 27)
    (h0 : ModelClauseZero) (hA1 : FundamentalWholeA1) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) (hmodel : LayerGenerationModel)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {a : G}
    (ha : a ∈ T.group) (ha1 : a ≠ 1) : CentralizerGenerationModOTwo Ω T.group a := by
  have hcen : ∀ {K : Subgroup G}, K ≤ Subgroup.centralizer (T.group : Set G) →
      K ≤ Subgroup.centralizer ({a} : Set G) := fun hK =>
    hK.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))
  have hAY : T.group ≤ centLayer Ω a := by
    rw [ExactTriple.group, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact le_centLayer ⟨hΩ₁, hcen T.le_centralizer₁⟩ T.mem₁
    · exact le_centLayer ⟨hΩ₂, hcen T.le_centralizer₂⟩ T.mem₂
    · exact le_centLayer ⟨hΩ₃, hcen T.le_centralizer₃⟩ T.mem₃
  exact centralizerGenerationModOTwo_of_model hp2 hq h27 h0 hA1 hΩ hIH hmodel T.isElemAbelian
    (T.card_eq_eight hind) ha (not_subset_center_of_ne_one hnab ha1) hAY
    fun L hL g hg hgC y hy =>
      oddQuotMk_centralizes_of_mem_group T hΩ₁ hΩ₂ hΩ₃ ha (Or.inr hL) hg hgC y hy

end Triple

end CFSG.ClassicalInvolution.Balance.Bootstrap

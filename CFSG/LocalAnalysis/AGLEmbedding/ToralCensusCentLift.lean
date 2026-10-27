module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

namespace ToralCensus

@[expose] def PerfectNoncycThreeIn {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ∃ V : Subgroup G, V ≤ C ∧ ⁅V, V⁆ = V ∧ ∃ Q : Subgroup G, Q ≤ V ∧ IsPGroup 3 Q ∧ ¬ IsCyclic Q

@[expose] def PerfectThreeIn {G : Type*} [Group G] (C : Subgroup G) : Prop :=
  ∃ V : Subgroup G, V ≤ C ∧ ⁅V, V⁆ = V ∧ ∃ x ∈ V, x ^ 3 = 1 ∧ x ≠ 1

@[expose] def CentNoncycThreeGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, g ^ 3 = 1 → g ≠ 1 → PerfectNoncycThreeIn (Subgroup.centralizer ({g} : Set G))

section Transfer

variable {G H : Type*} [Group G] [Group H]

theorem PerfectNoncycThreeIn.mono {C D : Subgroup G} (h : PerfectNoncycThreeIn C) (hCD : C ≤ D) :
    PerfectNoncycThreeIn D := by
  obtain ⟨V, hVC, hV⟩ := h
  exact ⟨V, hVC.trans hCD, hV⟩

theorem PerfectThreeIn.mono {C D : Subgroup G} (h : PerfectThreeIn C) (hCD : C ≤ D) :
    PerfectThreeIn D := by
  obtain ⟨V, hVC, hV⟩ := h
  exact ⟨V, hVC.trans hCD, hV⟩

theorem PerfectNoncycThreeIn.map {C : Subgroup G} (h : PerfectNoncycThreeIn C) (φ : G →* H)
    (hφ : Function.Injective φ) : PerfectNoncycThreeIn (C.map φ) := by
  obtain ⟨V, hVC, hV, Q, hQV, hQ, hnc⟩ := h
  refine ⟨V.map φ, Subgroup.map_mono hVC, by rw [← Subgroup.map_commutator, hV], Q.map φ,
    Subgroup.map_mono hQV, hQ.map φ, fun hc => hnc ?_⟩
  have e := Q.equivMapOfInjective φ hφ
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

theorem PerfectThreeIn.map {C : Subgroup G} (h : PerfectThreeIn C) (φ : G →* H)
    (hφ : Function.Injective φ) : PerfectThreeIn (C.map φ) := by
  obtain ⟨V, hVC, hV, x, hxV, hx3, hx1⟩ := h
  refine ⟨V.map φ, Subgroup.map_mono hVC, by rw [← Subgroup.map_commutator, hV], φ x,
    ⟨x, hxV, rfl⟩, by rw [← map_pow, hx3, map_one], fun h1 => hx1 (hφ (h1.trans ?_))⟩
  exact (map_one φ).symm

theorem CentNoncycThreeGroup.of_mulEquiv (e : G ≃* H) (h : CentNoncycThreeGroup H) :
    CentNoncycThreeGroup G := by
  intro g hg3 hg1
  refine ((h (e g) (by rw [← map_pow, hg3, map_one])
    (fun h1 => hg1 (e.injective (h1.trans (map_one e).symm)))).map e.symm.toMonoidHom
    e.symm.injective).mono ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply e.injective
  have := Subgroup.mem_centralizer_singleton_iff.mp hv
  simpa using this

end Transfer

theorem not_isCyclic_closure_pair {G : Type*} [Group G] [Finite G] {x y : G} (hxy : Commute x y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    IsPGroup 3 (Subgroup.closure {x, y}) ∧ ¬ IsCyclic (Subgroup.closure {x, y}) := by
  set C := Subgroup.closure ({x, y} : Set G)
  have hcomm : IsMulCommutative C := Subgroup.isMulCommutative_closure (by
    intro a ha b hb _
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    exacts [Commute.refl _, hxy, hxy.symm, Commute.refl _])
  have hpow : ∀ z ∈ C, z ^ 3 = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem a ha => rcases ha with rfl | rfl <;> assumption
    | one => exact one_pow 3
    | mul a b ha hb iha ihb =>
      have hab : Commute a b := by
        have := hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
        exact congrArg Subtype.val this
      rw [hab.mul_pow, iha, ihb, one_mul]
    | inv a _ iha => rw [inv_pow, iha, inv_one]
  have hxC : x ∈ C := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyC : y ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  refine ⟨fun z => ⟨1, Subtype.ext (by simpa using hpow z z.2)⟩, fun hc => ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := C)
  have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hpow g g.2)
  have hle : Nat.card C ≤ 3 := hg ▸ Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg3)
  have hlt : Subgroup.zpowers x < C := lt_of_le_of_ne
    ((Subgroup.zpowers_le).mpr hxC) (fun h => hyx (h ▸ hyC))
  have hcard := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, orderOf_eq_prime hx hx1] at hcard
  omega

theorem PerfectNoncycThreeIn.of_pair {G : Type*} [Group G] [Finite G] {C V : Subgroup G}
    (hVC : V ≤ C) (hV : ⁅V, V⁆ = V) {x y : G} (hxV : x ∈ V) (hyV : y ∈ V) (hxy : Commute x y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    PerfectNoncycThreeIn C := by
  obtain ⟨h3, hnc⟩ := not_isCyclic_closure_pair hxy hx hy hx1 hyx
  refine ⟨V, hVC, hV, _, ?_, h3, hnc⟩
  rw [Subgroup.closure_le]
  rintro _ (rfl | rfl)
  exacts [hxV, hyV]

theorem PerfectNoncycThreeIn.of_two {G : Type*} [Group G] [Finite G] {C F₁ F₂ : Subgroup G}
    (h₁ : F₁ ≤ C) (h₂ : F₂ ≤ C) (hcomm : ∀ a ∈ F₁, ∀ b ∈ F₂, Commute a b)
    (hdisj : Disjoint F₁ F₂) (hP₁ : PerfectThreeIn F₁) (hP₂ : PerfectThreeIn F₂) :
    PerfectNoncycThreeIn C := by
  obtain ⟨V₁, hV₁F, hV₁, x, hxV, hx3, hx1⟩ := hP₁
  obtain ⟨V₂, hV₂F, hV₂, y, hyV, hy3, hy1⟩ := hP₂
  have hperf : ⁅V₁ ⊔ V₂, V₁ ⊔ V₂⁆ = V₁ ⊔ V₂ := by
    refine le_antisymm (ParabPrime.commutator_self_le _) (sup_le ?_ ?_)
    · calc V₁ = ⁅V₁, V₁⁆ := hV₁.symm
        _ ≤ _ := Subgroup.commutator_mono le_sup_left le_sup_left
    · calc V₂ = ⁅V₂, V₂⁆ := hV₂.symm
        _ ≤ _ := Subgroup.commutator_mono le_sup_right le_sup_right
  refine PerfectNoncycThreeIn.of_pair (sup_le (hV₁F.trans h₁) (hV₂F.trans h₂)) hperf
    (Subgroup.mem_sup_left hxV) (Subgroup.mem_sup_right hyV) (hcomm x (hV₁F hxV) y (hV₂F hyV))
    hx3 hy3 hx1 fun hyx => hy1 ?_
  have hyF₁ : y ∈ F₁ := (Subgroup.zpowers_le.mpr (hV₁F hxV)) hyx
  exact Subgroup.disjoint_def.mp hdisj hyF₁ (hV₂F hyV)

theorem commutator_le_centralizer_of_central {G : Type*} [Group G] {W : Subgroup G} {u : G}
    (hW : ∀ w ∈ W, w * u * w⁻¹ * u⁻¹ ∈ Subgroup.center G) :
    ⁅W, W⁆ ≤ Subgroup.centralizer ({u} : Set G) := by
  set f : G → G := fun w => w * u * w⁻¹ * u⁻¹ with hf
  have hc : ∀ c ∈ Subgroup.center G, ∀ g : G, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.mp hc g
  have hmul : ∀ a b, f b ∈ Subgroup.center G → f (a * b) = f b * f a := fun a b hb =>
    calc f (a * b) = a * f b * (u * a⁻¹ * u⁻¹) := by simp only [hf]; group
      _ = f b * a * (u * a⁻¹ * u⁻¹) := by rw [hc _ hb a]
      _ = f b * f a := by simp only [hf]; group
  have hinv : ∀ a, f a ∈ Subgroup.center G → f a⁻¹ = (f a)⁻¹ := fun a ha => by
    have h1 := hmul a⁻¹ a ha
    rw [inv_mul_cancel, show f 1 = 1 by simp only [hf]; group] at h1
    exact (eq_inv_of_mul_eq_one_right h1.symm)
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hfa : f a ∈ Subgroup.center G := hW a ha
  have hfb : f b ∈ Subgroup.center G := hW b hb
  have hfa' : f a⁻¹ ∈ Subgroup.center G := by rw [hinv a hfa]; exact inv_mem hfa
  have hfb' : f b⁻¹ ∈ Subgroup.center G := by rw [hinv b hfb]; exact inv_mem hfb
  have hkey : f (a * b * a⁻¹ * b⁻¹) = 1 := by
    rw [hmul _ _ hfb', hmul _ _ hfa', hmul _ _ hfb, hinv a hfa, hinv b hfb, hc _ hfa (f b)]
    group
  rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
  have : a * b * a⁻¹ * b⁻¹ * u * (a * b * a⁻¹ * b⁻¹)⁻¹ * u⁻¹ = 1 := hkey
  calc a * b * a⁻¹ * b⁻¹ * u
      = a * b * a⁻¹ * b⁻¹ * u * (a * b * a⁻¹ * b⁻¹)⁻¹ * u⁻¹ * (u * (a * b * a⁻¹ * b⁻¹)) := by
        group
    _ = u * (a * b * a⁻¹ * b⁻¹) := by rw [this, one_mul]

theorem centPerfectNoncyc_of_quotient {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : CentNoncycThreeGroup (↥L ⧸ Subgroup.center ↥L)) {u : Y} (hu : u ∈ L)
    (hu3 : u ^ 3 = 1) (hnc : u ∉ Subgroup.centralizer (L : Set Y)) : CentPerfectNoncyc 3 L u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  set u' : ↥L := ⟨u, hu⟩ with hu'
  have hu'3 : u' ^ 3 = 1 := Subtype.ext (by simpa [hu'] using hu3)
  have hπu : π u' ≠ 1 := by
    intro h
    apply hnc
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := Subgroup.mem_center_iff.mp h ⟨l, hl⟩
    exact congrArg Subtype.val this
  obtain ⟨Vb, hVbC, hVb, Qb, hQbV, hQb3, hQbnc⟩ :=
    hL (π u') (by rw [← map_pow, hu'3, map_one]) hπu
  obtain ⟨W, hW, hWV, hWmap⟩ := ParabPrime.exists_perfect_map_eq π
    (by rw [hπ, QuotientGroup.ker_mk']) hVb
    (by rw [hπ, QuotientGroup.range_mk']; exact le_top)
  have hWC : W ≤ Subgroup.centralizer ({u'} : Set ↥L) := by
    rw [← hW]
    refine (Subgroup.commutator_mono le_rfl le_rfl).trans
      (commutator_le_centralizer_of_central fun w hw => ?_)
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hVbC (hWV hw))
    rw [← QuotientGroup.eq_one_iff (N := Subgroup.center ↥L)]
    change π (w * u' * w⁻¹ * u'⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  set R : Subgroup ↥L := Qb.comap π ⊓ W with hR
  have hRmap : R.map π = Qb := by
    refine le_antisymm (fun _ ⟨r, hr, hrq⟩ => hrq ▸ hr.1) fun q hq => ?_
    obtain ⟨w, hw, hwq⟩ := (hWmap.symm ▸ hQbV hq : q ∈ W.map π)
    refine ⟨w, Subgroup.mem_inf.mpr ⟨?_, hw⟩, hwq⟩
    show π w ∈ Qb
    rw [hwq]
    exact hq
  let f : ↥R →* ↥Qb := (π.comp R.subtype).codRestrict Qb fun r => by
    rw [← hRmap]
    exact ⟨r, r.2, rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨q, hq⟩
    rw [← hRmap] at hq
    obtain ⟨r, hr, hrq⟩ := hq
    exact ⟨⟨r, hr⟩, Subtype.ext hrq⟩
  obtain ⟨S⟩ : Nonempty (Sylow 3 ↥R) := inferInstance
  have hSmap : (S : Subgroup ↥R).map f = ⊤ := by
    rw [← Sylow.coe_mapSurjective hfs S]
    exact ((Sylow.mapSurjective hfs S).is_maximal' (IsPGroup.to_subgroup hQb3 ⊤) le_top).symm
  set ι : ↥R →* Y := L.subtype.comp R.subtype with hι
  have hιinj : Function.Injective ι :=
    (Subgroup.subtype_injective L).comp (Subgroup.subtype_injective R)
  refine ⟨W.map L.subtype, ?_, by rw [← Subgroup.map_commutator, hW], (S : Subgroup ↥R).map ι,
    ?_, S.isPGroup'.map ι, fun hcyc => hQbnc ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨w.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hWC hw))
  · rintro _ ⟨s, -, rfl⟩
    exact ⟨(s : ↥L), (s.2 : (s : ↥L) ∈ R).2, rfl⟩
  · have e := (S : Subgroup ↥R).equivMapOfInjective ι hιinj
    have : IsCyclic ↥(S : Subgroup ↥R) := isCyclic_of_surjective e.symm.toMonoidHom
      e.symm.surjective
    have : IsCyclic ↥((S : Subgroup ↥R).map f) :=
      isCyclic_of_surjective (f.subgroupMap (S : Subgroup ↥R)) (f.subgroupMap_surjective _)
    rw [hSmap] at this
    exact isCyclic_of_surjective (Subgroup.topEquiv.toMonoidHom) Subgroup.topEquiv.surjective

end ToralCensus

open ToralCensus in
theorem kFactCentNoncycThree_of_group {𝔉 : (X : Type) → [Group X] → Prop}
    (h : ∀ (X : Type) [Group X], 𝔉 X → CentNoncycThreeGroup X) : KFactCentNoncycThree 𝔉 :=
  fun _ _ _ _ _ _ hF _ hu hu3 hnc => centPerfectNoncyc_of_quotient (h _ hF) hu hu3 hnc

open ToralCensus in
theorem fixThreeVoid_of_group {𝔉 : (X : Type) → [Group X] → Prop}
    (h : ∀ (X : Type) [Group X], 𝔉 X → CentNoncycThreeGroup X) : FixThreeVoid 𝔉 :=
  fixThreeVoid_of_centNoncyc (kFactCentNoncycThree_of_group h)

end CFSG.AGLEmbedding

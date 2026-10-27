module

public import CFSG.ClassicalInvolution.RouteD.ConsistencyA
public import CFSG.ClassicalInvolution.Models.Transfer.Linear

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem fundamentalSingleClass_psl {F : Type} [Field F] {k : ℕ} (hk : 2 ≤ k + 1) :
    FundamentalSingleClass .PSL (SpecialLinear.rootDatum k F) := by
  intro R hR R' hR'
  obtain ⟨g, rfl⟩ := (mem_longRootSet_iff hk).mp (fundamentalSubgroups_psl_subset hk hR)
  obtain ⟨g', rfl⟩ := (mem_longRootSet_iff hk).mp (fundamentalSubgroups_psl_subset hk hR')
  refine ⟨g' * g⁻¹, ?_⟩
  show _ = conjSub _ _
  rw [conjSub, Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem fundamentalSingleClass_of_psl {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSL) {k : ℕ}
    (hr : D.rank i = k + 1) (hk : 2 ≤ k + 1) :
    FundamentalSingleClass (D.tag i) (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSL) (hN : n = k + 1) (hE : e = f),
      FundamentalSingleClass t (modelUniv t n p e Fact.out).D := by
    intro t n e hT hN hE
    have hE' : f = e := hE.symm
    subst hT hN hE'
    exact fundamentalSingleClass_psl hk
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  exact key _ _ _ ht hr he

theorem exists_psl_hom {X : Type} [Group X] {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ)
    (i : Fin D.card) (ht : D.tag i = .PSL) {k : ℕ} (hr : D.rank i = k + 1) :
    ∃ ψ : SL(k + 1, GaloisField p f) →* X,
      ψ.ker ≤ Subgroup.center SL(k + 1, GaloisField p f) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups (D.tag i)
          (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)) ↔
        ∃ R ∈ fundamentalSubgroups .PSL (SpecialLinear.rootDatum k (GaloisField p f)),
          K = R.map ψ := by
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSL) (hN : n = k + 1) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X) (hφ : φ.ker ≤ Subgroup.center _),
      ∃ ψ : SL(k + 1, GaloisField p f) →* X,
        ψ.ker ≤ Subgroup.center SL(k + 1, GaloisField p f) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
            K = R.map φ) ↔
          ∃ R ∈ fundamentalSubgroups .PSL (SpecialLinear.rootDatum k (GaloisField p f)),
            K = R.map ψ := by
    intro t n e hT hN hE φ hφ
    have hE' : f = e := hE.symm
    subst hT hN hE'
    exact ⟨φ, hφ, rfl, fun K => Iff.rfl⟩
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  exact key _ _ _ ht hr he (D.hom i) (D.ker_le_center i)

structure ShapeADict (p f m : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (z : G) where
  ψ : SL(m + 1, GaloisField p f) →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center SL(m + 1, GaloisField p f)
  Q₀ : Subgroup (locQuot Ω z)
  commutes : Commutes Q₀ ψ.range
  mem_fam : ∀ (hk : 2 ≤ m + 1), ∀ R ∈ longRootSet (K := GaloisField p f) hk,
    R.map ψ ∈ locFamily Ω z
  fam_cases : ∀ (hk : 2 ≤ m + 1), ∀ K ∈ locFamily Ω z,
    K ≤ Q₀ ∨ ∃ R ∈ longRootSet (K := GaloisField p f) hk, K = R.map ψ
  card_le : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField p f)

theorem LocalShapeA.nonempty_dict {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (h : LocalShapeA p f m Ω z) :
    Nonempty (ShapeADict p f m Ω z) := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  have hk : 2 ≤ m + 1 := by omega
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psl_hom D i₁ ht₁ hr₁
  obtain ⟨ψ₀, hker₀, hrange₀, hfund₀⟩ := exists_psl_hom D i₀ ht₀ (k := 1) hr₀
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  have hsingle := fundamentalSingleClass_of_psl D i₁ ht₁ hr₁ hk
  refine ⟨{
    ψ := ψ₁
    ker_le := hker₁
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro hk' R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ (R.map ψ₁)).mpr
      ⟨R, longRootSet_subset_fundamentalSubgroups_psl hk' hR, rfl⟩
    rw [hRR']
    exact D.map_mem_of_single_class hΦ i₁ hsingle hR'
  · intro hk' K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    have hi := i.isLt
    have hi₀ := i₀.isLt
    have hi₁ := i₁.isLt
    have hne' : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have : i = i₀ ∨ i = i₁ := by
      rcases Nat.lt_or_ge i.val 1 with h1 | h1
      · by_cases h0 : i₀.val = 0
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · by_cases h0 : i₀.val = 1
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
    rcases this with rfl | rfl
    · exact Or.inl (Subgroup.map_le_range _ _)
    · obtain ⟨R', hR', hRR'⟩ := (hfund₁ _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨R', fundamentalSubgroups_psl_subset hk' hR', hRR'⟩
  · show Nat.card (D.hom i₀).range ≤ _
    rw [← hrange₀]
    exact Nat.card_le_card_of_surjective (ψ₀.rangeRestrict) ψ₀.rangeRestrict_surjective


section Members

variable {G : Type} [Group G]

theorem card_map_of_inf_ker_eq_bot {Y Z : Type*} [Group Y] [Group Z] (φ : Y →* Z)
    (A : Subgroup Y) (h : A ⊓ φ.ker = ⊥) : Nat.card (A.map φ) = Nat.card A := by
  have hinj : Function.Injective (φ.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have : (x : Y) ∈ A ⊓ φ.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have h1 : Nat.card (φ.comp A.subtype).range = Nat.card A := Nat.card_range_of_injective hinj
  rwa [MonoidHom.range_comp, Subgroup.range_subtype] at h1

theorem card_locImg [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    {x : G} {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {x}) :
    Nat.card (locImg Ω x L) = Nat.card SL(2, GaloisField p f) := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hLY := le_centralizingLayer hL
  let e := Subgroup.subgroupOfEquivOfLe hLY
  have hO : classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x)) = ⊥ := by
    have h1 : Subgroup.map e.toMonoidHom (classicalInvolutionOddCore (L.subgroupOf (locLayer Ω x))) =
        classicalInvolutionOddCore ↥L := CFSG.ComponentClassification.OddCore.equiv_invariant e
    rw [hex L hL.1] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hinf := inf_oddCore_eq_bot hO
  unfold locImg
  rw [card_map_of_inf_ker_eq_bot _ _ (by rwa [QuotientGroup.ker_mk'])]
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨e'⟩ := hz.nonempty_equiv_sl2 (hex L hL.1)
  exact Nat.card_congr e'.toEquiv


theorem mem_center_of_comm_mem_center {S : Type*} [Group S] [Group.IsPerfect S] {r : S}
    (h : ∀ s : S, ⁅r, s⁆ ∈ Subgroup.center S) : r ∈ Subgroup.center S := by
  let φ : S →* Subgroup.center S :=
    { toFun := fun s => ⟨⁅r, s⁆, h s⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hs := Subgroup.mem_center_iff.mp (h t) s
        simp only [Subgroup.coe_mul, commutatorElement_def]
        calc r * (s * t) * r⁻¹ * (s * t)⁻¹
            = (r * s * r⁻¹ * s⁻¹) * (s * (r * t * r⁻¹ * t⁻¹) * s⁻¹) := by group
          _ = (r * s * r⁻¹ * s⁻¹) * (r * t * r⁻¹ * t⁻¹) := by
            congr 1
            have hs' : s * (r * t * r⁻¹ * t⁻¹) = (r * t * r⁻¹ * t⁻¹) * s := by
              simpa [commutatorElement_def] using hs
            calc s * (r * t * r⁻¹ * t⁻¹) * s⁻¹ = ((r * t * r⁻¹ * t⁻¹) * s) * s⁻¹ := by
                  rw [hs']
              _ = r * t * r⁻¹ * t⁻¹ := by group }
  have hker : commutator S ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [Subgroup.mem_center_iff]
  intro s
  have : s ∈ commutator S := by rw [Group.IsPerfect.commutator_eq_top]; trivial
  have h1 : φ s = 1 := hker this
  have h2 : ⁅r, s⁆ = 1 := congrArg Subtype.val h1
  rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
  exact h2.symm

theorem locImg_self_le_Q₀ [Finite G] {m : ℕ} (hm : 2 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    {Ω : Set (Subgroup G)} {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (d : ShapeADict p f m Ω z) : locImg Ω z K ≤ d.Q₀ := by
  have hk : 2 ≤ m + 1 := by omega
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hmem : locImg Ω z K ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨K, hKz, rfl⟩
  rcases d.fam_cases hk _ hmem with h | ⟨R, hR, hRK⟩
  · exact h
  · exfalso
    let zY : ↥(locLayer Ω z) := ⟨z, le_centralizingLayer hKz hz.mem⟩
    have hzK : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY ∈
        locImg Ω z K := ⟨zY, Subgroup.mem_subgroupOf.mpr hz.mem, rfl⟩
    rw [hRK] at hzK
    obtain ⟨r, hrR, hr⟩ := hzK
    have hcentral : ∀ w : locQuot Ω z,
        w * QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY =
          QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z)) zY * w := by
      intro w
      obtain ⟨w', rfl⟩ := QuotientGroup.mk'_surjective _ w
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (centralizingLayer_le_centralizer Ω {z} w'.2)
    have hrc : r ∈ Subgroup.center SL(m + 1, GaloisField p f) := by
      have := CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le
        (K := GaloisField p f) (n := m + 1) (by omega)
      refine mem_center_of_comm_mem_center fun s => d.ker_le ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, hr]
      rw [commutatorElement_def, ← hcentral (d.ψ s), mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨i, hi⟩ := hR
    have hr1 : r = 1 := by
      have hker : (QuotientGroup.mk' (Subgroup.center SL(m + 1, GaloisField p f))).ker ≤
          Subgroup.center SL(m + 1, GaloisField p f) := by
        rw [QuotientGroup.ker_mk']
      exact Transfer.eq_one_of_mem_ker_of_isLongRootSL2 hodd (by omega) hi hker r hrR
        (by rw [QuotientGroup.ker_mk']; exact hrc)
    rw [hr1, map_one] at hr
    have hO : zY ∈ classicalInvolutionOddCore ↥(locLayer Ω z) :=
      (QuotientGroup.eq_one_iff _).mp hr.symm
    have h2 : orderOf zY = 2 := by
      rw [Subgroup.orderOf_mk]; exact hz.orderOf_eq_two
    have h3 := orderOf_dvd_natCard (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z))
    have h4 : orderOf (⟨zY, hO⟩ : classicalInvolutionOddCore ↥(locLayer Ω z)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact h2
    rw [h4] at h3
    have := (CFSG.ComponentClassification.OddCore.odd_card (↥(locLayer Ω z)))
    exact (Nat.not_even_iff_odd.mpr this) (even_iff_two_dvd.mpr h3)

theorem commutes_locImg_of_commutes {Ω : Set (Subgroup G)} {x : G} {L L' : Subgroup G}
    (h : Commutes L L') : Commutes (locImg Ω x L) (locImg Ω x L') := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h a ha b hb)

theorem commutes_of_commutes_locImg [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) (h : Commutes (locImg Ω x L) (locImg Ω x L')) :
    Commutes L L' := by
  obtain ⟨z, hz⟩ := hΩ.classical L hL.1
  have hperf := (hz.subgroupOf p f (le_centralizingLayer hL)).perfect
  have := commutes_of_commutes_oddQuotient hP1 hperf h
  intro a ha b hb
  exact congrArg Subtype.val (this ⟨a, le_centralizingLayer hL ha⟩ (Subgroup.mem_subgroupOf.mpr ha)
    ⟨b, le_centralizingLayer hL' hb⟩ (Subgroup.mem_subgroupOf.mpr hb))

theorem commutes_iff_locImg [Finite G] {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) :
    Commutes L L' ↔ Commutes (locImg Ω x L) (locImg Ω x L') :=
  ⟨commutes_locImg_of_commutes, commutes_of_commutes_locImg hΩ hP1 hL hL'⟩

theorem eq_of_locImg_le_Q₀ [Finite G] {m : ℕ} (hm : 2 ≤ m)
    (hodd : Odd (Nat.card (GaloisField p f))) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z}) (d : ShapeADict p f m Ω z)
    {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLQ : locImg Ω z L ≤ d.Q₀) : L = K := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  have hKQ := locImg_self_le_Q₀ hm hodd hK hz d
  have hcL := card_locImg hΩ hex hL
  have hcK := card_locImg hΩ hex hKz
  have e1 : locImg Ω z L = d.Q₀ := Subgroup.eq_of_le_of_card_ge hLQ (by rw [hcL]; exact d.card_le)
  have e2 : locImg Ω z K = d.Q₀ := Subgroup.eq_of_le_of_card_ge hKQ (by rw [hcK]; exact d.card_le)
  exact locImg_injOn hΩ hP1 hL hKz (e1.trans e2.symm)

theorem exists_root_of_ne [Finite G] {m : ℕ} (hm : 2 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeADict p f m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    ∃ R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1), locImg Ω z L = R.map d.ψ := by
  have hmem : locImg Ω z L ∈ locFamily Ω z := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  rcases d.fam_cases (by omega) _ hmem with h | h
  · exact absurd (eq_of_locImg_le_Q₀ hm hodd hΩ hex hK hz hP1 d hL h) hLK
  · exact h

theorem exists_member_of_root [Finite G] {m : ℕ} (hm : 2 ≤ m)
    (hodd : Odd (Nat.card (GaloisField p f))) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z)
    (hP1 : LocalOddCentral Ω {z}) (d : ShapeADict p f m Ω z) {R : Subgroup SL(m + 1, GaloisField p f)}
    (hR : R ∈ longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1)) :
    ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = R.map d.ψ := by
  obtain ⟨L, hL, hLR⟩ := mem_locFamily_iff.mp (d.mem_fam (by omega) R hR)
  refine ⟨L, hL, fun hLK => ?_, hLR⟩
  subst hLK
  have h1 : Commutes (locImg Ω z L) (locImg Ω z L) := by
    intro a ha b hb
    have hb' : b ∈ d.ψ.range := by
      rw [hLR] at hb
      obtain ⟨c, _, rfl⟩ := hb
      exact ⟨c, rfl⟩
    exact d.commutes a (locImg_self_le_Q₀ hm hodd hK hz d ha) b hb'
  exact not_commutes_self_of_isClassicalMember hz
    ((commutes_iff_locImg hΩ hP1 hL hL).mpr h1)

theorem commutes_K_of_ne [Finite G] {m : ℕ} (hm : 2 ≤ m) (hodd : Odd (Nat.card (GaloisField p f)))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember p f K z) (hP1 : LocalOddCentral Ω {z})
    (d : ShapeADict p f m Ω z) {L : Subgroup G} (hL : L ∈ centralizingMembers Ω {z}) (hLK : L ≠ K) :
    Commutes K L := by
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, le_centralizer_of_isClassicalMember hz⟩
  obtain ⟨R, hR, hLR⟩ := exists_root_of_ne hm hodd hΩ hex hK hz hP1 d hL hLK
  refine commutes_of_commutes_locImg hΩ hP1 hKz hL ?_
  have := d.commutes
  intro a ha b hb
  rw [hLR] at hb
  exact this a (locImg_self_le_Q₀ hm hodd hK hz d ha) b
    (by obtain ⟨c, _, rfl⟩ := hb; exact ⟨c, rfl⟩)

theorem commutes_of_commutes_map {H X : Type*} [Group H] [Group X] (φ : H →* X)
    (hker : φ.ker ≤ Subgroup.center H) {A B : Subgroup H} (hA : Group.IsPerfect ↥A)
    (hc : Commutes (A.map φ) (B.map φ)) : Commutes A B := by
  intro a ha l hl
  have hcen : ∀ x ∈ A, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.center H := by
    intro x hx
    apply hker
    have h := hc (φ x) ⟨x, hx, rfl⟩ (φ l) ⟨l, hl, rfl⟩
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact h
  let ψ : A →* Subgroup.center H :=
    { toFun := fun x => ⟨x * l * x⁻¹ * l⁻¹, hcen x x.2⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := Subgroup.mem_center_iff.mp (hcen y y.2)
        have hx := Subgroup.mem_center_iff.mp (hcen x x.2)
        have hyl : (y : H) * l * (y : H)⁻¹ = ((y : H) * l * (y : H)⁻¹ * l⁻¹) * l := by group
        calc (((x * y : A) : H) * l * ((x * y : A) : H)⁻¹ * l⁻¹)
            = (x : H) * ((y : H) * l * (y : H)⁻¹) * (x : H)⁻¹ * l⁻¹ := by
              simp only [Subgroup.coe_mul, mul_inv_rev]; group
          _ = (x : H) * (((y : H) * l * (y : H)⁻¹ * l⁻¹) * l) * (x : H)⁻¹ * l⁻¹ := by rw [← hyl]
          _ = ((x : H) * ((y : H) * l * (y : H)⁻¹ * l⁻¹)) * l * (x : H)⁻¹ * l⁻¹ := by group
          _ = (((y : H) * l * (y : H)⁻¹ * l⁻¹) * (x : H)) * l * (x : H)⁻¹ * l⁻¹ := by
              rw [hy (x : H)]
          _ = ((y : H) * l * (y : H)⁻¹ * l⁻¹) * ((x : H) * l * (x : H)⁻¹ * l⁻¹) := by group
          _ = ((x : H) * l * (x : H)⁻¹ * l⁻¹) * ((y : H) * l * (y : H)⁻¹ * l⁻¹) :=
              hx ((y : H) * l * (y : H)⁻¹ * l⁻¹) }
  have hker' : commutator A ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
  have hmem : (⟨a, ha⟩ : A) ∈ ψ.ker := hker' (by rw [hA.1]; exact Subgroup.mem_top _)
  have h1 : a * l * a⁻¹ * l⁻¹ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hmem)
  calc a * l = a * l * a⁻¹ * l⁻¹ * l * a := by group
    _ = l * a := by rw [h1]; group

end Members

end CFSG.ClassicalInvolution.RouteD

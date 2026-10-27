module

public import CFSG.ClassicalInvolution.Q3.Q3KBSigma
public import CFSG.ClassicalInvolution.Q3.Q3KBLie
public import CFSG.ClassicalInvolution.Q3.Q3KBPair
public import CFSG.ClassicalInvolution.Q3.Q3Y2Lift
public import CFSG.ClassicalInvolution.Q3.Q3YAbs
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification
open scoped commutatorElement

section Step

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commutes_image_of_mem_inf_centralizer (hΩ : ConjInvariant Ω)
    (hO : LocalOddCentralizer3 Ω) {A : Subgroup G} (hA : IsElemAbelian 2 A) {a : G}
    (haA : a ∈ A) (hnc : a ∉ Subgroup.center G) (hAY : A ≤ centralizingLayer Ω {a})
    {F₀ : Subgroup G} (hF₀A : F₀ ≤ A) {d : OddQuot a} (hd : d ∈ deltaCore (modOdd a F₀)) {f : G}
    (hfF : f ∈ F₀) (hf1 : f ≠ 1) {g : G}
    (hg : g ∈ centralizingLayer Ω {a} ⊓ Subgroup.centralizer ({f} : Set G))
    (hgC : g ∈ Subgroup.centralizer ({a} : Set G)) :
    oddQuotMk a ⟨g, hgC⟩ * d = d * oddQuotMk a ⟨g, hgC⟩ := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hfA : f ∈ A := hF₀A hfF
  have hf2 : f * f = 1 := Q3C.elem_sq hA hfA
  have hfC : f ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (Q3C.elem_comm hA hfA haA)
  have hf'2 : (⟨f, hfC⟩ : ↥C) * ⟨f, hfC⟩ = 1 := Subtype.ext hf2
  have hfb : oddQuotMk a ⟨f, hfC⟩ ∈ modOdd a F₀ := oddQuotMk_mem_modOdd hfF hfC
  have hfb1 : oddQuotMk a ⟨f, hfC⟩ ≠ 1 := fun h =>
    hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hf'2 h))
  have hdf : d ∈ oddCoreIn (Subgroup.centralizer ({oddQuotMk a ⟨f, hfC⟩} : Set (OddQuot a))) :=
    mem_deltaCore_iff.mp hd _ hfb hfb1
  obtain ⟨R, hRf, hRodd, hRn, d₀, hd₀R, hd₀⟩ := exists_odd_normalized_lift
    (N := componentClassificationOddCore ↥C) (OddCore.odd_card _)
    (isPGroup_zpowers_of_sq hf'2) hdf
  have hR'a : R.map C.subtype ≤ Subgroup.centralizer ({a} : Set G) := Subgroup.map_subtype_le R
  have hR'f : R.map C.subtype ≤ Subgroup.centralizer ({f} : Set G) := by
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hRf hr)))
  have hR'odd : Odd (Nat.card (R.map C.subtype)) := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hRodd
  have hR'n : ∀ u ∈ Subgroup.centralizer ({f} : Set G), u ∈ Subgroup.centralizer ({a} : Set G) →
      ∀ x ∈ R.map C.subtype, u * x * u⁻¹ ∈ R.map C.subtype := by
    intro u huf hua x hx
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨⟨u, hua⟩ * r * ⟨u, hua⟩⁻¹, hRn ⟨u, hua⟩ ?_ r hr, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp huf))
  obtain ⟨c, hcN, hcg⟩ := commutator_mem_involutionOddCore_of_odd_normalized hΩ hO hnc
    (hAY hfA) (orderOf_eq_prime (by rw [pow_two]; exact hf2) hf1) hR'f hR'a hR'odd hR'n
    (r := (d₀ : G)) (g := g) ⟨d₀, hd₀R, rfl⟩ hg
  have hc : c = ⁅d₀, (⟨g, hgC⟩ : ↥C)⁆ := Subtype.ext hcg
  have h1 : oddQuotMk a ⁅d₀, (⟨g, hgC⟩ : ↥C)⁆ = 1 := oddQuotMk_eq_one_iff.mpr (hc ▸ hcN)
  rw [map_commutatorElement] at h1
  change ⁅QuotientGroup.mk' _ d₀, oddQuotMk a ⟨g, hgC⟩⁆ = 1 at h1
  rw [hd₀] at h1
  exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem mem_or_mul_mem_of_card {A F₀ : Subgroup G} (hF₀A : F₀ ≤ A)
    (hcard : Nat.card A = 2 * Nat.card F₀) {a : G} (haA : a ∈ A) (haF : a ∉ F₀) {x : G}
    (hx : x ∈ A) : x ∈ F₀ ∨ x * a ∈ F₀ := by
  set H : Subgroup ↥A := F₀.subgroupOf A with hH
  have hHcard : Nat.card H = Nat.card F₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF₀A).toEquiv
  have hpos : 0 < Nat.card F₀ := Nat.card_pos
  have hindex : H.index = 2 := by
    have h := Subgroup.card_mul_index H
    rw [hHcard, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)
  have key := (Subgroup.mul_mem_iff_of_index_two hindex (a := ⟨x, hx⟩) (b := ⟨a, haA⟩))
  have haH : (⟨a, haA⟩ : ↥A) ∉ H := fun h => haF (Subgroup.mem_subgroupOf.mp h)
  by_cases hxF : x ∈ F₀
  · exact Or.inl hxF
  · right
    have hxH : (⟨x, hx⟩ : ↥A) ∉ H := fun h => hxF (Subgroup.mem_subgroupOf.mp h)
    have : (⟨x, hx⟩ : ↥A) * ⟨a, haA⟩ ∈ H := key.mpr (by simp [hxH, haH])
    exact Subgroup.mem_subgroupOf.mp this


theorem commutes_of_centralizes_bar (hΩ : ConjInvariant Ω) (hO : LocalOddCentralizer3 Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) {a : G} (haA : a ∈ A)
    (hnc : a ∉ Subgroup.center G) (hAY : A ≤ centralizingLayer Ω {a}) {F₀ : Subgroup G}
    (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A) (haF : a ∉ F₀) {d : OddQuot a}
    (hd : d ∈ deltaCore (modOdd a F₀)) {u : G} (huA : u ∈ A) (hu1 : u ≠ 1) (hua : u ≠ a)
    (hu2 : u * u = 1)
    {q : ↥(centralizingLayer Ω {a}) ⧸ classicalInvolutionOddCore ↥(centralizingLayer Ω {a})}
    (hq : QuotientGroup.mk' (classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
        ⟨u, hAY huA⟩ * q = q * QuotientGroup.mk'
          (classicalInvolutionOddCore ↥(centralizingLayer Ω {a})) ⟨u, hAY huA⟩) :
    layerQuotientHom hΩ a q * d = d * layerQuotientHom hΩ a q := by
  obtain ⟨hF₀A, hF₀card⟩ := hF₀
  have hF₀4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hcard : Nat.card A = 2 * Nat.card F₀ := by rw [hA8, hF₀4]
  obtain ⟨y, hyu, hyq⟩ := Q3Y2.centralizer_mk_le (centralizingLayer Ω {a}) (hAY huA) hu2 hq
  have hyY : (y : G) ∈ centralizingLayer Ω {a} := y.2
  have hyC : (y : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    centralizingLayer_le_centralizer Ω {a} hyY
  have hθ : layerQuotientHom hΩ a q = oddQuotMk a ⟨y, hyC⟩ := by
    rw [← hyq]
    rfl
  rw [hθ]
  rcases mem_or_mul_mem_of_card hF₀A hcard haA haF huA with hF | hF
  · exact commutes_image_of_mem_inf_centralizer hΩ hO hA haA hnc hAY hF₀A hd hF hu1
      ⟨hyY, Subgroup.mem_centralizer_singleton_iff.mpr hyu⟩ hyC
  · have hfa1 : u * a ≠ 1 := by
      intro h
      apply hua
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_eq_of_mul_eq_one_right (Q3C.elem_sq hA haA)
    refine commutes_image_of_mem_inf_centralizer hΩ hO hA haA hnc hAY hF₀A hd hF hfa1
      ⟨hyY, ?_⟩ hyC
    have hya : (y : G) * a = a * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (y : G) * (u * a) = ((y : G) * u) * a := by group
      _ = (u * y) * a := by rw [hyu]
      _ = u * ((y : G) * a) := by group
      _ = u * (a * y) := by rw [hya]
      _ = (u * a) * y := by group

end Step

section Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure MemberPair (Ω : Set (Subgroup G)) (A K K' : Subgroup G) (w w' : G) : Prop where
  memΩ : K ∈ Ω
  memΩ' : K' ∈ Ω
  le : K ≤ Subgroup.centralizer (A : Set G)
  le' : K' ≤ Subgroup.centralizer (A : Set G)
  mem : w ∈ K
  mem' : w' ∈ K'
  memA : w ∈ A
  memA' : w' ∈ A
  central : ∀ k ∈ K, k * w = w * k
  central' : ∀ k ∈ K', k * w' = w' * k
  comm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x
  sq : w * w = 1
  sq' : w' * w' = 1
  ne : w ≠ w'
  ne_one : w ≠ 1
  ne_one' : w' ≠ 1


theorem commutes_component_of_pair (hΩ : InClass3 Ω) (hO : LocalOddCentralizer3 Ω)
    {A : Subgroup G} (hA : IsElemAbelian 2 A) (hA8 : Nat.card A = 8) {a : G} (haA : a ∈ A)
    (hnc : a ∉ Subgroup.center G) (hAY : A ≤ centralizingLayer Ω {a}) {F₀ : Subgroup G}
    (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 A) (haF : a ∉ F₀) {d : OddQuot a}
    (hd : d ∈ deltaCore (modOdd a F₀)) {ι : Type}
    (D : LieSystemData3 ι (↥(centralizingLayer Ω {a}) ⧸
      classicalInvolutionOddCore ↥(centralizingLayer Ω {a}))
      (oddQuotientFamily (restrictFamily (centralizingMembers Ω {a})
        (centralizingLayer Ω {a}))))
    {k : ι} (hk : D.kind k ≠ CompData.sl23) {K K' : Subgroup G} {w w' : G}
    (P : MemberPair Ω A K K' w w') (hwa : w ≠ a) (hw'a : w' ≠ a) (hww' : w * w' ≠ a)
    (hfaith : ∀ f ∈ A, f ≠ 1 → f ≠ a → ∀ hfC : f ∈ Subgroup.centralizer ({a} : Set G),
      ¬ ∀ x ∈ ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom k)).range,
        oddQuotMk a ⟨f, hfC⟩ * x = x * oddQuotMk a ⟨f, hfC⟩) :
    ∀ x ∈ ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom k)).range, x * d = d * x := by
  let Y : Subgroup G := centralizingLayer Ω {a}
  set θ := layerQuotientHom hΩ.conjInvariant a with hθ
  have hYC : Y ≤ Subgroup.centralizer ({a} : Set G) := centralizingLayer_le_centralizer Ω {a}
  have hbc : ∀ {M : Subgroup G}, M ≤ Subgroup.centralizer (A : Set G) →
      M ≤ Subgroup.centralizer ({a} : Set G) := fun hM =>
    hM.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
  have hmK : K ∈ centralizingMembers Ω {a} := ⟨P.memΩ, hbc P.le⟩
  have hmK' : K' ∈ centralizingMembers Ω {a} := ⟨P.memΩ', hbc P.le'⟩
  have hKY : K ≤ Y := le_centralizingLayer hmK
  have hK'Y : K' ≤ Y := le_centralizingLayer hmK'
  have hwY : w ∈ Y := hKY P.mem
  have hw'Y : w' ∈ Y := hK'Y P.mem'
  have hwwY : w * w' ∈ Y := Y.mul_mem hwY hw'Y
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hΦ : ∀ {M : Subgroup G}, M ∈ centralizingMembers Ω {a} →
      modOddIn Y M ∈ oddQuotientFamily (restrictFamily (centralizingMembers Ω {a}) Y) :=
    fun {M} hM => ⟨M.subgroupOf Y, ⟨M, hM, le_centralizingLayer hM, rfl⟩, rfl⟩
  have hww : w * w' = w' * w := P.comm w P.mem w' P.mem'
  have hsqww : (w * w') * (w * w') = 1 := by
    calc (w * w') * (w * w') = w * (w' * w) * w' := by group
      _ = w * (w * w') * w' := by rw [← hww]
      _ = (w * w) * (w' * w') := by group
      _ = 1 := by rw [P.sq, P.sq', one_mul]
  have hww1 : w * w' ≠ 1 := fun h => P.ne (by
    have h' : w' = w⁻¹ := eq_inv_of_mul_eq_one_right h
    exact (h'.trans (inv_eq_of_mul_eq_one_right P.sq)).symm)
  have hζmem : π ⟨w, hwY⟩ ∈ modOddIn Y K :=
    ⟨⟨w, hwY⟩, Subgroup.mem_subgroupOf.mpr P.mem, rfl⟩
  have hξmem : π ⟨w', hw'Y⟩ ∈ modOddIn Y K' :=
    ⟨⟨w', hw'Y⟩, Subgroup.mem_subgroupOf.mpr P.mem', rfl⟩
  have hζ2 : π ⟨w, hwY⟩ * π ⟨w, hwY⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w, hwY⟩ : ↥Y) * ⟨w, hwY⟩ = 1 := Subtype.ext P.sq
    rw [this, map_one]
  have hξ2 : π ⟨w', hw'Y⟩ * π ⟨w', hw'Y⟩ = 1 := by
    rw [← map_mul]
    have : (⟨w', hw'Y⟩ : ↥Y) * ⟨w', hw'Y⟩ = 1 := Subtype.ext P.sq'
    rw [this, map_one]
  have hζ1 : π ⟨w, hwY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hwY P.sq P.ne_one
  have hξ1 : π ⟨w', hw'Y⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hw'Y P.sq' P.ne_one'
  have hmul : π ⟨w * w', hwwY⟩ = π ⟨w, hwY⟩ * π ⟨w', hw'Y⟩ := by
    rw [← map_mul]
    rfl
  have hζξ : π ⟨w, hwY⟩ ≠ π ⟨w', hw'Y⟩ := by
    intro h
    apply Q3Y.mk_ne_one_of_involution Y hwwY hsqww hww1
    rw [hmul, ← h, hζ2]
  have hKK' : ∀ y ∈ modOddIn Y K, ∀ y' ∈ modOddIn Y K', y * y' = y' * y := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.comm x (Subgroup.mem_subgroupOf.mp hx) x'
      (Subgroup.mem_subgroupOf.mp hx'))
  have hζc : ∀ y ∈ modOddIn Y K, π ⟨w, hwY⟩ * y = y * π ⟨w, hwY⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central x (Subgroup.mem_subgroupOf.mp hx)).symm
  have hξc : ∀ y ∈ modOddIn Y K', π ⟨w', hw'Y⟩ * y = y * π ⟨w', hw'Y⟩ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (P.central' x (Subgroup.mem_subgroupOf.mp hx)).symm
  have hnc_of : ∀ (f : G) (hfA : f ∈ A) (hf1 : f ≠ 1) (hfa : f ≠ a) (hfY : f ∈ Y),
      ¬ ∀ q ∈ (D.hom k).range, π ⟨f, hfY⟩ * q = q * π ⟨f, hfY⟩ := by
    intro f hfA hf1 hfa hfY hall
    refine hfaith f hfA hf1 hfa (hYC hfY) ?_
    rintro _ ⟨y, rfl⟩
    have := congrArg θ (hall (D.hom k y) ⟨y, rfl⟩)
    exact (map_mul θ _ _).symm.trans (this.trans (map_mul θ _ _))
  have hrange := range_le_of_pair D hk (hΦ hmK) (hΦ hmK') hζmem hξmem hζ2 hξ2 hζ1 hξ1 hζξ hKK'
    hζc hξc (hnc_of w P.memA P.ne_one hwa hwY) (hnc_of w' P.memA' P.ne_one' hw'a hw'Y)
  have hcentD : ∀ (u : G) (huA : u ∈ A), u ≠ 1 → u ≠ a → u * u = 1 → ∀ (q : ↥Y ⧸
      classicalInvolutionOddCore ↥Y), π ⟨u, hAY huA⟩ * q = q * π ⟨u, hAY huA⟩ →
        θ q * d = d * θ q := fun u huA hu1 hua hu2 q hq =>
    commutes_of_centralizes_bar hΩ.conjInvariant hO hA hA8 haA hnc hAY hF₀ haF hd huA hu1 hua
      hu2 hq
  have hsub : (D.hom k).range ≤ (Subgroup.centralizer ({d} : Set (OddQuot a))).comap θ := by
    refine hrange.trans (sup_le (sup_le ?_ ?_) ?_)
    · rintro q ⟨hq, -⟩
      have hq' := Subgroup.mem_centralizer_singleton_iff.mp hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcentD w P.memA P.ne_one hwa P.sq q hq'.symm)
    · rintro q ⟨hq, -⟩
      have hq' := Subgroup.mem_centralizer_singleton_iff.mp hq
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcentD w' P.memA' P.ne_one' hw'a P.sq' q hq'.symm)
    · rintro q ⟨hq, -⟩
      have hq' := Subgroup.mem_centralizer_singleton_iff.mp hq
      rw [← hmul] at hq'
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hcentD (w * w') (A.mul_mem P.memA P.memA') hww1 hww' hsqww q hq'.symm)
  intro x hx
  obtain ⟨q, rfl⟩ := hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsub ⟨q, rfl⟩)

end Pair

section Triple

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


theorem deltaCore_modOdd_eq_bot_of_exactTriple (hΩ : InClass3 Ω) (hIH : LocalLieSystems3 Ω)
    {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G} (T : ExactTriple K₁ K₂ K₃ z₁ z₂ z₃)
    (hind : z₁ * z₂ ≠ z₃) (hΩ₁ : K₁ ∈ Ω) (hΩ₂ : K₂ ∈ Ω) (hΩ₃ : K₃ ∈ Ω) {a : G}
    (ha : a ∈ T.group) (ha1 : a ≠ 1) (hnc : a ∉ Subgroup.center G) {F₀ : Subgroup G}
    (hF₀ : F₀ ∈ signalizerFunctorEk 2 2 T.group) : deltaCore (modOdd a F₀) = ⊥ := by
  classical
  have hO : LocalOddCentralizer3 Ω :=
    localOddCentralizer3_of_lieSystem lieSystemOddCentralizer3_proved hIH
  have hA := T.isElemAbelian
  have hA8 := T.card_eq_eight hind
  have hAY : T.group ≤ centralizingLayer Ω {a} :=
    group_le_centralizingLayer_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha
  have hF₀' := hF₀
  obtain ⟨hF₀E, hF₀card⟩ := hF₀
  have h4 : Nat.card F₀ = 4 := by rw [hF₀card]; norm_num
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact T.comm_of_mem (hF₀E hf) ha
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => by
    rw [← pow_two]
    exact hA.2 f (hF₀E hf)
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have ha2 : a * a = 1 := Q3C.elem_sq hA ha
  have hz₁A : z₁ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₂A : z₂ ∈ T.group := Subgroup.subset_closure (by simp)
  have hz₃A : z₃ ∈ T.group := Subgroup.subset_closure (by simp)
  have P12 : MemberPair Ω T.group K₁ K₂ z₁ z₂ :=
    ⟨hΩ₁, hΩ₂, T.le_centralizer₁, T.le_centralizer₂, T.mem₁, T.mem₂, hz₁A, hz₂A, T.central₁,
      T.central₂, T.comm₁₂, T.sq₁, T.sq₂, T.ne₁₂, T.ne_one₁, T.ne_one₂⟩
  have P13 : MemberPair Ω T.group K₁ K₃ z₁ z₃ :=
    ⟨hΩ₁, hΩ₃, T.le_centralizer₁, T.le_centralizer₃, T.mem₁, T.mem₃, hz₁A, hz₃A, T.central₁,
      T.central₃, T.comm₁₃, T.sq₁, T.sq₃, T.ne₁₃, T.ne_one₁, T.ne_one₃⟩
  have P23 : MemberPair Ω T.group K₂ K₃ z₂ z₃ :=
    ⟨hΩ₂, hΩ₃, T.le_centralizer₂, T.le_centralizer₃, T.mem₂, T.mem₃, hz₂A, hz₃A, T.central₂,
      T.central₃, T.comm₂₃, T.sq₂, T.sq₃, T.ne₂₃, T.ne_one₂, T.ne_one₃⟩
  have h23 : z₂ * z₃ ≠ z₁ := by
    intro h
    apply hind
    calc z₁ * z₂ = z₂ * z₁ := T.comm₁₂'
      _ = z₂ * (z₂ * z₃) := by rw [h]
      _ = (z₂ * z₂) * z₃ := by group
      _ = z₃ := by rw [T.sq₂, one_mul]
  have h13 : z₁ * z₃ ≠ z₂ := by
    intro h
    apply hind
    calc z₁ * z₂ = z₁ * (z₁ * z₃) := by rw [h]
      _ = (z₁ * z₁) * z₃ := by group
      _ = z₃ := by rw [T.sq₁, one_mul]
  refine deltaCore_eq_bot_of_faithful_centralized (pPrimeCore_oddQuot_eq_bot a) ?_ ?_ ?_
  · rw [card_modOdd_of_exponent_two hFC hF2, h4]
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F₀ := hx
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hF2 _ hx')
    rw [this, map_one]
  · intro L hL _ hfaith d hd _ x hx
    obtain ⟨ι, -, ⟨D⟩⟩ := hIH {a} (fun h => hnc (h rfl))
    rcases component_cases hΩ D hL with hfree | ⟨k, hLk, hkne⟩
    · exfalso
      obtain ⟨f, hf, hf1, hfc⟩ :=
        exists_mem_ne_one_centralizes_of_exactTriple T hΩ₁ hΩ₂ hΩ₃ ha hF₀E h4 (Or.inl hfree)
      exact hfaith f hf hf1 hfc
    · subst hLk
      have haF : a ∉ F₀ := by
        intro haF
        have hfb1 : oddQuotMk a ⟨a, haC⟩ ≠ 1 := fun h =>
          ha1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext ha2) h))
        exact hfaith (oddQuotMk a ⟨a, haC⟩) (oddQuotMk_mem_modOdd haF haC) hfb1
          (fun y _ => oddQuotMk_central haC y)
      have hcard : Nat.card T.group = 2 * Nat.card F₀ := by rw [hA8, h4]
      have hfaith' : ∀ f ∈ T.group, f ≠ 1 → f ≠ a →
          ∀ hfC : f ∈ Subgroup.centralizer ({a} : Set G),
            ¬ ∀ y ∈ ((layerQuotientHom hΩ.conjInvariant a).comp (D.hom k)).range,
              oddQuotMk a ⟨f, hfC⟩ * y = y * oddQuotMk a ⟨f, hfC⟩ := by
        intro f hfA hf1 hfa hfC hall
        have hf2 : f * f = 1 := Q3C.elem_sq hA hfA
        rcases mem_or_mul_mem_of_card hF₀E hcard ha haF hfA with hF | hF
        · have hfb1 : oddQuotMk a ⟨f, hfC⟩ ≠ 1 := fun h =>
            hf1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext hf2) h))
          exact hfaith _ (oddQuotMk_mem_modOdd hF hfC) hfb1 hall
        · have hfaC : f * a ∈ Subgroup.centralizer ({a} : Set G) :=
            Subgroup.mem_centralizer_singleton_iff.mpr (by
              have hc : f * a = a * f := Q3C.elem_comm hA hfA ha
              calc (f * a) * a = (a * f) * a := by rw [hc]
                _ = a * (f * a) := by group)
          have hfa1 : f * a ≠ 1 := by
            intro h
            apply hfa
            rw [eq_inv_of_mul_eq_one_left h]
            exact inv_eq_of_mul_eq_one_right ha2
          have hfb1 : oddQuotMk a ⟨f * a, hfaC⟩ ≠ 1 := fun h =>
            hfa1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one
              (Subtype.ext (Q3C.elem_sq hA (T.group.mul_mem hfA ha))) h))
          refine hfaith _ (oddQuotMk_mem_modOdd hF hfaC) hfb1 ?_
          intro y hy
          have hmul : oddQuotMk a ⟨f * a, hfaC⟩ =
              oddQuotMk a ⟨f, hfC⟩ * oddQuotMk a ⟨a, haC⟩ := by
            rw [← map_mul]
            rfl
          rw [hmul]
          calc (oddQuotMk a ⟨f, hfC⟩ * oddQuotMk a ⟨a, haC⟩) * y
              = oddQuotMk a ⟨f, hfC⟩ * (oddQuotMk a ⟨a, haC⟩ * y) := mul_assoc _ _ _
            _ = oddQuotMk a ⟨f, hfC⟩ * (y * oddQuotMk a ⟨a, haC⟩) := by
              rw [oddQuotMk_central haC y]
            _ = (oddQuotMk a ⟨f, hfC⟩ * y) * oddQuotMk a ⟨a, haC⟩ := (mul_assoc _ _ _).symm
            _ = (y * oddQuotMk a ⟨f, hfC⟩) * oddQuotMk a ⟨a, haC⟩ := by rw [hall y hy]
            _ = y * (oddQuotMk a ⟨f, hfC⟩ * oddQuotMk a ⟨a, haC⟩) := mul_assoc _ _ _
      have key : ∀ {M M' : Subgroup G} {w w' : G}, MemberPair Ω T.group M M' w w' → w ≠ a →
          w' ≠ a → w * w' ≠ a → d * x = x * d := fun P hwa hw'a hww' =>
        (commutes_component_of_pair hΩ hO hA hA8 ha hnc hAY hF₀' haF hd D hkne P hwa hw'a hww'
          hfaith' x hx).symm
      by_cases e1 : a = z₁
      · exact key P23 (by rw [e1]; exact T.ne₁₂.symm) (by rw [e1]; exact T.ne₁₃.symm)
          (by rw [e1]; exact h23)
      by_cases e2 : a = z₂
      · exact key P13 (by rw [e2]; exact T.ne₁₂) (by rw [e2]; exact T.ne₂₃.symm)
          (by rw [e2]; exact h13)
      by_cases e3 : a = z₃
      · exact key P12 (by rw [e3]; exact T.ne₁₃) (by rw [e3]; exact T.ne₂₃)
          (by rw [e3]; exact hind)
      by_cases e4 : a = z₁ * z₂
      · exact key P13 (Ne.symm e1) (Ne.symm e3) (by
          rw [e4]
          intro h
          exact T.ne₂₃ (mul_left_cancel h).symm)
      · exact key P12 (Ne.symm e1) (Ne.symm e2) (Ne.symm e4)

end Triple

end CFSG.ClassicalInvolution.Q3.Q3KB

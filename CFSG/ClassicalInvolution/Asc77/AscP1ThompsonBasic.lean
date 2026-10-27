module

public import CFSG.ClassicalInvolution.Asc77.WP2Thompson
public import CFSG.ClassicalInvolution.Asc77.AscL62Final
public import CFSG.ClassicalInvolution.Asc77.AscP1Thompson3T

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace Thompson

variable {G : Type} [Group G]

theorem oddCoreOf_conjSub_eq (g : G) (J : Subgroup G) :
    oddCoreOf (conjSub g J) = conjSub g (oddCoreOf J) := by
  let e : ↥J ≃* ↥(conjSub g J) :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hinv : (classicalInvolutionOddCore ↥J).map e.toMonoidHom =
      classicalInvolutionOddCore ↥(conjSub g J) :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  have hcoe : ∀ j : ↥J, ((e j : ↥(conjSub g J)) : G) = g * (j : G) * g⁻¹ := fun j => rfl
  ext y
  constructor
  · intro hy
    obtain ⟨hyC, hyO⟩ := mem_oddCoreOf_iff.mp hy
    rw [← hinv] at hyO
    obtain ⟨j, hj, hje⟩ := hyO
    have h1 : g * (j : G) * g⁻¹ = y := by
      have hje' : e j = ⟨y, hyC⟩ := hje
      have := congrArg Subtype.val hje'
      rw [hcoe] at this
      exact this
    rw [mem_conjSub_iff]
    have h2 : g⁻¹ * y * g = (j : G) := by rw [← h1]; group
    rw [h2]
    exact mem_oddCoreOf_iff.mpr ⟨j.2, hj⟩
  · intro hy
    rw [mem_conjSub_iff] at hy
    obtain ⟨hjJ, hjO⟩ := mem_oddCoreOf_iff.mp hy
    have h1 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    have hyC : y ∈ conjSub g J := by
      rw [← h1]
      exact conj_mem_conjSub hjJ
    refine mem_oddCoreOf_iff.mpr ⟨hyC, ?_⟩
    rw [← hinv]
    refine ⟨⟨g⁻¹ * y * g, hjJ⟩, hjO, Subtype.ext ?_⟩
    show ((e ⟨g⁻¹ * y * g, hjJ⟩ : ↥(conjSub g J)) : G) = y
    rw [hcoe]
    exact h1

theorem conj_mem_centralizer {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) {x : G}
    (hx : x ∈ Subgroup.centralizer (W : Set G)) :
    n * x * n⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro w hw
  have hw' : n⁻¹ * w * n ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) w).mp hw
    simpa using this
  have h1 := hx _ hw'
  calc w * (n * x * n⁻¹) = n * ((n⁻¹ * w * n) * x) * n⁻¹ := by group
    _ = n * (x * (n⁻¹ * w * n)) * n⁻¹ := by rw [h1]
    _ = n * x * n⁻¹ * w := by group

theorem conjSub_centralizer_eq {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) :
    conjSub n (Subgroup.centralizer (W : Set G)) = Subgroup.centralizer (W : Set G) := by
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := conj_mem_centralizer hn hx
    simpa [mul_assoc] using this
  · intro hx
    have := conj_mem_centralizer (Subgroup.inv_mem _ hn) hx
    simpa [mul_assoc] using this

theorem normalizer_le_normalizer_OCW (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (OCW W : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_conjSub_eq]
  unfold OCW
  rw [← oddCoreOf_conjSub_eq, conjSub_centralizer_eq hn]

theorem conjSub_sup (g : G) (A B : Subgroup G) :
    conjSub g (A ⊔ B) = conjSub g A ⊔ conjSub g B :=
  Subgroup.map_sup _ _ _

theorem normalizer_le_normalizer_sup (W : Subgroup G) :
    Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff_conjSub_eq, conjSub_sup, mem_normalizer_iff_conjSub_eq.mp hn,
    mem_normalizer_iff_conjSub_eq.mp (normalizer_le_normalizer_OCW W hn)]

theorem OCW_le_centralizer (W : Subgroup G) : OCW W ≤ Subgroup.centralizer (W : Set G) :=
  oddCoreOf_le_self _

theorem OCW_le_normalizer (W : Subgroup G) : OCW W ≤ Subgroup.normalizer (W : Set G) :=
  (OCW_le_centralizer W).trans (Subgroup.centralizer_le_normalizer _)

theorem le_normalizer_sup (W : Subgroup G) :
    W ⊔ OCW W ≤ Subgroup.normalizer (W : Set G) :=
  sup_le (Subgroup.le_normalizer) (OCW_le_normalizer W)

theorem relIndex_eq_two_of_card {R U : Subgroup G} [Finite G] (hUR : U ≤ R)
    (hcard : Nat.card R = 2 * Nat.card U) : U.relIndex R = 2 := by
  have h := Subgroup.relIndex_mul_card (H := U) (K := R)
  rw [inf_eq_left.mpr hUR] at h
  have hpos : 0 < Nat.card U := Nat.card_pos
  have : (U.relIndex R) * Nat.card U = 2 * Nat.card U := by rw [hcard] at h; rw [h]
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem sq_mem_of_card_eq_two_mul {R U : Subgroup G} [Finite G] (hUR : U ≤ R)
    (hcard : Nat.card R = 2 * Nat.card U) {r : G} (hr : r ∈ R) : r * r ∈ U := by
  have h2 : (U.subgroupOf R).index = 2 := relIndex_eq_two_of_card hUR hcard
  have : (U.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two h2
  have := Subgroup.pow_index_mem (U.subgroupOf R) (⟨r, hr⟩ : ↥R)
  rw [h2, pow_two] at this
  exact this

theorem inv_mul_mem_of_card_eq_two_mul {R U : Subgroup G} [Finite G] (hUR : U ≤ R)
    (hcard : Nat.card R = 2 * Nat.card U) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R) (hrU : r ∉ U)
    (hr'U : r' ∉ U) : r⁻¹ * r' ∈ U := by
  have h2 : (U.subgroupOf R).index = 2 := relIndex_eq_two_of_card hUR hcard
  have hN : (U.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two h2
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp h2
  have h1 : (⟨r, hr⟩ : ↥R) * a ∈ U.subgroupOf R := by
    have := ha ⟨r, hr⟩
    rcases this with ⟨h, -⟩ | ⟨hb, -⟩
    · exact h
    · exact absurd hb hrU
  have h1' : (⟨r', hr'⟩ : ↥R) * a ∈ U.subgroupOf R := by
    have := ha ⟨r', hr'⟩
    rcases this with ⟨h, -⟩ | ⟨hb, -⟩
    · exact h
    · exact absurd hb hr'U
  have h3 : ((⟨r, hr⟩ : ↥R) * a)⁻¹ * ((⟨r', hr'⟩ : ↥R) * a) ∈ U.subgroupOf R :=
    (U.subgroupOf R).mul_mem ((U.subgroupOf R).inv_mem h1) h1'
  have h4 : (⟨r, hr⟩ : ↥R)⁻¹ * ⟨r', hr'⟩ ∈ U.subgroupOf R := by
    have := hN.conj_mem _ h3 a
    have e : a * (((⟨r, hr⟩ : ↥R) * a)⁻¹ * ((⟨r', hr'⟩ : ↥R) * a)) * a⁻¹ =
        (⟨r, hr⟩ : ↥R)⁻¹ * ⟨r', hr'⟩ := by group
    rwa [e] at this
  exact h4

section Members

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem exists_sylow_ge_of_mem_WSet {W : Subgroup G} (hW : W ∈ WSet Ω) :
    ∃ S : Sylow 2 G, W ≤ (S : Subgroup G) := by
  obtain ⟨η, ⟨S, hη, -⟩, rfl⟩ := hW
  exact ⟨S, iSup₂_le fun U hU => (hη.1 hU).2⟩

theorem isPGroup_of_mem_WSet [Finite G] {W : Subgroup G} (hW : W ∈ WSet Ω) : IsPGroup 2 W := by
  obtain ⟨S, hS⟩ := exists_sylow_ge_of_mem_WSet hW
  exact S.isPGroup'.to_le hS

theorem inf_W_of_mem_D [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω)
    (hRK : IsSylow2In R K) :
    R ⊓ W = K ⊓ W ∧ K ⊓ W ∈ USet Ω ∧ IsCyclic ↥(R ⊓ W) ∧ 4 ≤ Nat.card ↥(R ⊓ W) ∧
      Nat.card R = 2 * Nat.card ↥(R ⊓ W) := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := hW
  have hRW2 : IsPGroup 2 ↥(R ⊔ W) := hRK.2.1.to_sup_of_normal_right' hW2 hR.2
  obtain ⟨S', hS'⟩ := hRW2.exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hηS : ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS'
  have hR8 : 8 ≤ Nat.card R := hΩ.eight_le_of_mem_RSet hp (mem_RSet_of_isSylow2In hK hRK)
  have hRle : R ≤ K ⊓ (S' : Subgroup G) := le_inf hRK.1 hRS'
  have hcard : 2 < Nat.card ↥(K ⊓ (S' : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le hRle).trans' hR8)
  have h611 := l6_11_proved p f hp hq G Ω hΩ S' η hη hηS K hK hcard
  rw [← hWη] at h611
  have hUUSet : K ⊓ W ∈ USet Ω := by
    obtain ⟨S₀, hηS₀, -⟩ := hη
    exact (hηS₀.1 h611).1
  have hKS : K ⊓ (S' : Subgroup G) = R :=
    hRK.eq_of_le (S'.isPGroup'.to_inf_right) inf_le_left hRle
  have hKWR : K ⊓ W ≤ R := by
    rw [← hKS]
    exact inf_le_inf_left K hWS'
  have hRWeq : R ⊓ W = K ⊓ W :=
    le_antisymm (inf_le_inf_right W hRK.1) (le_inf hKWR inf_le_right)
  obtain ⟨R'', -, J, hJ, hR''J, hUR'', hcyc, hcard'', h4⟩ :=
    hΩ.exists_data_of_mem_USet hp hUUSet
  have hRR'' : Nat.card R = Nat.card R'' := by
    rw [hΩ.natCard_isSylow2In hK hRK, hΩ.natCard_isSylow2In hJ hR''J]
  refine ⟨hRWeq, hUUSet, hRWeq ▸ hcyc, hRWeq ▸ h4, ?_⟩
  rw [hRWeq, hRR'', hcard'']

theorem commutes_of_mem_WSet (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) [Finite G]
    {W : Subgroup G} (hW : W ∈ WSet Ω) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, ⟨S, hη, hinv⟩, rfl⟩ := hW
  exact ((l6_9_proved p f hp hq G Ω hΩ S).2 η hη hinv).1

theorem exists_conj_of_isSylow2In [Finite G] {P V₁ V₂ : Subgroup G} (h₁ : IsSylow2In V₁ P)
    (h₂ : IsSylow2In V₂ P) : ∃ x ∈ P, conjSub x V₁ = V₂ := by
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow (G := ↥P) (AscL62.sylowOfIsSylow2In'' h₁)
    (AscL62.sylowOfIsSylow2In'' h₂)
  refine ⟨(g : G), g.2, ?_⟩
  have hg' : conjSub g (V₁.subgroupOf P) = V₂.subgroupOf P := hg
  have key : ∀ y : ↥P, y ∈ V₂.subgroupOf P ↔ g⁻¹ * y * g ∈ V₁.subgroupOf P := by
    intro y
    rw [← mem_conjSub_iff, hg']
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have hxP : x ∈ P := by
      have h1 : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ ∈ P :=
        P.mul_mem (P.mul_mem g.2 (h₁.1 hx)) (P.inv_mem g.2)
      simpa [mul_assoc] using h1
    exact (key ⟨x, hxP⟩).mpr hx
  · intro hx
    exact (key ⟨x, h₂.1 hx⟩).mp hx

end Members

theorem mem_sup_OCW_iff {W : Subgroup G} {x : G} :
    x ∈ W ⊔ OCW W ↔ ∃ w ∈ W, ∃ c ∈ OCW W, w * c = x := by
  have h := Subgroup.coe_mul_of_left_le_normalizer_right W (OCW W)
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_OCW W))
  rw [← SetLike.mem_coe, h]
  exact Set.mem_mul

theorem mem_of_isPGroup_of_mem_sup_OCW [Finite G] {W : Subgroup G} (hW : IsPGroup 2 W) {x : G}
    (hx : IsPGroup 2 (Subgroup.zpowers x)) (hxs : x ∈ W ⊔ OCW W) : x ∈ W := by
  obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup_OCW_iff.mp hxs
  have hwc : Commute w c :=
    Subgroup.mem_centralizer_iff.mp (OCW_le_centralizer W hc) w hw
  have hw2 : IsPGroup 2 (Subgroup.zpowers w⁻¹) := by
    rw [Subgroup.zpowers_inv]
    exact hW.to_le (Subgroup.zpowers_le.mpr hw)
  have hcomm : Commute w⁻¹ (w * c) := (Commute.refl w).inv_left.mul_right hwc.inv_left
  have hc' : c = w⁻¹ * (w * c) := by group
  have hc2 : IsPGroup 2 (Subgroup.zpowers c) := by
    rw [hc']
    exact isPGroup_zpowers_mul hcomm hw2 hx
  have hc1 : c = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) hc hc2
  rw [hc1, mul_one]
  exact hw

theorem inf_sup_OCW_le [Finite G] {W A : Subgroup G} (hW : IsPGroup 2 W) (hA : IsPGroup 2 A) :
    A ⊓ (W ⊔ OCW W) ≤ W := fun _ hx =>
  mem_of_isPGroup_of_mem_sup_OCW hW (hA.to_le (Subgroup.zpowers_le.mpr hx.1)) hx.2

@[expose] noncomputable def piN (W : Subgroup G) :
    ↥(Subgroup.normalizer (W : Set G)) →* NQuot (W ⊔ OCW W) :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion (normalizer_le_normalizer_sup W))

theorem piN_eq_one_iff (W : Subgroup G) (a : ↥(Subgroup.normalizer (W : Set G))) :
    piN W a = 1 ↔ (a : G) ∈ W ⊔ OCW W := by
  have h := QuotientGroup.eq_one_iff
    (N := (W ⊔ OCW W).subgroupOf (Subgroup.normalizer ((W ⊔ OCW W : Subgroup G) : Set G)))
    (Subgroup.inclusion (normalizer_le_normalizer_sup W) a)
  refine Iff.trans Iff.rfl (h.trans ?_)
  rw [Subgroup.mem_subgroupOf]
  rfl

open scoped Classical in
@[expose] noncomputable def piG (W : Subgroup G) (g : G) : NQuot (W ⊔ OCW W) :=
  if h : g ∈ Subgroup.normalizer (W : Set G) then piN W ⟨g, h⟩ else 1

theorem piG_of_mem {W : Subgroup G} {g : G} (h : g ∈ Subgroup.normalizer (W : Set G)) :
    piG W g = piN W ⟨g, h⟩ := by
  simp [piG, h]

theorem piG_mul {W : Subgroup G} {a b : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) : piG W (a * b) = piG W a * piG W b := by
  rw [piG_of_mem ha, piG_of_mem hb, piG_of_mem (Subgroup.mul_mem _ ha hb)]
  exact (piN W).map_mul ⟨a, ha⟩ ⟨b, hb⟩

theorem piG_inv {W : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (W : Set G)) :
    piG W a⁻¹ = (piG W a)⁻¹ := by
  rw [piG_of_mem ha, piG_of_mem (Subgroup.inv_mem _ ha)]
  exact (piN W).map_inv ⟨a, ha⟩

theorem piG_eq_one_iff {W : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (W : Set G)) :
    piG W a = 1 ↔ a ∈ W ⊔ OCW W := by
  rw [piG_of_mem ha]
  exact piN_eq_one_iff W ⟨a, ha⟩

theorem piG_of_mem_sup {W : Subgroup G} {a : G} (ha : a ∈ W ⊔ OCW W) : piG W a = 1 :=
  (piG_eq_one_iff (le_normalizer_sup W ha)).mpr ha

theorem piG_eq_iff {W : Subgroup G} {a b : G} (ha : a ∈ Subgroup.normalizer (W : Set G))
    (hb : b ∈ Subgroup.normalizer (W : Set G)) :
    piG W a = piG W b ↔ a⁻¹ * b ∈ W ⊔ OCW W := by
  rw [← piG_eq_one_iff (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hb),
    piG_mul (Subgroup.inv_mem _ ha) hb, piG_inv ha, inv_mul_eq_one, eq_comm]

section Mu

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem MGrp_le_normalizer (Ω : Set (Subgroup G)) (W : Subgroup G) :
    MGrp Ω W ≤ Subgroup.normalizer (W : Set G) := iSup₂_le fun _ hR => hR.2

theorem MGrp_sup_le_normalizer (Ω : Set (Subgroup G)) (W : Subgroup G) :
    MGrp Ω W ⊔ OCW W ≤ Subgroup.normalizer (W : Set G) :=
  sup_le (MGrp_le_normalizer Ω W) (OCW_le_normalizer W)

theorem le_MGrp_of_mem_D {W : Subgroup G} {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    R ≤ MGrp Ω W := le_iSup₂ (f := fun R (_ : R ∈ DSet Ω W) => R) R hR

theorem mem_muGroup_iff {W : Subgroup G} {q : NQuot (W ⊔ OCW W)} :
    q ∈ muGroup Ω W ↔ ∃ m ∈ MGrp Ω W ⊔ OCW W, q = piG W m := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ MGrp Ω W ⊔ OCW W := hy
    have hmN : (y : G) ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hy'
    refine ⟨y, hy', ?_⟩
    rw [piG_of_mem hmN]
    rfl
  · rintro ⟨m, hm, rfl⟩
    have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
    refine ⟨Subgroup.inclusion (normalizer_le_normalizer_sup W) ⟨m, hmN⟩, hm, ?_⟩
    rw [piG_of_mem hmN]
    rfl

theorem piG_mem_muGroup {W : Subgroup G} {m : G} (hm : m ∈ MGrp Ω W ⊔ OCW W) :
    piG W m ∈ muGroup Ω W :=
  mem_muGroup_iff.mpr ⟨m, hm, rfl⟩

theorem conjSub_mem_RSet (hΩ : HypOmegaMod p f Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) (g : G) :
    conjSub g R ∈ RSet Ω := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (hΩ.conjInvariant g J hJ) (hRJ.conj g)

theorem mem_normalizer_iff_of_mem {W : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) (x : G) : n * x * n⁻¹ ∈ W ↔ x ∈ W :=
  (Subgroup.mem_normalizer_iff.mp hn x).symm

theorem conjSub_mem_D (hΩ : HypOmegaMod p f Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) : conjSub n R ∈ DSet Ω W := by
  refine ⟨conjSub_mem_RSet hΩ hR.1 n, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : n * (n⁻¹ * x * n) * n⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (hR.2 hx)) (Subgroup.inv_mem _ hn)
  simpa [mul_assoc] using h1

@[expose] def muDeltaOf (Ω : Set (Subgroup G)) (W : Subgroup G) (C : Set (Subgroup G)) :
    Set ↥(muGroup Ω W) :=
  {q | ∃ R ∈ C, ∃ r ∈ R, r ∉ W ∧ (q : NQuot (W ⊔ OCW W)) = piG W r}

@[expose] def muDelta (Ω : Set (Subgroup G)) (W : Subgroup G) : Set ↥(muGroup Ω W) :=
  muDeltaOf Ω W (DSet Ω W)

section DMembers

variable [Finite G]

theorem D_card (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    Nat.card R = 2 * Nat.card ↥(R ⊓ W) := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  exact (inf_W_of_mem_D hp hq hΩ hW hR hK hRK).2.2.2.2

theorem D_sq_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) : r * r ∈ W :=
  (sq_mem_of_card_eq_two_mul inf_le_left (D_card hp hq hΩ hW hR) hr).2

theorem D_not_mem_sup {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W)
    {r : G} (hr : r ∈ R) (hrW : r ∉ W) : r ∉ W ⊔ OCW W := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  intro h
  exact hrW (inf_sup_OCW_le (isPGroup_of_mem_WSet hW) hRK.2.1 ⟨hr, h⟩)

theorem D_inv_mul_mem (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (hrW : r ∉ W) (hr'W : r' ∉ W) : r⁻¹ * r' ∈ W :=
  (inv_mul_mem_of_card_eq_two_mul (inf_le_left : R ⊓ W ≤ R) (D_card hp hq hΩ hW hR) hr hr'
    (fun h => hrW h.2) (fun h => hr'W h.2)).2

theorem D_piG_eq (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (hrW : r ∉ W) (hr'W : r' ∉ W) : piG W r = piG W r' :=
  (piG_eq_iff (hR.2 hr) (hR.2 hr')).mpr
    (Subgroup.mem_sup_left (D_inv_mul_mem hp hq hΩ hW hR hr hr' hrW hr'W))

end DMembers

section DeltaTT

theorem muDelta_mul_self [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {a : ↥(muGroup Ω W)} (ha : a ∈ muDelta Ω W) :
    a * a = 1 := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  apply Subtype.ext
  show (a : NQuot (W ⊔ OCW W)) * a = 1
  rw [hra, ← piG_mul (hR.2 hr) (hR.2 hr)]
  exact piG_of_mem_sup (Subgroup.mem_sup_left (D_sq_mem hp hq hΩ hW hR hr))

theorem muDelta_ne_one [Finite G] {W : Subgroup G} (hW : W ∈ WSet Ω) {a : ↥(muGroup Ω W)}
    (ha : a ∈ muDelta Ω W) : a ≠ 1 := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  intro h
  have h1 : piG W r = 1 := by rw [← hra, h]; rfl
  exact D_not_mem_sup hW hR hr hrW ((piG_eq_one_iff (hR.2 hr)).mp h1)

theorem muDelta_conj_mem (hΩ : HypOmegaMod p f Ω) {W : Subgroup G} {a : ↥(muGroup Ω W)}
    (ha : a ∈ muDelta Ω W) (g : ↥(muGroup Ω W)) : g * a * g⁻¹ ∈ muDelta Ω W := by
  obtain ⟨R, hR, r, hr, hrW, hra⟩ := ha
  obtain ⟨m, hm, hgm⟩ := mem_muGroup_iff.mp g.2
  have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
  refine ⟨conjSub m R, conjSub_mem_D hΩ hR hmN, m * r * m⁻¹, conj_mem_conjSub hr, ?_, ?_⟩
  · rw [mem_normalizer_iff_of_mem hmN]
    exact hrW
  · show (g : NQuot (W ⊔ OCW W)) * a * (g : NQuot (W ⊔ OCW W))⁻¹ = piG W (m * r * m⁻¹)
    rw [hra, hgm, piG_mul (Subgroup.mul_mem _ hmN (hR.2 hr)) (Subgroup.inv_mem _ hmN),
      piG_mul hmN (hR.2 hr), piG_inv hmN]

theorem closure_muDelta_eq_top (Ω : Set (Subgroup G)) (W : Subgroup G) :
    Subgroup.closure (muDelta Ω W) = ⊤ := by
  let Pm : G → Prop := fun m => m ∈ Subgroup.normalizer (W : Set G) ∧
    ∃ h : piG W m ∈ muGroup Ω W,
      (⟨piG W m, h⟩ : ↥(muGroup Ω W)) ∈ Subgroup.closure (muDelta Ω W)
  have Pm_one : Pm 1 := by
    refine ⟨Subgroup.one_mem _, ?_⟩
    have h1 : piG W 1 = 1 := by
      rw [piG_of_mem (Subgroup.one_mem _)]
      exact (piN W).map_one
    refine ⟨h1 ▸ Subgroup.one_mem _, ?_⟩
    have : (⟨piG W 1, h1 ▸ Subgroup.one_mem _⟩ : ↥(muGroup Ω W)) = 1 := Subtype.ext h1
    rw [this]
    exact Subgroup.one_mem _
  have Pm_mul : ∀ a b, Pm a → Pm b → Pm (a * b) := by
    rintro a b ⟨haN, ha, ha'⟩ ⟨hbN, hb, hb'⟩
    refine ⟨Subgroup.mul_mem _ haN hbN, ?_⟩
    have hab : piG W (a * b) ∈ muGroup Ω W := by
      rw [piG_mul haN hbN]
      exact Subgroup.mul_mem _ ha hb
    refine ⟨hab, ?_⟩
    have : (⟨piG W (a * b), hab⟩ : ↥(muGroup Ω W)) = ⟨piG W a, ha⟩ * ⟨piG W b, hb⟩ :=
      Subtype.ext (piG_mul haN hbN)
    rw [this]
    exact Subgroup.mul_mem _ ha' hb'
  have Pm_inv : ∀ a, Pm a → Pm a⁻¹ := by
    rintro a ⟨haN, ha, ha'⟩
    refine ⟨Subgroup.inv_mem _ haN, ?_⟩
    have hab : piG W a⁻¹ ∈ muGroup Ω W := by
      rw [piG_inv haN]
      exact Subgroup.inv_mem _ ha
    refine ⟨hab, ?_⟩
    have : (⟨piG W a⁻¹, hab⟩ : ↥(muGroup Ω W)) = (⟨piG W a, ha⟩ : ↥(muGroup Ω W))⁻¹ :=
      Subtype.ext (piG_inv haN)
    rw [this]
    exact Subgroup.inv_mem _ ha'
  have hD : ∀ R ∈ DSet Ω W, ∀ x ∈ R, Pm x := by
    intro R hR x hx
    refine ⟨hR.2 hx, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hx)), ?_⟩
    by_cases hxW : x ∈ W
    · have h1 : piG W x = 1 := piG_of_mem_sup (Subgroup.mem_sup_left hxW)
      have : (⟨piG W x, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hx))⟩ :
          ↥(muGroup Ω W)) = 1 := Subtype.ext h1
      rw [this]
      exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨R, hR, x, hx, hxW, rfl⟩
  have hM : ∀ x ∈ MGrp Ω W, Pm x := by
    intro x hx
    refine Subgroup.iSup_induction (C := Pm) (fun R : Subgroup G => ⨆ (_ : R ∈ DSet Ω W), R) hx ?_
      Pm_one Pm_mul
    intro R y hy
    exact Subgroup.iSup_induction (C := Pm) (fun _ : R ∈ DSet Ω W => R) hy
      (fun hR z hz => hD R hR z hz) Pm_one Pm_mul
  have hX : ∀ x ∈ OCW W, Pm x := by
    intro x hx
    refine ⟨OCW_le_normalizer W hx, piG_mem_muGroup (Subgroup.mem_sup_right hx), ?_⟩
    have h1 : piG W x = 1 := piG_of_mem_sup (Subgroup.mem_sup_right hx)
    have : (⟨piG W x, piG_mem_muGroup (Subgroup.mem_sup_right hx)⟩ : ↥(muGroup Ω W)) = 1 :=
      Subtype.ext h1
    rw [this]
    exact Subgroup.one_mem _
  have hsup : ∀ x ∈ MGrp Ω W ⊔ OCW W, Pm x := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hM x hx
      · exact hX x hx
    | one => exact Pm_one
    | mul x y _ _ hx hy => exact Pm_mul x y hx hy
    | inv x _ hx => exact Pm_inv x hx
  rw [eq_top_iff]
  intro q _
  obtain ⟨m, hm, hqm⟩ := mem_muGroup_iff.mp q.2
  obtain ⟨-, h, hcl⟩ := hsup m hm
  have : q = ⟨piG W m, h⟩ := Subtype.ext hqm
  rw [this]
  exact hcl

end DeltaTT

section Translate

theorem piG_pow {W : Subgroup G} {a : G} (ha : a ∈ Subgroup.normalizer (W : Set G)) (n : ℕ) :
    piG W (a ^ n) = (piG W a) ^ n := by
  rw [piG_of_mem ha, piG_of_mem (Subgroup.pow_mem _ ha n)]
  exact (piN W).map_pow ⟨a, ha⟩ n

theorem piG_comm_iff {W : Subgroup G} {r t : G} (hr : r ∈ Subgroup.normalizer (W : Set G))
    (ht : t ∈ Subgroup.normalizer (W : Set G)) :
    piG W r * piG W t = piG W t * piG W r ↔ r * t * r⁻¹ * t⁻¹ ∈ W ⊔ OCW W := by
  rw [← piG_eq_one_iff (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr ht)
    (Subgroup.inv_mem _ hr)) (Subgroup.inv_mem _ ht)),
    piG_mul (Subgroup.mul_mem _ (Subgroup.mul_mem _ hr ht) (Subgroup.inv_mem _ hr))
      (Subgroup.inv_mem _ ht), piG_mul (Subgroup.mul_mem _ hr ht) (Subgroup.inv_mem _ hr),
    piG_mul hr ht, piG_inv hr, piG_inv ht]
  exact (commutatorElement_eq_one_iff_mul_comm (g₁ := piG W r) (g₂ := piG W t)).symm

theorem piG_cube_iff {W : Subgroup G} {r t : G} (hr : r ∈ Subgroup.normalizer (W : Set G))
    (ht : t ∈ Subgroup.normalizer (W : Set G)) :
    (piG W r * piG W t) ^ 3 = 1 ↔ (r * t) ^ 3 ∈ W ⊔ OCW W := by
  rw [← piG_eq_one_iff (Subgroup.pow_mem _ (Subgroup.mul_mem _ hr ht) 3),
    piG_pow (Subgroup.mul_mem _ hr ht), piG_mul hr ht]

theorem comm_mem_of_mem {W : Subgroup G} {x y : G} (hx : x ∈ W)
    (hy : y ∈ Subgroup.normalizer (W : Set G)) : x * y * x⁻¹ * y⁻¹ ∈ W := by
  have h1 : y * x⁻¹ * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hy _).mp (W.inv_mem hx)
  have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [this]
  exact W.mul_mem hx h1

instance finite_NQuot (K : Subgroup G) [Finite G] : Finite (NQuot K) := by
  unfold NQuot
  infer_instance

theorem exists_not_mem_of_mem_D (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    [Finite G] {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    ∃ r ∈ R, r ∉ W := by
  by_contra h
  push Not at h
  have h1 : R ⊓ W = R := inf_eq_left.mpr h
  have h2 := D_card hp hq hΩ hW hR
  rw [h1] at h2
  have : 0 < Nat.card R := Nat.card_pos
  omega

theorem le_sup_of_piG_eq {W : Subgroup G} {R T : Subgroup G} {r : G} (hr : r ∈ R)
    (hRN : R ≤ Subgroup.normalizer (W : Set G)) (hTN : T ≤ Subgroup.normalizer (W : Set G))
    (hT : ∀ x ∈ T, x ∉ W → piG W x = piG W r) : T ≤ R ⊔ W ⊔ OCW W := by
  intro x hx
  by_cases hxW : x ∈ W
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hxW)
  · have h2 : r⁻¹ * x ∈ W ⊔ OCW W := (piG_eq_iff (hRN hr) (hTN hx)).mp (hT x hx hxW).symm
    have hsub : W ⊔ OCW W ≤ R ⊔ W ⊔ OCW W := by
      rw [sup_assoc]
      exact le_sup_right
    have : x = r * (r⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_left hr)) (hsub h2)

section
variable [Finite G]

theorem piG_eq_of_le_sup (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hTR : T ≤ R ⊔ W ⊔ OCW W) {r t : G} (hr : r ∈ R) (ht : t ∈ T)
    (hrW : r ∉ W) (htW : t ∉ W) : piG W t = piG W r := by
  have hrN := hR.2 hr
  set g := piG W r with hg
  have hgg : g * g = 1 := by
    rw [hg, ← piG_mul hrN hrN]
    exact piG_of_mem_sup (Subgroup.mem_sup_left (D_sq_mem hp hq hΩ hW hR hr))
  let Y : Subgroup G :=
    ((Subgroup.zpowers g).comap (piN W)).map (Subgroup.normalizer (W : Set G)).subtype
  have hY : ∀ x : G, x ∈ Subgroup.normalizer (W : Set G) → piG W x ∈ Subgroup.zpowers g →
      x ∈ Y := fun x hx hxg =>
    ⟨⟨x, hx⟩, by simpa [piG_of_mem hx] using hxg, rfl⟩
  have hY' : ∀ x ∈ Y, piG W x ∈ Subgroup.zpowers g := by
    rintro _ ⟨y, hy, rfl⟩
    have : piG W (y : G) = piN W y := by rw [piG_of_mem y.2]
    show piG W (y : G) ∈ _
    rw [this]
    exact hy
  have hRY : R ≤ Y := fun x hx => by
    refine hY x (hR.2 hx) ?_
    by_cases hxW : x ∈ W
    · rw [piG_of_mem_sup (Subgroup.mem_sup_left hxW)]
      exact Subgroup.one_mem _
    · rw [D_piG_eq hp hq hΩ hW hR hx hr hxW hrW]
      exact Subgroup.mem_zpowers g
  have hWY : W ≤ Y := fun x hx => by
    refine hY x (Subgroup.le_normalizer hx) ?_
    rw [piG_of_mem_sup (Subgroup.mem_sup_left hx)]
    exact Subgroup.one_mem _
  have hXY : OCW W ≤ Y := fun x hx => by
    refine hY x (OCW_le_normalizer W hx) ?_
    rw [piG_of_mem_sup (Subgroup.mem_sup_right hx)]
    exact Subgroup.one_mem _
  have htY : t ∈ Y := (sup_le (sup_le hRY hWY) hXY) (hTR ht)
  have h1 := hY' t htY
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hk2 : g ^ k = g ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    have : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hgg
    rw [this, one_zpow, mul_one]
  have hne : piG W t ≠ 1 := fun h =>
    D_not_mem_sup hW hT ht htW ((piG_eq_one_iff (hT.2 ht)).mp h)
  rw [← hk, hk2] at hne ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hne
    exact absurd rfl hne
  · rw [h, zpow_one]

theorem exists_not_conn_of_not_connected (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    (hnc : ¬ DbarConnected Ω W) :
    ∃ d ∈ muDelta Ω W, ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  by_contra hcon
  push Not at hcon
  apply hnc
  intro R hR T hT
  obtain ⟨r, hr, hrW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hR
  obtain ⟨t, ht, htW⟩ := exists_not_mem_of_mem_D hp hq hΩ hW hT
  have hd : (⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨R, hR, r, hr, hrW, rfl⟩
  have ha : (⟨piG W t, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hT ht))⟩ :
      ↥(muGroup Ω W)) ∈ muDelta Ω W := ⟨T, hT, t, ht, htW, rfl⟩
  have hconn := hcon _ hd _ ha
  have key : ∀ x : ↥(muGroup Ω W), Star3T.Conn (muDelta Ω W)
      ⟨piG W r, piG_mem_muGroup (Subgroup.mem_sup_left (le_MGrp_of_mem_D hR hr))⟩ x →
      ∃ R' ∈ DSet Ω W, ∃ r' ∈ R', r' ∉ W ∧ (x : NQuot (W ⊔ OCW W)) = piG W r' ∧
        Relation.ReflTransGen (DbarAdj Ω W) R R' := by
    intro x hx
    induction hx with
    | refl => exact ⟨R, hR, r, hr, hrW, rfl, Relation.ReflTransGen.refl⟩
    | @tail y z _ hyz ih =>
      obtain ⟨Ry, hRy, ry, hry, hryW, hyr, hpath⟩ := ih
      obtain ⟨Rz, hRz, rz, hrz, hrzW, hzr⟩ := hyz.2.1
      refine ⟨Rz, hRz, rz, hrz, hrzW, hzr, hpath.tail ⟨hRz, ?_⟩⟩
      have hryN := hRy.2 hry
      have hrzN := hRz.2 hrz
      by_cases hyz' : y = z
      · right
        have e : piG W rz = piG W ry := by rw [← hzr, ← hyr, hyz']
        exact ⟨le_sup_of_piG_eq hry hRy.2 hRz.2 (fun x hx hxW =>
            (D_piG_eq hp hq hΩ hW hRz hx hrz hxW hrzW).trans e),
          le_sup_of_piG_eq hrz hRz.2 hRy.2 (fun x hx hxW =>
            (D_piG_eq hp hq hΩ hW hRy hx hry hxW hryW).trans e.symm)⟩
      · left
        refine ⟨fun hle => hyz' ?_, fun x hx x' hx' => ?_⟩
        · apply Subtype.ext
          rw [hyr, hzr]
          exact (piG_eq_of_le_sup hp hq hΩ hW hRy hRz hle hry hrz hryW hrzW).symm
        · by_cases hxW : x ∈ W
          · exact Subgroup.mem_sup_left (comm_mem_of_mem hxW (hRz.2 hx'))
          · by_cases hx'W : x' ∈ W
            · have h1 : x * x' * x⁻¹ * x'⁻¹ = (x * x' * x⁻¹) * x'⁻¹ := rfl
              have h2 : x * x' * x⁻¹ ∈ W := by
                have := (Subgroup.mem_normalizer_iff.mp (hRy.2 hx) x').mp hx'W
                exact this
              exact Subgroup.mem_sup_left (W.mul_mem h2 (W.inv_mem hx'W))
            · have hc : y * z = z * y := hyz.2.2
              have hc' : piG W x * piG W x' = piG W x' * piG W x := by
                rw [D_piG_eq hp hq hΩ hW hRy hx hry hxW hryW,
                  D_piG_eq hp hq hΩ hW hRz hx' hrz hx'W hrzW, ← hyr, ← hzr]
                exact congrArg Subtype.val hc
              exact (piG_comm_iff (hRy.2 hx) (hRz.2 hx')).mp hc'
  obtain ⟨R', hR', r', hr', hr'W, hr'eq, hpath⟩ := key _ hconn
  have hr'eq' : piG W t = piG W r' := hr'eq
  refine hpath.tail ⟨hT, Or.inr ⟨?_, ?_⟩⟩
  · exact le_sup_of_piG_eq hr' hR'.2 hT.2 (fun x hx hxW =>
      (D_piG_eq hp hq hΩ hW hT hx ht hxW htW).trans hr'eq')
  · exact le_sup_of_piG_eq ht hT.2 hR'.2 (fun x hx hxW =>
      (D_piG_eq hp hq hΩ hW hR' hx hr' hxW hr'W).trans hr'eq'.symm)

end

end Translate

end Mu

end Thompson

end CFSG.ClassicalInvolution.Asc77

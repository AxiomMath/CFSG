module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitGeneral
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup

@[expose] def FooteAbelianCoreAxiom : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    Blueprint.Catalog S →
    (¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ Blueprint.LieModel S .PSL 2 p f) →
    ∀ i : MulAut S, orderOf i = 2 →
      ∀ x y : ↥(pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S)))), x * y = y * x

@[expose] def FooteCoreCentral (K : Type) [Group K] : Prop :=
  ∀ a : K, orderOf a = 2 → ∀ Y : Subgroup K, IsPComponent 2 Y →
    (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) .PSL 2 p f) ∨
    ⁅⁅oddCoreOfCentralizer a, oddCoreOfCentralizer a⁆, Y⁆ ≤ pPrimeCore 2 K

@[expose] def KGroupFooteCoreInput : Prop :=
  ∀ (K : Type) [Group K] [Finite K], SectionRank.IsKGroupCat K → FooteCoreCentral K

variable {G : Type} [Group G]

theorem oddCoreOfCentralizer_le_centralizer (t : G) :
    oddCoreOfCentralizer t ≤ centralizer ({t} : Set G) :=
  map_subtype_le _

theorem conj_mem_oddCoreOfCentralizer {t g x : G} (hg : g ∈ centralizer ({t} : Set G))
    (hx : x ∈ oddCoreOfCentralizer t) : g * x * g⁻¹ ∈ oddCoreOfCentralizer t := by
  obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
  exact mem_map.mpr ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹,
    (pPrimeCore_normal (p := 2) (G := ↥(centralizer ({t} : Set G)))).conj_mem x' hx' ⟨g, hg⟩,
    rfl⟩

theorem oddCoreOfCentralizer_inf_le [Finite G] (C : Subgroup G) (t : C) :
    oddCoreOfCentralizer (t : G) ⊓ C ≤ (oddCoreOfCentralizer t).map C.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J := centralizer ({t} : Set C) with hJ
  let f : ↥J →* G := C.subtype.comp J.subtype
  have hf : Function.Injective f := C.subtype_injective.comp J.subtype_injective
  have hfJ : ∀ g : ↥J, f g ∈ centralizer ({(t : G)} : Set G) := fun g => by
    have h := mem_centralizer_singleton_iff.mp g.2
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h)
  let N : Subgroup ↥J := (oddCoreOfCentralizer (t : G)).comap f
  have hN : N.Normal := ⟨fun n hn g => by
    show f (g * n * g⁻¹) ∈ oddCoreOfCentralizer (t : G)
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_oddCoreOfCentralizer (hfJ g) hn⟩
  have hNc : Nat.Coprime 2 (Nat.card N) := by
    have h1 : Nat.card (N.map f) = Nat.card N := card_map_of_injective hf
    have h2 : Nat.card (N.map f) ∣ Nat.card (oddCoreOfCentralizer (t : G)) :=
      card_dvd_of_le (map_comap_le _ _)
    have h3 : Nat.card (oddCoreOfCentralizer (t : G)) =
        Nat.card (pPrimeCore 2 ↥(centralizer ({(t : G)} : Set G))) :=
      card_map_of_injective (subtype_injective _)
    rw [← h1]
    exact Nat.Coprime.coprime_dvd_right (h3 ▸ h2) pPrimeCore_coprime_card
  have hNle : N ≤ pPrimeCore 2 ↥J := le_sSup ⟨hN, hNc⟩
  rintro x ⟨hxO, hxC⟩
  have hxt : (⟨x, hxC⟩ : C) ∈ J := by
    have h := mem_centralizer_singleton_iff.mp (oddCoreOfCentralizer_le_centralizer _ hxO)
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext h)
  exact mem_map.mpr ⟨⟨x, hxC⟩, mem_map.mpr ⟨⟨⟨x, hxC⟩, hxt⟩, hNle hxO, rfl⟩, rfl⟩

theorem apply_mem_center_iff {P Q : Type*} [Group P] [Group Q] (φ : P ≃* Q) (x : P) :
    φ x ∈ center Q ↔ x ∈ center P := by
  simp only [mem_center_iff]
  constructor
  · intro h g
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ g)
  · intro h g
    obtain ⟨g, rfl⟩ := φ.surjective g
    rw [← map_mul, ← map_mul, h g]

theorem fusionZStar_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Open.fusionZStar A).map e.toMonoidHom = Open.fusionZStar B := by
  have hO : (Open.fusionOddCore A).map e.toMonoidHom = Open.fusionOddCore B := by
    rw [UnbalancingLocal.fusionOddCore_eq_pPrimeCore,
      UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
    exact pPrimeCore_map_iso 2 e
  let ē : A ⧸ Open.fusionOddCore A ≃* B ⧸ Open.fusionOddCore B := QuotientGroup.congr _ _ e hO
  ext b
  obtain ⟨a, rfl⟩ := e.surjective b
  have hmk : (QuotientGroup.mk (e a) : B ⧸ Open.fusionOddCore B) = ē (QuotientGroup.mk a) :=
    (QuotientGroup.congr_mk _ _ e hO a).symm
  constructor
  · intro h
    obtain ⟨a', ha', hae⟩ := mem_map.mp h
    obtain rfl : a' = a := e.injective hae
    show (QuotientGroup.mk (e a') : B ⧸ Open.fusionOddCore B) ∈ center _
    rw [hmk, apply_mem_center_iff]
    exact ha'
  · intro h
    refine mem_map.mpr ⟨a, ?_, rfl⟩
    show (QuotientGroup.mk a : A ⧸ Open.fusionOddCore A) ∈ center _
    rw [← apply_mem_center_iff ē]
    have h' : (QuotientGroup.mk (e a) : B ⧸ Open.fusionOddCore B) ∈ center _ := h
    rwa [hmk] at h'

theorem nonempty_quotient_fusionZStar_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (A ⧸ Open.fusionZStar A ≃* B ⧸ Open.fusionZStar B) :=
  ⟨QuotientGroup.congr _ _ e (fusionZStar_map_mulEquiv e)⟩

theorem footeCoreHypothesis_of_kGroupInput (hin : KGroupFooteCoreInput) {X : Type} [Group X]
    [Finite X] [IsSimpleGroup X] (hna : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) : FooteCoreHypothesis X := by
  intro H a b ha hb hab Y hYb hY
  set C := centralizer ({b} : Set H) with hC
  have hCtop : C.map H.subtype ≠ ⊤ := by
    intro htop
    have hbZ : (b : X) ∈ center X := by
      refine mem_center_iff.mpr fun g => ?_
      obtain ⟨g', hg', rfl⟩ := mem_map.mp (htop ▸ mem_top g : g ∈ C.map H.subtype)
      exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg')
    rw [(LocalCores.isQuasisimple_of_isSimpleGroup hna).2, mem_bot] at hbZ
    have hb1 : b = 1 := Subtype.ext hbZ
    rw [hb1, orderOf_one] at hb
    exact absurd hb (by norm_num)
  have hCK : SectionRank.IsKGroupCat ↥C :=
    (QuasithinUnique.isKGroupCat_of_kProper hK hCtop).of_mulEquiv
      (C.equivMapOfInjective H.subtype H.subtype_injective)
  have haC : a ∈ C := mem_centralizer_singleton_iff.mpr hab
  have ha' : orderOf (⟨a, haC⟩ : C) = 2 := by rw [Subgroup.orderOf_mk]; exact ha
  rcases hin ↥C hCK ⟨a, haC⟩ ha' (Y.subgroupOf C) hY with ⟨p, f, hp, hp2, hf, hL⟩ | hcomm
  · left
    obtain ⟨e⟩ := nonempty_quotient_fusionZStar_equiv (subgroupOfEquivOfLe hYb)
    exact ⟨p, f, hp, hp2, hf, LieType.CurtisTits.lieModel_of_mulEquiv e hL⟩
  · right
    have hD : oddCoreOfCentralizer a ⊓ C ≤
        (oddCoreOfCentralizer (⟨a, haC⟩ : C)).map C.subtype :=
      oddCoreOfCentralizer_inf_le C ⟨a, haC⟩
    have hmap := map_mono (f := C.subtype) hcomm
    rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hYb] at hmap
    exact (commutator_mono (commutator_mono hD hD) le_rfl).trans hmap

end CFSG.ComponentClassification.FooteLit

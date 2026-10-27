module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra
open scoped MatrixGroups commutatorElement

variable {X : Type} [Group X] [Finite X]

@[expose] def hatIn (β : X) (L : Subgroup X) : Subgroup (MBar β) :=
  (L.subgroupOf (centralizer {β})).map
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))

omit [Finite X] in
theorem mk_mem_hatIn {β : X} {L : Subgroup X} {l : X} (hl : l ∈ L)
    (hlβ : l ∈ centralizer ({β} : Set X)) :
    (QuotientGroup.mk ⟨l, hlβ⟩ : MBar β) ∈ hatIn β L :=
  ⟨⟨l, hlβ⟩, hl, rfl⟩

theorem pPrimeCore_mbar_eq_bot (β : X) : pPrimeCore 2 (MBar β) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact pPrimeCore_quotient_pPrimeCore_eq_bot 2

theorem not_two_dvd_card_ker_mk (β : X) :
    ¬ 2 ∣ Nat.card (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X)))).ker := by
  rw [QuotientGroup.ker_mk']
  exact fun h => (Nat.not_even_iff_odd.mpr (odd_card_pPrimeCore_two _)) (even_iff_two_dvd.mpr h)

theorem hatIn_spec {β : X} {L : Subgroup X} (hL : IsTwoComponentIn L (centralizer {β})) :
    IsTwoComponent (hatIn β L) ∧ pPrimeCore 2 ↥(hatIn β L) = ⊥ ∧
      Nonempty (Bar L ≃* ↥(hatIn β L)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, hiso⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    (QuotientGroup.mk'_surjective _) (not_two_dvd_card_ker_mk β)
  have hLp : IsPComponent 2 (L.subgroupOf (centralizer {β})) := (isTwoComponentIn_iff hL.1).mp hL
  have hcomp : IsTwoComponent (hatIn β L) :=
    (isTwoComponent_iff_isPComponent _).mpr (hbij.mapsTo hLp)
  have hO : pPrimeCore 2 ↥(hatIn β L) = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_mbar_eq_bot β) hcomp.1
  obtain ⟨e, -⟩ := hiso _ hLp
  let e₁ : ↥(L.subgroupOf (centralizer {β})) ≃* ↥L := subgroupOfEquivOfLe hL.1
  exact ⟨hcomp, hO,
    ⟨((QuotientGroup.congr _ _ e₁.symm (pPrimeCore_map_iso 2 e₁.symm)).trans e).trans
      ((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot)⟩⟩

theorem hatIn_commute {β : X} {L L' : Subgroup X} (hL : IsTwoComponentIn L (centralizer {β}))
    (hL' : IsTwoComponentIn L' (centralizer {β})) (hne : L ≠ L') {a b : MBar β}
    (ha : a ∈ hatIn β L) (hb : b ∈ hatIn β L') : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({β} : Set X))))
    (QuotientGroup.mk'_surjective _) (not_two_dvd_card_ker_mk β)
  have hLp : IsPComponent 2 (L.subgroupOf (centralizer {β})) := (isTwoComponentIn_iff hL.1).mp hL
  have hL'p : IsPComponent 2 (L'.subgroupOf (centralizer {β})) :=
    (isTwoComponentIn_iff hL'.1).mp hL'
  have hne' : hatIn β L ≠ hatIn β L' := by
    intro h
    apply hne
    have h1 := hbij.injOn hLp hL'p h
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hL.1, inf_eq_left.mpr hL'.1] at h1
    exact h1
  obtain ⟨-, -, hcomm⟩ := CatalogueBPrimeJoin.mutual_normalization_core_commutation 2
    (hatIn β L) (hatIn β L') (hbij.mapsTo hLp) (hbij.mapsTo hL'p) hne'
  have hO := (hatIn_spec hL).2.1
  have hmem : ⁅a, b⁆ ∈ ⁅hatIn β L, hatIn β L'⁆ := commutator_mem_commutator ha hb
  obtain ⟨o, ho, hoeq⟩ := (hcomm hmem).1
  rw [hO] at ho
  rw [(mem_bot.mp ho), map_one] at hoeq
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := hoeq.symm
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [h1, one_mul]

theorem mem_of_mk_mem_hatIn {β : X} {L : Subgroup X} (hL : IsTwoComponentIn L (centralizer {β}))
    {w : X} (hw : w ∈ centralizer ({β} : Set X)) {n : ℕ} (hwn : w ^ 2 ^ n = 1)
    (hwL : (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ hatIn β L) : w ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({β} : Set X)
  obtain ⟨l, hlL, hle⟩ := hwL
  have hlw : l⁻¹ * ⟨w, hw⟩ ∈ pPrimeCore 2 ↥H := QuotientGroup.eq.mp hle
  have hLp : IsPComponent 2 (L.subgroupOf H) := (isTwoComponentIn_iff hL.1).mp hL
  have hON := UnbalancedCorr.pPrimeCore_le_normalizer_of_isPComponent hL.1 hLp
  have hNA : pPrimeCore 2 ↥H ≤ normalizer ((L.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro r hr
    have hrN := hON ⟨r, hr, rfl⟩
    rw [mem_normalizer_iff] at hrN ⊢
    intro h
    exact hrN (h : X)
  have hmem : (⟨w, hw⟩ : ↥H) ∈ L.subgroupOf H ⊔ pPrimeCore 2 ↥H := by
    have h1 : (⟨w, hw⟩ : ↥H) = l * (l⁻¹ * ⟨w, hw⟩) := by group
    rw [h1]
    exact mul_mem (mem_sup_left hlL) (mem_sup_right hlw)
  have hwn' : (⟨w, hw⟩ : ↥H) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hwn)
  exact T23.mem_of_mem_sup_of_pow_two_pow hNA (odd_card_pPrimeCore_two ↥H) hmem hwn'

theorem lift_twoComponent {β u : X} (huβ : u ∈ centralizer ({β} : Set X)) (hu : orderOf u = 2)
    {Y : Subgroup (MBar β)}
    (hY : IsTwoComponentIn Y (centralizer {(QuotientGroup.mk ⟨u, huβ⟩ : MBar β)})) :
    ∃ J : Subgroup X, IsTwoComponentIn J (centralizer {β} ⊓ centralizer {u}) ∧
      (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)), w ∈ centralizer {u} →
        (∃ k : ℕ, orderOf w = 2 ^ k) → (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ J) ∧
      (∀ S : Subgroup X, (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)),
        w ∈ centralizer {u} → (∃ k : ℕ, orderOf w = 2 ^ k) →
          (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ S) → J ≤ S) ∧
      Nonempty (↥J ⧸ pPrimeCore 2 ↥J ≃* ↥Y ⧸ pPrimeCore 2 ↥Y) := by
  obtain ⟨J, hJle, hJc, hmem, hgen, -, g, hgs, hgk⟩ :=
    exists_lift_twoComponent huβ hu hY.1 ((isTwoComponentIn_iff hY.1).mp hY)
  exact ⟨J, (isTwoComponentIn_iff hJle).mpr hJc, hmem, hgen,
    GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective g hgs hgk⟩

theorem lift_le_of_le_hatIn {β u : X} {L : Subgroup X} (hL : IsTwoComponentIn L (centralizer {β}))
    {Y : Subgroup (MBar β)} (hYL : Y ≤ hatIn β L) {J : Subgroup X}
    (hgen : ∀ S : Subgroup X, (∀ (w : X) (hw : w ∈ centralizer ({β} : Set X)),
        w ∈ centralizer {u} → (∃ k : ℕ, orderOf w = 2 ^ k) →
          (QuotientGroup.mk ⟨w, hw⟩ : MBar β) ∈ Y → w ∈ S) → J ≤ S) : J ≤ L :=
  hgen L fun w hw _ ⟨k, hk⟩ hwY =>
    mem_of_mk_mem_hatIn hL hw (n := k) (by rw [← hk, pow_orderOf_eq_one]) (hYL hwY)

theorem spinSeven_three_in {Γ : Type} [Group Γ] [Finite Γ] {M : Subgroup Γ} {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (h5 : 5 ≤ p ^ f) (e : ↥M ≃* spinGroup (quadOdd 3 K)) {x : Γ} (hxM : x ∈ M)
    (hx : orderOf x = 2) (hxZ : (⟨x, hxM⟩ : ↥M) ∉ center ↥M) {w : Γ} (hwM : w ∈ M)
    (hwc : (⟨w, hwM⟩ : ↥M) ∈ center ↥M) (hw1 : w ≠ 1) :
    ∃ Y₁ Y₂ Y₃ : Subgroup Γ,
      (IsTwoComponentIn Y₁ (M ⊓ centralizer {x}) ∧
        (Y₁.subgroupOf (M ⊓ centralizer {x})).Normal ∧ IsSLTwoOver (p ^ f) ↥Y₁ ∧ w ∈ Y₁) ∧
      (IsTwoComponentIn Y₂ (M ⊓ centralizer {x}) ∧
        (Y₂.subgroupOf (M ⊓ centralizer {x})).Normal ∧ IsSLTwoOver (p ^ f) ↥Y₂ ∧ x ∈ Y₂) ∧
      (IsTwoComponentIn Y₃ (M ⊓ centralizer {x}) ∧
        (Y₃.subgroupOf (M ⊓ centralizer {x})).Normal ∧ IsSLTwoOver (p ^ f) ↥Y₃ ∧
          w * x ∈ Y₃) := by
  have hodd : Odd (Nat.card K) := hK ▸ (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  set x' := e ⟨x, hxM⟩ with hx'
  have hx'2 : orderOf x' = 2 := by rw [hx', MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hx
  have hx'Z : x' ∉ center (spinGroup (quadOdd 3 K)) := by
    rw [hx', mem_center_mulEquiv_iff]
    exact hxZ
  have hw' : e ⟨w, hwM⟩ = spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero := by
    refine eq_of_mem_center_spinSeven h2 ((mem_center_mulEquiv_iff e _).mpr hwc) ?_
    intro h1
    apply hw1
    have h3 : (⟨w, hwM⟩ : ↥M) = 1 := e.injective (by rw [h1, map_one])
    exact congrArg Subtype.val h3
  obtain ⟨J₁, J₂, J₃, ⟨hJ₁, hn₁, hs₁, hν₁⟩, ⟨hJ₂, hn₂, hs₂, hx₂⟩, ⟨hJ₃, hn₃, hs₃, hν₃⟩⟩ :=
    spinSeven_three_at hp hp2 hK h5 hx'2 hx'Z
  set ι : spinGroup (quadOdd 3 K) →* Γ := M.subtype.comp e.symm.toMonoidHom with hι
  have hιi : Function.Injective ι := M.subtype_injective.comp e.symm.injective
  have hCmap : (centralizer ({x'} : Set (spinGroup (quadOdd 3 K)))).map ι =
      M ⊓ centralizer {x} := by
    rw [hι, ← map_map, map_centralizer_singleton_mulEquiv e.symm, hx',
      MulEquiv.symm_apply_apply, map_subtype_centralizer_mem]
  have key : ∀ {J : Subgroup (spinGroup (quadOdd 3 K))}, IsTwoComponentIn J (centralizer {x'}) →
      (J.subgroupOf (centralizer {x'})).Normal → IsSLTwoOver (p ^ f) ↥J →
      IsTwoComponentIn (J.map ι) (M ⊓ centralizer {x}) ∧
        ((J.map ι).subgroupOf (M ⊓ centralizer {x})).Normal ∧ IsSLTwoOver (p ^ f) ↥(J.map ι) :=
    fun hJ hn hs => ⟨hCmap ▸ L35.isTwoComponentIn_map_of_injective ι hιi hJ,
      hCmap ▸ normal_subgroupOf_map ι hJ.1 hn,
      isSLTwoOver_of_mulEquiv' (Subgroup.equivMapOfInjective _ ι hιi) hs⟩
  have hιν : ι (spinGroup.negOne (quadOdd 3 K) (nondegenerate_quadOdd 3 K).ne_zero) = w := by
    rw [hι, MonoidHom.comp_apply, ← hw']
    simp
  have hιx : ι x' = x := by
    rw [hι, MonoidHom.comp_apply, hx']
    simp
  refine ⟨J₁.map ι, J₂.map ι, J₃.map ι, ⟨(key hJ₁ hn₁ hs₁).1, (key hJ₁ hn₁ hs₁).2.1,
    (key hJ₁ hn₁ hs₁).2.2, hιν ▸ mem_map_of_mem ι hν₁⟩, ⟨(key hJ₂ hn₂ hs₂).1,
    (key hJ₂ hn₂ hs₂).2.1, (key hJ₂ hn₂ hs₂).2.2, hιx ▸ mem_map_of_mem ι hx₂⟩,
    ⟨(key hJ₃ hn₃ hs₃).1, (key hJ₃ hn₃ hs₃).2.1, (key hJ₃ hn₃ hs₃).2.2, ?_⟩⟩
  have h3 := mem_map_of_mem ι hν₃
  rwa [map_mul, hιν, hιx] at h3

end CFSG.ComponentClassification.HarrisLit.T1

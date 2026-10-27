module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup
open scoped commutatorElement

section Lift

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] (θ : ↥A →* P)

@[expose] def liftSub (S : Subgroup P) : Subgroup G := (S.comap θ).map A.subtype

@[expose] def levLift (S : Subgroup P) : Subgroup G := ⁅liftSub θ S, liftSub θ S⁆

variable {θ} {S : Subgroup P}

theorem mem_liftSub {x : G} : x ∈ liftSub θ S ↔ ∃ hx : x ∈ A, θ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hxS⟩
    exact ⟨⟨x, hx⟩, hxS, rfl⟩

theorem liftSub_le : liftSub θ S ≤ A := fun _ hx => (mem_liftSub.1 hx).1

theorem commutator_self_le (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  commutator_le.2 fun _ ha _ hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem levLift_le_liftSub : levLift θ S ≤ liftSub θ S := commutator_self_le _

theorem levLift_le : levLift θ S ≤ A := levLift_le_liftSub.trans liftSub_le

theorem liftSub_mono {S' : Subgroup P} (h : S ≤ S') : liftSub θ S ≤ liftSub θ S' :=
  fun _ hx => by
    obtain ⟨hxA, hxS⟩ := mem_liftSub.1 hx
    exact mem_liftSub.2 ⟨hxA, h hxS⟩

theorem levLift_eq_map : levLift θ S = (⁅S.comap θ, S.comap θ⁆).map A.subtype := by
  rw [levLift, liftSub, map_commutator]

theorem theta_mem_of_mem_levLift {l : G} (hl : l ∈ levLift θ S) :
    θ ⟨l, levLift_le hl⟩ ∈ S :=
  (mem_liftSub.1 (levLift_le_liftSub hl)).2

theorem commutatorElement_mul_mul_of_commute' {M : Type*} [Group M] {a b z w : M}
    (hzb : z * b = b * z) (hwa : w * a = a * w) (hzw : z * w = w * z) :
    ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  simp only [commutatorElement_def]
  have h : w * a⁻¹ = a⁻¹ * w := by
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hwa]
      _ = a⁻¹ * w := by group
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * b) * w * z⁻¹ * a⁻¹ * w⁻¹ * b⁻¹ := by group
    _ = a * b * (z * w * z⁻¹) * a⁻¹ * w⁻¹ * b⁻¹ := by rw [hzb]; group
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by rw [hzw, mul_inv_cancel_right]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h]; group

variable (hker : θ.ker = center ↥A)
include hker

theorem mem_center_of_theta_eq_one {a : ↥A} (ha : θ a = 1) : a ∈ center ↥A := by
  rw [← hker]
  exact ha

theorem levLift_le_centralizer {w : G} (hw : w ∈ A)
    (hS : ∀ s ∈ S, θ ⟨w, hw⟩ * s = s * θ ⟨w, hw⟩) : levLift θ S ≤ centralizer {w} := by
  have key : ∀ a ∈ liftSub θ S, ∃ z : G, w * a * w⁻¹ = a * z ∧ ∃ hz : z ∈ A,
      (⟨z, hz⟩ : ↥A) ∈ center ↥A := by
    intro a ha
    obtain ⟨haA, haS⟩ := mem_liftSub.1 ha
    have hz : a⁻¹ * (w * a * w⁻¹) ∈ A :=
      mul_mem (inv_mem haA) (mul_mem (mul_mem hw haA) (inv_mem hw))
    refine ⟨a⁻¹ * (w * a * w⁻¹), by group, hz, mem_center_of_theta_eq_one hker ?_⟩
    have h1 : (⟨a⁻¹ * (w * a * w⁻¹), hz⟩ : ↥A) =
        (⟨a, haA⟩ : ↥A)⁻¹ * (⟨w, hw⟩ * ⟨a, haA⟩ * (⟨w, hw⟩ : ↥A)⁻¹) := rfl
    rw [h1, map_mul, map_inv, map_mul, map_mul, map_inv, hS _ haS]
    group
  rw [levLift, commutator_le]
  intro a ha b hb
  rw [mem_centralizer_singleton_iff]
  obtain ⟨z₁, hz₁, hz₁A, hz₁Z⟩ := key a ha
  obtain ⟨z₂, hz₂, hz₂A, hz₂Z⟩ := key b hb
  have hcomm : ∀ {z : G} (hzA : z ∈ A), (⟨z, hzA⟩ : ↥A) ∈ center ↥A → ∀ y ∈ A, z * y = y * z :=
    fun hzA hz y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hconj : w * ⁅a, b⁆ * w⁻¹ = ⁅a, b⁆ := by
    rw [show w * ⁅a, b⁆ * w⁻¹ = ⁅w * a * w⁻¹, w * b * w⁻¹⁆ by
      simp only [commutatorElement_def]; group, hz₁, hz₂]
    exact commutatorElement_mul_mul_of_commute' (hcomm hz₁A hz₁Z b (liftSub_le hb))
      (hcomm hz₂A hz₂Z a (liftSub_le ha)) (hcomm hz₁A hz₁Z z₂ hz₂A)
  calc ⁅a, b⁆ * w = w * ⁅a, b⁆ * w⁻¹ * w := by rw [hconj]
    _ = w * ⁅a, b⁆ := by group

omit hker in
theorem mem_normalizer_liftSub {y : G} (hy : y ∈ A)
    (hyS : θ ⟨y, hy⟩ ∈ normalizer (S : Set P)) : y ∈ normalizer (liftSub θ S : Set G) := by
  have key : ∀ z : G, ∀ hz : z ∈ A, θ ⟨z, hz⟩ ∈ normalizer (S : Set P) →
      ∀ x ∈ liftSub θ S, z * x * z⁻¹ ∈ liftSub θ S := by
    intro z hz hzS x hx
    obtain ⟨hxA, hxS⟩ := mem_liftSub.1 hx
    have hmem : z * x * z⁻¹ ∈ A := mul_mem (mul_mem hz hxA) (inv_mem hz)
    refine mem_liftSub.2 ⟨hmem, ?_⟩
    have h1 : (⟨z * x * z⁻¹, hmem⟩ : ↥A) = ⟨z, hz⟩ * ⟨x, hxA⟩ * (⟨z, hz⟩ : ↥A)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 hzS _).1 hxS
  refine mem_normalizer_iff.2 fun x => ⟨key y hy hyS x, fun hx => ?_⟩
  have hy' : θ ⟨y⁻¹, inv_mem hy⟩ ∈ normalizer (S : Set P) := by
    have h1 : (⟨y⁻¹, inv_mem hy⟩ : ↥A) = (⟨y, hy⟩ : ↥A)⁻¹ := rfl
    rw [h1, map_inv]
    exact inv_mem hyS
  have := key y⁻¹ (inv_mem hy) hy' _ hx
  simpa [mul_assoc] using this

omit hker in
theorem mem_normalizer_levLift {y : G} (hy : y ∈ A)
    (hyS : θ ⟨y, hy⟩ ∈ normalizer (S : Set P)) : y ∈ normalizer (levLift θ S : Set G) := by
  have h := mem_normalizer_liftSub hy hyS
  rw [mem_normalizer_iff_map_conj_eq] at h ⊢
  rw [levLift, map_commutator, h]

variable (hθ : Function.Surjective θ) (hperf : ⁅S, S⁆ = S)
include hθ hperf

omit hker in
theorem exists_mem_levLift {s : P} (hs : s ∈ S) :
    ∃ l : G, ∃ hl : l ∈ levLift θ S, θ ⟨l, levLift_le hl⟩ = s := by
  have hmap : (⁅S.comap θ, S.comap θ⁆).map θ = S := by
    rw [map_commutator, map_comap_eq_self_of_surjective hθ, hperf]
  rw [← hmap] at hs
  obtain ⟨n, hn, rfl⟩ := hs
  refine ⟨n, ?_, rfl⟩
  rw [levLift_eq_map]
  exact ⟨n, hn, rfl⟩

theorem exists_mem_levLift_inv_mul_mem {a : G} (ha : a ∈ liftSub θ S) :
    ∃ l ∈ levLift θ S, ∃ hz : l⁻¹ * a ∈ A, (⟨l⁻¹ * a, hz⟩ : ↥A) ∈ center ↥A := by
  obtain ⟨haA, haS⟩ := mem_liftSub.1 ha
  obtain ⟨l, hl, hlθ⟩ := exists_mem_levLift hθ hperf haS
  have hz : l⁻¹ * a ∈ A := mul_mem (inv_mem (levLift_le hl)) haA
  refine ⟨l, hl, hz, mem_center_of_theta_eq_one hker ?_⟩
  have h1 : (⟨l⁻¹ * a, hz⟩ : ↥A) = (⟨l, levLift_le hl⟩ : ↥A)⁻¹ * ⟨a, haA⟩ := rfl
  rw [h1, map_mul, map_inv, hlθ, inv_mul_cancel]

theorem commutator_levLift : ⁅levLift θ S, levLift θ S⁆ = levLift θ S := by
  refine le_antisymm (commutator_self_le _) ?_
  conv_lhs => rw [levLift]
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨l₁, hl₁, hz₁A, hz₁⟩ := exists_mem_levLift_inv_mul_mem hker hθ hperf ha
  obtain ⟨l₂, hl₂, hz₂A, hz₂⟩ := exists_mem_levLift_inv_mul_mem hker hθ hperf hb
  have hcomm : ∀ {z : G} (hzA : z ∈ A), (⟨z, hzA⟩ : ↥A) ∈ center ↥A → ∀ y ∈ A, z * y = y * z :=
    fun hzA hz y hy => congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩).symm
  have hab : ⁅a, b⁆ = ⁅l₁, l₂⁆ := by
    have e1 : a = l₁ * (l₁⁻¹ * a) := by group
    have e2 : b = l₂ * (l₂⁻¹ * b) := by group
    rw [e1, e2]
    exact commutatorElement_mul_mul_of_commute' (hcomm hz₁A hz₁ l₂ (levLift_le hl₂))
      (hcomm hz₂A hz₂ l₁ (levLift_le hl₁)) (hcomm hz₁A hz₁ _ hz₂A)
  rw [hab]
  exact commutator_mem_commutator hl₁ hl₂

theorem mem_levLift_of_pow (hZ : Odd (Nat.card (center ↥A))) {a : G} (ha : a ∈ liftSub θ S)
    {k : ℕ} (hak : a ^ 2 ^ k = 1) : a ∈ levLift θ S := by
  obtain ⟨l, hl, hzA, hz⟩ := exists_mem_levLift_inv_mul_mem hker hθ hperf ha
  set z := l⁻¹ * a with hzdef
  have hmodd : Odd (orderOf z) := by
    have h := orderOf_dvd_natCard (⟨⟨z, hzA⟩, hz⟩ : center ↥A)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hZ h
  set m := orderOf z with hm
  have hcomm : Commute l z := congrArg Subtype.val (mem_center_iff.mp hz ⟨l, levLift_le hl⟩)
  have hlm : l ^ m = a ^ m := by
    have h1 : a = l * z := by rw [hzdef, mul_inv_cancel_left]
    rw [h1, hcomm.mul_pow, hm, pow_orderOf_eq_one, mul_one]
  have hcop : Nat.Coprime m (orderOf a) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hak)
      (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hmodd))
  obtain ⟨b, hb⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hb, ← hlm]
  exact pow_mem (pow_mem hl _) _

end Lift

section Restrict

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] (θ : ↥A →* P)
  (S : Subgroup P)

@[expose] def levLiftHom : ↥(levLift θ S) →* ↥S :=
  (θ.comp (Subgroup.inclusion levLift_le)).codRestrict S fun l => theta_mem_of_mem_levLift l.2

variable {θ S}

theorem levLiftHom_apply (l : ↥(levLift θ S)) :
    ((levLiftHom θ S l : ↥S) : P) = θ ⟨l, levLift_le l.2⟩ :=
  rfl

variable (hker : θ.ker = center ↥A)
include hker

theorem mem_center_levLift_of {l : ↥(levLift θ S)} (h : levLiftHom θ S l ∈ center ↥S) :
    l ∈ center ↥(levLift θ S) := by
  have hle := levLift_le_centralizer hker (levLift_le l.2) (S := S) fun s hs => by
    have := mem_center_iff.mp h ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  rw [mem_center_iff]
  intro l'
  have h1 := mem_centralizer_singleton_iff.mp (hle l'.2)
  exact Subtype.ext h1

variable (hθ : Function.Surjective θ) (hperf : ⁅S, S⁆ = S)
include hθ hperf

omit hker in
theorem levLiftHom_surjective : Function.Surjective (levLiftHom θ S) := by
  rintro ⟨s, hs⟩
  obtain ⟨l, hl, hls⟩ := exists_mem_levLift hθ hperf hs
  exact ⟨⟨l, hl⟩, Subtype.ext hls⟩

theorem mem_center_levLift_iff (l : ↥(levLift θ S)) :
    l ∈ center ↥(levLift θ S) ↔ levLiftHom θ S l ∈ center ↥S := by
  refine ⟨fun h => ?_, mem_center_levLift_of hker⟩
  rw [mem_center_iff] at h ⊢
  intro s
  obtain ⟨l', rfl⟩ := levLiftHom_surjective hθ hperf s
  rw [← map_mul, ← map_mul, h l']

@[expose] noncomputable def levLiftQuotEquiv :
    ↥(levLift θ S) ⧸ center ↥(levLift θ S) ≃* ↥S ⧸ center ↥S := by
  let φ : ↥(levLift θ S) →* ↥S ⧸ center ↥S :=
    (QuotientGroup.mk' (center ↥S)).comp (levLiftHom θ S)
  have hφ : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective _).comp (levLiftHom_surjective hθ hperf)
  have hker' : φ.ker = center ↥(levLift θ S) := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_center_levLift_iff hker hθ hperf]
  exact (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)

theorem isQuasisimple_levLift (hS : CFSG.IsQuasisimple ↥S) :
    CFSG.IsQuasisimple ↥(levLift θ S) := by
  obtain ⟨-, hsimp, a, b, hab⟩ := hS
  let e := levLiftQuotEquiv hker hθ hperf
  have : IsSimpleGroup (↥(levLift θ S) ⧸ center ↥(levLift θ S)) := e.isSimpleGroup
  refine ⟨(Subgroup.isPerfect_iff).2 (commutator_levLift hker hθ hperf),
    this, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem odd_card_center_levLift [Finite G] (hZ : Odd (Nat.card (center ↥A)))
    (hZS : Odd (Nat.card (center ↥S))) : Odd (Nat.card (center ↥(levLift θ S))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥(levLift θ S)) 2 h2
  have hz2 : (z : ↥(levLift θ S)) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hzS : levLiftHom θ S z = 1 := by
    have hmem : levLiftHom θ S z ∈ center ↥S :=
      (mem_center_levLift_iff hker hθ hperf _).1 z.2
    have h1 : (⟨levLiftHom θ S z, hmem⟩ : center ↥S) ^ 2 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hz2, map_one]; rfl)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    have h3 : orderOf (⟨levLiftHom θ S z, hmem⟩ : center ↥S) ∣ Nat.card (center ↥S) :=
      orderOf_dvd_natCard _
    have h4 : orderOf (⟨levLiftHom θ S z, hmem⟩ : center ↥S) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
      · exact h
      · rw [h] at h3
        exact absurd h3 (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hZS))
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp h4)
  have hzA : (⟨((z : ↥(levLift θ S)) : G), levLift_le (z : ↥(levLift θ S)).2⟩ : ↥A) ∈
      center ↥A := mem_center_of_theta_eq_one hker (by
        have := congrArg Subtype.val hzS
        rwa [levLiftHom_apply] at this)
  have h5 : orderOf (⟨⟨((z : ↥(levLift θ S)) : G), _⟩, hzA⟩ : center ↥A) ∣
      Nat.card (center ↥A) := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_coe, Subgroup.orderOf_coe,
    hz] at h5
  exact absurd h5 (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hZ))

end Restrict

end CFSG.ComponentClassification.RankTwoClassical

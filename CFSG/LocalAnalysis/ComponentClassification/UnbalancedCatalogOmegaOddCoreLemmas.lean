module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogOmegaHigherRank

public section

namespace CFSG.ComponentClassification.UnbalancedCatalog

namespace OmegaRadical

variable {M : Type*} [Group M]

theorem commute_of_inf_eq_bot {K₁ K₂ : Subgroup M}
    (h₁ : ∀ x ∈ K₂, ∀ y ∈ K₁, x * y * x⁻¹ ∈ K₁) (h₂ : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y * x⁻¹ ∈ K₂)
    (hbot : K₁ ⊓ K₂ = ⊥) {a b : M} (ha : a ∈ K₁) (hb : b ∈ K₂) : a * b = b * a := by
  have hc₂ : a * b * a⁻¹ * b⁻¹ ∈ K₂ := mul_mem (h₂ a ha b hb) (inv_mem hb)
  have hc₁ : a * b * a⁻¹ * b⁻¹ ∈ K₁ := by
    have h := mul_mem ha (h₁ b hb a⁻¹ (inv_mem ha))
    rwa [show a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ by group] at h
  have hc : a * b * a⁻¹ * b⁻¹ ∈ K₁ ⊓ K₂ := ⟨hc₁, hc₂⟩
  rw [hbot, Subgroup.mem_bot] at hc
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hc, one_mul]

abbrev oddCoreImage (X : Subgroup M) : Subgroup M := (CFSG.oddCore ↥X).map X.subtype

theorem oddCoreImage_le (X : Subgroup M) : oddCoreImage X ≤ X := by
  rintro _ ⟨q, -, rfl⟩
  exact q.2

theorem oddCoreImage_conj (X : Subgroup M) {x : M} (hx : x ∈ X) {r : M}
    (hr : r ∈ oddCoreImage X) : x * r * x⁻¹ ∈ oddCoreImage X := by
  obtain ⟨q, hq, rfl⟩ := hr
  refine ⟨⟨x, hx⟩ * q * ⟨x, hx⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (CFSG.oddCore ↥X).Normal).conj_mem q hq _

theorem odd_card_oddCoreImage [Finite M] (X : Subgroup M) : Odd (Nat.card (oddCoreImage X)) := by
  rw [Subgroup.card_map_of_injective X.subtype_injective]
  exact EvenCatalog.odd_card_oddCore

theorem oddCore_eq_bot_of_oddCoreImage (X : Subgroup M) (h : oddCoreImage X = ⊥) :
    CFSG.oddCore ↥X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h

theorem le_oddCore_of_normalized [Finite M] {Y S : Subgroup M} (hSY : S ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ s ∈ S, y * s * y⁻¹ ∈ S) (hodd : Odd (Nat.card S)) :
    S.subgroupOf Y ≤ CFSG.oddCore ↥Y := by
  refine EvenCatalog.le_oddCore_of_normal ⟨fun s hs y => ?_⟩ ?_
  · rw [Subgroup.mem_subgroupOf] at hs ⊢
    exact hnorm y y.2 s hs
  · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv]

theorem oddCore_eq_bot_of_normal [Finite M] {X N : Subgroup M} (hNX : N ≤ X)
    (hnorm : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hN : CFSG.oddCore ↥N = ⊥)
    (hcent : ∀ x ∈ X, (∀ n ∈ N, x * n = n * x) → ∃ k : ℕ, x ^ 2 ^ k = 1) :
    CFSG.oddCore ↥X = ⊥ := by
  set R := oddCoreImage X with hRdef
  have hRN : R ⊓ N = ⊥ := by
    have hle := le_oddCore_of_normalized (Y := N) (S := R ⊓ N) inf_le_right
      (fun y hy s hs => ⟨oddCoreImage_conj X (hNX hy) hs.1, hnorm y (hNX hy) s hs.2⟩)
      (Odd.of_dvd_nat (odd_card_oddCoreImage X) (Subgroup.card_dvd_of_le inf_le_left))
    rw [hN, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hx.2⟩ : N) ∈ (R ⊓ N).subgroupOf N := Subgroup.mem_subgroupOf.mpr hx
    rw [hle, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  apply oddCore_eq_bot_of_oddCoreImage
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hrX := oddCoreImage_le X hr
  obtain ⟨k, hk⟩ := hcent r hrX fun n hn =>
    commute_of_inf_eq_bot (fun x hx y hy => oddCoreImage_conj X (hNX hx) hy)
      (fun x hx y hy => hnorm x (oddCoreImage_le X hx) y hy) hRN hr hn
  obtain ⟨q, hq, rfl⟩ := hr
  have := eq_one_of_mem_oddCore_of_two_pow hq (k := k) (Subtype.ext (by simpa using hk))
  rw [this]
  rfl

theorem oddCore_eq_bot_of_orbit_le_three [Finite M] {Y : Type*} [MulAction M Y] {y₀ : Y}
    (horb : Nat.card (MulAction.orbit M y₀) ≤ 3) {C N : Subgroup M} (hNC : N ≤ C)
    (hnorm : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hNE : N ≤ MulAction.stabilizer M y₀)
    (hCE : CFSG.oddCore ↥(C ⊓ MulAction.stabilizer M y₀) = ⊥)
    (hη : ∀ η ∈ C, orderOf η = 3 → (∀ n ∈ N, η * n * η⁻¹ = n) →
      η ∈ MulAction.stabilizer M y₀) :
    CFSG.oddCore ↥C = ⊥ := by
  set E := MulAction.stabilizer M y₀ with hEdef
  set R := oddCoreImage C with hRdef
  have hRE : R ⊓ E = ⊥ := by
    have hle := le_oddCore_of_normalized (Y := C ⊓ E) (S := R ⊓ E)
      (inf_le_inf_right E (oddCoreImage_le C))
      (fun y hy s hs => by
        obtain ⟨hyC, hyE⟩ := Subgroup.mem_inf.mp hy
        obtain ⟨hsR, hsE⟩ := Subgroup.mem_inf.mp hs
        exact Subgroup.mem_inf.mpr
          ⟨oddCoreImage_conj C hyC hsR, mul_mem (mul_mem hyE hsE) (inv_mem hyE)⟩)
      (Odd.of_dvd_nat (odd_card_oddCoreImage C) (Subgroup.card_dvd_of_le inf_le_left))
    rw [hCE, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, ⟨oddCoreImage_le C hx.1, hx.2⟩⟩ : ↥(C ⊓ E)) ∈ (R ⊓ E).subgroupOf (C ⊓ E) :=
      Subgroup.mem_subgroupOf.mpr hx
    rw [hle, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hx')
  have : Finite (MulAction.orbit M y₀) := (Set.finite_range fun m : M => m • y₀).to_subtype
  have hR3 : Nat.card R ≤ 3 := by
    refine (Nat.card_le_card_of_injective
      (fun r : R => (⟨(r : M) • y₀, MulAction.mem_orbit _ _⟩ : MulAction.orbit M y₀))
      fun r₁ r₂ h => ?_).trans horb
    have h1 : (r₁ : M) • y₀ = (r₂ : M) • y₀ := congrArg Subtype.val h
    have hE' : (r₂ : M)⁻¹ * r₁ ∈ E := by
      rw [hEdef, MulAction.mem_stabilizer_iff, mul_smul, h1, inv_smul_smul]
    have h2 : (r₂ : M)⁻¹ * r₁ ∈ R ⊓ E :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem r₂.2) r₁.2, hE'⟩
    rw [hRE, Subgroup.mem_bot] at h2
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  have hRodd : Odd (Nat.card R) := odd_card_oddCoreImage C
  apply oddCore_eq_bot_of_oddCoreImage
  rcases (show Nat.card R = 1 ∨ Nat.card R = 3 by
    obtain ⟨m, hm⟩ := hRodd
    omega) with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq R h1
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨η, hη3⟩ := exists_prime_orderOf_dvd_card' (G := R) 3 (by rw [h3])
    have hη3' : orderOf (η : M) = 3 := by rw [Subgroup.orderOf_coe, hη3]
    have hRN : R ⊓ N = ⊥ := eq_bot_iff.mpr fun x hx => by
      rw [← hRE]
      exact ⟨hx.1, hNE hx.2⟩
    have hcomm : ∀ n ∈ N, (η : M) * n * (η : M)⁻¹ = n := fun n hn => by
      rw [commute_of_inf_eq_bot (fun x hx y hy => oddCoreImage_conj C (hNC hx) hy)
        (fun x hx y hy => hnorm x (oddCoreImage_le C hx) y hy) hRN η.2 hn, mul_inv_cancel_right]
    have hηE := hη (η : M) (oddCoreImage_le C η.2) hη3' hcomm
    have h1 : (η : M) ∈ R ⊓ E := ⟨η.2, hηE⟩
    rw [hRE, Subgroup.mem_bot] at h1
    rw [h1, orderOf_one] at hη3'
    exact absurd hη3' (by norm_num)

theorem oddCore_centralizer_of_conj (H : Subgroup M) (α β : M)
    (h : CFSG.oddCore ↥(H.map (MulAut.conj β⁻¹).toMonoidHom ⊓
      Subgroup.centralizer {β⁻¹ * α * β}) = ⊥) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  set φ := MulAut.conj β⁻¹ with hφ
  have hφα : φ α = β⁻¹ * α * β := by
    rw [hφ, MulAut.conj_apply, inv_inv]
  have hmap : (H ⊓ Subgroup.centralizer {α}).map φ.toMonoidHom =
      H.map φ.toMonoidHom ⊓ Subgroup.centralizer {β⁻¹ * α * β} := by
    rw [← hφα]
    ext x
    rw [Subgroup.mem_map_equiv, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_map_equiv,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro hx
      have := congrArg φ hx
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
    · intro hx
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hx]
  have e : ↥(H ⊓ Subgroup.centralizer {α}) ≃*
      ↥(H.map φ.toMonoidHom ⊓ Subgroup.centralizer {β⁻¹ * α * β}) :=
    (φ.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv e.symm h

theorem inner_conj_mem {G : Type*} [Group G] (β : MulAut G) {ι : MulAut G}
    (hι : ι ∈ OuterAutomorphisms.inner G) : β * ι * β⁻¹ ∈ OuterAutomorphisms.inner G := by
  obtain ⟨p, rfl⟩ := hι
  refine ⟨β p, ?_⟩
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
    MulAut.inv_apply]

end OmegaRadical

end CFSG.ComponentClassification.UnbalancedCatalog

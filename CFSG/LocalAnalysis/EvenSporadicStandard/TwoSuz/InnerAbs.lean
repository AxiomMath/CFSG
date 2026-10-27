module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Swap

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup Pointwise
open scoped commutatorElement

section SetupLemmas

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem Setup.exists_center (h : Setup G L z) : ∃ c ∈ center ↥L, (c : G) = z := by
  have hz : z ∈ (center L).map L.subtype := by
    rw [h.center_map]
    exact mem_zpowers z
  obtain ⟨c, hc, hcz⟩ := Subgroup.mem_map.1 hz
  exact ⟨c, hc, hcz⟩

theorem Setup.zmem (h : Setup G L z) : z ∈ L := by
  obtain ⟨c, -, rfl⟩ := h.exists_center
  exact c.2

theorem Setup.mul_comm_of_mem (h : Setup G L z) {l : G} (hl : l ∈ L) : l * z = z * l :=
  mem_centralizer_singleton_iff.1 (h.le_cent hl)

theorem Setup.mem_center (h : Setup G L z) : (⟨z, h.zmem⟩ : ↥L) ∈ center ↥L := by
  obtain ⟨c, hc, hcz⟩ := h.exists_center
  have : c = ⟨z, h.zmem⟩ := Subtype.ext hcz
  exact this ▸ hc

theorem Setup.commutator_cent_le (h : Setup G L z) :
    ⁅centralizer ({z} : Set G), centralizer ({z} : Set G)⁆ ≤ L := by
  set D := centralizer ({z} : Set G)
  have : (L.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer h.cent_le_norm
  have hcard : Nat.card (↥D ⧸ L.subgroupOf D) ∣ 2 := by
    rw [← index_eq_card]
    exact h.relIndex_dvd
  have hsq : ∀ q : ↥D ⧸ L.subgroupOf D, q * q = 1 := fun q => by
    rw [← sq]
    exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_natCard q).trans hcard)
  have hcomm : ∀ a b : ↥D ⧸ L.subgroupOf D, a * b = b * a := fun a b => by
    calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (hsq (a * b))).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
        rw [inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]
  refine Subgroup.commutator_le.2 fun a ha b hb => ?_
  have h1 : QuotientGroup.mk' (L.subgroupOf D) ⁅(⟨a, ha⟩ : D), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  have h2 : ⁅(⟨a, ha⟩ : D), ⟨b, hb⟩⁆ ∈ L.subgroupOf D :=
    (QuotientGroup.eq_one_iff (N := L.subgroupOf D) _).1 h1
  exact h2

theorem Setup.le_of_perfect (h : Setup G L z) {P : Subgroup G}
    (hP : P ≤ centralizer ({z} : Set G)) (hperf : P ≤ ⁅P, P⁆) : P ≤ L :=
  hperf.trans ((Subgroup.commutator_mono hP hP).trans h.commutator_cent_le)

theorem Setup.centralizes_of_perfect (h : Setup G L z) {P : Subgroup G} (hPL : P ≤ L)
    (hperf : P ≤ ⁅P, P⁆) {y : G} (_hy : y ∈ centralizer ({z} : Set G))
    (hcomm : ∀ p ∈ P, y * p * y⁻¹ * p⁻¹ ∈ zpowers z) : P ≤ centralizer ({y} : Set G) := by
  have hc : ∀ u ∈ zpowers z, ∀ p ∈ P, p * u = u * p := by
    intro u hu p hp
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hu
    exact (Commute.zpow_right (h.mul_comm_of_mem (hPL hp)) k).eq
  let κ : P →* zpowers z :=
    { toFun := fun p => ⟨y * p * y⁻¹ * (p : G)⁻¹, hcomm p p.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p q => Subtype.ext (by
        have hq : (p : G) * (y * q * y⁻¹ * (q : G)⁻¹) * (p : G)⁻¹ = y * q * y⁻¹ * (q : G)⁻¹ := by
          rw [hc _ (hcomm q q.2) p p.2]
          group
        calc y * ((p * q : P) : G) * y⁻¹ * ((p * q : P) : G)⁻¹
            = (y * p * y⁻¹ * (p : G)⁻¹) * ((p : G) * (y * q * y⁻¹ * (q : G)⁻¹) * (p : G)⁻¹) := by
              simp only [Subgroup.coe_mul]
              group
          _ = (y * p * y⁻¹ * (p : G)⁻¹) * (y * q * y⁻¹ * (q : G)⁻¹) := by rw [hq]) }
  intro p hp
  have hmem : (⟨p, hp⟩ : P) ∈ commutator P := by
    have : p ∈ (commutator P).map P.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hperf hp
    obtain ⟨q, hq, hqp⟩ := Subgroup.mem_map.1 this
    exact (Subtype.ext hqp : q = ⟨p, hp⟩) ▸ hq
  have h1 : κ ⟨p, hp⟩ = 1 := MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker κ hmem)
  have h2 : y * p * y⁻¹ = p := mul_inv_eq_one.1 (congrArg Subtype.val h1)
  rw [mem_centralizer_singleton_iff]
  calc p * y = y * p * y⁻¹ * y := by rw [h2]
    _ = y * p := by group

end SetupLemmas

section Counting

@[expose] noncomputable def rootCount {Λ : Type*} [Group Λ] (S : Subgroup Λ) (c : Λ) : ℕ :=
  Set.ncard {w : Λ | w ∈ S ∧ w * w = c}

@[expose] def InnerData (Λ : Type*) [Group Λ] (z : Λ) : Prop :=
  ∃ (S J : Subgroup Λ) (x₁ x₂ : Λ), Nat.card S = 2 ^ 14 ∧ z ∈ S ∧ S ≤ J ∧ x₁ ∈ S ∧ x₂ ∈ S ∧
    (∀ j ∈ J, j * x₁ = x₁ * j) ∧ (∀ j ∈ J, j * x₂ = x₂ * j) ∧ J ≤ ⁅J, J⁆ ∧
    (∀ s ∈ S, s * s = 1 → s ≠ 1 → s ≠ z → ∃ g : Λ, g * s * g⁻¹ = x₁ ∨ g * s * g⁻¹ = x₂) ∧
    rootCount S z = 1056 ∧ rootCount S x₁ ≠ 1056 ∧ rootCount S x₂ ≠ 1056

theorem rootCount_map {Λ Λ' : Type*} [Group Λ] [Group Λ'] {φ : Λ →* Λ'}
    (hφ : Function.Injective φ) (S : Subgroup Λ) (c : Λ) :
    rootCount (S.map φ) (φ c) = rootCount S c := by
  unfold rootCount
  rw [← Set.ncard_image_of_injective _ hφ]
  congr 1
  ext w
  constructor
  · rintro ⟨hw, hww⟩
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hw
    exact ⟨s, ⟨hs, hφ (by rwa [map_mul])⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hss⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem φ hs, by rw [← map_mul, hss]⟩

theorem perfect_map {A B : Type*} [Group A] [Group B] (φ : A →* B) {P : Subgroup A}
    (hP : P ≤ ⁅P, P⁆) : P.map φ ≤ ⁅P.map φ, P.map φ⁆ := by
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono hP

theorem factorization_order_twoSuz : (896690995200 : ℕ).factorization 2 = 14 := by
  rw [Nat.factorization_def _ Nat.prime_two]
  have : (896690995200 : ℕ) = 2 ^ 14 * 54729675 := by norm_num
  rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]

end Counting

section Sylow

variable {Λ : Type*} [Group Λ] [Finite Λ]

theorem exists_conj_sylow {S : Subgroup Λ} (hS : Nat.card S = 2 ^ (Nat.card Λ).factorization 2)
    (Q : Sylow 2 Λ) : ∃ g : Λ, ∀ x : Λ, x ∈ (Q : Subgroup Λ) ↔ g⁻¹ * x * g ∈ S := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Λ (Sylow.ofCard S hS) Q
  refine ⟨g, fun x => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem exists_conj_of_card {P Q : Subgroup Λ}
    (hP : Nat.card P = 2 ^ (Nat.card Λ).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card Λ).factorization 2) :
    ∃ g : Λ, ∀ x : Λ, x ∈ Q ↔ g⁻¹ * x * g ∈ P :=
  exists_conj_sylow hP (Sylow.ofCard Q hQ)

theorem rootCount_eq_of_card {z : Λ} (hz : ∀ g : Λ, g * z = z * g) {P Q : Subgroup Λ}
    (hP : Nat.card P = 2 ^ (Nat.card Λ).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card Λ).factorization 2) : rootCount P z = rootCount Q z := by
  obtain ⟨g, hg⟩ := exists_conj_of_card hP hQ
  have hmap : P.map (MulAut.conj g).toMonoidHom = Q := by
    ext x
    rw [hg x, Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [mul_assoc] using hs
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp [mul_assoc]⟩
  have hgz : (MulAut.conj g).toMonoidHom z = z := by
    simp [MulAut.conj_apply, hz g]
  have := rootCount_map (φ := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective P z
  rw [hgz, hmap] at this
  exact this.symm

theorem exists_conj_mem {S : Subgroup Λ} (hS : Nat.card S = 2 ^ (Nat.card Λ).factorization 2)
    {u : Λ} (hu : u * u = 1) : ∃ g : Λ, g⁻¹ * u * g ∈ S := by
  have h2 : IsPGroup 2 (zpowers u) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    simpa using orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
  obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conj_sylow hS Q
  exact ⟨g, (hg u).1 (hQ (mem_zpowers u))⟩

theorem exists_conj_eq {S : Subgroup Λ} {z x₁ x₂ : Λ} (hz : ∀ g : Λ, g * z = z * g)
    (hS : Nat.card S = 2 ^ (Nat.card Λ).factorization 2)
    (hcover : ∀ s ∈ S, s * s = 1 → s ≠ 1 → s ≠ z → ∃ g : Λ, g * s * g⁻¹ = x₁ ∨ g * s * g⁻¹ = x₂)
    {u : Λ} (hu : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ c : Λ, c * x₁ * c⁻¹ = u ∨ c * x₂ * c⁻¹ = u := by
  obtain ⟨g, hg⟩ := exists_conj_mem hS hu
  have hu' : u = g * (g⁻¹ * u * g) * g⁻¹ := by group
  have hs2 : g⁻¹ * u * g * (g⁻¹ * u * g) = 1 := by
    calc g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu]; group
  have hs1 : g⁻¹ * u * g ≠ 1 := fun h1 => hu1 (by rw [hu', h1]; group)
  have hsz : g⁻¹ * u * g ≠ z := fun h1 => huz (by rw [hu', h1, hz g]; group)
  obtain ⟨k, hk⟩ := hcover _ hg hs2 hs1 hsz
  refine ⟨g * k⁻¹, ?_⟩
  rcases hk with hk | hk
  · left
    calc g * k⁻¹ * x₁ * (g * k⁻¹)⁻¹ = g * k⁻¹ * (k * (g⁻¹ * u * g) * k⁻¹) * (g * k⁻¹)⁻¹ := by
          rw [hk]
      _ = u := by group
  · right
    calc g * k⁻¹ * x₂ * (g * k⁻¹)⁻¹ = g * k⁻¹ * (k * (g⁻¹ * u * g) * k⁻¹) * (g * k⁻¹)⁻¹ := by
          rw [hk]
      _ = u := by group

end Sylow

section Data

variable {Λ : Type*} [Group Λ]

theorem exists_conj_data {z x u c : Λ} (hcz : c * z = z * c) (hcx : c * x * c⁻¹ = u)
    {S J : Subgroup Λ} (hzS : z ∈ S) (hSJ : S ≤ J) (hxS : x ∈ S)
    (hJx : ∀ j ∈ J, j * x = x * j) (hJ : J ≤ ⁅J, J⁆) (hz : rootCount S z = 1056)
    (hx : rootCount S x ≠ 1056) :
    ∃ S' J' : Subgroup Λ, Nat.card S' = Nat.card S ∧ z ∈ S' ∧ S' ≤ J' ∧ u ∈ S' ∧
      (∀ j ∈ J', j * u = u * j) ∧ J' ≤ ⁅J', J'⁆ ∧ rootCount S' z = 1056 ∧
      rootCount S' u ≠ 1056 := by
  have hφinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hφz : (MulAut.conj c).toMonoidHom z = z := by
    simp [MulAut.conj_apply, hcz]
  have hφx : (MulAut.conj c).toMonoidHom x = u := hcx
  refine ⟨S.map (MulAut.conj c).toMonoidHom, J.map (MulAut.conj c).toMonoidHom,
    Subgroup.card_map_of_injective hφinj, ⟨z, hzS, hφz⟩, Subgroup.map_mono hSJ,
    ⟨x, hxS, hφx⟩, ?_, perfect_map _ hJ, ?_, ?_⟩
  · rintro _ ⟨j, hj, rfl⟩
    rw [← hφx, ← map_mul, ← map_mul, hJx j hj]
  · have := rootCount_map hφinj S z
    rw [hφz] at this
    exact this.trans hz
  · have := rootCount_map hφinj S x
    rw [hφx] at this
    exact this ▸ hx

variable [Finite Λ]

theorem InnerData.exists_at {z : Λ} (hz : ∀ g : Λ, g * z = z * g)
    (hcard : Nat.card Λ = 896690995200) (hd : InnerData Λ z) {u : Λ} (hu : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) :
    ∃ S J : Subgroup Λ, Nat.card S = 2 ^ 14 ∧ z ∈ S ∧ S ≤ J ∧ u ∈ S ∧
      (∀ j ∈ J, j * u = u * j) ∧ J ≤ ⁅J, J⁆ ∧ rootCount S z = 1056 ∧ rootCount S u ≠ 1056 := by
  obtain ⟨S, J, x₁, x₂, hS, hzS, hSJ, hx₁, hx₂, hJ₁, hJ₂, hJ, hcover, h1056, hr₁, hr₂⟩ := hd
  have hS' : Nat.card S = 2 ^ (Nat.card Λ).factorization 2 := by
    rw [hcard, factorization_order_twoSuz, hS]
  obtain ⟨c, hc | hc⟩ := exists_conj_eq hz hS' hcover hu hu1 huz
  · obtain ⟨S', J', hcS, h⟩ := exists_conj_data (hz c) hc hzS hSJ hx₁ hJ₁ hJ h1056 hr₁
    exact ⟨S', J', hcS.trans hS, h⟩
  · obtain ⟨S', J', hcS, h⟩ := exists_conj_data (hz c) hc hzS hSJ hx₂ hJ₂ hJ h1056 hr₂
    exact ⟨S', J', hcS.trans hS, h⟩

end Data

section Transport

variable {G : Type*} [Group G] {A B : Subgroup G}

@[expose] def isoHom (f : A ≃* B) : A →* G := B.subtype.comp f.toMonoidHom

theorem isoHom_injective (f : A ≃* B) : Function.Injective (isoHom f) :=
  B.subtype_injective.comp f.injective

@[expose] def isoImage (f : A ≃* B) (P : Subgroup G) : Subgroup G :=
  (P.subgroupOf A).map (isoHom f)

theorem isoImage_le (f : A ≃* B) (P : Subgroup G) : isoImage f P ≤ B := by
  rintro _ ⟨a, -, rfl⟩
  exact (f a).2

theorem isoImage_mono (f : A ≃* B) {P Q : Subgroup G} (h : P ≤ Q) :
    isoImage f P ≤ isoImage f Q :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem mem_isoImage (f : A ≃* B) {P : Subgroup G} {a : G} (ha : a ∈ A) (hP : a ∈ P) :
    (f ⟨a, ha⟩ : G) ∈ isoImage f P :=
  ⟨⟨a, ha⟩, hP, rfl⟩

theorem card_isoImage (f : A ≃* B) {P : Subgroup G} (hPA : P ≤ A) :
    Nat.card (isoImage f P) = Nat.card P := by
  rw [isoImage, Subgroup.card_map_of_injective (isoHom_injective f)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA).toEquiv

theorem isoImage_perfect (f : A ≃* B) {P : Subgroup G} (hPA : P ≤ A) (hP : P ≤ ⁅P, P⁆) :
    isoImage f P ≤ ⁅isoImage f P, isoImage f P⁆ := by
  refine perfect_map _ ?_
  rw [← Subgroup.map_le_map_iff_of_injective A.subtype_injective, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hPA]
  exact hP

theorem rootCount_isoImage (f : A ≃* B) {P : Subgroup G} (hPA : P ≤ A) {a : G} (ha : a ∈ A) :
    rootCount (isoImage f P) (f ⟨a, ha⟩ : G) = rootCount P a := by
  have h1 := rootCount_map (isoHom_injective f) (P.subgroupOf A) ⟨a, ha⟩
  have h2 := rootCount_map A.subtype_injective (P.subgroupOf A) ⟨a, ha⟩
  rw [Subgroup.map_subgroupOf_eq_of_le hPA] at h2
  exact h1.trans h2.symm

theorem exists_perfect_image (f : A ≃* B) {P : Subgroup G} (hPA : P ≤ A) (hP : P ≤ ⁅P, P⁆)
    {a : G} (ha : a ∈ P) :
    ∃ Q : Subgroup G, Q ≤ B ∧ Q ≤ ⁅Q, Q⁆ ∧ (f ⟨a, hPA ha⟩ : G) ∈ Q :=
  ⟨isoImage f P, isoImage_le f P, isoImage_perfect f hPA hP, mem_isoImage f (hPA ha) ha⟩

variable [Finite G]

theorem rootCount_eq_of_card_le {L : Subgroup G} {z : G} (hzL : z ∈ L)
    (hz : ∀ l ∈ L, l * z = z * l) {P Q : Subgroup G} (hPL : P ≤ L) (hQL : Q ≤ L)
    (hP : Nat.card P = 2 ^ (Nat.card L).factorization 2)
    (hQ : Nat.card Q = 2 ^ (Nat.card L).factorization 2) : rootCount P z = rootCount Q z := by
  have hc : ∀ {R : Subgroup G}, R ≤ L → Nat.card R = 2 ^ (Nat.card L).factorization 2 →
      Nat.card (R.subgroupOf L) = 2 ^ (Nat.card L).factorization 2 := fun hR h' => by
    rw [← h']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hzc : ∀ g : ↥L, g * (⟨z, hzL⟩ : ↥L) = ⟨z, hzL⟩ * g := fun g => Subtype.ext (hz g g.2)
  have hmap : ∀ R : Subgroup G, R ≤ L →
      rootCount R z = rootCount (R.subgroupOf L) ⟨z, hzL⟩ := fun R hR => by
    have := rootCount_map L.subtype_injective (R.subgroupOf L) ⟨z, hzL⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hR] at this
  rw [hmap P hPL, hmap Q hQL, rootCount_eq_of_card hzc (hc hPL hP) (hc hQL hQ)]

end Transport

section Main

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem exists_inner_at (h : Setup G L z) (hcard : Nat.card L = 896690995200)
    (hd : InnerData ↥L (⟨z, h.zmem⟩ : ↥L)) {y : G} (hy : y ∈ L) (hy2 : y * y = 1)
    (hy1 : y ≠ 1) (hyz : y ≠ z) :
    ∃ S J : Subgroup G, Nat.card S = 2 ^ 14 ∧ S ≤ J ∧ J ≤ L ∧ z ∈ S ∧ y ∈ S ∧
      (∀ j ∈ J, j * y = y * j) ∧ J ≤ ⁅J, J⁆ ∧ rootCount S z = 1056 ∧ rootCount S y ≠ 1056 := by
  have hz : ∀ g : ↥L, g * (⟨z, h.zmem⟩ : ↥L) = ⟨z, h.zmem⟩ * g :=
    Subgroup.mem_center_iff.1 h.mem_center
  obtain ⟨S, J, hS, hzS, hSJ, hyS, hJy, hJ, h1056, hne⟩ :=
    InnerData.exists_at hz hcard hd (u := ⟨y, hy⟩) (Subtype.ext hy2)
      (fun h' => hy1 (congrArg Subtype.val h')) (fun h' => hyz (congrArg Subtype.val h'))
  refine ⟨S.map L.subtype, J.map L.subtype, ?_, Subgroup.map_mono hSJ, Subgroup.map_subtype_le J,
    ⟨⟨z, h.zmem⟩, hzS, rfl⟩, ⟨⟨y, hy⟩, hyS, rfl⟩, ?_, perfect_map _ hJ, ?_, ?_⟩
  · rwa [Subgroup.card_map_of_injective L.subtype_injective]
  · rintro _ ⟨j, hj, rfl⟩
    exact congrArg Subtype.val (hJy j hj)
  · exact (rootCount_map L.subtype_injective S ⟨z, h.zmem⟩).trans h1056
  · intro h'
    exact hne ((rootCount_map L.subtype_injective S ⟨y, hy⟩).symm.trans h')

theorem exists_perfect_of_innerData (hcard : Nat.card L = 896690995200) (h : Setup G L z)
    (hd : InnerData ↥L (⟨z, h.zmem⟩ : ↥L)) {y : G} (hy : y ∈ L) (hy2 : y * y = 1) (hy1 : y ≠ 1)
    (hyz : y ≠ z) :
    ∃ P : Subgroup G, P ≤ L ∧ P ≤ centralizer ({y} : Set G) ∧ P ≤ ⁅P, P⁆ ∧ z ∈ P := by
  obtain ⟨S, J, -, hSJ, hJL, hzS, -, hJy, hJ, -, -⟩ := exists_inner_at h hcard hd hy hy2 hy1 hyz
  exact ⟨J, hJL, fun j hj => mem_centralizer_singleton_iff.2 (hJy j hj), hJ, hSJ hzS⟩

theorem twoSuzNoSwapInner_of_data
    (hcard : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
      Nat.card L = 896690995200)
    (hdata : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G) (h : Setup G L z),
      InnerData ↥L (⟨z, h.zmem⟩ : ↥L)) : TwoSuzNoSwapInner := by
  intro G _ _ L z h x z' hxL _ _ _ hx2 _ hxz _ f hxm _ hfx _
  have hx1 : x ≠ 1 := fun h1 => by simp [h1] at hx2
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  obtain ⟨S, J, hS, hSJ, hJL, -, hxS, hJx, hJ, h1056, hne⟩ :=
    exists_inner_at h (hcard G L z h) (hdata G L z h) hxL hxx hx1 hxz
  have hJA : J ≤ centralizer ({z} : Set G) ⊓ centralizer ({x} : Set G) := fun j hj =>
    mem_comm_pair.2 ⟨h.mul_comm_of_mem (hJL hj), hJx j hj⟩
  have hSA := hSJ.trans hJA
  have hTL : isoImage f J ≤ L :=
    h.le_of_perfect ((isoImage_le f J).trans inf_le_left) (isoImage_perfect f hJA hJ)
  have hcS : Nat.card S = 2 ^ (Nat.card L).factorization 2 := by
    rw [hcard G L z h, factorization_order_twoSuz, hS]
  have hcT : Nat.card (isoImage f S) = 2 ^ (Nat.card L).factorization 2 := by
    rw [card_isoImage f hSA, hcS]
  have hroot : rootCount (isoImage f S) z = rootCount S x := by
    have := rootCount_isoImage f hSA (hSA hxS)
    rwa [show (f ⟨x, hSA hxS⟩ : G) = z from hfx] at this
  have hsyl := rootCount_eq_of_card_le h.zmem (fun l hl => h.mul_comm_of_mem hl)
    ((isoImage_mono f hSJ).trans hTL) (hSJ.trans hJL) hcT hcS
  exact hne (hroot.symm.trans (hsyl.trans h1056))

theorem Setup.noSwap_of_perfect (h : Setup G L z)
    (hP : ∀ y : G, y ∈ centralizer ({z} : Set G) → orderOf y = 2 → y ≠ z →
      ∃ P : Subgroup G, P ≤ centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ∧
        P ≤ ⁅P, P⁆ ∧ z ∈ P)
    {x z' : G} (hnot : ¬ (x ∈ L ∧ z' ∈ L)) (hxD : x ∈ centralizer ({z} : Set G))
    (hz'D : z' ∈ centralizer ({z} : Set G)) (hx2 : orderOf x = 2) (hz'2 : orderOf z' = 2)
    (hxz : x ≠ z) (hz'z : z' ≠ z) : NoSwap z x z' := by
  intro f hxm _ hfx hfz
  refine hnot ⟨?_, ?_⟩
  · obtain ⟨P, hPB, hPperf, hzP⟩ := hP z' hz'D hz'2 hz'z
    obtain ⟨Q, hQA, hQperf, hxQ⟩ := exists_perfect_image f.symm hPB hPperf hzP
    have hsymm : f.symm ⟨z, hPB hzP⟩ = ⟨x, hxm⟩ := f.symm_apply_eq.2 (Subtype.ext hfx.symm)
    rw [hsymm] at hxQ
    exact h.le_of_perfect (hQA.trans inf_le_left) hQperf hxQ
  · obtain ⟨P, hPA, hPperf, hzP⟩ := hP x hxD hx2 hxz
    obtain ⟨Q, hQB, hQperf, hz'Q⟩ := exists_perfect_image f hPA hPperf hzP
    exact h.le_of_perfect (hQB.trans inf_le_left) hQperf (hfz ▸ hz'Q)

theorem twoSuzNoSwapOuter_of_perfect
    (hP : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
      ∀ y : G, y ∈ centralizer ({z} : Set G) → orderOf y = 2 → y ≠ z →
        ∃ P : Subgroup G, P ≤ centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ∧
          P ≤ ⁅P, P⁆ ∧ z ∈ P) :
    TwoSuzNoSwapOuter := by
  intro G _ _ L z h x z' hnot hxD hz'D hx2 hz'2 hxz hz'z
  exact h.noSwap_of_perfect (hP G L z h) hnot hxD hz'D hx2 hz'2 hxz hz'z

@[expose] def TwoSuzNoSwapOuter' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
    centralizer (L : Set G) = zpowers z →
    ∀ x z' : G, ¬ (x ∈ L ∧ z' ∈ L) → x ∈ centralizer ({z} : Set G) →
      z' ∈ centralizer ({z} : Set G) → orderOf x = 2 → orderOf z' = 2 → x ≠ z → z' ≠ z →
      NoSwap z x z'

theorem twoSuzNoSwapOuter'_of_perfect
    (hP : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z : G), Setup G L z →
      centralizer (L : Set G) = zpowers z → ∀ y : G, y ∈ centralizer ({z} : Set G) →
        orderOf y = 2 → y ≠ z → ∃ P : Subgroup G,
          P ≤ centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G) ∧ P ≤ ⁅P, P⁆ ∧ z ∈ P) :
    TwoSuzNoSwapOuter' := by
  intro G _ _ L z h hcent x z' hnot hxD hz'D hx2 hz'2 hxz hz'z
  exact h.noSwap_of_perfect (hP G L z h hcent) hnot hxD hz'D hx2 hz'2 hxz hz'z

end Main

end CFSG.EvenSporadicStandard.TwoSuz

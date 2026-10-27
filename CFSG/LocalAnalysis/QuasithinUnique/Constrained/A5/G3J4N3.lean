module

public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4.QT2LocMain
public import CFSG.Sporadic.J4.QT2AGen

public section

namespace CFSG.QuasithinUnique.A5.G3.J4N3

open CFSG.Blueprint CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A

section Abstract

variable {G : Type*} [Group G]

@[expose] def BoundOn (A : Subgroup G) : Prop :=
  ∀ {S : Subgroup G}, IsPGroup 2 ↥S → S ≤ A → ∀ {y : G}, y ∈ A → orderOf y = 3 →
    (∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) → Nat.card ↥S ≤ 2 ^ 15

theorem conj_normalize {S : Subgroup G} (hS : IsPGroup 2 ↥S) {y z η g : G} (hg : g * η * g⁻¹ = z)
    (hy3 : orderOf y = 3) (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y)
    (hzc : ∀ s ∈ S, s * z = z * s) (hyz : y * z = z * y) :
    ∃ (S' : Subgroup G) (y' : G), IsPGroup 2 ↥S' ∧ Nat.card ↥S' = Nat.card ↥S ∧
      (∀ s ∈ S', s * η = η * s) ∧ y' * η = η * y' ∧ orderOf y' = 3 ∧
      ∀ s ∈ S', s * y' * s⁻¹ ∈ Subgroup.zpowers y' := by
  have hη : η = g⁻¹ * z * g := by rw [← hg]; group
  let φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom
  have hφ : ∀ x, φ x = g⁻¹ * x * g := fun x => by
    simp [φ]
  have hinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  let e := S.equivMapOfInjective φ hinj
  refine ⟨S.map φ, g⁻¹ * y * g, hS.of_equiv e, (Nat.card_congr e.toEquiv).symm, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    rw [hφ, hη]
    calc g⁻¹ * s * g * (g⁻¹ * z * g) = g⁻¹ * (s * z) * g := by group
      _ = g⁻¹ * (z * s) * g := by rw [hzc s hs]
      _ = g⁻¹ * z * g * (g⁻¹ * s * g) := by group
  · rw [hη]
    calc g⁻¹ * y * g * (g⁻¹ * z * g) = g⁻¹ * (y * z) * g := by group
      _ = g⁻¹ * (z * y) * g := by rw [hyz]
      _ = g⁻¹ * z * g * (g⁻¹ * y * g) := by group
  · have := orderOf_injective φ hinj y
    rw [hφ] at this
    rw [this, hy3]
  · rintro _ ⟨s, hs, rfl⟩
    have h1 : φ (s * y * s⁻¹) ∈ (Subgroup.zpowers y).map φ := Subgroup.mem_map_of_mem φ (hSy s hs)
    rw [MonoidHom.map_zpowers, hφ] at h1
    have h2 : φ s * (g⁻¹ * y * g) * (φ s)⁻¹ = φ (s * y * s⁻¹) := by
      rw [map_mul, map_mul, map_inv, hφ y]
    rw [h2]
    simpa [hφ] using h1

variable [Finite G]

theorem no_big_two_group_abs (η₁ η₃ : G) (A : Subgroup G)
    (hconj : ∀ r : G, r * r = 1 → r ≠ 1 → IsConj η₁ r ∨ IsConj η₃ r)
    (hA : ∀ x : G, x * η₁ = η₁ * x → x ∈ A) (hT : BoundOn A)
    (hZ : BoundOn (Subgroup.centralizer ({η₃} : Set G))) {S : Subgroup G} (hS : IsPGroup 2 ↥S)
    (hcard : 2 ^ 16 ≤ Nat.card ↥S) {y : G} (hy3 : orderOf y = 3)
    (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) : False := by
  have h0 : Nat.card ↥S ≤ 2 * Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ S) :=
    card_le_two_mul_centralizer S y hy3 hSy
  have h16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have h15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  have hne : Subgroup.centralizer ({y} : Set G) ⊓ S ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥(Subgroup.centralizer ({y} : Set G) ⊓ S) = 1 := by
      rw [h]
      exact Subgroup.card_bot
    rw [h1] at h0
    omega
  have hn : ∀ s ∈ S, ∀ x ∈ Subgroup.centralizer ({y} : Set G) ⊓ S,
      s * x * s⁻¹ ∈ Subgroup.centralizer ({y} : Set G) ⊓ S := by
    intro s hs x hx
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      S.mul_mem (S.mul_mem hs hx.2) (S.inv_mem hs)⟩
    have hxy : x * y = y * x := Subgroup.mem_centralizer_singleton_iff.1 hx.1
    have ht : s⁻¹ * y * s ∈ Subgroup.zpowers y := by simpa using hSy s⁻¹ (S.inv_mem hs)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 ht
    have hxt : x * (s⁻¹ * y * s) = (s⁻¹ * y * s) * x := by
      rw [← hn]
      exact (Commute.zpow_right hxy n).eq
    calc s * x * s⁻¹ * y = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by rw [hxt]
      _ = y * (s * x * s⁻¹) := by group
  obtain ⟨z, hz0, hz1, hz2, hzc⟩ :=
    exists_central_involution S (Subgroup.centralizer ({y} : Set G) ⊓ S) hS inf_le_right hn hne
  have hyz : y * z = z * y := (Subgroup.mem_centralizer_singleton_iff.1 hz0.1).symm
  rcases hconj z hz2 hz1 with hc | hc
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    obtain ⟨S', y', hS', hcard', hSc, hyc, hy3', hSy'⟩ := conj_normalize hS hg hy3 hSy hzc hyz
    have := hT hS' (fun s hs => hA s (hSc s hs)) (hA y' hyc) hy3' hSy'
    omega
  · obtain ⟨g, hg⟩ := isConj_iff.1 hc
    obtain ⟨S', y', hS', hcard', hSc, hyc, hy3', hSy'⟩ := conj_normalize hS hg hy3 hSy hzc hyz
    have hSC : S' ≤ Subgroup.centralizer ({η₃} : Set G) := fun s hs =>
      Subgroup.mem_centralizer_singleton_iff.2 (hSc s hs)
    have hyC : y' ∈ Subgroup.centralizer ({η₃} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hyc
    have := hZ hS' hSC hyC hy3' hSy'
    omega

theorem normalizer3_abs (η₁ η₃ : G) (A : Subgroup G)
    (hconj : ∀ r : G, r * r = 1 → r ≠ 1 → IsConj η₁ r ∨ IsConj η₃ r)
    (hA : ∀ x : G, x * η₁ = η₁ * x → x ∈ A) (hT : BoundOn A)
    (hZ : BoundOn (Subgroup.centralizer ({η₃} : Set G))) (P N : Subgroup G)
    (hP : Nat.card ↥P = 3) (hN : N ≤ Subgroup.normalizer (P : Set G)) :
    ¬ 2 ^ 16 ∣ Nat.card ↥N := by
  intro h16
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥N) 2 h16
  have hScard : Nat.card ↥(K.map N.subtype) = 2 ^ 16 := by
    rw [← hK]
    exact (Nat.card_congr (K.equivMapOfInjective N.subtype N.subtype_injective).toEquiv).symm
  have hS2 : IsPGroup 2 ↥(K.map N.subtype) := IsPGroup.of_card hScard
  have hSN : K.map N.subtype ≤ N := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 (by rw [hP])
  set y : G := (y₀ : G) with hy
  have hy3 : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe]; exact hy₀
  have hyP : y ∈ P := y₀.2
  have hPy : Subgroup.zpowers y = P := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hyP)
    rw [hP, Nat.card_zpowers, hy3]
  have hSy : ∀ s ∈ K.map N.subtype, s * y * s⁻¹ ∈ Subgroup.zpowers y := by
    intro s hs
    rw [hPy]
    exact ((Subgroup.mem_normalizer_iff.1 (hN (hSN hs))) y).1 hyP
  exact no_big_two_group_abs η₁ η₃ A hconj hA hT hZ hS2 (by rw [hScard]) hy3 hSy

end Abstract

theorem normalizer3_of_equiv_sub {X M : Type*} [Group X] [Group M] (H : Subgroup M) (φ : X ≃* H)
    (h : ∀ P N : Subgroup H, Nat.card ↥P = 3 → N ≤ Subgroup.normalizer (P : Set H) →
      ¬ 2 ^ 16 ∣ Nat.card ↥N)
    (P N : Subgroup X) (hP : Nat.card ↥P = 3) (hN : N ≤ Subgroup.normalizer (P : Set X)) :
    ¬ 2 ^ 16 ∣ Nat.card ↥N := by
  intro h16
  refine h (P.map φ.toMonoidHom) (N.map φ.toMonoidHom) ?_ ?_ ?_
  · exact (Nat.card_congr (P.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm.trans hP
  · rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h'
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
    have e : φ.symm (φ.toMonoidHom n * h' * (φ.toMonoidHom n)⁻¹) = n * φ.symm h' * n⁻¹ := by
      simp
    rw [e]
    exact Subgroup.mem_normalizer_iff.1 (hN hn) (φ.symm h')
  · rwa [(Nat.card_congr (N.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm]

@[expose] def BoundT : Prop := BoundOn Hj

@[expose] def BoundZ : Prop := BoundOn (Subgroup.centralizer ({eta uJ 11 3} : Set J))

theorem normalizer3_J
    (hT : BoundT) (hZ : BoundZ) (P N : Subgroup J) (hP : Nat.card ↥P = 3)
    (hN : N ≤ Subgroup.normalizer (P : Set J)) : ¬ 2 ^ 16 ∣ Nat.card ↥N :=
  normalizer3_abs (eta uJ 11 1) (eta uJ 11 3) Hj
    (fun _ h1 h2 => inv_conj_root CFSG.Sporadic.J4.j4Facts h1 h2)
    (fun _ hx => CFSG.Sporadic.J4.QT2.centralizer_eta_one_le_Hj hx) hT hZ P N hP hN

theorem normalizer3_of_equiv_carrier
    (f : NativeSporadic.Carrier .J4 ≃* J) (hT : BoundT)
    (hZ : BoundZ) {X : Type} [Group X] (hX : Nonempty (X ≃* NativeSporadic.Carrier .J4))
    (P N : Subgroup X) (hP : Nat.card ↥P = 3) (hN : N ≤ Subgroup.normalizer (P : Set X)) :
    ¬ 2 ^ 16 ∣ Nat.card ↥N := by
  obtain ⟨e⟩ := hX
  exact normalizer3_of_equiv_sub J (e.trans f) (normalizer3_J hT hZ) P N hP hN

theorem normalizer3_of_bounds
    (hT : BoundT) (hZ : BoundZ) {X : Type} [Group X]
    (hX : Nonempty (X ≃* NativeSporadic.Carrier .J4)) (P N : Subgroup X) (hP : Nat.card ↥P = 3)
    (hN : N ≤ Subgroup.normalizer (P : Set X)) : ¬ 2 ^ 16 ∣ Nat.card ↥N :=
  normalizer3_of_equiv_carrier (seedEquiv CFSG.Sporadic.J4.j4Facts.mat) hT hZ hX P N hP hN

end CFSG.QuasithinUnique.A5.G3.J4N3

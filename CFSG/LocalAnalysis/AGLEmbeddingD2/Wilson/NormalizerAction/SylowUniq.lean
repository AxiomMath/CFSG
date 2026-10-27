module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped commutatorElement

section Aux

variable {G : Type*} [Group G]

private lemma comm_of_mem_zpowers {z q w : G} (hq : q * z = z * q) (hw : w ∈ zpowers z) :
    q * w = w * q := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_right (show Commute q z from hq) k).eq

private lemma comm_zpowers {z a b : G} (ha : a ∈ zpowers z) (hb : b ∈ zpowers z) :
    a * b = b * a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
  obtain ⟨l, rfl⟩ := mem_zpowers_iff.mp hb
  rw [← zpow_add, ← zpow_add, add_comm]

lemma exists_commHom (Q : Subgroup G) (z u : G)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q)
    (huQ : u ∈ Q) :
    ∃ φ : Q →* zpowers z, ∀ q : Q, (φ q : G) = ⁅(q : G), u⁆ := by
  refine ⟨{ toFun := fun q => ⟨⁅(q : G), u⁆, hcQ _ q.2 _ huQ⟩
            map_one' := by ext; simp
            map_mul' := fun q q' => ?_ }, fun _ => rfl⟩
  apply Subtype.ext
  have hw' : ⁅(q' : G), u⁆ ∈ zpowers z := hcQ _ q'.2 _ huQ
  have h1 : ⁅((q * q' : Q) : G), u⁆ =
      (q : G) * ⁅(q' : G), u⁆ * (q : G)⁻¹ * ⁅(q : G), u⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul]; group
  have h2 : (q : G) * ⁅(q' : G), u⁆ * (q : G)⁻¹ = ⁅(q' : G), u⁆ := by
    rw [comm_of_mem_zpowers (hzc _ q.2) hw', mul_inv_cancel_right]
  change ⁅((q * q' : Q) : G), u⁆ = ⁅(q : G), u⁆ * ⁅(q' : G), u⁆
  rw [h1, h2]
  exact comm_zpowers hw' (hcQ _ q.2 _ huQ)

lemma exists_commHom_surjective [Finite G] (Q : Subgroup G) (z u : G) (hz : orderOf z = 11)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hZQ : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ zpowers z)
    (huQ : u ∈ Q) (hu : u ∉ zpowers z) :
    ∃ φ : Q →* zpowers z, (∀ q : Q, (φ q : G) = ⁅(q : G), u⁆) ∧ Function.Surjective φ := by
  obtain ⟨φ, hφ⟩ := exists_commHom Q z u hcQ hzc huQ
  refine ⟨φ, hφ, ?_⟩
  have : Fact (Nat.card (zpowers z)).Prime := ⟨by rw [Nat.card_zpowers, hz]; norm_num⟩
  have hne : φ.range ≠ ⊥ := by
    intro h
    apply hu
    apply hZQ u huQ
    intro a ha
    have h1 : φ ⟨a, ha⟩ = 1 := by
      have : φ ⟨a, ha⟩ ∈ φ.range := ⟨_, rfl⟩
      rw [h] at this
      simpa using this
    have h2 : ⁅a, u⁆ = 1 := by
      have := congrArg (fun x : zpowers z => (x : G)) h1
      simpa [hφ] using this
    rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  rcases φ.range.eq_bot_or_eq_top_of_prime_card with h | h
  · exact absurd h hne
  · exact MonoidHom.range_eq_top.mp h

lemma card_centralizer_of_noncentral [Finite G] (Q : Subgroup G) (z u : G) (hz : orderOf z = 11)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hZQ : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ zpowers z)
    (huQ : u ∈ Q) (hu : u ∉ zpowers z) :
    Nat.card ↥(centralizer ({u} : Set G) ⊓ Q) = Nat.card Q / 11 := by
  obtain ⟨φ, hφ, hsurj⟩ := exists_commHom_surjective Q z u hz hcQ hzc hZQ huQ hu
  have h1 := card_ker_mul_card_of_surjective hsurj
  rw [Nat.card_zpowers, hz] at h1
  have h2 : Nat.card ↥(centralizer ({u} : Set G) ⊓ Q) = Nat.card φ.ker := by
    refine Nat.card_congr ⟨fun g => ⟨⟨g, g.2.2⟩, ?_⟩, fun q => ⟨q, ?_, q.1.2⟩, ?_, ?_⟩
    · have hg := mem_centralizer_singleton_iff.mp g.2.1
      ext
      rw [hφ, commutatorElement_def]
      change (g : G) * u * (g : G)⁻¹ * u⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact hg
    · have hq : φ q.1 = 1 := q.2
      have := congrArg (fun x : zpowers z => (x : G)) hq
      simp only [hφ, OneMemClass.coe_one] at this
      rw [commutatorElement_def, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
      exact mem_centralizer_singleton_iff.mpr this
    · intro g; rfl
    · intro q; rfl
  rw [h2]
  omega

end Aux

section Index

variable {G : Type*} [Group G] [Finite G]

lemma le_of_relIndex_le_two {A B C : Subgroup G} {n : ℕ} (hA : Nat.card A = 11 ^ n)
    (hAC : A ≤ C) (hidx : B.relIndex C ≤ 2) : A ≤ B := by
  have hne : B.relIndex C ≠ 0 := by
    intro h
    have := relIndex_mul_card (H := B) (K := C)
    rw [h] at this
    have := Nat.card_pos (α := C)
    omega
  have h1 : B.relIndex A ≤ B.relIndex C := relIndex_le_of_le_right hAC hne
  have h2 : B.relIndex A ∣ 11 ^ n := hA ▸ relIndex_dvd_card B A
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 11)).mp h2
  have hi0 : i = 0 := by
    by_contra hne
    have : 11 ≤ 11 ^ i := by
      calc 11 = 11 ^ 1 := by norm_num
        _ ≤ 11 ^ i := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hne)
    omega
  rw [hi0, pow_zero] at hi'
  exact relIndex_eq_one.mp hi'

omit [Finite G] in
lemma relIndex_le_two_of_card {B C : Subgroup G} (hBC : B ≤ C) (hB : Nat.card B = 121)
    (hC : Nat.card C ≤ 242) : B.relIndex C ≤ 2 := by
  have h := relIndex_mul_card (H := B) (K := C)
  rw [inf_of_le_left hBC, hB] at h
  omega

lemma centralizer_inf_eq_of_card {Q Q' : Subgroup G} {u : G}
    (hQ : Nat.card ↥(centralizer ({u} : Set G) ⊓ Q) = 121)
    (hQ' : Nat.card ↥(centralizer ({u} : Set G) ⊓ Q') = 121)
    (hC : Nat.card (centralizer ({u} : Set G)) ≤ 242) :
    centralizer ({u} : Set G) ⊓ Q = centralizer ({u} : Set G) ⊓ Q' := by
  refine le_antisymm ?_ ?_
  · exact le_of_relIndex_le_two (n := 2) (by simpa using hQ) inf_le_left
      (relIndex_le_two_of_card inf_le_left hQ' hC)
  · exact le_of_relIndex_le_two (n := 2) (by simpa using hQ') inf_le_left
      (relIndex_le_two_of_card inf_le_left hQ hC)

end Index

section Main

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private lemma conj_mem_centralizer_pair {Q : Subgroup G} {z u : G}
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q) (huQ : u ∈ Q)
    {q r : G} (hq : q ∈ Q) (hr : r ∈ centralizer ({u, z} : Set G)) :
    q * r * q⁻¹ ∈ centralizer ({u, z} : Set G) := by
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq] at hr ⊢
  obtain ⟨hru, hrz⟩ := hr
  have hw : ⁅q⁻¹, u⁆ ∈ zpowers z := hcQ _ (inv_mem hq) _ huQ
  obtain ⟨w, hwdef⟩ : ∃ w, w = ⁅q⁻¹, u⁆ := ⟨_, rfl⟩
  rw [← hwdef] at hw
  have hwu : w * u = q⁻¹ * u * q := by rw [hwdef, commutatorElement_def]; group
  have hrw : r * w = w * r := comm_of_mem_zpowers hrz.symm hw
  have hqz : q * z = z * q := hzc q hq
  have hqz' : q⁻¹ * z = z * q⁻¹ := hzc q⁻¹ (inv_mem hq)
  have hzq : z * (q * r * q⁻¹) = q * r * q⁻¹ * z := by
    calc z * (q * r * q⁻¹) = (z * q) * r * q⁻¹ := by group
      _ = (q * z) * r * q⁻¹ := by rw [hqz]
      _ = q * (z * r) * q⁻¹ := by group
      _ = q * (r * z) * q⁻¹ := by rw [hrz]
      _ = q * r * (z * q⁻¹) := by group
      _ = q * r * (q⁻¹ * z) := by rw [hqz']
      _ = q * r * q⁻¹ * z := by group
  refine ⟨?_, hzq⟩
  have e1 : u * (q * r * q⁻¹) = q * ((q⁻¹ * u * q) * r) * q⁻¹ := by group
  have e2 : q * r * q⁻¹ * u = q * (r * (q⁻¹ * u * q)) * q⁻¹ := by group
  rw [e1, e2, ← hwu]
  congr 2
  rw [mul_assoc, hru, ← mul_assoc, ← hrw, mul_assoc]

omit [Finite G] in
private lemma le_normalizer_centralizer_pair {Q : Subgroup G} {z u : G}
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q) (huQ : u ∈ Q) :
    Q ≤ normalizer (centralizer ({u, z} : Set G)) := by
  intro q hq
  rw [mem_normalizer_iff]
  intro r
  refine ⟨fun hr => conj_mem_centralizer_pair hcQ hzc huQ hq hr, fun hr => ?_⟩
  have := conj_mem_centralizer_pair hcQ hzc huQ (inv_mem hq) hr
  convert this using 1
  group

lemma exists_mul_mem_centralizer_pair (Q : Subgroup G) (z u : G) (hz : orderOf z = 11)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z) (hzc : ∀ q ∈ Q, q * z = z * q)
    (hZQ : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ zpowers z)
    (huQ : u ∈ Q) (hu : u ∉ zpowers z) {q' : G} (hq'z : q' * z = z * q')
    (hq'u : ⁅q', u⁆ ∈ zpowers z) :
    ∃ q ∈ Q, q⁻¹ * q' ∈ centralizer ({u, z} : Set G) := by
  obtain ⟨φ, hφ, hsurj⟩ := exists_commHom_surjective Q z u hz hcQ hzc hZQ huQ hu
  obtain ⟨⟨q, hq⟩, hqe⟩ := hsurj ⟨⁅q', u⁆, hq'u⟩
  have hqq : ⁅q, u⁆ = ⁅q', u⁆ := by
    have := congrArg (fun x : zpowers z => (x : G)) hqe
    simpa [hφ] using this
  refine ⟨q, hq, ?_⟩
  simp only [mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
    forall_eq]
  obtain ⟨w, hwdef⟩ : ∃ w, w = ⁅q', u⁆ := ⟨_, rfl⟩
  have hwu : w * u = q * u * q⁻¹ := by rw [hwdef, ← hqq, commutatorElement_def]; group
  have hB : q' * u = w * u * q' := by rw [hwdef, commutatorElement_def]; group
  refine ⟨?_, ?_⟩
  · have e : q⁻¹ * w * u = u * q⁻¹ := by
      calc q⁻¹ * w * u = q⁻¹ * (w * u) := mul_assoc _ _ _
        _ = q⁻¹ * (q * u * q⁻¹) := by rw [hwu]
        _ = u * q⁻¹ := by group
    calc u * (q⁻¹ * q') = (u * q⁻¹) * q' := by group
      _ = (q⁻¹ * w * u) * q' := by rw [e]
      _ = q⁻¹ * (w * u * q') := by group
      _ = q⁻¹ * (q' * u) := by rw [hB]
      _ = q⁻¹ * q' * u := by group
  · have hqz' : q⁻¹ * z = z * q⁻¹ := hzc q⁻¹ (inv_mem hq)
    calc z * (q⁻¹ * q') = (z * q⁻¹) * q' := by group
      _ = (q⁻¹ * z) * q' := by rw [hqz']
      _ = q⁻¹ * (z * q') := by group
      _ = q⁻¹ * (q' * z) := by rw [hq'z]
      _ = q⁻¹ * q' * z := by group

theorem eq_of_mem_of_card_centralizer_le
    (Q Q' : Subgroup G) (z u : G)
    (hQ : Nat.card Q = 11 ^ 3) (hQ' : Nat.card Q' = 11 ^ 3) (hz : orderOf z = 11)
    (hcQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ zpowers z)
    (hcQ' : ∀ a ∈ Q', ∀ b ∈ Q', ⁅a, b⁆ ∈ zpowers z)
    (hZQ : ∀ q ∈ Q, (∀ a ∈ Q, q * a = a * q) → q ∈ zpowers z)
    (hzQc : ∀ q ∈ Q, q * z = z * q) (hzQc' : ∀ q ∈ Q', q * z = z * q)
    (huQ : u ∈ Q) (huQ' : u ∈ Q') (hu : u ∉ zpowers z)
    (hC : Nat.card (centralizer ({u} : Set G)) ≤ 242) : Q = Q' := by
  set R : Subgroup G := centralizer ({u, z} : Set G) with hR
  have hRle : Nat.card R ≤ 242 :=
    le_trans (card_le_of_le (centralizer_le (by simp))) hC
  have hQR : Q ⊓ R = centralizer ({u} : Set G) ⊓ Q := by
    ext g
    simp only [mem_inf, hR, mem_centralizer_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hg, hgu, -⟩
      exact ⟨hgu, hg⟩
    · rintro ⟨hgu, hg⟩
      exact ⟨hg, hgu, (hzQc g hg).symm⟩
  have hQR121 : Nat.card ↥(Q ⊓ R) = 121 := by
    rw [hQR, card_centralizer_of_noncentral Q z u hz hcQ hzQc hZQ huQ hu, hQ]
    norm_num
  have hLE := le_normalizer_centralizer_pair hcQ hzQc huQ
  have hiso : R.relIndex Q = R.relIndex (Q ⊔ R) :=
    letI := normal_subgroupOf_of_le_normalizer hLE
    letI := normal_subgroupOf_sup_of_le_normalizer hLE
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient Q R hLE).toEquiv
  have h1 : R.relIndex Q * 121 = 11 ^ 3 := by
    have := relIndex_mul_card (H := R) (K := Q)
    rwa [inf_comm, hQR121, hQ] at this
  have h2 : R.relIndex (Q ⊔ R) * Nat.card R = Nat.card ↥(Q ⊔ R) := by
    have := relIndex_mul_card (H := R) (K := Q ⊔ R)
    rwa [inf_of_le_left le_sup_right] at this
  have h3 : Q.relIndex (Q ⊔ R) * 11 ^ 3 = Nat.card ↥(Q ⊔ R) := by
    have := relIndex_mul_card (H := Q) (K := Q ⊔ R)
    rwa [inf_of_le_left le_sup_left, hQ] at this
  have h11 : R.relIndex Q = 11 := by omega
  rw [← hiso, h11] at h2
  have hidx : Q.relIndex (Q ⊔ R) ≤ 2 := by omega
  have hQ'M : Q' ≤ Q ⊔ R := by
    intro q' hq'
    obtain ⟨q, hq, hr⟩ := exists_mul_mem_centralizer_pair Q z u hz hcQ hzQc hZQ huQ hu
      (hzQc' q' hq') (hcQ' _ hq' _ huQ')
    have := mul_mem ((le_sup_left : Q ≤ Q ⊔ R) hq) ((le_sup_right : R ≤ Q ⊔ R) hr)
    simpa using this
  have hle : Q' ≤ Q := le_of_relIndex_le_two hQ' hQ'M hidx
  exact (eq_of_le_of_card_ge hle (by rw [hQ, hQ'])).symm

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction


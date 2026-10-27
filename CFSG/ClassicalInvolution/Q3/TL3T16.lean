module

public import CFSG.ClassicalInvolution.Q3.TL3T8

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph

variable {G : Type} [Group G]

structure E8Struct (X E : Subgroup G) : Prop where
  le : E ≤ X
  normal : ∀ x ∈ X, ∀ e ∈ E, x * e * x⁻¹ ∈ E
  card : Nat.card E = 8
  sq : ∀ e ∈ E, e * e = 1
  cent : ∀ x ∈ X, (∀ e ∈ E, x * e = e * x) → x ∈ E
  core : ∀ Q : Subgroup G, Q ≤ X → (∀ x ∈ X, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) → IsPGroup 2 Q → Q ≤ E
  index : E.relIndex X = 168

theorem comm_of_sq {E : Subgroup G} (hsq : ∀ e ∈ E, e * e = 1) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) : a * b = b * a := by
  have hab := hsq _ (E.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, ha', hb']

theorem isUniqueInvolution_comm {L : Subgroup G} {z : G} (hz : IsUniqueInvolution L z)
    {k : G} (hk : k ∈ L) : k * z = z * k := by
  have h := hz.conj_eq (conjSub_eq_self_of_mem hk)
  calc k * z = k * z * k⁻¹ * k := by group
    _ = z * k := by rw [h]

section E8

variable [DecidableEq G]

@[expose] def kleinSet (z j : G) : Finset G := {1, z, j, z * j}

structure E8Frame (E : Subgroup G) (z j e : G) : Prop where
  card : Nat.card E = 8
  sq : ∀ x ∈ E, x * x = 1
  zE : z ∈ E
  jE : j ∈ E
  z1 : z ≠ 1
  j1 : j ≠ 1
  zj : z ≠ j
  eE : e ∈ E
  eV : e ∉ kleinSet z j

namespace E8Frame

variable {E : Subgroup G} {z j e : G} (F : E8Frame E z j e)
include F

theorem comm {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := comm_of_sq F.sq ha hb

theorem mem_of_mem_klein {v : G} (hv : v ∈ kleinSet z j) : v ∈ E := by
  simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact E.one_mem
  · exact F.zE
  · exact F.jE
  · exact E.mul_mem F.zE F.jE

theorem klein_mul {a b : G} (ha : a ∈ kleinSet z j) (hb : b ∈ kleinSet z j) :
    a * b ∈ kleinSet z j := by
  have zz : z * z = 1 := F.sq z F.zE
  have jj : j * j = 1 := F.sq j F.jE
  have hjz : j * z = z * j := F.comm F.jE F.zE
  have hzz' : ∀ x, z * (z * x) = x := fun x => by rw [← mul_assoc, zz, one_mul]
  have hjz' : ∀ x, j * (z * x) = z * (j * x) := fun x => by rw [← mul_assoc, hjz, mul_assoc]
  simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, hzz', hjz, hjz', zz, jj, mul_one, one_mul, true_or, or_true]

theorem klein_card : (kleinSet z j).card = 4 := by
  have zz : z * z = 1 := F.sq z F.zE
  have jj : j * j = 1 := F.sq j F.jE
  have hzj1 : z * j ≠ 1 := by
    intro h
    apply F.zj
    calc z = z * (j * j) := by rw [jj, mul_one]
      _ = (z * j) * j := by rw [mul_assoc]
      _ = j := by rw [h, one_mul]
  have hzjz : z * j ≠ z := by
    intro h
    apply F.j1
    calc j = z * (z * j) := by rw [← mul_assoc, zz, one_mul]
      _ = z * z := by rw [h]
      _ = 1 := zz
  have hzjj : z * j ≠ j := by
    intro h
    apply F.z1
    calc z = (z * j) * j := by rw [mul_assoc, jj, mul_one]
      _ = j * j := by rw [h]
      _ = 1 := jj
  rw [kleinSet, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_pair hzjj.symm]
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨F.zj, hzjz.symm⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨F.z1.symm, F.j1.symm, hzj1.symm⟩

variable [Finite G]

theorem decomp {x : G} (hx : x ∈ E) : x ∈ kleinSet z j ∨ x * e ∈ kleinSet z j := by
  set V := kleinSet z j with hV
  have hdisj : Disjoint V (V.image (· * e)) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ha'
    apply F.eV
    have : e = v * (v * e) := by rw [← mul_assoc, F.sq v (F.mem_of_mem_klein hv), one_mul]
    rw [this]
    exact F.klein_mul hv ha
  have himg : (V.image (· * e)).card = 4 := by
    rw [Finset.card_image_of_injective _ (mul_left_injective e), F.klein_card]
  have hFcard : (V ∪ V.image (· * e)).card = 8 := by
    rw [Finset.card_union_of_disjoint hdisj, F.klein_card, himg]
  by_contra hcon
  push Not at hcon
  have hxF : x ∉ V ∪ V.image (· * e) := by
    simp only [Finset.mem_union, Finset.mem_image]
    rintro (h | ⟨v, hv, rfl⟩)
    · exact hcon.1 h
    · apply hcon.2
      rw [mul_assoc, F.sq e F.eE, mul_one]
      exact hv
  have hsub : ((insert x (V ∪ V.image (· * e)) : Finset G) : Set G) ⊆ (E : Set G) := by
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_union, Finset.coe_image, Set.mem_insert_iff,
      Set.mem_union, Set.mem_image, Finset.mem_coe] at hy
    rcases hy with rfl | hy | ⟨v, hv, rfl⟩
    · exact hx
    · exact F.mem_of_mem_klein hy
    · exact E.mul_mem (F.mem_of_mem_klein hv) F.eE
  have hle : (insert x (V ∪ V.image (· * e))).card ≤ Nat.card E := by
    rw [← Nat.card_eq_finsetCard, ← SetLike.coe_sort_coe]
    exact Nat.card_mono (Set.toFinite _) hsub
  rw [Finset.card_insert_of_notMem hxF, hFcard, F.card] at hle
  omega

omit [Finite G] in
theorem comm_klein {g : G} (hgz : g * z = z * g) (hgj : g * j = j * g) :
    ∀ v ∈ kleinSet z j, g * v = v * g := by
  intro v hv
  simp only [kleinSet, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · simp
  · exact hgz
  · exact hgj
  · rw [← mul_assoc, hgz, mul_assoc, hgj, mul_assoc]

theorem comm_of_comm {g : G} (hgz : g * z = z * g) (hgj : g * j = j * g) (hge : g * e = e * g) :
    ∀ x ∈ E, g * x = x * g := by
  have hee : e * e = 1 := F.sq e F.eE
  intro x hx
  rcases F.decomp hx with h | h
  · exact F.comm_klein hgz hgj x h
  · have hV := F.comm_klein hgz hgj _ h
    calc g * x = g * ((x * e) * e) := by rw [mul_assoc x e e, hee, mul_one]
      _ = (g * (x * e)) * e := (mul_assoc _ _ _).symm
      _ = ((x * e) * g) * e := by rw [hV]
      _ = (x * e) * (g * e) := mul_assoc _ _ _
      _ = (x * e) * (e * g) := by rw [hge]
      _ = x * g := by rw [← mul_assoc, mul_assoc x e e, hee, mul_one]

theorem exists_conj {X M : Subgroup G} (hnorm : ∀ x ∈ X, ∀ y ∈ E, x * y * x⁻¹ ∈ E)
    (hcent : ∀ x ∈ X, (∀ y ∈ E, x * y = y * x) → x ∈ E) (hMX : M ≤ X) (hM8 : Nat.card M = 8)
    {u : G} (hu : IsUniqueInvolution M u) (huE : u ∈ E) (hMz : ∀ k ∈ M, k * z = z * k)
    (hMj : ∀ k ∈ M, k * j = j * k) : ∃ k ∈ M, k * e * k⁻¹ = z * e ∧ k * k ≠ 1 := by
  have hee : e * e = 1 := F.sq e F.eE
  have hwV : ∀ k ∈ M, k * e * k⁻¹ * e ∈ kleinSet z j := by
    intro k hk
    have hc : k * e * k⁻¹ ∈ E := hnorm k (hMX hk) e F.eE
    rcases F.decomp hc with h | h
    · exfalso
      apply F.eV
      have hk' := F.comm_klein (Commute.inv_left (hMz k hk)) (Commute.inv_left (hMj k hk)) _ h
      have : e = k⁻¹ * (k * e * k⁻¹) * k := by group
      rw [this, hk', mul_assoc, inv_mul_cancel, mul_one]
      exact h
    · exact h
  let w : ↥M →* G :=
    { toFun := fun k => (k : G) * e * (k : G)⁻¹ * e
      map_one' := by simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one, hee]
      map_mul' := by
        intro a b
        have hB := hwV b b.2
        have haB : (a : G) * ((b : G) * e * (b : G)⁻¹ * e) =
            ((b : G) * e * (b : G)⁻¹ * e) * a :=
          F.comm_klein (hMz a a.2) (hMj a a.2) _ hB
        have hAB := F.comm (F.mem_of_mem_klein (hwV a a.2)) (F.mem_of_mem_klein hB)
        have hBe : (b : G) * e * (b : G)⁻¹ * e * e = (b : G) * e * (b : G)⁻¹ := by
          rw [mul_assoc _ e e, hee, mul_one]
        simp only [Subgroup.coe_mul]
        calc (a : G) * b * e * ((a : G) * b)⁻¹ * e
            = (a : G) * ((b : G) * e * (b : G)⁻¹) * (a : G)⁻¹ * e := by group
          _ = (a : G) * ((b : G) * e * (b : G)⁻¹ * e * e) * (a : G)⁻¹ * e := by rw [hBe]
          _ = ((a : G) * ((b : G) * e * (b : G)⁻¹ * e)) * (e * (a : G)⁻¹ * e) := by group
          _ = (((b : G) * e * (b : G)⁻¹ * e) * a) * (e * (a : G)⁻¹ * e) := by rw [haB]
          _ = ((b : G) * e * (b : G)⁻¹ * e) * ((a : G) * e * (a : G)⁻¹ * e) := by group
          _ = ((a : G) * e * (a : G)⁻¹ * e) * ((b : G) * e * (b : G)⁻¹ * e) := hAB.symm }
  have hw : ∀ k : ↥M, w k = (k : G) * e * (k : G)⁻¹ * e := fun k => rfl
  have hker : ∀ k : ↥M, w k = 1 ↔ k = 1 ∨ k = ⟨u, hu.mem⟩ := by
    intro k
    constructor
    · intro hk
      rw [hw] at hk
      have hke : (k : G) * e = e * k := by
        calc (k : G) * e = ((k : G) * e * (k : G)⁻¹ * e) * e * k := by
              rw [mul_assoc ((k : G) * e * (k : G)⁻¹) e e, hee, mul_one]; group
          _ = e * k := by rw [hk, one_mul]
      have hkE : (k : G) ∈ E := hcent k (hMX k.2) (F.comm_of_comm (hMz k k.2) (hMj k k.2) hke)
      rcases hu.unique k k.2 (F.sq k hkE) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact map_one w
      · rw [hw]
        show u * e * u⁻¹ * e = 1
        rw [F.comm huE F.eE, mul_assoc e u, mul_inv_cancel, mul_one, hee]
  have hu1 : (⟨u, hu.mem⟩ : ↥M) ≠ 1 := fun h => hu.ne_one (congrArg Subtype.val h)
  have hkerset : (w.ker : Set ↥M) = {1, ⟨u, hu.mem⟩} := by
    ext k
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact hker k
  have hk2 : Nat.card w.ker = 2 := by
    rw [← SetLike.coe_sort_coe, hkerset, Nat.card_coe_set_eq, Set.ncard_pair hu1.symm]
  have hrange : Nat.card w.range = 4 := by
    have h1 := Subgroup.card_mul_index w.ker
    rw [Subgroup.index_ker, hk2, hM8] at h1
    omega
  have hsub : (w.range : Set G) ⊆ ((kleinSet z j : Finset G) : Set G) := by
    rintro _ ⟨k, rfl⟩
    exact hwV k k.2
  have heq : (w.range : Set G) = ((kleinSet z j : Finset G) : Set G) := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, F.klein_card, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe,
      hrange]
  have hzr : z ∈ w.range := by
    have : z ∈ ((kleinSet z j : Finset G) : Set G) := by simp [kleinSet]
    rw [← heq] at this
    exact this
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp hzr
  rw [hw] at hk
  refine ⟨k, k.2, ?_, ?_⟩
  · calc (k : G) * e * (k : G)⁻¹ = ((k : G) * e * (k : G)⁻¹ * e) * e := by
          rw [mul_assoc _ e e, hee, mul_one]
      _ = z * e := by rw [hk]
  · intro hkk
    have h1 : w k = 1 := by
      rcases hu.unique k k.2 hkk with h | h
      · exact (hker k).mpr (Or.inl (Subtype.ext h))
      · exact (hker k).mpr (Or.inr (Subtype.ext h))
    rw [hw, hk] at h1
    exact F.z1 h1

end E8Frame

end E8

variable [Finite G]

theorem false_of_e8_commuting {X E L L' : Subgroup G}
    (hnorm : ∀ x ∈ X, ∀ y ∈ E, x * y * x⁻¹ ∈ E) (hcard : Nat.card E = 8)
    (hsq : ∀ y ∈ E, y * y = 1) (hcent : ∀ x ∈ X, (∀ y ∈ E, x * y = y * x) → x ∈ E)
    (hLX : L ≤ X) (hL'X : L' ≤ X) (hL8 : Nat.card L = 8) (hL'8 : Nat.card L' = 8)
    {z j : G} (hz : IsUniqueInvolution L z) (hj : IsUniqueInvolution L' j) (hzE : z ∈ E)
    (hjE : j ∈ E) (hzj : z ≠ j) (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    (hdisj : ∀ x ∈ L, x ∈ L' → x = 1) : False := by
  classical
  obtain ⟨e, heE, heV⟩ : ∃ e ∈ E, e ∉ kleinSet z j := by
    by_contra hcon
    push Not at hcon
    have hsub : (E : Set G) ⊆ ((kleinSet z j : Finset G) : Set G) := fun x hx => hcon x hx
    have h1 : Nat.card E ≤ (kleinSet z j).card := by
      rw [← Nat.card_eq_finsetCard, ← SetLike.coe_sort_coe]
      exact Nat.card_mono (Finset.finite_toSet _) hsub
    have h2 : (kleinSet z j).card ≤ 4 := Finset.card_le_four
    omega
  have F : E8Frame E z j e := ⟨hcard, hsq, hzE, hjE, hz.ne_one, hj.ne_one, hzj, heE, heV⟩
  have hkz : ∀ k ∈ L, k * z = z * k := fun k hk => isUniqueInvolution_comm hz hk
  have hkj : ∀ k ∈ L, k * j = j * k := fun k hk => hcomm k hk j hj.mem
  have hxz : ∀ x ∈ L', x * z = z * x := fun x hx => (hcomm z hz.mem x hx).symm
  have hxj : ∀ x ∈ L', x * j = j * x := fun x hx => isUniqueInvolution_comm hj hx
  obtain ⟨k, hk, hke, hkk⟩ := F.exists_conj hnorm hcent hLX hL8 hz hzE hkz hkj
  obtain ⟨x, hx, hxe, -⟩ := F.exists_conj hnorm hcent hL'X hL'8 hj hjE hxz hxj
  have hy : x⁻¹ * k ∈ E := by
    refine hcent _ (X.mul_mem (X.inv_mem (hL'X hx)) (hLX hk)) (F.comm_of_comm ?_ ?_ ?_)
    · exact Commute.mul_left (Commute.inv_left (hxz x hx)) (hkz k hk)
    · exact Commute.mul_left (Commute.inv_left (hxj x hx)) (hkj k hk)
    · calc x⁻¹ * k * e = x⁻¹ * (k * e * k⁻¹) * k := by group
        _ = x⁻¹ * (x * e * x⁻¹) * k := by rw [hke, hxe]
        _ = e * (x⁻¹ * k) := by group
  have hyy := F.sq _ hy
  have hkx : k * x⁻¹ = x⁻¹ * k := Commute.inv_right (hcomm k hk x hx)
  have hkk' : k * k = x * x := by
    calc k * k = x * x * (x⁻¹ * (x⁻¹ * k) * k) := by group
      _ = x * x * (x⁻¹ * (k * x⁻¹) * k) := by rw [hkx]
      _ = x * x * (x⁻¹ * k * (x⁻¹ * k)) := by group
      _ = x * x := by rw [hyy, mul_one]
  exact hkk (hdisj _ (L.mul_mem hk hk) (by rw [hkk']; exact L'.mul_mem hx hx))

theorem eq_one_of_mem_inf {L L' : Subgroup G} {z j : G} (hL2 : IsPGroup 2 L)
    (hz : IsUniqueInvolution L z) (hj : IsUniqueInvolution L' j) (hzj : z ≠ j) {x : G}
    (hxL : x ∈ L) (hxL' : x ∈ L') : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hx1
  have hH2 : IsPGroup 2 ↥(L ⊓ L') := hL2.to_le inf_le_left
  have hne : L ⊓ L' ≠ ⊥ := by
    intro h
    apply hx1
    have : x ∈ L ⊓ L' := ⟨hxL, hxL'⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  rcases hH2.card_eq_or_dvd with h1 | h1
  · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h1
  have hw1 : (w : G) ≠ 1 := by
    intro h
    have : w = 1 := Subtype.ext h
    rw [this, orderOf_one] at hw
    exact absurd hw (by norm_num)
  have hww : (w : G) * w = 1 := by
    have := pow_orderOf_eq_one w
    rw [hw, pow_two] at this
    exact congrArg Subtype.val this
  have h1 := (hz.unique w w.2.1 hww).resolve_left hw1
  have h2 := (hj.unique w w.2.2 hww).resolve_left hw1
  exact hzj (h1.symm.trans h2)

theorem indep_of_e8Struct {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω)
    (h2 : ∀ J ∈ Ω, IsPGroup 2 J) (h8 : ∀ J ∈ Ω, Nat.card J = 8)
    (hnt : ∀ J ∈ Ω, ∀ J' ∈ Ω, ∀ u : G, IsUniqueInvolution J u → IsUniqueInvolution J' u → J = J')
    {P : Set (Subgroup G)} (hPΩ : P ⊆ Ω)
    (hE2 : ∀ L ∈ P, ∀ u : G, IsUniqueInvolution L u → ∃ Q : Subgroup G, Q ≤ pSpan P ∧
      (∀ x ∈ pSpan P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) ∧ IsPGroup 2 Q ∧ u ∈ Q)
    {E : Subgroup G} (hE : E8Struct (pSpan P) E) :
    ∀ L ∈ P, ∀ L' ∈ P, L ≠ L' → ¬ nbrAdj Ω L L' := by
  intro L hL L' hL' hne hadj
  obtain ⟨z, hz⟩ := (hΩ.omega1 L (hPΩ hL)).1
  obtain ⟨j, hj⟩ := (hΩ.omega1 L' (hPΩ hL')).1
  have hzE : z ∈ E := by
    obtain ⟨Q, hQX, hQn, hQ2, hzQ⟩ := hE2 L hL z hz
    exact hE.core Q hQX hQn hQ2 hzQ
  have hjE : j ∈ E := by
    obtain ⟨Q, hQX, hQn, hQ2, hjQ⟩ := hE2 L' hL' j hj
    exact hE.core Q hQX hQn hQ2 hjQ
  have hzj : z ≠ j := fun h => hne (hnt L (hPΩ hL) L' (hPΩ hL') z hz (h ▸ hj))
  have hN := ((mem_omegaNbr_iff hΩ h2).mp hadj.2).2.2
  have hP2 : IsPGroup 2 ↥(L' ⊔ L) :=
    (h2 L' (hPΩ hL')).to_sup_of_normal_right' (h2 L (hPΩ hL)) hN
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x :=
    Q3CP.l67Gen G Ω hΩ S L (mem_RSet_of_isPGroup (hPΩ hL) (h2 L (hPΩ hL))) L'
      (mem_RSet_of_isPGroup (hPΩ hL') (h2 L' (hPΩ hL'))) (le_sup_right.trans hPS)
      (le_sup_left.trans hPS) hne
  exact false_of_e8_commuting hE.normal hE.card hE.sq hE.cent (le_pSpan hL) (le_pSpan hL')
    (h8 L (hPΩ hL)) (h8 L' (hPΩ hL')) hz hj hzE hjE hzj hcomm
    (fun x hx hx' => eq_one_of_mem_inf (h2 L (hPΩ hL)) hz hj hzj hx hx')

end CFSG.ClassicalInvolution.Q3.TC.Thin

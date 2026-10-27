module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

variable {G : Type*} [Group G]

@[expose] def commSet (Q : Subgroup G) : Set G := {x | ∃ a ∈ Q, ∃ b ∈ Q, x = a * b * a⁻¹ * b⁻¹}

theorem mem_sup_central {M Z Q : Subgroup G} (hMQ : M ≤ Q) (hZcen : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    {x : G} (hx : x ∈ M ⊔ Z) : ∃ m ∈ M, ∃ z ∈ Z, x = m * z := by
  rw [← Subgroup.closure_eq M, ← Subgroup.closure_eq Z, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, Z.one_mem, (mul_one y).symm⟩
    · exact ⟨1, M.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, M.one_mem, 1, Z.one_mem, (mul_one 1).symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨m1, hm1, z1, hz1, rfl⟩ := ha
    obtain ⟨m2, hm2, z2, hz2, rfl⟩ := hb
    refine ⟨m1 * m2, M.mul_mem hm1 hm2, z1 * z2, Z.mul_mem hz1 hz2, ?_⟩
    have h := hZcen z1 hz1 m2 (hMQ hm2)
    calc m1 * z1 * (m2 * z2) = m1 * (z1 * m2) * z2 := by group
      _ = m1 * (m2 * z1) * z2 := by rw [h]
      _ = m1 * m2 * (z1 * z2) := by group
  | inv a _ ha =>
    obtain ⟨m, hm, z, hz, rfl⟩ := ha
    refine ⟨m⁻¹, M.inv_mem hm, z⁻¹, Z.inv_mem hz, ?_⟩
    have h := hZcen z hz m (hMQ hm)
    have h' : z⁻¹ * m⁻¹ = m⁻¹ * z⁻¹ := by
      calc z⁻¹ * m⁻¹ = (m * z)⁻¹ := by group
        _ = (z * m)⁻¹ := by rw [h]
        _ = m⁻¹ * z⁻¹ := by group
    calc (m * z)⁻¹ = z⁻¹ * m⁻¹ := by group
      _ = m⁻¹ * z⁻¹ := h'

theorem closure_commute {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := by
  have h1 : ∀ x ∈ Subgroup.closure S, ∀ b ∈ S, x * b = b * x := by
    intro x hx b hb
    have hle : Subgroup.closure S ≤ Subgroup.centralizer {b} := by
      rw [Subgroup.closure_le]
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (hS b hb a ha).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  intro x hx y hy
  have hle : Subgroup.closure S ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    intro b hb
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (h1 x hx b hb).symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem trivial_action {C Q Z N : Subgroup G} (hNC : N ≤ C) (hQC : Q ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Z) (hsup : N ⊔ Q = C)
    (hMZ : ∀ m ∈ N ⊓ Q, m ∈ Z) :
    ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ * q⁻¹ ∈ Z := by
  have hcl : Subgroup.closure ((N : Set G) ∪ Q) ≤ C := by
    rw [Subgroup.closure_le]
    exact Set.union_subset hNC hQC
  intro c hc
  have hcK : c ∈ Subgroup.closure ((N : Set G) ∪ Q) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hsup]
    exact hc
  clear hc
  induction hcK using Subgroup.closure_induction with
  | mem y hy =>
    intro q hq
    rcases hy with hy | hy
    · apply hMZ
      refine ⟨?_, ?_⟩
      · have h1 : y * (q * y⁻¹ * q⁻¹) ∈ N := N.mul_mem hy (hNn q (hQC hq) y⁻¹ (N.inv_mem hy))
        have e : y * (q * y⁻¹ * q⁻¹) = y * q * y⁻¹ * q⁻¹ := by group
        rwa [e] at h1
      · exact Q.mul_mem (hQn y (hNC hy) q hq) (Q.inv_mem hq)
    · exact hcomm y hy q hq
  | one =>
    intro q _
    simp
  | mul a b ha hb pa pb =>
    intro q hq
    have hbC : b ∈ C := hcl hb
    have hq' : b * q * b⁻¹ ∈ Q := hQn b hbC q hq
    have h1 := pa _ hq'
    have h2 := pb q hq
    have e : a * b * q * (a * b)⁻¹ * q⁻¹ =
        (a * (b * q * b⁻¹) * a⁻¹ * (b * q * b⁻¹)⁻¹) * (b * q * b⁻¹ * q⁻¹) := by group
    rw [e]
    exact Z.mul_mem h1 h2
  | inv a ha pa =>
    intro q hq
    have haC : a ∈ C := hcl ha
    have hq' : a⁻¹ * q * a ∈ Q := by
      have := hQn a⁻¹ (C.inv_mem haC) q hq
      simpa using this
    have h1 := pa _ hq'
    have e : a⁻¹ * q * a⁻¹⁻¹ * q⁻¹ = (a * (a⁻¹ * q * a) * a⁻¹ * (a⁻¹ * q * a)⁻¹)⁻¹ := by group
    rw [e]
    exact Z.inv_mem h1

theorem comm_inv_of_comm {z a : G} (h : z * a = a * z) : z * a⁻¹ = a⁻¹ * z := by
  calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
    _ = a⁻¹ * (z * a) * a⁻¹ := by rw [h]
    _ = a⁻¹ * z := by group

theorem comm_mul_central_left {a b z : G} (h : z * b = b * z) :
    a * z * b * (a * z)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_central_right {a b z : G} (h : z * a = a * z) :
    a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h' := comm_inv_of_comm h
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h']
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commSet_le {M Z Q : Subgroup G} (hMQ : M ≤ Q) (hZQ : Z ≤ Q) (hQM : Q ≤ M ⊔ Z)
    (hZcen : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z) {x : G} (hx : x ∈ commSet Q) : x ∈ M := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  obtain ⟨m1, hm1, z1, hz1, rfl⟩ := mem_sup_central hMQ hZcen (hQM ha)
  obtain ⟨m2, hm2, z2, hz2, rfl⟩ := mem_sup_central hMQ hZcen (hQM hb)
  have hm1z1 : m1 * z1 ∈ Q := Q.mul_mem (hMQ hm1) (hZQ hz1)
  have e1 : (m1 * z1) * (m2 * z2) * (m1 * z1)⁻¹ * (m2 * z2)⁻¹ =
      (m1 * z1) * m2 * (m1 * z1)⁻¹ * m2⁻¹ :=
    comm_mul_central_right (a := m1 * z1) (b := m2) (hZcen z2 hz2 _ hm1z1)
  have e2 : (m1 * z1) * m2 * (m1 * z1)⁻¹ * m2⁻¹ = m1 * m2 * m1⁻¹ * m2⁻¹ :=
    comm_mul_central_left (a := m1) (b := m2) (hZcen z1 hz1 _ (hMQ hm2))
  rw [e1, e2]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm1 hm2) (M.inv_mem hm1)) (M.inv_mem hm2)

theorem normal_le_or_eq {C Q Z : Subgroup G} (hQC : Q ≤ C)
    (hQn : ∀ c ∈ C, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q)
    (hsimple : ∀ K : Subgroup G, Q ≤ K → K ≤ C → (∀ c ∈ C, ∀ k ∈ K, c * k * c⁻¹ ∈ K) →
      K = Q ∨ K = C)
    (hZQ : Z ≤ Q) (hZcen : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hZn : ∀ c ∈ C, ∀ z ∈ Z, c * z * c⁻¹ ∈ Z) (hZne : Z ≠ ⊥)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Z)
    (hZcomm : ∀ z ∈ Z, z ∈ Subgroup.closure (commSet Q))
    (hirr : ∀ M : Subgroup G, Z ≤ M → M ≤ Q → (∀ c ∈ C, ∀ m ∈ M, c * m * c⁻¹ ∈ M) →
      M = Z ∨ M = Q)
    {N : Subgroup G} (hNC : N ≤ C) (hNn : ∀ c ∈ C, ∀ n ∈ N, c * n * c⁻¹ ∈ N) :
    N ≤ Q ∨ N = C := by
  have hKC : N ⊔ Q ≤ C := sup_le hNC hQC
  have hKn : ∀ c ∈ C, ∀ k ∈ N ⊔ Q, c * k * c⁻¹ ∈ N ⊔ Q := by
    intro c hc k hk
    have hle : N ⊔ Q ≤ (N ⊔ Q).comap (MulAut.conj c).toMonoidHom := by
      refine sup_le (fun n hn => ?_) (fun q hq => ?_)
      · exact Subgroup.mem_sup_left (hNn c hc n hn)
      · exact Subgroup.mem_sup_right (hQn c hc q hq)
    exact hle hk
  obtain ⟨⟨z0, hz0⟩, hz01'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
  have hz01 : z0 ≠ 1 := fun h => hz01' (Subtype.ext h)
  rcases hsimple (N ⊔ Q) le_sup_right hKC hKn with hKQ | hKC'
  · exact Or.inl (le_sup_left.trans hKQ.le)
  · right
    by_cases hMZ : ∀ m ∈ N ⊓ Q, m ∈ Z
    · exfalso
      have hact := trivial_action hNC hQC hQn hNn hcomm hKC' hMZ
      have hbot : (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) → False := by
        intro hab
        have hle : Subgroup.closure (commSet Q) ≤ ⊥ := by
          rw [Subgroup.closure_le]
          rintro x ⟨a, ha, b, hb, rfl⟩
          have h1 : a * b = b * a := hab a ha b hb
          rw [SetLike.mem_coe, Subgroup.mem_bot]
          calc a * b * a⁻¹ * b⁻¹ = (b * a) * a⁻¹ * b⁻¹ := by rw [h1]
            _ = 1 := by group
        exact hz01 (Subgroup.mem_bot.1 (hle (hZcomm z0 hz0)))
      have hex : ∃ q' ∈ Q, q' ∉ Z := by
        by_contra hcon
        push Not at hcon
        exact hbot fun a ha b hb => hZcen a (hcon a ha) b hb
      obtain ⟨q', hq', hq'Z⟩ := hex
      set T : Subgroup G := Subgroup.closure ((Z : Set G) ∪ {q'}) with hT
      have hZT : Z ≤ T := fun z hz => Subgroup.subset_closure (Or.inl hz)
      have hq'T : q' ∈ T := Subgroup.subset_closure (Or.inr rfl)
      have hTQ : T ≤ Q := by
        rw [hT, Subgroup.closure_le]
        exact Set.union_subset hZQ (Set.singleton_subset_iff.2 hq')
      have hTn : ∀ c ∈ C, ∀ m ∈ T, c * m * c⁻¹ ∈ T := by
        intro c hc m hm
        have hle : T ≤ T.comap (MulAut.conj c).toMonoidHom := by
          rw [hT, Subgroup.closure_le]
          rintro x (hx | hx)
          · exact hZT (hZn c hc x hx)
          · rw [Set.mem_singleton_iff] at hx
            subst hx
            have h1 := hact c hc x hq'
            have e : c * x * c⁻¹ = (c * x * c⁻¹ * x⁻¹) * x := by group
            show c * x * c⁻¹ ∈ T
            rw [e]
            exact T.mul_mem (hZT h1) hq'T
        exact hle hm
      rcases hirr T hZT hTQ hTn with hTZ | hTQ'
      · exact hq'Z (hTZ ▸ hq'T)
      · apply hbot
        have hS : ∀ a ∈ ((Z : Set G) ∪ {q'}), ∀ b ∈ ((Z : Set G) ∪ {q'}), a * b = b * a := by
          rintro a (ha | ha) b (hb | hb)
          · exact hZcen a ha b (hZQ hb)
          · rw [Set.mem_singleton_iff] at hb
            subst hb
            exact hZcen a ha b hq'
          · rw [Set.mem_singleton_iff] at ha
            subst ha
            exact (hZcen b hb a hq').symm
          · rw [Set.mem_singleton_iff] at ha hb
            rw [ha, hb]
        intro a ha b hb
        rw [← hTQ'] at ha hb
        exact closure_commute hS a ha b hb
    · push Not at hMZ
      obtain ⟨m, hm, hmZ⟩ := hMZ
      have hirr' := hirr ((N ⊓ Q) ⊔ Z) le_sup_right (sup_le inf_le_right hZQ) (by
        intro c hc x hx
        have hle : (N ⊓ Q) ⊔ Z ≤ ((N ⊓ Q) ⊔ Z).comap (MulAut.conj c).toMonoidHom := by
          refine sup_le (fun n hn => ?_) (fun z hz => ?_)
          · exact Subgroup.mem_sup_left ⟨hNn c hc n hn.1, hQn c hc n hn.2⟩
          · exact Subgroup.mem_sup_right (hZn c hc z hz)
        exact hle hx)
      rcases hirr' with hMZ' | hMQ
      · exact absurd (hMZ' ▸ (Subgroup.mem_sup_left hm : m ∈ (N ⊓ Q) ⊔ Z)) hmZ
      · have hQM : Q ≤ (N ⊓ Q) ⊔ Z := hMQ.ge
        have hZN : Z ≤ N := by
          intro z hz
          have : Subgroup.closure (commSet Q) ≤ N := by
            rw [Subgroup.closure_le]
            intro x hx
            exact (commSet_le inf_le_right hZQ hQM hZcen hx).1
          exact this (hZcomm z hz)
        have hQN : Q ≤ N := hMQ.symm.le.trans (sup_le inf_le_left hZN)
        exact (sup_eq_left.2 hQN).symm.trans hKC'

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2

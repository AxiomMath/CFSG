module

public import CFSG.ClassicalInvolution.RouteD.TwinYElement
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeBase

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD
open CFSG.Open (classicalInvolutionOddCore)

section Element

variable {G : Type} [Group G] {K T : Subgroup G} {z : G}

structure TwinElt (K T : Subgroup G) (z : G) where
  a : G
  a' : G
  mem_a : a ∈ K
  mem_a' : a' ∈ T
  mul_self_a : a * a = z
  mul_self_a' : a' * a' = z

@[expose] def TwinElt.u (e : TwinElt K T z) : G := e.a * e.a'

variable {p f : ℕ} [Fact p.Prime]

theorem exists_twinElt (hz : IsClassicalMember p f K z) (hzT : IsClassicalMember p f T z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hexT : classicalInvolutionOddCore T = ⊥)
    (hodd : Odd (Nat.card (GaloisField p f))) : Nonempty (TwinElt K T z) := by
  obtain ⟨a, ha, haa⟩ := exists_mul_self_eq_of_exact hz hexK hodd
  obtain ⟨a', ha', ha'a'⟩ := exists_mul_self_eq_of_exact hzT hexT hodd
  exact ⟨⟨a, a', ha, ha', haa, ha'a'⟩⟩

omit [Fact p.Prime] in
theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (h : orderOf x = 2) : x * x = 1 := by
  have h2 := pow_orderOf_eq_one x
  rwa [h, pow_two] at h2

omit [Fact p.Prime] in
theorem ne_one_of_orderOf_eq_two {x : G} (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  omega

theorem TwinElt.u_mul_self (e : TwinElt K T z) (hKT : Commutes K T) (hz2 : z * z = 1) :
    e.u * e.u = 1 := by
  have hc : e.a * e.a' = e.a' * e.a := hKT _ e.mem_a _ e.mem_a'
  unfold TwinElt.u
  calc e.a * e.a' * (e.a * e.a') = e.a * (e.a' * e.a) * e.a' := by group
    _ = e.a * (e.a * e.a') * e.a' := by rw [← hc]
    _ = (e.a * e.a) * (e.a' * e.a') := by group
    _ = 1 := by rw [e.mul_self_a, e.mul_self_a', hz2]

theorem TwinElt.u_ne_one (e : TwinElt K T z) (hz : IsClassicalMember p f K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f)))
    (hKT : Commutes K T) : e.u ≠ 1 := by
  intro h
  have ha' : e.a' = e.a⁻¹ := by
    have : e.a * e.a' = 1 := h
    exact (eq_inv_of_mul_eq_one_right this)
  have hmem : e.a' ∈ K := by rw [ha']; exact K.inv_mem e.mem_a
  have hc : ∀ k ∈ K, k * e.a' = e.a' * k := fun k hk => hKT k hk _ e.mem_a'
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz.orderOf_eq_two
  have hz1 := ne_one_of_orderOf_eq_two hz.orderOf_eq_two
  have hsq := e.mul_self_a'
  rcases eq_one_or_eq_of_central_of_exact hz hexK hodd hmem hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hz1 hsq.symm
  · rw [h1, hz2] at hsq
    exact hz1 hsq.symm

theorem TwinElt.u_ne_z (e : TwinElt K T z) (hz : IsClassicalMember p f K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f)))
    (hKT : Commutes K T) : e.u ≠ z := by
  intro h
  have hzK : z ∈ K := hz.mem
  have ha' : e.a' = e.a⁻¹ * z := by
    have h' : e.a * e.a' = z := h
    calc e.a' = e.a⁻¹ * (e.a * e.a') := by group
      _ = e.a⁻¹ * z := by rw [h']
  have hmem : e.a' ∈ K := by rw [ha']; exact K.mul_mem (K.inv_mem e.mem_a) hzK
  have hc : ∀ k ∈ K, k * e.a' = e.a' * k := fun k hk => hKT k hk _ e.mem_a'
  have hz2 := mul_self_eq_one_of_orderOf_eq_two hz.orderOf_eq_two
  have hz1 := ne_one_of_orderOf_eq_two hz.orderOf_eq_two
  have hsq := e.mul_self_a'
  rcases eq_one_or_eq_of_central_of_exact hz hexK hodd hmem hc with h1 | h1
  · rw [h1, one_mul] at hsq
    exact hz1 hsq.symm
  · rw [h1, hz2] at hsq
    exact hz1 hsq.symm

theorem TwinElt.u_mem_sup (e : TwinElt K T z) : e.u ∈ K ⊔ T :=
  (K ⊔ T).mul_mem (Subgroup.mem_sup_left e.mem_a) (Subgroup.mem_sup_right e.mem_a')

theorem TwinElt.u_comm_z (e : TwinElt K T z) (hK : K ≤ Subgroup.centralizer ({z} : Set G))
    (hT : T ≤ Subgroup.centralizer ({z} : Set G)) : e.u * z = z * e.u := by
  have h1 : e.a * z = z * e.a := Subgroup.mem_centralizer_singleton_iff.mp (hK e.mem_a)
  have h2 : e.a' * z = z * e.a' := Subgroup.mem_centralizer_singleton_iff.mp (hT e.mem_a')
  unfold TwinElt.u
  calc e.a * e.a' * z = e.a * (e.a' * z) := by group
    _ = e.a * (z * e.a') := by rw [h2]
    _ = (e.a * z) * e.a' := by group
    _ = (z * e.a) * e.a' := by rw [h1]
    _ = z * (e.a * e.a') := by group

theorem exists_not_commute_mul {A : Subgroup G} (hz : IsClassicalMember p f A z)
    (hex : classicalInvolutionOddCore A = ⊥) (hodd : Odd (Nat.card (GaloisField p f))) {x y : G}
    (hx : x ∈ A) (hxx : x * x = z) (hy : ∀ k ∈ A, k * y = y * k) :
    ∃ k ∈ A, k * (x * y) ≠ (x * y) * k := by
  obtain ⟨k, hk, hne⟩ := exists_not_commute_of_mul_self_eq hz hex hodd hx hxx
  refine ⟨k, hk, fun h => hne ?_⟩
  have h1 : k * x * y = x * k * y := by
    calc k * x * y = k * (x * y) := by group
      _ = (x * y) * k := h
      _ = x * (y * k) := by group
      _ = x * (k * y) := by rw [← hy k hk]
      _ = x * k * y := by group
  exact mul_right_cancel h1

theorem TwinElt.not_le_centralizer_left (e : TwinElt K T z) (hz : IsClassicalMember p f K z)
    (hexK : classicalInvolutionOddCore K = ⊥) (hodd : Odd (Nat.card (GaloisField p f)))
    (hKT : Commutes K T) : ¬ K ≤ Subgroup.centralizer ({e.u} : Set G) := by
  intro hle
  obtain ⟨k, hk, hne⟩ := exists_not_commute_mul hz hexK hodd e.mem_a e.mul_self_a
    (y := e.a') (fun k hk => hKT k hk _ e.mem_a')
  exact hne (Subgroup.mem_centralizer_singleton_iff.mp (hle hk))

theorem TwinElt.not_le_centralizer_right (e : TwinElt K T z) (hzT : IsClassicalMember p f T z)
    (hexT : classicalInvolutionOddCore T = ⊥) (hodd : Odd (Nat.card (GaloisField p f)))
    (hKT : Commutes K T) : ¬ T ≤ Subgroup.centralizer ({e.u} : Set G) := by
  intro hle
  have hc : e.a * e.a' = e.a' * e.a := hKT _ e.mem_a _ e.mem_a'
  obtain ⟨k, hk, hne⟩ := exists_not_commute_mul hzT hexT hodd e.mem_a' e.mul_self_a'
    (y := e.a) (fun k hk => (hKT _ e.mem_a _ hk).symm)
  have hu : e.u = e.a' * e.a := hc
  have := Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
  rw [hu] at this
  exact hne this

end Element

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {K T : Subgroup G}
  {z : G}

theorem TwinElt.mem_centralizingMembers_u (e : TwinElt K T z) {N : Subgroup G} (hN : N ∈ Ω)
    (hNK : Commutes N K) (hNT : Commutes N T) : N ∈ centralizingMembers Ω {e.u} := by
  refine ⟨hN, fun x hx => ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : x * e.a = e.a * x := hNK x hx _ e.mem_a
  have h2 : x * e.a' = e.a' * x := hNT x hx _ e.mem_a'
  unfold TwinElt.u
  calc x * (e.a * e.a') = (x * e.a) * e.a' := by group
    _ = (e.a * x) * e.a' := by rw [h1]
    _ = e.a * (x * e.a') := by group
    _ = e.a * (e.a' * x) := by rw [h2]
    _ = (e.a * e.a') * x := by group

theorem TwinElt.layer_mem_centralizingMembers_u {tY : StatedLieTag} {nY : ℕ} [Finite G]
    (e : TwinElt K T z) (c : TCtx p f tY nY Ω K z) {N : Subgroup G}
    (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁)
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNT : N ≠ T) :
    N ∈ centralizingMembers Ω {e.u} :=
  e.mem_centralizingMembers_u hN.1 (c.commutes_K_of_ne hN hNK).symm
    (c.commutes_T_of_ne hT hTQ hN hNT).symm

theorem TwinElt.not_mem_centralizingMembers_left (e : TwinElt K T z)
    (hz : IsClassicalMember p f K z) (hexK : classicalInvolutionOddCore K = ⊥)
    (hodd : Odd (Nat.card (GaloisField p f))) (hKT : Commutes K T) :
    K ∉ centralizingMembers Ω {e.u} :=
  fun h => e.not_le_centralizer_left hz hexK hodd hKT h.2

theorem TwinElt.not_mem_centralizingMembers_right (e : TwinElt K T z)
    (hzT : IsClassicalMember p f T z) (hexT : classicalInvolutionOddCore T = ⊥)
    (hodd : Odd (Nat.card (GaloisField p f))) (hKT : Commutes K T) :
    T ∉ centralizingMembers Ω {e.u} :=
  fun h => e.not_le_centralizer_right hzT hexT hodd hKT h.2

theorem TwinElt.layer_le_locLayer {tY : StatedLieTag} {nY : ℕ} [Finite G]
    (e : TwinElt K T z) (c : TCtx p f tY nY Ω K z) {N : Subgroup G}
    (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁)
    (hN : N ∈ centralizingMembers Ω {z}) (hNK : N ≠ K) (hNT : N ≠ T) :
    N ≤ locLayer Ω e.u :=
  le_centralizingLayer (e.layer_mem_centralizingMembers_u c hT hTQ hN hNK hNT)

end Members

section Local

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K T : Subgroup G} {z : G}

omit [Finite G] in
theorem exists_lieSystemData_u (S : RouteDSetup p f K z) (hnab : ∃ x y : G, x * y ≠ y * x)
    (e : TwinElt K T z) (hu1 : e.u ≠ 1) :
    Nonempty (LieSystemData p f (locQuot (conjClass K) e.u) (locFamily (conjClass K) e.u)) :=
  NonClassical.exists_lieSystemData S.ih (singleton_not_subset_center hnab hu1)

omit [IsSimpleGroup G] in
theorem twin_indistinguishable (S : RouteDSetup p f K z) (hcen : Subgroup.center G = ⊥)
    {J J' : Subgroup G} (hJ : J ∈ conjClass K) (hJ' : J' ∈ conjClass K) {w : G}
    (hw : IsClassicalMember p f J w) (hw' : IsClassicalMember p f J' w) :
    ∀ N ∈ conjClass K, ((N = J ∨ Commutes N J) ↔ (N = J' ∨ Commutes N J')) := by
  have key : ∀ {A : Subgroup G}, A ∈ conjClass K → IsClassicalMember p f A w →
      ∀ N ∈ conjClass K, ((N = A ∨ Commutes N A) ↔ N ≤ Subgroup.centralizer ({w} : Set G)) := by
    intro A hA hwA N hN
    constructor
    · rintro (rfl | h)
      · exact le_centralizer_of_isClassicalMember hwA
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact h x hx w hwA.mem
    · intro hle
      rcases S.cp_at_member hcen hA hwA (L := N) ⟨hN, hle⟩ with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
  intro N hN
  rw [key hJ hw N hN, key hJ' hw' N hN]

end Local

end CFSG.ClassicalInvolution.RouteD.TwinY

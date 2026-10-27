module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

theorem exists_orderOf_eq_two_of_even_card {G : Type*} [Group G] [Finite G]
    (h : ¬ Odd (Nat.card G)) : ∃ x : G, orderOf x = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card G := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
  exact exists_prime_orderOf_dvd_card' 2 h2

theorem isClassicalMember_map_central {K C : Type} [Group K] [Finite K] [Group C] (θ : K →* C)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center K)
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup K} {z : K}
    (h : IsClassicalMember p f L z) (hz : θ z ≠ 1) :
    IsClassicalMember p f (L.map θ) (θ z) where
  orderOf_eq_two := by
    refine orderOf_eq_prime ?_ hz
    rw [← map_pow, ← h.orderOf_eq_two, pow_orderOf_eq_one, map_one]
  mem := Subgroup.mem_map_of_mem θ h.mem
  perfect := by
    have := h.perfect
    exact Group.IsPerfect.map θ
  subnormal := by
    have hA := isSubnormal_map θ h.subnormal
    set B := Subgroup.centralizer ({θ z} : Set C) with hB
    set A := (Subgroup.centralizer ({z} : Set K)).map θ with hA'
    have hle : A ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      rw [hB, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp hx]
    have hcomm : ⁅B, B⁆ ≤ A := by
      have h1 := commutator_le_map_centralizer θ hker z
      rwa [MonoidHom.range_eq_top.2 hθ, top_inf_eq] at h1
    have hnorm : (A.subgroupOf B).Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      have hc : ⁅(x : C), (a : C)⁆ ∈ A := hcomm (Subgroup.commutator_mem_commutator x.2 a.2)
      have e : ((x * a * x⁻¹ : B) : C) = ⁅(x : C), (a : C)⁆ * (a : C) := by
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e]
      exact A.mul_mem hc ha
    exact isSubnormal_trans hA (IsSubnormal.step hle hnorm (IsSubnormal.refl B))
  nonempty_equiv := by
    obtain ⟨e⟩ := h.nonempty_equiv
    set φ := θ.subgroupMap L with hφdef
    have hφ : Function.Surjective φ := MonoidHom.subgroupMap_surjective θ L
    have : Finite ↥(L.map θ) := Finite.of_surjective φ hφ
    have hkodd : Odd (Nat.card φ.ker) := by
      by_contra hne
      obtain ⟨x, hx⟩ := exists_orderOf_eq_two_of_even_card hne
      have hxk : θ ((x : L) : K) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
        simpa [hφdef] using this
      have hxL : orderOf (x : L) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
      have hxc : ((x : L) : K) ∈ Subgroup.center K := hker (MonoidHom.mem_ker.mpr hxk)
      have hne' : ((x : L) : K) ≠ z := fun h' => hz (by rw [← h']; exact hxk)
      exact false_of_two_commuting_involutions_sl2 hodd e (a := (x : L)) (b := ⟨z, h.mem⟩) hxL
        (by rw [Subgroup.orderOf_mk]; exact h.orderOf_eq_two)
        (Subtype.ext ((Subgroup.mem_center_iff.mp hxc z).symm))
        (fun hh => hne' (congrArg Subtype.val hh))
    exact ⟨(CFSG.ComponentClassification.OddKernel.coreQuotientEquiv φ hφ hkodd).symm.trans e⟩

theorem isClassicalMember_map_iso {Y Y' : Type} [Group Y] [Finite Y] [Group Y']
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (φ : Y ≃* Y') :
    IsClassicalMember p f (L.map φ.toMonoidHom) (φ z) := by
  refine isClassicalMember_map_central φ.toMonoidHom φ.surjective ?_ hodd h ?_
  · rw [(MonoidHom.ker_eq_bot_iff _).2 φ.injective]
    exact bot_le
  · intro h1
    have : z = 1 := φ.injective (by simpa using h1)
    have h2 := h.orderOf_eq_two
    rw [this, orderOf_one] at h2
    omega

theorem isClassicalMember_map_conj {Y : Type} [Group Y] [Finite Y]
    (hodd : Odd (Nat.card (GaloisField p f))) {L : Subgroup Y} {z : Y}
    (h : IsClassicalMember p f L z) (g : Y) :
    IsClassicalMember p f (L.map (MulAut.conj g).toMonoidHom) (g * z * g⁻¹) :=
  isClassicalMember_map_iso hodd h (MulAut.conj g)

end CFSG.ClassicalInvolution.ModelFacts

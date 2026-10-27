module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

section Loc

variable {G : Type} [Group G]

theorem exists_noncomm_order_four_q8 {V : Subgroup G} (e : ↥V ≃* QuaternionGroup 2) :
    ∃ a b : G, a ∈ V ∧ b ∈ V ∧ orderOf a = 4 ∧ orderOf b = 4 ∧ a * b ≠ b * a := by
  refine ⟨(e.symm (QuaternionGroup.a 1) : G), (e.symm (QuaternionGroup.xa 0) : G),
    (e.symm _).2, (e.symm _).2, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_a_one]
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, QuaternionGroup.orderOf_xa]
  · intro h
    have h1 : e.symm (QuaternionGroup.a 1) * e.symm (QuaternionGroup.xa 0) =
        e.symm (QuaternionGroup.xa 0) * e.symm (QuaternionGroup.a 1) := Subtype.ext h
    have h2 := congrArg e h1
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    revert h2
    decide

variable [Finite G]

theorem false_of_q8_centralized {z : G} {k : Kind} (hcl : IsClassicalKind k) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {U V X : Subgroup G} (halt : Lemma29Alt z k U) (hV2 : IsPGroup 2 ↥V)
    (hVq : Nonempty (↥V ≃* QuaternionGroup 2)) (hX : IsPGroup p ↥X)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) (hXV : X ≤ normalizer (V : Set G))
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x * u = u * x) (hVX : ⁅V, X⁆ = V) : False := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hVq
  obtain ⟨a₀, b₀, ha₀, hb₀, ha4, hb4, hab⟩ := exists_noncomm_order_four_q8 e
  set C : Subgroup G := centralizer (U : Set G) with hC
  have hXC : ∀ x ∈ X, x ∈ C := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hXU x hx u hu).symm
  have hVC : ∀ v ∈ V, v ∈ C := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun u hu => hUV u hu v hv
  have hXodd : ∀ x ∈ X, Nat.Coprime (orderOf x) 2 := by
    intro x hx
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hX) ⟨x, hx⟩
    have h1 : orderOf x = p ^ n := by
      rw [← Subgroup.orderOf_mk x hx]
      exact hn
    rw [h1]
    exact Nat.Coprime.pow_left n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  rcases halt with hN2 | ⟨-, hdih, -⟩ | ⟨hk, -⟩
  ·
    obtain ⟨N₂, hN₂C, hN₂n, hN₂odd, a, hidx⟩ := hN2
    have hxN : ∀ x ∈ X, x ∈ N₂ := by
      intro x hx
      have hxC' : x ∈ C := hXC x hx
      let q : ↥C ⧸ N₂.subgroupOf C := QuotientGroup.mk ⟨x, hxC'⟩
      have h1 : orderOf q ∣ orderOf x := by
        have := orderOf_map_dvd (QuotientGroup.mk' (N₂.subgroupOf C)) (⟨x, hxC'⟩ : ↥C)
        rwa [Subgroup.orderOf_mk] at this
      have h2 : orderOf q ∣ 2 ^ a := by
        have := orderOf_dvd_natCard q
        rwa [← Subgroup.index_eq_card, hidx] at this
      have h3 : orderOf q = 1 := by
        have hc : Nat.Coprime (orderOf q) 2 := Nat.Coprime.coprime_dvd_left h1 (hXodd x hx)
        have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right a hc) h2
        exact this
      have hq1 : q = 1 := orderOf_eq_one_iff.mp h3
      have : (⟨x, hxC'⟩ : ↥C) ∈ N₂.subgroupOf C := (QuotientGroup.eq_one_iff _).mp hq1
      exact this
    have hdisj : V ⊓ N₂ = ⊥ := isPGroup_two_inf_eq_bot_of_odd V N₂ hV2 hN₂odd
    have hcomm1 : ⁅V, X⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv x hx
      have hvC : v ∈ C := hVC v hv
      have hxN' : (⟨x, hXC x hx⟩ : ↥C) ∈ N₂.subgroupOf C := hxN x hx
      have hconj := hN₂n.conj_mem _ hxN' ⟨v, hvC⟩
      have hconj' : v * x * v⁻¹ ∈ N₂ := hconj
      have hc1 : ⁅v, x⁆ ∈ N₂ := by
        have : ⁅v, x⁆ = (v * x * v⁻¹) * x⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact N₂.mul_mem hconj' (N₂.inv_mem (hxN x hx))
      have hc2 : ⁅v, x⁆ ∈ V := by
        have h3 : x * v⁻¹ * x⁻¹ ∈ V := (mem_normalizer_iff.mp (hXV hx) v⁻¹).mp (V.inv_mem hv)
        have : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
        rw [this]
        exact V.mul_mem hv h3
      have : ⁅v, x⁆ ∈ V ⊓ N₂ := Subgroup.mem_inf.mpr ⟨hc2, hc1⟩
      rw [hdisj] at this
      exact this
    rw [hcomm1] at hVX
    have : a₀ ∈ (⊥ : Subgroup G) := by rw [hVX]; exact ha₀
    rw [Subgroup.mem_bot] at this
    rw [this, orderOf_one] at ha4
    omega
  ·
    have hXO : ∀ x ∈ X, x ∈ O2Of C := fun x hx => mem_O2Of_of_odd (hXC x hx) (hXodd x hx)
    have hVO : ∀ w ∈ V, w ∈ O2Of C := by
      have hle : V ≤ O2Of C := by
        rw [← hVX, Subgroup.commutator_le]
        intro a ha b hb
        have haC : a ∈ C := hVC a ha
        have hbO : b ∈ O2Of C := hXO b hb
        have e' : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by simp [commutatorElement_def, mul_assoc]
        rw [e']
        exact (O2Of C).mul_mem (mem_O2Of_conj haC hbO) ((O2Of C).inv_mem hbO)
      exact fun w hw => hle hw
    have hVsub : IsPGroup 2 ↥(V.subgroupOf (O2Of C)) :=
      hV2.of_equiv (Subgroup.subgroupOfEquivOfLe (fun w hw => hVO w hw)).symm
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P, hP⟩ := hVsub.exists_le_sylow
    obtain ⟨m, k', -, -, ⟨e'⟩⟩ := hdih P
    have hP' : ∀ a : G, ∀ ha : a ∈ V, (⟨a, hVO a ha⟩ : ↥(O2Of C)) ∈ (P : Subgroup ↥(O2Of C)) := by
      intro a ha
      exact hP (Subgroup.mem_subgroupOf.mpr ha)
    have hord : ∀ (a : G) (ha : a ∈ V), orderOf a = 4 →
        orderOf (⟨⟨a, hVO a ha⟩, hP' a ha⟩ : ↥P) = 4 := by
      intro a ha hao
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact hao
    have hcommP := dihedral_order_four_commute e' (hord a₀ ha₀ ha4) (hord b₀ hb₀ hb4)
    apply hab
    have := congrArg (fun t : ↥P => (((t : ↥(O2Of C)) : G))) hcommP
    simpa using this
  ·
    rcases hcl with rfl | ⟨ε, rfl⟩ <;> rcases hk with h | h <;> cases h

end Loc

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87

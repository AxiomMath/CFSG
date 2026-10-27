module

public import CFSG.GF2Type.Aschbacher1976Full.WidthForm
public import CFSG.GF2Type.CenterFour.BridgeLinear

public section

namespace CFSG.GF2Type.Aschbacher1976Full.Width

open CFSG CFSG.GF2Type.CenterFour Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Bounds

variable {z : G} {F : Subgroup G}

theorem isElemAbelian_subgroupOf {U : Subgroup G} (hUF : U ≤ F)
    (hU : CFSG.Open.IsElemAbelian 2 U) : CFSG.Open.IsElemAbelian 2 (U.subgroupOf F) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    have h := hU.1.is_comm.comm ⟨(a : G), (Subgroup.mem_subgroupOf.mp a.2)⟩
      ⟨(b : G), (Subgroup.mem_subgroupOf.mp b.2)⟩
    have h2 := congrArg Subtype.val h
    simpa using h2
  · intro x hx
    apply Subtype.ext
    have hx' : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
    have := hU.2 (x : G) hx'
    simpa using this

theorem bounds_F [Fact (Nat.Prime 2)] (hF : CData z F) (v : ℕ)
    (hcard : Nat.card ↥F = 2 ^ (2 * v + 2)) (Zs : Subgroup G)
    (hZs : ∀ x : ↥F, x ∈ Subgroup.center ↥F ↔ (x : G) ∈ Zs)
    (hZcyc : IsCyclic ↥(Subgroup.center ↥F)) (hZcard : Nat.card ↥(Subgroup.center ↥F) = 4) :
    (∀ U : Subgroup G, U ≤ F → CFSG.Open.IsElemAbelian 2 U → Nat.card U ≤ 2 ^ (v + 1)) ∧
    (∀ U : Subgroup G, U ≤ F → CFSG.Open.IsElemAbelian 2 U → U ⊓ Zs = ⊥ →
      Nat.card U ≤ 2 ^ v) ∧
    (∀ (s : ℕ) (f : Fin s → G), (∀ i, f i ∈ F) → (∀ i j, i ≠ j → ⁅f i, f j⁆ = z) →
      s ≤ 2 * v + 1) := by
  haveI := isEA_quot hF
  have hQcard : Nat.card (↥F ⧸ Subgroup.center ↥F) = 2 ^ (2 * v) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥F)
    rw [hcard, hZcard] at h
    have h2 : Nat.card (↥F ⧸ Subgroup.center ↥F) * 4 = 2 ^ (2 * v) * 4 := by
      rw [← h]
      ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h2
  have hdim : Module.finrank (ZMod 2) (Additive (↥F ⧸ Subgroup.center ↥F)) = 2 * v := by
    haveI : Fintype (Additive (↥F ⧸ Subgroup.center ↥F)) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (↥F ⧸ Subgroup.center ↥F))
    have hA : Nat.card (Additive (↥F ⧸ Subgroup.center ↥F)) = 2 ^ (2 * v) := by
      rw [← hQcard]
      exact Nat.card_congr Additive.ofMul
    rw [← Nat.card_eq_fintype_card, ZMod.card, hA] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  have hnd := bil_nondegenerate hF
  have halt := bil_alt hF
  have hrule := bil_hrule hF
  have hc : (⟨z, hF.zF⟩ : ↥F) ≠ 1 := fun h => hF.z1 (congrArg Subtype.val h)
  refine ⟨?_, ?_, ?_⟩
  · intro U hUF hU
    have hU' := isElemAbelian_subgroupOf hUF hU
    have h := card_le_of_elemAbelian (bil hF) hrule hdim hnd hc hZcyc hU'
    have hcardU : Nat.card ↥(U.subgroupOf F) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv
    rw [hcardU] at h
    exact h
  · intro U hUF hU hUZ
    have hU' := isElemAbelian_subgroupOf hUF hU
    have hdisj : U.subgroupOf F ⊓ Subgroup.center ↥F = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx1
      have hxZ : (x : G) ∈ Zs := (hZs x).mp hx2
      have hmem : (x : G) ∈ U ⊓ Zs := Subgroup.mem_inf.mpr ⟨hxU, hxZ⟩
      rw [hUZ, Subgroup.mem_bot] at hmem
      exact Subtype.ext (by simpa using hmem)
    have h := card_le_of_disjoint (bil hF) hrule hdim hnd hc hU' hdisj
    have hcardU : Nat.card ↥(U.subgroupOf F) = Nat.card ↥U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUF).toEquiv
    rw [hcardU] at h
    exact h
  · intro s f hfF hpair
    let f' : Fin s → ↥F := fun i => ⟨f i, hfF i⟩
    have hf' : ∀ i j, i ≠ j → ⁅f' i, f' j⁆ = (⟨z, hF.zF⟩ : ↥F) := by
      intro i j hij
      apply Subtype.ext
      simp only [Subgroup.coe_mul, commutatorElement_def]
      have := hpair i j hij
      rw [commutatorElement_def] at this
      simpa [f'] using this
    exact card_le_of_pairwise (bil hF) hrule hdim halt hc f' hf'

end Bounds

end CFSG.GF2Type.Aschbacher1976Full.Width

module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialBinaryActionCounterexample
public import CFSG.LocalAnalysis.RankThreeUC.Section5.MaxInvariantOddAbove
public import CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc59_pCoreOf_le (q : ℕ) (H : Subgroup G) : CFSG.Open.pCoreOf q H ≤ H := by
  intro x hx
  unfold CFSG.Open.pCoreOf at hx
  obtain ⟨a, _, ha⟩ := Subgroup.mem_map.mp hx
  rw [← ha]
  exact a.2

private theorem uc59_mem_centerP_iff (P : Subgroup G) (x : G) :
    x ∈ centerP P ↔ x ∈ P ∧ ∀ y ∈ P, x * y = y * x := by
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hx
    refine ⟨z.2, fun y hy => ?_⟩
    have := (Subgroup.mem_center_iff.1 hz) ⟨y, hy⟩
    have h2 := congrArg Subtype.val this
    simpa using h2.symm
  · rintro ⟨hxP, hc⟩
    refine Subgroup.mem_map.2 ⟨⟨x, hxP⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have := hc g.1 g.2
    simpa using this.symm

private theorem uc59_conj_mem (P : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (P : Set G))
    {x : G} (hx : x ∈ centerP P) : g * x * g⁻¹ ∈ centerP P := by
  rw [uc59_mem_centerP_iff] at hx ⊢
  obtain ⟨hxP, hc⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.1 hg x).1 hxP, fun y hy => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hg
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 hg' y).1 hy
  rw [inv_inv] at hy'
  have hc' := hc _ hy'
  calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by rw [hc']
    _ = y * (g * x * g⁻¹) := by group

theorem commutator_actorTwoCore_sup_actor_center_eq_bot {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) :
    ⁅twoCoreCommutator T B ⊔ B, centerP P⁆ = ⊥ := by
  classical
  have hp : p.Prime := h.oddPrimeClassTwoAction.setting.prime
  have hodd : Odd p := h.oddPrimeClassTwoAction.setting.odd
  have hZcard : Nat.card (centerP P) = p := by
    have h1 := h.extraspecial.2.2.2
    rw [show centerP P = (Subgroup.center ↥P).map P.subtype from rfl,
      Subgroup.card_map_of_injective P.subtype_injective]
    exact h1
  have hXodd : Odd (Nat.card (centerP P)) := by rw [hZcard]; exact hodd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hXcyc : IsCyclic (centerP P) := isCyclic_of_prime_card hZcard
  have hBT : B ⊔ T ≤ Subgroup.normalizer (P : Set G) :=
    sup_le h.oddPrimeClassTwoAction.setting.normB h.oddPrimeClassTwoAction.setting.normT
  have hNX : ∀ g ∈ Subgroup.normalizer (P : Set G),
      g ∈ Subgroup.normalizer ((centerP P : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact uc59_conj_mem P hg
    · intro hx
      have := uc59_conj_mem P (inv_mem hg) hx
      simpa [mul_assoc] using this
  have hB : B ≤ Subgroup.normalizer ((centerP P : Subgroup G) : Set G) :=
    fun b hb => hNX b (h.oddPrimeClassTwoAction.setting.normB hb)
  have hK : CFSG.Open.pCoreOf 2 (B ⊔ T) ≤ Subgroup.normalizer ((centerP P : Subgroup G) : Set G) :=
    fun k hk => hNX k (hBT ((uc59_pCoreOf_le 2 (B ⊔ T)) hk))
  have hS : twoCoreCommutator T B ≤ Subgroup.centralizer ((centerP P : Subgroup G) : Set G) := by
    have h1 : ⁅CFSG.Open.pCoreOf 2 (B ⊔ T), B⁆ ≤
        ⁅Subgroup.normalizer ((centerP P : Subgroup G) : Set G),
          Subgroup.normalizer ((centerP P : Subgroup G) : Set G)⁆ :=
      Subgroup.commutator_mono hK hB
    exact h1.trans (CFSG.GroupTheory.CoprimeActionSupport.CyclicNormalizerDerivedCentralizer.commutator_normalizer_le_centralizer
      (centerP P))
  have hXC : centerP P ≤ Subgroup.centralizer ((twoCoreCommutator T B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 hS
  obtain ⟨R, hR, hXR⟩ := exists_maxInvariantOdd_ge
    (Subgroup.centralizer ((twoCoreCommutator T B : Subgroup G) : Set G)) B (centerP P) hXC hXodd hB
  have hchar : ∀ φ : ↥B ≃* ↥B,
      Subgroup.map φ.toMonoidHom (B.subgroupOf B) = B.subgroupOf B := by
    intro φ
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 φ.surjective
  obtain ⟨_, h2, _⟩ := characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants h.oddPrimeClassTwoAction h.faithfulBinaryIrreducibleAction B le_rfl hchar
  have hXB : centerP P ≤ Subgroup.centralizer (B : Set G) := hXR.trans (h2 R hR)
  have hBX : B ≤ Subgroup.centralizer ((centerP P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.1 hXB
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (sup_le hS hBX)

end Section5
end CFSG.LocalAnalysis.RankThreeUC

module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitHS7Inner
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrders

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem center_eq_bot_of_equiv_A7 {Q : Type*} [Group Q] (e : Q ≃* alternatingGroup (Fin 7)) :
    center Q = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ center (alternatingGroup (Fin 7)) := by
    rw [mem_center_iff] at hz ⊢
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hz x]
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at h1
  rw [mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem nonempty_zStar_equiv_A7 {Y : Type*} [Group Y]
    (e : Y ⧸ pPrimeCore 2 Y ≃* alternatingGroup (Fin 7)) :
    Nonempty (Y ⧸ Open.fusionZStar Y ≃* alternatingGroup (Fin 7)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    (GSThmB.fusionZStar_eq_of_center_eq_bot (center_eq_bot_of_equiv_A7 e))).trans e⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_outer_properFixedComponent (hF : IsSimpleGroup ↥(generalizedFitting G)) {t : G}
    (ht : orderOf t = 2) (htF : t ∉ generalizedFitting G) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({t} : Set G))))
    (h7 : Nonempty (GSThmB.OddBar L ≃* alternatingGroup (Fin 7))) :
    ∃ σ : MulAut ↥(generalizedFitting G), orderOf σ = 2 ∧
      σ ∉ (MulAut.conj : ↥(generalizedFitting G) →* MulAut ↥(generalizedFitting G)).range ∧
      ProperFixedComponent σ (L.subgroupOf (generalizedFitting G)) ∧
      Nonempty (↥(L.subgroupOf (generalizedFitting G)) ⧸
        Open.fusionZStar ↥(L.subgroupOf (generalizedFitting G)) ≃* alternatingGroup (Fin 7)) := by
  have hnab := generalizedFitting_nonabelian hF h7
  have hLN := le_generalizedFitting hF hnab ht hLt hL
  set N := generalizedFitting G with hN
  have : N.Normal := AS76b.generalizedFitting_normal
  let σ : MulAut ↥N := MulAut.conjNormal t
  have hσapp : ∀ y : ↥N, ((σ y : ↥N) : G) = t * (y : G) * t⁻¹ := fun y => rfl
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y
    apply Subtype.ext
    rw [hσapp, hσapp, hti, ← mul_assoc, ← mul_assoc, htt, one_mul, mul_assoc, htt, mul_one]
  have hfixmem : ∀ y : ↥N, y ∈ fixedSubgroup σ ↔ (y : G) ∈ centralizer ({t} : Set G) := by
    intro y
    change σ y = y ↔ _
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, hσapp]
    constructor
    · intro h
      calc (y : G) * t = t * (y : G) * t⁻¹ * t := by rw [h]
        _ = t * (y : G) := by group
    · intro h
      rw [← h, mul_inv_cancel_right]
  have hfix : (fixedSubgroup σ).map N.subtype = centralizer ({t} : Set G) ⊓ N := by
    ext x
    simp only [mem_map, mem_inf, subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hfixmem y).mp hy, y.2⟩
    · rintro ⟨hx, hxN⟩
      exact ⟨⟨x, hxN⟩, (hfixmem ⟨x, hxN⟩).mpr hx, rfl⟩
  have hL'F : L.subgroupOf N ≤ fixedSubgroup σ := fun y hy =>
    (hfixmem y).mpr (hLt (mem_subgroupOf.mp hy))
  have hL'p : IsPComponent 2 ((L.subgroupOf N).subgroupOf (fixedSubgroup σ)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Burgoyne.isPComponent_subgroupOf_map_iff 2 Nat.prime_two N.subtype_injective, hfix,
      subgroupOf_map_subtype, inf_eq_left.mpr hLN]
    exact CatalogueBPrimeJoin.pComponent_subgroupOf_of_le (le_inf hLt hLN) inf_le_left hL
  have hcent : ∀ g : G, (∀ x ∈ N, x * g = g * x) → g ∈ N := fun g hg =>
    CFSG.centralizer_generalizedFitting_le G (mem_centralizer_iff.mpr hg)
  have hL'top : L.subgroupOf N ≠ ⊤ := by
    intro htop
    apply htF
    apply hcent
    intro x hx
    have hxL : x ∈ L := by
      have h1 : (⟨x, hx⟩ : ↥N) ∈ L.subgroupOf N := htop ▸ mem_top _
      exact mem_subgroupOf.mp h1
    exact mem_centralizer_singleton_iff.mp (hLt hxL)
  have hσ1 : σ ≠ 1 := by
    intro h1
    apply htF
    apply hcent
    intro x hx
    have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : G)) h1
    simp only [MulAut.one_apply] at h2
    change t * x * t⁻¹ = x at h2
    calc x * t = t * x * t⁻¹ * t := by rw [h2]
      _ = t * x := by group
  have hσ2 : orderOf σ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact MulEquiv.ext fun y => hσσ y) hσ1
  have hσout : σ ∉ (MulAut.conj : ↥N →* MulAut ↥N).range := by
    rintro ⟨n, hn⟩
    apply htF
    have hmem : (n : G)⁻¹ * t ∈ N := by
      apply hcent
      intro x hx
      have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨x, hx⟩ : ↥N) : G)) hn
      change (n : G) * x * (n : G)⁻¹ = t * x * t⁻¹ at h2
      calc x * ((n : G)⁻¹ * t) = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * t := by group
        _ = (n : G)⁻¹ * (t * x * t⁻¹) * t := by rw [h2]
        _ = ((n : G)⁻¹ * t) * x := by group
    have h3 : t = (n : G) * ((n : G)⁻¹ * t) := by group
    rw [h3]
    exact mul_mem n.2 hmem
  obtain ⟨e7⟩ := nonempty_oddBar_restrict hLN h7
  exact ⟨σ, hσ2, hσout, ⟨hσσ, hL'F, hL'p, hL'top⟩, nonempty_zStar_equiv_A7 e7⟩

end CFSG.ComponentClassification.HSFLit.HS7

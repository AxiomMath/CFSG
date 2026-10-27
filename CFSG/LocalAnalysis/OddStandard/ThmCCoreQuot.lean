module

public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.OddStandard.ThmCCoreOddCore
public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts

public section

namespace CFSG.OddStandard.ThmC.Core

open CFSG Subgroup CFSG.OddStandard.ThmC CFSG.OddStandard.ThmC.T
open CFSG.GH74.GLS.Bg.TwoGroups

variable {X : Type} [Group X] [Finite X]

section Quot

variable (Q : Subgroup X)

abbrev nzr : Subgroup X := normalizer (Q : Set X)

abbrev QuotN : Type := nzr Q ⧸ pPrimeCore 2 (nzr Q)

@[expose] def projN : nzr Q →* QuotN Q := QuotientGroup.mk' (pPrimeCore 2 (nzr Q))

omit [Finite X] in
theorem projN_surjective : Function.Surjective (projN Q) := QuotientGroup.mk'_surjective _

omit [Finite X] in
theorem projN_eq_one_iff (x : nzr Q) : projN Q x = 1 ↔ (x : X) ∈ oddCoreIn (nzr Q) := by
  rw [projN, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · intro h
    obtain ⟨y, hy, hyx⟩ := mem_oddCoreIn_iff.1 h
    have : y = x := Subtype.ext hyx
    rwa [this] at hy

variable {Q}

omit [Finite X] in
theorem le_nzr_of_normalizes {T : Subgroup X} (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) :
    T ≤ nzr Q := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hQn t ht h hh
  · intro hh
    have := hQn t⁻¹ (T.inv_mem ht) _ hh
    simpa [mul_assoc] using this

theorem projN_injOn {P : Subgroup X} (hP : IsPGroup 2 P) (hPle : P ≤ nzr Q) {x y : X}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : projN Q ⟨x, hPle hx⟩ = projN Q ⟨y, hPle hy⟩) : x = y := by
  have h1 : projN Q (⟨x, hPle hx⟩⁻¹ * ⟨y, hPle hy⟩) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rw [projN_eq_one_iff] at h1
  have h2 : x⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hx) hy
  have := eq_one_of_mem_inf_oddCore hP h2 h1
  exact inv_mul_eq_one.mp this

@[expose] noncomputable def sylowBar (T : Sylow 2 X) (hTH : (T : Subgroup X) ≤ nzr Q) :
    Sylow 2 (QuotN Q) :=
  Sylow.mapSurjective (projN_surjective Q) (T.subtype hTH)

theorem coe_sylowBar (T : Sylow 2 X) (hTH : (T : Subgroup X) ≤ nzr Q) :
    ((sylowBar T hTH : Sylow 2 (QuotN Q)) : Subgroup (QuotN Q)) =
      ((T : Subgroup X).subgroupOf (nzr Q)).map (projN Q) := by
  simp [sylowBar]

theorem pCore_quotN_ne_bot (hQ1 : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q) :
    pCore 2 (QuotN Q) ≠ ⊥ := by
  intro hbot
  have hnorm : (Q.subgroupOf (nzr Q)).Normal := Subgroup.normal_in_normalizer
  have hn : ((Q.subgroupOf (nzr Q)).map (projN Q)).Normal :=
    hnorm.map _ (projN_surjective Q)
  have hp : IsPGroup 2 ((Q.subgroupOf (nzr Q)).map (projN Q)) := by
    have : IsPGroup 2 (Q.subgroupOf (nzr Q)) := hQ2.comap_subtype
    exact this.map _
  have hle : (Q.subgroupOf (nzr Q)).map (projN Q) ≤ pCore 2 (QuotN Q) :=
    le_sSup ⟨hn, hp⟩
  rw [hbot, le_bot_iff] at hle
  apply hQ1
  rw [eq_bot_iff]
  intro q hq
  have hqH : q ∈ nzr Q := (Subgroup.le_normalizer (H := Q)) hq
  have hmem : projN Q ⟨q, hqH⟩ ∈ (Q.subgroupOf (nzr Q)).map (projN Q) :=
    ⟨⟨q, hqH⟩, hq, rfl⟩
  rw [hle, Subgroup.mem_bot] at hmem
  have h1 : (q : X) ∈ oddCoreIn (nzr Q) := (projN_eq_one_iff Q ⟨q, hqH⟩).1 hmem
  exact Subgroup.mem_bot.2 (eq_one_of_mem_inf_oddCore hQ2 hq h1)

theorem concl_quotN (hS2 : O2Structure) (T : Sylow 2 X) (hT : IsT (T : Subgroup X))
    (hQ1 : Q ≠ ⊥) (hQT : Q ≤ T) (hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q) :
    Concl (QuotN Q) (sylowBar T (le_nzr_of_normalizes hQn)) := by
  have hTH : (T : Subgroup X) ≤ nzr Q := le_nzr_of_normalizes hQn
  have hQ2 : IsPGroup 2 Q := T.isPGroup'.to_le hQT
  refine hS2 (QuotN Q) (pPrimeCore_quotient_eq_bot (G := nzr Q) Nat.prime_two)
    (pCore_quotN_ne_bot hQ1 hQ2) _ ?_
  obtain ⟨e⟩ := hT
  let T' : Subgroup (nzr Q) := (T : Subgroup X).subgroupOf (nzr Q)
  have hinj : Function.Injective ((projN Q).comp T'.subtype) := by
    intro a b hab
    have hx : ((a : nzr Q) : X) ∈ (T : Subgroup X) := a.2
    have hy : ((b : nzr Q) : X) ∈ (T : Subgroup X) := b.2
    exact Subtype.ext (Subtype.ext (projN_injOn T.isPGroup' hTH hx hy hab))
  let φ : T' →* T'.map (projN Q) :=
    ((projN Q).comp T'.subtype).codRestrict (T'.map (projN Q)) (fun x => ⟨x, x.2, rfl⟩)
  have hφ : Function.Bijective φ :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => by
      obtain ⟨x, hx, hxy⟩ := y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let e1 : T' ≃* T'.map (projN Q) := MulEquiv.ofBijective φ hφ
  rw [coe_sylowBar]
  exact ⟨e1.symm.trans ((Subgroup.subgroupOfEquivOfLe hTH).trans e)⟩

end Quot

end CFSG.OddStandard.ThmC.Core

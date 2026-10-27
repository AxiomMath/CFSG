module

public import CFSG.RankThree.PartOne.KC.UnitaryGoodModel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel

theorem exists_two_lift_of_le_primeFormD {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {n : ℕ} (hn : 3 ≤ n) (hne : ¬(n = 3 ∧ ℓ ^ f = 2))
    {V E : Subgroup (MulAut (primeFormP h (idGram K n)))} (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥)
    (hVD : V ≤ primeFormD h (idGram K n)) (hEV : ∀ c ∈ E, ∀ v ∈ V, c * v * c⁻¹ ∈ V) :
    ∃ T₂ : Subgroup (GL (Fin n) K), IsPGroup 2 T₂ ∧ T₂ ≠ ⊥ ∧
      T₂ ≤ primeFormUnitary h (idGram K n) ∧
      ∀ X : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) X ∈ E →
        ∀ t ∈ T₂, (X : GL (Fin n) K) * t * (X : GL (Fin n) K)⁻¹ ∈ T₂ := by
  classical
  have := h.finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U := primeFormUnitary h (idGram K n)
  let ρ := primeFormConjHom h (idGram K n)
  let Vt : Subgroup U := V.comap ρ
  let Tl : Subgroup (GL (Fin n) K) := Vt.map U.subtype
  have hconj : ∀ X : U, ρ X ∈ E → ∀ t ∈ Tl,
      (X : GL (Fin n) K) * t * (X : GL (Fin n) K)⁻¹ ∈ Tl := by
    rintro X hX _ ⟨g, hg, rfl⟩
    refine ⟨X * g * X⁻¹, ?_, rfl⟩
    show ρ (X * g * X⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hEV _ hX _ hg
  haveI : Group.IsNilpotent V := hV2.isNilpotent
  let ψ : Vt →* V := MonoidHom.codRestrict (ρ.comp Vt.subtype) V (fun x => x.2)
  have hψ : ψ.ker ≤ Subgroup.center Vt := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : ρ (x : U) = 1 := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (commute_of_mem_ker_of_ne hn hne hx1 (y : U)).symm.eq
  have hψs : Function.Surjective ψ := by
    rintro ⟨v, hv⟩
    obtain ⟨A, hA⟩ := hVD hv
    exact ⟨⟨A, show ρ A ∈ V from hA ▸ hv⟩, Subtype.ext hA⟩
  haveI : Group.IsNilpotent Vt := Subgroup.isNilpotent_of_ker_le_center ψ hψ
  let e : Vt ≃* Tl := Vt.equivMapOfInjective U.subtype Subtype.val_injective
  haveI : Group.IsNilpotent Tl := Group.nilpotent_of_mulEquiv e
  have h2V : 2 ∣ Nat.card V := by
    rcases hV2.card_eq_or_dvd with h1 | h2
    · exact absurd (Subgroup.eq_bot_of_card_eq V h1) hV
    · exact h2
  have h2Tl : 2 ∣ Nat.card Tl := by
    rw [← Nat.card_congr e.toEquiv]
    exact h2V.trans (Subgroup.card_dvd_of_surjective hψs)
  obtain ⟨P⟩ : Nonempty (Sylow 2 Tl) := inferInstance
  have hPc : (P : Subgroup Tl).Characteristic := Sylow.characteristic_of_normal P inferInstance
  let φ : ∀ X : U, ρ X ∈ E → Tl ≃* Tl := fun X hX => MulEquiv.ofBijective
    (((MulAut.conj (X : GL (Fin n) K)).toMonoidHom.comp Tl.subtype).codRestrict Tl
      (fun t => hconj X hX t t.2))
    (Finite.injective_iff_bijective.mp (fun a b hab =>
      Subtype.ext ((MulAut.conj (X : GL (Fin n) K)).injective (congrArg Subtype.val hab))))
  refine ⟨(P : Subgroup Tl).map Tl.subtype, P.isPGroup'.map _, ?_, ?_, ?_⟩
  · intro hbot
    exact P.ne_bot_of_dvd_card h2Tl
      ((Subgroup.map_eq_bot_iff_of_injective _ Subtype.val_injective).mp hbot)
  · rintro _ ⟨x, -, rfl⟩
    obtain ⟨g, -, hg⟩ := x.2
    show (x : GL (Fin n) K) ∈ U
    rw [← hg]
    exact g.2
  · rintro X hX _ ⟨x, hx, rfl⟩
    have hmem : φ X hX x ∈ (P : Subgroup Tl) := by
      rw [← Subgroup.characteristic_iff_map_eq.mp hPc (φ X hX)]
      exact Subgroup.mem_map_of_mem _ hx
    exact ⟨φ X hX x, hmem, rfl⟩

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end

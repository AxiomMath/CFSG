module

public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.Quasithin.Background.SmithCurtisChevType

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley

section Twist

variable {τ : Tag} {K : Type} [Field K]

theorem entrywise_torusElt' (σ : K ≃+* K) (i : Fin τ.rank) (t : Kˣ) :
    Units.map (entrywiseHom σ.toRingHom) (torusElt τ K i t) =
      torusElt τ K i (Units.map σ.toRingHom.toMonoidHom t) := by
  rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit]
  refine Units.ext ?_
  have h := entrywise_rootDiag (τ := τ) σ.toRingHom (fun j => t ^ τ.cartan i j)
  refine h.trans ?_
  congr 1
  funext j
  simp [map_zpow]

variable [Finite K] [CharP K 2]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {m : ℕ}

theorem chi_eq_of_twist (ρ : Representation k (adjointGroup τ K) (Fin m → k)) (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K 2 hw ρ y χ J) (φ : MulAut (adjointGroup τ K))
    (g : adjointGroup τ K) (σ : K ≃+* K)
    (hφ : ∀ h : adjointGroup τ K, (φ h : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹)
    (B : Module.End k (Fin m → k)) (hB : IsUnit B)
    (hBρ : ∀ s, B * ρ s = ρ (φ s) * B) (i : Fin τ.rank) (t : Kˣ) :
    χ (dC τ K i (Units.map σ.toRingHom.toMonoidHom t)) = χ (dC τ K i t) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  let ψ : adjointGroup τ K →* adjointGroup τ K :=
    (MulAut.conj g⁻¹).toMonoidHom.comp φ.toMonoidHom
  have hψ : ∀ s, (ψ s : ModGL τ K) = Units.map (entrywiseHom σ.toRingHom) (s : ModGL τ K) := by
    intro s
    show (g⁻¹ * φ s * g⁻¹⁻¹ : adjointGroup τ K).1 = _
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hφ s]
    simp [mul_assoc]
  have hψinj : Function.Injective ψ := by
    intro a b h
    apply φ.injective
    have := congrArg (fun x => g * x * g⁻¹) h
    simpa [ψ, mul_assoc] using this
  set B' : Module.End k (Fin m → k) := ρ g⁻¹ * B with hB'
  have hρunit : ∀ s, IsUnit (ρ s) := fun s =>
    ⟨⟨ρ s, ρ s⁻¹, by rw [← map_mul, mul_inv_cancel, map_one], by
      rw [← map_mul, inv_mul_cancel, map_one]⟩, rfl⟩
  have hB'unit : IsUnit B' := (hρunit g⁻¹).mul hB
  have hB'ρ : ∀ s, B' * ρ s = ρ (ψ s) * B' := by
    intro s
    have e : g⁻¹ * φ s = ψ s * g⁻¹ := by
      show g⁻¹ * φ s = g⁻¹ * φ s * g⁻¹⁻¹ * g⁻¹
      group
    rw [hB', mul_assoc, hBρ, ← mul_assoc, ← map_mul, e, map_mul, mul_assoc]
  have hUψ : ∀ u ∈ (chevDatum τ K 2 hw).U, ψ u ∈ (chevDatum τ K 2 hw).U := by
    intro u hu
    have hu' : (u : ModGL τ K) ∈ posUnipotent τ K := hu
    have hmap := (chevalley_root_character_and_field_conjugation τ K).2.2.2.2.1 σ |>.2.1
    show (ψ u : ModGL τ K) ∈ posUnipotent τ K
    rw [hψ]
    rw [← hmap]
    exact ⟨_, hu', rfl⟩
  let ψU : (chevDatum τ K 2 hw).U → (chevDatum τ K 2 hw).U := fun u => ⟨ψ u, hUψ u u.2⟩
  have hψUinj : Function.Injective ψU := fun a b h =>
    Subtype.ext (hψinj (congrArg Subtype.val h))
  have hψUsurj : Function.Surjective ψU := Finite.surjective_of_injective hψUinj
  have hy1 : B' y ∈ (chevDatum τ K 2 hw).fixU ρ := by
    intro u' hu'
    obtain ⟨u, hu⟩ := hψUsurj ⟨u', hu'⟩
    have hu2 : ψ u = u' := congrArg Subtype.val hu
    rw [← hu2]
    have := congrArg (fun f : Module.End k (Fin m → k) => f y) (hB'ρ u)
    simp only [Module.End.mul_apply] at this
    rw [← this, ht.1 u u.2]
  have hy10 : B' y ≠ 0 := by
    intro h0
    have hbij := (Module.End.isUnit_iff B').1 hB'unit
    exact ht.2.1 (hbij.injective (by rw [h0, map_zero]))
  obtain ⟨c, hc⟩ := (chevDatum τ K 2 hw).fixU_eq_smul hρ hμ hy1
  have hH : dC τ K i t ∈ (chevDatum τ K 2 hw).H := dC_mem_H i t
  have hψd : ψ (dC τ K i t) = dC τ K i (Units.map σ.toRingHom.toMonoidHom t) := by
    apply Subtype.ext
    rw [hψ]
    exact entrywise_torusElt' σ i t
  have e1 : ρ (ψ (dC τ K i t)) (B' y) = χ (dC τ K i t) • B' y := by
    have := congrArg (fun f : Module.End k (Fin m → k) => f y) (hB'ρ (dC τ K i t))
    simp only [Module.End.mul_apply] at this
    rw [← this, ht.2.2.1 _ hH, map_smul]
  have e2 : ρ (ψ (dC τ K i t)) (B' y) =
      χ (dC τ K i (Units.map σ.toRingHom.toMonoidHom t)) • B' y := by
    rw [hψd, hc, map_smul, ht.2.2.1 _ (dC_mem_H i _), smul_comm]
  exact smul_left_injective k hy10 (e2.symm.trans e1)

end Twist

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107XCentral
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107ETwB2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I107X

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped IsMulCommutative


set_option synthInstance.maxHeartbeats 400000 in
theorem simplyLaced_pRank_ge {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (Ψ : List (Fin τ.rank → ℤ))
    (hΨ : PsiOK τ Ψ = true) (hnd : Ψ.Nodup)
    (hchain : ∀ γ ∈ Ψ, ∃ β β' : Fin τ.rank → ℤ, chainOK τ Ψ γ β β' = true)
    [Finite (AdjointQuotient τ K)] :
    Ψ.length * n ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (AdjointQuotient τ K)) := by
  have hS : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr hτ
  obtain ⟨hroot, -, hpos⟩ := PsiOK_spec hΨ
  haveI : IsMulCommutative (Subgroup.closure (rootSet τ K Ψ)) :=
    rootSet_isMulCommutative hS hroot hpos
  have h2 : (2 : K) = 0 := CFSG.LocalAnalysis.GLTheoremA.I107G.two_eq_zero_of_card hn hK
  let ψ : Fin Ψ.length → Fin τ.rank → ℤ := fun i => Ψ.get i
  have hψ : ∀ i, ψ i ∈ Ψ := fun i => List.get_mem Ψ i
  have hinj : Function.Injective ψ := List.nodup_iff_injective_get.1 hnd
  let Φ : (Fin Ψ.length → K) → ↥(Subgroup.closure (rootSet τ K Ψ)) :=
    fun x => ∏ i, fE ψ hψ i (x i)
  have hΦadd : ∀ x y, Φ (x + y) = Φ x * Φ y := by
    intro x y
    simp only [Φ, Pi.add_apply, fE_add, Finset.prod_mul_distrib]
  let Φh : Multiplicative (Fin Ψ.length → K) →* ↥(Subgroup.closure (rootSet τ K Ψ)) :=
    MonoidHom.mk' (fun x => Φ (Multiplicative.toAdd x))
      (fun x y => by rw [toAdd_mul]; exact hΦadd _ _)
  let Fq : Multiplicative (Fin Ψ.length → K) →* AdjointQuotient τ K :=
    (QuotientGroup.mk' (Subgroup.center (adjointGroup τ K))).comp
      ((Subgroup.closure (rootSet τ K Ψ)).subtype.comp Φh)
  have hinjFq : Function.Injective Fq := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : (Φ (Multiplicative.toAdd a) : adjointGroup τ K) ∈
        Subgroup.center (adjointGroup τ K) :=
      (QuotientGroup.eq_one_iff _).1 ha
    have hx : Multiplicative.toAdd a = 0 := by
      funext i
      exact central_coeff_zero hτ hΨ hchain ψ hψ hinj (Multiplicative.toAdd a) hz i
    exact Multiplicative.toAdd.injective (by rw [hx, toAdd_one])
  have hcard : Nat.card Fq.range = 2 ^ (n * Ψ.length) := by
    have e1 := Nat.card_congr (MonoidHom.ofInjective hinjFq).toEquiv
    rw [← e1, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, hK, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul]
  have hE : CFSG.Open.IsElemAbelian 2 Fq.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨q, hq⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hp, ← hq, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨p, rfl⟩ := MonoidHom.mem_range.1 hx
      have hA : ∀ v : Fin Ψ.length → K, v + v = 0 := fun v => by
        ext i
        simp [← two_mul, h2]
      have hsq : p ^ 2 = 1 := by
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, two_nsmul, hA]
      rw [← map_pow, hsq, map_one]
  have hk := CFSG.LocalAnalysis.GLTheoremA.I107E.pRank_two_ge Fq.range hE hcard
  rw [mul_comm]
  exact hk

end CFSG.LocalAnalysis.GLTheoremA.I107X

end

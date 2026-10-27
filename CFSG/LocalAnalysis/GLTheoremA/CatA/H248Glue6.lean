module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue2

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H248

open CFSG.Open
open scoped commutatorElement

theorem commutator_eq_top_of_surjective {E F : Type} [Group E] [Group F] (f : E →* F)
    (hf : Function.Surjective f) (hE : commutator E = ⊤) : commutator F = ⊤ := by
  have htop : Subgroup.map f (⊤ : Subgroup E) = ⊤ := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hf]
  have h : Subgroup.map f (commutator E) = commutator F := by
    rw [commutator_def E, commutator_def F]
    rw [Subgroup.map_commutator ⊤ ⊤ f, htop]
  rw [hE, htop] at h
  exact h.symm

theorem exists_elemAbelian_mulAut_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {p : ℕ}
    (A : Subgroup (MulAut S)) (hA : CFSG.Open.IsElemAbelian p A) :
    ∃ A' : Subgroup (MulAut T), CFSG.Open.IsElemAbelian p A' ∧ Nat.card A' = Nat.card A := by
  have hF : Function.Injective (mulAutConjHom e) := mulAutConjHom_injective e
  refine ⟨A.map (mulAutConjHom e), isElemAbelian_map _ hF hA, ?_⟩
  exact (Nat.card_congr (Subgroup.equivMapOfInjective A _ hF).toEquiv).symm

theorem pRank_mono {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 2 ≤ p) {H H' : Subgroup G}
    (hHH' : H ≤ H') : CFSG.Open.pRank p H ≤ CFSG.Open.pRank p H' := by
  refine csSup_le' ?_
  rintro k ⟨E, hEH, hE, hcard⟩
  exact le_pRank_of_elemAbelian hp (hEH.trans hHH') hE hcard

theorem quotient_quotient_map_equiv {K : Type} [Group K] (W N : Subgroup K) [W.Normal] [N.Normal]
    (hWN : W ≤ N) : Nonempty (((K ⧸ W) ⧸ N.map (QuotientGroup.mk' W)) ≃* (K ⧸ N)) := by
  haveI : (N.map (QuotientGroup.mk' W)).Normal := Subgroup.Normal.map inferInstance _
    (QuotientGroup.mk'_surjective W)
  let χ : K →* ((K ⧸ W) ⧸ N.map (QuotientGroup.mk' W)) :=
    (QuotientGroup.mk' (N.map (QuotientGroup.mk' W))).comp (QuotientGroup.mk' W)
  have hχ : Function.Surjective χ := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨x, rfl⟩
  have hker : χ.ker = N := by
    ext x
    simp only [MonoidHom.mem_ker, χ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
      have h1 : (n⁻¹ * x) ∈ W := by
        simp only [QuotientGroup.mk'_apply] at hnx
        exact QuotientGroup.eq.mp hnx
      have h2 : x = n * (n⁻¹ * x) := by group
      rw [h2]
      exact N.mul_mem hn (hWN h1)
    · intro hx
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective χ hχ)).symm⟩

theorem map_mk_le_center {K : Type} [Group K] (W N : Subgroup K) [W.Normal]
    (hcomm : ∀ n ∈ N, ∀ k : K, ⁅n, k⁆ ∈ W) :
    N.map (QuotientGroup.mk' W) ≤ Subgroup.center (K ⧸ W) := by
  rintro _ ⟨n, hn, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
  have hc : ⁅n⁻¹, k⁻¹⁆ ∈ W := hcomm n⁻¹ (N.inv_mem hn) k⁻¹
  have hid : (k * n)⁻¹ * (n * k) = ⁅n⁻¹, k⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hid]
  exact hc

end CFSG.LocalAnalysis.GLTheoremA.H248

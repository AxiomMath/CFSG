module

public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

variable {τ : Tag} {K : Type} [Field K]

theorem rootDiagAut_eq_exactNormalAut
    (a : Fin τ.rank → Kˣ) :
    rootDiagAut τ K a = exactNormalAut τ K a 1 0 :=
  MulEquiv.ext fun g => Subtype.ext (by
    rw [coe_rootDiagAut, coe_exactNormalAut, exactQ_zero, inv_one, mul_one, mul_one]
    congr 2
    exact (Units.ext (entrywise_id _)).symm)

theorem monomialHom_transpose_cartan (t : Fin τ.rank → Kˣ) :
    CFSG.LocalAnalysis.ComponentInitial.monomialHom τ.cartan.transpose t = cartanChar t := by
  funext l
  rw [CFSG.LocalAnalysis.ComponentInitial.monomialHom_apply]
  rfl

theorem rootDiagAut_cartanChar_mem_inner
    (t : Fin τ.rank → Kˣ) :
    rootDiagAut τ K (cartanChar t) ∈ inner (adjointGroup τ K) := by
  have hmem : ((List.finRange τ.rank).map fun j => torusElt τ K j (t j)).prod ∈
      adjointGroup τ K := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hg
    exact torusElt_mem_adjointGroup j _
  refine ⟨⟨_, hmem⟩, MulEquiv.ext fun g => Subtype.ext ?_⟩
  rw [coe_rootDiagAut, ← list_prod_torusElt_eq_rootDiagUnit]
  rfl

theorem exists_outer_hom_E
    [Finite K] (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    ∃ Φ : Outer (adjointGroup τ K) →* RingAut K × Multiplicative (ZMod (exactE τ)),
      Function.Surjective Φ ∧
      Φ.ker = ((QuotientGroup.mk' (inner (adjointGroup τ K))).comp (rootDiagAutHom τ K)).range ∧
      Nat.card Φ.ker ∣ τ.cartan.det.natAbs := by
  obtain ⟨Θ, hsurj, -, hker, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  have hkerΘ : ∀ α : MulAut (adjointGroup τ K),
      α ∈ Θ.ker ↔ ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        α = MulAut.conj g * rootDiagAut τ K a := by
    intro α
    rw [hker]
    constructor
    · rintro ⟨g, a, h⟩
      refine ⟨g, a, MulEquiv.ext fun x => Subtype.ext ?_⟩
      rw [h x, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
    · rintro ⟨g, a, rfl⟩
      refine ⟨g, a, fun x => ?_⟩
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_rootDiagAut, Subgroup.coe_inv]
      simp only [mul_assoc]
  have h1 : rootDiagAut τ K 1 = 1 := (rootDiagAutHom τ K).map_one
  have hinn : inner (adjointGroup τ K) ≤ Θ.ker := by
    rintro _ ⟨g, rfl⟩
    exact (hkerΘ _).2 ⟨g, 1, by rw [h1, mul_one]⟩
  set ρ := (QuotientGroup.mk' (inner (adjointGroup τ K))).comp (rootDiagAutHom τ K)
  have hΦsurj : Function.Surjective (QuotientGroup.lift (inner (adjointGroup τ K)) Θ hinn) :=
    fun y => by
      obtain ⟨α, rfl⟩ := hsurj y
      exact ⟨α, QuotientGroup.lift_mk _ hinn α⟩
  have hkerΦ : (QuotientGroup.lift (inner (adjointGroup τ K)) Θ hinn).ker = ρ.range := by
    refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (inner (adjointGroup τ K)) x
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.lift_mk] at hx
      obtain ⟨g, a, rfl⟩ := (hkerΘ _).1 hx
      refine ⟨a, ?_⟩
      change (QuotientGroup.mk (rootDiagAut τ K a) : Outer (adjointGroup τ K)) =
        QuotientGroup.mk' (inner (adjointGroup τ K)) (MulAut.conj g * rootDiagAut τ K a)
      rw [map_mul, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff
        (N := inner (adjointGroup τ K)) (MulAut.conj g)).2 (MonoidHom.mem_range.2 ⟨g, rfl⟩),
        one_mul]
      rfl
    · rintro _ ⟨a, rfl⟩
      change QuotientGroup.lift (inner (adjointGroup τ K)) Θ hinn
        (QuotientGroup.mk (rootDiagAut τ K a)) = 1
      rw [QuotientGroup.lift_mk]
      exact (hkerΘ _).2 ⟨1, a, by rw [map_one, one_mul]⟩
  refine ⟨QuotientGroup.lift (inner (adjointGroup τ K)) Θ hinn, hΦsurj, hkerΦ, ?_⟩
  have hle : (CFSG.LocalAnalysis.ComponentInitial.monomialHom (G := Kˣ)
      τ.cartan.transpose).range ≤ ρ.ker := by
    rintro _ ⟨t, rfl⟩
    rw [MonoidHom.mem_ker, monomialHom_transpose_cartan]
    change (QuotientGroup.mk (rootDiagAut τ K (cartanChar t)) : Outer (adjointGroup τ K)) = 1
    exact (QuotientGroup.eq_one_iff _).2 (rootDiagAut_cartanChar_mem_inner t)
  rw [hkerΦ, ← Subgroup.index_ker, ← Matrix.det_transpose]
  exact (Subgroup.index_dvd_of_le hle).trans (index_range_monomialHom_dvd K _).2

theorem ordProj_two_six : ordProj[2] 6 = 2 := by
  have h : (6 : ℕ).factorization 2 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
  rw [h, pow_one]

theorem ordinary_E_outer_order_Cartan_divisor
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = p ^ f)
    (d e : ℕ)
    (hde : (τ = .E6 ∧ d = 3 ∧ e = 2) ∨ (τ = .E7 ∧ d = 2 ∧ e = 1) ∨ (τ = .E8 ∧ d = 1 ∧ e = 1)) :
    Nat.card (Outer (adjointGroup τ K)) ∣ d * e * f ∧
      ordProj[2] (Nat.card (Outer (adjointGroup τ K))) ≤ 2 * ordProj[2] f := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  obtain ⟨Φ, hsurj, -, hdvd⟩ := exists_outer_hom_E (K := K) hτ
  have hcard : Nat.card (Outer (adjointGroup τ K)) = Nat.card Φ.ker * (f * exactE τ) := by
    rw [← Subgroup.card_mul_index Φ.ker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj,
      Subgroup.card_top, Nat.card_prod, (card_ringAut_and_isCyclic hp K hK).1,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hde' : τ.cartan.det.natAbs = d ∧ exactE τ = e := by
    rcases hde with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rw [det_cartan_E6]
      exact ⟨rfl, rfl⟩
    · rw [det_cartan_E7]
      exact ⟨rfl, rfl⟩
    · rw [det_cartan_E8]
      exact ⟨rfl, rfl⟩
  have hmain : Nat.card (Outer (adjointGroup τ K)) ∣ d * e * f := by
    rw [hcard, show d * e * f = d * (f * e) by ring, ← hde'.1, ← hde'.2]
    exact Nat.mul_dvd_mul_right hdvd _
  refine ⟨hmain, ?_⟩
  have hf0 : f ≠ 0 := by omega
  have h6 : Nat.card (Outer (adjointGroup τ K)) ∣ 6 * f := by
    refine hmain.trans (Nat.mul_dvd_mul_right ?_ f)
    rcases hde with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> decide
  have h2 := Nat.ordProj_dvd_ordProj_of_dvd (by positivity) h6 2
  rw [Nat.ordProj_mul 2 (by norm_num) hf0, ordProj_two_six] at h2
  exact Nat.le_of_dvd (by positivity) h2

end CFSG.LieType.Chevalley

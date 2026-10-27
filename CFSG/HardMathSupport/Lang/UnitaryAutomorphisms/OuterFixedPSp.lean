module

public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield

public section

namespace CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSp)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.CASymplecticSubfield
open CFSG.RankThree.Classical.SteinbergBY (symplectic_prime_semilinear_field_descent)
open CFSG.HardMathSupport.Lang.Coordinator
open CFSG.ComponentClassification.UnbalancedCatalog (descentField)

theorem mem_of_pow_eq_one_of_relIndex_dvd_two {G : Type*} [Group G] {H D : Subgroup G} [H.Normal]
    (hrel : H.relIndex D ∣ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : G} (hβD : β ∈ D)
    (hβp : β ^ p = 1) : β ∈ H := by
  have : (H.subgroupOf D).Normal := inferInstance
  have h1 : orderOf (QuotientGroup.mk (⟨β, hβD⟩ : D) : D ⧸ H.subgroupOf D) ∣ p := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow]
    have : (⟨β, hβD⟩ : D) ^ p = 1 := Subtype.ext hβp
    rw [this]
    rfl
  have h2 : orderOf (QuotientGroup.mk (⟨β, hβD⟩ : D) : D ⧸ H.subgroupOf D) ∣ 2 :=
    (_root_.orderOf_dvd_natCard _).trans hrel
  rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
  · have h4 := orderOf_eq_one_iff.mp h3
    exact (QuotientGroup.eq_one_iff (N := H.subgroupOf D) _).mp h4
  · exact absurd (h3 ▸ h2 : p ∣ 2) (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd))

theorem mem_of_pow_eq_one_of_index_dvd_two {G : Type*} [Group G] {E : Subgroup G}
    (hidx : E.index ∣ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {β : G} (hβp : β ^ p = 1) :
    β ∈ E := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
  · rw [Subgroup.index_eq_one.mp h]; exact Subgroup.mem_top _
  · haveI : E.Normal := Subgroup.normal_of_index_eq_two h
    exact mem_of_pow_eq_one_of_relIndex_dvd_two (H := E) (D := ⊤)
      (by rw [Subgroup.relIndex_top_right, h]) hp hp2 (Subgroup.mem_top _) hβp


theorem outerFixedOrderBoundAt_PSp : OuterFixedOrderBoundAt .PSp := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 hdiv _ α hαp hαin
  left
  have hcl : StatedClassicalModel K .PSp n ℓ f := by
    rcases hmodel with ⟨-, hcl⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hcl
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  classical
  obtain ⟨⟨hℓ, hf, hn, -⟩, F, hF, hFin, hFcard, ⟨e⟩⟩ := hcl
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, -, -, -, hidx, hDH, hdesc⟩ :=
    symplectic_prime_semilinear_field_descent hℓ hf hn hFcard
  set β := MulAut.congr e α with hβdef
  have hβp : β ^ p = 1 := by rw [hβdef, ← map_pow, hαp, map_one]
  have hβout : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (StatedProj (StatedSp n F)) :=
    fun hin => hαin ((congr_mem_inner_iff e α).mp hin)
  rw [← card_fixedSubgroup_congr e α]
  have hβ1 : β ≠ 1 := fun h1 =>
    hβout (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner _).one_mem)
  have hβord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ spSemilinearAutGroup n F := mem_of_pow_eq_one_of_index_dvd_two hidx hp hp2 hβp
  by_cases hD : β ∈ spLinearAutGroup n F
  · exfalso
    haveI := CFSG.ComponentClassification.OuterAutomorphisms.inner_normal (StatedProj (StatedSp n F))
    exact hβout (mem_of_pow_eq_one_of_relIndex_dvd_two
      (H := CFSG.ComponentClassification.OuterAutomorphisms.inner (StatedProj (StatedSp n F)))
      (D := spLinearAutGroup n F) (hDH.trans (Nat.gcd_dvd_left 2 _)) hp hp2 hD hβp)
  obtain ⟨hpf, σ, hσord, hcardk, h, hh, hβh⟩ := hdesc p hp β hβE hD hβord
  have hcard1 : Nat.card (fixedSubgroup β) = Nat.card (fixedSubgroup (fieldAut n F σ)) := by
    refine (card_fixedSubgroup_eq_of_intertwine (h : MulAut _) (fieldAut n F σ) β fun x => ?_).symm
    rw [hβh]
    simp [MulAut.mul_apply]
  have hfix : fixedSubgroup (fieldAut n F σ) = (subfieldSpProj n (descentField σ)).range :=
    Subgroup.ext fun x => fieldAut_apply_eq_self_iff (by omega)
      (by rw [hσord]; exact hp.odd_of_ne_two hp2) x
  have hinj := subfieldSpProj_injective (K := F) (r := n) (by omega) (descentField σ)
  have : Finite (descentField σ) := Subtype.finite
  have hcard2 : Nat.card (fixedSubgroup (fieldAut n F σ)) =
      Nat.card (StatedProj (StatedSp n (descentField σ))) := by
    rw [hfix]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hk : Nat.card (descentField σ) = ℓ ^ (f / p) := hcardk
  refine ⟨f / p, (Nat.mul_div_cancel' hpf).symm, ?_⟩
  rw [hcard1, hcard2]
  have h5 := Subgroup.card_quotient_dvd_card
    ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin n ⊕ Fin n) (descentField σ)).subgroupOf
      (StatedSp n (descentField σ)))
  refine h5.trans ?_
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hk]
  simp [lieOrderNumerator]

end CFSG.HardMathSupport.Lang.UnitaryAutomorphisms

module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrOddTimesTwoTransport
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalComponent
import CFSG.LocalAnalysis.ComponentClassification.StandardSubgroupAPI

public section

namespace CFSG.ComponentClassification.RestrictedStd

open CFSG Subgroup

variable {H : Type*} [Group H]

theorem mem_conjugate_iff {X : Subgroup H} {g x : H} :
    x ∈ conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    refine ⟨g * x * g⁻¹, h, ?_⟩
    simp [mul_assoc]

theorem conjugate_conjugate_inv (X : Subgroup H) (g : H) :
    conjugate (conjugate X g⁻¹) g = X := by
  ext x
  rw [mem_conjugate_iff, mem_conjugate_iff]
  simp [mul_assoc]

theorem le_conjugate_inv_of_conjugate_le {X Y : Subgroup H} {g : H} (h : conjugate X g ≤ Y) :
    X ≤ conjugate Y g⁻¹ := by
  intro x hx
  rw [mem_conjugate_iff]
  apply h
  rw [mem_conjugate_iff]
  simpa [mul_assoc] using hx

theorem normal_of_forall_conjugate_eq {J : Subgroup H} (h : ∀ g : H, conjugate J g = J) :
    J.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← h g⁻¹, mem_conjugate_iff]
  simpa [mul_assoc] using hn

variable {J : Subgroup H}

theorem centralizer_le_normalizer (hJ : IsStandardSubgroup J) {t : H}
    (ht : t ∈ centralizer (J : Set H)) (ht2 : orderOf t = 2) :
    centralizer ({t} : Set H) ≤ normalizer (J : Set H) := fun _ hg =>
  hJ.standardComponentIsStandard.mem_normalizer_of_commute ht ht2
    (mem_centralizer_singleton_iff.mp hg)

theorem isComponentOf_of_normal {J X : Subgroup H} (hJ : IsQuasisimple J) (hJX : J ≤ X)
    (hn : X ≤ normalizer (J : Set H)) : Assembly.IsComponentOf J X := by
  refine ⟨hJX, ?_, (AssemblyBPredicates.isQuasisimple_iff_native J).2 hJ⟩
  refine Assembly.IsSubnormal.step hJX ?_ (Assembly.IsSubnormal.refl X)
  refine (normal_subgroupOf_iff hJX).mpr fun j x hj hx => ?_
  exact (mem_normalizer_iff.mp (hn hx) j).mp hj

theorem isComponentOf_centralizer (hJ : IsStandardSubgroup J) {t : H}
    (ht : t ∈ centralizer (J : Set H)) (ht2 : orderOf t = 2) :
    Assembly.IsComponentOf J (centralizer ({t} : Set H)) := by
  have hJt : J ≤ centralizer ({t} : Set H) := by
    intro j hj
    rw [mem_centralizer_singleton_iff]
    exact (mem_centralizer_iff.mp ht) j hj
  exact isComponentOf_of_normal hJ.1 hJt (centralizer_le_normalizer hJ ht ht2)

variable [Finite H]

theorem not_isComponent (hJ : IsStandardSubgroup J) (hn : ¬ J.Normal) : ¬ IsComponent J := by
  intro hc
  refine hn (normal_of_forall_conjugate_eq fun g => ?_)
  have hcg : IsComponent (conjugate J g) :=
    LocalAnalysis.ComponentInitial.isComponent_conjSub hc g⁻¹
  rcases LocalCores.distinct_components_commute hcg hc with h | h
  · exact h
  · exact absurd (by rw [commutator_comm]; exact h) (hJ.2.2.2.2 g)

theorem even_card_of_isComponent (hO : pPrimeCore 2 H = ⊥) {K : Subgroup H} (hK : IsComponent K) :
    Even (Nat.card K) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hle := UnbalancedCorr.le_pPrimeCore_of_isSubnormal hK.2 (Nat.coprime_two_left.mpr hodd)
  rw [hO, le_bot_iff] at hle
  have : Nontrivial K := LocalCores.isQuasisimple_nontrivial hK.1
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this hle

theorem exists_conjugate_commutator_ne_bot (hO : pPrimeCore 2 H = ⊥)
    (hJ : IsStandardSubgroup J) (hn : ¬ J.Normal) {K : Subgroup H} (hK : IsComponent K) :
    ∃ g : H, ⁅J, conjugate K g⁆ ≠ ⊥ := by
  by_contra hall
  simp only [not_exists, not_not] at hall
  have hle : ∀ g : H, conjugate K g ≤ centralizer (J : Set H) := fun g => by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact hall g
  have hKeven := even_card_of_isComponent hO hK
  apply hn
  rw [← normalizer_eq_top_iff, ← hJ.2.2.2.1, eq_top_iff]
  intro g _
  by_contra hg
  have hodd := hJ.2.2.1 g hg
  have hK1 : K ≤ centralizer (J : Set H) := by
    have := hle 1
    rwa [show conjugate K 1 = K from by
      ext x; rw [mem_conjugate_iff]; simp] at this
  have hK2 : K ≤ conjugate (centralizer (J : Set H)) g := by
    have := le_conjugate_inv_of_conjugate_le (hle g⁻¹)
    rwa [inv_inv] at this
  have hdvd := Subgroup.card_dvd_of_le (le_inf hK1 hK2)
  exact (Nat.not_even_iff_odd.mpr hodd) (hKeven.two_dvd.trans hdvd |> even_iff_two_dvd.mpr)

end CFSG.ComponentClassification.RestrictedStd

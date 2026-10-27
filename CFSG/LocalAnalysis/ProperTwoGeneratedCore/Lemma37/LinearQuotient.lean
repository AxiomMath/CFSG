module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.LinearField
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open CFSG.ComponentClassification.OuterAutomorphisms

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {H : Subgroup G} {z : G}
  (hset : CoreSetting G S H) (hz : IsCentralInvolution (S : Subgroup G) z)
  (hesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ H) {J : Subgroup (EscapingQuotient z)}
  (hJ : CFSG.IsComponent J) (hzJ : escapingBar z ∉ J)
include hset hz hesc hJ hzJ

theorem caseOne_linear_eq_two {n : ℕ} (hn : 2 ≤ n) (e : J ≃* CFSG.Theory.Comparator.PSL2Model n) :
    n = 2 := by
  obtain ⟨D, hlin⟩ := exists_linearSylowData hset hz hesc hJ hzJ hn e
  have h := caseOne_field_eq_four hset hz hesc hJ hzJ hlin hn rfl
  exact Nat.pow_right_injective le_rfl (h.trans (by norm_num : (4 : ℕ) = 2 ^ 2))

theorem caseOne_component_alternatingGroup {n : ℕ} (hn : 2 ≤ n)
    (e : J ≃* CFSG.Theory.Comparator.PSL2Model n) : Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  have h2 := caseOne_linear_eq_two hset hz hesc hJ hzJ hn e
  subst h2
  obtain ⟨e₅⟩ := BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
  exact ⟨e.trans e₅⟩

theorem caseOne_component_sup_zpowers_eq_top {n : ℕ} (hn : 2 ≤ n)
    (e : J ≃* CFSG.Theory.Comparator.PSL2Model n) : J ⊔ Subgroup.zpowers (escapingBar z) = ⊤ := by
  have hq := caseOne_quotientData hset hz hesc
  have := caseOne_component_normal hset hz hesc hJ hzJ
  obtain ⟨D, hlin⟩ := exists_linearSylowData hset hz hesc hJ hzJ hn e
  obtain ⟨eA⟩ := caseOne_component_alternatingGroup hset hz hesc hJ hzJ hn e
  have hout := BenderFacts.card_outer_eq_two_of_mulEquiv_alternatingGroup_five eA
  set θ : EscapingQuotient z →* Outer J := (QuotientGroup.mk' (inner J)).comp MulAut.conjNormal
  have hker : ∀ m : EscapingQuotient z, ∀ j ∈ J, (∀ y ∈ J, m * y * m⁻¹ = j * y * j⁻¹) →
      m ∈ θ.ker := by
    intro m j hj h
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨⟨j, hj⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩
    exact (h y y.2).symm
  have hSker : (sylowBar hz).range ≤ θ.ker := by
    intro s hs
    rcases caseOne_sylowBar_mem_or hset hz hesc hJ hzJ hlin hs with h | h
    · exact hker s s h fun y _ => rfl
    · refine hker s _ h fun y _ => ?_
      rw [mul_inv_rev, show escapingBar z * s * y * (s⁻¹ * (escapingBar z)⁻¹) =
        escapingBar z * (s * y * s⁻¹) * (escapingBar z)⁻¹ by group,
        ← (hq.commute_bar (s * y * s⁻¹)).eq, mul_inv_cancel_right]
  have hindex : θ.ker.index = 1 := by
    have hdvd : θ.ker.index ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card θ.range
      rw [hout] at h
      rw [Subgroup.index_ker]
      exact h
    have hodd : Odd θ.ker.index := by
      have h1 := Subgroup.index_dvd_of_le hSker
      rw [← coe_sylowBarSylow] at h1
      exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        (Sylow.not_dvd_index (sylowBarSylow hz)))) h1
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  have htop := Subgroup.index_eq_one.mp hindex
  rw [eq_top_iff]
  intro m _
  have hm : m ∈ θ.ker := htop ▸ Subgroup.mem_top m
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hm
  obtain ⟨j, hj⟩ := hm
  have hjm : (j : EscapingQuotient z)⁻¹ * m ∈
      Subgroup.centralizer (J : Set (EscapingQuotient z)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    have h := congrArg (fun φ : MulAut J => ((φ ⟨y, hy⟩ : J) : EscapingQuotient z)) hj
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h
    calc y * ((j : EscapingQuotient z)⁻¹ * m) = (j : EscapingQuotient z)⁻¹ *
          ((j : EscapingQuotient z) * y * (j : EscapingQuotient z)⁻¹) * m := by group
      _ = (j : EscapingQuotient z)⁻¹ * (m * y * m⁻¹) * m := by rw [h]
      _ = (j : EscapingQuotient z)⁻¹ * m * y := by group
  rw [caseOne_component_centralizer_eq hset hz hesc hJ hzJ hlin] at hjm
  have hmj : m = (j : EscapingQuotient z) * ((j : EscapingQuotient z)⁻¹ * m) := by group
  rw [hmj]
  exact Subgroup.mul_mem_sup j.2 hjm

end CFSG.ProperTwoGeneratedCore.Lemma37

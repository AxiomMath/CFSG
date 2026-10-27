module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AInnerLay
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514Cover

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs

theorem l514vinn_nonempty_barEquiv_of_surjective {A B : Type*} [Group A] [Group B]
    (hA : CFSG.Open.IsQuasisimple A) (hB : CFSG.Open.IsQuasisimple B) {ψ : A →* B}
    (hψ : Function.Surjective ψ) :
    Nonempty ((A ⧸ Subgroup.center A) ≃* (B ⧸ Subgroup.center B)) := by
  have hc : Subgroup.center A ≤ (Subgroup.center B).comap ψ := fun a ha => by
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro b
    obtain ⟨a', rfl⟩ := hψ b
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha a']
  set ψ' := QuotientGroup.map (Subgroup.center A) (Subgroup.center B) ψ hc with hψ'
  have hsurj : Function.Surjective ψ' := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨a, rfl⟩ := hψ b
    exact ⟨a, rfl⟩
  have := hA.2
  have := hB.2.toNontrivial
  have hker : ψ'.ker = ⊥ := by
    rcases (ψ'.normal_ker).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨y, hy⟩ := exists_ne (1 : B ⧸ Subgroup.center B)
      obtain ⟨x, rfl⟩ := hsurj y
      apply hy
      exact (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))
  exact ⟨MulEquiv.ofBijective ψ' ⟨(MonoidHom.ker_eq_bot_iff ψ').1 hker, hsurj⟩⟩

theorem l514vinn_isTypeL2_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) {r : ℕ}
    (h : IsTypeL2 r A) : IsTypeL2 r B :=
  p6_isTypeL2_of_equiv e h

theorem l514vinn_exists_slPiTwo_proj {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) :
    ∃ (F₂ : Type) (_ : Field F₂) (_ : Finite F₂), Nat.card F₂ = p ^ f ∧
      Nonempty ((↥(slPi π 2 (p ^ f) K) ⧸ Subgroup.center ↥(slPi π 2 (p ^ f) K)) ≃*
        StatedProj (StatedSL 2 F₂)) := by
  have := hK.finite
  cases π
  · have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [hK.card, piCard, Bool.cond_false]
    have := hK.charP
    have : Fact p.Prime := ⟨hK.prime⟩
    obtain ⟨e⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := K) (r := p) (f := f) hcard
    refine ⟨↥(CFSG.LieType.Steinberg.fixedSubfield K p f), inferInstance, inferInstance,
      CFSG.LieType.Steinberg.card_fixedSubfield (F := K) (p := p) (f := f) hcard, ⟨?_⟩⟩
    exact (barEquiv e).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _)
  · refine ⟨K, inferInstance, inferInstance, by rw [hK.card, piCard, Bool.cond_true], ⟨?_⟩⟩
    exact (barEquiv (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K)

theorem l514vinn_isTypeL2_of_range_slPiTwo {π : Bool} {p f : ℕ} {K : Type} [Field K]
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (hq2 : 2 < p ^ f) {Y : Type} [Group Y]
    (Φ : ↥(slPi π 2 (p ^ f) K) →* Y) {J : Subgroup Y} (hΦ : Φ.range = J)
    (hJ : CFSG.Open.IsQuasisimple (↥J ⧸ GLAPPrimeCore 3 ↥J)) :
    IsTypeL2 (p ^ f) (↥J ⧸ GLAPPrimeCore 3 ↥J) := by
  obtain ⟨F₂, _, _, hc, ⟨e⟩⟩ := l514vinn_exists_slPiTwo_proj hK
  have hQ : CFSG.Open.IsQuasisimple ↥(slPi π 2 (p ^ f) K) :=
    isQuasisimple_open (isQuasisimple_slPi_two hK hq hq2)
  let ψ : ↥(slPi π 2 (p ^ f) K) →* (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J)).comp
      ((MulEquiv.subgroupCongr hΦ).toMonoidHom.comp Φ.rangeRestrict)
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective _).comp
      ((MulEquiv.subgroupCongr hΦ).surjective.comp Φ.rangeRestrict_surjective)
  obtain ⟨e'⟩ := l514vinn_nonempty_barEquiv_of_surjective hQ hJ hψ
  exact ⟨F₂, inferInstance, inferInstance, hc, ⟨e'.symm.trans e⟩⟩

end CFSG.HardMathSupport.Solomon.Coordinator

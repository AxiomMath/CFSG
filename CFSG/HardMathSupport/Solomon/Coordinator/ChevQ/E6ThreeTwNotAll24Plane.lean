module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24Grp
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeDiagParTw
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwCoreDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CatTw
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.Exc
  (not_isD2SeitzException_of_chevalleyExc isChevalleyExcIndex_twistedE6)
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp (catEquiv_twistedE6_of_field)

namespace KSNotAll24

theorem exists_plane_through {H : Type*} [Group H] {E I : Subgroup H}
    (hE : CFSG.Open.IsElemAbelian 3 E) (hEI : ¬ E ≤ I) {c : H} (hcE : c ∈ E) (hcI : c ∈ I)
    (hc1 : c ≠ 1) :
    ∃ F : Subgroup H, F ≤ E ∧ Nat.card F = 3 ^ 2 ∧ c ∈ F ∧ ¬ F ≤ I := by
  obtain ⟨d, hdE, hdI⟩ := SetLike.not_le_iff_exists.1 hEI
  have hdc : d ∉ Subgroup.zpowers c := fun h => hdI ((Subgroup.zpowers_le.2 hcI) h)
  have hcomm : Commute c d := congrArg Subtype.val (hE.1.is_comm.comm ⟨c, hcE⟩ ⟨d, hdE⟩)
  refine ⟨Subgroup.zpowers c ⊔ Subgroup.zpowers d,
    sup_le (Subgroup.zpowers_le.2 hcE) (Subgroup.zpowers_le.2 hdE),
    card_zpowers_sup_zpowers hcomm hc1 (hE.2 c hcE) (hE.2 d hdE) hdc,
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c), fun h =>
      hdI (Subgroup.zpowers_le.1 ((le_sup_right (a := Subgroup.zpowers c)).trans h))⟩

theorem mem_zpowers_of_mem_inf {H : Type*} [Group H] {F I : Subgroup H} (hF : Nat.card F = 3 ^ 2)
    (hFI : ¬ F ≤ I) {c : H} (hcF : c ∈ F) (hcI : c ∈ I) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    {f : H} (hfF : f ∈ F) (hfI : f ∈ I) : f ∈ Subgroup.zpowers c := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  haveI : Finite ↥(F ⊓ I) :=
    Finite.of_injective (Subgroup.inclusion (inf_le_left : F ⊓ I ≤ F))
      (Subgroup.inclusion_injective _)
  have hz : Subgroup.zpowers c ≤ F ⊓ I :=
    le_inf (Subgroup.zpowers_le.2 hcF) (Subgroup.zpowers_le.2 hcI)
  have hzc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hdvd : Nat.card ↥(F ⊓ I) ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : F ⊓ I ≤ F)
    rwa [hF] at this
  have hge : 3 ≤ Nat.card ↥(F ⊓ I) := by
    have := Subgroup.card_le_of_le hz
    rwa [hzc] at this
  have hne : Nat.card ↥(F ⊓ I) ≠ 3 ^ 2 := by
    intro h
    apply hFI
    have heq : F ⊓ I = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hF])
    rw [← heq]
    exact inf_le_right
  obtain ⟨i, hi, hiq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hcard : Nat.card ↥(F ⊓ I) = 3 := by
    interval_cases i
    · omega
    · simpa using hiq
    · exact absurd hiq hne
  have heq : Subgroup.zpowers c = F ⊓ I :=
    Subgroup.eq_of_le_of_card_ge hz (by rw [hcard, hzc])
  rw [heq]
  exact ⟨hfF, hfI⟩

end KSNotAll24

section Plane


@[expose] def TwE6NotAll24Plane : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), ringChar K ≠ 3 → (∀ c, σ c = c ^ q) →
    Nat.card K = q ^ 2 → 3 ∣ q + 1 → q ≠ 2 →
    ∀ E : Subgroup (MulAut (twistedE6RootGroup K σ)), IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      E ≤ twistedE6Inn K σ ⊔ twistedE6Diag K σ → ¬ E ≤ twistedE6Inn K σ →
      ¬ TwE6NormalizesR K σ E → ¬ TwE6InnerAll24 K σ E →
      ∃ F : Subgroup (MulAut (twistedE6RootGroup K σ)), F ≤ E ∧ Nat.card F = 3 ^ 2 ∧
        ∀ f ∈ F, f ≠ 1 → ∀ x : twistedE6RootGroup K σ, f x = x → x ∈ seitzHyperGamma 3 E

theorem twE6NotAll24Gen_of_plane
    (hS : AGLEmbeddingD2.KFactSeitzRankTwo)
    (hP : TwE6NotAll24Plane) : TwE6NotAll24Gen := by
  intro K _ _ σ q hK3 hσ hKq h3 hq2 E hE hEc hED hEi hER hnot
  classical
  obtain ⟨F, hFE, hFc, hFfix⟩ := hP K σ q hK3 hσ hKq h3 hq2 E hE hEc hED hEi hER hnot
  obtain ⟨hp, f, hf, hqf⟩ := prime_ringChar_and_eq_pow_of_card_sq K q hKq (by omega)
  let qp : TauCeti.PrimePower := ⟨ringChar K, f, hp, by omega⟩
  have hqp : qp.card = q := by
    rw [TauCeti.PrimePower.card_def]
    exact hqf.symm
  have hv : (TauCeti.LieTypeIndex.twistedE6 qp).Valid := TauCeti.LieTypeIndex.valid_twistedE6 qp
  obtain ⟨e⟩ := catEquiv_twistedE6_of_field qp hv K (hqp ▸ hKq) σ (hqp ▸ hσ)
  have hgen := planeGen_of_kfact hS Nat.prime_three (by norm_num) ⟨_, hv⟩ e.symm
    (by
      show 3 ≠ (TauCeti.LieTypeIndex.twistedE6 qp).characteristic
      rw [TauCeti.LieTypeIndex.characteristic_twistedE6]
      exact fun h => hK3 h.symm)
    (not_isD2SeitzException_of_chevalleyExc (isChevalleyExcIndex_twistedE6 qp))
    (hE.mono hFE) hFc
  have hH : seitzHyperGamma 3 E = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro x ⟨φ, hφF, hφ1, hφx⟩
    exact hFfix φ hφF hφ1 x hφx
  exact hH

end Plane

section Inner


theorem exists_plane_through_inner_outer {K : Type} [Field K] {σ : K ≃+* K}
    (E : Subgroup (MulAut (twistedE6RootGroup K σ))) (hE : IsElemAbelian 3 E)
    (hEi : ¬ E ≤ twistedE6Inn K σ) (s : twistedE6RootGroup K σ) (hs : MulAut.conj s ∈ E)
    (hs1 : (MulAut.conj s : MulAut (twistedE6RootGroup K σ)) ≠ 1) :
    ∃ F : Subgroup (MulAut (twistedE6RootGroup K σ)), F ≤ E ∧ Nat.card F = 3 ^ 2 ∧
      MulAut.conj s ∈ F ∧ ¬ F ≤ twistedE6Inn K σ :=
  KSNotAll24.exists_plane_through hE hEi hs ⟨s, rfl⟩ hs1

end Inner

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

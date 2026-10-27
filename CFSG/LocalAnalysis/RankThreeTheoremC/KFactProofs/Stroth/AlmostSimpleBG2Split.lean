module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBG2Comp
public import CFSG.RankThree.Chevalley.SteinbergCEG2EvenSplitPrime
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.EvenG2
open scoped commutatorElement Pointwise

section


theorem odd_card_torusGroup_G2 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Odd (Nat.card (torusGroup .G2 K)) := by
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  exact odd_card_of_injective_pi_units e.symm.toMonoidHom e.symm.injective

theorem oddPCoreInClosure_of_toral_cases (K : Type) [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) (h4 : 4 ≤ Nat.card K)
    {x g : adjointGroup .G2 K} {a : Fin Tag.G2.rank → Kˣ}
    (ha : ((g * x * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) = rootDiagUnit .G2 a)
    (hcases : (rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K) ∨
      (∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
        toralCentralizer .G2 K a =
          torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
        (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
          (torusGroup .G2 K : Set (ModGL .G2 K)) *
            ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
              Set (ModGL .G2 K)) ∧
        ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
          rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
        toralCentralizer .G2 K a ⊓ Subgroup.centralizer
            ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
              Set (ModGL .G2 K)) =
          (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ∧
        (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
          torusGroup .G2 K)) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) := by
  classical
  have hmap := map_centralizer_eq_toralCentralizer ha
  rcases hcases with ⟨-, hMH⟩ | ⟨α, hα, -, -, -, hcomm, hZ, hZH⟩
  · obtain ⟨φ, hφ⟩ := exists_injective_of_toralCentralizer_eq_torusGroup ha hMH
    exact OddPCoreInClosure.of_odd_card (odd_card_of_injective_pi_units φ hφ)
  ·
    set D := toralCentralizer .G2 K a with hD
    set Q : Subgroup (ModGL .G2 K) :=
      rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) with hQ
    let F₀ : adjointGroup .G2 K →* ModGL .G2 K :=
      (adjointGroup .G2 K).subtype.comp (MulAut.conj g).toMonoidHom
    let F : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) →* ModGL .G2 K :=
      F₀.comp (Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))).subtype
    have hF : Function.Injective F :=
      (Subtype.val_injective.comp (MulAut.conj g).injective).comp
        (Subgroup.subtype_injective _)
    have hFrange : F.range = D := by
      rw [← hmap, MonoidHom.range_comp, Subgroup.range_subtype]
    have hQD : Q ≤ D := by
      rw [← hcomm, Subgroup.commutator_le]
      intro u hu v hv
      exact D.mul_mem (D.mul_mem (D.mul_mem hu hv) (D.inv_mem hu)) (D.inv_mem hv)
    have hQn : ∀ c : ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))), ∀ q ∈ Q,
        F c * q * (F c)⁻¹ ∈ Q := by
      intro c q hq
      have hFc : F c ∈ D := hFrange ▸ ⟨c, rfl⟩
      have h1 : ⁅F c, q⁆ ∈ Q := by
        rw [← hcomm]
        exact Subgroup.commutator_mem_commutator hFc (hQD hq)
      have h2 : F c * q * (F c)⁻¹ = ⁅F c, q⁆ * q := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Q.mul_mem h1 hq
    obtain ⟨hQs, hQnab, hQcard⟩ := even_pinned_component_data .G2 K h4 hα
    have hpQ : p ∣ Nat.card Q := by
      rw [hQ, hQcard]
      refine Dvd.dvd.mul_left ?_ _
      have h1 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        have : 1 ≤ Nat.card K := Nat.card_pos
        zify [this, Nat.one_le_pow 2 _ this]
        ring
      rw [h1]
      exact Dvd.dvd.mul_right hpq _
    refine oddPCoreInClosure_of_map_component hp F hF Q (hFrange ▸ hQD) hQn hQs hQnab hpQ
      (torusGroup .G2 K) ?_ (odd_card_torusGroup_G2 K)
    intro c hc
    have hFc : F c ∈ D := hFrange ▸ ⟨c, rfl⟩
    have hcent : F c ∈ D ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) :=
      ⟨hFc, Subgroup.mem_centralizer_iff.2 fun q hq => (hc q hq).symm⟩
    rw [hZ] at hcent
    exact hZH hcent

theorem oddPCoreInClosure_centralizer_split_large (K : Type) [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    {x : adjointGroup .G2 K} (hx : orderOf x = p) :
    OddPCoreInClosure p ↥(Subgroup.centralizer ({x} : Set (adjointGroup .G2 K))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hq6 := six_le_card_of_dvd hp hp3 hpq
  have hPx : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨g, hg⟩ :=
    exists_conj_map_le_of_not_dvd_index (not_dvd_index_torusGroup_G2 hp hp3 hpq) hPx
  have hgx : g * x * g⁻¹ ∈ (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) :=
    hg ⟨x, Subgroup.mem_zpowers x, rfl⟩
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hgx
  have hao : orderOf (rootDiagUnit .G2 a) = p := by
    rw [← ha, orderOf_injective _ (adjointGroup .G2 K).subtype_injective,
      show g * x * g⁻¹ = (MulAut.conj g).toMonoidHom x from rfl,
      orderOf_injective _ (MulAut.conj g).injective x, hx]
  exact oddPCoreInClosure_of_toral_cases K hp hpq (by omega) ha
    (toral_centralizer_cases_G2_of_charTwo K hp hp3 hpq a hao)

end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

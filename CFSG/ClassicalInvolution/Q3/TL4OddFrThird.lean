module

public import CFSG.ClassicalInvolution.Q3.TL4OddFrMem
public import CFSG.ClassicalInvolution.Asc77.AscT8T1

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.Q3.Q3CH
open CFSG.ClassicalInvolution.Asc77.T8T (TriFrame)

@[expose] def D4OddAutInnerNC3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X → Subgroup.center X = ⊥ →
    ∀ f : (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →* X, Function.Surjective f →
      f.ker ≤ Subgroup.center (modelUniv .POmegaPlus 4 3 1 Nat.prime_three).K →
        ∀ s : X, orderOf s = 2 → (¬ ∃ K : Subgroup X, IsClassicalMember3 K s) →
          ∀ α : MulAut X, Odd (orderOf α) →
            (∀ c ∈ Subgroup.centralizer ({s} : Set X),
              c⁻¹ * α c ∈ oddCoreIn (Subgroup.centralizer ({s} : Set X))) →
              ∃ g : X, α = MulAut.conj g

section Rows

theorem autOddFreeInnerTag_D4_of_nc (h : D4OddAutInnerNC3) :
    Q3NM.AutOddFreeInnerTag .POmegaPlus 4 :=
  Q3NM.autOddFreeInnerTag_of_oddAut fun _ _ _ S _ _ hSq hZ f hf hker s hs α hα hcent => by
    have hfix : ∀ c ∈ Subgroup.centralizer ({s} : Set S),
        c⁻¹ * α c ∈ oddCoreIn (Subgroup.centralizer ({s} : Set S)) := fun c hc => by
      rw [hcent c hc, inv_mul_cancel]
      exact one_mem _
    by_cases hcl : ∃ K : Subgroup S, IsClassicalMember3 K s
    · obtain ⟨K, hK⟩ := hcl
      obtain ⟨g, hg⟩ := Q3T.d4OddAutInner3_proved S hSq hZ f hf hker s K hK α hα hfix
      exact ⟨g, hg.symm⟩
    · obtain ⟨g, hg⟩ := h S hSq hZ f hf hker s hs hcl α hα hfix
      exact ⟨g, hg.symm⟩

theorem autOddFreeInner_range_of_nc (hD4 : D4OddAutInnerNC3) {X : Type} [Group X] [Finite X]
    {c : CompData}
    (hc : (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n : ℕ), IsFundTag t ∧
      CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n 3 1 ∧ c = CompData.model t n) ∨
      c = CompData.m11)
    (ψ : c.G →* X) (hker : ψ.ker ≤ Subgroup.center c.G) (hψ1 : ∃ x, ψ x ≠ 1) :
    Q3NM.AutOddFreeInner ↥ψ.range := by
  rcases hc with ⟨t, n, ht, hadm, rfl⟩ | rfl
  · have hker' : ψ.rangeRestrict.ker ≤ Subgroup.center _ := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hker
    by_cases hD4' : t = .POmegaPlus ∧ n = 4
    · obtain ⟨rfl, rfl⟩ := hD4'
      exact autOddFreeInnerTag_D4_of_nc hD4 Nat.prime_three ht hadm _ ψ.rangeRestrict
        ψ.rangeRestrict_surjective hker'
    · by_cases hT : t = .trialityD4
      · subst hT
        have hn : n = 0 := hadm.2.2
        subst hn
        exact Q3NM.autOddFreeInnerTag_trialityD4 Nat.prime_three ht hadm _ ψ.rangeRestrict
          ψ.rangeRestrict_surjective hker'
      · exact Q3NM.autOddFreeInnerTag_of_not_D4 hD4' hT Nat.prime_three ht hadm _
          ψ.rangeRestrict ψ.rangeRestrict_surjective hker'
  · obtain ⟨-, ⟨e⟩⟩ := range_m11 m11Facts rfl ψ hψ1
    exact Q3CH.autOddFreeInner_of_mulEquiv e.symm (autOddFreeInner_m11 m11OddAutInner3)

end Rows

section Vertex

variable {G : Type} [Group G] [Finite G]

theorem mem_inner_of_classicalOrQuiet (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {c a : G} (hc1 : c ≠ 1)
    {haC : a ∈ Subgroup.centralizer ({c} : Set G)} (h : ClassicalOrQuiet c a haC)
    (hD4 : D4OddAutInnerNC3) {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L)
    (hm : ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩) :
    oddQuotMk c ⟨a, haC⟩ ∈ L ∧ Q3NM.AutOddFreeInner ↥L := by
  rcases h with ⟨K, hK⟩ | hq
  · have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hc1 (by
      have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
      rwa [hZ, Subgroup.mem_bot] at h1)
    have hΦ := secData3_sFamily3 hK hK hK
    obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
    obtain ⟨j, hj⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c K K K)
    have haj : oddQuotMk c ⟨a, haC⟩ ∈ secComp hΦ D j := hj (oddQuotMk_mem_modOdd hK.mem haC)
    have hLj := eq_secComp_of_not_commute hΦ D haj hL hm
    have hk := kind_of_isComponent_secComp hΦ D (hLj ▸ hL)
    subst hLj
    exact ⟨haj, autOddFreeInner_range_of_nc hD4 hk _
      (Q3CH.ker_comp_le_center D _ (sectionQuotientHom_injective _) j)
      (Q3CH.exists_comp_ne_one D _ (sectionQuotientHom_injective _) j)⟩
  · exfalso
    obtain ⟨y, hy, hne⟩ := hm
    exact hne (hq L hL y hy)

theorem autOddFreeOn_mul_of_classicalOrQuiet (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {c a b : G} (hc1 : c ≠ 1)
    {haC : a ∈ Subgroup.centralizer ({c} : Set G)} {hbC : b ∈ Subgroup.centralizer ({c} : Set G)}
    (ha : ClassicalOrQuiet c a haC) (hb : ClassicalOrQuiet c b hbC)
    (habC : a * b ∈ Subgroup.centralizer ({c} : Set G)) (hD4 : D4OddAutInnerNC3)
    (L : Subgroup (OddQuot c)) (hL : CFSG.IsComponent L)
    (hma : ∃ y ∈ L, oddQuotMk c ⟨a, haC⟩ * y ≠ y * oddQuotMk c ⟨a, haC⟩)
    (hmb : ∃ y ∈ L, oddQuotMk c ⟨b, hbC⟩ * y ≠ y * oddQuotMk c ⟨b, hbC⟩) :
    Q3NM.AutOddFreeOn ↥L (IsInducedAut L (oddQuotMk c ⟨a * b, habC⟩)) := by
  obtain ⟨haL, hrow⟩ := mem_inner_of_classicalOrQuiet hBelow hZ hc1 ha hD4 hL hma
  obtain ⟨hbL, -⟩ := mem_inner_of_classicalOrQuiet hBelow hZ hc1 hb hD4 hL hmb
  have habL : oddQuotMk c ⟨a * b, habC⟩ ∈ L := by
    have e : oddQuotMk c ⟨a * b, habC⟩ = oddQuotMk c ⟨a, haC⟩ * oddQuotMk c ⟨b, hbC⟩ := by
      rw [← map_mul]
      rfl
    rw [e]
    exact L.mul_mem haL hbL
  intro 𝒳 hinn f hf hf2
  refine hrow 𝒳 hinn f ⟨⟨_, habL⟩, MulEquiv.ext fun y => Subtype.ext ?_⟩ hf2
  exact (hf y).symm

theorem hyp51At_of_classicalOrQuiet_pair (hBelow : CIT3Below (Nat.card G))
    (hZ : Subgroup.center G = ⊥) {B : Subgroup G} (hB : IsElemAbelian 2 B) {a b c : G}
    (hgen : B = Subgroup.closure {a, b, c}) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (hb1 : b ≠ 1) (hbc : b ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (ha : ClassicalOrQuiet c a haC) (hb : ClassicalOrQuiet c b hbC) (hD4 : D4OddAutInnerNC3) :
    Hyp51At B c := by
  have haB : a ∈ B := hgen ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  have hbB : b ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcB : c ∈ B :=
    hgen ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have habC : a * b ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.mul_mem _ haC hbC
  refine hyp51At_of_classical_pair hBelow hZ hB hgen hc1 ha1 hac haC hbC habC ha hb ?_
  intro L hL hm _ _
  exact autOddFreeOn_mul_of_classicalOrQuiet hBelow hZ hc1 ha hb habC hD4 L hL
    (hm _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC))
    (hm _ (oddQuotMk_mem_modOdd hbB hbC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC))

end Vertex

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient
import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

@[expose] def ParabolicCover (T T₁ T₂ : Subgroup X) (L : Subgroup (X ⧸ gnC T)) : Prop :=
  ∀ P : Subgroup (X ⧸ gnC T), IsMinOverBorel L (gnImg T T ⊓ L) P →
    pElementSubgroup 2 P ≤ gnImg T (Subgroup.centralizer (T₁ : Set X)) ∨
      pElementSubgroup 2 P ≤ gnImg T (Subgroup.normalizer (T₂ : Set X))

omit [Finite X] in
theorem exists_parabolic_le_gnA {T₁ T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)}
    (hY : GNYComponent T T₁ T₂ L) (hcov : ParabolicCover T T₁ T₂ L)
    {Ps : Set (Subgroup (X ⧸ gnC T))} (hPs : ∀ P ∈ Ps, IsMinOverBorel L (gnImg T T ⊓ L) P)
    (hgen : L = ⨆ P ∈ Ps, pElementSubgroup 2 P) :
    (∃ P ∈ Ps, pElementSubgroup 2 P ≤ gnA T T₁ L) ∧
      (∃ P ∈ Ps, pElementSubgroup 2 P ≤ gnA T T₂ L) := by
  have hPL : ∀ P ∈ Ps, pElementSubgroup 2 P ≤ L :=
    fun P hP => (pElementSubgroup_le P).trans (hPs P hP).1
  have hCN : gnImg T (Subgroup.centralizer (T₁ : Set X)) ≤
      gnImg T (Subgroup.normalizer (T₁ : Set X)) :=
    Subgroup.map_mono (Subgroup.centralizer_le_normalizer _)
  refine ⟨?_, ?_⟩
  · by_contra h
    push Not at h
    apply hY.2.2
    rw [hgen]
    refine iSup₂_le fun P hP => ?_
    rcases hcov P (hPs P hP) with h1 | h2
    · exact absurd (le_inf (h1.trans hCN) (hPL P hP)) (h P hP)
    · exact h2
  · by_contra h
    push Not at h
    apply hY.2.1
    rw [hgen]
    refine iSup₂_le fun P hP => ?_
    rcases hcov P (hPs P hP) with h1 | h2
    · exact h1
    · exact absurd (le_inf h2 (hPL P hP)) (h P hP)

theorem mem_pElementSubgroup_of_orderOf {Y : Type*} [Group Y] {p : ℕ} {A : Subgroup Y} {x : Y}
    (hx : x ∈ A) (ho : orderOf x = p) : x ∈ pElementSubgroup p A :=
  Subgroup.subset_closure ⟨hx, 1, by rw [pow_one, ho]⟩

theorem gnThree_of_cover (hG : KFactChevGenThree) (hX : GNSetting X T)
    {T₁ T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ L)
    (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) (hcov : ParabolicCover T T₁ T₂ L) :
    ¬ pElementSubgroup 3 (gnA T T₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
      ¬ pElementSubgroup 3 (gnA T T₂ L) ≤ (Subgroup.center ↥L).map L.subtype := by
  have hS : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hY.1.2.1
  obtain ⟨Ps, hPs, hgen, hK⟩ := hG _ L (gnImg T T ⊓ L) hY.1.2.2 hcl hS
  obtain ⟨⟨P₁, hP₁, h₁⟩, ⟨P₂, hP₂, h₂⟩⟩ := exists_parabolic_le_gnA hY hcov hPs hgen
  have key : ∀ (A P : Subgroup (X ⧸ gnC T)), P ∈ Ps →
      pElementSubgroup 2 P ≤ A → ¬ pElementSubgroup 3 A ≤ (Subgroup.center ↥L).map L.subtype := by
    intro A P hP hPA hle
    obtain ⟨x, hx, ho, hxZ⟩ := hK P hP
    exact hxZ (hle (mem_pElementSubgroup_of_orderOf (hPA hx) ho))
  exact ⟨key _ P₁ hP₁ h₁, key _ P₂ hP₂ h₂⟩

theorem gnCentre_of_cover (hG : KFactChevGenCentre) (hX : GNSetting X T)
    {T₁ T₂ : Subgroup X} {L : Subgroup (X ⧸ gnC T)} (hY : GNYComponent T T₁ T₂ L)
    (hcl : IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L)) (hcov : ParabolicCover T T₁ T₂ L)
    (hZodd : ¬ 2 ∣ Nat.card (Subgroup.center ↥L))
    (hz : ∀ p : ℕ, p.Prime → p ∣ Nat.card (Subgroup.center ↥L) →
      ∃ z ∈ (Subgroup.center ↥L).map L.subtype, orderOf z = p ∧
        (z ∈ gnA T T₁ L ∨ z ∈ gnA T T₂ L)) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (Subgroup.center ↥L) →
      1 < Open.pRank p (gnA T T₁ L) ∨ 1 < Open.pRank p (gnA T T₂ L) := by
  intro p hp hpZ
  have hS : IsSylowTwoOf (gnImg T T ⊓ L) L :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf hX.sylow
      hY.1.2.1
  obtain ⟨Ps, hPs, hgen, hK⟩ := hG _ L (gnImg T T ⊓ L) hY.1.2.2 hcl hS
  obtain ⟨⟨P₁, hP₁, h₁⟩, ⟨P₂, hP₂, h₂⟩⟩ := exists_parabolic_le_gnA hY hcov hPs hgen
  obtain ⟨z, hzZ, hzo, hzA⟩ := hz p hp hpZ
  have key : ∀ (A P : Subgroup (X ⧸ gnC T)), P ∈ Ps →
      pElementSubgroup 2 P ≤ A → z ∈ A → 1 < Open.pRank p A := by
    intro A P hP hPA hzA'
    obtain ⟨y, hy, hyo, hyZ⟩ := hK P hP p hp (fun h => hZodd (h ▸ hpZ)) hpZ
    have hyL : y ∈ L := (pElementSubgroup_le P).trans (hPs P hP).1 hy
    have hcomm : Commute z y := by
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hzZ
      have := Subgroup.mem_center_iff.mp hz' ⟨y, hyL⟩
      exact (congrArg Subtype.val this).symm
    have hind : y ∉ Subgroup.zpowers z := by
      intro hyz
      apply hyZ
      have hle : Subgroup.zpowers z ≤ (Subgroup.center ↥L).map L.subtype :=
        (Subgroup.zpowers_le).mpr hzZ
      exact hle hyz
    have hzp : z ^ p = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
    have hyp : y ^ p = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hE := CFSG.LieType.SeitzGeneration.isElemAbelian_closure_pair (p := p) hcomm hzp hyp
    have hcard := CFSG.LieType.SeitzGeneration.card_closure_pair_sq hp hcomm hzo hyo hind
    have hEA : Subgroup.closure ({z, y} : Set (X ⧸ gnC T)) ≤ A := by
      rw [Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hzA'
      · exact hPA hy
    have := CFSG.SectionRank.le_pRank hp.one_lt hEA hE hcard
    omega
  rcases hzA with h | h
  · exact Or.inl (key _ P₁ hP₁ h₁ h)
  · exact Or.inr (key _ P₂ hP₂ h₂ h)

end CFSG.AGLEmbeddingD2.GN

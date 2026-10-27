module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFront
public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFrame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Balance.Bootstrap (LayerGenerationPairAt)
open scoped MatrixGroups

section Abstract

variable {S H : Type} [Group S] [Group H]

theorem thm5IH_innerHom_eq_one_of_central (ψ : S →* H) {y : S} (hy : ∀ s : S, y * s = s * y) :
    FrameVertex.innerHom ψ y = 1 := by
  rw [FrameVertex.innerHom_apply]
  refine Lemma52Proof.toInducedAutOn_eq_one_of_commute ψ.range
    (FrameVertex.mem_normalizer_range ψ y) ?_
  rintro _ ⟨s, rfl⟩
  rw [← map_mul, ← map_mul, hy s]

end Abstract

variable {p f : ℕ} [Fact p.Prime]

theorem t5BaseAt_nt_of_prod_layers {t : StatedLieTag} {k e : ℕ} (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4)
    (hLG : p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t k p e → LayerGenerationPairAt t k p e Fact.out)
    (hprod : p ≠ 2 → 5 ≤ p ^ e → StatedLieAdmissible t k p e → ∀ {Y : Type} [Group Y] [Finite Y]
      (π : (modelUniv t k p e Fact.out).K →* Y),
      π.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ y : (modelUniv t k p e Fact.out).K, y * y = 1 → (¬ ∀ s, y * s = s * y) →
          ∃ A B : Subgroup Y, CentralizerProd π.range (π y) A B) :
    T5BaseAt p f t k e Not := by
  intro hp2 hq hfund hadm hef H _ _ ψ hker R hR R' hR' eK eJ hne hcomm z hz hzJ A hA hAKJ hzA
    hfaith
  have hef' : e = f := hef.resolve_right fun h => hD4 h.1
  subst hef'
  obtain ⟨x, x', hd⟩ := thm5IH_nt_front hG2 hD4 hp2 hq hfund hadm rfl ψ hker hR hR' eK eJ hcomm hz
    hzJ hA hAKJ
  have hA4 : Nat.card A = 4 := by simpa using hA.1
  have hopen := ModelFacts.isQuasisimple_modelUniv t k p e Fact.out hfund hadm
  have hperfK : Group.IsPerfect (modelUniv t k p e Fact.out).K := ⟨hopen.1⟩
  obtain ⟨hcen, hnorm, hcentY⟩ := FrameVertex.innerHom_spec ψ hker
  set L : Subgroup H := ψ.range with hL
  set π := FrameVertex.innerHom ψ with hπ
  have hπk : π.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K := fun g hg =>
    hcen g (MonoidHom.mem_ker.mp hg)
  have hAL : A ≤ L :=
    hAKJ.trans (sup_le (Subgroup.map_le_range ψ R) (Subgroup.map_le_range ψ R'))
  have hLn : A ≤ Subgroup.normalizer (L : Set H) := fun a ha => Subgroup.le_normalizer (hAL ha)
  have hF : inducedImage L A = ((toInducedAutOn L).comp (Subgroup.inclusion hLn)).range :=
    thm5IH_inducedImage_eq_range hLn
  have hcardF : Nat.card (inducedImage L A) = 4 := thm5IH_card_inducedImage hLn hA4 hfaith
  set τ : ↥A →* ↥(inducedAutOn L) := (toInducedAutOn L).comp (Subgroup.inclusion hLn) with hτ
  have hFsq : ∀ g ∈ inducedImage L A, g * g = 1 := by
    intro g hg
    rw [hF] at hg
    obtain ⟨b, rfl⟩ := hg
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (hA.2 b b.2)
    rw [this, map_one]
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have hc := Lemma52Proof.commute_of_toInducedAutOn_eq_one L (hLn b.2) hb
    rw [Subgroup.mem_bot]
    by_contra hb1
    exact hfaith b b.2 (fun h => hb1 (Subtype.ext h)) fun y hy => hc y hy
  have hne1 : ∀ (a : H) (ha : a ∈ A), a ≠ 1 → τ ⟨a, ha⟩ ≠ 1 := fun a ha ha1 h =>
    ha1 (congrArg Subtype.val (hτinj (h.trans (map_one τ).symm)))
  have hπτ : ∀ (a : H) (ha : a ∈ A) (y : (modelUniv t k p e Fact.out).K), ψ y = a →
      π y = τ ⟨a, ha⟩ := by
    intro a ha y h
    subst h
    rfl
  have hzz : z * z = 1 := hz.sq
  have htA : ψ x' ∈ A := by
    obtain ⟨u, huA, hu1, huz⟩ := thm5IH_exists_ne hA4 1 z
    rcases hd.elems u huA with h | h | h | h
    · exact absurd h hu1
    · exact absurd h huz
    · rw [← h]
      exact huA
    · have : ψ x' = z * u := by
        rw [h, ← mul_assoc, hzz, one_mul]
      rw [this]
      exact A.mul_mem hzA huA
  have hFelem : ∀ g ∈ inducedImage L A, g = 1 ∨ g = π x ∨ g = π x' ∨ g = π (x * x') := by
    intro g hg
    rw [hF] at hg
    obtain ⟨⟨a, ha⟩, rfl⟩ := hg
    rcases hd.elems a ha with h | h | h | h
    · left
      have : (⟨a, ha⟩ : ↥A) = 1 := Subtype.ext h
      rw [this, map_one]
    · right; left
      have : (⟨a, ha⟩ : ↥A) = ⟨z, hzA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ z hzA x hd.map_x).symm
    · right; right; left
      have : (⟨a, ha⟩ : ↥A) = ⟨ψ x', htA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ _ htA x' rfl).symm
    · right; right; right
      have : (⟨a, ha⟩ : ↥A) = ⟨z * ψ x', A.mul_mem hzA htA⟩ := Subtype.ext h
      rw [this]
      exact (hπτ _ (A.mul_mem hzA htA) (x * x') (by rw [map_mul, hd.map_x])).symm
  have hFR : inducedImage L A ≤ π.range := by
    intro g hg
    rcases hFelem g hg with h | h | h | h
    · rw [h]; exact π.range.one_mem
    · rw [h]; exact ⟨x, rfl⟩
    · rw [h]; exact ⟨x', rfl⟩
    · rw [h]; exact ⟨x * x', rfl⟩
  have hxx' : (x * x') * (x * x') = 1 := by
    calc (x * x') * (x * x') = x * (x' * x) * x' := by group
      _ = x * (x * x') * x' := by rw [hd.comm]
      _ = (x * x) * (x' * x') := by group
      _ = 1 := by rw [hd.sq, hd.sq', one_mul]
  have hprodF : ∀ g ∈ inducedImage L A, g ≠ 1 →
      ∃ A' B' : Subgroup ↥(inducedAutOn L), CentralizerProd π.range g A' B' := by
    intro g hg hg1
    have key : ∀ y : (modelUniv t k p e Fact.out).K, y * y = 1 → π y = g →
        ∃ A' B' : Subgroup ↥(inducedAutOn L), CentralizerProd π.range g A' B' := by
      intro y hy2 hyg
      have hyc : ¬ ∀ s, y * s = s * y := fun hall =>
        hg1 (hyg ▸ thm5IH_innerHom_eq_one_of_central ψ hall)
      obtain ⟨A', B', h⟩ := hprod hp2 hq hadm π hπk y hy2 hyc
      exact ⟨A', B', hyg ▸ h⟩
    rcases hFelem g hg with h | h | h | h
    · exact absurd h hg1
    · exact key x hd.sq h.symm
    · exact key x' hd.sq' h.symm
    · exact key (x * x') hxx' h.symm
  have hπx : π x ∈ inducedImage L A := by
    rw [hF]
    exact ⟨⟨z, hzA⟩, (hπτ z hzA x hd.map_x).symm⟩
  have hπx' : π x' ∈ inducedImage L A := by
    rw [hF]
    exact ⟨⟨ψ x', htA⟩, (hπτ _ htA x' rfl).symm⟩
  have hker_ne : π.ker ≠ ⊤ := by
    intro h
    have h1 : π x = 1 := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)
    exact hne1 z hzA hz.ne_one ((hπτ z hzA x hd.map_x) ▸ h1)
  have hq' : CFSG.Open.IsQuasisimple ↥π.range :=
    CFSG.ComponentClassification.Quasisimple.range_quasisimple_of_ker_ne_top hopen π hker_ne
  have hcomp : CFSG.IsComponent π.range :=
    ⟨(CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hq',
      hnorm.isSubnormal⟩
  have hFN : inducedImage L A ≤ Subgroup.normalizer (π.range : Set ↥(inducedAutOn L)) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hgen := hLG hp2 hq hadm ↥(inducedAutOn L) π hπk hcomp R hR R' hR' (π x)
    (Subgroup.mem_map_of_mem π hd.mem) (π x') (Subgroup.mem_map_of_mem π hd.mem')
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hd.central r hr])
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hd.central' r hr])
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, (hd.comm_RR' r hr x' hd.mem').symm])
    (by
      rintro _ ⟨r, hr, rfl⟩
      rw [← map_mul, ← map_mul, hd.comm_RR' x hd.mem r hr])
    (inducedImage L A) hcardF hFsq hFN (fun g _ hg1 hall => hg1 (hcentY g hall)) (π x) hπx (π x')
    hπx'
    (by
      rw [hπτ z hzA x hd.map_x]
      exact hne1 z hzA hz.ne_one)
    (by
      rw [hπτ _ htA x' rfl]
      exact hne1 _ htA hd.map_x'_ne_one)
    (by
      rw [hπτ z hzA x hd.map_x, hπτ _ htA x' rfl]
      intro h
      exact hd.ne (congrArg Subtype.val (hτinj h)))
    (fun y _ => rfl) (fun y _ => rfl)
  exact thm5IH_alphaOf_eq_bot_of_prod_layers hnorm hcentY hFsq hFR hprodF hgen

end CFSG.ClassicalInvolution.Asc77

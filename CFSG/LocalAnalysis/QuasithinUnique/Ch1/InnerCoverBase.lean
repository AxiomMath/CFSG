module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Families
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverEven
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Open CFSG.QuasithinUnique

@[expose] def NonSporadicList (X : Type) [Group X] : Prop :=
  AltList X ∨ OddList X ∨ SQTKCharTwoLie X

@[expose] def SylowCentralizerCentral (K : Type) [Group K] [Finite K] : Prop :=
  ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L → IsPGroup 2 (Subgroup.center L) →
    Subgroup.center L ≠ ⊥ → Nonempty ((L ⧸ Subgroup.center L) ≃* K) →
    ∀ P : Sylow 2 L, ∀ x ∈ (P : Subgroup L), x * x ∈ Subgroup.center L →
      x ∈ Subgroup.centralizer ((P : Subgroup L) : Set L) → x ∈ Subgroup.center L

theorem sylowCentralizerCentral_of_bender {K : Type} [Group K] [Finite K]
    (h : fusionIsBenderGroup K) : SylowCentralizerCentral K := by
  intro L _ _ hperf hZ hne ⟨e⟩ P x _ _ hx
  by_contra hxn
  have := hperf
  exact hne (RankOneRecog.center_eq_bot_of_noncentral_sylow_centralizer hZ
    (RankOneRecog.fusionIsBenderGroup_of_mulEquiv e.symm h) P hx hxn)

theorem sylowCentralizerCentral_of_cover_trivial {K : Type} [Group K] [Finite K]
    (H : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (η : E →* K),
      Function.Surjective η → η.ker ≤ Subgroup.center E → IsPGroup 2 η.ker → η.ker = ⊥) :
    SylowCentralizerCentral K := by
  intro L _ _ hperf hZ hne ⟨e⟩ P x _ _ hx
  exfalso
  apply hne
  have := hperf
  have hker := RankOneRecog.ker_comp_centerQuotient e
  have hsurj : Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have h2 : IsPGroup 2 (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker := by
    rw [hker]
    exact hZ
  have hbot := H L _ hsurj hker.le h2
  rwa [hker] at hbot

namespace InvDatum

variable {L : Type} [Group L] [Finite L] {α : L ≃* L}

theorem exists_noncentral_sylow_centralizer (h : InvDatum L α) (hi : IsInnerAut α) :
    ∃ (P : Sylow 2 L) (l : L), l ∈ Subgroup.centralizer ((P : Subgroup L) : Set L) ∧
      l ∉ Subgroup.center L ∧ l ∈ (P : Subgroup L) ∧ l * l ∈ Subgroup.center L := by
  obtain ⟨l, hl⟩ := hi
  obtain ⟨P, hP⟩ := h.sylow
  obtain ⟨x, hx⟩ := h.nontrivial
  have hcomm : ∀ t ∈ (P : Subgroup L), t * l = l * t := by
    intro t ht
    have h1 : l⁻¹ * t * l = t := by rw [← hl t]; exact hP t ht
    calc t * l = l * (l⁻¹ * t * l) := by group
      _ = l * t := by rw [h1]
  have hlP : l ∈ Subgroup.centralizer ((P : Subgroup L) : Set L) :=
    Subgroup.mem_centralizer_iff.mpr fun t ht => hcomm t ht
  have hln : l ∉ Subgroup.center L := by
    intro hc
    apply hx
    have h1 : α x = x := by
      rw [hl x, mul_assoc, Subgroup.mem_center_iff.mp hc x, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [h1, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hl2 : l * l ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := h.involutory g
    rw [hl, hl] at h1
    calc g * (l * l) = l * l * (l⁻¹ * (l⁻¹ * g * l) * l) := by group
      _ = l * l * g := by rw [h1]
  have hZ := h.isPGroup_center_of_inner ⟨l, hl⟩
  obtain ⟨k, hk⟩ := hZ ⟨l * l, hl2⟩
  have hk' : (l * l) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hl' : l ^ 2 ^ (k + 1) = 1 := by
    calc l ^ 2 ^ (k + 1) = (l ^ 2) ^ 2 ^ k := by rw [pow_succ', pow_mul]
      _ = (l * l) ^ 2 ^ k := by rw [pow_two]
      _ = 1 := hk'
  have hz : IsPGroup 2 ↥(Subgroup.zpowers l) := isPGroup_zpowers_of_pow hl'
  have hsup : IsPGroup 2 ↥((P : Subgroup L) ⊔ Subgroup.zpowers l) := by
    refine P.isPGroup'.to_sup_of_normal_right' hz fun a ha => ?_
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact ((show Commute a l from hcomm a ha).zpow_right i).eq.symm
  have hmax := P.is_maximal' hsup le_sup_left
  refine ⟨P, l, hlP, hln, ?_, hl2⟩
  have hmem : l ∈ (P : Subgroup L) ⊔ Subgroup.zpowers l :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers l)
  rw [hmax] at hmem
  exact hmem

end InvDatum

theorem innerCover_nonSporadic_of_sylowCentralizerCentral
    (H : ∀ (X : Type) [Group X] [Finite X], NonSporadicList X → ¬ IsL34OrG24 X →
      SylowCentralizerCentral X) : InnerCover NonSporadicList := by
  intro L _ _ α h hi hz hP
  by_cases hA : IsL34OrG24 (L ⧸ Subgroup.center L)
  · exact Or.inl hA
  · exfalso
    obtain ⟨P, l, hl, hln, hlP, hl2⟩ := h.exists_noncentral_sylow_centralizer hi
    exact hln (H (L ⧸ Subgroup.center L) hP hA L h.perfect (h.isPGroup_center_of_inner hi) hz
      ⟨MulEquiv.refl _⟩ P l hlP hl2 hl)

end CFSG.QuasithinUnique.Ch1

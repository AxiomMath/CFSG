module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11P34Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7KFact
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1L44c
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairMaximal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open scoped commutatorElement

structure P34YData (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y) : Prop where
  normal : L.Normal
  simple : IsSimpleGroup L
  nonabelian : ∃ a b : L, a * b ≠ b * a
  equiv : Nonempty (L ≃* (TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11).Group)
  pGroup : IsPGroup 3 (centralizer (L : Set Y))
  commutative : IsMulCommutative (centralizer (L : Set Y))
  inf_eq_bot : L ⊓ centralizer (L : Set Y) = ⊥

theorem p34_comm_of_isMulCommutative {Y : Type*} [Group Y] {H : Subgroup Y}
    (hH : IsMulCommutative H) {a b : Y} (ha : a ∈ H) (hb : b ∈ H) : a * b = b * a :=
  congrArg Subtype.val (hH.is_comm.comm (⟨a, ha⟩ : H) ⟨b, hb⟩)

namespace P34YData

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem decomp (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (y : Y) :
    ∃ ℓ ∈ L, ∃ d ∈ centralizer (L : Set Y), y = ℓ * d := by
  have := h.normal
  obtain ⟨e⟩ := h.equiv
  exact l44_decomp L (hKM ↥L ⟨e⟩).1 y

theorem mem_center (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) {d : Y}
    (hd : d ∈ centralizer (L : Set Y)) : d ∈ center Y := by
  rw [mem_center_iff]
  intro y
  obtain ⟨ℓ, hℓ, d', hd', rfl⟩ := h.decomp hKM y
  have h1 : ℓ * d = d * ℓ := mem_centralizer_iff.mp hd ℓ hℓ
  have h2 : d' * d = d * d' := p34_comm_of_isMulCommutative h.commutative hd' hd
  calc ℓ * d' * d = ℓ * (d' * d) := mul_assoc _ _ _
    _ = ℓ * (d * d') := by rw [h2]
    _ = (ℓ * d) * d' := (mul_assoc _ _ _).symm
    _ = (d * ℓ) * d' := by rw [h1]
    _ = d * (ℓ * d') := mul_assoc _ _ _

omit [Finite Y] in
theorem center_le (L : Subgroup Y) : center Y ≤ centralizer (L : Set Y) := fun _ hz =>
  mem_centralizer_iff.mpr fun l _ => (mem_center_iff.mp hz l)

theorem inf_center_eq_bot (h : P34YData Y L) : L ⊓ center Y = ⊥ :=
  eq_bot_iff.mpr fun z hz => by
    have := h.inf_eq_bot
    exact (eq_bot_iff.mp this) ⟨hz.1, center_le L hz.2⟩

theorem centralizer_le_sylow (h : P34YData Y L) (S : Sylow 3 Y) :
    centralizer (L : Set Y) ≤ (S : Subgroup Y) := by
  have := h.normal
  exact h.pGroup.le_sylow_of_normal S

theorem exists_sylow_eq_inf (h : P34YData Y L) (S : Sylow 3 Y) :
    ∃ T : Sylow 3 L, (T : Subgroup L).map L.subtype = (S : Subgroup Y) ⊓ L := by
  have := h.normal
  exact CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S h.normal.isSubnormal

theorem inf_elemAbelian (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (S : Sylow 3 Y) :
    IsElemAbelian 3 ((S : Subgroup Y) ⊓ L) ∧
      Nat.card ((S : Subgroup Y) ⊓ L : Subgroup Y) = 3 ^ 2 := by
  obtain ⟨e⟩ := h.equiv
  obtain ⟨T, hT⟩ := h.exists_sylow_eq_inf S
  obtain ⟨hTe, -⟩ := hKA ↥L ⟨e⟩ T
  have hTc := ((hKM ↥L ⟨e⟩).2 T).1
  rw [← hT]
  exact ⟨CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 hTe L.subtype,
    by rw [Subgroup.card_map_of_injective L.subtype_injective]; exact hTc⟩

theorem sylow_eq_mul (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (S : Sylow 3 Y) {s : Y} (hs : s ∈ (S : Subgroup Y)) :
    ∃ ℓ ∈ (S : Subgroup Y) ⊓ L, ∃ d ∈ centralizer (L : Set Y), s = ℓ * d := by
  obtain ⟨ℓ, hℓ, d, hd, rfl⟩ := h.decomp hKM s
  have hdS : d ∈ (S : Subgroup Y) := h.centralizer_le_sylow S hd
  have hℓS : ℓ ∈ (S : Subgroup Y) := by
    simpa using (S : Subgroup Y).mul_mem hs ((S : Subgroup Y).inv_mem hdS)
  exact ⟨ℓ, ⟨hℓS, hℓ⟩, d, hd, rfl⟩

theorem sylow_isMulCommutative (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (S : Sylow 3 Y) : IsMulCommutative (S : Subgroup Y) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨ℓ₁, hℓ₁, d₁, hd₁, ha⟩ := h.sylow_eq_mul hKM S a.2
  obtain ⟨ℓ₂, hℓ₂, d₂, hd₂, hb⟩ := h.sylow_eq_mul hKM S b.2
  have hel := (h.inf_elemAbelian hKM hKA S).1
  have h1 : ℓ₁ * ℓ₂ = ℓ₂ * ℓ₁ := p34_comm_of_isMulCommutative hel.1 hℓ₁ hℓ₂
  have h2 : d₁ * d₂ = d₂ * d₁ := p34_comm_of_isMulCommutative h.commutative hd₁ hd₂
  have h3 : d₁ * ℓ₂ = ℓ₂ * d₁ := (mem_centralizer_iff.mp hd₁ ℓ₂ hℓ₂.2).symm
  have h4 : d₂ * ℓ₁ = ℓ₁ * d₂ := (mem_centralizer_iff.mp hd₂ ℓ₁ hℓ₁.2).symm
  apply Subtype.ext
  change (a : Y) * b = b * a
  rw [ha, hb]
  calc ℓ₁ * d₁ * (ℓ₂ * d₂) = ℓ₁ * (d₁ * ℓ₂) * d₂ := by group
    _ = ℓ₁ * (ℓ₂ * d₁) * d₂ := by rw [h3]
    _ = (ℓ₁ * ℓ₂) * (d₁ * d₂) := by group
    _ = (ℓ₂ * ℓ₁) * (d₂ * d₁) := by rw [h1, h2]
    _ = ℓ₂ * (ℓ₁ * d₂) * d₁ := by group
    _ = ℓ₂ * (d₂ * ℓ₁) * d₁ := by rw [h4]
    _ = ℓ₂ * d₂ * (ℓ₁ * d₁) := by group

theorem inf_eq_bot_two_three {F D : Subgroup Y} (hF : IsPGroup 2 F) (hD : IsPGroup 3 D) :
    F ⊓ D = ⊥ := by
  refine CFSG.AGLEmbedding.inf_eq_bot_of_isPGroup Nat.prime_two hF ?_
  obtain ⟨n, hn⟩ := hD.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right _ (by norm_num)

theorem sylow_commute_two (h : P34YData Y L) (hKM : CFSG.AGLEmbeddingD2.KFactM11Three)
    (hKA : KFactM11TwoSignalizer) (hSig : SignalizerTwoGroupKFact) (S : Sylow 3 Y)
    {F : Subgroup Y} (hF : IsPGroup 2 F)
    (hSF : ∀ s ∈ (S : Subgroup Y), s ∈ normalizer (F : Set Y)) :
    ∀ s ∈ (S : Subgroup Y), ∀ f ∈ F, s * f = f * s := by
  obtain ⟨hBe, hBc⟩ := h.inf_elemAbelian hKM hKA S
  set B : Subgroup Y := (S : Subgroup Y) ⊓ L with hB
  have hBD : B ⊓ centralizer (L : Set Y) = ⊥ :=
    eq_bot_iff.mpr fun z hz => (eq_bot_iff.mp h.inf_eq_bot) ⟨hz.1.2, hz.2⟩
  have hSE : IsRankTwoSEGroup 3 ↥L :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr h.equiv⟩)))
  have hBF : B ≤ normalizer (F : Set Y) := fun b hb => hSF b hb.1
  have hcomm := hSig Y L h.normal h.simple h.nonabelian
    ⟨TauCeti.CFSGIndex.sporadic TauCeti.SporadicName.M11, h.equiv⟩ 3 Nat.prime_three (by norm_num)
    B hBe hBc hBD (Or.inl ⟨hSE, inf_le_right⟩) F hF hBF
  have hBF' : ⁅B, F⁆ ≤ F := Subgroup.commutator_le.mpr fun b hb f hf => by
    have h1 := (mem_normalizer_iff.mp (hBF hb) f⁻¹).mp (F.inv_mem hf)
    have h2 : ⁅b, f⁆ = (b * f * b⁻¹) * f⁻¹ := by
      rw [commutatorElement_def]
    rw [h2]
    have h3 : b * f * b⁻¹ ∈ F := by
      have := (mem_normalizer_iff.mp (hBF hb) f).mp hf
      exact this
    exact F.mul_mem h3 (F.inv_mem hf)
  have hbot : ⁅B, F⁆ = ⊥ := by
    refine eq_bot_iff.mpr fun c hc => ?_
    have h1 : c ∈ F ⊓ centralizer (L : Set Y) := ⟨hBF' hc, hcomm hc⟩
    rw [inf_eq_bot_two_three hF h.pGroup] at h1
    exact h1
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
  intro s hs f hf
  obtain ⟨ℓ, hℓ, d, hd, rfl⟩ := h.sylow_eq_mul hKM S hs
  have h1 : ℓ * f = f * ℓ := (mem_centralizer_iff.mp (hbot hℓ) f hf).symm
  have h2 : d * f = f * d := (mem_center_iff.mp (h.mem_center hKM hd) f).symm
  calc ℓ * d * f = ℓ * (d * f) := mul_assoc _ _ _
    _ = ℓ * (f * d) := by rw [h2]
    _ = (ℓ * f) * d := (mul_assoc _ _ _).symm
    _ = (f * ℓ) * d := by rw [h1]
    _ = f * (ℓ * d) := mul_assoc _ _ _

theorem sylow_transitive (h : P34YData Y L) (hKT : KFactM11SylowTransitive) (S : Sylow 3 Y)
    {a b : Y} (ha : a ∈ (S : Subgroup Y) ⊓ L) (hb : b ∈ (S : Subgroup Y) ⊓ L) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) :
    ∃ n ∈ L, n ∈ normalizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) ∧ n * a * n⁻¹ = b := by
  obtain ⟨e⟩ := h.equiv
  obtain ⟨T, hT⟩ := h.exists_sylow_eq_inf S
  have hmem : ∀ z : Y, z ∈ (S : Subgroup Y) ⊓ L → ∃ t ∈ (T : Subgroup L), (t : Y) = z := by
    intro z hz
    rw [← hT] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact ⟨t, ht, rfl⟩
  obtain ⟨a', ha', rfl⟩ := hmem a ha
  obtain ⟨b', hb', rfl⟩ := hmem b hb
  have ha1' : a' ≠ 1 := fun h' => ha1 (by rw [h']; rfl)
  have hb1' : b' ≠ 1 := fun h' => hb1 (by rw [h']; rfl)
  obtain ⟨n', hn', hnab⟩ := hKT ↥L ⟨e⟩ T a' b' ha' hb' ha1' hb1'
  refine ⟨(n' : Y), n'.2, ?_, ?_⟩
  · have := Subgroup.le_normalizer_map L.subtype ⟨n', hn', rfl⟩
    rwa [hT] at this
  · exact congrArg Subtype.val hnab

end P34YData

end CFSG.LocalAnalysis.RankThreeTheoremC

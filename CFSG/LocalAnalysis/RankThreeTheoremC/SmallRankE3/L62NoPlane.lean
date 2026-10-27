module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Triple
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.L62Center
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentCase
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftEbar
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.LiftFaith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3

variable {H : Type} [Group H] [Finite H]

theorem l62_center_isCyclic (hNC : T29.NoncyclicCentreRank)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections H)
    (hH : primeComplementCore (G := H) 3 = ⊥) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3)
    {C : Subgroup H} (hC : IsComponentOf C ⊤) : IsCyclic ↥(center ↥C) := by
  by_contra hnc
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) :=
    hNC ↥C hC.2.2 (hcat.isCatalogGroup_center_quotient hC) (l62_center_isPGroup hH hC) hnc
  have hmono : CFSG.Open.pRank 3 (⊤ : Subgroup ↥C) ≤
      CFSG.Open.pRank 3 ((⊤ : Subgroup ↥C).map C.subtype) :=
    CFSG.SectionRank.pRank_le_map (by norm_num) C.subtype C.subtype_injective ⊤
  have hmono2 : CFSG.Open.pRank 3 ((⊤ : Subgroup ↥C).map C.subtype) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup H) :=
    CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top
  omega

theorem l62_card_inf_center_le {C : Subgroup H} (hZc : IsCyclic ↥(center ↥C)) {E : Subgroup H}
    (hE : IsElemAbelian 3 E) : Nat.card ↥(E ⊓ (center ↥C).map C.subtype) ≤ 3 := by
  have hcyc : IsCyclic ↥((center ↥C).map C.subtype) := by
    have e : ↥(center ↥C) ≃* ↥((center ↥C).map C.subtype) :=
      (center ↥C).equivMapOfInjective C.subtype C.subtype_injective
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  have hA : IsCyclic ↥(E ⊓ (center ↥C).map C.subtype) :=
    isCyclic_of_injective (Subgroup.inclusion (inf_le_right : E ⊓ (center ↥C).map C.subtype ≤
      (center ↥C).map C.subtype)) (Subgroup.inclusion_injective _)
  exact l62_card_le_three_of_cyclic (CFSG.Open.IsElemAbelian.mono hE inf_le_left) hA

theorem l62_no_plane_of_triData (hNC : T29.NoncyclicCentreRank)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections H)
    (hH : primeComplementCore (G := H) 3 = ⊥) (hrk : CFSG.Open.pRank 3 (⊤ : Subgroup H) ≤ 3)
    {L₁ L₂ L₃ : Subgroup H} {g : H} (hT : TriData L₁ L₂ L₃ g) (hc₂ : IsComponentOf L₂ ⊤)
    (hc₃ : IsComponentOf L₃ ⊤) {E : Subgroup H} (hEL : E ≤ L₁) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : MulAut H := MulAut.conj g
  set E₂ : Subgroup H := E.map φ.toMonoidHom with hE₂def
  set E₃ : Subgroup H := E₂.map φ.toMonoidHom with hE₃def
  have hE₂L : E₂ ≤ L₂ := by rw [← hT.cyc₁]; exact Subgroup.map_mono hEL
  have hE₃L : E₃ ≤ L₃ := by rw [← hT.cyc₂]; exact Subgroup.map_mono hE₂L
  have hE₂ : IsElemAbelian 3 E₂ := hE.map φ.toMonoidHom
  have hE₃ : IsElemAbelian 3 E₃ := hE₂.map φ.toMonoidHom
  have hE₂9 : Nat.card E₂ = 9 :=
    (Nat.card_congr (E.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm.trans hE9
  have hE₃9 : Nat.card E₃ = 9 :=
    (Nat.card_congr (E₂.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv).symm.trans hE₂9
  have hz₂ := l62_center_isCyclic hNC hcat hH hrk hc₂
  have hz₃ := l62_center_isCyclic hNC hcat hH hrk hc₃
  have hZ₂ := l62_card_inf_center_le hz₂ hE₂
  have hZ₃ := l62_card_inf_center_le hz₃ hE₃
  have c12 : ∀ a ∈ E, ∀ b ∈ E₂, a * b = b * a := fun a ha b hb => hT.c12 a (hEL ha) b (hE₂L hb)
  have c13 : ∀ a ∈ E, ∀ c ∈ E₃, a * c = c * a := fun a ha c hc => hT.c13 a (hEL ha) c (hE₃L hc)
  have c23 : ∀ b ∈ E₂, ∀ c ∈ E₃, b * c = c * b := fun b hb c hc => hT.c23 b (hE₂L hb) c (hE₃L hc)
  have hker : ∀ a ∈ E, ∀ b ∈ E₂, ∀ c ∈ E₃, a * b * c = 1 →
      b ∈ E₂ ⊓ (center ↥L₂).map L₂.subtype ∧ c ∈ E₃ ⊓ (center ↥L₃).map L₃.subtype := by
    intro a ha b hb c hc h1
    have hb' : b = a⁻¹ * c⁻¹ := by
      have : b * c = a⁻¹ := by
        have h2 : a * (b * c) = 1 := by rw [← mul_assoc]; exact h1
        exact (inv_eq_of_mul_eq_one_right h2).symm
      calc b = b * c * c⁻¹ := by group
        _ = a⁻¹ * c⁻¹ := by rw [this]
    have hc' : c = b⁻¹ * a⁻¹ := by
      have : a * b = c⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
      have h3 : (a * b)⁻¹ = c := by rw [this, inv_inv]
      rw [← h3, mul_inv_rev]
    refine ⟨⟨hb, ?_⟩, ⟨hc, ?_⟩⟩
    · refine ⟨⟨b, hE₂L hb⟩, ?_, rfl⟩
      show (⟨b, hE₂L hb⟩ : ↥L₂) ∈ center ↥L₂
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hla : Commute (l : H) a := (hT.c12 a (hEL ha) l l.2).symm
      have hlc : Commute (l : H) c := hT.c23 (l : H) l.2 c (hE₃L hc)
      have := (hla.inv_right.mul_right hlc.inv_right).eq
      show (l : H) * b = b * l
      rw [hb']
      exact this
    · refine ⟨⟨c, hE₃L hc⟩, ?_, rfl⟩
      show (⟨c, hE₃L hc⟩ : ↥L₃) ∈ center ↥L₃
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      have hlb : Commute (l : H) b := (hT.c23 b (hE₂L hb) l l.2).symm
      have hla : Commute (l : H) a := (hT.c13 a (hEL ha) l l.2).symm
      have := (hlb.inv_right.mul_right hla.inv_right).eq
      show (l : H) * c = c * l
      rw [hc']
      exact this
  obtain ⟨hF, h81⟩ := l62_card_triple_prod hE hE₂ hE₃ c12 c13 c23 hE9 hE₂9 hE₃9 hZ₂ hZ₃ hker
  have hFp : IsPGroup 3 ↥(E ⊔ E₂ ⊔ E₃) := fun x => ⟨1, by simpa using Subtype.ext (hF.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hFp.exists_card_eq
  have hk4 : 4 ≤ k := by
    by_contra hlt
    have hk3 : k ≤ 3 := by omega
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    omega
  have hle := CFSG.SectionRank.le_pRank Nat.prime_three.one_lt (le_top : E ⊔ E₂ ⊔ E₃ ≤ ⊤) hF hk
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

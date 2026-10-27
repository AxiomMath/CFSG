module

public import CFSG.CGT.PushingUpLit.Glue.BlockInteract

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.QuasithinUnique.Setup.Campbell (pRank_mono)

variable {G : Type} [Group G]

theorem jIn_eq_of_le_isPGroup [Finite G] {T S : Subgroup G} (hT : IsSylowOf 2 T ⊤)
    (hJS : jIn T ≤ S) (hS : IsPGroup 2 S) : jIn S = jIn T := by
  obtain ⟨T₁, hT₁, hST₁⟩ := Nine.exists_isSylowOf_ge (K := ⊤) hS le_top
  obtain ⟨h, -, hTh⟩ := exists_conjugate_eq_of_isSylowOf hT₁ hT
  have hrT : pRank 2 ↥T = pRank 2 ↥T₁ :=
    (Glue.pRank_eq_of_isSylowOf hT).trans (Glue.pRank_eq_of_isSylowOf hT₁).symm
  have hrJ : pRank 2 ↥(jIn T) = pRank 2 ↥T := pRank_jIn T
  have h1 : pRank 2 ↥(jIn T) ≤ pRank 2 ↥S := pRank_mono hJS
  have h2 : pRank 2 ↥S ≤ pRank 2 ↥T₁ := pRank_mono hST₁
  have hrS : pRank 2 ↥(jIn T) = pRank 2 ↥S := by omega
  have hrS₁ : pRank 2 ↥S = pRank 2 ↥T₁ := by omega
  have hle1 : jIn T ≤ jIn S := by
    have := jIn_mono_of_pRank_eq hJS hrS
    rwa [jIn_jIn] at this
  have hle2 : jIn S ≤ jIn T₁ := jIn_mono_of_pRank_eq hST₁ hrS₁
  have hcard : Nat.card ↥(jIn T₁) ≤ Nat.card ↥(jIn T) := by
    rw [hTh, ← conjugate_jIn]
    exact (Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective).le
  have hTT₁ : jIn T = jIn T₁ := Subgroup.eq_of_le_of_card_ge (hle1.trans hle2) hcard
  exact le_antisymm (hle2.trans hTT₁.ge) hle1

theorem isSylowOf_conjugate_top [Finite G] {T : Subgroup G} (hT : IsSylowOf 2 T ⊤) (g : G) :
    IsSylowOf 2 (conjugate T g) ⊤ := by
  refine ⟨le_top, hT.2.1.of_equiv (T.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective), ?_⟩
  have h := hT.2.2
  rw [Subgroup.relIndex_top_right] at h ⊢
  rwa [conjugate, Subgroup.index_map_of_bijective (MulAut.conj g⁻¹).bijective]

theorem jIn_eq_conjugate_of_le_isPGroup [Finite G] {T S : Subgroup G} (hT : IsSylowOf 2 T ⊤)
    (g : G) (hJS : conjugate (jIn T) g ≤ S) (hS : IsPGroup 2 S) :
    jIn S = conjugate (jIn T) g := by
  have h := jIn_eq_of_le_isPGroup (isSylowOf_conjugate_top hT g)
    (by rw [conjugate_jIn] at hJS; exact hJS) hS
  rw [h, conjugate_jIn]

end CFSG.CGT.PushingUpLit.CGT6

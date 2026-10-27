module

public import CFSG.CGT.PushingUpLit.BHS7.QuotInv
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.BHS7.QuotOffender

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.LieType.BorelTits
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

section KLevel

variable {V : Type} [CommGroup V] [Finite V] {K S : Subgroup (MulAut V)}

theorem not_le_of_mem_offQ (hK2 : pCoreOf 2 K = ⊥) {P E R : Subgroup (MulAut V)} (hPK : P ≤ K)
    (hKPE : K ≤ P ⊔ E) (hRS : R ≤ S) (hSK : S ≤ K)
    (hPR : P ≤ Subgroup.normalizer (R : Set (MulAut V))) (hR2 : IsPGroup 2 ↥R)
    (hcomm : ∀ B ∈ offQMin K S, ∀ g ∈ E, ∀ b ∈ B, g * b = b * g)
    {C : Subgroup (MulAut V)} (hC : C ∈ offQ K S) (hCR : C ≤ R) : False := by
  set 𝒮 : Set (Subgroup (MulAut V)) := {B | B ∈ offQMin K S ∧ B ≤ R} with h𝒮
  have hemp : 𝒮 = ∅ := by
    refine eq_empty_of_conj_closed hK2 hKPE (R := R) ?_ ?_ ?_ hR2
    · rintro g hg B ⟨hB, hBR⟩
      have hle : conjSub g B ≤ R := by
        have := conjSub_mono g hBR
        rwa [conjSub_eq_of_mem_normalizer (hPR hg)] at this
      exact ⟨conjSub_mem_offQMin (hPK hg) hB (hle.trans hRS), hle⟩
    · rintro g hg B ⟨hB, hBR⟩
      rw [conjSub_eq_of_commute (hcomm B hB g hg)]
      exact ⟨hB, hBR⟩
    · rintro B ⟨hB, hBR⟩
      exact ⟨hB.1.1.trans hSK, hBR, ne_bot_of_mem_offQ hB.1⟩
  obtain ⟨B, hB, hBC⟩ := exists_offQMin_le hC
  have : B ∈ 𝒮 := ⟨hB, hBC.trans hCR⟩
  rw [hemp] at this
  exact this

@[expose] def qSubQ (K S : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  ⨆ B : ↥(offQMin K S), (B : Subgroup (MulAut V))

omit [Finite V] in
theorem le_qSubQ {B : Subgroup (MulAut V)} (hB : B ∈ offQMin K S) : B ≤ qSubQ K S :=
  le_iSup (fun B : ↥(offQMin K S) => (B : Subgroup (MulAut V))) ⟨B, hB⟩

omit [Finite V] in
theorem qSubQ_le_centralizer {E : Subgroup (MulAut V)}
    (hcomm : ∀ B ∈ offQMin K S, ∀ g ∈ E, ∀ b ∈ B, g * b = b * g) :
    qSubQ K S ≤ Subgroup.centralizer (E : Set (MulAut V)) := by
  refine iSup_le fun B b hb => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact hcomm B B.2 g hg b hb

omit [Finite V] in
theorem conjSub_qSubQ_le {τ : MulAut V} (hτK : τ ∈ K) (hτS : τ ∈ S) :
    conjSub τ (qSubQ K S) ≤ qSubQ K S := by
  unfold qSubQ
  rw [conjSub_iSup]
  refine iSup_le fun B => ?_
  have hle : conjSub τ (B : Subgroup (MulAut V)) ≤ S := by
    intro x hx
    rw [mem_conjSub_iff] at hx
    have := B.2.1.1 hx
    have h2 : x = τ * (τ⁻¹ * x * τ) * τ⁻¹ := by group
    rw [h2]
    exact S.mul_mem (S.mul_mem hτS this) (S.inv_mem hτS)
  exact le_iSup (fun B : ↥(offQMin K S) => (B : Subgroup (MulAut V)))
    ⟨conjSub τ B, conjSub_mem_offQMin hτK B.2 hle⟩

end KLevel

end CFSG.CGT.PushingUpLit.BHS7

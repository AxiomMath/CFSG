module

public import CFSG.GF2Type.Smith1979.W4AsE11Main
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.GF2Type.Smith1979.W4AsOmega
public import CFSG.GF2Type.Smith1979.W4AsSel
public import CFSG.GF2Type.Smith1979.W4AsTI
public import CFSG.GF2Type.Smith1980Orth.Setup
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32NSp4Over

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4As

open Subgroup Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

@[expose] def LinGen4All : Prop :=
  ∀ {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G},
    S.width = 4 → S11.NoA2All S → Hyp4 S g → Cons311 S g → ¬ S.IsReducible →
    ∀ {t : S.O} (ht : t ∈ S.Lbar g), t ≠ 1 → LinCase S g ht →
      Module.finrank (ZMod 2) (Vt S g t) = 2 → CFSG.GH74.SectionalTwoRankLE S.Mbar 4

section Wiring

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem rbar_ne_of_linCase (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} {ht : t ∈ S.Lbar g}
    (hL : LinCase S g ht) : Rbar S g t ≠ S.Lbar g := by
  intro hR
  have h1 := Submodule.finrank_mono (S11.Vt_le_span_of_Rbar_eq H C hR)
  have h2 := finrank_span_singleton (K := ZMod 2)
    (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
  have h3 := hL.two_le_finrank
  omega

theorem hyp_of_no_omega (hw : S.width = 4) (hno : S11.NoA2All S) (H : Hyp4 S g)
    (C : Cons311 S g) (hΩ : ∀ t ∈ S.Lbar g, t ≠ 1 → V S g t ≤ S.Qa g) : S11.Hyp S g := by
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  refine ⟨H, C, hno, fun {t} ht ht1 => ?_⟩
  by_cases hR : Rbar S g t = S.Lbar g
  · exact Or.inl hR
  · rcases classify_four hw H hNo C ht ht1 hR with ⟨hL, -⟩ | ⟨hVQ, -⟩
    · exact Or.inr hL
    · exact absurd (hΩ t ht ht1) hVQ

theorem false_of_lin_only [IsSimpleGroup G] (h111 : S11_1StmtW4) (hw : S.width = 4)
    (hno : S11.NoA2All S) (hirr : ¬ S.IsReducible) (H : Hyp4 S g) (C : Cons311 S g)
    (hΩ : ∀ t ∈ S.Lbar g, t ≠ 1 → V S g t ≤ S.Qa g)
    (hT : ∃ t ∈ S.Lbar g, t ≠ 1 ∧ Rbar S g t ≠ S.Lbar g) : False := by
  have hy := hyp_of_no_omega hw hno H C hΩ
  obtain ⟨k, u, hτ, hkQ, hkz, huQ, huk, hR⟩ := h111 G S g hy hirr hw hT
  have hyk : S11.Hyp S k := hy.of_conj hkQ hkz
  have K := hyk.conf (τ := ⟨u * S.z * u⁻¹, hτ⟩) (u := u) rfl huQ huk hR
  have hodd := K.odd_width_add_finrank hyk
  rcases classify_four hw hyk.hyp4 hyk.noA2' hyk.cons K.mem_Lbar K.ne_one hR with
    ⟨-, h2⟩ | ⟨hVQ, -⟩
  · rw [hw, h2] at hodd
    exact absurd hodd (by decide)
  · exact absurd (hyk.V_le_Qa K.mem_Lbar K.ne_one) hVQ

theorem linGen4_of_s11_1StmtW4 (h111 : S11_1StmtW4) (I : Smith1980Orth.TimInputs) :
    LinGen4All := by
  intro G _ _ _ S g hw hno H C hirr t ht ht1 hL _
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  by_cases hΩ : ∀ t ∈ S.Lbar g, t ≠ 1 → V S g t ≤ S.Qa g
  · exact (false_of_lin_only h111 hw hno hirr H C hΩ ⟨t, ht, ht1, rbar_ne_of_linCase H C hL⟩).elim
  · push Not at hΩ
    obtain ⟨t', ht', ht1', hVQ⟩ := hΩ
    have hR : Rbar S g t' ≠ S.Lbar g := fun h => hVQ (S11.V_le_Qa_of_Rbar_eq H C h)
    rcases classify_four hw H hNo C ht' ht1' hR with ⟨hL', -⟩ | ⟨hVQ', hΩ', h4⟩
    · exact absurd hL'.le_Qa hVQ
    · exact gen4_of_omega I.hCE hw H C hNo hirr ht' ht1' hVQ' hΩ' h4

end Wiring

section GenFourBetaAll

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {S : Setting G} {g : G}

theorem gen4_of_beta_all (I : Smith1980Orth.TimInputs) (hLin : LinGen4All) (hw : S.width = 4)
    (hno : S11.NoA2All S) (H : Hyp4 S g) (C : Cons311 S g) (hirr : ¬ S.IsReducible) :
    CFSG.GH74.SectionalTwoRankLE S.Mbar 4 := by
  have hNo : NoA2 S g := fun α h1 h2 h3 => hno g H.conj_mem H.conj_ne ⟨α, h1, h2, h3⟩
  by_cases hTI : ∀ h : S.M, S.Lbar ((h : G) * g) ⊓ S.Lbar g = ⊥ ∨ S.Lbar ((h : G) * g) = S.Lbar g
  · exact gen4_of_ti I.hF2 I.hBen I.hTI H C hNo hTI hirr
  · obtain ⟨t, ht, ht1, hR⟩ := exists_Rbar_ne_of_not_TI hTI
    rcases classify_four hw H hNo C ht ht1 hR with ⟨hL, hdim⟩ | ⟨hVQ, hΩ, h4⟩
    · exact hLin hw hno H C hirr ht ht1 hL hdim
    · exact gen4_of_omega I.hCE hw H C hNo hirr ht ht1 hVQ hΩ h4

end GenFourBetaAll

end CFSG.GF2Type.Smith1979.W4As

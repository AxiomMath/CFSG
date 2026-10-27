module

public import CFSG.LargeExtraspecial.S14C13Data
public import CFSG.LargeExtraspecial.S14C13Conj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem noA2_of_stage {t : S.O} (hSt : Stage S g t) : NoA2 S g := fun α h1 h2 h3 =>
  hSt.noA2 g hSt.hyp4.conj_mem hSt.hyp4.conj_ne ⟨α, h1, h2, h3⟩

variable (S g) in
structure B2Data {t : S.O} (ht : t ∈ S.Lbar g) where
  hVQ : ¬ V S g t ≤ S.Qa g
  Q : QuadraticForm (ZMod 2) (Vt S g t)
  hQ : Q.polarBilin.Nondegenerate
  hX : RmodN S g t = omegaGroup Q hQ
  hE : LmodN S g t = pointRadical Q (aV ht)
  horb : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht))
  h : S.M
  hh : S.ρ h ∈ Rbar S g t
  hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g
  hth : t ∈ S.Lbar ((h : G) * g)
  hab : polar Q (aV ht) (bV hth) = 1
  hdim : finrank (ZMod 2) (Vt S g t) = 8

namespace B2Data

variable {t : S.O} {ht : t ∈ S.Lbar g}

theorem Q_aV (D : B2Data S g ht) (H : Hyp4 S g) : D.Q (aV ht) = 0 :=
  (D.horb _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩

theorem Q_bV (D : B2Data S g ht) (H : Hyp4 S g) : D.Q (bV D.hth) = 0 :=
  (D.horb _ (bV_ne_zero H _)).mpr ((mem_orbitOf_RmodN_iff H.conj_mem ht).mpr
    ⟨S.ρ D.h, D.hh, (ρ_cl_conj_z S D.h H.conj_mem).symm⟩)

theorem nq_isCompl (D : B2Data S g ht) (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) [NQHyp S g t] :
    IsCompl (S2.fixOf (nqRep S g t D.hX) (pointRadical D.Q (aV ht) : Set _))
      (S2.fixOf (nqRep S g t D.hX) (pointRadical D.Q (bV D.hth) : Set _)) := by
  obtain ⟨-, hN0⟩ := pairGen_N0_of_occurs hCE hSt hocc
  obtain ⟨⟨H, C, ht', ht1, hVQ', hΩ, -⟩, -⟩ := hocc.1
  exact isCompl_of_radDecomp (S6.timmesfeld_6_5_omega H (noA2_of_stage hSt) C ht ht1 D.hVQ
    hΩ hN0 D.hh D.hb D.hX D.hE)

theorem finrank_nq (hSt : Stage S g t) (hocc : Config.omegaPlus8b.Occurs S g t)
    [NQHyp S g t] : finrank (ZMod 2) (NQ S g t) = 16 :=
  finrank_NQ_eq_of_card hSt.ne_one (mul_self_of_mem_Lbar S hSt.hyp4.conj_mem hSt.mem)
    (S6.self_mem_Nbar hSt.hyp4 hSt.mem) (e := 16) hocc.2.2

theorem exists_wv (D : B2Data S g ht) (hCE : CentralExtInput.{0}) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) :
    ∃ ρ : omegaGroup D.Q D.hQ →*
        (↥((Wt S g t).map (Vt S g t).mkQ) ≃ₗ[ZMod 2] ↥((Wt S g t).map (Vt S g t).mkQ)),
      (∀ (e : omegaGroup D.Q D.hQ) (x : Rbar S g t),
        (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV hSt.hyp4.conj_mem t x →
        ∀ w (hw : w ∈ Wt S g t), ((ρ e (secMk (Vt S g t) hw) :
          ↥((Wt S g t).map (Vt S g t).mkQ)) : S.Qt ⧸ Vt S g t) =
            (Vt S g t).mkQ (((x : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w)) ∧
      IsCompl (S2.fixOf ρ (pointRadical D.Q (aV ht) : Set _))
        (S2.fixOf ρ (pointRadical D.Q (bV D.hth) : Set _)) := by
  obtain ⟨⟨H, C, ht', ht1, hVQ', hΩ, -⟩, -⟩ := hocc.1
  obtain ⟨ρ, hρ, hD⟩ := S6.timmesfeld_6_1_two hCE H (noA2_of_stage hSt) C ht ht1 D.hVQ hΩ D.hh
    D.hb D.hX D.hE
  exact ⟨ρ, hρ, isCompl_of_radDecomp hD⟩

theorem finrank_wv (D : B2Data S g ht) (hSt : Stage S g t)
    (hocc : Config.omegaPlus8b.Occurs S g t) :
    finrank (ZMod 2) ↥((Wt S g t).map (Vt S g t).mkQ) = 16 := by
  have h := S6.finrank_wv hSt.hyp4 hSt.ne_one (S := S) (g := g)
  rw [D.hdim, hocc.2.1] at h
  change _ + 2 * 8 = 2 * 16 at h
  omega

end B2Data

end CFSG.LargeExtraspecial.S14

module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1Transfer
public import CFSG.Assembly.InCatalogConverse

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def KD264Y1FamA4 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .A 3 q ∧ 3 ∣ q.card - 1

@[expose] def KD264Y1FamU4 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedA 3 q ∧ 3 ∣ q.card + 1

@[expose] def KD264Y1FamA6 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .A 5 q ∧ 3 ∣ q.card + 1

@[expose] def KD264Y1FamU6 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedA 5 q ∧ 3 ∣ q.card - 1

@[expose] def KD264Y1FamA7 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .A 6 q ∧ 3 ∣ q.card + 1

@[expose] def KD264Y1FamU7 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedA 6 q ∧ 3 ∣ q.card - 1

@[expose] def KD264Y1FamC3 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .C 3 q

@[expose] def KD264Y1FamB3 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .B 3 q

@[expose] def KD264Y1FamD4 (e : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, e = .twistedD 4 q

@[expose] def KD264Y1Fam (e : TauCeti.LieTypeIndex) : Prop :=
  KD264Y1FamA4 e ∨ KD264Y1FamU4 e ∨ KD264Y1FamA6 e ∨ KD264Y1FamU6 e ∨ KD264Y1FamA7 e ∨
    KD264Y1FamU7 e ∨ KD264Y1FamC3 e ∨ KD264Y1FamB3 e ∨ KD264Y1FamD4 e

@[expose] def KD264Y1Out : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) ≤ 3 →
    ∀ a ∈ innAutDerived (TauCeti.CFSGIndex.lie d).Group, a ^ 3 = 1 →
      a ∈ inner (TauCeti.CFSGIndex.lie d).Group

@[expose] def KD264Y1Cls : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 →
    CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3 → KD264Y1Fam d.1

@[expose] def KD264Y1Kernel (P : TauCeti.LieTypeIndex → Prop) : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex) [Finite (TauCeti.CFSGIndex.lie d).Group],
    ¬ IsChevSimple 3 (TauCeti.CFSGIndex.lie d).Group → ¬ k2Lie 3 d.1 → ¬ k3Lie d.1 → P d.1 →
    ∀ E : Subgroup (TauCeti.CFSGIndex.lie d).Group, IsElemAbelian 3 E → Nat.card E = 27 →
      ∃ F ≤ E, Nat.card F = 9 ∧ ∃ H : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        H ≤ Subgroup.centralizer (F : Set (TauCeti.CFSGIndex.lie d).Group) ∧
        IsSubnormal H (Subgroup.centralizer (F : Set (TauCeti.CFSGIndex.lie d).Group)) ∧
        CFSG.Open.IsQuasisimple ↥H ∧ 3 ∣ Nat.card (↥H ⧸ Subgroup.center ↥H)

@[expose] def KD264Y1KerA4 : Prop := KD264Y1Kernel KD264Y1FamA4

@[expose] def KD264Y1KerU4 : Prop := KD264Y1Kernel KD264Y1FamU4

@[expose] def KD264Y1KerA6 : Prop := KD264Y1Kernel KD264Y1FamA6

@[expose] def KD264Y1KerU6 : Prop := KD264Y1Kernel KD264Y1FamU6

@[expose] def KD264Y1KerA7 : Prop := KD264Y1Kernel KD264Y1FamA7

@[expose] def KD264Y1KerU7 : Prop := KD264Y1Kernel KD264Y1FamU7

@[expose] def KD264Y1KerC3 : Prop := KD264Y1Kernel KD264Y1FamC3

@[expose] def KD264Y1KerB3 : Prop := KD264Y1Kernel KD264Y1FamB3

@[expose] def KD264Y1KerD4 : Prop := KD264Y1Kernel KD264Y1FamD4

theorem kd264Y1Row_of_pieces
    (hOut : KD264Y1Out) (hCls : KD264Y1Cls)
    (hA4 : KD264Y1KerA4) (hU4 : KD264Y1KerU4) (hA6 : KD264Y1KerA6) (hU6 : KD264Y1KerU6)
    (hA7 : KD264Y1KerA7) (hU7 : KD264Y1KerU7) (hC3 : KD264Y1KerC3) (hB3 : KD264Y1KerB3)
    (hD4 : KD264Y1KerD4) :
    KD264Y1Row := by
  intro d hfin hns hk2 hk3 hpR A hA hE hc
  have hAin : A ≤ inner (TauCeti.CFSGIndex.lie d).Group := fun a ha =>
    hOut d hns hk2 hk3 hpR a (hA ha) (hE.2 a ha)
  obtain ⟨-, hsimp⟩ := CFSG.Assembly.lie_finite_simple d
  haveI : IsSimpleGroup (TauCeti.CFSGIndex.lie d).Group := hsimp
  obtain ⟨Ab, hAbE, hAbc, hinj, hmap⟩ := exists_comap_of_le_inner hAin hE hc
  have hp3 : CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.CFSGIndex.lie d).Group) = 3 :=
    le_antisymm hpR (three_le_pRank_top hAbE hAbc)
  have hfam := hCls d hns hk2 hk3 hp3
  unfold KD264Y1Fam at hfam
  rcases hfam with h | h | h | h | h | h | h | h | h
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hA4 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hU4 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hA6 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hU6 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hA7 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hU7 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hC3 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hB3 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd
  · obtain ⟨Fb, hF, h9, H, hH, hsub, hq, hdvd⟩ := hD4 d hns hk2 hk3 h Ab hAbE hAbc
    exact exists_good_of_kernel hinj hmap hF h9 hH hsub hq hdvd

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end

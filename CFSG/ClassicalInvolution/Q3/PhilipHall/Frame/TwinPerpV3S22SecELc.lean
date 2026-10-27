module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecELb
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Gold
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ATr3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22SecELa
public import CFSG.ClassicalInvolution.Q3.TL4LieZ2Ck
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2Exit
public import Certificates.Certificate55123

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups Certificates.TL4LieZ2Inv
open CFSG.Blueprint
open scoped MatrixGroups

section Models

variable {X : Type} [Group X] {n : ℕ}

theorem concl163_of_autModel' (Mo : AutModel X (Equiv.Perm (Fin n)))
    {LP LA reps : List (Equiv.Perm (Fin n))} (hLP : ∀ g, g ∈ LP ↔ g ∈ Mo.P)
    (hLA : ∀ g ∈ Mo.A, g ∈ LA) (hPA : Mo.P ≤ Mo.A) (h : q8InvCheck LP LA reps = true)
    {Φ : Set (Subgroup X)}
    (hq : ∀ L ∈ Φ, ∀ P : Subgroup X, IsSylow2In P L → Nonempty (↥P ≃* QuaternionGroup 2)) :
    ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a := by
  intro L hL a ha P hP β hβ hfix
  obtain ⟨e⟩ := hq L hL P hP
  let e' : ↥P ≃* QuaternionGroup 2 := e
  have hco : ∀ u v : QuaternionGroup 2,
      ((e'.symm (u * v) : ↥P) : X) = (e'.symm u : X) * (e'.symm v : X) := fun u v => by
    rw [map_mul, Subgroup.coe_mul]
  have hz1 : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) ≠ 1 := fun h0 => by
    have h1 : e'.symm (QuaternionGroup.a 2) = e'.symm 1 := by
      rw [map_one]
      exact Subtype.ext h0
    exact absurd (e'.symm.injective h1) (by decide)
  have hzz : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) *
      (e'.symm (QuaternionGroup.a 2) : X) = 1 := by
    rw [← hco, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by
      decide, map_one, Subgroup.coe_one]
  have hza : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) = a :=
    (ha.unique _ (hP.1 (e'.symm (QuaternionGroup.a 2)).2) hzz).resolve_left hz1
  rw [← hza]
  refine LieZ2.eq_one_or_conj_of_autModel Mo hLP hLA hPA h hz1 hzz
    (i := (e'.symm (QuaternionGroup.a 1) : X)) (j := (e'.symm (QuaternionGroup.xa 0) : X))
    ?_ ?_ ?_ hβ (hfix _ (e'.symm _).2) (hfix _ (e'.symm _).2)
  · rw [← hco, show (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide]
  · rw [← hco, show (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide]
  · rw [← hco, ← hco, ← hco, show (QuaternionGroup.xa 0 * QuaternionGroup.a 1 :
      QuaternionGroup 2) = QuaternionGroup.a 2 * QuaternionGroup.a 1 * QuaternionGroup.xa 0 by
      decide]

end Models

section LieModels

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem concl163_l33
    (hq : ∀ L ∈ Φ, ∀ P : Subgroup X, IsSylow2In P L → Nonempty (↥P ≃* QuaternionGroup 2))
    (hl : LieModel X .PSL 3 3 1) :
    ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a := by
  obtain ⟨eP⟩ := L33.equiv_of_lieModel hl
  obtain ⟨Mo, hMP, hMA⟩ := L33.autModel eP
  have hPA : Mo.P ≤ Mo.A := by
    rw [hMP, hMA, L33.QP_closure, TA3.l33_QA_closure]
    exact Subgroup.closure_mono fun x hx => by
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
  exact concl163_of_autModel' Mo (LP := elemsT L33.QP) (LA := elemsT L33.QA)
    (reps := pickReps (elemsT L33.QP))
    (fun g => by
      rw [hMP]
      exact mem_elemsT _ L33.QP_ok g)
    (fun g hg => (mem_elemsT _ L33.QA_ok g).2 (hMA ▸ hg)) hPA
    Certificates.certificate55123.1 hq

theorem concl163_m11
    (hq : ∀ L ∈ Φ, ∀ P : Subgroup X, IsSylow2In P L → Nonempty (↥P ≃* QuaternionGroup 2))
    (hm : NativeSporadic.IsSporadic X .M11) :
    ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a := by
  obtain ⟨Mo, hMP, hMA⟩ := M11.autModel hm
  exact concl163_of_autModel' Mo (LP := elemsT M11.Q) (LA := elemsT M11.Q)
    (reps := pickReps (elemsT M11.Q))
    (fun g => by
      rw [hMP]
      exact mem_elemsT _ M11.Q_ok g)
    (fun g hg => (mem_elemsT _ M11.Q_ok g).2 (hMA ▸ hg)) (hMP.le.trans hMA.ge)
    Certificates.certificate55123.2 hq

end LieModels

section S3Kinds


@[expose] def Lie3S3Gen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], (∃ a b : Y, a * b ≠ b * a) →
    (LieModel Y .PSU 3 3 1 ∨ LieModel Y .G2 0 3 1 ∨ LieModel Y .trialityD4 0 3 1) →
      ∀ a b : Y, a * a = 1 → a ≠ 1 → b * b = 1 → b ≠ 1 → b ≠ a → a * b = b * a →
        Subgroup.centralizer ({a} : Set Y) ⊔ Subgroup.centralizer ({b} : Set Y) = ⊤

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem false_of_lieS3 (hgen : Lie3S3Gen) (hT : MuZ2Table) (hS : TwinDisc.Q8Section X Φ)
    (htr : ∀ K ∈ Φ, ∀ M ∈ Φ, ∃ g : X, conjSub g K = M) (hE : Disconnected.DEdgeless Φ)
    (hdisc : ¬ T3.DStarConnected Φ) {L : Subgroup X} (hL : L ∈ Φ) {S : Sylow 2 ↥L} {z : X}
    (hd : TightDatum L S z) (hc : TightCls X L S z)
    (hcl : CoreAssembly.conjClass (tightCore L) = Φ)
    (hlie : LieModel X .PSU 3 3 1 ∨ LieModel X .G2 0 3 1 ∨ LieModel X .trialityD4 0 3 1) : False := by
  have hΩ := hS.hyp
  obtain ⟨eQ⟩ := hc.1
  have hnab := exists_ne_comm_of_quat eQ
  have hsh := omegaStarNbr_eq_empty_of_gen hΩ hE htr
    (fun a b ha2 ha1 hb2 hb1 hba hab => hgen X hnab hlie a b ha2 ha1 hb2 hb1 hba hab) hdisc
  have hE' : TightEdgeless L := by
    show Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore L))
    rw [hcl]
    exact hE
  have hm : EdgelessMember3 L S z := ⟨hd, tightClsR_three_iff.mpr hc, hE'⟩
  have hmu : MuZ2Member L := fun W hW =>
    Q3T6.Mu.muIsoZ2_of_shape hd.partIHypG hW ⟨L, hcl ▸ hL⟩ (fun K hK => by
      rw [hcl] at hK ⊢
      exact hsh K hK)
  rcases hlie with h | h | h
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    have h4 := ((hT X L S z hm hmu hFs (hi ▸ one_dvd 6)).2.1 3 1 hF).2.2
    norm_num at h4
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact (hT X L S z hm hmu hFs (hi ▸ one_dvd 6)).2.2.1 3 1 hF
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact (hT X L S z hm hmu hFs (hi ▸ one_dvd 6)).2.2.2.1 3 1 hF

end S3Kinds

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.SecEL

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Blueprint

section Main


theorem secEdgelessConcl163_of {n : ℕ} (hcit : CIT3Below n) (hP : TightBelowRPlus 3 n)
    (hgen : SecEL.Lie3S3Gen) : SecEdgelessConcl163 n := by
  intro X _ _ Φ hlt hS htr hdisc hE L hL a ha hna P hP' β hβ2 hβP
  obtain ⟨S, z, hz, hd, hc, hcl⟩ := SecEL.exists_datum_of_edgeless hS htr hE hL
  have hza : a = z := ha.eq hz
  subst hza
  have hE' : TightEdgeless L := by
    show Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore L))
    rw [hcl]
    exact hE
  have h163 : Concl163Syl L S a := by
    rcases hP.tbelow X hlt L S a hd (tightClsR_three_iff.mpr hc) with hex | hgood
    · exact SecEL.concl163Syl_of_edgeless_exit hP.thm6 hlt hd hc hex hE' hna
    · obtain ⟨L', hKL, hL'⟩ := tightHasLift_of_good hd hgood
      have hΛ := inClass3_conjClass_of_lift hc hKL hL'
      have hLie : SecIdLie3 L a := ⟨L', hKL, hL', hΛ, hcit X hlt _ hΛ⟩
      have hCT : Uniform.CITBelowT (.sl2 3 1) n :=
        (Uniform.citBelowT_three_iff (p := 3) (f := 1) (by norm_num) n).mpr hcit
      rcases secIdLieEdgeless3Below_of hCT X hlt L S a hd hc hLie hE' with hl | hl | hl | hl | hl
      · exact fun β hβ2 hβS => SecEL.concl163_l33 hS.q8 hl L hL a ha _
          (isSylow2In_map_sylow L S) β hβ2 hβS
      · exact (SecEL.false_of_lieS3 hgen muZ2Table_proved hS htr hE hdisc hL hd hc hcl
          (Or.inl hl)).elim
      · exact (SecEL.false_of_lieS3 hgen muZ2Table_proved hS htr hE hdisc hL hd hc hcl
          (Or.inr (Or.inl hl))).elim
      · exact (SecEL.false_of_lieS3 hgen muZ2Table_proved hS htr hE hdisc hL hd hc hcl
          (Or.inr (Or.inr hl))).elim
      · exact fun β hβ2 hβS => SecEL.concl163_m11 hS.q8 hl L hL a ha _
          (isSylow2In_map_sylow L S) β hβ2 hβS
  exact Z2Exit.concl163_conjClass hd h163 L (hcl ▸ hL) a ha P hP' β hβ2 hβP

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

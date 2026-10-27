module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29D4
public import CFSG.GH74.Generic.BProg.B3.S3Sec29C1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D2
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.GH74.Generic.S45
open scoped commutatorElement

namespace S3Sec29D5

variable {G : Type} [Group G] [Finite G] {x y : G} {K A B Q D J : Subgroup G}

theorem Jss_le_centralizer (L : Subgroup G) : Jss y L ≤ centralizer ({y} : Set G) :=
  iSup_le fun _ => iSup_le fun hJ' => iSup_le fun _ => hJ'.1

theorem Jss_le_cSec (L : Subgroup G) : Jss y L ≤ cSec L :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hle => hle

theorem le_Jss {L : Subgroup G} (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hJL : J ≤ cSec L) : J ≤ Jss y L :=
  le_iSup₂_of_le (f := fun (J' : Subgroup G) (_ : IsPCompIn 2 (centralizer ({y} : Set G)) J') =>
    ⨆ (_ : J' ≤ cSec L), J') J hJ (le_iSup (fun _ : J ≤ cSec L => J) hJL)

omit [Finite G] in
theorem FixesLayer.mono {v : G} {M : Subgroup G} {P P' : Subgroup G}
    (h : S3Sec29C.FixesLayer v M y P') (hle : P ≤ P') : S3Sec29C.FixesLayer v M y P :=
  fun hM hyM _ _ _ S hS t ht s hs => h hM hyM S hS t (hle ht) s hs

theorem B_le_normalizer_Ly (h : Ctx29w G x K A B Q y y D J) :
    B ≤ normalizer ((Ly29 K y : Subgroup G) : Set G) := by
  obtain ⟨E, hEK, hAE, -, hEel, hE4, hyE⟩ := S3Sec29D2.exists_E h
  obtain ⟨hAB, hxB, -, hBel, -, -, hBeq⟩ := h.ext
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.1.1.2.2
  have hBK : B ≤ normalizer (K : Set G) := by
    rw [hBeq]
    refine sup_le ?_ (inf_le_right.trans (fun g hg => hg.1))
    rw [hAE]
    refine sup_le (fun e he => Subgroup.le_normalizer (hEK he)) ?_
    rw [Subgroup.zpowers_le]
    exact S3Theta52.mem_normalizer_of_le_centralizer hK.1
  have hBy := S3Sec29D2.B_le_centralizer_y h
  intro b hb
  exact S3Ctx29Layer.mem_normalizer_pLayerOf_of_mem_normalizer
    (S3Ctx29Layer.mem_normalizer_inf_centralizer (hBK hb)
      (Subgroup.mem_centralizer_singleton_iff.1 (hBy hb)))

theorem Q_le_centralizer_y (h : Ctx29w G x K A B Q y y D J) : Q ≤ centralizer ({y} : Set G) :=
  fun _ hq => Subgroup.mem_centralizer_singleton_iff.2
    ((Subgroup.mem_centralizer_iff.1 (h.Q_cent hq)) y (Subgroup.mem_inf.1 h.y_mem).1).symm

theorem Q_le_cSec_Ly (h : Ctx29w G x K A B Q y y D J) : Q ≤ cSec (Ly29 K y) := fun _ hq =>
  S3Ctx29Layer.mem_cSec_pLayerOf (Subgroup.mem_inf.1 (h.Q_syl.le hq)).2
    (Subgroup.mem_centralizer_singleton_iff.1 (Q_le_centralizer_y h hq))

omit [Finite G] in
theorem map_conj_centralizer {g : G} (hg : g ∈ centralizer ({y} : Set G)) :
    (centralizer ({y} : Set G)).map (MulAut.conj g).toMonoidHom = centralizer ({y} : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)

theorem conj_isPCompIn (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) {g : G}
    (hg : g ∈ centralizer ({y} : Set G)) :
    IsPCompIn 2 (centralizer ({y} : Set G)) (J.map (MulAut.conj g).toMonoidHom) := by
  have := Stage1.Thm2.Recip.isPCompIn_map_conj hJ g
  rwa [map_conj_centralizer hg] at this

theorem conj_le_Jss (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) {L : Subgroup G}
    (hJL : J ≤ cSec L) {g : G} (hg : g ∈ centralizer ({y} : Set G))
    (hgL : g ∈ normalizer (L : Set G)) : J.map (MulAut.conj g).toMonoidHom ≤ Jss y L := by
  refine le_Jss (conj_isPCompIn hJ hg) ?_
  rintro _ ⟨j, hj, rfl⟩
  exact Stage1.Thm2.Recip.cSec_conj L hgL (hJL hj)

theorem Jss_le_normalizer_J (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) (L : Subgroup G) :
    Jss y L ≤ normalizer (J : Set G) := by
  refine iSup_le fun J' => iSup_le fun hJ' => iSup_le fun _ => ?_
  by_cases he : J' = J
  · rw [he]; exact Subgroup.le_normalizer
  · exact (Stage1.Thm2.Recip.le_cSec_of_ne hJ' hJ he).trans fun g hg => hg.1

theorem le_normalizer_Jss {L T : Subgroup G} (hTy : T ≤ centralizer ({y} : Set G))
    (hTL : T ≤ normalizer (L : Set G)) : T ≤ normalizer ((Jss y L : Subgroup G) : Set G) := by
  have key : ∀ q ∈ T, (Jss y L).map (MulAut.conj q).toMonoidHom ≤ Jss y L := by
    intro q hq
    refine Subgroup.map_le_iff_le_comap.2 (iSup_le fun J' => iSup_le fun hJ' => iSup_le fun hle => ?_)
    rw [← Subgroup.map_le_iff_le_comap]
    exact conj_le_Jss hJ' hle (hTy hq) (hTL hq)
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => key q hq ⟨a, ha, rfl⟩, fun ha => ?_⟩
  have := key q⁻¹ (inv_mem hq) ⟨_, ha, rfl⟩
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem pPrimeCoreOf_le_of_normal {N X : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set G)) : pPrimeCoreOf 2 N ≤ pPrimeCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := pPrimeCoreOf 2 N with hM
  have hMX : M ≤ X := (Subgroup.map_subtype_le _).trans hNX
  have hnorm : X ≤ normalizer (M : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (hXN hg)
  have hcop : Nat.Coprime 2 (Nat.card ↥M) := by
    rw [hM, pPrimeCoreOf, Subgroup.card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hnormal : (M.subgroupOf X).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hnorm h.2) a).mp ha
  have hcop' : Nat.Coprime 2 (Nat.card (M.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMX).toEquiv]
  have hle : M.subgroupOf X ≤ pPrimeCore 2 ↥X := le_sSup ⟨hnormal, hcop'⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hMX]
  exact Subgroup.map_mono hle

theorem Jstar_le_normalizer_conj (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hBy : B ≤ centralizer ({y} : Set G)) {b : G} (hb : b ∈ B) :
    Jstar B J ≤ normalizer ((J.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G) := by
  refine iSup₂_le fun b' hb' => ?_
  have h1 := conj_isPCompIn hJ (hBy hb)
  have h2 := conj_isPCompIn hJ (hBy hb')
  by_cases he : J.map (MulAut.conj b').toMonoidHom = J.map (MulAut.conj b).toMonoidHom
  · rw [he]; exact Subgroup.le_normalizer
  · exact (Stage1.Thm2.Recip.le_cSec_of_ne h2 h1 he).trans fun g hg => hg.1

theorem conj_le_Jstar {b : G} (hb : b ∈ B) : J.map (MulAut.conj b).toMonoidHom ≤ Jstar B J :=
  le_iSup₂ (f := fun g (_ : g ∈ B) => J.map (MulAut.conj g).toMonoidHom) b hb

theorem mem_Zstar_Jstar (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hBy : B ≤ centralizer ({y} : Set G)) {z : G} (hzJ : z ∈ J) (hzc : z ∈ cSec J) :
    z ∈ Zstar (Jstar B J) := by
  set X := Jstar B J with hX
  set O := pPrimeCoreOf 2 X with hO
  have hzX : z ∈ X := S3Sec29C.le_Jstar B J hzJ
  have hXO : X ≤ normalizer (O : Set G) := fun g hg =>
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hg)
  let S' : Subgroup G :=
    { carrier := {k | k ∈ X ∧ ⁅k, z⁆ ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haX, ha⟩ ⟨hbX, hb⟩
        refine ⟨mul_mem haX hbX, ?_⟩
        have e : ⁅a * b, z⁆ = (a * ⁅b, z⁆ * a⁻¹) * ⁅a, z⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hXO haX) _).1 hb) ha
      inv_mem' := by
        rintro a ⟨haX, ha⟩
        refine ⟨inv_mem haX, ?_⟩
        have e : ⁅a⁻¹, z⁆ = a⁻¹ * ⁅a, z⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.1 (hXO (inv_mem haX)) _).1 (inv_mem ha) }
  have hle : X ≤ S' := by
    refine iSup₂_le fun b hb => ?_
    intro k hk
    refine ⟨conj_le_Jstar hb hk, ?_⟩
    have hJb := conj_isPCompIn hJ (hBy hb)
    have hcO : pPrimeCoreOf 2 (J.map (MulAut.conj b).toMonoidHom) ≤ O :=
      pPrimeCoreOf_le_of_normal (conj_le_Jstar hb) (Jstar_le_normalizer_conj hJ hBy hb)
    by_cases he : J.map (MulAut.conj b).toMonoidHom = J
    · have hkJ : k ∈ J := he ▸ hk
      have h1 : ⁅k, z⁆ ∈ pPrimeCoreOf 2 J := hzc.2.2 k hkJ
      rw [← he] at h1
      exact hcO h1
    · have hzb : z ∈ cSec (J.map (MulAut.conj b).toMonoidHom) :=
        Stage1.Thm2.Recip.le_cSec_of_ne hJ hJb (Ne.symm he) hzJ
      exact hcO (hzb.2.2 k hk)
  refine Subgroup.mem_inf.2 ⟨hzX, Subgroup.le_normalizer hzX,
    TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer hzX), fun k hk => (hle hk).2⟩

omit [Finite G] in
theorem piC_y_comm (c : CentralizerBar y) : c * piC y y = piC y y * c := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ c
  have hyC : y ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hgy : (g : G) * y = y * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
  rw [piC_of_mem y hyC]
  show proj y g * proj y ⟨y, hyC⟩ = proj y ⟨y, hyC⟩ * proj y g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hgy

theorem commConj_of_not_mem_normalizer (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) {g : G}
    (hg : g ∈ centralizer ({y} : Set G)) (hgN : g ∉ normalizer (J : Set G)) :
    S3Sec29D3.CommConj (S3.imgBar y J) (piC y g) := by
  have hne : J.map (MulAut.conj g).toMonoidHom ≠ J := fun he =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he)
  have hle := Stage1.Thm2.Recip.le_cSec_of_ne (conj_isPCompIn hJ hg) hJ hne
  intro a ha b hb
  obtain ⟨a', ha'J, rfl⟩ := S3.mem_imgBar.1 ha
  obtain ⟨b', hb'J, rfl⟩ := S3.mem_imgBar.1 hb
  have hbC : (b' : G) ∈ centralizer ({y} : Set G) := b'.2
  have hr : g * b' * g⁻¹ ∈ cSec J := hle ⟨b', hb'J, rfl⟩
  have hrC : g * b' * g⁻¹ ∈ centralizer ({y} : Set G) := mul_mem (mul_mem hg hbC) (inv_mem hg)
  have h1 := S3Sec29C.piC_of_mem_cSec hJ hrC hr a' ha'J
  rw [← piC_of_mem y a'.2, ← piC_of_mem y hbC, ← S3Sec29D4.piC_conj hg hbC]
  calc piC y (a' : G) * piC y (g * b' * g⁻¹) =
      (piC y (g * b' * g⁻¹) * piC y a' * (piC y (g * b' * g⁻¹))⁻¹) * piC y (g * b' * g⁻¹) := by
        rw [h1]
    _ = piC y (g * b' * g⁻¹) * piC y a' := by group

theorem isQuasisimple_imgBar (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J) :
    IsQuasisimple ↥(S3.imgBar y J) :=
  (S3Fusion.isComponent_imgBar hJ).1

theorem exists_sl2Data (hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J)
    (hsl : HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd) :
    ∃ z : ↥(S3.imgBar y J), SL2Data ↥(S3.imgBar y J) z := by
  obtain ⟨e⟩ := B1.PilotS5.hat_equiv_imgBar hJ
  obtain ⟨F, hF, hFin, hodd, ⟨e'⟩⟩ := hsl
  exact S3Sec29D1.sl2Data_of_model ⟨F, hF, hFin, hodd, ⟨e.symm.trans e'⟩⟩

end S3Sec29D5

end CFSG.GH74.Generic.BProg.B3

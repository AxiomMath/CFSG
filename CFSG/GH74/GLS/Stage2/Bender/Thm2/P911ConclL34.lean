module

public import CFSG.GH74.Generic.S1.SL2Facts
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic
public import CFSG.GH74.GLS.Stage2.Signalizer.Bridge
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Cross
public import CFSG.GH74.GLS.Stage2.Signalizer.Stmt43E
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.GH74.KGroups.L3EpsOuterLin

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace ConclL34

theorem pCore_eq_center {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hQ : IsQuasisimple Q) (hZ : IsPGroup p ↥(Subgroup.center Q)) :
    pCore p Q = Subgroup.center Q := by
  refine le_antisymm ?_ (le_sSup ⟨inferInstance, hZ⟩)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
      (CFSG.pCore_normal (p := p) (G := Q)) with h | h
  · refine (not_quasisimple_of_pgroup hp hQ ?_).elim
    exact (CFSG.pCore_isPGroup (p := p) (G := Q)).of_equiv
      ((MulEquiv.subgroupCongr h).trans Subgroup.topEquiv)
  · exact h

theorem center_eq_bot {A : Type} [Group A] [IsSimpleGroup A] [Group.IsPerfect A] :
    Subgroup.center A = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative A (Subgroup.center_eq_top_iff.mp h)).elim

theorem false_of_sl2_top {A : Type} [Group A] (hcen : Subgroup.center A = ⊥) {X : Subgroup A}
    (htop : ncl X = ⊤) {q : ℕ} (hq : Odd q) (h : HasSL2Model ↥(ncl X) (fun q' => q' = q)) :
    False := by
  obtain ⟨t, htV, ht2, hu, -⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hq h
  have hsq : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht2, pow_two] at h1
    exact h1
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  have htc : t ∈ Subgroup.center A := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hxV : x ∈ ncl X := htop ▸ Subgroup.mem_top x
    have hxt : x * t * x⁻¹ ∈ ncl X := mul_mem (mul_mem hxV htV) (inv_mem hxV)
    have hxsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    rcases hu _ hxt hxsq with h1 | h1
    · exfalso
      apply ht1
      have : t = x⁻¹ * (x * t * x⁻¹) * x := by group
      rw [this, h1]
      group
    · calc x * t = (x * t * x⁻¹) * x := by group
        _ = t * x := by rw [h1]
  rw [hcen, Subgroup.mem_bot] at htc
  exact ht1 htc

theorem psl3Order_ne_of_odd {q : ℕ} (hq : Odd q) (h3 : 3 ≤ q) :
    Odd87.psl3Order q ≠ 20160 := by
  intro h
  unfold Odd87.psl3Order at h
  have hg : Nat.gcd 3 (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (q - 1))
  have hgpos : 0 < Nat.gcd 3 (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  rcases (show q = 3 ∨ 5 ≤ q by obtain ⟨m, hm⟩ := hq; omega) with rfl | h5
  · norm_num at h
  · have hlt : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) < 20161 * Nat.gcd 3 (q - 1) := by
      rw [← Nat.div_lt_iff_lt_mul hgpos]
      omega
    have h1 : 125 ≤ q ^ 3 := by
      calc 125 = 5 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left h5 3
    have h2 : 24 ≤ q ^ 2 - 1 := by
      have : 25 ≤ q ^ 2 := by
        calc 25 = 5 ^ 2 := by norm_num
          _ ≤ q ^ 2 := Nat.pow_le_pow_left h5 2
      omega
    have h4 : 124 ≤ q ^ 3 - 1 := by omega
    have h6 : 125 * 24 * 124 ≤ q ^ 3 * (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h4
    omega

theorem false_of_lie_top {A : Type} [Group A] [Finite A] [IsSimpleGroup A] [Group.IsPerfect A]
    (hcard : Nat.card A = 20160) {X : Subgroup A} (htop : ncl X = ⊤) {p n : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) (hn : 1 ≤ n)
    (h : LieModel (↥(ncl X) ⧸ Subgroup.center ↥(ncl X)) .PSL 3 p n) : False := by
  let e : ↥(ncl X) ≃* A := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have : IsSimpleGroup ↥(ncl X) := e.isSimpleGroup
  have : Group.IsPerfect ↥(ncl X) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcenH : Subgroup.center ↥(ncl X) = ⊥ := center_eq_bot
  obtain ⟨K, _, _, hK, ⟨e'⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel h
  have hcardH : Nat.card ↥(ncl X) = 20160 := (Nat.card_congr e.toEquiv).trans hcard
  have hmul := (Subgroup.center ↥(ncl X)).card_eq_card_quotient_mul_card_subgroup
  have hc1 : Nat.card ↥(Subgroup.center ↥(ncl X)) = 1 := by
    rw [hcenH]
    exact Subgroup.card_bot
  rw [hc1, mul_one, hcardH, Nat.card_congr e'.toEquiv, Odd87.card_projectiveSL_three, hK] at hmul
  have hodd : Odd (p ^ n) := (hp.odd_of_ne_two hpodd).pow
  have h3 : 3 ≤ p ^ n := by
    have h2' : 3 ≤ p := by
      have := hp.two_le
      omega
    exact h2'.trans (Nat.le_self_pow (by omega) p)
  exact psl3Order_ne_of_odd hodd h3 hmul.symm

theorem not_isPerfect_pgl3 {F : Type} [Field F] [Finite F] (hF4 : Nat.card F = 4) :
    ¬ Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 3) F) := by
  classical
  intro hperf
  have : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card Fˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hF4]
  have hcube : ∀ u : Fˣ, u ^ 3 = 1 := fun u => by
    rw [← hcard]
    exact pow_card_eq_one'
  let f : Matrix.ProjGenLinGroup (Fin 3) F →* Fˣ :=
    Matrix.ProjGenLinGroup.lift (Matrix.GeneralLinearGroup.det) (by
      ext u
      simp [hcube])
  have hker : commutator (Matrix.ProjGenLinGroup (Fin 3) F) ≤ f.ker :=
    Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp hperf] at hker
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; norm_num)
  obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
  obtain ⟨g, hg⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 3) (R := F) u
  apply hu
  have h1 := hker (Subgroup.mem_top (Matrix.ProjGenLinGroup.mk g))
  rw [MonoidHom.mem_ker] at h1
  rw [← hg]
  exact h1

theorem false_of_pgl3_top {A : Type} [Group A] [Group.IsPerfect A] {X : Subgroup A}
    (htop : ncl X = ⊤) (h : IsPGL3Four ↥(ncl X)) : False := by
  obtain ⟨F, _, _, hF4, ⟨e'⟩⟩ := h
  let e : ↥(ncl X) ≃* A := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hperf : Group.IsPerfect (Matrix.ProjGenLinGroup (Fin 3) F) :=
    Group.IsPerfect.ofSurjective (f := (e.symm.trans e').toMonoidHom)
      (e.symm.trans e').surjective
  exact not_isPerfect_pgl3 hF4 hperf

theorem false_of_concl_simple {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    [Group.IsPerfect A] (hcard : Nat.card A = 20160) {k : Kind} {z : A} {p : ℕ} (hp : p.Prime)
    (hpodd : p ≠ 2) {X : Subgroup A} (hX : X ≠ ⊥) (hconc : Concl43E k z p X) : False := by
  have htop : ncl X = ⊤ := by
    have : (ncl X).Normal := Subgroup.normalClosure_normal
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ncl X) with h | h
    · exact absurd (le_bot_iff.mp (h ▸ (Subgroup.le_normalClosure : X ≤ ncl X))) hX
    · exact h
  rcases hconc with ⟨n, -, hsl, -⟩ | ⟨n, hn, hlie, -⟩ | ⟨-, -, hpgl, -⟩ | ⟨hsl, -⟩
  · exact false_of_sl2_top center_eq_bot htop (hp.odd_of_ne_two hpodd).pow hsl
  · exact false_of_lie_top hcard htop hp hpodd hn hlie
  · exact false_of_pgl3_top htop hpgl
  · exact false_of_sl2_top center_eq_bot htop (by decide : Odd 5) hsl

end ConclL34

theorem false_of_concl43E_L34 {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {p : ℕ}
    {J₁ W₁ : Subgroup G} (hp : p.Prime) (hpodd : p ≠ 2) (hz : z ∈ J₁)
    (hJ : IsQuasisimple ↥J₁) (hL : LieModel (↥J₁ ⧸ Subgroup.center ↥J₁) .PSL 3 2 2)
    (hZp : IsPGroup p ↥(Subgroup.center ↥J₁)) (hW1 : W₁ ≤ J₁) (hW0 : W₁ ≠ ⊥)
    (hWp : IsPGroup p ↥W₁) (hWz : ⁅W₁, zpowers z⁆ = W₁)
    (hconc : Concl43E k (zSec z J₁ hz (pCore p ↥J₁)) p (xBar p J₁ W₁)) : False := by
  have _ := hWp
  have hZ' : pCore p ↥J₁ = Subgroup.center ↥J₁ := ConclL34.pCore_eq_center hp hJ hZp
  let e : Sec J₁ (pCore p ↥J₁) ≃* (↥J₁ ⧸ Subgroup.center ↥J₁) :=
    QuotientGroup.quotientMulEquivOfEq hZ'
  have := hJ.1
  have : IsSimpleGroup (↥J₁ ⧸ Subgroup.center ↥J₁) := hJ.2.1
  have : IsSimpleGroup (Sec J₁ (pCore p ↥J₁)) := e.isSimpleGroup
  have hcard : Nat.card (Sec J₁ (pCore p ↥J₁)) = 20160 := by
    obtain ⟨K, _, _, hK, ⟨e'⟩⟩ :=
      CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hL
    rw [Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, Odd87.card_projectiveSL_three, hK]
    norm_num [Odd87.psl3Order]
  have hX : xBar p J₁ W₁ ≠ ⊥ := by
    intro hbot
    apply hW0
    rw [← hWz]
    have hle : W₁.subgroupOf J₁ ≤ pCore p ↥J₁ := by
      have h1 := hbot
      unfold xBar at h1
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h1
      exact h1
    rw [hZ'] at hle
    rw [eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun w hw g hg => ?_
    have hgJ : g ∈ J₁ := (Subgroup.zpowers_le.mpr hz) hg
    have hwc : (⟨w, hW1 hw⟩ : ↥J₁) ∈ Subgroup.center ↥J₁ :=
      hle (Subgroup.mem_subgroupOf.mpr hw)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨g, hgJ⟩)).symm
  exact ConclL34.false_of_concl_simple hcard hp hpodd hX hconc

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

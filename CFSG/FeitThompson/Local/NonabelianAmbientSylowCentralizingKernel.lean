module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.NonregularPlaneLineUniqueCentralizer
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.OddFrobeniusComplementCentralizesFitting

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson

universe u

theorem FNI_nonabelian_ambient_sylow_centralizing_kernel
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_unique_nonregular_line.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_complement_normalizer.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_core_disjoint.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u}) :
    _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_ambient_sylow_centralizing_kernel.{u} := by
  intro G _ _ hG p M A E hOSP hSC hAE hnonab P hP hAP
  have hp : p.Prime := hOSP.prime
  have hfp := Fact.mk hp
  have _inst : Fintype G := Fintype.ofFinite G
  have hsemi := hSC.isInternalSemidirectProduct
  have hamb : CFSG.FeitThompson.Prep03.IsAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG02 : CFSG.FeitThompson.IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hSbot : sigmaCore M ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hG02 M hOSP.isCoatom).2
  obtain ⟨A₀, hA₀A, hA₀card, hA₀cent, hline, hA₀eq, -, -⟩ :=
    h₂ G hG p M A E hOSP hSC hAE hnonab
  have hPcard : Nat.card ↥P = p ^ (Nat.card ↥E).factorization p :=
    (_root_.CFSG.FeitThompson.isSylowIn_iff_natCard hp hP.le).1 hP
  obtain ⟨Syl, hPR⟩ := (IsPGroup.of_card hPcard).exists_le_sylow
  set R : Subgroup G := (Syl : Subgroup G) with hRdef
  have hRtop : Nat.card ↥R = p ^ (Nat.card G).factorization p := Syl.card_eq_multiplicity
  have hRp : IsPGroup p ↥R := IsPGroup.of_card hRtop
  have hsetup : CFSG.FeitThompson.Prep03.IsPlaneSetup G p M A E :=
    ⟨hamb, hOSP.isCoatom, hp, hOSP.notMem_sigmaPrimes, hOSP.le, hOSP.isElementaryAbelianPlane,
      ⟨hsemi.left_le, hsemi.right_le, hsemi.le_normalizer, hsemi.sup_eq, hsemi.inf_eq_bot⟩, hAE⟩
  obtain ⟨Q, hQ, hQnc⟩ := hnonab
  have hnonab' : ∃ Q : Subgroup G,
      CFSG.FeitThompson.Prep03.IsSylowTop p Q ∧
        ¬ IsMulCommutative ↥Q :=
    ⟨Q, (_root_.CFSG.FeitThompson.isSylowSubgroup_iff_natCard hp).1 hQ, hQnc⟩
  obtain ⟨hPcomm, hRnc, hPltR, hRM, hCRA, -⟩ :=
    FNI_nonabelian_ambient_plane_centralizer h₃ h₅ h₆ G hamb p M A E P R hsetup hnonab'
      ⟨hP.le, hPcard⟩ hAP hRtop hPR
  have hCRA' : R ⊓ centralizer (A : Set G) = P := hCRA
  obtain ⟨-, hAmax, -, -⟩ := h₅ G hG p M A hOSP
  have hAcard : Nat.card ↥A = p ^ 2 := hOSP.isElementaryAbelianPlane.natCard'
  have hpodd : Odd p :=
    odd_of_prime_of_dvd_odd hp hG.odd_natCard
      (dvd_trans (hAcard ▸ dvd_pow_self p two_ne_zero) (Subgroup.card_subgroup_dvd_card A))
  obtain ⟨Z, hZset, hZA, hZcard, ⟨Y, hYle, hYcyc, hZY, hYdecomp⟩, -⟩ :=
    FPL_global_maximal_plane_geometry h₆ G hG6 p hp hpodd A R
      hOSP.isElementaryAbelianPlane (forall_not_nonempty_mulEquiv_of_maximal hAmax)
      ⟨_, hRtop⟩ (hAP.trans hPR) hRnc
      {z | z ∈ R ⊓ centralizer (R : Set G) ∧ z ^ p = 1} rfl
  have hCA₀M : centralizer (A₀ : Set G) ≤ M :=
    (FNI_nonregular_plane_line_unique_centralizer h₃ h₄ G hG p M A E A₀ hOSP hSC hAE
      (hA₀A.trans hAE) hA₀card (by rw [hA₀cent]; exact hSbot)).1.le
  have hZR : Z ≤ R ⊓ centralizer (R : Set G) := by
    intro z hz
    have hz' : z ∈ ({z | z ∈ R ⊓ centralizer (R : Set G) ∧ z ^ p = 1} : Set G) := hZset ▸ hz
    exact hz'.1
  have hZne : A₀ ≠ Z := by
    rintro rfl
    have hRC : R ≤ centralizer (A₀ : Set G) := fun r hr =>
      mem_centralizer_iff.2 fun z hz => ((mem_centralizer_iff.1 (hZR hz).2) r hr).symm
    have hRle : R ≤ P := hRM ▸ le_inf le_rfl (hRC.trans hCA₀M)
    exact absurd (le_antisymm hRle hPR) hPltR.ne'
  obtain ⟨hsup, hinf, hcomm⟩ := hYdecomp A₀ hA₀A hA₀card hZne
  have hsupP : A₀ ⊔ Y = P := by rw [hsup, hCRA']
  have hYP : Y ≤ P := hsupP ▸ le_sup_right
  have hcomm' : ∀ x ∈ A₀, ∀ y ∈ Y, Commute x y := fun x hx y hy =>
    (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm hx) y hy).symm
  have hprod : IsInternalDirectProduct P A₀ Y :=
    IsInternalDirectProduct.mk' (by rw [← hsupP]; exact coe_sup_eq_mul_of_commute hcomm')
      hinf hcomm'
  have hYbot : Y ≠ ⊥ := by
    rintro rfl
    rw [le_bot_iff] at hZY
    rw [hZY, Subgroup.card_bot] at hZcard
    exact hp.one_lt.ne hZcard
  have hYcent : Y ⊓ centralizer (sigmaCore M : Set G) = ⊥ := by
    by_contra hC
    have hYcyc' : IsCyclic ↥Y := hYcyc
    have hCcyc : IsCyclic ↥(Y ⊓ centralizer (sigmaCore M : Set G)) :=
      Subgroup.isCyclic_of_le (H' := Y) inf_le_left
    have hCp : IsPGroup p ↥(Y ⊓ centralizer (sigmaCore M : Set G)) :=
      hRp.to_le (inf_le_left.trans (hYP.trans hPR))
    obtain ⟨t, htC, htord, -⟩ :=
      exists_orderOf_eq_prime_of_isCyclic_of_isPGroup hp hCcyc hCp hC
    have hWcard : Nat.card ↥(zpowers t) = p := by rw [Nat.card_zpowers, htord]
    have hWY : zpowers t ≤ Y := zpowers_le.2 htC.1
    have hZeqW : Z = zpowers t :=
      eq_of_le_of_natCard_eq_of_isCyclic (A := Y) hZY hWY (by rw [hZcard, hWcard])
    have hZC : Z ≤ centralizer (sigmaCore M : Set G) := by
      rw [hZeqW]; exact zpowers_le.2 htC.2
    have hSCle : sigmaCore M ≤ centralizer (Z : Set G) := fun s hs =>
      mem_centralizer_iff.2 fun z hz => ((mem_centralizer_iff.1 (hZC hz)) s hs).symm
    have hcon := (hline Z (hZA.trans hAE) hZcard (Ne.symm hZne)).1
    rw [inf_eq_left.2 hSCle] at hcon
    exact hSbot hcon
  refine ⟨⟨Y, hYbot, hYcyc, ?_, hYcent⟩, ?_⟩
  · rw [← hA₀eq]; exact hprod
  · rw [← hA₀eq]
    refine le_antisymm (fun x hx => ?_) (le_inf (hA₀A.trans hAP) ?_)
    · obtain ⟨a, ha, y, hy, rfl⟩ := Set.mem_mul.1 (hprod.coe_eq_mul ▸ (hx.1 : x ∈ (P : Set G)))
      have hacent : a ∈ centralizer (sigmaCore M : Set G) := by
        have hle : A₀ ≤ centralizer (sigmaCore M : Set G) := hA₀eq ▸ inf_le_right
        exact hle ha
      have hycent : y ∈ centralizer (sigmaCore M : Set G) := by
        have h' : a⁻¹ * (a * y) ∈ centralizer (sigmaCore M : Set G) :=
          mul_mem (inv_mem hacent) hx.2
        simpa using h'
      have hyb : y ∈ (⊥ : Subgroup G) := hYcent ▸ ⟨hy, hycent⟩
      rw [Subgroup.mem_bot] at hyb
      simpa [hyb] using ha
    · rw [hA₀eq]; exact inf_le_right

end

end CFSG.FeitThompson.Proofs

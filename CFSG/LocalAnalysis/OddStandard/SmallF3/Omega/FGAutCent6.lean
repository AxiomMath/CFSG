module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGAutCentConv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxIV
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGCplxN2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGEichlerGlue
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4Split
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4IV
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK4III
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MK4
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MN2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MShapes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G]

theorem fg_centModel_six (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1 ∨ quadSign Q = -1) (h2 : 2 ≤ Module.finrank (ZMod 3) V)
    {x : ProjSim Q} (hx1 : x ≠ 1) (hx2 : x * x = 1) {J : Subgroup ↥(omegaProj hQ)}
    (hJ : IsComponentIn J (ffFix hQ h2 x)) {A : Subgroup (ProjSim Q)}
    (hAJ : ∀ a ∈ A, ∀ j ∈ J, projSimAct Q a (j : ProjOrth Q) = (j : ProjOrth Q))
    (hyp62 : quadSign Q = 1 → ∀ a ∈ A, SimInGStar a → SimInOmegaStar hQ a) :
    FGCentModel hQ J A := by
  by_cases hG : SimInGStar x
  · obtain ⟨y, hyx⟩ := hG
    have hy2 : y * y = 1 :=
      projOrthToProjSim_injective (by rw [map_mul, hyx, hx2, map_one])
    have hy1 : y ≠ 1 := fun h => hx1 (by rw [← hyx, h, map_one])
    rcases hsgn with hs | hs
    · have hnot : ¬ (Even (Module.finrank (ZMod 3) V) ∧
          quadSign Q = (-1) ^ (Module.finrank (ZMod 3) V / 2)) := by
        rintro ⟨-, hq⟩
        rw [hdim, hs] at hq
        exact absurd hq (by decide)
      obtain ⟨t, htt, hty⟩ := exists_lift_of_mul_self_eq_one hQ hnot hy2
      exact fg_centModel_of_lift hQ hdim h2 hx1 htt (by rw [hty, hyx]) hJ hAJ hyp62
    · obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
      have hyt : toProj Q t = y := ht
      have hg1 : t * t ∈ piGroup Q := by
        apply (QuotientGroup.eq_one_iff (t * t)).mp
        change toProj Q (t * t) = 1
        rw [map_mul, hyt]
        exact hy2
      rcases mem_piGroup_iff.mp hg1 with htt | htt
      · exact fg_centModel_of_lift hQ hdim h2 hx1 htt (by rw [hyt, hyx]) hJ hAJ hyp62
      · have hKN2 : KN2 x := ⟨y, hyx, hy1, hy2, t, htt, hyt⟩
        have hLM := ff6m_N2_layerModel hQ hdim hs hKN2
        have hxeq : x = QuotientGroup.mk (orthToSim Q t) := by
          rw [← hyx, ← hyt]
          rfl
        subst hxeq
        have hsh : ∀ (E : Type) [Group E], LieModel E .PSU 3 3 1 →
            IsSimpleGroup E ∧ ∃ a b : E, a * b ≠ b * a :=
          fun E _ hE => ff_simple_of_lieModel_psu3 hE
        rcases fg_cent_kn2 hQ hdim hs h2 htt hLM hJ hAJ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl ⟨hs, fg_lieModel_of_layerModel hsh hLM hJ, h⟩))
  · rcases hsgn with hs | hs
    · obtain ⟨ρ, rfl, hρ, hρρ⟩ := ff_K4_split hQ hdim hs hx2 hG
      rcases hρρ with hρρ | hρρ
      · exact Or.inl (fg_cent_typeIII hQ hdim h2 hρ hρρ (ff_K4III_layerModel hQ hdim hs hρ hρρ)
          hJ hAJ)
      · exact Or.inl (fg_cent_typeIV hQ hdim h2 hρ hρρ (ff_K4IV_layerModel hQ hdim hs hρ hρρ)
          hJ hAJ)
    · have hLM := ff6m_K4_layerModel hQ hdim hs hx2 hG
      obtain ⟨ρ, rfl, hρ, hρρ⟩ := ff6m_K4_split hQ hdim hs hx2 hG
      exact Or.inl (fg_cent_typeIV hQ hdim h2 hρ hρρ hLM hJ hAJ)

theorem fg_aut_cent_six_of_model [Finite G] {L : Subgroup G} (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : (quadSign Q = 1 ∧ IsOm6P L) ∨ (quadSign Q = -1 ∧ IsOm6M L))
    (hH : IsOm6P L → Hyp62At L) (e : ↥L ⧸ Subgroup.center ↥L ≃* omegaProj hQ)
    (hodd : Odd (Nat.card (Subgroup.center ↥L))) (hLp : commutator ↥L = ⊤) {x : G}
    (hx2 : x * x = 1) (hxN : x ∈ normalizer (L : Set G)) {X : Subgroup G}
    (hX : IsComponentIn X (L ⊓ centralizer ({x} : Set G))) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    (centralizer (L : Set G)).relIndex R ≤ 2 ∨
      (IsL29 X ∧ IsOm6M L ∧ QuotEquivTo R (R ⊓ centralizer (L : Set G))
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
      (IsU33 X ∧ IsOm6M L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) ∨
      (IsL29 X ∧ IsOm6P L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) := by
  have hsgn' : quadSign Q = 1 ∨ quadSign Q = -1 :=
    hsgn.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have h : (Module.finrank (ZMod 3) V = 5 ∧ quadSign Q = 1) ∨
      (Module.finrank (ZMod 3) V = 6 ∧ (quadSign Q = 1 ∨ quadSign Q = -1)) := Or.inr ⟨hdim, hsgn'⟩
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hRN : R ≤ normalizer (L : Set G) := hR.trans inf_le_left
  have hRC : R ≤ centralizer (X : Set G) := hR.trans inf_le_right
  have hXL : X ≤ L := hX.1.trans inf_le_left
  by_cases hx1 : ffTheta hQ h e ⟨x, hxN⟩ = 1
  · have hxC : x ∈ centralizer (L : Set G) :=
      (ffTheta_eq_one_iff hQ h e hLp ⟨x, hxN⟩).mp hx1
    have hLle : L ≤ centralizer ({x} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC l hl)
    have hX' : IsComponentIn X L := by
      have := hX
      rwa [inf_eq_left.mpr hLle] at this
    have hLq : CFSG.IsQuasisimple ↥L := hsgn.elim (fun hp => hp.2.1) (fun hm => hm.2.1)
    have hXL' : X = L := hX'.eq_of_isQuasisimple hLq
    rw [hXL'] at hRC
    left
    rw [Subgroup.relIndex_eq_one.mpr hRC]
    norm_num
  · have hθ2 : ffTheta hQ h e ⟨x, hxN⟩ * ffTheta hQ h e ⟨x, hxN⟩ = 1 := by
      rw [← map_mul]
      have hxx : (⟨x, hxN⟩ : ↥(normalizer (L : Set G))) * ⟨x, hxN⟩ = 1 := Subtype.ext hx2
      rw [hxx, map_one]
    have hJ := fg_isComponentIn_rho hQ h e h2 hodd hx2 hxN hX
    have hAJ := fg_thetaR_centralizes hQ h e hR
    have hyp62 : quadSign Q = 1 → ∀ a ∈ (fgThetaR hQ h e hRN).range, SimInGStar a →
        SimInOmegaStar hQ a := by
      intro hs a ha hGa
      have hLP : IsOm6P L :=
        hsgn.elim (fun hp => hp.2) (fun hm => absurd (hm.1.symm.trans hs) (by decide))
      obtain ⟨s, rfl⟩ := ha
      exact fg_simInOmegaStar_of_hyp62 hLP (hH hLP) hQ e hdim hs
        (ffTheta_induces hQ h e (Subgroup.inclusion hRN s)) hGa
    exact fg_aut_cent_of_model hQ h e hodd hLp hsgn hXL hRN
      (fg_centModel_six hQ hdim hsgn' h2 hx1 hθ2 hJ hAJ hyp62)

theorem fg_aut_cent_om6 [Finite G] {L : Subgroup G} (hL : IsOm6P L ∨ IsOm6M L)
    (hH : IsOm6P L → Hyp62At L) {x : G} (hx : orderOf x = 2)
    (hxN : x ∈ normalizer (L : Set G)) {X : Subgroup G}
    (hX : IsComponentIn X (L ⊓ centralizer ({x} : Set G))) {R : Subgroup G}
    (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    (centralizer (L : Set G)).relIndex R ≤ 2 ∨
      (IsL29 X ∧ IsOm6M L ∧ QuotEquivTo R (R ⊓ centralizer (L : Set G))
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∨
      (IsU33 X ∧ IsOm6M L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) ∨
      (IsL29 X ∧ IsOm6P L ∧
        QuotEquivTo R (R ⊓ centralizer (L : Set G)) (Multiplicative (ZMod 4))) := by
  have hx2 : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  rcases hL with hP | hM
  · obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_plus hP
    have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
      rw [ff_center_eq_oddCore_six_plus hP]
      exact ff_odd_card_oddCore ↥L
    exact fg_aut_cent_six_of_model hQ hdim (Or.inl ⟨hsgn, hP⟩) hH e hodd
      hP.1.1.commutator_eq_top hx2 hxN hX hR
  · obtain ⟨V, _, _, _, Q, hQ, hdim, hsgn, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hM
    have hodd : Odd (Nat.card (Subgroup.center ↥L)) := by
      rw [ff_center_eq_oddCore_six_minus hM]
      exact ff_odd_card_oddCore ↥L
    exact fg_aut_cent_six_of_model hQ hdim (Or.inr ⟨hsgn, hM⟩) hH e hodd
      hM.1.1.commutator_eq_top hx2 hxN hX hR

end CFSG.OddStandard.SmallF3.Omega

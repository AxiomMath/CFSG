module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance

section Twins

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_twin_tq (hc : P23Cfg n Y R S t K' W u e g) :
    tightCore R ∈ tqMembers3 (Om R) e ∧ K' ∈ tqMembers3 (Om R) e := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  have hs : CFSG.ClassicalInvolution.Q8P.Asc77.Hyp23Setting (Om R) (tightCore R) K' t :=
    ⟨CFSG.ClassicalInvolution.Q8P.ascStand_of_twinCore hC, hc.std.perp.disc, hz, hc.std.hK',
      hc.std.hne, hperp⟩
  obtain ⟨S₀, R₀, R', hWS, hR₀, hR', hRS, hR'S⟩ :=
    CFSG.ClassicalInvolution.Q8P.Asc77.T7D.exists_sylow_frame hs hc.std.hW hc.std.htW
  have hNe := normalizer_le_centralizer_e hc.data
  refine ⟨?_, ?_⟩
  · have hRD : R₀ ∈ DSet (Om R) W :=
      Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK hR₀) hRS
    have hRN : R₀ ≤ Subgroup.normalizer (W : Set Y) := hRD.2
    exact ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₀, hR₀, hRN.trans hNe⟩⟩
  · have hK'Ω : K' ∈ Om R := hc.std.hK'.1
    have hRD : R' ∈ DSet (Om R) W :=
      Q3CL.Thompson.mem_DSet_of_le_sylow hΩ hc.std.hW hWS (mem_RSet_of_isSylow2In hK'Ω hR') hR'S
    have hRN : R' ≤ Subgroup.normalizer (W : Set Y) := hRD.2
    exact ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK'Ω ⟨R', hR', hRN.trans hNe⟩⟩

namespace F7I

theorem conj_cent_of_perm {Q : Type} [Group Q] {A B : Subgroup Q} {eb : Q}
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb) (ρ : Q) :
    (∀ x ∈ A, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) ∧
      (∀ x ∈ B, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) := by
  have key : ∀ x : Q, (ρ⁻¹ * x * ρ ∈ A ∨ ρ⁻¹ * x * ρ ∈ B) →
      ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹) := by
    intro x hx
    have h1 : eb * (ρ⁻¹ * x * ρ) = (ρ⁻¹ * x * ρ) * eb := by
      rcases hx with hx | hx
      · exact heA _ hx
      · exact heB _ hx
    calc ρ * eb * ρ⁻¹ * x = ρ * (eb * (ρ⁻¹ * x * ρ)) * ρ⁻¹ := by group
      _ = ρ * ((ρ⁻¹ * x * ρ) * eb) * ρ⁻¹ := by rw [h1]
      _ = x * (ρ * eb * ρ⁻¹) := by group
  have hmem : ∀ (H : Subgroup Q) (x : Q), x ∈ H → ρ⁻¹ * x * ρ ∈ conjSub ρ⁻¹ H := by
    intro H x hx
    rw [mem_conjSub_iff]
    have e : ρ⁻¹⁻¹ * (ρ⁻¹ * x * ρ) * ρ⁻¹ = x := by group
    rw [e]
    exact hx
  constructor
  · intro x hx
    apply key
    rcases hperm ρ⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
    · left; rw [← h1]; exact hmem A x hx
    · right; rw [← h1]; exact hmem A x hx
  · intro x hx
    apply key
    rcases hperm ρ⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
    · right; rw [← h1]; exact hmem B x hx
    · left; rw [← h1]; exact hmem B x hx

end F7I

theorem comm_clause_of_bar {J J' : Subgroup Y} {t : Y}
    (hJ : J ≤ Subgroup.centralizer ({t} : Set Y)) (hJ' : J' ≤ Subgroup.centralizer ({t} : Set Y))
    {x : Y} (hx : x ∈ Subgroup.centralizer ({t} : Set Y))
    (h1 : ∀ a ∈ (J.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
        (F7I.piC (Subgroup.centralizer ({t} : Set Y))),
      F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨x, hx⟩ * a =
        a * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨x, hx⟩)
    (h2 : ∀ a ∈ (J'.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
        (F7I.piC (Subgroup.centralizer ({t} : Set Y))),
      F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨x, hx⟩ * a =
        a * F7I.piC (Subgroup.centralizer ({t} : Set Y)) ⟨x, hx⟩) :
    ∀ l ∈ J ⊔ J', x * l * x⁻¹ * l⁻¹ ∈ oddCoreIn (Subgroup.centralizer ({t} : Set Y)) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  let H : Subgroup Y := ((Subgroup.centralizer
    ({F7I.piC C ⟨x, hx⟩} : Set (↥C ⧸ classicalInvolutionOddCore ↥C))).comap (F7I.piC C)).map
      C.subtype
  have hH : ∀ {L : Subgroup Y}, L ≤ C →
      (∀ a ∈ (L.subgroupOf C).map (F7I.piC C), F7I.piC C ⟨x, hx⟩ * a = a * F7I.piC C ⟨x, hx⟩) →
      L ≤ H := by
    intro L hLC hL l hl
    refine ⟨⟨l, hLC hl⟩, ?_, rfl⟩
    show F7I.piC C ⟨l, hLC hl⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hL _ ⟨⟨l, hLC hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩).symm
  intro l hl
  obtain ⟨l', hl', rfl⟩ := sup_le (hH hJ h1) (hH hJ' h2) hl
  have hcomm : F7I.piC C l' * F7I.piC C ⟨x, hx⟩ = F7I.piC C ⟨x, hx⟩ * F7I.piC C l' :=
    Subgroup.mem_centralizer_singleton_iff.mp hl'
  have h3 : F7I.piC C (⟨x, hx⟩ * l' * ⟨x, hx⟩⁻¹ * l'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hcomm]
    group
  exact (F7I.piC_eq_one_iff _).mp h3

theorem ABar_cent_twins (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ q ∈ p23ABar t 1 e,
      (∀ a ∈ ((tightCore R).subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
          (F7I.piC (Subgroup.centralizer ({t} : Set Y))), q * a = a * q) ∧
      (∀ a ∈ (K'.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map
          (F7I.piC (Subgroup.centralizer ({t} : Set Y))), q * a = a * q) := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  obtain ⟨-, -, -, -, -, -, -, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) = (K'.subgroupOf C).map (F7I.piC C)) ∨
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  have hle : p23ABar t 1 e ≤ Subgroup.centralizer ((A : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ∪
      (B : Set (↥C ⧸ classicalInvolutionOddCore ↥C))) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨c, hcC, hx⟩, rfl⟩
    have ex : x = ⟨c, hcC⟩ * ⟨e, heC⟩ * ⟨c, hcC⟩⁻¹ := Subtype.ext (by rw [hx, one_mul]; rfl)
    have hcent := F7I.conj_cent_of_perm hperm heA heB (F7I.piC C ⟨c, hcC⟩)
    have hxq : ((x : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) = F7I.piC C ⟨c, hcC⟩ *
        F7I.piC C ⟨e, heC⟩ * (F7I.piC C ⟨c, hcC⟩)⁻¹ := by
      show F7I.piC C x = _
      rw [ex]
      simp only [map_mul, map_inv]
    show _ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro a (ha | hb)
    · rw [hxq]; exact (hcent.1 a ha).symm
    · rw [hxq]; exact (hcent.2 a hb).symm
  intro q hq
  have := Subgroup.mem_centralizer_iff.mp (hle hq)
  exact ⟨fun a ha => (this a (Or.inl ha)).symm, fun a hb => (this a (Or.inr hb)).symm⟩

end Twins

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

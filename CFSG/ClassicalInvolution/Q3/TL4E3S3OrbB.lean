module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3Orb
public import CFSG.ClassicalInvolution.Q3.TL4E3OneOrbitC
public import CFSG.ClassicalInvolution.Q3.TL4Conn264B
public import CFSG.ClassicalInvolution.Q3.TL4E3S3OrbA

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement

section Cit3

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J : Subgroup Y} {u : Y}

theorem E3Frame.exists_conj_edge' (hF : E3Frame n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    ∃ g : Y, conjSub g J = L ∧ conjSub g (tightCore R) = J ∧ g * t * g⁻¹ = u := by
  obtain ⟨g', hg'K, hg'J, hgt, -⟩ := hF.exists_swap'
  obtain ⟨x, hx, hxL⟩ := hLπ
  have hxC := hF.nbrGen_le_centralizer hx
  refine ⟨x * g', ?_, ?_, ?_⟩
  · rw [conjSub_mul, hg'J, hxL]
  · rw [conjSub_mul, hg'K, hF.conjSub_J_of_mem_centralizer hxC]
  · calc x * g' * t * (x * g')⁻¹ = x * (g' * t * g'⁻¹) * x⁻¹ := by group
      _ = x * u * x⁻¹ := by rw [hgt]
      _ = u := by rw [Subgroup.mem_centralizer_singleton_iff.mp hxC]; group

theorem E3Frame.orbOf_mem_maxOrbs_of_mem (hF : E3Frame n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R)) :
    orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J ∈
      maxOrbs (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L := by
  obtain ⟨g, hgJ, hgK, -⟩ := hF.exists_conj_edge' hLπ
  have h1 := isMaxOrb_conj hF.graphFam hF.orbOf_J_mem_maxOrbs g
  rw [← orbOf_conj hF.graphFam.graph J (tightCore R) g, hgJ, hgK] at h1
  exact h1

theorem E3Frame.exists_conj_of_mem_orbOf_L (hF : E3Frame n R S t J u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    {M : Subgroup Y} (hM : M ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) L J) :
    ∃ l ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J, conjSub l J = M :=
  transitive_of_maxOrb hF.graphFam (hF.orbOf_mem_maxOrbs_of_mem hLπ) J (mem_orbOf_self L J) M hM

theorem E3Frame.tightInO2_secT_of_orbQ' (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (huX : u ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)
    (h : TightInO2 (QuotientGroup.mk'
      (classicalInvolutionOddCore ↥(E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J))
      (⟨u, huX⟩ : ↥(E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J)))) :
    TightInO2 (E3.secT htu ht) := by
  classical
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  set C := Subgroup.centralizer ({u} : Set Y) with hC
  set Xh := E3.orbGen Ω L J with hXhdef
  have hc : ConjInvariant Ω := hF.large.datum.hypOmegaGen.conjInvariant
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  obtain ⟨g, hgJ, hgK, hgt⟩ := hF.exists_conj_edge' hLπ
  have hXg : conjSub g (E3.orbGen Ω J (tightCore R)) = Xh := by
    rw [← E3.orbGen_conj hc hJΩ g, hgJ, hgK]
  have hmem : ∀ x : ↥(secH R u), g * ((x : C) : Y) * g⁻¹ ∈ Xh := by
    intro x
    have h1 : ((x : C) : Y) ∈ E3.orbGen Ω J (tightCore R) :=
      Subgroup.mem_subgroupOf.mp (hF.secH_eq_orbGen.le x.2)
    rw [← hXg]
    exact conj_mem_conjSub h1
  let ψ : ↥(secH R u) →* ↥Xh :=
    { toFun := fun x => ⟨g * ((x : C) : Y) * g⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show g * (((x * y : ↥(secH R u)) : C) : Y) * g⁻¹ =
          (g * ((x : C) : Y) * g⁻¹) * (g * ((y : C) : Y) * g⁻¹)
        simp only [Subgroup.coe_mul]
        group) }
  have hψ : Function.Injective ψ := by
    intro x y hxy
    have h1 : g * ((x : C) : Y) * g⁻¹ = g * ((y : C) : Y) * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext (mul_left_cancel (mul_right_cancel h1)))
  let f₂ : ↥(secH R u) →* ↥Xh ⧸ classicalInvolutionOddCore ↥Xh :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Xh)).comp ψ
  have hker : Odd (Nat.card f₂.ker) := by
    have hle : f₂.ker.map ψ ≤ classicalInvolutionOddCore ↥Xh := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hx)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective hψ] at h1
    exact Odd.of_dvd_nat (CFSG.ComponentClassification.OddCore.odd_card _) h1
  have hC₂ : classicalInvolutionOddCore (SecQ R u) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree _
  have hft : f₂ ⟨⟨t, htu⟩, ht⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Xh) (⟨u, huX⟩ : ↥Xh) := by
    show QuotientGroup.mk' _ (ψ ⟨⟨t, htu⟩, ht⟩) = _
    congr 1
    exact Subtype.ext hgt
  have h' : TightInO2 (f₂ ⟨⟨t, htu⟩, ht⟩) := by
    rw [hft]
    exact h
  exact E3.tightInO2_of_hom f₂ (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) hker hC₂ h'

theorem E3Frame.not_secInO2' (hF : E3Frame n R S t J u)
    (htu : t ∈ Subgroup.centralizer ({u} : Set Y))
    (ht : (⟨t, htu⟩ : Subgroup.centralizer ({u} : Set Y)) ∈ secH R u)
    (hE2 : ¬ TightInO2 (E3.secT htu ht)) {L : Subgroup Y}
    (hLπ : L ∈ orbOf (TC.nbrAdj (CoreAssembly.conjClass (tightCore R))) J (tightCore R))
    (hc : ∀ y ∈ E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J,
      ⁅u * t, y⁆ ∈ oddCoreOf (E3.orbGen (CoreAssembly.conjClass (tightCore R)) L J))
    {RJ : Subgroup Y} (hJcore : tightCore RJ = J) :
    ¬ SecInO2 (CoreAssembly.conjClass (tightCore R)) J (u * t) u := by
  intro hS
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have h := TightLargeHypR.typeRFam hF.large
  have hJΩ : J ∈ Ω := hF.maxAdj.1.2.1
  have hu2 : u * u = 1 := hF.inv.sq
  have ht2 : t * t = 1 := hF.large.datum.isUniqueInvolution_core.sq
  have htu' : t * u = u * t := Subgroup.mem_centralizer_singleton_iff.mp htu
  have ha : (u * t) * (u * t) = 1 := by
    calc (u * t) * (u * t) = u * (t * u) * t := by group
      _ = u * (u * t) * t := by rw [htu']
      _ = (u * u) * (t * t) := by group
      _ = 1 := by rw [hu2, ht2, one_mul]
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) L J := mem_orbOf_self L J
  have hπ : ∀ M ∈ orbOf (TC.nbrAdj Ω) L J, ∃ l ∈ E3.orbGen Ω L J, conjSub l J = M :=
    fun M hM => hF.exists_conj_of_mem_orbOf_L hLπ hM
  have huX : u ∈ E3.orbGen Ω L J :=
    le_iSup₂ (f := fun N (_ : N ∈ orbOf (TC.nbrAdj Ω) L J) => N) J hJπ hF.inv.mem
  have h2 := E3.tightInO2_of_secInO2 (X := E3.orbGen Ω L J) (π := orbOf (TC.nbrAdj Ω) L J) h ha
    rfl hJcore hJΩ hJπ hF.inv hπ hc (hF.oddCoreOf_orbGen_le_centralizer hLπ) hS huX
  exact hE2 (hF.tightInO2_secT_of_orbQ' htu ht hLπ huX h2)

theorem tightE3S3Orbit_of' {n : ℕ} (h4 : Thm4RBelow 3 n) : TightE3S3Orbit n := by
  intro Y _ _ R S t J u hF htu ht hedge hμ hE2 L hLπ hLs hLn hc Rd Sd S' R' T W hcore hs
  have hfam : CoreAssembly.conjClass (tightCore Rd) = CoreAssembly.conjClass (tightCore R) := by
    obtain ⟨g, hg⟩ := hF.maxAdj.1.2.1
    have hg' : conjSub g (tightCore R) = J := hg
    rw [hcore, ← hg', conjClass_conjSub]
  have hnO2 : ¬ SecInO2 (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) (u * t) u := by
    rw [hfam, hcore]
    exact hF.not_secInO2' htu ht hE2 hLπ hc hcore
  refine ⟨?_, hnO2⟩
  by_contra hnc
  obtain ⟨hJn, -⟩ := hs.secImg_normal_of_not_conj h4 hnc
  exact hnO2 (hs.secInO2_of_normal hJn)

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4

module

public import CFSG.GH74.GLS.C3.Layer1.St1P720Sh
public import CFSG.GH74.GLS.C3.Layer1.St1P720Top
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.GH74.GLS.C3.Layer1.Back112Iv2
public import CFSG.GH74.GLS.C3.Layer1.Back91Core
public import CFSG.GH74.GLS.C3.Layer1.St1PumpH2
public import CFSG.GH74.GLS.C3.Layer2.FusionTools
public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import CFSG.RankThree.PartOne.S9.MinTwoAction.QuotientRep

public section

namespace CFSG.GH74.GLS.C3.Layer1.P720

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.C3.Layer1.PumpCalc
  CFSG.GH74.GLS.C3.Layer1.PumpRigid CFSG.GH74.GLS.C3.Layer1.P720c2
open scoped commutatorElement

section Vertical

variable {G : Type} [Group G] [Finite G] {x t : G}

theorem false_of_vertical' (hc2 : B_ivk_7_20_c2g) {K : Subgroup G} (hxo : orderOf x = 2)
    (hxY : x ∈ centralizer ({t} : Set G)) {Λ : Subgroup G} (hΛ : IsLam x t K Λ)
    {L : Subgroup (barQ ↥(centralizer ({t} : Set G)))}
    (hstab : conjSub (sbar x hxY)⁻¹ L = L) (hAL : bar t Λ ≤ L) (hLC2 : InC2 ↥L) (hL4 : Gen4Comp ↥L)
    (hbad : HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q) ∨
      Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : False := by
  have hso : orderOf (sbar x hxY) = 2 := orderOf_sbar hxo hxY
  have hss : sbar x hxY * sbar x hxY = 1 := by
    have := pow_orderOf_eq_one (sbar x hxY)
    rwa [hso, sq] at this
  have hsinv : (sbar x hxY)⁻¹ = sbar x hxY := inv_eq_of_mul_eq_one_left hss
  have hstab' : L.map (MulAut.conj (sbar x hxY)).toMonoidHom = L := by
    have := hstab
    rw [hsinv] at this
    exact this
  have hsN : sbar x hxY ∈ normalizer (L : Set (barQ ↥(centralizer ({t} : Set G)))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : sbar x hxY * h * (sbar x hxY)⁻¹ ∈ L.map (MulAut.conj (sbar x hxY)).toMonoidHom :=
        ⟨h, hh, by simp [MulAut.conj_apply]⟩
      rwa [hstab'] at this
    · intro hh
      have h1 : sbar x hxY * (sbar x hxY * h * (sbar x hxY)⁻¹) * (sbar x hxY)⁻¹ ∈
          L.map (MulAut.conj (sbar x hxY)).toMonoidHom := ⟨_, hh, by simp [MulAut.conj_apply]⟩
      have h2 : sbar x hxY * (sbar x hxY * h * (sbar x hxY)⁻¹) * (sbar x hxY)⁻¹ = h := by
        calc sbar x hxY * (sbar x hxY * h * (sbar x hxY)⁻¹) * (sbar x hxY)⁻¹
            = (sbar x hxY * sbar x hxY) * h * ((sbar x hxY)⁻¹ * (sbar x hxY)⁻¹) := by group
          _ = h := by rw [hsinv, hss]; group
      rwa [hstab', h2] at h1
  have hΛK : Λ ≤ K := hΛ.le.trans inf_le_left
  have hΛY : Λ ≤ centralizer ({t} : Set G) := hΛ.le.trans inf_le_right
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hΛ.pcW).1 hxY
  have hΛX : bar t Λ ≤ L ⊓ centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G)))) := by
    refine le_inf hAL ?_
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : a * (⟨x, hxY⟩ : ↥(centralizer ({t} : Set G))) =
        (⟨x, hxY⟩ : ↥(centralizer ({t} : Set G))) * a :=
      Subgroup.mem_centralizer_singleton_iff.1 (hΛC ha)
    show barMk _ a * barMk _ ⟨x, hxY⟩ = barMk _ ⟨x, hxY⟩ * barMk _ a
    rw [← map_mul, ← map_mul, h1]
  have hΛ2 := isTwoComponent_centralizer_mk hΛ.pcW hxY
  obtain ⟨Kc, hKc, hsub, -, -⟩ :=
    (ComponentClassification.CatalogueBAlternating.pComponent_two_iff _).mpr hΛ2
  have hsub1 := isSubnormal_map_subgroupOf (barMk ↥(centralizer ({t} : Set G))) hΛC hsub
  have hXB : L ⊓ centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G)))) ≤
      (centralizer ({(⟨x, hxY⟩ : ↥(centralizer ({t} : Set G)))} :
        Set ↥(centralizer ({t} : Set G)))).map (barMk ↥(centralizer ({t} : Set G))) :=
    inf_le_right.trans (centralizer_sbar_le_map hxo hxY)
  have hMsub : ((bar t Λ).subgroupOf
      (L ⊓ centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G)))))).IsSubnormal :=
    isSubnormal_subgroupOf_of_le hXB hsub1
  obtain ⟨φ, hφs, hφo, -⟩ := exists_phi hΛK hΛY hΛ.cover
  let M : Subgroup ↥(L ⊓ centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G))))) :=
    (bar t Λ).subgroupOf (L ⊓ centralizer ({sbar x hxY} : Set (barQ ↥(centralizer ({t} : Set G)))))
  let e : ↥M ≃* ↥(bar t Λ) := Subgroup.subgroupOfEquivOfLe hΛX
  let ψ : ↥M →* kBar K := φ.comp e.toMonoidHom
  have hψs : Function.Surjective ψ := hφs.comp e.surjective
  have hψo : Odd (Nat.card ψ.ker) := by
    have h1 : ψ.ker = φ.ker.comap e.toMonoidHom := (MonoidHom.comap_ker φ e.toMonoidHom).symm
    have h3 : φ.ker.comap e.toMonoidHom = φ.ker.map e.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm e φ.ker
    have h2 : Nat.card ↥(φ.ker.comap e.toMonoidHom) = Nat.card ↥φ.ker := by
      rw [h3, Subgroup.card_map_of_injective e.symm.injective]
    rw [h1, h2]
    exact hφo
  have hker : ψ.ker = pPrimeCore 2 ↥M := by
    apply le_antisymm
    · exact le_sSup ⟨MonoidHom.normal_ker ψ, Nat.coprime_two_left.mpr hψo⟩
    · exact normal_odd_le_ker ψ hψs (pPrimeCore_quotient_eq_bot ↥K) (pPrimeCore 2 ↥M)
        (odd_card_pPrimeCore ↥M)
  let hiso : (↥M ⧸ pPrimeCore 2 ↥M) ≃* kBar K :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hbad' : HasL2Model (↥M ⧸ pPrimeCore 2 ↥M) (fun q => Odd q ∧ ¬ IsFM9 q) ∨
      Nonempty ((↥M ⧸ pPrimeCore 2 ↥M) ≃* alternatingGroup (Fin 7)) := by
    rcases hbad with h | hf
    · exact Or.inl (hasL2Model_of_mulEquiv hiso.symm h)
    · obtain ⟨f⟩ := hf
      exact Or.inr ⟨hiso.trans f⟩
  exact hc2 (barQ ↥(centralizer ({t} : Set G))) L hLC2 hL4 (sbar x hxY) hss hsN M hMsub hbad'

end Vertical

section Step

variable {G : Type} [Group G] [Finite G] {x t : G}

theorem not_inC2_pumpup'
    (hc2 : B_ivk_7_20_c2g) (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    (hgen4 : CFSG.GH74.Gen4 G) {K K' : Subgroup G} (hlt : PumpUpLT 2 x K t K')
    (hU2 : InU2 (kBar K)) (hnC2 : ¬ InC2 (kBar K)) (hno34 : ¬ IsL34Quotient (kBar K))
    (hsimple : IsSimpleGroup (kBar K))
    (hbad : HasL2Model (kBar K) (fun q => Odd q ∧ ¬ IsFM9 q) ∨
      Nonempty (kBar K ≃* alternatingGroup (Fin 7))) : ¬ InC2 ↥(bar t K') := by
  intro hInC2
  have hxY : x ∈ centralizer ({t} : Set G) := mem_centralizer_symm hlt.2.2.1
  obtain ⟨Λ, hΛ, hK'c, ⟨L, hL, himg, hcases⟩, -, -, -⟩ := step_core hlt hxY
  rcases hcases with ⟨hstab, hAL⟩ | ⟨hne, -, -⟩
  · have hbar : bar t K' = L := by
      rcases himg with h | h
      · exact h
      · rw [h, hstab]
    have hLC2 : InC2 ↥L := by
      rw [← hbar]
      exact hInC2
    have hL4 : Gen4Comp ↥L := gen4Comp_of_gen4Cen (gen4Cen_barQ hgen4 hlt.2.1.1) L
    exact false_of_vertical' hc2 hlt.1.1 hxY hΛ hstab hAL hLC2 hL4 hbad
  · exact P720.false_of_diagonal hG hF hgen4 hlt hxY hU2 hnC2 hno34 hsimple hΛ himg hne hInC2

end Step

end CFSG.GH74.GLS.C3.Layer1.P720

namespace CFSG.GH74.GLS

open Subgroup CFSG.GH74.GLS.C3.Layer1.P720 CFSG.GH74.GLS.C3.Layer1.PumpCalc CFSG.GH74.GLS.C3.Layer1.P720c2

theorem b_ivk_7_20_h2_of_c2g
    (hc2 : B_ivk_7_20_c2g) (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    (hL34 : B_gen4_noL34_elem) : B_ivk_7_20_h2 := by
  intro G _ _ hGc x K x' K' hpair hU2 hnC2 _ hlong
  have key : ∀ (a b : G × Subgroup G),
      Relation.ReflTransGen (fun a b : G × Subgroup G => PumpUpLT 2 a.1 a.2 b.1 b.2) a b →
      IsILo 2 a.1 a.2 → InU2 (kBar a.2) → ¬ InC2 (kBar a.2) →
      IsILo 2 b.1 b.2 ∧ InU2 (kBar b.2) ∧ ¬ InC2 (kBar b.2) := by
    intro a b hab
    induction hab with
    | refl => exact fun h1 h2 h3 => ⟨h1, h2, h3⟩
    | @tail c b hac hstep ih =>
      intro h1 h2 h3
      obtain ⟨hIc, hUc, hNc⟩ := ih h1 h2 h3
      have hno : ¬ (IsL34Quotient (kBar c.2) ∧ CFSG.IsElementaryAbelian 2 ↥(center (kBar c.2)) ∧
          Nat.card ↥(center (kBar c.2)) ≤ 4) :=
        hL34 G hGc.gen4 c.1 c.2 hIc.1 hIc.2.2
      obtain ⟨hbad, hsimple, hno34⟩ := bad_of_inU2_not_inC2 hUc hNc hno
      have hIb : IsILo 2 b.1 b.2 := hstep.2.1
      have hK'c : IsPCompIn 2 (centralizer ({b.1} : Set G)) b.2 := hIb.2.2
      have hnot : ¬ InC2 ↥(bar b.1 b.2) :=
        not_inC2_pumpup' hc2 hG hF hGc.gen4 hstep hUc hNc hno34 hsimple hbad
      obtain ⟨e⟩ := kBar_equiv_bar hK'c
      refine ⟨hIb, ?_, fun h => hnot (E2.inC2_of_mulEquiv e h)⟩
      rcases hGc.lt2o.2 b.1 hIb.1 (bar b.1 b.2) (isComponent_bar hK'c) with h | h
      · exact absurd h hnot
      · exact inU2_of_mulEquiv e.symm h
  obtain ⟨-, h1, h2⟩ := key (x, K) (x', K') hlong.2 hlong.1 hU2 hnC2
  exact ⟨h1, h2⟩


theorem b_ivk_7_20_h2_proved
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts) (hLB : Prop27.Prop27LocalBalance)
    (hP : E2.PumpUpData) (hL34 : B_gen4_noL34_elem) : B_ivk_7_20_h2 :=
  b_ivk_7_20_h2_of_c2g (C3.Layer1.P720c2.b_ivk_7_20_c2g_proved hG hF hLB hP) hG hF hL34

end CFSG.GH74.GLS

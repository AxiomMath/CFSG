module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGenSec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf4Type
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Twin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf9Fin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

section Trans

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem layer_trans (hT : Thm4RTwinBelow 3 n) (h : PerpHypS n Y R S t) {c : Y}
    (hc2 : c * c = 1) (hc1 : c ≠ 1) (hno : SecNoExit R c) {J₁ J₂ : Subgroup Y}
    (hJ₁ : J₁ ∈ Om R) (hJ₂ : J₂ ∈ Om R) {w : Y}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w) {T₁ T₂ : Subgroup Y}
    (hT₁ : IsSylow2In T₁ J₁) (hT₂ : IsSylow2In T₂ J₂)
    (hT₁c : T₁ ≤ Subgroup.centralizer ({c} : Set Y)) (hT₂c : T₂ ≤ Subgroup.centralizer ({c} : Set Y))
    (hperp₁ : ∀ J₀ ∈ Om R, J₀ ∈ KPerp (Om R) J₁ → J₀ = J₁ ∨ J₀ = J₂)
    (hperp₂ : ∀ J₀ ∈ Om R, J₀ ∈ KPerp (Om R) J₂ → J₀ = J₂ ∨ J₀ = J₁) :
    ∀ K ∈ TwinDisc.secFam (Om R) c, ∀ L ∈ TwinDisc.secFam (Om R) c,
      ∃ x : SecQ R c, conjSub x K = L := by
  have hC := CoreData.of_S h.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2' : IsPGroup 2 (Subgroup.zpowers c) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hKtq : J₁ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨T₁, hT₁, hT₁c⟩⟩
  have hK'tq : J₂ ∈ tqMembers3 (Om R) c :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨T₂, hT₂, hT₂c⟩⟩
  have hS := p23_q8Section h hc2
  have hlt := secQ_card_lt h hc1
  obtain ⟨htC₁, htY₁, hz₁⟩ := isUniqueInvolution_secImg hΩ hc2' hKtq hw₁
  obtain ⟨htC₂, htY₂, hz₂⟩ := isUniqueInvolution_secImg hΩ hc2' hK'tq hw₂
  refine TwinLayerGen.transitive_of_twin_nbr hT hlt hS hno (secImg_mem_secFam hKtq)
    (secImg_mem_secFam hK'tq) hz₁ hz₂ ?_ ?_
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hKtq hJ₀
      (fun J₀' hJ₀' hp => hperp₁ J₀' hJ₀'.1 hp) hMn
  · intro M hM hMn
    obtain ⟨J₀, hJ₀, rfl⟩ := exists_of_mem_secFam hM
    exact TwinLayerGen.secNbr_eq_of_perp hΩ hc2' hK'tq hJ₀
      (fun J₀' hJ₀' hp => hperp₂ J₀' hJ₀'.1 hp) hMn

end Trans

section Frame

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem perp_pair (hc : P23Cfg n Y R S t K' W u e g) :
    (∀ J ∈ Om R, J ∈ KPerp (Om R) (tightCore R) → J = tightCore R ∨ J = K') ∧
      (∀ J ∈ Om R, J ∈ KPerp (Om R) K' → J = K' ∨ J = tightCore R) := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hperp : KPerp (Om R) (tightCore R) = {tightCore R, K'} :=
    hc.std.perp.perp.trans (twinSet_eq_pair hc.std.two hc.std.hK' hc.std.hne)
  refine ⟨fun J _ hJ => ?_, fun J _ hJ => ?_⟩
  · rw [hperp] at hJ
    exact hJ
  · rw [← CFSG.ClassicalInvolution.A7Q.Gen.kPerp_eq_of_twin hΩ hK hc.std.hK', hperp] at hJ
    exact hJ.symm

theorem perp_conj_pair {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) {A B : Subgroup Y}
    (hperp : ∀ J ∈ Ω, J ∈ KPerp Ω A → J = A ∨ J = B) (x : Y) :
    ∀ J ∈ Ω, J ∈ KPerp Ω (conjSub x A) → J = conjSub x A ∨ J = conjSub x B := by
  intro J hJ hJp
  rcases hJp with h | h
  · exact Or.inl h
  · have h1 := omegaNbr_conj hΩ.conjInvariant h x⁻¹
    rw [conjSub_inv_conjSub] at h1
    rcases hperp (conjSub x⁻¹ J) (hΩ.conjInvariant _ _ hJ) (Set.mem_insert_of_mem _ h1) with h2 | h2
    · have h3 := congrArg (conjSub x) h2
      rw [conjSub_conjSub_inv] at h3
      exact absurd h3 h.2.1
    · have h3 := congrArg (conjSub x) h2
      rw [conjSub_conjSub_inv] at h3
      exact Or.inr h3

theorem e_trans (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R e) :
    ∀ K ∈ TwinDisc.secFam (Om R) e, ∀ L ∈ TwinDisc.secFam (Om R) e,
      ∃ x : SecQ R e, conjSub x K = L := by
  have hC := CoreData.of_S hc.std.perp.core
  have hzK : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hc.std.hK'
  obtain ⟨A, A', hA, hA', hAe, hA'e, -, -, -⟩ := exists_std_t hc
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  exact layer_trans hT hc.std.perp hc.data.he2 hc.data.he1 hno (CoreAssembly.mem_conjClass_self _)
    hc.std.hK'.1 hzK hzK' hA hA' hAe hA'e hp₁ hp₂

theorem u_trans (hT : Thm4RTwinBelow 3 n) (hc : P23Cfg n Y R S t K' W u e g) (hno : SecNoExit R u) :
    ∀ K ∈ TwinDisc.secFam (Om R) u, ∀ L ∈ TwinDisc.secFam (Om R) u,
      ∃ x : SecQ R u, conjSub x K = L := by
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hzK : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hzK' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hzK hc.std.hK'
  obtain ⟨A, A', hA, hA', hAe, hA'e, -, htA, htA'⟩ := exists_std_t hc
  obtain ⟨hp₁, hp₂⟩ := perp_pair hc
  have hd := hc.data
  have hNe := normalizer_le_centralizer_e hd
  have hgN : g ∈ Subgroup.normalizer (W : Set Y) := by
    have : (⨆ X ∈ DSet (Om R) W, X) ≤ Subgroup.normalizer (W : Set Y) :=
      iSup₂_le fun X hX => hX.2
    exact this hd.hg
  have hgC : g ∈ Subgroup.centralizer ({e} : Set Y) := hNe hgN
  have hu : u = (g * t * g⁻¹) * e := by
    rw [hd.hgt, mul_assoc, hd.he2, mul_one]
  have hconj : ∀ {T : Subgroup Y}, T ≤ Subgroup.centralizer ({e} : Set Y) →
      (∀ x ∈ T, x * t = t * x) → conjSub g T ≤ Subgroup.centralizer ({u} : Set Y) := by
    intro T hTe hTt
    rintro _ ⟨x, hx, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl
    rw [e1, Subgroup.mem_centralizer_singleton_iff]
    have hxe : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hTe hx)
    have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hye : (g * x * g⁻¹) * e = e * (g * x * g⁻¹) := by
      have hge' : g⁻¹ * e = e * g⁻¹ := by
        calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * e) * g⁻¹ := by rw [hge]
          _ = e * g⁻¹ := by group
      calc (g * x * g⁻¹) * e = g * x * (g⁻¹ * e) := by group
        _ = g * x * (e * g⁻¹) := by rw [hge']
        _ = g * (x * e) * g⁻¹ := by group
        _ = g * (e * x) * g⁻¹ := by rw [hxe]
        _ = (g * e) * x * g⁻¹ := by group
        _ = (e * g) * x * g⁻¹ := by rw [hge]
        _ = e * (g * x * g⁻¹) := by group
    have hxt := hTt x hx
    have hyt : (g * x * g⁻¹) * (g * t * g⁻¹) = (g * t * g⁻¹) * (g * x * g⁻¹) := by
      calc (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
        _ = g * (t * x) * g⁻¹ := by rw [hxt]
        _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group
    have key : (g * x * g⁻¹) * u = u * (g * x * g⁻¹) := by
      rw [hu]
      calc (g * x * g⁻¹) * ((g * t * g⁻¹) * e)
          = ((g * x * g⁻¹) * (g * t * g⁻¹)) * e := by group
        _ = ((g * t * g⁻¹) * (g * x * g⁻¹)) * e := by rw [hyt]
        _ = (g * t * g⁻¹) * ((g * x * g⁻¹) * e) := by group
        _ = (g * t * g⁻¹) * (e * (g * x * g⁻¹)) := by rw [hye]
        _ = ((g * t * g⁻¹) * e) * (g * x * g⁻¹) := by group
    exact key
  have hAt : ∀ x ∈ A, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK (hA.1 hx))
  have hA't : ∀ x ∈ A', x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.le_centralizer_of_unique hzK' (hA'.1 hx))
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hzK.conj g
  have hw' : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hzK'.conj g
  exact layer_trans hT hc.std.perp hd.hu2 hd.hu1 hno
    (hΩ.conjInvariant g _ hK) (hΩ.conjInvariant g _ hc.std.hK'.1) hw hw'
    (hA.conj g) (hA'.conj g) (hconj hAe hAt) (hconj hA'e hA't)
    (perp_conj_pair hΩ hp₁ g) (perp_conj_pair hΩ hp₂ g)

end Frame

section Steps

theorem p23E4Trans_of_t4 {n : ℕ} (hT : TwinThmE.T4Supply) : P23E4Trans n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno
  exact e_trans (hT n hcit hP) hc hno

theorem p23Y5Trans_of_t4 {n : ℕ} (hT : TwinThmE.T4Supply) : P23Y5Trans n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno
  exact u_trans (hT n hcit hP) hc hno

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

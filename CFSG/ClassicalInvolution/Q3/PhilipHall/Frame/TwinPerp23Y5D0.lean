module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Y5C0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711Cor
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinSec711Mu
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Cls

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement


section Y5D0

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem secD_subset_pair (hc : P23Cfg n Y R S t K' W u e g) :
    ∀ N ∈ TwinSec711.secD (Om R) W u,
      N = TwinDisc.secImg (Om R) u (conjSub g (tightCore R)) ∨
        N = TwinDisc.secImg (Om R) u (conjSub g K') := by
  classical
  rintro N ⟨J, hJ, T, hT, hTJ, hTu, rfl⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hNe := normalizer_le_centralizer_e hd
  have hTe : T ≤ Subgroup.centralizer ({e} : Set Y) := hT.2.trans hNe
  have hgt : g * t * g⁻¹ = u * e := hd.hgt
  have hTt : ∀ x ∈ T, (g⁻¹ * x * g) * t = t * (g⁻¹ * x * g) := by
    intro x hx
    have h1 : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp (hTu hx)
    have h2 : x * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp (hTe hx)
    have h3 : x * (g * t * g⁻¹) = (g * t * g⁻¹) * x := by
      rw [hgt, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]
    calc (g⁻¹ * x * g) * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [h3]
      _ = t * (g⁻¹ * x * g) := by group
  have hJ'Ω : conjSub g⁻¹ J ∈ Om R := hΩ.conjInvariant g⁻¹ J hJ.1
  have hT'J : IsSylow2In (conjSub g⁻¹ T) (conjSub g⁻¹ J) := hTJ.conj g⁻¹
  have hT'c : conjSub g⁻¹ T ≤ Subgroup.centralizer ({t} : Set Y) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by simp
    rw [e1]
    exact hTt x hx
  by_cases hJK : conjSub g⁻¹ J = tightCore R
  · left
    have : J = conjSub g (tightCore R) := by
      rw [← hJK, conjSub_conjSub_inv]
    rw [this]
  · right
    have h8 : 8 ≤ Nat.card ↥(conjSub g⁻¹ T) :=
      Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hJ'Ω hT'J)
    have hN : conjSub g⁻¹ T ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hJ'Ω (Ne.symm hJK) hz hT'J.1 hT'J.2.1
        (by omega) hT'c
    have hnbr : conjSub g⁻¹ J ∈ KPerp (Om R) (tightCore R) :=
      Or.inr ⟨hJ'Ω, hJK, conjSub g⁻¹ T, mem_RSet_of_isSylow2In hJ'Ω hT'J, hT'J.1, hN⟩
    rcases (perp_pair hc).1 _ hJ'Ω hnbr with h | h
    · exact absurd h hJK
    · have : J = conjSub g K' := by
        rw [← h, conjSub_conjSub_inv]
      rw [this]

theorem u_pair_data (hc : P23Cfg n Y R S t K' W u e g) :
    ∃ A ∈ TwinDisc.secFam (Om R) u, ∃ B ∈ TwinDisc.secFam (Om R) u, A ≠ B ∧
      B ∈ omegaNbr (TwinDisc.secFam (Om R) u) A ∧
      ∀ N ∈ TwinSec711.secD (Om R) W u, N = A ∨ N = B := by
  classical
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hc2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcomm, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hR₃u := conj_cent_u hc hR₁e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz (hR₁.1 hx)))
  have hR₃'u := conj_cent_u hc hR₁'e (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp
    (le_centralizer_of_unique hz' (hR₁'.1 hx)))
  have hJ₁ : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hJ₂ : conjSub g K' ∈ Om R := hΩ.conjInvariant g _ hc.std.hK'.1
  have hR₃ : IsSylow2In (conjSub g R₁) (conjSub g (tightCore R)) := hR₁.conj g
  have hR₃' : IsSylow2In (conjSub g R₁') (conjSub g K') := hR₁'.conj g
  have hτ₁ : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    rw [← hd.hgt]; exact hz.conj g
  have hτ₂ : IsUniqueInvolution (conjSub g K') (u * e) := by
    rw [← hd.hgt]; exact hz'.conj g
  have hne₂ : conjSub g K' ≠ conjSub g (tightCore R) := by
    intro he
    apply hc.std.hne
    have := congrArg (conjSub g⁻¹) he
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hJ₁tq : conjSub g (tightCore R) ∈ tqMembers3 (Om R) u :=
    ⟨hJ₁, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₁ ⟨conjSub g R₁, hR₃, hR₃u⟩⟩
  have hJ₂tq : conjSub g K' ∈ tqMembers3 (Om R) u :=
    ⟨hJ₂, TwinADescent3.mem_tq_of_sylCent hΩ h2 hJ₂ ⟨conjSub g R₁', hR₃', hR₃'u⟩⟩
  have hR₁'N : R₁' ≤ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) :=
    Sec6Gen.le_normalizer_of_le_centralizer hΩ hK hc.std.hK'.1 (Ne.symm hc.std.hne) hz hR₁'.1
      hR₁'.2.1
      (by have := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hc.std.hK'.1 hR₁'); omega)
      (fun x hx => le_centralizer_of_unique hz' (hR₁'.1 hx))
  have hR₃'N : conjSub g R₁' ≤
      Subgroup.normalizer ((conjSub g (tightCore R) : Subgroup Y) : Set Y) := by
    intro x hx
    have hy : g⁻¹ * x * g ∈ R₁' := mem_conjSub_iff.mp hx
    have hyN := hR₁'N hy
    refine Subgroup.mem_normalizer_iff.mpr fun a => ?_
    rw [mem_conjSub_iff, mem_conjSub_iff]
    have := Subgroup.mem_normalizer_iff.mp hyN (g⁻¹ * a * g)
    have e1 : g⁻¹ * (x * a * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * a * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1]
    exact this
  refine ⟨_, TwinDisc.secImg_mem_secFam hJ₁tq, _, TwinDisc.secImg_mem_secFam hJ₂tq,
    secImg_ne_of_twins hΩ hc2' hJ₁tq hJ₂tq hne₂ hτ₁ hτ₂, ?_, secD_subset_pair hc⟩
  exact omegaNbr_secImg hΩ hc2' hJ₁tq hJ₂tq hR₃ hR₃' hR₃u hR₃'u (hcomm.conjSub g) hR₃'N

end Y5D0


section Y5D1

theorem p23Y5SecMuE4Ex_proved (n : ℕ) : P23Y5SecMuE4Ex n := by
  intro _ _ Y _ _ R S t K' W u e g hc _
  classical
  obtain ⟨A, hA, B, hB, hAB, hBA, hpair⟩ := u_pair_data hc
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have hS := p23_q8Section hc.std.perp hd.hu2
  have hΦ := hS.hyp
  have hq8 : ∀ L ∈ TwinDisc.secFam (Om R) u, ∃ P, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup 2) := fun L hL => by
    obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (T := ⊥) IsPGroup.of_bot (bot_le : ⊥ ≤ L)
    exact ⟨P, hP, hS.q8 L hL P hP⟩
  have hPΦ : Q3CL.PartIHypG (TwinDisc.secFam (Om R) u) :=
    ⟨hΦ, TwinThmE.classicalClause_of_q8 hΦ hq8 hS.two, hS.aEmpty⟩
  obtain ⟨V, hV, hDV⟩ := TwinSec711.exists_wgroup_dSet_le hΩ hc2 hc.std.hW hd.huW
  refine ⟨V, hV, ?_⟩
  obtain ⟨g', ρ, σ, hρ, hσ⟩ := Q3MT.exists_rep_pair_of_omegaNbr hPΦ hV hA hBA
  have hrep : ∀ τ : Asc77.Thompson.Rep (TwinDisc.secFam (Om R) u) V, τ.K = A ∨ τ.K = B :=
    fun τ => hpair τ.K (hDV τ.K τ.hK τ.R τ.hRK τ.hR.2)
  have hne : ρ.K ≠ σ.K := by
    rw [hρ, hσ]
    exact fun h => hAB ((conjSub_inj g').mp h)
  have hσρ : σ.K ∈ omegaNbr (TwinDisc.secFam (Om R) u) ρ.K := by
    rw [hρ, hσ]
    exact omegaNbr_conj hΦ.conjInvariant hBA g'
  refine TwinSec711.muIsoE4_of_two hPΦ hV hne hσρ fun τ => ?_
  rcases hrep τ with h1 | h1 <;> rcases hrep ρ with h2 | h2 <;> rcases hrep σ with h3 | h3
  · exact absurd (h2.trans h3.symm) hne
  · exact Or.inl (h1.trans h2.symm)
  · exact Or.inr (h1.trans h3.symm)
  · exact absurd (h2.trans h3.symm) hne
  · exact absurd (h2.trans h3.symm) hne
  · exact Or.inr (h1.trans h3.symm)
  · exact Or.inl (h1.trans h2.symm)
  · exact absurd (h2.trans h3.symm) hne

end Y5D1

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

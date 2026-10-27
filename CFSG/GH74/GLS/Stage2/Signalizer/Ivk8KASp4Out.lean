module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Cls
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Out
public import CFSG.GH74.GLS.IVK.L2.Lemma12
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd
public import CFSG.RankThree.Classical.SteinbergBYSymplecticFieldDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerB
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerD

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree CFSG.RankThree.Classical.SteinbergBY
open scoped commutatorElement

theorem ka_conj_inj_psp4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) :
    Function.Injective
      (MulAut.conj : StatedProj (StatedSp 2 F) →* MulAut (StatedProj (StatedSp 2 F))) := by
  intro y z h
  have hz : z⁻¹ * y ∈ center (StatedProj (StatedSp 2 F)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : y * g * y⁻¹ = z * g * z⁻¹ := by
      have := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) => φ g) h
      simpa [MulAut.conj_apply] using this
    calc g * (z⁻¹ * y) = z⁻¹ * (z * g * z⁻¹) * y := by group
      _ = z⁻¹ * (y * g * y⁻¹) * y := by rw [h1]
      _ = z⁻¹ * y * g := by group
  rw [center_psp4_eq_bot hodd, Subgroup.mem_bot] at hz
  calc y = z * (z⁻¹ * y) := by group
    _ = z := by rw [hz, mul_one]

theorem ka_outCentral_psp4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (α : MulAut (StatedProj (StatedSp 2 F))) :
    ∀ x : MulAut (StatedProj (StatedSp 2 F)), ⁅x, α⁆ ∈ innSub (StatedProj (StatedSp 2 F)) := by
  intro x
  rw [commutatorElement_def]
  exact outAbelian_psp4 hodd x α

theorem ka_eq_sq_of_pow_odd {G : Type*} [CommGroup G] (m c : G) (k : ℕ)
    (h : m ^ (2 * k + 1) = c * c) : m = (c * (m ^ k)⁻¹) * (c * (m ^ k)⁻¹) := by
  have h' : (m ^ k) * (m ^ k) * m = c * c := by
    rw [← h, pow_succ, pow_mul', sq]
  generalize m ^ k = a at h' ⊢
  calc m = (a * a * m) * (a⁻¹ * a⁻¹) := by simp [mul_comm, mul_assoc]
    _ = c * a⁻¹ * (c * a⁻¹) := by rw [h']; simp [mul_comm, mul_left_comm, mul_assoc]

theorem ka_conjAut_inner_of_odd {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (A : gsp 2 F) (ho : Odd (orderOf (conjAut 2 F A))) :
    conjAut 2 F A ∈ innSub (StatedProj (StatedSp 2 F)) := by
  obtain ⟨k, hk⟩ := ho
  have h1 : (conjAut 2 F A) ^ (2 * k + 1) = 1 := by
    rw [← hk]
    exact pow_orderOf_eq_one _
  have h2 : conjAut 2 F (A ^ (2 * k + 1)) * fieldAut 2 F 1 = 1 := by
    rw [map_pow, map_one, mul_one]
    exact h1
  obtain ⟨-, c, hc⟩ :=
    ((CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      hodd le_rfl).2.1 (A ^ (2 * k + 1)) 1).1 h2
  have hs : A ^ (2 * k + 1) = scalarGsp c := Subtype.ext hc
  have hm : multiplier 2 F A ^ (2 * k + 1) = c * c := by
    rw [← map_pow, hs, multiplier_scalarGsp]
  refine conjAut_inner_of_multiplier_sq A (c * ((multiplier 2 F A) ^ k)⁻¹) ?_
  exact ka_eq_sq_of_pow_odd (multiplier 2 F A) c k hm

theorem ka_diag_normal {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) :
    ((conjAut 2 F : gsp 2 F →* MulAut (StatedProj (StatedSp 2 F))).range).Normal := by
  refine ⟨fun n hn γ => ?_⟩
  obtain ⟨A, rfl⟩ := hn
  obtain ⟨B, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd γ
  refine ⟨B * gspFieldMap σ A * B⁻¹, ?_⟩
  have e := fieldAut_mul_conjAut_mul_inv σ A
  calc conjAut 2 F (B * gspFieldMap σ A * B⁻¹)
      = conjAut 2 F B * (fieldAut 2 F σ * conjAut 2 F A * (fieldAut 2 F σ)⁻¹) *
          (conjAut 2 F B)⁻¹ := by rw [e]; simp only [map_mul, map_inv]
    _ = conjAut 2 F B * fieldAut 2 F σ * conjAut 2 F A * (conjAut 2 F B * fieldAut 2 F σ)⁻¹ := by
        simp only [mul_inv_rev]; group

theorem ka_outCyc_psp4 {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) :
    KAOutCyc (StatedProj (StatedSp 2 F)) := by
  intro p hp hp2 P hPp hPinn
  set N : Subgroup (MulAut (StatedProj (StatedSp 2 F))) :=
    (conjAut 2 F : gsp 2 F →* MulAut (StatedProj (StatedSp 2 F))).range with hN
  have hNn : N.Normal := ka_diag_normal hodd
  let ψ : (F ≃+* F) →* MulAut (StatedProj (StatedSp 2 F)) ⧸ N :=
    (QuotientGroup.mk' N).comp (fieldAut 2 F)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨B, σ, rfl⟩ := psp4_odd_automorphism_normal_form hodd γ
    refine ⟨σ, ?_⟩
    show (QuotientGroup.mk (fieldAut 2 F σ) : MulAut (StatedProj (StatedSp 2 F)) ⧸ N) =
      QuotientGroup.mk (conjAut 2 F B * fieldAut 2 F σ)
    rw [QuotientGroup.eq]
    have hB : conjAut 2 F B ∈ N := ⟨B, rfl⟩
    have := hNn.conj_mem _ hB (fieldAut 2 F σ)⁻¹
    simpa [mul_assoc] using this
  have := CFSG.GH74.GLS.IVK.ringAut_isCyclic F
  have hq : IsCyclic (MulAut (StatedProj (StatedSp 2 F)) ⧸ N) := isCyclic_of_surjective ψ hψ
  let φ : ↥P →* MulAut (StatedProj (StatedSp 2 F)) ⧸ N := (QuotientGroup.mk' N).comp P.subtype
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have heN : (e : MulAut (StatedProj (StatedSp 2 F))) ∈ N := (QuotientGroup.eq_one_iff _).1 he
    obtain ⟨A, hA⟩ := heN
    have ho : Odd (orderOf (e : MulAut (StatedProj (StatedSp 2 F)))) :=
      ka_odd_of_mem_pGroup hp hp2 hPp e.2
    have hinn : (e : MulAut (StatedProj (StatedSp 2 F))) ∈
        innSub (StatedProj (StatedSp 2 F)) := by
      rw [← hA]
      exact ka_conjAut_inner_of_odd hodd A (hA ▸ ho)
    exact Subtype.ext (hPinn _ e.2 hinn)
  have : IsCyclic ↥φ.range := Subgroup.isCyclic _
  exact isCyclic_of_surjective ((MonoidHom.ofInjective hinj).symm : φ.range →* P)
    (MulEquiv.surjective _)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

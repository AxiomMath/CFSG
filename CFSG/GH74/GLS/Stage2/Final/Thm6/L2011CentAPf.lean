module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Cons
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011Type

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Final.Thm6 CFSG.GH74.GLS.Stage2.Final.Thm6.L20 CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Local.P34
open CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound (bar_mem_S1_iff)
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2012 (F20_conj_mem F20_le_OddCore)

section CentA

variable {G : Type} [Group G]

theorem commute_of_inv_conj {y f : G} (hyy : y * y = 1) {F : Subgroup G} (hFodd : Odd (Nat.card ↥F))
    (hcF : f * y * f⁻¹ * y⁻¹ ∈ F) (hyc : y * (f * y * f⁻¹ * y⁻¹) = (f * y * f⁻¹ * y⁻¹) * y) :
    y * f = f * y := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  set c : G := f * y * f⁻¹ * y⁻¹ with hc
  have hinv : y * c * y⁻¹ = c⁻¹ := by
    have h1 : y * c * y⁻¹ = y * f * y * f⁻¹ * (y * y) := by
      rw [hc, hyi]; group
    have h2 : c⁻¹ = y * f * y * f⁻¹ := by
      calc c⁻¹ = y * f * y⁻¹ * f⁻¹ := by rw [hc]; group
        _ = y * f * y * f⁻¹ := by rw [hyi]
    rw [h1, h2, hyy, mul_one]
  have hcc : c = c⁻¹ := by
    rw [← hinv, hyc]; group
  have hcsq : c * c = 1 := by
    calc c * c = c * c⁻¹ := by rw [← hcc]
      _ = 1 := mul_inv_cancel c
  have hord2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hcsq)
  have hordF : orderOf c ∣ Nat.card ↥F := by
    have := Subgroup.orderOf_dvd_natCard F hcF
    simpa using this
  have hcop : Nat.Coprime 2 (Nat.card ↥F) := Nat.coprime_two_left.2 hFodd
  have h1 : orderOf c ∣ Nat.gcd 2 (Nat.card ↥F) := Nat.dvd_gcd hord2 hordF
  rw [hcop] at h1
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h1)
  have : f * y * f⁻¹ = y := by
    have h3 : f * y * f⁻¹ * y⁻¹ = 1 := hc1
    calc f * y * f⁻¹ = f * y * f⁻¹ * y⁻¹ * y := by group
      _ = y := by rw [h3, one_mul]
  calc y * f = (f * y * f⁻¹) * f := by rw [this]
    _ = f * y := by group

end CentA

section CentA2

variable {G : Type} [Group G] [Finite G]

theorem centA20_of (hCF : CFTypeAut) (h20b : Coprime20b) (hcore : CentCoreProp) : CentA20 := by
  intro G _ _ z k S hC g hg hJ hSJ y hyS hyS1 hy2 hy0 hF1 a ha
  obtain ⟨q, L₁, L₂, K₁, K₂, hP, -, hK⟩ := exists_data2011 hC
  have hconcl := typeData20 hCF h20b hcore hC hg hJ hP hK
  have hctx : Stage2Ctx G z k S := hC.1.ctx.ctx17.ctx
  have hz2 : orderOf z = 2 := hctx.orderOf_z
  have hJle : J0 z g ≤ H0 z g := J0_le_H0 z g
  have hJH : ∀ h ∈ H0 z g, ∀ j ∈ J0 z g, h * j * h⁻¹ ∈ J0 z g := fun _ hh _ hj => J0_conj_mem z g hh hj
  have hyJ : y ∈ J0 z g := hSJ hyS
  have hyC : y ∈ Cen z := hctx.S_le_Cen hyS
  have hysq : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hyL : ∀ l ∈ L₁, toBar z ⟨y, hyC⟩ * l * (toBar z ⟨y, hyC⟩)⁻¹ ∈ L₁ := by
    obtain ⟨-, hyC', hcomp⟩ := bar_mem_S1_iff.1 hyS1
    have hL₁ : IsComponent L₁ := by
      have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
        rw [hP.comps]; exact Set.mem_insert _ _
      exact this
    have hL₁le : L₁ ≤ LBar z := le_sup_left.trans hP.prod.1.le
    intro l hl
    exact (Subgroup.mem_normalizer_iff.1 (hcomp L₁ hL₁ hL₁le) l).1 hl
  have hfix : ∀ a ∈ K₁, y * a * y⁻¹ ∈ K₁ := compData_fix hK hyC hyL
  have hybar : mkH (J0 z g) ⟨y, hyJ⟩ * mkH (J0 z g) ⟨y, hyJ⟩ = 1 := by
    rw [← map_mul, show (⟨y, hyJ⟩ : ↥(J0 z g)) * ⟨y, hyJ⟩ = 1 from Subtype.ext hysq, map_one]
  have hN : mkH (J0 z g) ⟨y, hyJ⟩ ∈
      normalizer ((barIn (J0 z g) K₁ : Subgroup (HBar (J0 z g))) : Set (HBar (J0 z g))) := by
    have fwd : ∀ x ∈ barIn (J0 z g) K₁, mkH (J0 z g) ⟨y, hyJ⟩ * x * (mkH (J0 z g) ⟨y, hyJ⟩)⁻¹ ∈
        barIn (J0 z g) K₁ := by
      intro x hx
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 hx
      refine Subgroup.mem_map.2 ⟨⟨y, hyJ⟩ * a' * ⟨y, hyJ⟩⁻¹,
        Subgroup.mem_subgroupOf.2 (hfix _ (Subgroup.mem_subgroupOf.1 ha')), ?_⟩
      simp only [map_mul, map_inv]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fwd x, fun hx => ?_⟩
    have h1 := fwd _ hx
    have e : mkH (J0 z g) ⟨y, hyJ⟩ * (mkH (J0 z g) ⟨y, hyJ⟩ * x * (mkH (J0 z g) ⟨y, hyJ⟩)⁻¹) *
        (mkH (J0 z g) ⟨y, hyJ⟩)⁻¹ = x := by
      have e1 : mkH (J0 z g) ⟨y, hyJ⟩ * (mkH (J0 z g) ⟨y, hyJ⟩ * x * (mkH (J0 z g) ⟨y, hyJ⟩)⁻¹) *
          (mkH (J0 z g) ⟨y, hyJ⟩)⁻¹ = (mkH (J0 z g) ⟨y, hyJ⟩ * mkH (J0 z g) ⟨y, hyJ⟩) * x *
          (mkH (J0 z g) ⟨y, hyJ⟩ * mkH (J0 z g) ⟨y, hyJ⟩)⁻¹ := by group
      rw [e1, hybar]; simp
    rwa [e] at h1
  set F₂ : Subgroup G := F20 z ⊓ H0 z g with hF₂
  have hF₂z : ∀ f ∈ F₂, f * z = z * f := fun f hf =>
    Subgroup.mem_centralizer_singleton_iff.1
      ((Subgroup.map_subtype_le _ : OddCore z ≤ Cen z) (F20_le_OddCore z hf.1))
  have hF₂H : F₂ ≤ H0 z g := inf_le_right
  have hF₂odd : Odd (Nat.card ↥F₂) :=
    Odd.of_dvd_nat (odd_card_F20 z) (Subgroup.card_dvd_of_le inf_le_left)
  have hnorm : ∀ c ∈ Cen z, c ∈ H0 z g → ∀ f ∈ F₂, c * f * c⁻¹ ∈ F₂ := fun c hc hcH f hf =>
    ⟨F20_conj_mem z hc hf.1, (H0 z g).mul_mem ((H0 z g).mul_mem hcH hf.2) ((H0 z g).inv_mem hcH)⟩
  have hcent := hconcl.cent (Yimg hJle hJH F₂) (Yimg_le_range hJle hJH F₂)
    (Yimg_fix hJle hJH hJ.z_mem hF₂z) (Yimg_norm hJle hJH hJ.z_mem hz2 hnorm)
    (Yimg_odd hJle hJH hF₂H hF₂odd)
  have hcomm : ∀ f ∈ F₂, f * y * f⁻¹ * y⁻¹ ∈ pPrimeCoreOf 2 (J0 z g) := by
    intro f hf
    have hfH : f ∈ H0 z g := hf.2
    have hβ : actB hJle hJH ⟨f, hfH⟩ ∈ Yimg hJle hJH F₂ :=
      ⟨⟨f, hfH⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
    have h1 := hcent _ hβ _ hN
    rw [actB_mk] at h1
    have h2 : mkH (J0 z g) (⟨f * y * f⁻¹, hJH f hfH y hyJ⟩ * (⟨y, hyJ⟩ : ↥(J0 z g))⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]; simp
    exact ⟨_, (mkH_eq_one_iff (J0 z g)).1 h2, rfl⟩
  have hcommF₀ : ∀ f ∈ F₂, f * y * f⁻¹ * y⁻¹ ∈ F0 z g := by
    intro f hf
    have hcF : f * y * f⁻¹ * y⁻¹ ∈ F20 z := by
      have h := F20_conj_mem z hyC ((F20 z).inv_mem hf.1)
      have e : f * y * f⁻¹ * y⁻¹ = f * (y * f⁻¹ * y⁻¹) := by group
      rw [e]; exact (F20 z).mul_mem hf.1 h
    exact hF1 ⟨hcF, pPrimeCoreOf_le_of_normal hJle hJH (hcomm f hf)⟩
  have hyN : ∀ f ∈ F20 z ⊓ normalizer ((F0 z g : Subgroup G) : Set G), y * f = f * y := by
    intro f hf
    have hfF₂ : f ∈ F₂ := ⟨hf.1, hf.2⟩
    have hcF : f * y * f⁻¹ * y⁻¹ ∈ F20 z := by
      have h := F20_conj_mem z hyC ((F20 z).inv_mem hf.1)
      have e : f * y * f⁻¹ * y⁻¹ = f * (y * f⁻¹ * y⁻¹) := by group
      rw [e]; exact (F20 z).mul_mem hf.1 h
    exact commute_of_inv_conj hysq (odd_card_F20 z) hcF (hy0 _ (hcommF₀ f hfF₂))
  have hF₀ : F0 z g ≤ F20 z := fun x hx => hx.1
  exact (l2011_centralizes_A z hF₀ hyC hysq hy0 hyN a ha).symm

end CentA2

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2011

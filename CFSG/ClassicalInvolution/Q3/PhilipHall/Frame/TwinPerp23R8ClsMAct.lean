module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamData
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E7
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8YGamLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.YGam

section Action

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {c : Y}
  (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))

@[expose] noncomputable def conjH (g : ↥(Subgroup.centralizer ({c} : Set Y))) (h : ↥(coreHull Ω c)) :
    ↥(coreHull Ω c) :=
  ⟨g * (h : ↥(Subgroup.centralizer ({c} : Set Y))) * g⁻¹,
    (TwinExitPf6.normal_coreHull hΩ hc2).conj_mem _ h.2 g⟩

theorem hcoeHom_conjH (g : ↥(Subgroup.centralizer ({c} : Set Y))) (h : ↥(coreHull Ω c)) :
    hcoeHom Ω c (conjH hΩ hc2 g h) = (g : Y) * hcoeHom Ω c h * (g : Y)⁻¹ := rfl

theorem secAut_mk' (g : ↥(Subgroup.centralizer ({c} : Set Y))) (h : ↥(coreHull Ω c)) :
    TwinExitPf6.secAut Ω c hΩ hc2 g (QuotientGroup.mk h) = QuotientGroup.mk (conjH hΩ hc2 g h) :=
  TwinExitPf6.secAut_mk hΩ hc2 g h _ rfl

theorem secAut_one (z : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    TwinExitPf6.secAut Ω c hΩ hc2 1 z = z := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  rw [secAut_mk']
  congr 1
  exact Subtype.ext (by simp [conjH])

theorem secAut_mul (g₁ g₂ : ↥(Subgroup.centralizer ({c} : Set Y)))
    (z : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    TwinExitPf6.secAut Ω c hΩ hc2 (g₁ * g₂) z =
      TwinExitPf6.secAut Ω c hΩ hc2 g₁ (TwinExitPf6.secAut Ω c hΩ hc2 g₂ z) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  rw [secAut_mk', secAut_mk', secAut_mk']
  congr 1
  apply Subtype.ext
  show (g₁ * g₂ * (h : ↥(Subgroup.centralizer ({c} : Set Y))) * (g₁ * g₂)⁻¹ :
      ↥(Subgroup.centralizer ({c} : Set Y))) = g₁ * (g₂ * h * g₂⁻¹) * g₁⁻¹
  group

theorem secAut_iterate (g : ↥(Subgroup.centralizer ({c} : Set Y))) (j : ℕ)
    (z : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    ((TwinExitPf6.secAut Ω c hΩ hc2 g : _ ≃* _) : _ → _)^[j] z =
      TwinExitPf6.secAut Ω c hΩ hc2 (g ^ j) z := by
  induction j generalizing z with
  | zero => simp [secAut_one hΩ hc2]
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ', secAut_mul hΩ hc2]

theorem secAut_eq_of_comm (g : ↥(Subgroup.centralizer ({c} : Set Y))) (h : ↥(coreHull Ω c))
    (hg : (g : Y) * hcoeHom Ω c h = hcoeHom Ω c h * (g : Y)) :
    TwinExitPf6.secAut Ω c hΩ hc2 g (QuotientGroup.mk h) = QuotientGroup.mk h := by
  rw [secAut_mk']
  congr 1
  apply hcoeHom_injective Ω c
  rw [hcoeHom_conjH, hg]
  group

theorem inv_mul_mem_oddCore_of_eq (g₁ g₂ : ↥(Subgroup.centralizer ({c} : Set Y))) (h : ↥(coreHull Ω c))
    (hg : TwinExitPf6.secAut Ω c hΩ hc2 g₁ (QuotientGroup.mk h) =
      TwinExitPf6.secAut Ω c hΩ hc2 g₂ (QuotientGroup.mk h)) :
    ((g₁ : Y) * hcoeHom Ω c h * (g₁ : Y)⁻¹)⁻¹ * ((g₂ : Y) * hcoeHom Ω c h * (g₂ : Y)⁻¹) ∈
      oddCoreOf (Subgroup.centralizer ({c} : Set Y)) := by
  rw [secAut_mk', secAut_mk'] at hg
  have hmem : (conjH hΩ hc2 g₁ h)⁻¹ * conjH hΩ hc2 g₂ h ∈
      classicalInvolutionOddCore ↥(coreHull Ω c) := QuotientGroup.eq.mp hg
  have h2 := TwinExitPf6.mem_oddCore_of_mem_oddCore_coreHull hΩ hc2 hmem
  exact ⟨_, h2, rfl⟩

end Action

section Odd

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_mem_conj_of_odd {N : Subgroup Y} (hN : Odd (Nat.card N)) {a b : Y} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a⁻¹ * b ∈ N) : ∃ v ∈ N, a = v * b * v⁻¹ := by
  obtain ⟨v, hv, hva⟩ := exists_conj_zpowers_of_mul_mem_odd hN ha hb hab
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  rw [hainv] at hab
  exact ⟨v, Subgroup.zpowers_le.mpr hab hv, hva⟩

theorem inv_mul_mem_oddCore {t u e : Y} (he2 : e * e = 1)
    (heC : e ∈ Subgroup.centralizer ({t} : Set Y))
    (hAB : ∀ a ∈ p23ABar t 1 e, ∀ b ∈ p23ABar t 1 e, a * b = b * a) {c₁ c₂ : Y}
    (h₁ : c₁ ∈ Subgroup.centralizer ({t} : Set Y)) (h₂ : c₂ ∈ Subgroup.centralizer ({t} : Set Y))
    (hw : (c₁ * e * c₁⁻¹)⁻¹ * (c₂ * e * c₂⁻¹) ∈ oddCoreOf (Subgroup.centralizer ({u} : Set Y))) :
    (c₁ * e * c₁⁻¹)⁻¹ * (c₂ * e * c₂⁻¹) ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hmem : ∀ c ∈ C, c * e * c⁻¹ ∈ C := fun c hc => C.mul_mem (C.mul_mem hc heC) (C.inv_mem hc)
  set a : ↥C := ⟨c₁ * e * c₁⁻¹, hmem c₁ h₁⟩ with ha
  set b : ↥C := ⟨c₂ * e * c₂⁻¹, hmem c₂ h₂⟩ with hb
  have hpa : F7I.piC C a ∈ p23ABar t 1 e :=
    Subgroup.subset_closure ⟨a, ⟨c₁, h₁, by simp [ha]⟩, rfl⟩
  have hpb : F7I.piC C b ∈ p23ABar t 1 e :=
    Subgroup.subset_closure ⟨b, ⟨c₂, h₂, by simp [hb]⟩, rfl⟩
  have hab := hAB _ hpa _ hpb
  have hsq : ∀ c : Y, c * e * c⁻¹ * (c * e * c⁻¹) = 1 := fun c => by
    calc c * e * c⁻¹ * (c * e * c⁻¹) = c * (e * e) * c⁻¹ := by group
      _ = 1 := by rw [he2]; group
  have ha2 : a * a = 1 := Subtype.ext (hsq c₁)
  have hb2 : b * b = 1 := Subtype.ext (hsq c₂)
  have hpa2 : F7I.piC C a * F7I.piC C a = 1 := by rw [← map_mul, ha2, map_one]
  have hpb2 : F7I.piC C b * F7I.piC C b = 1 := by rw [← map_mul, hb2, map_one]
  have hainv : (F7I.piC C a)⁻¹ = F7I.piC C a := inv_eq_of_mul_eq_one_right hpa2
  have hw2 : (F7I.piC C (a⁻¹ * b)) ^ 2 = 1 := by
    rw [map_mul, map_inv, hainv, pow_two]
    calc F7I.piC C a * F7I.piC C b * (F7I.piC C a * F7I.piC C b)
        = F7I.piC C a * (F7I.piC C b * F7I.piC C a) * F7I.piC C b := by group
      _ = F7I.piC C a * (F7I.piC C a * F7I.piC C b) * F7I.piC C b := by rw [hab]
      _ = (F7I.piC C a * F7I.piC C a) * (F7I.piC C b * F7I.piC C b) := by group
      _ = 1 := by rw [hpa2, hpb2, one_mul]
  have hwY : ((a⁻¹ * b : ↥C) : Y) = (c₁ * e * c₁⁻¹)⁻¹ * (c₂ * e * c₂⁻¹) := rfl
  have hodd : Odd (orderOf ((a⁻¹ * b : ↥C) : Y)) := by
    rw [hwY]
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.orderOf_dvd_natCard _ hw)
  obtain ⟨j, hj⟩ := hodd
  have hpow : (a⁻¹ * b) ^ orderOf ((a⁻¹ * b : ↥C) : Y) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow]
    exact pow_orderOf_eq_one _
  have h1 : F7I.piC C (a⁻¹ * b) = 1 := by
    have h2 : (F7I.piC C (a⁻¹ * b)) ^ orderOf ((a⁻¹ * b : ↥C) : Y) = 1 := by
      rw [← map_pow, hpow, map_one]
    rw [hj, pow_succ, pow_mul, hw2, one_pow, one_mul] at h2
    exact h2
  exact (F7I.piC_eq_one_iff _).mp h1

theorem exists_lift {t u m : Y} (hu2 : u * u = 1) (huC : u ∈ Subgroup.centralizer ({t} : Set Y))
    (hmC : m ∈ Subgroup.centralizer ({t} : Set Y))
    (hcomm : m * u * m⁻¹ * u⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y))) :
    ∃ v ∈ oddCoreOf (Subgroup.centralizer ({t} : Set Y)), ∃ m' ∈ Subgroup.centralizer ({t} : Set Y),
      m' * u = u * m' ∧ m = v * m' := by
  set C := Subgroup.centralizer ({t} : Set Y) with hC
  have hN : Odd (Nat.card (classicalInvolutionOddCore ↥C)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥C
  have h1 : F7I.piC C ((⟨m, hmC⟩ : ↥C) * ⟨u, huC⟩ * (⟨m, hmC⟩ : ↥C)⁻¹ * (⟨u, huC⟩ : ↥C)⁻¹) = 1 :=
    (F7I.piC_eq_one_iff _).mpr hcomm
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have hc : (QuotientGroup.mk (⟨m, hmC⟩ : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) *
      QuotientGroup.mk (⟨u, huC⟩ : ↥C) =
      QuotientGroup.mk (⟨u, huC⟩ : ↥C) * QuotientGroup.mk (⟨m, hmC⟩ : ↥C) := by
    change F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨u, huC⟩ = F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩
    calc F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨u, huC⟩
        = (F7I.piC C ⟨m, hmC⟩ * F7I.piC C ⟨u, huC⟩ * (F7I.piC C ⟨m, hmC⟩)⁻¹ *
            (F7I.piC C ⟨u, huC⟩)⁻¹) * (F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩) := by group
      _ = F7I.piC C ⟨u, huC⟩ * F7I.piC C ⟨m, hmC⟩ := by rw [h1, one_mul]
  obtain ⟨v, hvN, hvC⟩ := YGam.exists_mem_centralizer_of_quot_comm hN (x := ⟨u, huC⟩) (h := ⟨m, hmC⟩)
    (Subtype.ext hu2) hc
  have hcomm' := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hvC)
  refine ⟨(v : Y), ⟨v, hvN, rfl⟩, ((v⁻¹ * ⟨m, hmC⟩ : ↥C) : Y), (v⁻¹ * ⟨m, hmC⟩ : ↥C).2, hcomm', ?_⟩
  show m = (v : Y) * ((v : Y)⁻¹ * m)
  rw [mul_inv_cancel_left]

end Odd

section Conj

variable {Y : Type} [Group Y] [Finite Y] {Ω : Set (Subgroup Y)} {u : Y}
  (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers u))

theorem conj_inv_mul_eq {e g₁ g₂ : Y} (h₁ : g₁ * u = u * g₁) (h₂ : g₂ * u = u * g₂) :
    (g₁ * (u * e) * g₁⁻¹)⁻¹ * (g₂ * (u * e) * g₂⁻¹) = (g₁ * e * g₁⁻¹)⁻¹ * (g₂ * e * g₂⁻¹) := by
  have key : ∀ g : Y, g * u = u * g → g * (u * e) * g⁻¹ = u * (g * e * g⁻¹) := fun g hg => by
    calc g * (u * e) * g⁻¹ = (g * u) * e * g⁻¹ := by group
      _ = (u * g) * e * g⁻¹ := by rw [hg]
      _ = u * (g * e * g⁻¹) := by group
  rw [key g₁ h₁, key g₂ h₂]
  group

include hΩ hc2 in
theorem act_conj {t e : Y} (x : ↥(coreHull Ω u)) (hx : hcoeHom Ω u x = u * e) (he2 : e * e = 1)
    (heC : e ∈ Subgroup.centralizer ({t} : Set Y))
    (hAB : ∀ a ∈ p23ABar t 1 e, ∀ b ∈ p23ABar t 1 e, a * b = b * a)
    (g₁ g₂ : ↥(Subgroup.centralizer ({u} : Set Y))) (h₁ : (g₁ : Y) ∈ Subgroup.centralizer ({t} : Set Y))
    (h₂ : (g₂ : Y) ∈ Subgroup.centralizer ({t} : Set Y))
    (heq : TwinExitPf6.secAut Ω u hΩ hc2 g₁ (QuotientGroup.mk x) =
      TwinExitPf6.secAut Ω u hΩ hc2 g₂ (QuotientGroup.mk x)) :
    ((g₁ : Y) * e * (g₁ : Y)⁻¹)⁻¹ * ((g₂ : Y) * e * (g₂ : Y)⁻¹) ∈
      oddCoreOf (Subgroup.centralizer ({t} : Set Y)) := by
  have h := inv_mul_mem_oddCore_of_eq hΩ hc2 g₁ g₂ x heq
  rw [hx, conj_inv_mul_eq (Subgroup.mem_centralizer_singleton_iff.mp g₁.2)
    (Subgroup.mem_centralizer_singleton_iff.mp g₂.2)] at h
  exact inv_mul_mem_oddCore he2 heC hAB h₁ h₂ h

end Conj

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.ClsM

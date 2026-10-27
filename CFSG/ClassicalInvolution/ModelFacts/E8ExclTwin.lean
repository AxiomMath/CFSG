module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclFrame
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Twin

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)

theorem neg_one_zpow_eq_of_emod {F : Type} [Field F] {a b : ℤ} (h : a % 2 = b % 2) :
    (-1 : Fˣ) ^ a = (-1) ^ b := by
  rcases Int.emod_two_eq_zero_or_one a with ha | ha
  · rw [ha] at h
    have ha' : Even a := Int.even_iff.2 ha
    have hb' : Even b := Int.even_iff.2 h.symm
    rw [ha'.neg_one_zpow, hb'.neg_one_zpow]
  · rw [ha] at h
    have ha' : Odd a := Int.odd_iff.2 ha
    have hb' : Odd b := Int.odd_iff.2 h.symm
    rw [ha'.neg_one_zpow, hb'.neg_one_zpow]

theorem thetaDiag_neg_one_eq_mul {δ γ₁ γ₂ : V7}
    (hpar : ∀ i : Fin (Tag.rank .E7), iform δ (Pi.single i 1) % 2 =
      (iform γ₁ (Pi.single i 1) + iform γ₂ (Pi.single i 1)) % 2) :
    thetaDiag δ (-1 : (GaloisField p f)ˣ) =
      thetaDiag γ₁ (-1 : (GaloisField p f)ˣ) * thetaDiag γ₂ (-1) := by
  funext i
  simp only [Pi.mul_apply, thetaDiag]
  rw [← zpow_add, neg_one_zpow_eq_of_emod (hpar i)]

theorem mul_inv_mul_mem_center (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {g : M₇} {γ₁ γ₂ ρ : V7}
    (hγ₁ : IsRoot .E7 γ₁) (hγ₂ : IsRoot .E7 γ₂) (hρ : IsRoot .E7 ρ)
    (hpar : ∀ i : Fin (Tag.rank .E7), iform ρ (Pi.single i 1) % 2 =
      (iform γ₁ (Pi.single i 1) + iform γ₂ (Pi.single i 1)) % 2) {r₁ r₂ r : M₇}
    (hr₁ : r₁ ∈ conjSub g (stdRankOne D₇ γ₁)) (hr₂ : r₂ ∈ conjSub g (stdRankOne D₇ γ₂))
    (hr : r ∈ conjSub g (stdRankOne D₇ ρ)) (ho₁ : orderOf r₁ = 2) (ho₂ : orderOf r₂ = 2)
    (ho : orderOf r = 2) : (r₁ * r₂)⁻¹ * r ∈ Subgroup.center M₇ := by
  obtain ⟨a₁, ha₁, rfl⟩ := Subgroup.mem_map.1 hr₁
  obtain ⟨a₂, ha₂, rfl⟩ := Subgroup.mem_map.1 hr₂
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hr
  have ord : ∀ b : M₇, orderOf ((MulAut.conj g).toMonoidHom b) = 2 → orderOf b = 2 := fun b hb => by
    rw [← hb]
    exact (orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective b).symm
  have o₁ := ord a₁ ho₁
  have o₂ := ord a₂ ho₂
  have o := ord a ho
  have h1 := εm_mul_involutions hp2 hq hγ₁ hγ₂ ha₁ ha₂ o₁ o₂
  have h2 := εm_involution_std hp2 hq hρ ha o
  have hker : (a₁ * a₂)⁻¹ * a ∈ (εm (GaloisField p f)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, thetaDiag_neg_one_eq_mul hpar,
      rootDiagUnit_mul]
    group
  have hc := εm_ker_le_center hker
  have e : ((MulAut.conj g).toMonoidHom a₁ * (MulAut.conj g).toMonoidHom a₂)⁻¹ *
      (MulAut.conj g).toMonoidHom a = g * ((a₁ * a₂)⁻¹ * a) * g⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e, mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_center_iff.mp hc g)]
  exact hc

theorem involution_central_fund (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {R : Subgroup M₇}
    (hR : R ∈ fundamentalSubgroups .E7 D₇) {r : M₇} (hr : r ∈ R) (h2 : orderOf r = 2) :
    ∀ a ∈ R, a * r = r * a := by
  intro a ha
  have hmem : a * r * a⁻¹ ∈ R := R.mul_mem (R.mul_mem ha hr) (R.inv_mem ha)
  have hord : orderOf (a * r * a⁻¹) = 2 := by
    rw [← h2]
    exact orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective r
  have := eq_of_orderOf_two_fund hp2 hq hR hmem hr hord h2
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

theorem le_centralizer_iff_of_mul_mem_center {G : Type*} [Group G] {A : Subgroup G} {a b : G}
    (h : a⁻¹ * b ∈ Subgroup.center G) :
    A ≤ Subgroup.centralizer ({a} : Set G) ↔ A ≤ Subgroup.centralizer ({b} : Set G) := by
  have hb : b = a * (a⁻¹ * b) := by group
  constructor
  · intro hA x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hA hx)
    have h2 := Subgroup.mem_center_iff.mp h x
    rw [hb]
    calc x * (a * (a⁻¹ * b)) = (x * a) * (a⁻¹ * b) := by group
      _ = (a * x) * (a⁻¹ * b) := by rw [h1]
      _ = a * (x * (a⁻¹ * b)) := by group
      _ = a * ((a⁻¹ * b) * x) := by rw [← h2]
      _ = (a * (a⁻¹ * b)) * x := by group
  · intro hA x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hA hx)
    have h3 := Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem h) x
    have hb' : a = b * (a⁻¹ * b)⁻¹ := by group
    rw [hb']
    calc x * (b * (a⁻¹ * b)⁻¹) = (x * b) * (a⁻¹ * b)⁻¹ := by group
      _ = (b * x) * (a⁻¹ * b)⁻¹ := by rw [h1]
      _ = b * (x * (a⁻¹ * b)⁻¹) := by group
      _ = b * ((a⁻¹ * b)⁻¹ * x) := by rw [h3]
      _ = (b * (a⁻¹ * b)⁻¹) * x := by group

end Twin

end CFSG.ClassicalInvolution.ModelFacts.E7Model

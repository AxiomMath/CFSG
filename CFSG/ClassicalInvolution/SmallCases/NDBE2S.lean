module

public import CFSG.ClassicalInvolution.SmallCases.NDBE0Stmt
public import CFSG.ClassicalInvolution.SmallCases.NDBE2SModel
import CFSG.ClassicalInvolution.SmallCases.NDBC7
import CFSG.ClassicalInvolution.SmallCases.NDBC4
import CFSG.ClassicalInvolution.SmallCases.NDB1Shape
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

section Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

structure ExoticCtxS (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (K : Subgroup G) (z : G) where
  hS : ExoticBase p f K z
  hnoT : ¬ HasTwin p f K z
  hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A
  D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z
  card_eq : D.card = 2
  i₀ : Fin D.card
  i₁ : Fin D.card
  ne : i₀ ≠ i₁
  tag₀ : D.tag i₀ = .PSL
  rank₀ : D.rank i₀ = 2
  tag₁ : ExoticModel.SpinTag (D.tag i₁) (D.rank i₁)
  K₀ : modOdd z (exactCore z K) =
    ((Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D).psi i₀).range

namespace ExoticCtxS

noncomputable abbrev X {K : Subgroup G} {z : G} (C : ExoticCtxS p f K z) :
    Asc77.XCtx p f (𝒞 K) z :=
  Cover.toXCtx C.hS.nonabelian C.hS.odd C.hS.five C.hS.member C.hS.below C.D

noncomputable abbrev psi {K : Subgroup G} {z : G} (C : ExoticCtxS p f K z) (j : Fin C.D.card) :
    (compModel C.D j).K →* OddQuot z :=
  C.X.psi j

end ExoticCtxS

end Ctx

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

namespace Exotic

theorem exists_exoticCtxS {K : Subgroup G} {z : G} (hS : ExoticBase p f K z)
    (hnoT : ¬ HasTwin p f K z) (hnoF : ∀ A : Subgroup G, ¬ Theorem5.FuzzyFrameOn p f (𝒞 K) A)
    (D : LocalLieSystemAt p f (exactFamily (𝒞 K) z) z)
    {i : Fin D.card} (hi : ExoticModel.SpinTag (D.tag i) (D.rank i)) :
    Nonempty (ExoticCtxS p f K z) := by
  set C₀ := Cover.toXCtx hS.nonabelian hS.odd hS.five hS.member hS.below D with hC₀
  have hQ : ¬ (D.tag i = .PSL ∧ D.rank i = 2) := hi.not_A1
  obtain ⟨i₀, hi₀, hK₀⟩ := C₀.exists_A1_of_K
  have hi₀i : i₀ ≠ i := fun h => hQ (h ▸ hi₀)
  have hcases : ∀ j, j = i₀ ∨ j = i := by
    intro j
    by_cases hji : j = i
    · exact Or.inr hji
    by_cases hj₀ : j = i₀
    · exact Or.inl hj₀
    have hjA : D.tag j = .PSL ∧ D.rank j = 2 := by
      by_contra h
      exact Cover.false_of_two_nonA1 C₀ hnoF hji h hQ
    obtain ⟨T, hT, hTK, hTz, -⟩ := Cover.A1_member_twin C₀ hnoF hQ hi₀ hK₀ hjA hj₀
    exact (hnoT ⟨T, hT, hTK, hTz⟩).elim
  exact ⟨⟨hS, hnoT, hnoF, D, Cover.card_eq_two_of hi₀i hcases, i₀, i, hi₀i, hi₀.1, hi₀.2, hi,
    hK₀⟩⟩

end Exotic

namespace ExoticCtxS


variable {K : Subgroup G} {z : G} (C : ExoticCtxS p f K z)

theorem eq_or_eq (j : Fin C.D.card) : j = C.i₀ ∨ j = C.i₁ := by
  have hne : C.i₀.val ≠ C.i₁.val := fun e => C.ne (Fin.ext e)
  have hc := C.card_eq
  have h0 := C.i₀.2
  have h1 := C.i₁.2
  have hj := j.2
  by_contra h
  push Not at h
  have a0 : j.val ≠ C.i₀.val := fun e => h.1 (Fin.ext e)
  have a1 : j.val ≠ C.i₁.val := fun e => h.2 (Fin.ext e)
  omega

theorem exp_eq : C.D.exp C.i₁ = f :=
  (C.D.exp_eq C.i₁).resolve_right fun h => C.tag₁.ne_D4 h.1

theorem five : 5 ≤ p ^ C.D.exp C.i₁ := by rw [C.exp_eq]; exact C.hS.five

theorem psi_injective : Function.Injective (C.psi C.i₁) := by
  have hp2 := C.hS.odd
  have hadm := C.D.admissible C.i₁
  have hperf := ExoticModel.spin_perfect hp2 (e := C.D.exp C.i₁) C.tag₁
  obtain ⟨R, hR, -, -, -⟩ := Cover.exists_member_of_meets C.X C.i₁
  obtain ⟨R', hR', hne, hc⟩ := ExoticModel.spin_twins hp2 C.five C.tag₁ hadm R hR
  have hz := Cover.zbar_mem_of_pair C.X (fun M hM => hM) C.hnoF C.hnoT C.tag₁.not_A1
    C.tag₁.ne_G2 C.tag₁.ne_D4 hR hR' hne hc
  obtain ⟨ε, hεZ, hε⟩ := Seed.exists_central_lift (C.psi C.i₁) (C.X.psi_ker C.i₁) hz
    (fun y _ => Cover.zbar_comm y)
  have hUK := C.X.isUniqueInvolution_modOdd C.X.K_tq C.X.K_cl
  have hz1 : oddQuotMk z ⟨z, Asc77.XCtx.hzC z⟩ ≠ 1 := hUK.ne_one
  have hε1 : ε ≠ 1 := fun h => hz1 (by rw [← hε, h, map_one])
  rw [injective_iff_map_eq_one]
  intro k hk
  by_contra hk1
  have hkZ := C.X.psi_ker C.i₁ (MonoidHom.mem_ker.mpr hk)
  have e := ExoticModel.spin_center_eq hp2 C.tag₁ k hkZ ε hεZ hk1 hε1
  rw [e, hε] at hk
  exact hz1 hk

theorem mem_center_of_comm {x : (compModel C.D C.i₁).K}
    (h : ∀ y : (compModel C.D C.i₁).K, C.psi C.i₁ x * C.psi C.i₁ y = C.psi C.i₁ y * C.psi C.i₁ x) :
    x ∈ Subgroup.center (compModel C.D C.i₁).K := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply C.psi_injective
  rw [map_mul, map_mul]
  exact (h y).symm

theorem ne_z_of_bar {a : G} (haC : a ∈ Subgroup.centralizer ({z} : Set G))
    {x : (compModel C.D C.i₁).K} (hx : oddQuotMk z ⟨a, haC⟩ = C.psi C.i₁ x)
    (hx1 : x ∉ Subgroup.center (compModel C.D C.i₁).K) : a ≠ z := by
  rintro rfl
  apply hx1
  apply C.mem_center_of_comm
  intro y
  rw [← hx]
  exact oddQuotMk_central haC _

theorem le_Q_of_bar {N : Subgroup G} (hN : N ∈ tqMembers (𝒞 K) z) {w : G}
    (hw : IsClassicalMember p f N w) {x : (compModel C.D C.i₁).K}
    (hx : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ = C.psi C.i₁ x)
    (hx1 : x ∉ Subgroup.center (compModel C.D C.i₁).K) :
    modOdd z (exactCore z N) ≤ (C.psi C.i₁).range := by
  obtain ⟨j, R, -, hRN⟩ := C.X.exists_fund_of_mem hN
  rcases C.eq_or_eq j with rfl | rfl
  · exfalso
    have hwN : oddQuotMk z ⟨w, C.X.involution_mem_centralizer hN hw⟩ ∈
        modOdd z (exactCore z N) :=
      oddQuotMk_mem_modOdd (C.X.involution_mem_exactCore hN hw) _
    rw [← hRN] at hwN
    obtain ⟨r, -, hr⟩ := hwN
    apply hx1
    apply C.mem_center_of_comm
    intro y
    rw [← hx, ← hr]
    exact C.X.psi_commute C.ne r y
  · rw [← hRN]
    exact Subgroup.map_le_range _ _

end ExoticCtxS

end CFSG.ClassicalInvolution.NDB

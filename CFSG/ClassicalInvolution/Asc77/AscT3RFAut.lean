module

public import CFSG.ClassicalInvolution.Asc77.AscT3RFix
public import CFSG.ClassicalInvolution.Asc77.AscT3RAct

public section

namespace CFSG.ClassicalInvolution.Asc77.T3CII.T3R

open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.GorensteinWalter
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open CFSG.RankThree.PartTwo.KFacts
open scoped MatrixGroups commutatorElement Pointwise

section Lift

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F]
  {L : Subgroup G} {e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)}

@[expose] def fiberEquiv (L : Subgroup G) (e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F))
    (k : ↥L) : {y : ↥L // eta L e y = eta L e k} ≃ ↥(classicalInvolutionOddCore ↥L) where
  toFun y := ⟨k⁻¹ * y, (eta_eq_one_iff L e _).mp (by rw [map_mul, map_inv, y.2, inv_mul_cancel])⟩
  invFun o := ⟨k * o, by rw [map_mul, (eta_eq_one_iff L e _).mpr o.2, mul_one]⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv o := by
    apply Subtype.ext
    simp

omit [Finite G] in
theorem natCard_fiber (k : ↥L) :
    Nat.card {y : ↥L // eta L e y = eta L e k} = Nat.card ↥(classicalInvolutionOddCore ↥L) :=
  Nat.card_congr (fiberEquiv L e k)

theorem exists_fixed_lift {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) (n : ℕ)
    (hn : a ^ (2 ^ n) = 1) {x : SL(2, F)} (hx : phiG L e a x = x) :
    ∃ y : ↥L, eta L e y = x ∧ a * (y : G) * a⁻¹ = y := by
  classical
  obtain ⟨k, rfl⟩ := eta_surjective L e x
  set c : Equiv.Perm ↥L := MulAut.toPerm ↥L (normalizerConj L ⟨a, haN⟩) with hc
  have hcy : ∀ y : ↥L, ((c y : ↥L) : G) = a * (y : G) * a⁻¹ := fun y => rfl
  have hceta : ∀ y : ↥L, eta L e (c y) = phiG L e a (eta L e y) := by
    intro y
    rw [phiG_apply_eta haN]
    rfl
  have hp : ∀ y : ↥L, eta L e (c y) = eta L e k ↔ eta L e y = eta L e k := by
    intro y
    rw [hceta]
    constructor
    · intro h
      apply (phiG L e a).injective
      rw [h, hx]
    · intro h
      rw [h, hx]
  set σ : Equiv.Perm {y : ↥L // eta L e y = eta L e k} := c.subtypePerm hp with hσ
  have hc1 : c ^ (2 ^ n) = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ (2 ^ n) = 1 :=
      Subtype.ext (by simpa using hn)
    rw [hc, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσ1 : σ ^ 2 ^ n = 1 := by
    rw [hσ, Equiv.Perm.subtypePerm_pow]
    apply Equiv.ext
    intro y
    apply Subtype.ext
    simp [Equiv.Perm.subtypePerm_apply, hc1]
  have : Fintype {y : ↥L // eta L e y = eta L e k} := Fintype.ofFinite _
  have hodd : ¬ 2 ∣ Fintype.card {y : ↥L // eta L e y = eta L e k} := by
    rw [← Nat.card_eq_fintype_card, natCard_fiber]
    intro hd
    exact (Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card ↥L))
      (even_iff_two_dvd.mpr hd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hs⟩ := Equiv.Perm.exists_fixed_point_of_prime hodd hσ1
  refine ⟨s.1, s.2, ?_⟩
  have h1 : ((σ s : {y : ↥L // eta L e y = eta L e k}) : ↥L) = s.1 := by rw [hs]
  have h2 : ((σ s : {y : ↥L // eta L e y = eta L e k}) : ↥L) = c s.1 := rfl
  have h3 : ((c s.1 : ↥L) : G) = (s.1 : G) := by rw [← h2, h1]
  rw [← hcy]
  exact h3

theorem range_eta_centralizer {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G)) {n : ℕ}
    (hn : a ^ (2 ^ n) = 1) :
    ((eta L e).comp ((L ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf L).subtype).range =
      fixSub (phiG L e a) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    have hyc : (y : G) * a = a * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (show (y : G) ∈ Subgroup.centralizer {a} from hy.2)
    show phiG L e a (eta L e y) = eta L e y
    rw [phiG_apply_eta haN]
    congr 1
    apply Subtype.ext
    show a * (y : G) * a⁻¹ = y
    rw [← hyc]
    group
  · intro hx
    obtain ⟨y, hyx, hya⟩ := exists_fixed_lift haN n hn (show phiG L e a x = x from hx)
    refine ⟨⟨y, ?_⟩, hyx⟩
    refine ⟨y.2, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (y : G) * a = (a * (y : G) * a⁻¹) * a := by rw [hya]
      _ = a * (y : G) := by group

theorem odd_natCard_ker_of_le {H : Subgroup G} :
    Odd (Nat.card ((eta L e).comp (H.subgroupOf L).subtype).ker) := by
  set φ : ↥(H.subgroupOf L) →* SL(2, F) := (eta L e).comp (H.subgroupOf L).subtype with hφ
  have hle : φ.ker.map (H.subgroupOf L).subtype ≤ classicalInvolutionOddCore ↥L := by
    rintro _ ⟨x, hx, rfl⟩
    exact (eta_eq_one_iff L e _).mp hx
  have h1 : Nat.card (φ.ker.map (H.subgroupOf L).subtype) = Nat.card φ.ker :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have h2 := Subgroup.card_dvd_of_le hle
  rw [h1] at h2
  exact (CFSG.ComponentClassification.OddCore.odd_card ↥L).of_dvd_nat h2

end Lift

section Main

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
  {L : Subgroup G} {e : ↥L ⧸ classicalInvolutionOddCore ↥L ≃* SL(2, F)}

theorem field_involution_data (hF : Odd (Nat.card F)) {σ : F ≃+* F} (hσ2 : σ * σ = 1)
    (hσ1 : σ ≠ 1) {γ : MulAut SL(2, F)} {a : G} (haN : a ∈ Subgroup.normalizer (L : Set G))
    {n : ℕ} (hn : a ^ (2 ^ n) = 1) (hγ : phiG L e a = γ * slFieldAut F σ * γ⁻¹)
    {RL : Subgroup G} (hRL : IsSylow2In RL L) :
    a * a ∈ cStar L ∧
      ∃ P : Subgroup G, IsSylow2In P (L ⊓ Subgroup.centralizer ({a} : Set G)) ∧
        (∃ k : ℕ, 1 ≤ k ∧ Nonempty (↥P ≃* QuaternionGroup (2 ^ k))) ∧
          2 * Nat.card P = Nat.card RL := by
  classical
  have hσfsq : slFieldAut F σ * slFieldAut F σ = 1 := by
    rw [← slFieldAut_mul, hσ2, slFieldAut_one]
  have hi2 : phiG L e a * phiG L e a = 1 := by
    rw [hγ]
    calc γ * slFieldAut F σ * γ⁻¹ * (γ * slFieldAut F σ * γ⁻¹)
        = γ * (slFieldAut F σ * slFieldAut F σ) * γ⁻¹ := by group
      _ = 1 := by rw [hσfsq]; group
  refine ⟨(phiG_eq_one_iff (L := L) (e := e) (Subgroup.mul_mem _ haN haN)).mp
    (by rw [phiG_mul haN haN]; exact hi2), ?_⟩
  set H : Subgroup G := L ⊓ Subgroup.centralizer ({a} : Set G) with hH
  have hHL : H ≤ L := inf_le_left
  obtain ⟨P, hP, -⟩ := IsSylow2In.exists_ge (P := H) (T := ⊥) IsPGroup.of_bot bot_le
  have hPL : P ≤ L := hP.1.trans hHL
  set g : ↥P →* SL(2, F) := (eta L e).comp (Subgroup.inclusion hPL) with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : eta L e (Subgroup.inclusion hPL x) = 1 := hx
    have hxO := (eta_eq_one_iff L e _).mp hx'
    have hxG : ((x : P) : G) ∈ oddCoreOf L := ⟨Subgroup.inclusion hPL x, hxO, rfl⟩
    have hx2 : IsPGroup 2 (Subgroup.zpowers ((x : P) : G)) :=
      hP.2.1.to_le (Subgroup.zpowers_le.mpr x.2)
    have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard L) hxG hx2
    exact Subtype.ext this
  have hfix : g.range ≤ fixSub (phiG L e a) := by
    rintro _ ⟨x, rfl⟩
    rw [← range_eta_centralizer haN hn]
    exact ⟨⟨⟨(x : G), hPL x.2⟩, hP.1 x.2⟩, rfl⟩
  have hHcard : Nat.card H = Nat.card (fixSub (phiG L e a)) *
      Nat.card ((eta L e).comp (H.subgroupOf L).subtype).ker := by
    have h1 := Subgroup.card_ker_mul_card_range ((eta L e).comp (H.subgroupOf L).subtype)
    rw [range_eta_centralizer haN hn,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv] at h1
    rw [← h1, mul_comm]
  have hfac : (Nat.card H).factorization 2 = (Nat.card (fixSub (phiG L e a))).factorization 2 := by
    have hodd := odd_natCard_ker_of_le (e := e) (H := H)
    have : (Nat.card ((eta L e).comp (H.subgroupOf L).subtype).ker).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd))
    rw [hHcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, this,
      add_zero]
  have hPcard : Nat.card P = 2 ^ (Nat.card (fixSub (phiG L e a))).factorization 2 := by
    rw [natCard_isSylow2In hP, hfac]
  have hrcard : Nat.card g.range = Nat.card P :=
    (Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv).symm
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 SL(2, F)))
  rw [hγ] at hfix hPcard
  obtain ⟨⟨k, hk, ⟨eq⟩⟩, h2⟩ := quaternion_of_sylow_fix hF hσ2 hσ1 γ hfix
    (hrcard.trans hPcard) Q
  refine ⟨P, hP, ⟨k, hk, ⟨(MonoidHom.ofInjective hginj).trans eq⟩⟩, ?_⟩
  rw [natCard_isSylow2In_eq_natCard_sylow (e := e) Q hRL, ← h2, hrcard]

end Main

end CFSG.ClassicalInvolution.Asc77.T3CII.T3R

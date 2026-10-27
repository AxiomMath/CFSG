module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR14
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR13

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS
open CFSG.Walter.Huppert
open scoped commutatorElement

theorem hasDihedralSylowTwo_of_kBar {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (h : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J)) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (CFSG.ABGDGroups.hasDihedralSylowTwo_iff_of_surjective
    (π := QuotientGroup.mk' (pPrimeCore 2 ↥J)) (QuotientGroup.mk'_surjective _) ?_).1 h
  rw [QuotientGroup.ker_mk']
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem dihedralData_of_hasDihedralSylowTwo {X : Type} [Group X] [Finite X]
    (h : CFSG.GorensteinWalter.HasDihedralSylowTwo X) :
    ∃ (S : Sylow 2 X) (n : ℕ), 2 ≤ n ∧ Nonempty (DihedralGroup (2 ^ (n - 1)) ≃* (S : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  obtain ⟨m, hm, ⟨e⟩⟩ := h S
  exact ⟨S, m + 1, by omega, ⟨by simpa using e.symm⟩⟩

section Main

variable {G : Type} [Group G] [Finite G]

theorem p79_of_cbar_of_lift {J B V Hc : Subgroup G} {b x : G} (hperf : Group.IsPerfect ↥J)
    (hsimple : IsSimpleGroup (kBar J)) (hnqs : ¬ CFSG.IsQuasisimple ↥J)
    (hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J))
    (hJH : J ≤ Hc) (hOH : pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 Hc)
    (hBN : B ≤ normalizer (J : Set G)) (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hVB : V ≤ B) (hrk : 3 ≤ pRank 2 ↥V) (hbB : b ∈ B)
    {c : kBar J} (hcp : Nat.Prime (orderOf c))
    (hxJ : x ∈ J) (hxc : (QuotientGroup.mk (⟨x, hxJ⟩ : ↥J) : kBar J) = c)
    (hxodd : Odd (orderOf x))
    (hVx : ∀ v ∈ V, v * x = x * v) (hbx : b * x * b⁻¹ = x⁻¹) :
    ∃ (W X₀ X₁ : Subgroup G), X₁ = Subgroup.zpowers x ∧ W ≤ V ∧
      Nat.card V = 2 * Nat.card W ∧
      Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧ X₀ ≤ pPrimeCoreOf 2 Hc ∧ X₁ ≤ Hc ∧
      (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
      (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
      (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
      ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
        (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxO : x ∉ pPrimeCoreOf 2 J := by
    intro hxO
    obtain ⟨hxJ', hmem⟩ := C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 hxO
    have h1 : (QuotientGroup.mk (⟨x, hxJ⟩ : ↥J) : kBar J) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    rw [hxc] at h1
    rw [h1, orderOf_one] at hcp
    exact Nat.not_prime_one hcp
  obtain ⟨p, hp, hp2, w, hw, hxw⟩ := exists_prime_noncentral hperf hsimple hnqs hxJ hxO
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := Pp J p with hPdef
  have hP : IsPGroup p ↥P := Pp_isPGroup J p
  have hJN : ∀ j ∈ J, j ∈ normalizer (P : Set G) := fun j hj =>
    mem_normalizer_Pp (Subgroup.le_normalizer hj)
  have hxN : x ∈ normalizer (P : Set G) := hJN x hxJ
  let ρ : ↥J →* MulAut ↥P :=
    P.normalizerMonoidHom.comp (Subgroup.inclusion (fun j hj => hJN j hj : J ≤ normalizer (P : Set G)))
  have hρ : ∀ (j : ↥J), ρ j = P.normalizerMonoidHom ⟨(j : G), hJN j j.2⟩ := fun j => rfl
  have hdihJ := dihedralData_of_hasDihedralSylowTwo (hasDihedralSylowTwo_of_kBar hdih)
  have hstab : PStableAct p ((frattiniAut ↥P).comp ρ) :=
    pStableAct_of_dihedral hdihJ hp (Nat.Prime.odd_of_ne_two hp hp2) (hP.to_quotient _) _
  have : Group.IsPerfect ↥J := hperf
  have hOodd : Odd (Nat.card (pPrimeCore 2 ↥J)) := Nat.coprime_two_left.1 pPrimeCore_coprime_card
  have hxO' : (⟨x, hxJ⟩ : ↥J)⁻¹ ∉ pPrimeCore 2 ↥J := by
    intro h
    exact hxO (C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hxJ, by simpa using h⟩)
  have hx1 : ρ (⟨x, hxJ⟩ : ↥J)⁻¹ ≠ 1 := by
    intro h
    apply hxw
    have h1 := congrArg (fun φ : MulAut ↥P => ((φ ⟨w, hw⟩ : ↥P) : G)) h
    simp only [hρ, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
      Subgroup.coe_inv, inv_inv] at h1
    have h2 : x⁻¹ * w * x = w := h1
    calc x * w = x * (x⁻¹ * w * x) := by rw [h2]
      _ = w * x := by group
  obtain ⟨z, hz⟩ := exists_not_quadratic_frattini hOodd hsimple hP ρ hstab hxO' hx1
  rw [inv_inv] at hz
  have hnq : NQ hP ⟨x, hxN⟩ z := by
    intro h
    apply hz
    rw [nuP_mk] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  obtain ⟨W, X₀, X₁, hX₁eq, hW⟩ := p79_assemble (P := P) (V := V) (B := B) (Hc := Hc) hP hp2
    ((Pp_le_O J p).trans hOH) (hJH hxJ) hxN (fun g hg => mem_normalizer_Pp (hBN hg)) hBel hVB hrk
    hVx hbx hxodd hnq
  exact ⟨W, X₀, X₁, hX₁eq, hW⟩

theorem p79_of_cbar {J B V Hc : Subgroup G} {b : G} (hperf : Group.IsPerfect ↥J)
    (hsimple : IsSimpleGroup (kBar J)) (hnqs : ¬ CFSG.IsQuasisimple ↥J)
    (hdih : CFSG.GorensteinWalter.HasDihedralSylowTwo (kBar J))
    (hJH : J ≤ Hc) (hOH : pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 Hc)
    (hBN : B ≤ normalizer (J : Set G)) (hBel : CFSG.IsElementaryAbelian 2 ↥B)
    (hVB : V ≤ B) (hrk : 3 ≤ pRank 2 ↥V) (hbB : b ∈ B)
    {c : kBar J} (hcp : Nat.Prime (orderOf c)) (hcodd : Odd (orderOf c))
    (hVc : ∀ v (hv : v ∈ V), barAct J ⟨v, hBN (hVB hv)⟩ c = c)
    (hbc : barAct J ⟨b, hBN hbB⟩ c = c⁻¹) :
    ∃ (W X₀ X₁ : Subgroup G), W ≤ V ∧ Nat.card V = 2 * Nat.card W ∧
      Odd (Nat.card X₀) ∧ Odd (Nat.card X₁) ∧ X₀ ≤ pPrimeCoreOf 2 Hc ∧ X₁ ≤ Hc ∧
      (∀ w ∈ W, ∀ z ∈ X₀, w * z = z * w) ∧ (∀ v ∈ V, ∀ z ∈ X₁, v * z = z * v) ∧
      (∀ g ∈ B, ∀ z ∈ X₀, g * z * g⁻¹ ∈ X₀) ∧ (∀ z ∈ X₁, ∀ z' ∈ X₀, z * z' * z⁻¹ ∈ X₀) ∧
      (∀ z ∈ X₁, b * z * b⁻¹ = z⁻¹) ∧ ⁅⁅X₀, X₁⁆, X₁⁆ ≠ ⊥ ∧
      ((∀ v ∈ V, ∀ z ∈ X₀, v * z = z * v) ∨
        (∀ v ∈ V, v ∉ W → ∃ z ∈ ⁅⁅X₀, X₁⁆, X₁⁆, v * z ≠ z * v)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hxJ, hxc, ⟨k, hxk⟩, hVx, hbx⟩ := exists_lift_pElement hBN hBel hVB hbB hcp hVc hbc
  have hxodd : Odd (orderOf x) :=
    Odd.of_dvd_nat (Odd.pow hcodd) (orderOf_dvd_of_pow_eq_one hxk)
  obtain ⟨W, X₀, X₁, -, hW⟩ :=
    p79_of_cbar_of_lift hperf hsimple hnqs hdih hJH hOH hBN hBel hVB hrk hbB hcp
      hxJ hxc hxodd hVx hbx
  exact ⟨W, X₀, X₁, hW⟩

end Main

end CFSG.GH74.GLS.Th2.Obs

module

public import CFSG.GH74.GLS.C3.Layer1.Thm1G33Vi

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.C3.Layer1.Thm1G33

section PureAb

theorem exists_hom_kills_odd {A : Type*} [Group A] [Finite A] (hA : ∀ a b : A, a * b = b * a) :
    ∃ κ : A →* A, (∀ a : A, Odd (orderOf a) → κ a = 1) ∧
      (∀ a : A, orderOf a = 2 → κ a = a) ∧ (∀ a : A, ∃ s : ℕ, κ a ^ (2 ^ s) = 1) := by
  classical
  have hn0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, m, hmodd, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨MonoidHom.mk' (fun a => a ^ m) (fun a b => Commute.mul_pow (hA a b) m), ?_, ?_, ?_⟩
  · intro a ha
    show a ^ m = 1
    rw [← orderOf_dvd_iff_pow_eq_one]
    have h1 : orderOf a ∣ 2 ^ s * m := hnm ▸ orderOf_dvd_natCard a
    have hcop : Nat.Coprime (orderOf a) (2 ^ s) :=
      Nat.Coprime.pow_right s (Nat.coprime_two_right.2 ha)
    exact hcop.dvd_of_dvd_mul_left h1
  · intro a ha
    show a ^ m = a
    obtain ⟨j, hj⟩ := hmodd
    have h2 : a ^ 2 = 1 := by
      have := pow_orderOf_eq_one a
      rwa [ha] at this
    rw [hj, pow_succ, pow_mul, h2, one_pow, one_mul]
  · intro a
    refine ⟨s, ?_⟩
    show (a ^ m) ^ (2 ^ s) = 1
    rw [← pow_mul, mul_comm, ← hnm]
    exact pow_card_eq_one'

end PureAb


section Bridge

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

theorem Env33.out_comm (E : Env33 x y K T V W f z) :
    ∀ a b : MulAut (kBar (pumpJ K f)) ⧸ innAut (kBar (pumpJ K f)), a * b = b * a := by
  obtain ⟨r, -, -, -, F₀, _, _, -, hF₀, ⟨e₀⟩⟩ := E.hJdata
  intro a b
  induction a using QuotientGroup.induction_on with | H α => ?_
  induction b using QuotientGroup.induction_on with | H β => ?_
  have h := outer_comm_mem_innAut hF₀ e₀ α β
  have h0 : (QuotientGroup.mk' (innAut (kBar (pumpJ K f))) ⁅α, β⁆) = 1 ↔
      ⁅α, β⁆ ∈ innAut (kBar (pumpJ K f)) := QuotientGroup.eq_one_iff _
  rw [← h0, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

@[expose] noncomputable def Env33.rhoOut (E : Env33 x y K T V W f z) :
    ↥(centralizer ({f} : Set G)) →* MulAut (kBar (pumpJ K f)) ⧸ innAut (kBar (pumpJ K f)) :=
  (QuotientGroup.mk' (innAut (kBar (pumpJ K f)))).comp (Back.actHom E.hJn)

theorem Env33.rho_not_inn (E : Env33 x y K T V W f z) {w : G} (hw : w ∈ T ⊓ K)
    (hwI : w ∉ layerI K f) : E.rho ⟨w, E.hPV hw⟩ ∉ innAut (kBar (pumpJ K f)) := by
  intro h
  obtain ⟨q, hq, d, hd, hwq⟩ := E.inn_decomp ⟨w, E.hPV hw⟩ h
  have hwq' : w = q * d := hwq
  have hdP : d ∈ T ⊓ K := by
    have : d = q⁻¹ * w := by rw [hwq']; group
    rw [this]
    exact (T ⊓ K).mul_mem ((T ⊓ K).inv_mem hq.1) hw
  have hd1 : d ∈ (T ⊓ K) ⊓ secD K f V := ⟨hdP, hd⟩
  rw [E.hPD, Subgroup.mem_bot] at hd1
  rw [hd1, mul_one] at hwq'
  exact hwI (hwq' ▸ hq.2)


theorem Env33.not_mem_oRes (E : Env33 x y K T V W f z) {w : G} (hw : w ∈ T ⊓ K)
    (hw2 : orderOf w = 2) (hwI : w ∉ layerI K f) :
    centMap E.hKN E.hfC ⟨w, ⟨hw.2, mem_centralizer_singleton_iff.2 (E.hfP w hw).symm⟩⟩ ∉
      oResidual 2 ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hmem
  set X : Subgroup G := K ⊓ centralizer ({f} : Set G) with hX
  set cm := centMap E.hKN E.hfC with hcm
  have hsurj : Function.Surjective cm := centMap_surjective E.hKN E.hfC E.cfg.hf2
  have hkerodd : Odd (Nat.card cm.ker) := centMap_ker_odd E.hKN E.hfC
  let ρX : ↥X →* MulAut (kBar (pumpJ K f)) ⧸ innAut (kBar (pumpJ K f)) :=
    E.rhoOut.comp (Subgroup.inclusion (inf_le_right : X ≤ centralizer ({f} : Set G)))
  obtain ⟨κ, hκ1, hκ2, hκ3⟩ := exists_hom_kills_odd E.out_comm
  let lam : ↥X →* MulAut (kBar (pumpJ K f)) ⧸ innAut (kBar (pumpJ K f)) := κ.comp ρX
  have hlamker : ∀ k ∈ cm.ker, lam k = 1 := by
    intro k hk
    have h1 : orderOf k ∣ Nat.card cm.ker := by
      have := orderOf_dvd_natCard (⟨k, hk⟩ : cm.ker)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : Odd (orderOf (ρX k)) :=
      Odd.of_dvd_nat (Odd.of_dvd_nat hkerodd h1) (orderOf_map_dvd ρX k)
    exact hκ1 _ h2
  have hlamodd : ∀ c : ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)),
      Odd (orderOf c) → ∃ x₀ : ↥X, cm x₀ = c ∧ lam x₀ = 1 := by
    intro c hc
    obtain ⟨x₀, hx₀⟩ := hsurj c
    refine ⟨x₀, hx₀, ?_⟩
    have h1 : x₀ ^ orderOf c ∈ cm.ker := by
      rw [MonoidHom.mem_ker, map_pow, hx₀]
      exact pow_orderOf_eq_one c
    have h2 : (lam x₀) ^ orderOf c = 1 := by
      rw [← map_pow]
      exact hlamker _ h1
    have h3 : Odd (orderOf (lam x₀)) := Odd.of_dvd_nat hc (orderOf_dvd_of_pow_eq_one h2)
    obtain ⟨s, hs⟩ := hκ3 (ρX x₀)
    have h4 : orderOf (lam x₀) ∣ 2 ^ s := orderOf_dvd_of_pow_eq_one hs
    have h5 : Nat.Coprime (orderOf (lam x₀)) (2 ^ s) :=
      Nat.Coprime.pow_right s (Nat.coprime_two_right.2 h3)
    have h6 : orderOf (lam x₀) = 1 := Nat.eq_one_of_dvd_coprimes h5 (dvd_refl _) h4
    exact orderOf_eq_one_iff.1 h6
  set N₀ : Subgroup ↥X := lam.ker with hN₀
  have hle : oResidual 2 ↥(fixedSubgroup (kBar K) (Back.actHom E.hKN ⟨f, E.hfC⟩)) ≤ N₀.map cm := by
    unfold oResidual
    refine (Subgroup.closure_le _).2 ?_
    intro c hc
    obtain ⟨x₀, hx₀, hlx⟩ := hlamodd c (Nat.coprime_two_right.1 hc)
    exact ⟨x₀, hlx, hx₀⟩
  obtain ⟨x₀, hx₀N, hx₀c⟩ := hle hmem
  set w' : ↥X := ⟨w, ⟨hw.2, mem_centralizer_singleton_iff.2 (E.hfP w hw).symm⟩⟩ with hw'
  have hker : x₀⁻¹ * w' ∈ cm.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx₀c, inv_mul_cancel]
  have hlw : lam w' = 1 := by
    have h1 : w' = x₀ * (x₀⁻¹ * w') := by group
    rw [h1, map_mul, hlamker _ hker, (hx₀N : lam x₀ = 1), mul_one]
  have hρw : ρX w' ≠ 1 := by
    intro h
    apply E.rho_not_inn hw hwI
    have : ρX w' = QuotientGroup.mk' (innAut (kBar (pumpJ K f))) (E.rho ⟨w, E.hPV hw⟩) := rfl
    rw [this] at h
    exact (QuotientGroup.eq_one_iff _).1 h
  have hρw2 : orderOf (ρX w') = 2 := by
    refine orderOf_eq_prime ?_ hρw
    rw [sq, ← map_mul]
    have : w' * w' = 1 := by
      apply Subtype.ext
      show w * w = 1
      have := pow_orderOf_eq_one w
      rwa [hw2, sq] at this
    rw [this, map_one]
  have : lam w' = ρX w' := hκ2 _ hρw2
  exact hρw (this ▸ hlw)

end Bridge

end CFSG.GH74.GLS.C3.Layer1.Thm1G33

module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyConf
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

theorem z3_pow : ∀ c : Z3, ∃ n : ℕ, c = Multiplicative.ofAdd (1 : ZMod 3) ^ n := by
  intro c
  have : c = 1 ∨ c = Multiplicative.ofAdd (1 : ZMod 3) ∨
      c = Multiplicative.ofAdd (1 : ZMod 3) * Multiplicative.ofAdd (1 : ZMod 3) := by
    revert c; decide
  rcases this with h | h | h
  · exact ⟨0, by simpa using h⟩
  · exact ⟨1, by simpa using h⟩
  · exact ⟨2, by simpa [sq] using h⟩

theorem d8_r2_ne_one : (DihedralGroup.r 2 : DihedralGroup 4) ≠ 1 := by decide

theorem card_hmodel : Nat.card HModel = 2880 := by
  rw [Nat.card_prod, Nat.card_prod, DihedralGroup.nat_card]
  have h3 : Nat.card Z3 = 3 := by
    rw [Nat.card_eq_fintype_card]; decide
  have h5 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; decide
  rw [h3, h5]

section Red

variable {G : Type} [Group G] [Finite G]

abbrev RedC (r : G) : Type := ↥(centralizer ({r} : Set G))

noncomputable abbrev RedO (r : G) : Subgroup (RedC r) := CFSG.pPrimeCore 2 (RedC r)

abbrev RedX (r : G) : Type := RedC r ⧸ RedO r

@[expose] noncomputable def redPi (r : G) : RedC r →* RedX r := QuotientGroup.mk' (RedO r)

theorem redO_odd (r : G) : Odd (Nat.card (RedO r)) :=
  Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := RedC r))

variable {t r : G} {Θ : HModel →* G}

theorem FyConf.comm_r (h : FyConf t r Θ) (m : HModel) : Θ m * r = r * Θ m :=
  ((h.mem_range _).2 ⟨m, rfl⟩).2

theorem FyConf.comm_t (h : FyConf t r Θ) (m : HModel) : Θ m * t = t * Θ m :=
  ((h.mem_range _).2 ⟨m, rfl⟩).1

@[expose] def FyConf.thetaC (h : FyConf t r Θ) : HModel →* RedC r :=
  Θ.codRestrict _ fun m => mem_centralizer_singleton_iff.2 (h.comm_r m)

theorem FyConf.thetaC_injective (h : FyConf t r Θ) : Function.Injective h.thetaC := by
  intro a b hab
  apply h.inj
  exact congrArg Subtype.val hab

@[expose] noncomputable def FyConf.Phi (h : FyConf t r Θ) : HModel →* RedX r :=
  (redPi r).comp h.thetaC

theorem FyConf.Phi_apply (h : FyConf t r Θ) (m : HModel) :
    h.Phi m = QuotientGroup.mk (h.thetaC m) := rfl

theorem FyConf.r_mem_O (h : FyConf t r Θ) :
    (h.thetaC (1, Multiplicative.ofAdd 1, 1)) ∈ RedO r := by
  set R : RedC r := h.thetaC (1, Multiplicative.ofAdd 1, 1) with hR
  have hRc : ∀ g : RedC r, g * R = R * g := by
    intro g
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.1 g.2
    have h2 : (R : G) = r := h.r_eq
    show (g : G) * (R : G) = (R : G) * (g : G)
    rw [h2]; exact h1
  have hn : (zpowers R).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have : g * R ^ k * g⁻¹ = R ^ k := by
      have hc : Commute g R := hRc g
      have := (hc.zpow_right k).eq
      calc g * R ^ k * g⁻¹ = (R ^ k * g) * g⁻¹ := by rw [← this]
        _ = R ^ k := by group
    rw [this]; exact zpow_mem_zpowers R k
  have hcard : Nat.card (zpowers R) = 3 := by
    rw [Nat.card_zpowers]
    have : orderOf (R : G) = 3 := by
      rw [show (R : G) = r from h.r_eq]; exact h.orderOf_r
    rw [← this]
    exact (Subgroup.orderOf_coe R).symm
  have hcop : Nat.Coprime 2 (Nat.card (zpowers R)) := by rw [hcard]; norm_num
  have hle : zpowers R ≤ RedO r := le_sSup ⟨hn, hcop⟩
  exact hle (mem_zpowers R)

@[expose] noncomputable def FyConf.kerO (h : FyConf t r Θ) : Subgroup HModel :=
  (RedO r).comap h.thetaC

instance FyConf.kerO_normal (h : FyConf t r Θ) : h.kerO.Normal :=
  Subgroup.Normal.comap inferInstance _

theorem FyConf.kerO_odd (h : FyConf t r Θ) : Odd (Nat.card h.kerO) := by
  have hinj : Function.Injective (h.thetaC.subgroupComap (RedO r)) := by
    intro a b hab
    apply Subtype.ext
    apply h.thetaC_injective
    exact congrArg Subtype.val hab
  have hd : Nat.card h.kerO ∣ Nat.card (RedO r) := Subgroup.card_dvd_of_injective _ hinj
  exact Odd.of_dvd_nat (redO_odd r) hd

theorem FyConf.Phi_eq_one_iff (h : FyConf t r Θ) (m : HModel) :
    h.Phi m = 1 ↔ m.1 = 1 ∧ m.2.2 = 1 := by
  constructor
  · intro hm
    have hm' : (QuotientGroup.mk (h.thetaC m) : RedX r) = 1 := hm
    have hmO : m ∈ h.kerO := (QuotientGroup.eq_one_iff (h.thetaC m)).1 hm'
    exact normal_odd_hmodel h.kerO h.kerO_odd m hmO
  · rintro ⟨h1, h2⟩
    obtain ⟨d, c, σ⟩ := m
    simp only at h1 h2
    subst h1; subst h2
    obtain ⟨n, hn⟩ := z3_pow c
    have : ((1 : DihedralGroup 4), c, (1 : Equiv.Perm (Fin 5))) =
        ((1 : DihedralGroup 4), Multiplicative.ofAdd (1 : ZMod 3),
          (1 : Equiv.Perm (Fin 5))) ^ n := by
      rw [hn]; ext <;> simp
    rw [FyConf.Phi_apply, QuotientGroup.eq_one_iff, this, map_pow]
    exact pow_mem h.r_mem_O n

end Red

end CFSG.EvenSporadicStandard.TwoHS

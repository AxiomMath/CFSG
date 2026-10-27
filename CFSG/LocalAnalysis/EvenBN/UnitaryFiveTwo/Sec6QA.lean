module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Lin1
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec6Lin2
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6Split
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckSL44

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup Matrix CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.L44Sylow
open scoped MatrixGroups

section QA

variable {V Γ : Type*} [Group V] [Finite V] [Group Γ] [Finite Γ]

@[expose] def comm1 (hc : ∀ a b : V, a * b = b * a) (ρ : Γ →* MulAut V) (u : Γ) : V →* V where
  toFun v := ρ u v * v⁻¹
  map_one' := by simp
  map_mul' a b := by
    letI : CommGroup V := { ‹Group V› with mul_comm := hc }
    rw [map_mul, mul_inv]
    exact mul_mul_mul_comm _ _ _ _

theorem comm1_apply (hc : ∀ a b : V, a * b = b * a) (ρ : Γ →* MulAut V) (u : Γ) (v : V) :
    comm1 hc ρ u v = ρ u v * v⁻¹ := rfl

theorem lowerSL_mul (a b : F4) : lowerSL a * lowerSL b = lowerSL (a + b) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerSL, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem lowerSL_zero : lowerSL 0 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerSL]

theorem lowerSL_mul_self (a : F4) : lowerSL a * lowerSL a = 1 := by
  rw [lowerSL_mul, CharTwo.add_self_eq_zero, lowerSL_zero]

theorem exists_of_card_le_two (R : Subgroup V) (h : Nat.card R ≤ 2) :
    ∃ x : V, ∀ r ∈ R, r = 1 ∨ r = x := by
  by_cases hb : R = ⊥
  · exact ⟨1, fun r hr => Or.inl (by rw [hb] at hr; exact (Subgroup.mem_bot.1 hr))⟩
  · obtain ⟨⟨x, hxR⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hb
    have hx1 : x ≠ 1 := fun h => hx1' (Subtype.ext h)
    refine ⟨x, fun r hr => ?_⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨hr1, hrx⟩ := hcon
    let f : Fin 3 → R := ![⟨1, R.one_mem⟩, ⟨x, hxR⟩, ⟨r, hr⟩]
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f, Subtype.ext_iff] at hij ⊢
      all_goals first
        | exact absurd hij.symm hx1
        | exact absurd hij hx1
        | exact absurd hij.symm hr1
        | exact absurd hij hr1
        | exact absurd hij.symm hrx
        | exact absurd hij hrx
    have := Nat.card_le_card_of_injective f hf
    simp at this
    omega

theorem card_range_comm1 (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) (hVcard : Nat.card V = 2 ^ 4)
    (ρ : Γ →* MulAut V) (e : Γ ≃* SL(2, F4))
    (hfix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1)
    {u : Γ} (hu1 : e u ≠ 1) (h00 : (e u : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1)
    (h01 : (e u : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0)
    (h11 : (e u : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1) :
    Nat.card (comm1 hc ρ u).range = 4 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  have heu : e u = lowerSL ((e u : Matrix (Fin 2) (Fin 2) F4) 1 0) :=
    eq_lowerSL_of_entries h00 h01 h11
  obtain ⟨a, ha⟩ : ∃ a : F4, a = (e u : Matrix (Fin 2) (Fin 2) F4) 1 0 := ⟨_, rfl⟩
  rw [← ha] at heu
  have ha0 : a ≠ 0 := by
    intro h0
    apply hu1
    rw [heu, h0, lowerSL_zero]
  have huu : u * u = 1 := by
    apply e.injective
    rw [map_mul, heu, lowerSL_mul_self, map_one]
  have key : ∀ v : V, ρ u (ρ u v) = v := fun v => by
    rw [← MulAut.mul_apply, ← map_mul, huu, map_one, MulAut.one_apply]
  have hrk : (comm1 hc ρ u).range ≤ (comm1 hc ρ u).ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker, comm1_apply hc, comm1_apply]
    have e1 : ρ u (ρ u v * v⁻¹) = (ρ u v * v⁻¹)⁻¹ := by
      rw [map_mul, map_inv, key, mul_inv, inv_inv, mul_comm]
    rw [e1, ← mul_inv, hV, inv_one]
  have hcard := Subgroup.card_ker_mul_card_range (comm1 hc ρ u)
  rw [hVcard] at hcard
  have hle : Nat.card (comm1 hc ρ u).range ≤ Nat.card (comm1 hc ρ u).ker :=
    Subgroup.card_le_of_le hrk
  have hdvd : Nat.card (comm1 hc ρ u).range ∣ 2 ^ 4 := hVcard ▸ Subgroup.card_range_dvd (comm1 hc ρ u)
  have hle4 : Nat.card (comm1 hc ρ u).range ≤ 4 := by nlinarith
  by_contra hne
  have h2 : Nat.card (comm1 hc ρ u).range ≤ 2 := by
    by_contra h3
    have h3' : Nat.card (comm1 hc ρ u).range = 3 := by omega
    rw [h3'] at hdvd
    norm_num at hdvd
  obtain ⟨x, hx⟩ := exists_of_card_le_two _ h2
  have hα : ∀ v : V, ρ u v = v ∨ ρ u v = v * x := by
    intro v
    rcases hx _ ⟨v, rfl⟩ with h1 | h1
    · left
      rw [comm1_apply hc] at h1
      exact (mul_inv_eq_one.1 h1)
    · right
      rw [comm1_apply hc] at h1
      rw [← h1]
      simp [mul_comm]
  obtain ⟨g, hg5, hg1⟩ := exists_order_five_pair a ha0
  set γ : Γ := e.symm g with hγ
  have heγ : e γ = g := e.apply_symm_apply g
  have hβ : ∀ v : V, ρ (γ * u * γ⁻¹) v = v ∨ ρ (γ * u * γ⁻¹) v = v * ρ γ x := by
    intro v
    rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply]
    rcases hα (ρ γ⁻¹ v) with h1 | h1
    · left
      rw [h1, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    · right
      rw [h1, map_mul, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have h48 := pow_48_eq_one_of_transvections hV ⟨x, hα⟩ ⟨ρ γ x, hβ⟩
  have h48' : (ρ (u * (γ * u * γ⁻¹))) ^ 48 = 1 := by
    rw [map_mul]
    exact h48
  have hub5 : (u * (γ * u * γ⁻¹)) ^ 5 = 1 := by
    apply e.injective
    rw [map_pow, map_mul, map_mul, map_mul, map_inv, heγ, heu, map_one]
    exact hg5
  have hub1 : u * (γ * u * γ⁻¹) ≠ 1 := by
    intro h1
    apply hg1
    have := congrArg e h1
    rw [map_mul, map_mul, map_mul, map_inv, heγ, heu, map_one] at this
    exact this
  have h5' : (ρ (u * (γ * u * γ⁻¹))) ^ 5 = 1 := by
    rw [← map_pow, hub5, map_one]
  have hρ1 : ρ (u * (γ * u * γ⁻¹)) = 1 := by
    have := pow_gcd_eq_one.2 ⟨h5', h48'⟩
    have hg : Nat.gcd 5 48 = 1 := by norm_num
    rwa [hg, pow_one] at this
  haveI : IsSimpleGroup (SL(2, F4)) := by
    refine CFSG.LocalAnalysis.EvenBN.Common.sl2_isSimpleGroup_of_charTwo ?_
    rw [Nat.card_eq_fintype_card, F4.card]
  haveI : IsSimpleGroup Γ := e.isSimpleGroup
  have hker : ρ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h1 | h1
    · exfalso
      apply hub1
      have : u * (γ * u * γ⁻¹) ∈ ρ.ker := hρ1
      rw [h1] at this
      exact Subgroup.mem_bot.1 this
    · exact h1
  have hall : ∀ g : Γ, ρ g = 1 := fun g => MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top g)
  have hsub : Subsingleton V := ⟨fun a b => by
    have h1 := hfix a (fun g => by rw [hall g]; rfl)
    have h2 := hfix b (fun g => by rw [hall g]; rfl)
    rw [h1, h2]⟩
  have : Nat.card V = 1 := Nat.card_unique
  rw [hVcard] at this
  norm_num at this

theorem range_comm1_eq_fixSub (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) (hVcard : Nat.card V = 2 ^ 4)
    (ρ : Γ →* MulAut V) (e : Γ ≃* SL(2, F4))
    (hfix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1) {U : Subgroup Γ}
    (hU : ∀ g ∈ U, (e g : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e g : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧ (e g : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hCU : Nat.card (ModSplit.fixSub ρ U) = 4) {u : Γ} (huU : u ∈ U) (hu1 : e u ≠ 1) :
    (comm1 hc ρ u).range = ModSplit.fixSub ρ U := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨h00, h01, h11⟩ := hU u huU
  have hr4 := card_range_comm1 hc hV hVcard ρ e hfix hu1 h00 h01 h11
  have hcard := Subgroup.card_ker_mul_card_range (comm1 hc ρ u)
  rw [hVcard, hr4] at hcard
  have hk4 : Nat.card (comm1 hc ρ u).ker = 4 := by omega
  have hfk : ModSplit.fixSub ρ U ≤ (comm1 hc ρ u).ker := by
    intro v hv
    rw [MonoidHom.mem_ker, comm1_apply hc, hv u huU, mul_inv_cancel]
  have heq : ModSplit.fixSub ρ U = (comm1 hc ρ u).ker :=
    Subgroup.eq_of_le_of_card_ge hfk (by rw [hCU, hk4])
  have huu : u * u = 1 := by
    have heu : e u = lowerSL ((e u : Matrix (Fin 2) (Fin 2) F4) 1 0) :=
      eq_lowerSL_of_entries h00 h01 h11
    apply e.injective
    rw [map_mul, heu, lowerSL_mul_self, map_one]
  have key : ∀ v : V, ρ u (ρ u v) = v := fun v => by
    rw [← MulAut.mul_apply, ← map_mul, huu, map_one, MulAut.one_apply]
  have hrk : (comm1 hc ρ u).range ≤ (comm1 hc ρ u).ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker, comm1_apply hc, comm1_apply]
    have e1 : ρ u (ρ u v * v⁻¹) = (ρ u v * v⁻¹)⁻¹ := by
      rw [map_mul, map_inv, key, mul_inv, inv_inv, mul_comm]
    rw [e1, ← mul_inv, hV, inv_one]
  rw [heq]
  exact Subgroup.eq_of_le_of_card_ge hrk (by rw [hr4, hk4])

theorem comm1_mem_fixSub (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) (hVcard : Nat.card V = 2 ^ 4)
    (ρ : Γ →* MulAut V) (e : Γ ≃* SL(2, F4))
    (hfix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1) {U : Subgroup Γ}
    (hU : ∀ g ∈ U, (e g : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e g : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧ (e g : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    (hCU : Nat.card (ModSplit.fixSub ρ U) = 4) {u : Γ} (huU : u ∈ U) (v : V) :
    comm1 hc ρ u v ∈ ModSplit.fixSub ρ U := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  by_cases hu1 : e u = 1
  · have : u = 1 := e.injective (by rw [hu1, map_one])
    rw [this]
    simp [comm1_apply hc, (ModSplit.fixSub ρ U).one_mem]
  · rw [← range_comm1_eq_fixSub hc hV hVcard ρ e hfix hU hCU huU hu1]
    exact ⟨v, rfl⟩


theorem card_fixSub_le_four (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) (hVcard : Nat.card V = 2 ^ 4)
    (ρ : Γ →* MulAut V) (e : Γ ≃* SL(2, F4))
    (hfix : ∀ v : V, (∀ g : Γ, ρ g v = v) → v = 1) {U : Subgroup Γ}
    (hU : ∀ g ∈ U, (e g : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 ∧
      (e g : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 ∧ (e g : Matrix (Fin 2) (Fin 2) F4) 1 1 = 1)
    {u : Γ} (huU : u ∈ U) (hu1 : e u ≠ 1) : Nat.card (ModSplit.fixSub ρ U) ≤ 4 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hc }
  obtain ⟨h00, h01, h11⟩ := hU u huU
  have hr4 := card_range_comm1 hc hV hVcard ρ e hfix hu1 h00 h01 h11
  have hcard := Subgroup.card_ker_mul_card_range (comm1 hc ρ u)
  rw [hVcard, hr4] at hcard
  have hk4 : Nat.card (comm1 hc ρ u).ker = 4 := by omega
  have hfk : ModSplit.fixSub ρ U ≤ (comm1 hc ρ u).ker := by
    intro v hv
    rw [MonoidHom.mem_ker, comm1_apply hc, hv u huU, mul_inv_cancel]
  have := Subgroup.card_le_of_le hfk
  omega


end QA

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

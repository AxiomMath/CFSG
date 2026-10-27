module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteCore
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFooteSolv
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cat81

open CFSG GorensteinWalter CatalogueSchreierLinearTwo Subgroup AutL2Facts

theorem mem_centralizer_conj_iff {F : Type} [Field F] [Finite F] {Y : Type} [Group Y]
    (e : Y ≃* PSL2 F) (α : MulAut Y) (y : Y) :
    α ∈ centralizer ({MulAut.conj y} : Set (MulAut Y)) ↔ α y = y := by
  rw [mem_centralizer_singleton_iff, apply_eq_iff_commute e, ← autEquiv_conj, ← map_mul,
    ← map_mul, (autEquiv e).injective.eq_iff]

theorem centPerfect_body : ∀ (Y : Type) [Group Y] [Finite Y] (p f : ℕ), p.Prime → p ≠ 2 →
    1 ≤ f → Blueprint.LieModel Y .PSL 2 p f → ∀ y₀ : Y, orderOf y₀ = 2 →
      ∀ R : Subgroup (MulAut Y), R ≤ centralizer ({MulAut.conj y₀} : Set (MulAut Y)) →
        Group.IsPerfect R → R = ⊥ := by
  intro Y _ _ p f hp hp2 hf hY y₀ hy₀ R hRC hRp
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ := lieModel_psl2_data hY
  set H := centralizer ({y₀} : Set Y) with hH
  have hHs : Group.IsSolvable H :=
    footeInvolutionSolvable Y (Or.inr ⟨p, f, hp, hp2, hf, hY⟩) y₀ hy₀
  have hRI : R ≤ H.map (MulAut.conj : Y →* MulAut Y) := by
    intro α hα
    have hα' : α ∈ ⁅R, R⁆ := by rw [Subgroup.commutator_eq_self]; exact hα
    have hαI : α ∈ (MulAut.conj : Y →* MulAut Y).range := by
      refine (commutator_le.2 ?_) hα'
      intro φ _ ψ _
      obtain ⟨s, hs⟩ := footeOutAbelian Y p f hp hp2 hf hY φ ψ
      exact ⟨s, by rw [commutatorElement_def, hs]⟩
    obtain ⟨s, rfl⟩ := hαI
    refine ⟨s, ?_, rfl⟩
    have h1 := (mem_centralizer_conj_iff e _ y₀).1 (hRC hα)
    rw [MulAut.conj_apply] at h1
    rw [hH, SetLike.mem_coe, mem_centralizer_singleton_iff]
    calc s * y₀ = s * y₀ * s⁻¹ * s := by group
      _ = y₀ * s := by rw [h1]
  have hRs : Group.IsSolvable R := by
    have : Group.IsSolvable (H.map (MulAut.conj : Y →* MulAut Y)) :=
      Group.isSolvable_of_surjective ((MulAut.conj : Y →* MulAut Y).subgroupMap_surjective H)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRI)
  by_contra hR
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).2 hR
  exact Group.IsPerfect.not_isSolvable R hRs

theorem nineCent_body : ∀ (Y : Type) [Group Y] [Finite Y], Blueprint.LieModel Y .PSL 2 3 2 →
    ∀ y₀ : Y, orderOf y₀ = 2 →
      IsPGroup 2 ↥(centralizer ({MulAut.conj y₀} : Set (MulAut Y))) := by
  intro Y _ _ hY y₀ hy₀
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ := lieModel_psl2_data hY
  have h := (autL2Stab_conclusions (p := 3) (f := 1) Nat.prime_three (by norm_num) le_rfl hY y₀
    hy₀).2 (by norm_num)
  have heq : centralizer ({MulAut.conj y₀} : Set (MulAut Y)) =
      MulAction.stabilizer (MulAut Y) y₀ := by
    ext α
    rw [mem_centralizer_conj_iff e, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  rw [heq]
  exact h

theorem sp4_poly_ge {q : ℕ} (hq : 4 ≤ q) : 979200 ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := by
  have h1 : 256 ≤ q ^ 4 :=
    calc 256 = 4 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have h2 : 16 ≤ q ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 15 ≤ q ^ 2 - 1 := by omega
  have h4 : 255 ≤ q ^ 4 - 1 := by omega
  calc 979200 = 256 * (15 * 255) := by norm_num
    _ ≤ q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) := Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)

theorem sp4Three_body : ∀ (X : Type) [Group X] [Finite X] (p f : ℕ), p.Prime → 1 ≤ f →
    Blueprint.LieModel X .PSp 2 3 1 → Blueprint.LieModel X .PSp 2 p f → p ^ f = 3 := by
  intro X _ _ p f hp hf h3 hq
  have hX := CatFactsSp4.two_mul_card_of_lieModel_psp (by norm_num) h3
  norm_num at hX
  have hX' : Nat.card X = 25920 := by omega
  by_cases hp2 : p = 2
  · subst hp2
    exfalso
    obtain ⟨-, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hq
    have : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = 2 ^ f := by rw [← Nat.card_eq_fintype_card, hF]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP F 2 := charP_of_card_eq_prime_pow hc
    have hcard := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := F) 2
    have hI : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hI] at hcard
    rw [Finset.prod_insert (by decide), Finset.prod_singleton] at hcard
    rw [← Nat.card_congr e.toEquiv, hX'] at hcard
    set q := Nat.card F with hqdef
    have h2q : 2 ∣ q := hF ▸ dvd_pow_self 2 (by omega : f ≠ 0)
    have hq2 : 2 ≤ q := Nat.le_of_dvd (by rw [hF]; positivity) h2q
    by_cases hq4 : 4 ≤ q
    · have := sp4_poly_ge hq4
      norm_num at hcard this
      omega
    · have hq2' : q = 2 := by omega
      rw [hq2'] at hcard
      norm_num at hcard
  · have hX2 := CatFactsSp4.two_mul_card_of_lieModel_psp hp2 hq
    rw [hX'] at hX2
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hq3 : 3 ≤ p ^ f :=
      le_trans hp3 (Nat.le_self_pow (by omega) p)
    by_contra hne
    have hq4 : 4 ≤ p ^ f := by omega
    have := sp4_poly_ge hq4
    omega

end Cat81

end CFSG.ComponentClassification.CatFactsL4U4

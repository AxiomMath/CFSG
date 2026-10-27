module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8C12Gen
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Gen
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvRee

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.GH74.GLS.IVK.GHInv CFSG.LieType.Chevalley
  CFSG.Blueprint.Chevalley
open CFSG.LieType.Ree (ReeTag)


theorem hom_trivial_of_no_involutions {S Q : Type} [Group S] [Group Q] [Finite S] {n : ℕ}
    (hS : Nat.card S = 2 ^ n) (ρ : S →* Q)
    (hQ : ∀ E : Subgroup Q, (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 1) : ∀ s, ρ s = 1 := by
  intro s
  by_contra hne
  have h1 : orderOf (ρ s) ∣ orderOf s := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have h2 : orderOf s ∣ 2 ^ n := hS ▸ orderOf_dvd_natCard s
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (h1.trans h2)
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hne (orderOf_eq_one_iff.1 (by simpa using hjeq))
  have h2dvd : 2 ∣ orderOf (ρ s) := by
    rw [hjeq]; exact dvd_pow_self 2 hj0
  have hord : orderOf ((ρ s) ^ (orderOf (ρ s) / 2)) = 2 :=
    orderOf_pow_orderOf_div (Nat.pos_of_dvd_of_pos h1 (orderOf_pos s)).ne' h2dvd
  set e := (ρ s) ^ (orderOf (ρ s) / 2) with he
  have he2 : e ^ (2 : ℤ) = 1 := by
    have := pow_orderOf_eq_one e
    rw [hord] at this
    rw [zpow_two, ← sq]
    exact this
  have hE : ∀ x ∈ Subgroup.zpowers e, x * x = 1 := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_add, ← two_mul, zpow_mul, he2, one_zpow]
  have := hQ _ hE
  rw [Nat.card_zpowers, hord] at this
  omega

theorem ree812_model_of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {f : ℕ}
    (h : ReeTitsModel G .twistedG2 3 f) : ReeTitsModel G' .twistedG2 3 f := by
  have h' := CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e (t := .twistedG2) (n := 0) (p := 3)
    (f := f) (Or.inr (Or.inr (Or.inl ⟨rfl, by simp [reeTitsTags], h⟩)))
  rcases h' with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact hR
  · exact absurd hh (by decide)

theorem ree812_model_of_FRee {Y : Type} [Group Y] (h : FRee Y) :
    ∃ f : ℕ, ReeTitsModel Y .twistedG2 3 f := by
  obtain ⟨f, -, hlie⟩ := h
  refine ⟨f, ?_⟩
  rcases hlie with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact hR
  · exact absurd hh (by decide)

theorem not_two_pow_eight_dvd_ree (a : ℕ) :
    ¬ 2 ^ 8 ∣ (3 ^ (2 * a + 1)) ^ 3 * (3 ^ (2 * a + 1) - 1) * ((3 ^ (2 * a + 1)) ^ 3 + 1) := by
  intro h
  have hq : 3 ^ (2 * a + 1) % 8 = 3 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  obtain ⟨k, hk⟩ : ∃ k, 3 ^ (2 * a + 1) = 8 * k + 3 := ⟨3 ^ (2 * a + 1) / 8, by omega⟩
  rw [hk] at h
  have hsub : 8 * k + 3 - 1 = 2 * (4 * k + 1) := by omega
  have hN : (8 * k + 3) ^ 3 * (8 * k + 3 - 1) * ((8 * k + 3) ^ 3 + 1) =
      8 * ((8 * k + 3) ^ 3 * (4 * k + 1) * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7)) := by
    rw [hsub]
    ring
  rw [hN] at h
  have hodd : Odd ((8 * k + 3) ^ 3 * (4 * k + 1) * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7)) := by
    refine Odd.mul (Odd.mul (Odd.pow ⟨4 * k + 1, by ring⟩) ⟨2 * k, by ring⟩) ?_
    exact ⟨64 * k ^ 3 + 72 * k ^ 2 + 27 * k + 3, by ring⟩
  have h2 : 32 ∣ (8 * k + 3) ^ 3 * (4 * k + 1) * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) := by
    have : 8 * 32 ∣
        8 * ((8 * k + 3) ^ 3 * (4 * k + 1) * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7)) := by
      norm_num at h ⊢
      exact h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have h3 : 2 ∣ (8 * k + 3) ^ 3 * (4 * k + 1) * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) :=
    (by norm_num : 2 ∣ 32).trans h2
  exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h3)

section Ree


theorem card_ree_model {T : Type} [Group T] {f : ℕ} (h : ReeTitsModel T .twistedG2 3 f) :
    ∃ a : ℕ, 1 ≤ a ∧ f = 2 * a + 1 ∧ Finite T ∧
      Nat.card T = (3 ^ f) ^ 3 * (3 ^ f - 1) * ((3 ^ f) ^ 3 + 1) := by
  classical
  obtain ⟨hfin, -, -, ⟨a, ha, hfa⟩, hiso⟩ := small_Ree_model_Schreier T 3 f h
  obtain ⟨-, a', hfa', K, _, _, hK, hw⟩ := h
  have ha' : a' = a := by omega
  subst ha'
  have : CharP K ReeTag.G2.prime :=
    finite_field_prime_power_characteristic Nat.prime_three (by omega) hK
  obtain ⟨E⟩ := hiso a' K hfa hK hw
  have hKa : Nat.card K = 3 ^ (2 * a' + 1) := by rw [hK, hfa]
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max
    (fun w : WeylGroup ReeTag.G2.tag => (coxeterSystem ReeTag.G2.tag).length w)
  obtain ⟨-, -, -, -, -, -, -, -, -, hΓcard, -⟩ :=
    small_Ree_Borel_coset_Sylow_action a' K hKa w₀ hw₀
  refine ⟨a', ha, hfa, hfin, ?_⟩
  rw [Nat.card_congr E.toEquiv, hΓcard, hfa]

theorem not_kfa_ree {Y : Type} [Group Y] {f : ℕ} (hM : ReeTitsModel Y .twistedG2 3 f) :
    ¬ KindFactorAll Kind.ly Y := by
  obtain ⟨a, ha, hfa, hfin, hcard⟩ := card_ree_model hM
  have h243 : ¬ 3 ^ 5 ∣ Nat.factorial 11 := by decide
  refine notKFA_of_card (p := 3) (k := f * 3) ?_ ?_
  · rw [hcard, pow_mul]
    exact ((Dvd.intro _ rfl : (3 ^ f) ^ 3 ∣ (3 ^ f) ^ 3 * (3 ^ f - 1)).mul_right _)
  · intro h
    exact h243 ((pow_dvd_pow 3 (by omega : 5 ≤ f * 3)).trans h)

theorem cellAbs_Ree : CellAbs FRee := by
  intro A _ _ zb Sb Vb J hfr hJ _ hF
  exfalso
  obtain ⟨f, hRee⟩ := ree812_model_of_FRee hF
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := not_isSolvable_quot_of_quasisimple hJ.1
  have hnk : ¬ KindFactorAll Kind.ly (↥J ⧸ center ↥J) := not_kfa_ree hRee
  obtain ⟨hZ, hcomp, -⟩ := hfr.reduce hJ hnk
  obtain ⟨φ, hφinj, -⟩ := hfr.embed_aut hJ hZ hcomp
  let e : (↥J ⧸ center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hmod : ReeTitsModel ↥J .twistedG2 3 f := ree812_model_of_mulEquiv e hRee
  obtain ⟨a, ha, hfa, hfin, hcard⟩ := card_ree_model hmod
  let ρ : ↥Sb →* Outer ↥J := (QuotientGroup.mk' (inner ↥J)).comp φ
  have hρ : ∀ s, ρ s = 1 := by
    refine hom_trivial_of_no_involutions (n := 8) hfr.card ρ ?_
    intro E hE
    have := ree_card_outer_elementary hmod E hE
    simpa using this
  have hinn : ∀ s : ↥Sb, φ s ∈ (MulAut.conj : ↥J →* MulAut ↥J).range := fun s =>
    (QuotientGroup.eq_one_iff _).1 (hρ s)
  have hconj : Function.Injective (MulAut.conj : ↥J →* MulAut ↥J) := by
    intro g h hgh
    have hx : ∀ x : ↥J, g * x * g⁻¹ = h * x * h⁻¹ := fun x => by
      simpa [MulAut.conj_apply] using DFunLike.congr_fun hgh x
    have hmem : h⁻¹ * g ∈ center ↥J := by
      rw [Subgroup.mem_center_iff]
      intro x
      have := hx (x)
      calc x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
        _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [this]
        _ = h⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact (inv_mul_eq_one.1 hmem).symm
  let φ' : ↥Sb →* (MulAut.conj : ↥J →* MulAut ↥J).range := φ.codRestrict _ hinn
  let ψ : ↥Sb →* ↥J := (MonoidHom.ofInjective hconj).symm.toMonoidHom.comp φ'
  have hψ : Function.Injective ψ := by
    intro x y hxy
    apply hφinj
    have h2 := (MonoidHom.ofInjective hconj).symm.injective hxy
    exact congrArg Subtype.val h2
  have hdvd : 2 ^ 8 ∣ Nat.card ↥J := by
    rw [← hfr.card]
    exact Subgroup.card_dvd_of_injective ψ hψ
  rw [hcard, hfa] at hdvd
  exact not_two_pow_eight_dvd_ree a hdvd

end Ree

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporReduce

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3.SporCent

theorem factorization_eq_of_pow_dvd {p n e : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ^ e ∣ n)
    (h2 : ¬ p ^ (e + 1) ∣ n) : n.factorization p = e := by
  have h3 := (hp.pow_dvd_iff_le_factorization hn).1 h1
  have h4 : ¬ e + 1 ≤ n.factorization p := fun h => h2 ((hp.pow_dvd_iff_le_factorization hn).2 h)
  omega

theorem center_eq_bot_of_not_prime {F : Type*} [Group F] [Finite F] [IsSimpleGroup F]
    (h : ¬ (Nat.card F).Prime) : Subgroup.center F = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center F) with h' | h'
  · exact h'
  · exfalso
    apply h
    let : CommGroup F :=
      { (inferInstance : Group F) with
        mul_comm := fun x y => ((Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top x)) y).symm }
    exact IsSimpleGroup.prime_card

end CFSG.LocalAnalysis.AGL81I.Section3.SporCent

namespace CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}

theorem false_of_centralizers_eq_top (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Subgroup.center ↥K = ⊥) (hout : ¬ p ∣ Nat.card (Outer ↥K))
    (hgen : ∀ A : Subgroup ↥K, IsElemAbelian p A → Nat.card A = p ^ 2 → ∀ Y : Subgroup ↥K,
      (∀ y ∈ A, y ≠ 1 → Subgroup.centralizer {y} ≤ Y) → Y = ⊤) : False := by
  obtain ⟨Ebar, hEl, hEc, hC, -⟩ := h.exists_barE hZ hout
  apply h.not_K_le
  intro x hx
  have : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K := hgen Ebar hEl hEc _ hC ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

theorem exists_sylow_subgroupOf_eq_normalizer (h : ThreeNineHyp K E D X₁ p d)
    (hZ : Subgroup.center ↥K = ⊥) (hout : ¬ p ∣ Nat.card (Outer ↥K))
    (hmax : ∀ S : Sylow p ↥K, ∀ H : Subgroup ↥K,
      Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) ≤ H →
        H = Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) ∨ H = ⊤) :
    ∃ S : Sylow p ↥K, X₁.subgroupOf K = Subgroup.normalizer ((S : Subgroup ↥K) : Set ↥K) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨Ebar, -, hEc, -, hN⟩ := h.exists_barE hZ hout
  obtain ⟨S, hES⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  refine ⟨S, ?_⟩
  rcases hmax S _ (hN S S.isPGroup' hES) with h1 | h1
  · exact h1
  · refine absurd (fun x hx => ?_) h.not_K_le
    have : (⟨x, hx⟩ : ↥K) ∈ X₁.subgroupOf K := h1 ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this

theorem dvd_card_of_subgroupOf_le (h : ThreeNineHyp K E D X₁ p d) (hDK : D ≤ K)
    {M : Subgroup ↥K} (hM : X₁.subgroupOf K ≤ M) :
    d ∣ Nat.card M ∧ d ^ (Nat.card ↥K).factorization d ∣ Nat.card M := by
  have : Fact d.Prime := ⟨h.d_prime⟩
  have hDM : Nat.card D ∣ Nat.card M := by
    have h1 : D.subgroupOf K ≤ M := fun x hx =>
      hM (Subgroup.mem_subgroupOf.mpr (h.D_le (Subgroup.mem_subgroupOf.mp hx)))
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv]
    exact Subgroup.card_dvd_of_le h1
  obtain ⟨Q, hQ⟩ := h.sylow
  have hcD : Nat.card D = d ^ (Nat.card X).factorization d := by
    rw [← hQ, Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
      Sylow.card_eq_multiplicity, Subgroup.card_top]
  have hKX : (Nat.card ↥K).factorization d ≤ (Nat.card X).factorization d :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card K) d
  refine ⟨?_, (pow_dvd_pow d hKX).trans (hcD ▸ hDM)⟩
  have hne : (Nat.card X).factorization d ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcD
    exact h.D_ne_bot (Subgroup.eq_bot_of_card_eq D hcD)
  exact (dvd_pow_self d hne).trans (hcD ▸ hDM)

end CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineHyp

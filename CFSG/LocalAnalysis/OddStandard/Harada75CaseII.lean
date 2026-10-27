module

public import CFSG.LocalAnalysis.OddStandard.Harada75Normal
public import CFSG.LocalAnalysis.OddStandard.Harada75Dual
public import CFSG.LocalAnalysis.OddStandard.Harada75Pres

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

private theorem caseII_card_le_finset {G : Type} [Group G] [Finite G] (U : Subgroup G)
    (F : Finset G) (hF : ∀ x ∈ U, x ∈ F) : Nat.card U ≤ F.card := by
  have h1 : (U : Set G) ⊆ (F : Set G) := fun x hx => hF x hx
  have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset] at h2
  rwa [← Nat.card_coe_set_eq] at h2

private theorem caseII_hCA [Finite S] {A E : Subgroup S} (h : Cfg S A E)
    (hcard : Nat.card ↥(A ⊓ E) = 2) {z : S} (hAE : ∀ x ∈ A ⊓ E, x = 1 ∨ x = z) {a : S}
    (ha : a ∈ A) (hac : ∀ b ∈ E, a * b = b * a) : a = 1 ∨ a = z := by
  by_contra hne
  push Not at hne
  have haE : a ∉ A ⊓ E := fun hm => (hAE a hm).elim hne.1 hne.2
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : Subgroup S, ∀ x, x ∈ C₁ ↔ x ∈ A ∧ ∀ b ∈ E, x * b = b * x :=
    ⟨A ⊓ Subgroup.centralizer (E : Set S), fun x => by
      rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
      exact and_congr_right fun _ =>
        ⟨fun hx b hb => (hx b hb).symm, fun hx b hb => (hx b hb).symm⟩⟩
  have hC₁A : C₁ ≤ A := fun x hx => ((hC₁ x).mp hx).1
  have hAEC : A ⊓ E ≤ C₁ := fun x hx => (hC₁ x).mpr ⟨hx.1, fun b hb => h.E_comm x hx.2 b hb⟩
  have haC₁ : a ∈ C₁ := (hC₁ a).mpr ⟨ha, hac⟩
  by_cases hall : ∀ a' ∈ A, ∀ b ∈ E, a' * b = b * a'
  · have hEA : E ≤ A := fun x hx => h.A_cent x fun a' ha' => (hall a' ha' x hx).symm
    have hAE' : A ⊓ E = E := inf_eq_right.mpr hEA
    rw [hAE', h.E_card] at hcard
    omega
  · push Not at hall
    obtain ⟨a₀, ha₀, x₀, hx₀, hx₀ne⟩ := hall
    have ha₀C : a₀ ∉ C₁ := fun hm => hx₀ne (((hC₁ a₀).mp hm).2 x₀ hx₀)
    have hC₁card : Nat.card C₁ = 4 := by
      have hdvd : Nat.card C₁ ∣ Nat.card A := Subgroup.card_dvd_of_le hC₁A
      have hdvd2 : Nat.card ↥(A ⊓ E) ∣ Nat.card C₁ := Subgroup.card_dvd_of_le hAEC
      rw [h.A_card] at hdvd
      rw [hcard] at hdvd2
      have h2 : Nat.card C₁ ≠ 2 := by
        intro h2
        have heq : A ⊓ E = C₁ := Subgroup.eq_of_le_of_card_ge hAEC (by rw [h2, hcard])
        exact haE (by rw [heq]; exact haC₁)
      have h8 : Nat.card C₁ ≠ 8 := by
        intro h8
        have heq : C₁ = A := Subgroup.eq_of_le_of_card_ge hC₁A (by rw [h8, h.A_card])
        exact ha₀C (by rw [heq]; exact ha₀)
      have hle : Nat.card C₁ ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < Nat.card C₁ := Nat.card_pos
      generalize Nat.card C₁ = n at hdvd hdvd2 h2 h8 hle hpos ⊢
      interval_cases n <;> first | rfl | omega
    have hcardA : Nat.card A = 2 * Nat.card C₁ := by
      have := h.A_card
      omega
    have hcent : ∀ x ∈ E, a₀ * x = x * a₀ → x ∈ A := by
      intro x hx hax
      refine h.A_cent x fun a' ha' => ?_
      by_cases ha'C : a' ∈ C₁
      · exact (((hC₁ a').mp ha'C).2 x hx).symm
      · have hmem : a₀⁻¹ * a' ∈ C₁ := inv_mul_mem_of_card hC₁A hcardA ha₀ ha' ha₀C ha'C
        obtain ⟨c, hcC, rfl⟩ : ∃ c ∈ C₁, a' = a₀ * c := ⟨a₀⁻¹ * a', hmem, by group⟩
        have hxc : c * x = x * c := ((hC₁ c).mp hcC).2 x hx
        calc x * (a₀ * c) = (x * a₀) * c := by group
          _ = (a₀ * x) * c := by rw [← hax]
          _ = a₀ * (x * c) := by group
          _ = a₀ * (c * x) := by rw [hxc]
          _ = a₀ * c * x := by group
    have h4 := card_centralizer_involution (E := E) (a := a₀) h.E_comm h.E_sq h.E_card
      (fun x hx => h.E_norm a₀ x hx) (h.A_sq a₀ ha₀) ⟨x₀, hx₀, hx₀ne⟩
    have hle : E ⊓ Subgroup.centralizer ({a₀} : Set S) ≤ A ⊓ E := fun x hx =>
      ⟨hcent x hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm, hx.1⟩
    have h5 := Subgroup.card_le_of_le hle
    rw [h4, hcard] at h5
    omega

private theorem caseII_hcomm [Finite S] {A E : Subgroup S} (h : Cfg S A E) {z : S}
    (hzc : ∀ s : S, s * z = z * s) (hAE : ∀ x ∈ A ⊓ E, x = 1 ∨ x = z) {a : S} (ha : a ∈ A)
    (b : S) (hb : b ∈ E) : a * b = b * a ∨ a * b = b * a * z := by
  by_cases hna : ∃ x ∈ E, a * x ≠ x * a
  swap
  · push Not at hna
    exact Or.inl (hna b hb)
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hna
  have hEa : ∀ x ∈ E, a * x * a⁻¹ ∈ E := fun x hx => h.E_norm a x hx
  have hker4 := card_centralizer_involution (E := E) (a := a) h.E_comm h.E_sq h.E_card hEa
    (h.A_sq a ha) ⟨x₀, hx₀, hx₀ne⟩
  set φ : E →* E := invMap E a h.E_comm hEa
  have hφval : ∀ x : E, (φ x).1 = x.1 * (a * x.1 * a⁻¹) := fun x => rfl
  have hmemker : ∀ x : E, x ∈ φ.ker ↔ a * x.1 = x.1 * a :=
    mem_ker_invMap E a h.E_comm h.E_sq hEa
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ Subgroup.centralizer ({a} : Set S)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((hmemker x.1).mp x.2).symm⟩
        invFun := fun x => ⟨⟨x.1, x.2.1⟩, (hmemker ⟨x.1, x.2.1⟩).mpr
          (Subgroup.mem_centralizer_singleton_iff.mp x.2.2).symm⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hrange : Nat.card φ.range = 2 := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [h.E_card, hker, hker4] at h1
    omega
  obtain ⟨x₁, hx₁ne⟩ : ∃ x₁ : E, a * x₁.1 ≠ x₁.1 * a := ⟨⟨x₀, hx₀⟩, hx₀ne⟩
  have hu1 : φ x₁ ≠ 1 := fun h1 => hx₁ne ((hmemker x₁).mp (MonoidHom.mem_ker.mpr h1))
  have hstruct : ∀ y ∈ φ.range, y = 1 ∨ y = φ x₁ :=
    eq_one_or_eq_of_card_two hrange ⟨x₁, rfl⟩ hu1
  have hconj : ∀ a' ∈ A, a' * (φ x₁).1 = (φ x₁).1 * a' := by
    intro a' ha'
    have hc : a' * a = a * a' := h.A_comm a' ha' a ha
    obtain ⟨c, hc1⟩ : ∃ c : E, c.1 = a' * x₁.1 * a'⁻¹ := ⟨⟨_, h.E_norm a' x₁.1 x₁.2⟩, rfl⟩
    have hcφ : (φ c).1 = a' * (φ x₁).1 * a'⁻¹ := by
      rw [hφval, hφval, hc1]
      calc a' * x₁.1 * a'⁻¹ * (a * (a' * x₁.1 * a'⁻¹) * a⁻¹)
          = a' * x₁.1 * a'⁻¹ * ((a * a') * x₁.1 * (a * a')⁻¹) := by group
        _ = a' * x₁.1 * a'⁻¹ * ((a' * a) * x₁.1 * (a' * a)⁻¹) := by rw [hc]
        _ = a' * (x₁.1 * (a * x₁.1 * a⁻¹)) * a'⁻¹ := by group
    rcases hstruct (φ c) ⟨c, rfl⟩ with h1 | h1
    · exfalso
      have h2 : a' * (φ x₁).1 * a'⁻¹ = 1 := by
        rw [← hcφ]
        exact congrArg Subtype.val h1
      apply hu1
      apply Subtype.ext
      calc (φ x₁).1 = a'⁻¹ * (a' * (φ x₁).1 * a'⁻¹) * a' := by group
        _ = 1 := by rw [h2]; group
    · have h2 : a' * (φ x₁).1 * a'⁻¹ = (φ x₁).1 := by rw [← hcφ, h1]
      calc a' * (φ x₁).1 = a' * (φ x₁).1 * a'⁻¹ * a' := by group
        _ = (φ x₁).1 * a' := by rw [h2]
  have hz : (φ x₁).1 = z := by
    have hmemA : (φ x₁).1 ∈ A := h.A_cent _ fun a' ha' => (hconj a' ha').symm
    have hne1 : (φ x₁).1 ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    exact (hAE _ ⟨hmemA, (φ x₁).2⟩).resolve_left hne1
  rcases hstruct (φ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩ with h1 | h1
  · exact Or.inl ((hmemker ⟨b, hb⟩).mp (MonoidHom.mem_ker.mpr h1))
  · refine Or.inr ?_
    have e0 : (φ ⟨b, hb⟩).1 = z := by rw [h1, hz]
    have e1 : b * (a * b * a⁻¹) = z := (hφval ⟨b, hb⟩).symm.trans e0
    calc a * b = b⁻¹ * (b * (a * b * a⁻¹)) * a := by group
      _ = b⁻¹ * z * a := by rw [e1]
      _ = b * z * a := by rw [h.E_inv hb]
      _ = b * (z * a) := mul_assoc _ _ _
      _ = b * (a * z) := by rw [← hzc a]
      _ = b * a * z := (mul_assoc _ _ _).symm

theorem noE32_of_caseII {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S}
    (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 2) : NoE32 S := by
  classical
  obtain ⟨z, hzE, hz1, hzc⟩ := h.exists_z hS
  have hz2 : z * z = 1 := h.E_sq z hzE
  have hzA : z ∈ A := h.A_cent z fun a _ => (hzc a).symm
  have hAE : ∀ x ∈ A ⊓ E, x = 1 ∨ x = z :=
    eq_one_or_eq_of_card_two hcard (u := z) (Subgroup.mem_inf.mpr ⟨hzA, hzE⟩) hz1
  have hAB : ∀ x : S, (x ∈ A ∧ x ∈ E) ↔ (x = 1 ∨ x = z) := by
    intro x
    constructor
    · exact fun hx => hAE x (Subgroup.mem_inf.mpr hx)
    · intro hx
      rcases hx with hx | hx
      · rw [hx]
        exact ⟨A.one_mem, E.one_mem⟩
      · rw [hx]
        exact ⟨hzA, hzE⟩
  have hcomm : ∀ a ∈ A, ∀ b ∈ E, a * b = b * a ∨ a * b = b * a * z := fun a ha b hb =>
    caseII_hcomm h hzc hAE ha b hb
  have hCA : ∀ a ∈ A, (∀ b ∈ E, a * b = b * a) → a = 1 ∨ a = z := fun a ha hac =>
    caseII_hCA h hcard hAE ha hac
  have hCB : ∀ b ∈ E, (∀ a ∈ A, a * b = b * a) → b = 1 ∨ b = z := fun b hb hbc =>
    hAE b (Subgroup.mem_inf.mpr ⟨h.A_cent b fun a ha => (hbc a ha).symm, hb⟩)
  obtain ⟨f₁, hf₁A, hf₁1, hf₁z⟩ : ∃ f₁ ∈ A, f₁ ≠ 1 ∧ f₁ ≠ z := by
    by_contra hne
    push Not at hne
    have hle := caseII_card_le_finset A ({1, z} : Finset S) (by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hne x hx hx1])
    have h2 : ({1, z} : Finset S).card ≤ 2 := Finset.card_le_two
    rw [h.A_card] at hle
    omega
  obtain ⟨f₂, hf₂A, hf₂1, hf₂z, hf₂f₁, hf₂f₁z⟩ :
      ∃ f₂ ∈ A, f₂ ≠ 1 ∧ f₂ ≠ z ∧ f₂ ≠ f₁ ∧ f₂ ≠ f₁ * z := by
    by_contra hne
    push Not at hne
    have hle := caseII_card_le_finset A ({1, z, f₁, f₁ * z} : Finset S) (by
      intro x hx
      by_cases hx1 : x = 1
      · simp [hx1]
      by_cases hx2 : x = z
      · simp [hx2]
      by_cases hx3 : x = f₁
      · simp [hx3]
      · simp [hne x hx hx1 hx2 hx3])
    have h4 : ({1, z, f₁, f₁ * z} : Finset S).card ≤ 4 := Finset.card_le_four
    rw [h.A_card] at hle
    omega
  obtain ⟨e₁, e₂, he₁, he₂, P, hcl⟩ := exists_hyperbolic_dual (A := A) (B := E) (z := z)
    (f₁ := f₁) (f₂ := f₂) h.A_comm h.A_sq h.A_card h.E_comm h.E_sq h.E_card hzc hz1 hz2 hAB
    hcomm hCA hCB hf₁A hf₂A ⟨hf₁1, hf₁z⟩ ⟨hf₂1, hf₂z, hf₂f₁, hf₂f₁z⟩
  refine noE32_of_pres hS h P he₁ he₂ hzE fun a ha => ?_
  refine Subgroup.closure_mono ?_ (hcl a ha)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

end CFSG.OddStandard.Harada75

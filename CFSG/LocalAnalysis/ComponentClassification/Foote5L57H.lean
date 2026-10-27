module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L57G
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_kleinFour_iff {X : Type} [Group X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) {w : X} :
    w ∈ kleinFourOfCommutingInvolutions a b ha hb hab ↔ w = a * b ∨ w = a ∨ w = b ∨ w = 1 := by
  change w ∈ ({a * b, a, b, 1} : Set X) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

variable {A : Subgroup G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊] (ε : A ⧸ pPrimeCore 2 A ≃* 𝕊)

theorem exists_normalizing_of_fourgroup {K : Subgroup G} {c₀ u₁ u₂ : G}
    (hc₀ : c₀ ∈ K) (hu₁ : u₁ ∈ ⁅K, K⁆) (hu₂ : u₂ ∈ ⁅K, K⁆) (hc₀A : c₀ ∈ A) (hu₁A : u₁ ∈ A)
    (hu₂A : u₂ ∈ A) (hu₁2 : u₁ * u₁ = 1) (hu₂2 : u₂ * u₂ = 1) (hcomm : Commute u₁ u₂)
    (ha₁ : psi A ε ⟨u₁, hu₁A⟩ ≠ 1) (ha₂ : psi A ε ⟨u₂, hu₂A⟩ ≠ 1)
    (hne : psi A ε ⟨u₁, hu₁A⟩ ≠ psi A ε ⟨u₂, hu₂A⟩)
    (hc1 : psi A ε ⟨c₀, hc₀A⟩ * psi A ε ⟨u₁, hu₁A⟩ * (psi A ε ⟨c₀, hc₀A⟩)⁻¹ =
      psi A ε ⟨u₂, hu₂A⟩)
    (hc2 : psi A ε ⟨c₀, hc₀A⟩ * psi A ε ⟨u₂, hu₂A⟩ * (psi A ε ⟨c₀, hc₀A⟩)⁻¹ =
      psi A ε ⟨u₁, hu₁A⟩ * psi A ε ⟨u₂, hu₂A⟩) :
    ∃ y₁ ∈ K, (∀ w ∈ kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hcomm,
        y₁ * w * y₁⁻¹ ∈ kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hcomm) ∧
      ∀ w ∈ kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hcomm, y₁ * w * y₁⁻¹ = w → w = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := psi A ε with hψ
  set a₁ := ψ ⟨u₁, hu₁A⟩ with ha₁def
  set a₂ := ψ ⟨u₂, hu₂A⟩ with ha₂def
  set c := ψ ⟨c₀, hc₀A⟩ with hcdef
  have hψmul : ∀ (x y : G) (hx : x ∈ A) (hy : y ∈ A),
      ψ ⟨x * y, mul_mem hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ := fun x y hx hy => by
    rw [← map_mul]
    rfl
  have hψinv : ∀ (x : G) (hx : x ∈ A), ψ ⟨x⁻¹, inv_mem hx⟩ = (ψ ⟨x, hx⟩)⁻¹ := fun x hx => by
    rw [← map_inv]
    rfl
  have ha₁2 : a₁ * a₁ = 1 := by
    rw [ha₁def, ← hψmul]
    simp only [hu₁2]
    exact map_one ψ
  have ha₂2 : a₂ * a₂ = 1 := by
    rw [ha₂def, ← hψmul]
    simp only [hu₂2]
    exact map_one ψ
  have hacomm : Commute a₁ a₂ := by
    show a₁ * a₂ = a₂ * a₁
    rw [ha₁def, ha₂def, ← hψmul, ← hψmul]
    simp only [hcomm.eq]
  set Wb := kleinFourOfCommutingInvolutions a₁ a₂ ha₁2 ha₂2 hacomm with hWb
  have hWbsq : ∀ x ∈ Wb, x * x = 1 := by
    intro x hx
    rcases (mem_kleinFour_iff ha₁2 ha₂2 hacomm).mp hx with rfl | rfl | rfl | rfl
    · rw [show a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ by group, ← hacomm.eq,
        show a₁ * (a₁ * a₂) * a₂ = (a₁ * a₁) * (a₂ * a₂) by group, ha₁2, ha₂2, one_mul]
    · exact ha₁2
    · exact ha₂2
    · exact one_mul 1
  have hWbc : ∀ x ∈ Wb, ∀ y ∈ Wb, x * y = y * x := fun x hx y hy =>
    commute_of_sq_eq_one hWbsq hx hy
  have hcWb : ∀ x ∈ Wb, c * x * c⁻¹ ∈ Wb := by
    intro x hx
    rw [mem_kleinFour_iff ha₁2 ha₂2 hacomm]
    rcases (mem_kleinFour_iff ha₁2 ha₂2 hacomm).mp hx with rfl | rfl | rfl | rfl
    · right; left
      rw [show c * (a₁ * a₂) * c⁻¹ = (c * a₁ * c⁻¹) * (c * a₂ * c⁻¹) by group, hc1, hc2,
        ← mul_assoc, ← hacomm.eq, mul_assoc, ha₂2, mul_one]
    · right; right; left
      exact hc1
    · left
      exact hc2
    · right; right; right
      group
  set A₁ : Subgroup G := ⁅K, K⁆ ⊓ (Wb.comap ψ).map A.subtype with hA₁
  have hA₁A : A₁ ≤ A := fun g hg => by
    obtain ⟨x, -, rfl⟩ := (mem_inf.mp hg).2
    exact x.2
  have hA₁W : ∀ g (hg : g ∈ A₁), ψ ⟨g, hA₁A hg⟩ ∈ Wb := by
    intro g hg
    obtain ⟨x, hx, hxg⟩ := (mem_inf.mp hg).2
    have h1 : (⟨g, hA₁A hg⟩ : A) = x := Subtype.ext hxg.symm
    rw [h1]
    exact hx
  have hmemA₁ : ∀ g (hgK : g ∈ ⁅K, K⁆) (hgA : g ∈ A), ψ ⟨g, hgA⟩ ∈ Wb → g ∈ A₁ :=
    fun g hgK hgA hgW => mem_inf.mpr ⟨hgK, ⟨⟨g, hgA⟩, hgW, rfl⟩⟩
  set W₁ := kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hcomm with hW₁
  have hu₁1 : u₁ ≠ 1 := fun h1 => ha₁ (by
    rw [ha₁def, show (⟨u₁, hu₁A⟩ : A) = 1 from Subtype.ext h1, map_one])
  have hu₂1 : u₂ ≠ 1 := fun h1 => ha₂ (by
    rw [ha₂def, show (⟨u₂, hu₂A⟩ : A) = 1 from Subtype.ext h1, map_one])
  have hu₁₂ : u₁ ≠ u₂ := fun h1 => hne (by
    rw [ha₁def, ha₂def]
    congr 1
    exact Subtype.ext h1)
  have hW₁4 : Nat.card W₁ = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions u₁ u₂ hu₁2 hu₂2 hu₁1 hu₂1 hu₁₂ hcomm).card_four
  have hWb4 : Nat.card Wb = 4 :=
    (isKleinFour_kleinFourOfCommutingInvolutions a₁ a₂ ha₁2 ha₂2 ha₁ ha₂ hne hacomm).card_four
  have hW₁2 : IsPGroup 2 W₁ := IsPGroup.of_card (n := 2) (by rw [hW₁4]; norm_num)
  have hW₁A₁ : W₁ ≤ A₁ := by
    intro w hw
    rcases (mem_kleinFour_iff hu₁2 hu₂2 hcomm).mp hw with rfl | rfl | rfl | rfl
    · refine hmemA₁ _ (mul_mem hu₁ hu₂) (mul_mem hu₁A hu₂A) ?_
      rw [hψmul u₁ u₂ hu₁A hu₂A]
      exact (mem_kleinFour_iff ha₁2 ha₂2 hacomm).mpr (Or.inl rfl)
    · exact hmemA₁ _ hu₁ hu₁A ((mem_kleinFour_iff ha₁2 ha₂2 hacomm).mpr (Or.inr (Or.inl rfl)))
    · exact hmemA₁ _ hu₂ hu₂A
        ((mem_kleinFour_iff ha₁2 ha₂2 hacomm).mpr (Or.inr (Or.inr (Or.inl rfl))))
    · exact one_mem _
  have hWsyl : IsSylowOf 2 W₁ A₁ := by
    obtain ⟨P', hP', hWP'⟩ := exists_isSylowOf_ge_of_le hW₁A₁ hW₁2
    have hinj : Function.Injective fun p : P' =>
        (⟨ψ ⟨p, hA₁A (hP'.le p.2)⟩, hA₁W _ (hP'.le p.2)⟩ : Wb) := by
      intro p p' hpp'
      have h1 : ψ ⟨p, hA₁A (hP'.le p.2)⟩ = ψ ⟨p', hA₁A (hP'.le p'.2)⟩ :=
        congrArg Subtype.val hpp'
      rw [hψ, psi_eq_iff] at h1
      have h2 := eq_one_of_mem_of_odd hP'.isPGroup (odd_card_oddCoreIn A)
        (mul_mem (inv_mem p.2) p'.2) h1
      rw [inv_mul_eq_one] at h2
      exact Subtype.ext h2
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [hWb4] at h1
    have h2 : W₁ = P' := eq_of_le_of_card_ge hWP' (by rw [hW₁4]; exact h1)
    rw [h2]
    exact hP'
  have hc₀A₁ : ∀ g ∈ A₁, c₀ * g * c₀⁻¹ ∈ A₁ := by
    intro g hg
    have hgA := hA₁A hg
    refine hmemA₁ _ (conj_mem_commutator_of_mem_normalizer (le_normalizer hc₀) (mem_inf.mp hg).1)
      (mul_mem (mul_mem hc₀A hgA) (inv_mem hc₀A)) ?_
    rw [hψmul _ _ (mul_mem hc₀A hgA) (inv_mem hc₀A), hψmul _ _ hc₀A hgA, hψinv]
    exact hcWb _ (hA₁W g hg)
  have hW'le : conjugate W₁ c₀⁻¹ ≤ A₁ := by
    intro x hx
    rw [mem_conjugate_iff, inv_inv] at hx
    have h1 := hc₀A₁ _ (hW₁A₁ hx)
    rwa [show c₀ * (c₀⁻¹ * x * c₀) * c₀⁻¹ = x by group] at h1
  have hW'syl : IsSylowOf 2 (conjugate W₁ c₀⁻¹) A₁ :=
    isSylowOf_of_card hW'le (by rw [card_conjugate_eq_card, hWsyl.card_eq])
  obtain ⟨a, haA₁, ha⟩ := exists_conj_eq_of_isSylowOf hWsyl hW'syl
  have haK : a ∈ K := by
    have h1 : ⁅K, K⁆ ≤ K := commutator_le.mpr fun g₁ hg₁ g₂ hg₂ => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
    exact h1 (mem_inf.mp haA₁).1
  have hnorm : ∀ x, x ∈ W₁ ↔ (c₀⁻¹ * a) * x * (c₀⁻¹ * a)⁻¹ ∈ W₁ := by
    intro x
    have h1 : x ∈ W₁ ↔ x ∈ conjugate (conjugate W₁ c₀⁻¹) a := by rw [ha]
    rw [h1, mem_conjugate_iff, mem_conjugate_iff, inv_inv]
    constructor <;> intro h2 <;> convert h2 using 1 <;> group
  refine ⟨a⁻¹ * c₀, mul_mem (inv_mem haK) hc₀, fun w hw => ?_, fun w hw hww => ?_⟩
  · rw [hnorm]
    convert hw using 1
    group
  · have hwA := hA₁A (hW₁A₁ hw)
    have haA := hA₁A haA₁
    have hwW := hA₁W w (hW₁A₁ hw)
    have haW := hA₁W a haA₁
    have h1 : c * ψ ⟨w, hwA⟩ * c⁻¹ = ψ ⟨w, hwA⟩ := by
      have hmem : a⁻¹ * c₀ * w * (a⁻¹ * c₀)⁻¹ ∈ A :=
        mul_mem (mul_mem (mul_mem (inv_mem haA) hc₀A) hwA) (inv_mem (mul_mem (inv_mem haA) hc₀A))
      have h2 : ψ ⟨a⁻¹ * c₀ * w * (a⁻¹ * c₀)⁻¹, hmem⟩ = ψ ⟨w, hwA⟩ := by
        congr 1
        exact Subtype.ext hww
      have h3 : ψ ⟨a⁻¹ * c₀ * w * (a⁻¹ * c₀)⁻¹, hmem⟩ =
          (ψ ⟨a, haA⟩)⁻¹ * (c * ψ ⟨w, hwA⟩ * c⁻¹) * ψ ⟨a, haA⟩ := by
        rw [show (⟨a⁻¹ * c₀ * w * (a⁻¹ * c₀)⁻¹, hmem⟩ : A) =
          (⟨a, haA⟩)⁻¹ * ⟨c₀, hc₀A⟩ * ⟨w, hwA⟩ * ((⟨a, haA⟩)⁻¹ * ⟨c₀, hc₀A⟩)⁻¹ from rfl]
        simp only [map_mul, map_inv]
        rw [hcdef]
        group
      rw [h3] at h2
      have h4 := hWbc _ (hcWb _ hwW) _ haW
      rw [mul_assoc, h4, ← mul_assoc, inv_mul_cancel, one_mul] at h2
      exact h2
    have hψw1 : ψ ⟨w, hwA⟩ = 1 := by
      rcases (mem_kleinFour_iff ha₁2 ha₂2 hacomm).mp hwW with h2 | h2 | h2 | h2
      · exfalso
        rw [h2, show c * (a₁ * a₂) * c⁻¹ = (c * a₁ * c⁻¹) * (c * a₂ * c⁻¹) by group, hc1, hc2,
          ← mul_assoc, ← hacomm.eq, mul_assoc, ha₂2, mul_one] at h1
        apply ha₂
        calc a₂ = a₁⁻¹ * (a₁ * a₂) := by group
          _ = 1 := by rw [← h1, inv_mul_cancel]
      · exfalso
        rw [h2, hc1] at h1
        exact hne h1.symm
      · exfalso
        rw [h2, hc2] at h1
        apply ha₁
        calc a₁ = a₁ * a₂ * a₂⁻¹ := by group
          _ = 1 := by rw [h1, mul_inv_cancel]
      · exact h2
    have h5 := (psi_eq_one_iff ε ⟨w, hwA⟩).mp hψw1
    exact eq_one_of_mem_of_odd hW₁2 (odd_card_oddCoreIn A) hw h5

end CFSG.ComponentClassification.Foote5

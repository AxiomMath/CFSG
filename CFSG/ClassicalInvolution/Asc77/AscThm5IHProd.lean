module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHFrame
public import CFSG.ClassicalInvolution.Asc77.WP3FrameAlpha

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG
open scoped commutatorElement

section Img

variable {S Y : Type} [Group S] [Group Y]

theorem thm5IH_odd_normal_eq_bot_of_quasisimple [Finite Y] {Q : Subgroup S}
    (hQ : CFSG.Open.IsQuasisimple ↥Q) (hcz : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c * c = 1)
    (π : S →* Y) {M : Subgroup Y} (hMA : M ≤ Q.map π)
    (hMn : ∀ a ∈ Q.map π, ∀ m ∈ M, a * m * a⁻¹ ∈ M) (hModd : Odd (Nat.card M)) : M = ⊥ := by
  classical
  set M' : Subgroup ↥Q := M.comap (π.comp Q.subtype) with hM'
  have hnorm : M'.Normal := ⟨fun n hn g => by
    show π ((g : S) * (n : S) * (g : S)⁻¹) ∈ M
    rw [map_mul, map_mul, map_inv]
    exact hMn _ (Subgroup.mem_map_of_mem π g.2) _ hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hQ M' with h | h
  · rw [Subgroup.eq_bot_iff_forall]
    intro m hm
    obtain ⟨q, hq, rfl⟩ := hMA hm
    have hqM : (⟨q, hq⟩ : ↥Q) ∈ M' := hm
    have hqc := Subgroup.mem_center_iff.mp (h hqM)
    have hq2 : q * q = 1 := hcz q hq fun q' hq' => congrArg Subtype.val (hqc ⟨q', hq'⟩).symm
    have hm2 : π q * π q = 1 := by rw [← map_mul, hq2, map_one]
    have hodd : Odd (orderOf (π q)) := hModd.of_dvd_nat (Subgroup.orderOf_dvd_natCard M hm)
    have hdvd : orderOf (π q) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hm2)
    have h2 : orderOf (π q) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h2
  · have hall : ∀ q ∈ Q, π q ∈ M := fun q hq => by
      have : (⟨q, hq⟩ : ↥Q) ∈ M' := by rw [h]; exact Subgroup.mem_top _
      exact this
    have hAM : Q.map π = M := le_antisymm (by
      rintro _ ⟨q, hq, rfl⟩
      exact hall q hq) hMA
    have : Group.IsPerfect ↥Q := ⟨hQ.1⟩
    have hperf : Group.IsPerfect ↥(Q.map π) := Group.IsPerfect.map π
    have : Finite ↥M := inferInstance
    have hsolv : Group.IsSolvable ↥M := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hModd
    rw [← hAM] at hsolv hModd
    by_contra hM
    rw [← hAM] at hM
    have hAne : Nontrivial ↥(Q.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hM
    exact Group.IsPerfect.not_isSolvable ↥(Q.map π) hsolv

theorem thm5IH_center_sq_of_quasisimple {Q : Subgroup S} (hQ : CFSG.Open.IsQuasisimple ↥Q)
    (hcz : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c * c = 1) {π : S →* Y}
    (hπ : π.ker ≤ Subgroup.center S) {a : Y} (ha : a ∈ Q.map π)
    (hac : ∀ a' ∈ Q.map π, a * a' = a' * a) : a * a = 1 := by
  classical
  obtain ⟨q, hq, rfl⟩ := ha
  have : Group.IsPerfect ↥Q := ⟨hQ.1⟩
  have hcomm : ∀ q' ∈ Q, ⁅q, q'⁆ ∈ Subgroup.center S := by
    intro q' hq'
    apply hπ
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hac _ (Subgroup.mem_map_of_mem π hq'))
  let c : ↥Q →* ↥(Subgroup.center S) :=
    { toFun := fun q' => ⟨⁅q, (q' : S)⁆, hcomm q' q'.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show ⁅q, ((a : S) * (b : S))⁆ = ⁅q, (a : S)⁆ * ⁅q, (b : S)⁆
        have hb := Subgroup.mem_center_iff.mp (hcomm b b.2) (a : S)
        calc ⁅q, ((a : S) * (b : S))⁆ = ⁅q, (a : S)⁆ * ((a : S) * ⁅q, (b : S)⁆ * (a : S)⁻¹) := by
              simp only [commutatorElement_def]; group
          _ = ⁅q, (a : S)⁆ * ⁅q, (b : S)⁆ := by
              rw [mul_inv_eq_iff_eq_mul.mpr hb]) }
  have hc : c = 1 := FrameVertex.eq_one_of_perfect_center c
  have hq2 : q * q = 1 := by
    refine hcz q hq fun q' hq' => ?_
    have h1 := congrArg (fun φ : ↥Q →* ↥(Subgroup.center S) =>
      ((φ ⟨q', hq'⟩ : ↥(Subgroup.center S)) : S)) hc
    have h2 : ⁅q, q'⁆ = 1 := h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h2
  rw [← map_mul, hq2, map_one]

theorem thm5IH_centralizerProd_of_quasisimple [Finite Y] {π : S →* Y}
    (hπ : π.ker ≤ Subgroup.center S) {y : S} (hy2 : y * y = 1) {Q₁ Q₂ : Subgroup S}
    (hQ₁ : CFSG.Open.IsQuasisimple ↥Q₁) (hQ₂ : CFSG.Open.IsQuasisimple ↥Q₂)
    (hc₁ : ∀ c ∈ Q₁, (∀ q ∈ Q₁, c * q = q * c) → c * c = 1)
    (hc₂ : ∀ c ∈ Q₂, (∀ q ∈ Q₂, c * q = q * c) → c * c = 1)
    (hy₁ : ∀ q ∈ Q₁, q * y = y * q) (hy₂ : ∀ q ∈ Q₂, q * y = y * q)
    (h₁₂ : ∀ a ∈ Q₁, ∀ b ∈ Q₂, a * b = b * a)
    (hC : ∀ g : S, g * y = y * g → ∃ a ∈ Q₁, ∃ b ∈ Q₂, g = a * b) :
    CentralizerProd π.range (π y) (Q₁.map π) (Q₂.map π) where
  A_le := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, hy₁ q hq])⟩
  B_le := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨⟨q, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (by rw [← map_mul, ← map_mul, hy₂ q hq])⟩
  comm := by
    rintro _ ⟨q₁, h1, rfl⟩ _ ⟨q₂, h2, rfl⟩
    rw [← map_mul, ← map_mul, h₁₂ q₁ h1 q₂ h2]
  A_odd := fun M hMA hMn hModd => thm5IH_odd_normal_eq_bot_of_quasisimple hQ₁ hc₁ π hMA hMn hModd
  B_odd := fun M hMA hMn hModd => thm5IH_odd_normal_eq_bot_of_quasisimple hQ₂ hc₂ π hMA hMn hModd
  center_odd := by
    intro a ha b hb hac hbc hodd
    have ha2 := thm5IH_center_sq_of_quasisimple hQ₁ hc₁ hπ ha fun a' ha' => hac a' ha'
    have hb2 := thm5IH_center_sq_of_quasisimple hQ₂ hc₂ hπ hb fun b' hb' => hbc b' hb'
    have hab : a * b = b * a := by
      obtain ⟨q₁, h1, rfl⟩ := ha
      obtain ⟨q₂, h2, rfl⟩ := hb
      rw [← map_mul, ← map_mul, h₁₂ q₁ h1 q₂ h2]
    have hsq : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    have hdvd : orderOf (a * b) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    have h2 : orderOf (a * b) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact h1
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h2
  sq_mem := by
    rintro g ⟨⟨γ, rfl⟩, hg⟩
    have hgc : π γ * π y = π y * π γ := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hker : γ * y * γ⁻¹ * y⁻¹ ∈ Subgroup.center S := by
      apply hπ
      have hconj : π γ * π y * (π γ)⁻¹ = π y := mul_inv_eq_iff_eq_mul.mpr hgc
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hconj, mul_inv_cancel]
    set c : S := γ * y * γ⁻¹ * y⁻¹ with hcdef
    have hcc : ∀ s : S, c * s = s * c := fun s => (Subgroup.mem_center_iff.mp hker s).symm
    have hγ : γ * y * γ⁻¹ = c * y := by
      rw [hcdef]
      group
    have hc2 : c * c = 1 := by
      have h1 : (γ * y * γ⁻¹) * (γ * y * γ⁻¹) = 1 := by
        calc (γ * y * γ⁻¹) * (γ * y * γ⁻¹) = γ * (y * y) * γ⁻¹ := by group
          _ = 1 := by rw [hy2]; group
      rw [hγ] at h1
      calc c * c = c * c * (y * y) := by rw [hy2, mul_one]
        _ = (c * y) * (c * y) := by
            calc c * c * (y * y) = c * (c * y) * y := by group
              _ = c * (y * c) * y := by rw [hcc y]
              _ = (c * y) * (c * y) := by group
        _ = 1 := h1
    have hγ2 : γ * γ * y = y * (γ * γ) := by
      have h1 : γ * (γ * y * γ⁻¹) * γ⁻¹ = y := by
        rw [hγ]
        calc γ * (c * y) * γ⁻¹ = (γ * c * γ⁻¹) * (γ * y * γ⁻¹) := by group
          _ = c * (c * y) := by
              rw [hγ, show γ * c * γ⁻¹ = c by rw [← hcc γ]; group]
          _ = (c * c) * y := by group
          _ = y := by rw [hc2, one_mul]
      calc γ * γ * y = (γ * (γ * y * γ⁻¹) * γ⁻¹) * (γ * γ) := by group
        _ = y * (γ * γ) := by rw [h1]
    obtain ⟨a, ha, b, hb, hab⟩ := hC (γ * γ) hγ2
    rw [← map_mul, hab, map_mul]
    exact Subgroup.mul_mem_sup (Subgroup.mem_map_of_mem π ha) (Subgroup.mem_map_of_mem π hb)

end Img

end CFSG.ClassicalInvolution.Asc77

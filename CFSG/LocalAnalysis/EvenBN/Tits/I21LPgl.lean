module

public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6Aut
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6AutPgl

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup

theorem pgl9_sylow {Y : Type*} [Group Y] [Finite Y] (J : Subgroup Y) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 6)) (hC : centralizer (J : Set Y) = ⊥) {t : Y}
    (ht2 : t * t = 1) (htJ : t ∉ J) (hpgl : PGLTwoSquareOuter J t) :
    Nat.card ↥(J ⊔ Subgroup.zpowers t) = 720 ∧
      (∀ D : Subgroup Y, D ≤ J ⊔ Subgroup.zpowers t → IsPGroup 2 D → Nat.card D = 16 → t ∈ D →
        ∀ s ∈ D, s ∉ J → s * s = 1 → ∃ d ∈ D, d * t * d⁻¹ = s) ∧
      (∀ F : Subgroup Y, F ≤ J ⊔ Subgroup.zpowers t → (∀ f ∈ F, f * f = 1) → Nat.card F ≤ 4) := by
  have hJ360 : Nat.card J = 360 := by
    rw [Nat.card_congr e.toEquiv]
    exact a6aut_card
  have hP : Nat.card ↥(J ⊔ zpowers t) = 720 := by
    rw [pglP_card_sup J ht2 htJ, hJ360]
  obtain ⟨K, _, _, hK9, ⟨Φ⟩⟩ := pglP_iso J hJ360 ht2 htJ hpgl
  refine ⟨hP, ?_, ?_⟩
  · intro D hDP _ hD16 htD s hsD hsJ hs2
    obtain ⟨ψ⟩ := pglP_dihedral_of_le hK9 Φ hDP hD16
    let t' : D := ⟨t, htD⟩
    let s' : D := ⟨s, hsD⟩
    have ht'2 : t' * t' = 1 := Subtype.ext ht2
    have hs'2 : s' * s' = 1 := Subtype.ext hs2
    have hnsq : ∀ u : D, (u : Y) ∉ J → ∀ x : DihedralGroup 8, x * x ≠ ψ u := by
      intro u huJ x hx
      apply huJ
      have h1 : ψ.symm x * ψ.symm x = u := by
        apply ψ.injective
        rw [map_mul, MulEquiv.apply_symm_apply, hx]
      have h2 := congrArg Subtype.val h1
      rw [← h2]
      exact pglP_sq_mem J ht2 (hDP (ψ.symm x).2)
    have hts : t * s ∈ J := by
      have h := pglP_mul_inv_mem J ht2 (hDP htD) (hDP hsD) htJ hsJ
      rwa [inv_eq_of_mul_eq_one_right hs2] at h
    have h8D : (t' * s') ^ 8 = 1 := by
      apply ψ.injective
      rw [map_pow, map_one]
      exact pglD16_pow _
    have h8Y : (t * s) ^ 8 = 1 := by simpa using congrArg Subtype.val h8D
    have h4Y : (t * s) ^ 4 = 1 := by
      have h8J : (⟨t * s, hts⟩ : J) ^ 8 = 1 := Subtype.ext (by simpa using h8Y)
      have h4A := a6aut_pow_four (e ⟨t * s, hts⟩) (by rw [← map_pow, h8J, map_one])
      have h4J : (⟨t * s, hts⟩ : J) ^ 4 = 1 := e.injective (by rw [map_pow, h4A, map_one])
      simpa using congrArg Subtype.val h4J
    have h4D : (t' * s') ^ 4 = 1 := Subtype.ext (by simpa using h4Y)
    have hab : (ψ t' * ψ s') ^ 4 = 1 := by rw [← map_mul, ← map_pow, h4D, map_one]
    obtain ⟨d', hd'⟩ := pglD16_conj (by rw [← map_mul, ht'2, map_one])
      (by rw [← map_mul, hs'2, map_one]) (hnsq t' htJ) (hnsq s' hsJ) hab
    refine ⟨(ψ.symm d' : Y), (ψ.symm d').2, ?_⟩
    have h1 : ψ.symm d' * t' * (ψ.symm d')⁻¹ = s' := by
      apply ψ.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hd'
    exact congrArg Subtype.val h1
  · intro E hEP hE2
    have hEp : IsPGroup 2 (E.subgroupOf (J ⊔ zpowers t)) := by
      intro g
      refine ⟨1, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have h := hE2 g.1.1 g.2
      simpa [pow_two] using h
    obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
    let D : Subgroup Y := (Q : Subgroup ↥(J ⊔ zpowers t)).map (J ⊔ zpowers t).subtype
    have hDP : D ≤ J ⊔ zpowers t := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hD16 : Nat.card D = 16 := by
      rw [card_map_of_injective (J ⊔ zpowers t).subtype_injective]
      exact pglP_card_sylow hP Q
    obtain ⟨ψ⟩ := pglP_dihedral_of_le hK9 Φ hDP hD16
    have hED : E ≤ D := fun x hx =>
      ⟨⟨x, hEP hx⟩, hQ (show (⟨x, hEP hx⟩ : ↥(J ⊔ zpowers t)) ∈ E.subgroupOf (J ⊔ zpowers t) from
        hx), rfl⟩
    refine pglP_card_le_four_of_key E ?_
    intro a ha b hb c hc ha1 hb1 hc1 hab hac hbc
    have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      a6aut_comm_of_sq_eq_one (hE2 x hx) (hE2 y hy) (hE2 _ (E.mul_mem hx hy))
    let a' : D := ⟨a, hED ha⟩
    let b' : D := ⟨b, hED hb⟩
    let c' : D := ⟨c, hED hc⟩
    have hsq : ∀ x : D, (x : Y) ∈ E → ψ x * ψ x = 1 := fun x hx => by
      rw [← map_mul, show x * x = 1 from Subtype.ext (hE2 x hx), map_one]
    have hne : ∀ x y : D, (x : Y) ≠ y → ψ x ≠ ψ y := fun x y h h' =>
      h (congrArg Subtype.val (ψ.injective h'))
    have hne1 : ∀ x : D, (x : Y) ≠ 1 → ψ x ≠ 1 := fun x h h' =>
      h (congrArg Subtype.val (ψ.injective (h'.trans (map_one ψ).symm)))
    have hcm : ∀ x y : D, (x : Y) * y = y * x → ψ x * ψ y = ψ y * ψ x := fun x y h => by
      rw [← map_mul, ← map_mul]
      exact congrArg ψ (Subtype.ext h)
    have key := pglD16_key (hsq a' ha) (hsq b' hb) (hsq c' hc) (hne1 a' ha1) (hne1 b' hb1)
      (hne1 c' hc1) (hne a' b' hab) (hne a' c' hac) (hne b' c' hbc)
      (hcm a' b' (hcomm a ha b hb)) (hcm a' c' (hcomm a ha c hc)) (hcm b' c' (hcomm b hb c hc))
    have h2 : a' * b' = c' := ψ.injective (by rw [map_mul]; exact key)
    exact congrArg Subtype.val h2

end CFSG.LocalAnalysis.EvenBN.Tits.I21L

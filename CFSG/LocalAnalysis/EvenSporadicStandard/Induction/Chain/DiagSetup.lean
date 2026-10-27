module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.InnCover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem diag_setup {R T₀ K' A N₀ : Subgroup H} (hKq : CFSG.IsQuasisimple ↥K')
    (hT₀R : T₀ ≤ centralizer (R : Set H)) (hK'T₀ : K' ≤ centralizer (T₀ : Set H))
    (hA : IsCompIn A (centralizer (R : Set H))) (hK'P : K' ≤ conjClosure A T₀)
    (hcov : ∃ π : ↥A →* ↥K', Function.Surjective π)
    (hN₀K' : N₀ ≤ centralizer (K' : Set H)) :
    (∀ s ∈ N₀, A.map (MulAut.conj s).toMonoidHom = A → ∀ x ∈ A, s * x * s⁻¹ = x) ∧
      Nonempty ((↥A ⧸ center ↥A) ≃* (↥K' ⧸ center ↥K')) := by
  set X : Subgroup H := centralizer (R : Set H) with hX
  obtain ⟨π₀, hπ₀⟩ := hcov
  have hAq : CFSG.IsQuasisimple ↥A := hA.isQuasisimple
  have hAperf : Group.IsPerfect ↥A := hAq.1
  have : Nontrivial ↥K' := CFSG.LocalCores.isQuasisimple_nontrivial hKq
  have hker₀ : π₀.ker ≤ center ↥A := central_kernel_of_surj hAq π₀ hπ₀
  have hcq : cqOrd A = cqOrd K' := cqOrd_eq_of_central_cover π₀ hπ₀ hker₀
  have hcompAB : ∀ B : Subgroup H, IsCompIn B X → B = A ∨ ∀ x ∈ B, ∀ y ∈ A, x * y = y * x := by
    intro B hB
    by_cases hBA : B = A
    · exact Or.inl hBA
    · exact Or.inr (hB.commute_of_ne hA hBA)
  have hBN : ∀ B : Subgroup H, IsCompIn B X → B ≤ normalizer (A : Set H) := by
    intro B hB
    rcases hcompAB B hB with rfl | hc
    · exact Subgroup.le_normalizer
    · intro y hy
      exact Subgroup.centralizer_le_normalizer (A : Set H)
        (Subgroup.mem_centralizer_iff.2 fun a ha => (hc y hy a ha).symm)
  have hconj : ∀ g ∈ T₀, IsCompIn (A.map (MulAut.conj g).toMonoidHom) X := fun g hg =>
    hA.map_conj (hT₀R hg)
  have hPN : conjClosure A T₀ ≤ normalizer (A : Set H) :=
    iSup₂_le fun g hg => hBN _ (hconj g hg)
  have hAC : ∀ a ∈ A, ∀ c ∈ centralizer (A : Set H), a * c = c * a := fun a ha c hc =>
    Subgroup.mem_centralizer_iff.1 hc a ha
  have hPAC : conjClosure A T₀ ≤ prodSub A (centralizer (A : Set H)) hAC := by
    refine iSup₂_le fun g hg x hx => ?_
    rcases hcompAB _ (hconj g hg) with hKA | hc
    · exact mem_prodSub.2 ⟨x, by rw [← hKA]; exact hx, 1, (centralizer (A : Set H)).one_mem,
        by simp⟩
    · exact mem_prodSub.2 ⟨1, A.one_mem, x,
        Subgroup.mem_centralizer_iff.2 fun a ha => (hc x hx a ha).symm, by simp⟩
  have hnc : ¬ ∀ k ∈ K', ∀ a ∈ A, k * a = a * k := by
    intro hall
    have hPC : conjClosure A T₀ ≤ centralizer (K' : Set H) := by
      refine iSup₂_le fun g hg => ?_
      rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have hgk : g * k = k * g := Subgroup.mem_centralizer_iff.1 (hK'T₀ hk) g hg
      have hk' : g * k * g⁻¹ = k := by rw [hgk]; group
      show k * (g * a * g⁻¹) = (g * a * g⁻¹) * k
      calc k * (g * a * g⁻¹) = (g * k * g⁻¹) * (g * a * g⁻¹) := by rw [hk']
        _ = g * (k * a) * g⁻¹ := by group
        _ = g * (a * k) * g⁻¹ := by rw [hall k hk a ha]
        _ = (g * a * g⁻¹) * (g * k * g⁻¹) := by group
        _ = (g * a * g⁻¹) * k := by rw [hk']
    exact not_forall_commute_of_isQuasisimple hKq fun a ha b hb =>
      Subgroup.mem_centralizer_iff.1 (hPC (hK'P hb)) a ha
  have hK'N : K' ≤ normalizer (A : Set H) := hK'P.trans hPN
  have hKAC : ∀ k ∈ K', ∃ a ∈ A, ∃ c ∈ centralizer (A : Set H), k = a * c := fun k hk =>
    mem_prodSub.1 (hPAC (hK'P hk))
  have hstar := exists_mul_of_cover hKq hcq hK'N hKAC hnc
  have hnormC : ∀ g ∈ normalizer (A : Set H), ∀ c ∈ centralizer (A : Set H),
      g * c * g⁻¹ ∈ centralizer (A : Set H) := fun g hg c hc =>
    (mem_normalizer_iff.1 (mem_normalizer_centralizer_of_mem_normalizer hg) c).1 hc
  refine ⟨?_, ?_⟩
  · intro s hsN hsA x hx
    have hsn : s ∈ normalizer (A : Set H) := Solomon78.mem_normalizer_iff_map_conj_eq.2 hsA
    have hsK' : ∀ k ∈ K', k * s = s * k := fun k hk =>
      Subgroup.mem_centralizer_iff.1 (hN₀K' hsN) k hk
    set Z : Subgroup H := A ⊓ centralizer (A : Set H) with hZdef
    have hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z := fun z hz z' hz' =>
      (Subgroup.mem_centralizer_iff.1 hz.2 z' hz'.1).symm
    have hZA : ∀ z ∈ Z, ∀ a ∈ A, z * a = a * z := fun z hz a ha =>
      (Subgroup.mem_centralizer_iff.1 hz.2 a ha).symm
    have hc : ∀ a ∈ A, a * s * a⁻¹ * s⁻¹ ∈ Z := by
      intro a ha
      obtain ⟨k, hk, c, hc, rfl⟩ := hstar a ha
      have hkN : k ∈ normalizer (A : Set H) := hK'N hk
      have h1 : k * c * s * (k * c)⁻¹ * s⁻¹ =
          k * (c * (s * c⁻¹ * s⁻¹)) * k⁻¹ := by
        have := hsK' k hk
        calc k * c * s * (k * c)⁻¹ * s⁻¹ = k * c * s * c⁻¹ * (k⁻¹ * s⁻¹) := by group
          _ = k * c * s * c⁻¹ * (s⁻¹ * k⁻¹) := by
              have h2 : k⁻¹ * s⁻¹ = s⁻¹ * k⁻¹ := by
                rw [← mul_inv_rev, ← mul_inv_rev, this]
              rw [h2]
          _ = k * (c * (s * c⁻¹ * s⁻¹)) * k⁻¹ := by group
      have hmemC : c * (s * c⁻¹ * s⁻¹) ∈ centralizer (A : Set H) :=
        (centralizer (A : Set H)).mul_mem hc
          (hnormC s hsn c⁻¹ ((centralizer (A : Set H)).inv_mem hc))
      have hmemC' : k * (c * (s * c⁻¹ * s⁻¹)) * k⁻¹ ∈ centralizer (A : Set H) :=
        hnormC k hkN _ hmemC
      refine ⟨?_, ?_⟩
      · have h3 : (k * c) * s * (k * c)⁻¹ * s⁻¹ ∈ A := by
          have h4 : s * (k * c)⁻¹ * s⁻¹ ∈ A := by
            have : (k * c)⁻¹ ∈ A := A.inv_mem ha
            exact (mem_normalizer_iff.1 hsn _).1 this
          have h5 : (k * c) * s * (k * c)⁻¹ * s⁻¹ = (k * c) * (s * (k * c)⁻¹ * s⁻¹) := by
            group
          rw [h5]
          exact A.mul_mem ha h4
        exact h3
      · rw [h1]
        exact hmemC'
    have hcomm := commutes_of_commutator_mem (A := A) (Z := Z) hZ hZA hc x hx
    calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hcomm]
      _ = x := by group
  · obtain ⟨e₁⟩ := cqEquiv_of_central_cover π₀ hπ₀ hker₀
    exact ⟨e₁⟩

end CFSG.EvenSporadicStandard.Induction
